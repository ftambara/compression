package compress

import (
	"bytes"
	"io"
	"maps"
	"slices"
	"testing"
)

func assertSliceEqualSort[T comparable](t *testing.T, cmp func(a, b T) int, expected, got []T) {
	t.Helper()
	slices.SortFunc(expected, cmp)
	slices.SortFunc(got, cmp)
	if !slices.Equal(expected, got) {
		t.Errorf("expected %v, got %v", expected, got)
	}
}

func Test_symbolCounts(t *testing.T) {
	cmp := func(a, b symbolCount) int {
		if a.count == b.count {
			return int(a.symbol) - int(b.symbol)
		}
		return a.count - b.count
	}

	symbols := []byte("abc")
	counts := symbolCounts(symbols)
	expected := []symbolCount{
		{'a', 1},
		{'b', 1},
		{'c', 1},
	}
	assertSliceEqualSort(t, cmp, expected, counts)

	symbols = []byte("Daniele De Rossi")
	counts = symbolCounts(symbols)
	expected = []symbolCount{
		{'D', 2},
		{'a', 1},
		{'n', 1},
		{'i', 2},
		{'e', 3},
		{'l', 1},
		{' ', 2},
		{'R', 1},
		{'o', 1},
		{'s', 2},
	}
	assertSliceEqualSort(t, cmp, expected, counts)
}

func Test_newHuffmanTree(t *testing.T) {
	aLeaf := newHuffmanLeaf('a')
	bLeaf := newHuffmanLeaf('b')
	cLeaf := newHuffmanLeaf('c')

	root := newHuffmanInternalNode(
		aLeaf,
		newHuffmanInternalNode(bLeaf, cLeaf),
	)
	tree := newHuffmanTree(*root)
	expectedLeaves := make(map[byte]*huffmanNode, 3)
	expectedLeaves['a'] = aLeaf
	expectedLeaves['b'] = bLeaf
	expectedLeaves['c'] = cLeaf
	if !maps.Equal(expectedLeaves, tree.leaves) {
		t.Fatalf("expected %v, got %v", expectedLeaves, tree.leaves)
	}
	expectedCode := huffmanCode{Codepoint: 0b10, Length: 2}
	if aLeaf.code != expectedCode {
		t.Errorf("expected %v, got %v", expectedCode, aLeaf.code)
	}
	expectedCode = huffmanCode{Codepoint: 0b110, Length: 3}
	if bLeaf.code != expectedCode {
		t.Errorf("expected %v, got %v", expectedCode, bLeaf.code)
	}
	expectedCode = huffmanCode{Codepoint: 0b111, Length: 3}
	if cLeaf.code != expectedCode {
		t.Errorf("expected %v, got %v", expectedCode, cLeaf.code)
	}
}

func assertHuffmanTreeEqual(t *testing.T, expected, actual HuffmanTree) {
	t.Helper()

	// compare leaves
	for symbol, expectedLeaf := range expected.leaves {
		actualLeaf, ok := actual.leaves[symbol]
		if !ok {
			t.Errorf("expected leaf for symbol %v, got nil", symbol)
		}
		if expectedLeaf.symbol != actualLeaf.symbol {
			t.Errorf("expected symbol %v, got %v", expectedLeaf.symbol, actualLeaf.symbol)
		}
		if expectedLeaf.code != actualLeaf.code {
			t.Errorf("expected code %v, got %v", expectedLeaf.code, actualLeaf.code)
		}
	}

	expectedStack := []*huffmanNode{expected.root}
	actualStack := []*huffmanNode{actual.root}
	count := 0
	for len(actualStack) != 0 {
		expectedItem := expectedStack[len(expectedStack)-1]
		expectedStack = expectedStack[:len(expectedStack)-1]

		actualItem := actualStack[len(actualStack)-1]
		actualStack = actualStack[:len(actualStack)-1]

		if expectedItem.isLeaf() {
			if !actualItem.isLeaf() {
				t.Fatalf("#%d: expected leaf, got internal node", count)
			}
			if expectedItem.symbol != actualItem.symbol {
				t.Fatalf("#%d: expected symbol %v, got %v", count, expectedItem.symbol, actualItem.symbol)
			}
			if expectedItem.code != actualItem.code {
				t.Fatalf("#%d: expected code %v, got %v", count, expectedItem.code, actualItem.code)
			}
		} else {
			if actualItem.isLeaf() {
				t.Fatalf("#%d: expected internal node, got leaf", count)
			}
			if expectedItem.left != nil {
				if actualItem.left == nil {
					t.Fatalf("#%d: expected left node, got nil", count)
				}
				expectedStack = append(expectedStack, expectedItem.left)
				actualStack = append(actualStack, actualItem.left)
			}
			if expectedItem.right != nil {
				if actualItem.right == nil {
					t.Fatalf("#%d: expected right node, got nil", count)
				}
				expectedStack = append(expectedStack, expectedItem.right)
				actualStack = append(actualStack, actualItem.right)
			}
		}
		count++
	}
}

func TestBuildHuffmanTree(t *testing.T) {
	input := bytes.NewBufferString("")
	_, err := BuildHuffmanTree(input)
	if err == nil {
		t.Errorf("expected an error due to empty slice")
	}

	input = bytes.NewBufferString("ABAC")
	tree, err := BuildHuffmanTree(input)
	if err != nil {
		t.Fatalf("unexpected error %v", err)
	}
	expectedTree := newHuffmanTree(
		*newHuffmanInternalNode(
			newHuffmanLeaf('A'),
			newHuffmanInternalNode(
				newHuffmanLeaf('B'),
				newHuffmanLeaf('C'),
			),
		),
	)
	assertHuffmanTreeEqual(t, expectedTree, tree)
}

func assertHuffmanDecoding(
	t *testing.T,
	tree HuffmanTree,
	codes []byte,
	expectedWritten int,
	expectedUsed int,
	expectedErr error,
	expectedDecoded []byte,
) {
	t.Helper()
	out := make([]byte, codeBufferBits)
	used, written, err := tree.decode(codes, out)
	if err != expectedErr {
		t.Fatalf("unexpected error: %v", err)
	}
	if used != expectedUsed {
		t.Errorf("expected used = %v, got %v", expectedUsed, used)
	}
	if written != expectedWritten {
		t.Errorf("expected written = %v, got %v", expectedWritten, written)
	}
	if !slices.Equal(out[:written], expectedDecoded) {
		t.Errorf("expected %v, got %v", expectedDecoded, out[:written])
	}
}

var DefaultTree = newHuffmanTree(
	*newHuffmanInternalNode(
		newHuffmanLeaf('a'),
		newHuffmanInternalNode(
			newHuffmanLeaf('b'),
			newHuffmanLeaf('c'),
		),
	),
)

func TestHuffmanDecoder(t *testing.T) {
	code := []byte{0b10101100}
	buffer := bytes.NewBuffer(code)
	hd := NewHuffmanDecoder(buffer)
	hd.SetTree(&DefaultTree)
	expectedMessage := []byte("aab")
	out := make([]byte, len(expectedMessage))
	n, err := hd.Read(out)
	if err != nil && err != io.EOF {
		t.Fatalf("unexpected error %v", err)
	}
	if n != len(expectedMessage) {
		t.Fatalf("expected n = %v, got %v", len(expectedMessage), n)
	}
	if !slices.Equal(out[:n], expectedMessage) {
		t.Errorf("expected %v, got %v", expectedMessage, out[:n])
	}

	code = []byte{0b10101111, 0b10111000}
	buffer = bytes.NewBuffer(code)
	hd = NewHuffmanDecoder(buffer)
	hd.SetTree(&DefaultTree)
	expectedMessage = []byte("aacbc")
	out = make([]byte, len(expectedMessage))
	n, err = hd.Read(out)
	if err != nil && err != io.EOF {
		t.Fatalf("unexpected error %v", err)
	}
	if n != len(expectedMessage) {
		t.Fatalf("expected n = %v, got %v", len(expectedMessage), n)
	}
	if !slices.Equal(out[:n], expectedMessage) {
		t.Errorf("expected %v, got %v", expectedMessage, out[:n])
	}
}

// alignToLeft shifts n to the left until the most significant bit is set.
func alignToLeft(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	for n&(1<<(codeBufferBits-1)) == 0 {
		n <<= 1
	}
	return n
}

func Test_decodeHuffmanEmpty(t *testing.T) {
	tree := HuffmanTree{}
	codes := []byte{}
	assertHuffmanDecoding(t, tree, codes, 0, 0, ErrEmptyTree, nil)

	tree = newHuffmanTree(*newHuffmanInternalNode(nil, nil))
	assertHuffmanDecoding(t, tree, codes, 0, 0, nil, nil)
}

func Test_decodeHuffman(t *testing.T) {
	type testCase struct {
		name            string
		tree            *HuffmanTree
		codes           []byte
		expectedWritten int
		expectedUsed    int
		expectedErr     error
		expectedMessage []byte
	}
	table := []testCase{
		{
			name:            "normal case 1",
			codes:           []byte{0b10},
			expectedUsed:    1,
			expectedWritten: 1,
			expectedMessage: []byte{'a'},
		},
		{
			name:            "normal case 2",
			codes:           []byte{0b110},
			expectedUsed:    1,
			expectedWritten: 1,
			expectedMessage: []byte{'b'},
		},
		{
			name:            "normal case 3",
			codes:           []byte{0b10111},
			expectedUsed:    1,
			expectedWritten: 2,
			expectedMessage: []byte("ac"),
		},
		{
			name:            "codes can span multiple bytes",
			codes:           []byte{0b10111101, 0b01000000},
			expectedUsed:    2,
			expectedWritten: 5,
			expectedMessage: []byte("acaaa"),
		},
		{
			name:            "leading zeroes",
			codes:           []byte{0b00010},
			expectedUsed:    1,
			expectedWritten: 1,
			expectedMessage: []byte{'a'},
		},
		{
			name:            "leading zeroes must be at the beginning of the first byte",
			codes:           []byte{0b00000010, 0b00100000},
			expectedUsed:    1,
			expectedWritten: 1,
			expectedErr:     ErrInvalidCode{0b00100000},
			expectedMessage: []byte{'a'},
		},
		{
			name:            "padding",
			codes:           []byte{0b10000},
			expectedUsed:    1,
			expectedWritten: 1,
			expectedMessage: []byte{'a'},
		},
		{
			name:            "padding in the middle of the byte",
			codes:           []byte{0b10000, 0b11100000},
			expectedUsed:    0,
			expectedWritten: 1,
			expectedErr:     ErrInvalidPadding,
			expectedMessage: []byte{'a'},
		},
		{
			name:            "incomplete code",
			codes:           []byte{0b11011111},
			expectedUsed:    0,
			expectedWritten: 2,
			expectedMessage: []byte("bc"),
		},
		{
			name:            "invalid code",
			codes:           []byte{0b1001},
			expectedUsed:    0,
			expectedWritten: 1,
			expectedErr:     ErrInvalidCode{0b1001},
			expectedMessage: []byte{'a'},
		},
		{
			name:            "zero bytes",
			codes:           []byte{0b11011110, 0, 0b11100000},
			expectedUsed:    1,
			expectedWritten: 3,
			expectedErr:     ErrInvalidCode{0},
			expectedMessage: []byte("bca"),
		},
	}

	for _, tc := range table {
		if tc.tree == nil {
			tc.tree = &DefaultTree
		}
		t.Run(tc.name, func(t *testing.T) {
			assertHuffmanDecoding(
				t,
				*tc.tree,
				tc.codes,
				tc.expectedWritten,
				tc.expectedUsed,
				tc.expectedErr,
				tc.expectedMessage,
			)
		})
	}
}

func assertHuffmanEncoding(
	t *testing.T,
	tree HuffmanTree,
	message []byte,
	expectedCode []byte,
) {
	t.Helper()
	buffer := bytes.NewBuffer(message)
	he := NewHuffmanEncoder(buffer)
	he.SetTree(&tree)
	out := make([]byte, len(expectedCode))
	n, err := he.Read(out)
	if err != nil && err != io.EOF {
		t.Fatalf("unexpected error %v", err)
	}
	if n != len(expectedCode) {
		t.Fatalf("expected n = %v, got %v", len(expectedCode), n)
	}
	if !slices.Equal(out[:n], expectedCode) {
		t.Errorf("expected %v, got %v", expectedCode, out[:n])
	}
}

func TestHuffmanEncoder(t *testing.T) {
	assertHuffmanEncoding(t, DefaultTree, []byte("cab"), []byte{0b11110110})
	assertHuffmanEncoding(t, DefaultTree, []byte("abbac"), []byte{0b10110110, 0b10111000})
	assertHuffmanEncoding(t, DefaultTree, []byte{}, []byte{})
}

func TestHuffmanEncodeDecode(t *testing.T) {
	type testCase struct {
		name    string
		message []byte
	}
	table := []testCase{
		{"empty message", []byte{}},
		{"single character", []byte{'a'}},
		{"multiple characters", []byte("abbacca")},
	}

	for _, tc := range table {
		t.Run(tc.name, func(t *testing.T) {
			encoder := NewHuffmanEncoder(bytes.NewBuffer(tc.message))
			encoder.SetTree(&DefaultTree)
			encoded := make([]byte, len(tc.message)*codepointMaxLength)
			n, err := encoder.Read(encoded)
			if err != nil && err != io.EOF {
				t.Fatalf("unexpected error %v", err)
			}

			decoder := NewHuffmanDecoder(bytes.NewBuffer(encoded[:n]))
			decoder.SetTree(&DefaultTree)
			decoded := make([]byte, len(tc.message))
			n, err = decoder.Read(decoded)
			if err != nil && err != io.EOF {
				t.Fatalf("unexpected error %v", err)
			}
			if n != len(tc.message) {
				t.Fatalf("expected n = %v, got %v", len(tc.message), n)
			}
			if !slices.Equal(decoded, tc.message) {
				t.Errorf("expected %v, got %v", tc.message, decoded)
			}
		})
	}
}

func TestExportHuffmanTreeJSON(t *testing.T) {
	buffer := &bytes.Buffer{}
	DefaultTree.ExportJSON(buffer)

	expected := `{"left":{"symbol":97,"code":{"Codepoint":2,"Length":2}},"right":{"left":{"symbol":98,"code":{"Codepoint":6,"Length":3}},"right":{"symbol":99,"code":{"Codepoint":7,"Length":3}}}}`
	if buffer.String() != expected+"\n" {
		t.Errorf("expected \n\t%v\ngot \n\t%v", expected, buffer.String())
	}
}

func TestImportHuffmanTreeJSON(t *testing.T) {
	exportedTree := `{"left":{"symbol":97,"code":{"Codepoint":2,"Length":2}},"right":{"left":{"symbol":98,"code":{"Codepoint":6,"Length":3}},"right":{"symbol":99,"code":{"Codepoint":7,"Length":3}}}}`
	tree, err := ImportHuffmanTreeJSON(bytes.NewBufferString(exportedTree))
	if err != nil {
		t.Fatalf("unexpected error %v", err)
	}

	assertHuffmanTreeEqual(t, DefaultTree, tree)
}
