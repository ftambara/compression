package compress

import (
	"bytes"
	"fmt"
	"io"
	"maps"
	"math"
	"os"
	"slices"
	"testing"
)

func assertSliceEqualUnordered[T comparable](t *testing.T, expected, got []T) {
	t.Helper()
	if len(expected) != len(got) {
		t.Fatalf("expected %v, got %v", expected, got)
	}
	// transform the slices into maps and compare them
	expectedMap := make(map[T]bool, len(expected))
	for _, v := range expected {
		expectedMap[v] = true
	}
	gotMap := make(map[T]bool, len(got))
	for _, v := range got {
		gotMap[v] = true
	}
	if !maps.Equal(expectedMap, gotMap) {
		t.Errorf("expected %v, got %v", expected, got)
	}
}

func Test_symbolCounts(t *testing.T) {
	type testCase struct {
		input    []byte
		expected []symbolCount
	}
	table := []testCase{
		{
			input:    []byte{},
			expected: []symbolCount{},
		},
		{
			input:    []byte("a"),
			expected: []symbolCount{{'a', 1}},
		},
		{
			input:    []byte("abac"),
			expected: []symbolCount{{'a', 2}, {'b', 1}, {'c', 1}},
		},
		{
			input: []byte("Daniele De Rossi"),
			expected: []symbolCount{
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
			},
		},
	}
	for _, tc := range table {
		t.Run(fmt.Sprintf("input: '%q`", tc.input), func(t *testing.T) {
			counts := symbolCounts(tc.input)
			assertSliceEqualUnordered(t, tc.expected, counts)
		})
	}
}

func assertHuffmanTreeEqual(t *testing.T, expected, actual HuffmanTree) {
	t.Helper()

	if len(expected.Leaves) != len(actual.Leaves) {
		t.Fatalf("expected %v leaves, got %v", len(expected.Leaves), len(actual.Leaves))
	}
	for i, expectedLeaf := range expected.Leaves {
		actualLeaf := actual.Leaves[i]
		if expectedLeaf.Symbol != actualLeaf.Symbol {
			t.Errorf("expected %v, got %v", expectedLeaf.Symbol, actualLeaf.Symbol)
		}
		if expectedLeaf.Code != actualLeaf.Code {
			t.Errorf("expected %v, got %v", expectedLeaf.Code, actualLeaf.Code)
		}
	}
	if !maps.Equal(expected.LeavesBySymbol, actual.LeavesBySymbol) {
		t.Errorf("expected %v, got %v", expected.LeavesBySymbol, actual.LeavesBySymbol)
	}
	if !maps.Equal(expected.LeavesByCode, actual.LeavesByCode) {
		t.Errorf("expected %v, got %v", expected.LeavesByCode, actual.LeavesByCode)
	}
}

func assertHuffmanTreeOk(t *testing.T, tree HuffmanTree) {
	t.Helper()
	bySymbol := tree.LeavesBySymbol
	byCode := tree.LeavesByCode
	if len(byCode) != len(bySymbol) {
		t.Fatalf("incompatible map lengths: %v != %v", len(byCode), len(bySymbol))
	}
	codeIndexes := make(map[uint32]bool, len(byCode))
	for _, index := range byCode {
		if codeIndexes[index] {
			t.Fatalf("duplicate index %v", index)
		}
		codeIndexes[index] = true
	}
	symbolIndexes := make(map[uint32]bool, len(bySymbol))
	for _, index := range bySymbol {
		if symbolIndexes[index] {
			t.Fatalf("duplicate symbol %v", index)
		}
		symbolIndexes[index] = true
	}
	// compare the two maps
	if !maps.Equal(codeIndexes, symbolIndexes) {
		t.Fatalf("incompatible indexes")
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
	expectedTree := huffmanTreeFromNode(
		huffmanBuildingNode{
			left: &huffmanBuildingNode{symbol: 'A'},
			right: &huffmanBuildingNode{
				left:  &huffmanBuildingNode{symbol: 'B'},
				right: &huffmanBuildingNode{symbol: 'C'},
			},
		},
	)
	assertHuffmanTreeOk(t, tree)
	assertHuffmanTreeEqual(t, expectedTree, tree)
}

func TestBuildUniversalHuffmanTree(t *testing.T) {
	input := bytes.NewBufferString("")
	_, err := BuildUniversalHuffmanTree(input)
	if err != nil {
		t.Fatalf("unexpected error %v", err)
	}

	input = bytes.NewBufferString("ABAC")
	tree, err := BuildUniversalHuffmanTree(input)
	if err != nil {
		t.Fatalf("unexpected error %v", err)
	}
	if len(tree.LeavesBySymbol) != math.MaxUint8+1 {
		t.Errorf("expected %v leaves, got %v", math.MaxUint8, len(tree.LeavesBySymbol))
	}
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
	out := make([]byte, len(expectedDecoded))
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

var DefaultTree = huffmanTreeFromNode(
	huffmanBuildingNode{
		left: &huffmanBuildingNode{symbol: 'a'},
		right: &huffmanBuildingNode{
			left:  &huffmanBuildingNode{symbol: 'b'},
			right: &huffmanBuildingNode{symbol: 'c'},
		},
	},
)

func TestHuffmanReader(t *testing.T) {
	code := []byte{0b10101100}
	buffer := bytes.NewBuffer(code)
	hr := NewHuffmanReader(buffer)
	hr.SetTree(&DefaultTree)
	expectedMessage := []byte("aab")
	out := make([]byte, len(expectedMessage))
	n, err := hr.Read(out)
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
	hr = NewHuffmanReader(buffer)
	hr.SetTree(&DefaultTree)
	expectedMessage = []byte("aacbc")
	out = make([]byte, len(expectedMessage))
	n, err = hr.Read(out)
	if err != nil && err != io.EOF {
		t.Fatalf("unexpected error %v", err)
	}
	if n != len(expectedMessage) {
		t.Fatalf("expected n = %v, got %v", len(expectedMessage), n)
	}
	if !slices.Equal(out[:n], expectedMessage) {
		t.Errorf("expected %v, got %v", expectedMessage, out[:n])
	}

	// test reading when the buffer is too small
	code = []byte{0b10101111, 0b10111000}
	buffer = bytes.NewBuffer(code)
	hr = NewHuffmanReader(buffer)
	hr.SetTree(&DefaultTree)
	out = make([]byte, 2)
	n, err = hr.Read(out)
	if err != nil {
		t.Fatalf("unexpected error %v", err)
	}
	if n != 2 {
		t.Fatalf("expected n = 2, got %v", n)
	}
	expectedMessage = []byte("aa")
	if !slices.Equal(out, expectedMessage) {
		t.Errorf("expected %v, got %v", expectedMessage, out)
	}
	expectedPending := []byte{0b00001111, 0b10111000}
	if !bytes.Equal(hr.pending[:n], expectedPending) {
		t.Errorf("expected %v, got %v", expectedPending, hr.pending[:n])
	}
}

// alignToLeft8 shifts x to the left until the most significant bit is 1
func alignToLeft8(x byte) byte {
	if x == 0 {
		return 0
	}
	var msb byte = 0x80
	for x&msb == 0 {
		x <<= 1
	}
	return x
}

func Test_decodeHuffmanEmpty(t *testing.T) {
	tree := newHuffmanTree()
	codes := []byte{}
	assertHuffmanDecoding(t, tree, codes, 0, 0, ErrEmptyTree, nil)

	tree = huffmanTreeFromNode(huffmanBuildingNode{left: nil, right: nil})
	assertHuffmanDecoding(t, tree, codes, 0, 0, nil, nil)
}

func Test_decodeHuffman(t *testing.T) {
	type testCase struct {
		name            string
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
			expectedUsed:    1,
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
			name:            "incomplete code",
			codes:           []byte{0b11011111},
			expectedUsed:    0,
			expectedWritten: 2,
			expectedMessage: []byte("bc"),
		},
		{
			name:            "invalid code, too short to detect error",
			codes:           []byte{0b1001},
			expectedUsed:    0,
			expectedWritten: 1,
			expectedMessage: []byte{'a'},
		},
	}

	for _, tc := range table {
		t.Run(tc.name, func(t *testing.T) {
			assertHuffmanDecoding(
				t,
				DefaultTree,
				tc.codes,
				tc.expectedWritten,
				tc.expectedUsed,
				tc.expectedErr,
				tc.expectedMessage,
			)
		})
	}
}

func assertHuffmanWrite(
	t *testing.T,
	tree HuffmanTree,
	message []byte,
	expectedCode []byte,
) {
	t.Helper()
	buffer := bytes.Buffer{}
	hw := NewHuffmanWriter(&buffer)
	hw.SetTree(&tree)
	n, err := hw.Write(message)
	if err != nil {
		t.Fatalf("unexpected error %v", err)
	}
	if n != len(message) {
		t.Fatalf("expected n = %v, got %v", len(expectedCode), n)
	}
	if !slices.Equal(buffer.Bytes(), expectedCode) {
		t.Errorf("expected %b, got %b", expectedCode, buffer.Bytes())
	}
}

func TestHuffmanWriter(t *testing.T) {
	table := []struct {
		name         string
		message      []byte
		expectedCode []byte
	}{
		{"empty message", []byte{}, []byte{}},
		{"single character", []byte{'a'}, []byte{alignToLeft8(0b10)}},
		{"multiple characters", []byte("abbac"), []byte{0b10110110, 0b10111000}},
	}

	for _, tc := range table {
		t.Run(tc.name, func(t *testing.T) {
			assertHuffmanWrite(t, DefaultTree, tc.message, tc.expectedCode)
		})
	}
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
			encoded := bytes.Buffer{}
			hw := NewHuffmanWriter(&encoded)
			hw.SetTree(&DefaultTree)
			_, err := hw.Write(tc.message)
			if err != nil {
				t.Fatalf("unexpected error %v", err)
			}

			hr := NewHuffmanReader(&encoded)
			hr.SetTree(&DefaultTree)
			decoded := make([]byte, len(tc.message))
			n, err := hr.Read(decoded)
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
	buffer := bytes.Buffer{}
	DefaultTree.ExportJSON(&buffer)

	f, err := os.Open("testdata/default-tree.json")
	if err != nil {
		t.Fatalf("unexpected error %v", err)
	}
	expected, err := io.ReadAll(f)
	if err != nil {
		t.Fatalf("unexpected error %v", err)
	}
	if buffer.String() != string(expected) {
		t.Errorf("expected \n\t%v\ngot \n\t%v", expected, buffer.String())
	}
}

func TestImportHuffmanTreeJSON(t *testing.T) {
	f, err := os.Open("testdata/default-tree.json")
	if err != nil {
		t.Fatalf("unexpected error %v", err)
	}
	tree, err := ImportHuffmanTreeJSON(f)
	if err != nil {
		t.Fatalf("unexpected error %v", err)
	}

	assertHuffmanTreeOk(t, tree)
	assertHuffmanTreeEqual(t, DefaultTree, tree)
}
