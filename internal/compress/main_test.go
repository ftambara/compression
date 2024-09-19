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
	expectedCode := huffmanCode{codepoint: 0b10, length: 2}
	if aLeaf.code != expectedCode {
		t.Errorf("expected %v, got %v", expectedCode, aLeaf.code)
	}
	expectedCode = huffmanCode{codepoint: 0b110, length: 3}
	if bLeaf.code != expectedCode {
		t.Errorf("expected %v, got %v", expectedCode, bLeaf.code)
	}
	expectedCode = huffmanCode{codepoint: 0b111, length: 3}
	if cLeaf.code != expectedCode {
		t.Errorf("expected %v, got %v", expectedCode, cLeaf.code)
	}
}

func assertHuffmanDecoding(
	t *testing.T,
	tree huffmanTree,
	code uint64,
	expectedErr error,
	expectedDecoded []byte,
) {
	t.Helper()
	out := make([]byte, codeBufferBits)
	written, err := tree.decode(code, out)
	if err != expectedErr {
		t.Fatalf("unexpected error: %v", err)
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

	code = []byte{0b10101100, 0, 0, 0, 0, 0, 0, 0, 0b11111000}
	buffer = bytes.NewBuffer(code)
	hd = NewHuffmanDecoder(buffer)
	hd.SetTree(&DefaultTree)
	expectedMessage = []byte("aabcb")
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
	tree := huffmanTree{}
	var code uint64
	assertHuffmanDecoding(t, tree, code, ErrEmptyTree, nil)

	tree = newHuffmanTree(*newHuffmanInternalNode(nil, nil))
	assertHuffmanDecoding(t, tree, code, ErrInvalidCode{code}, nil)
}

func Test_decodeHuffman(t *testing.T) {
	code := alignToLeft(0b10)
	assertHuffmanDecoding(t, DefaultTree, code, nil, []byte{'a'})

	code = alignToLeft(0b110)
	assertHuffmanDecoding(t, DefaultTree, code, nil, []byte{'b'})

	code = alignToLeft(0b10111)
	assertHuffmanDecoding(t, DefaultTree, code, nil, []byte{'a', 'c'})

	// Padding
	code = alignToLeft(0b100)
	assertHuffmanDecoding(t, DefaultTree, code, nil, []byte{'a'})

	// Errors
	code = 0b010
	assertHuffmanDecoding(t, DefaultTree, code, ErrInvalidCode{code}, nil)

	code = 0xffffffffffffffff
	assertHuffmanDecoding(t, DefaultTree, code, ErrInvalidCode{code}, []byte("ccccccccccccccccccccc"))

	code = alignToLeft(0b01) >> 1
	assertHuffmanDecoding(t, DefaultTree, code, ErrInvalidCode{code}, nil)
}

func assertHuffmanEncoding(
	t *testing.T,
	tree huffmanTree,
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
