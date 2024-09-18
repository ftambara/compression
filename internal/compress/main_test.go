package compress

import (
	"bytes"
	"io"
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
	newHuffmanInternalNode(
		newHuffmanLeaf('a'),
		newHuffmanInternalNode(
			newHuffmanLeaf('b'),
			newHuffmanLeaf('c'),
		),
	),
)

func TestHuffmanReader(t *testing.T) {
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
	tree := newHuffmanTree(nil)
	var code uint64
	assertHuffmanDecoding(t, tree, code, errEmptyTree, nil)

	tree = huffmanTree{}
	assertHuffmanDecoding(t, tree, code, errEmptyTree, nil)

	tree = newHuffmanTree(newHuffmanInternalNode(nil, nil))
	assertHuffmanDecoding(t, tree, code, errInvalidCode{code}, nil)
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
	assertHuffmanDecoding(t, DefaultTree, code, errInvalidCode{code}, nil)

	code = 0xffffffffffffffff
	assertHuffmanDecoding(t, DefaultTree, code, errInvalidCode{code}, []byte("ccccccccccccccccccccc"))

	code = alignToLeft(0b01) >> 1
	assertHuffmanDecoding(t, DefaultTree, code, errInvalidCode{code}, nil)
}
