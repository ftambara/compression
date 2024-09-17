package compress

import (
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
	expectedUsed int,
	expectedDecoded []byte,
) {
	t.Helper()
	out := make([]byte, codeBufferBits)
	written, used, err := tree.decode(code, out)
	if err != expectedErr {
		t.Fatalf("unexpected error: %v", err)
	}
	if used != expectedUsed {
		t.Errorf("expected %d, got %d", expectedUsed, used)
	}
	if !slices.Equal(out[:written], expectedDecoded) {
		t.Errorf("expected %v, got %v", expectedDecoded, out[:written])
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
	assertHuffmanDecoding(t, tree, code, errEmptyTree, 0, nil)

	tree = huffmanTree{}
	assertHuffmanDecoding(t, tree, code, errEmptyTree, 0, nil)

	tree = newHuffmanTree(newHuffmanInternalNode(nil, nil))
	assertHuffmanDecoding(t, tree, code, errInvalidCode{code}, 0, nil)
}

func Test_decodeHuffman(t *testing.T) {
	tree := newHuffmanTree(
		newHuffmanInternalNode(
			newHuffmanLeaf('a'),
			newHuffmanInternalNode(
				newHuffmanLeaf('b'),
				newHuffmanLeaf('c'),
			),
		),
	)

	code := alignToLeft(0b10)
	assertHuffmanDecoding(t, tree, code, nil, 64, []byte{'a'})

	code = alignToLeft(0b110)
	assertHuffmanDecoding(t, tree, code, nil, 64, []byte{'b'})

	code = alignToLeft(0b10111)
	assertHuffmanDecoding(t, tree, code, nil, 64, []byte{'a', 'c'})

	// Padding
	code = alignToLeft(0b100)
	assertHuffmanDecoding(t, tree, code, nil, 64, []byte{'a'})

	// Errors
	code = 0b010
	assertHuffmanDecoding(t, tree, code, errInvalidCode{code}, 0, nil)

	code = 0xffffffffffffffff
	assertHuffmanDecoding(t, tree, code, errIncompleteCode, 64, []byte("ccccccccccccccccccccc"))

	code = alignToLeft(0b01) >> 1
	assertHuffmanDecoding(t, tree, code, errInvalidCode{code}, 0, nil)
}
