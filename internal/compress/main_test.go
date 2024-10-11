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
		t.Errorf(
			"leaf count mismatch: expected %d, got %d",
			len(expected.Leaves),
			len(actual.Leaves),
		)
		return
	}

	// Leaves can be in any order, so we need to check that both maps have the same entries
	actualLeaves := make(map[byte]huffmanLeaf, len(actual.Leaves))
	for _, leaf := range actual.Leaves {
		actualLeaves[leaf.Symbol] = *leaf
	}
	expectedLeaves := make(map[byte]huffmanLeaf, len(expected.Leaves))
	for _, leaf := range expected.Leaves {
		expectedLeaves[leaf.Symbol] = *leaf
	}
	if !maps.Equal(expectedLeaves, actualLeaves) {
		t.Errorf("leaves mismatch")
	}

	// Check that LeavesBySymbol points to the same leaves,
	// independently from the actual indices
	for symbol, expectedLeafIndex := range expected.LeavesBySymbol {
		expectedLeaf := expected.Leaves[expectedLeafIndex]
		actualLeafIndex, ok := actual.LeavesBySymbol[symbol]
		if !ok {
			t.Errorf("leaf for symbol 0x%x not found", symbol)
		}
		actualLeaf := actual.Leaves[actualLeafIndex]
		if *expectedLeaf != *actualLeaf {
			t.Errorf("for symbol 0x%x expected leaf %v, got %v", symbol, expectedLeaf, actualLeaf)
		}
	}

	// Check that LeavesByCode points to the same leaves,
	// independently from the actual indices
	for code, expectedLeafIndex := range expected.LeavesByCode {
		expectedLeaf := expected.Leaves[expectedLeafIndex]
		actualLeafIndex, ok := actual.LeavesByCode[code]
		if !ok {
			t.Errorf("leaf for code 0b%b not found", code)
		}
		actualLeaf := actual.Leaves[actualLeafIndex]
		if *expectedLeaf != *actualLeaf {
			t.Errorf("for code 0b%b expected leaf %v, got %v", code, expectedLeaf, actualLeaf)
		}
	}
}

func TestBuildHuffmanTree(t *testing.T) {
	testCases := []struct {
		name     string
		input    string
		expected HuffmanTree
	}{
		{
			name:     "empty input",
			input:    "",
			expected: NewHuffmanTree([]*huffmanLeaf{}),
		},
		{
			name:  "single character",
			input: "A",
			expected: NewHuffmanTree(
				[]*huffmanLeaf{
					{Symbol: 'A', Code: huffmanCode{Codepoint: 0b1, Length: 1}},
				},
			),
		},
		{
			name:  "multiple characters",
			input: "AAABBAC",
			expected: NewHuffmanTree(
				[]*huffmanLeaf{
					{Symbol: 'A', Code: huffmanCode{Codepoint: 0b10, Length: 2}},
					{Symbol: 'B', Code: huffmanCode{Codepoint: 0b110, Length: 3}},
					{Symbol: 'C', Code: huffmanCode{Codepoint: 0b111, Length: 3}},
				},
			),
		},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			tree, err := BuildHuffmanTree(bytes.NewBufferString(tc.input))
			if err != nil {
				t.Fatalf("unexpected error %v", err)
			}
			assertHuffmanTreeEqual(t, tc.expected, tree)
		})
	}
}

func TestBuildUniversalHuffmanTree(t *testing.T) {
	testCases := []struct {
		name  string
		input string
	}{
		{
			name:  "empty input",
			input: "",
		},
		{
			name:  "single character",
			input: "A",
		},
		{
			name:  "multiple characters",
			input: "AAABBAC",
		},
	}
	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			tree, err := BuildUniversalHuffmanTree(bytes.NewBufferString(tc.input))
			if err != nil {
				t.Fatalf("unexpected error %v", err)
			}
			expectedLeafCount := math.MaxUint8 + 1
			if len(tree.LeavesBySymbol) != expectedLeafCount {
				t.Errorf("expected %v leaves, got %v", expectedLeafCount, len(tree.LeavesBySymbol))
			}
			// Check that all possible byte values are present in the tree
			for i := 0; i < expectedLeafCount; i++ {
				if _, ok := tree.LeavesBySymbol[byte(i)]; !ok {
					t.Errorf("symbol %d not present in tree", i)
				}
			}
		})
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

var DefaultTree = NewHuffmanTree(
	[]*huffmanLeaf{
		{Symbol: 'A', Code: huffmanCode{Codepoint: 0b10, Length: 2}},
		{Symbol: 'B', Code: huffmanCode{Codepoint: 0b110, Length: 3}},
		{Symbol: 'C', Code: huffmanCode{Codepoint: 0b111, Length: 3}},
	},
)

func TestHuffmanReader(t *testing.T) {
	testCases := []struct {
		name           string
		input          []byte
		expectedOutput []byte
		outBufSize     int
		expectedError  error
	}{
		{
			name:           "empty input",
			input:          []byte{},
			expectedOutput: []byte{},
			outBufSize:     10,
			expectedError:  io.EOF,
		},
		{
			name:           "single character",
			input:          []byte{0b10},
			expectedOutput: []byte{'A'},
			outBufSize:     10,
			expectedError:  io.EOF,
		},
		{
			name:           "multiple characters",
			input:          []byte{0b10, 0b110},
			expectedOutput: []byte("AB"),
			outBufSize:     10,
			expectedError:  io.EOF,
		},
		{
			name:           "small output buffer",
			input:          []byte{0b10, 0b110},
			expectedOutput: []byte{'A'},
			outBufSize:     1,
			expectedError:  nil,
		},
		{
			name:           "incomplete code",
			input:          []byte{0b10, 0b11011111},
			expectedOutput: []byte("ABC"),
			outBufSize:     10,
			expectedError:  ErrInvalidCode{codept: 0b11},
		},
	}

	for _, tc := range testCases {
		t.Run(tc.name, func(t *testing.T) {
			hr := NewHuffmanReader(bytes.NewBuffer(tc.input))
			hr.SetTree(&DefaultTree)
			out := make([]byte, tc.outBufSize)

			n, err := hr.Read(out)
			if err != tc.expectedError {
				t.Fatalf("expected error %v, got %v", tc.expectedError, err)
			}
			if n != len(tc.expectedOutput) {
				t.Fatalf("expected n = %v, got %v", len(tc.expectedOutput), n)
			}
			if !slices.Equal(out[:n], tc.expectedOutput) {
				t.Errorf("expected %v, got %v", tc.expectedOutput, out[:n])
			}
		})
	}

	t.Run("multiple reads", func(t *testing.T) {
		hr := NewHuffmanReader(bytes.NewBuffer([]byte{0b10, 0b11010111}))
		hr.SetTree(&DefaultTree)
		out := make([]byte, 1)
		outBuff := bytes.Buffer{}
		expectedOutput := []byte("ABAC")
		var err error
		var n int
		for n, err = hr.Read(out); err == nil; n, err = hr.Read(out) {
			outBuff.Write(out[:n])
		}
		if err != io.EOF {
			t.Fatalf("expected EOF, got %v", err)
		}
		if outBuff.String() != string(expectedOutput) {
			t.Errorf("expected %v, got %v", expectedOutput, outBuff.String())
		}
	})
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
	tree := NewHuffmanTree([]*huffmanLeaf{})
	codes := []byte{}
	assertHuffmanDecoding(t, tree, codes, 0, 0, ErrEmptyTree, nil)
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
			expectedUsed:    8,
			expectedWritten: 1,
			expectedMessage: []byte{'A'},
		},
		{
			name:            "normal case 2",
			codes:           []byte{0b110},
			expectedUsed:    8,
			expectedWritten: 1,
			expectedMessage: []byte{'B'},
		},
		{
			name:            "normal case 3",
			codes:           []byte{0b10111},
			expectedUsed:    8,
			expectedWritten: 2,
			expectedMessage: []byte("AC"),
		},
		{
			name:            "codes can span multiple bytes",
			codes:           []byte{0b10111101, 0b01000000},
			expectedUsed:    11,
			expectedWritten: 5,
			expectedMessage: []byte("ACAAA"),
		},
		{
			name:            "leading zeroes",
			codes:           []byte{0b00010},
			expectedUsed:    8,
			expectedWritten: 1,
			expectedMessage: []byte{'A'},
		},
		{
			name:            "incomplete code",
			codes:           []byte{0b11011111},
			expectedUsed:    6,
			expectedWritten: 2,
			expectedMessage: []byte("BC"),
		},
		{
			name:            "invalid code, too short to detect error",
			codes:           []byte{0b1001},
			expectedUsed:    6,
			expectedWritten: 1,
			expectedMessage: []byte{'A'},
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
		{"single character", []byte{'A'}, []byte{alignToLeft8(0b10)}},
		{"multiple characters", []byte("ABBAC"), []byte{0b10110110, 0b10111000}},
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
		{"single character", []byte{'A'}},
		{"multiple characters", []byte("ABBACCA")},
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

	assertHuffmanTreeEqual(t, DefaultTree, tree)
}
