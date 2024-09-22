package compress

import (
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"log"
	"math"
	"math/bits"
	"slices"
	"unicode"

	"github.com/ftambara/compression/internal/pq"
)

const (
	// codeBufferBits defines number of bits in code processing buffers
	codeBufferBits = 64

	// encoder/decoder buffers
	decoderBufferLen = 8 * 1024
	encoderBufferLen = 8 * 1024

	// max number of symbols in a huffman tree
	maxReadBytes = 16 * 1024
)

type HuffmanReader struct {
	r       io.Reader
	tree    *HuffmanTree
	pending []byte
}

func NewHuffmanReader(rd io.Reader) *HuffmanReader {
	return &HuffmanReader{
		r:       rd,
		tree:    nil,
		pending: make([]byte, 0, decoderBufferLen),
	}
}

func (hr *HuffmanReader) SetTree(t *HuffmanTree) {
	hr.tree = t
}

// Read reads packed codepoints from hr.r and writes decoded symbols to buffer
func (hr *HuffmanReader) Read(p []byte) (int, error) {
	if len(p) == 0 {
		return 0, nil
	}
	if hr.tree == nil {
		return 0, errors.New("on-the-fly tree generation not implemented yet")
	}
	if len(hr.pending) > 0 {
		pending := hr.pending
		hr.pending = pending[:0]
		hr.Read(pending)
	}

	readbuff := make([]byte, decoderBufferLen)
	readbuffStart := 0
	totalN := 0

	for {
		n, readErr := hr.r.Read(readbuff[readbuffStart:])
		if readErr != nil && readErr != io.EOF {
			return totalN, readErr
		}
		n += readbuffStart

		// Decode
		used, written, err := hr.tree.decode(readbuff[:n], p[totalN:])
		totalN += written
		if totalN == len(p) {
			// No more space left in output buffer, save pending
			hr.pending = readbuff[used:]
			return totalN, nil
		}
		if err != nil {
			return totalN, err
		}
		if readErr == io.EOF {
			return totalN, io.EOF
		}
		if used < n {
			copy(readbuff, readbuff[used:n])
			readbuffStart = n - used
		}
	}
}

type HuffmanWriter struct {
	w    io.Writer
	tree *HuffmanTree
}

func NewHuffmanWriter(w io.Writer) *HuffmanWriter {
	return &HuffmanWriter{
		w:    w,
		tree: nil,
	}
}

func (hw *HuffmanWriter) SetTree(t *HuffmanTree) {
	hw.tree = t
}

// Write writes an encoded version of message to the underlying writer
//
// The encoded message is written in a packed format,
// not suitable for random access.
//
// Padding (zero bits) are added only at the last byte,
// when w's EOF is reached.
func (hw *HuffmanWriter) Write(message []byte) (int, error) {
	if hw.tree == nil {
		return 0, errors.New("on-the-fly tree generation not implemented yet")
	}

	codes := make([]huffmanCode, 0, encoderBufferLen)

	for _, symbol := range message {
		code, err := hw.tree.symbolCode(symbol)
		if err != nil {
			return 0, err
		}
		codes = append(codes, code)
	}

	packed := packCodes(codes)
	_, err := hw.w.Write(packed)
	if err != nil {
		return 0, err
	}
	return len(message), nil
}

type ErrInvalidCode struct {
	codept codepoint
}

func (e ErrInvalidCode) Error() string {
	return fmt.Sprintf("invalid code %x", e.codept)
}

var (
	ErrEmptyTree      = errors.New("tree has no root")
	ErrInvalidPadding = errors.New("invalid padding")
)

type HuffmanTree struct {
	Leaves         []*huffmanLeaf
	LeavesByCode   map[codepoint]uint32
	LeavesBySymbol map[byte]uint32
}

func BuildHuffmanTree(input io.Reader) (HuffmanTree, error) {
	symbols := make([]byte, maxReadBytes)

	n, err := input.Read(symbols)
	if err != nil && err != io.EOF {
		return HuffmanTree{}, err
	}
	if n == maxReadBytes {
		log.Printf("Warning: input too large, using only first %d bytes", n)
	}
	freqs := symbolCounts(symbols[:n])
	return huffmanTreeFromCounts(freqs)
}

// BuildUniversalHuffmanTree builds a Huffman tree with codes for all possible symbols,
// not just the ones present in the input.
func BuildUniversalHuffmanTree(input io.Reader) (HuffmanTree, error) {
	symbols := make([]byte, maxReadBytes)

	n, err := input.Read(symbols)
	if err != nil && err != io.EOF {
		return HuffmanTree{}, err
	}
	if n == maxReadBytes {
		log.Printf("Warning: input too large, using only first %d bytes", n)
	}
	symbols = symbols[:n]

	// add all missing symbols with frequency 0
	presentSymbols := make(map[byte]bool, len(symbols))
	for _, symbol := range symbols {
		presentSymbols[symbol] = true
	}
	for symbol := range math.MaxUint8 + 1 {
		if !presentSymbols[byte(symbol)] {
			symbols = append(symbols, byte(symbol))
		}
	}
	freqs := symbolCounts(symbols)
	return huffmanTreeFromCounts(freqs)
}

// huffmanBuildingNode might represent a leaf (if left == nil && right == nil)
// or an internal huffmanBuildingNode
// It's only goal is to be a helper to builder code. A tree does not contain
// huffmanBuildingNode instances
type huffmanBuildingNode struct {
	left, right *huffmanBuildingNode
	symbol      byte
	code        codepoint
}

func huffmanTreeFromCounts(symbolFrequencies []symbolCount) (HuffmanTree, error) {
	if len(symbolFrequencies) == 0 {
		return HuffmanTree{}, errors.New("empty symbolFrequencies")
	}

	// initialize queue items
	items := make([]pq.PQItem[*huffmanBuildingNode], len(symbolFrequencies))
	for i, sf := range symbolFrequencies {
		items[i] = pq.PQItem[*huffmanBuildingNode]{
			Value:    &huffmanBuildingNode{symbol: sf.Symbol},
			Priority: -int64(sf.Count), // negate to make lowest count come first
		}
	}

	// iteratively build tree using Huffman algorithm
	queue := pq.NewPriorityQueue(items)
	for queue.Len() >= 2 {
		node1 := queue.Pop()
		node2 := queue.Pop()
		queue.Push(pq.PQItem[*huffmanBuildingNode]{
			Value:    &huffmanBuildingNode{left: node1.Value, right: node2.Value},
			Priority: node1.Priority + node2.Priority,
		})
	}
	root := queue.Pop().Value
	return huffmanTreeFromNode(*root), nil
}

func newHuffmanTree() HuffmanTree {
	return HuffmanTree{
		Leaves:         make([]*huffmanLeaf, 0),
		LeavesByCode:   make(map[codepoint]uint32),
		LeavesBySymbol: make(map[byte]uint32),
	}
}

func huffmanTreeFromNode(root huffmanBuildingNode) HuffmanTree {
	tree := newHuffmanTree()

	// traverse tree to find the codepoint for each leaf
	type stackItem struct {
		node      *huffmanBuildingNode
		accumCode []byte
	}

	// New trees have a "hidden" root that makes all valid codes start with 1
	actualRoot := huffmanBuildingNode{left: nil, right: &root}
	nodeStack := []stackItem{{&actualRoot, []byte{}}}

	for len(nodeStack) != 0 {
		item := nodeStack[len(nodeStack)-1]
		nodeStack = nodeStack[:len(nodeStack)-1]

		node := item.node
		if node.left == nil && node.right == nil {
			if len(item.accumCode) > codepointMaxLength {
				panic("code too long")
			}
			var codept codepoint
			for _, b := range item.accumCode {
				codept = (codept << 1) + codepoint(b)
			}
			hcode := huffmanCode{Codepoint: codept, Length: len(item.accumCode)}
			tree.appendLeaf(huffmanLeaf{Symbol: node.symbol, Code: hcode})
			continue
		}
		if node.left != nil {
			nodeStack = append(
				nodeStack,
				stackItem{node.left, append(slices.Clone(item.accumCode), 0)},
			)
		}
		if node.right != nil {
			// Don't need to clone accumcode again since this will be the only
			// potential reference left to the original
			nodeStack = append(nodeStack, stackItem{node.right, append(item.accumCode, 1)})
		}
	}
	return tree
}

func (t *HuffmanTree) appendLeaf(leaf huffmanLeaf) {
	t.LeavesByCode[leaf.Code.Codepoint] = uint32(len(t.Leaves))
	t.LeavesBySymbol[leaf.Symbol] = uint32(len(t.Leaves))
	t.Leaves = append(t.Leaves, &leaf)
}

func (t HuffmanTree) ExportJSON(w io.Writer) error {
	encoder := json.NewEncoder(w)
	err := encoder.Encode(t)
	return err
}

func ImportHuffmanTreeJSON(r io.Reader) (HuffmanTree, error) {
	decoder := json.NewDecoder(r)
	t := HuffmanTree{}
	err := decoder.Decode(&t)
	return t, err
}

func (t HuffmanTree) decode(codes []byte, out []byte) (used, written int, err error) {
	if len(t.LeavesByCode) == 0 {
		return 0, 0, ErrEmptyTree
	}
	if len(codes) == 0 {
		return 0, 0, nil
	}

	// Skip leading zeros
	bitN := bits.LeadingZeros8(codes[0])

	if (codes[0] & (1 << (8 - bitN - 1))) == 0 {
		return 1, 0, ErrInvalidCode{0}
	}

	var hcode huffmanCode
	for i, code := range codes {
		for bitN %= 8; bitN < 8; bitN++ {
			var bit uint8
			if (code & (1 << (8 - bitN - 1))) == 0 {
				bit = 0
			} else {
				bit = 1
			}
			hcode.Length++
			if hcode.Length > codepointMaxLength {
				return used, written, ErrInvalidCode{hcode.Codepoint}
			}
			hcode.Codepoint = (hcode.Codepoint << 1) + codepoint(bit)
			leaf, ok := t.leaf(hcode.Codepoint)
			if !ok {
				continue
			}
			out[written] = leaf.Symbol
			written++

			// only update used bytes when fully decoded
			if bitN == 8-1 {
				used = i + 1
			} else {
				used = i
			}
			// if output has no space left
			if written == len(out) {
				// clear used bits before returning
				// TODO: don't mix input and output parameters
				codes[i] = code & ((1 << (8 - bitN)) - 1)
				return used, written, nil
			}

			hcode = huffmanCode{}
		}
	}
	return used, written, nil
}

func (t HuffmanTree) leaf(codept codepoint) (*huffmanLeaf, bool) {
	index, ok := t.LeavesByCode[codept]
	if !ok {
		return nil, false
	}
	return t.Leaves[index], true
}

func (t HuffmanTree) symbolCode(symbol byte) (huffmanCode, error) {
	index, ok := t.LeavesBySymbol[symbol]
	if !ok {
		return huffmanCode{}, fmt.Errorf("symbol 0x%x not present in tree", symbol)
	}
	return t.Leaves[index].Code, nil
}

type huffmanLeaf struct {
	Symbol byte
	Code   huffmanCode
}

type symbolCount struct {
	Symbol byte
	Count  int
}

const codepointMaxLength = 16

type codepoint uint16

func (c codepoint) toBytes() []byte {
	return []byte{byte(c)}
}

type huffmanCode struct {
	Codepoint codepoint
	Length    int
}

// packCodes turns a slice of codes into a slice of bytes, properly packed
// to save space. The last code is aligned to the left and padded.
func packCodes(codes []huffmanCode) []byte {
	result := make([]byte, 0)
	var currentCode codepoint
	spaceLeft := 8
	for _, code := range codes {
		codept := code.Codepoint
		codeLen := code.Length
		for codeLen > spaceLeft {
			currentCode += codept >> codepoint(codeLen-spaceLeft)
			result = append(result, byte(currentCode))
			codeLen -= spaceLeft
			codept &= (1 << codeLen) - 1
			currentCode = 0
			spaceLeft = 8
		}
		currentCode += codept << codepoint(spaceLeft-codeLen)
		spaceLeft -= codeLen
	}
	if currentCode != 0 {
		result = append(result, byte(currentCode))
	}
	return result
}

func (s symbolCount) String() string {
	if unicode.IsSpace(rune(s.Symbol)) {
		return fmt.Sprintf("<space>:%d", s.Count)
	}
	return fmt.Sprintf("%c:%d", s.Symbol, s.Count)
}

func symbolCounts(symbols []byte) []symbolCount {
	r := map[byte]int{}
	total := 0
	for _, sym := range symbols {
		r[sym]++
		total++
	}
	unique := make([]symbolCount, len(r))
	i := 0
	for sym, count := range r {
		unique[i] = symbolCount{Symbol: sym, Count: count}
		i++
	}
	return unique
}
