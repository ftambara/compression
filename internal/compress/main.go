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
	// encoder/decoder buffers
	decoderBufferLen = 8 * 1024
	encoderBufferLen = 8 * 1024

	// max number of symbols in a huffman tree
	maxReadBytes = 16 * 1024
)

type HuffmanReader struct {
	r           io.Reader
	tree        *HuffmanTree
	readBuff    []byte
	readBuffEnd int
}

func NewHuffmanReader(rd io.Reader) *HuffmanReader {
	return &HuffmanReader{
		r:        rd,
		tree:     nil,
		readBuff: make([]byte, decoderBufferLen),
	}
}

func (hr *HuffmanReader) SetTree(t *HuffmanTree) {
	hr.tree = t
}

// Read reads packed codepoints from hr.r and writes decoded symbols to buffer
func (hr *HuffmanReader) Read(p []byte) (int, error) {
	if hr.tree == nil {
		return 0, errors.New("on-the-fly tree generation not implemented yet")
	}
	written := 0

	for {
		readBytes, readErr := hr.r.Read(hr.readBuff[hr.readBuffEnd:])
		if readErr != nil && readErr != io.EOF {
			return written, readErr
		}
		readLen := hr.readBuffEnd + readBytes
		if readLen == 0 {
			return written, readErr
		}

		// Decode
		usedBits, writtenBytes, err := hr.tree.decode(hr.readBuff[:readLen], p[written:])
		if err != nil {
			return written, err
		}
		if usedBits == 0 {
			mask := byte(1<<(8-usedBits%8) - 1)
			invalidCodept := codepoint(hr.readBuff[hr.readBuffEnd] & mask)
			return written, ErrInvalidCode{codept: invalidCodept}
		}
		written += writtenBytes
		fullyUsedBytes := usedBits / 8

		if usedBits%8 != 0 {
			// Clear used bits in partially read byte
			// e.g. if buffer = 0b10101100, usedBits = 4, then mask = 0b00001111
			mask := byte(1<<(8-usedBits%8) - 1)
			hr.readBuff[fullyUsedBytes] &= mask
		}

		if fullyUsedBytes < readLen {
			// Need to keep unused bits for next read
			copy(hr.readBuff, hr.readBuff[fullyUsedBytes:readLen])
			hr.readBuffEnd = readLen - fullyUsedBytes
		} else {
			hr.readBuffEnd = 0
		}

		if written == len(p) {
			return written, nil
		}
		if readErr == io.EOF {
			if fullyUsedBytes < readLen {
				mask := byte(1<<(8-usedBits%8) - 1)
				invalidCodept := codepoint(hr.readBuff[fullyUsedBytes] & mask)
				return written, ErrInvalidCode{codept: invalidCodept}
			}
			return written, readErr
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
	LeavesByCode   map[codepoint]uint64
	LeavesBySymbol map[byte]uint64
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

func NewHuffmanTree(leaves []*huffmanLeaf) HuffmanTree {
	tree := HuffmanTree{
		Leaves:         leaves,
		LeavesByCode:   make(map[codepoint]uint64, len(leaves)),
		LeavesBySymbol: make(map[byte]uint64, len(leaves)),
	}
	for i, leaf := range leaves {
		tree.LeavesByCode[leaf.Code.Codepoint] = uint64(i)
		tree.LeavesBySymbol[leaf.Symbol] = uint64(i)
	}
	return tree
}

func huffmanTreeFromCounts(symbolFrequencies []symbolCount) (HuffmanTree, error) {
	if len(symbolFrequencies) == 0 {
		return NewHuffmanTree([]*huffmanLeaf{}), nil
	}

	// huffmanBuildingNode might represent a leaf (if left == nil && right == nil)
	// or an internal huffmanBuildingNode
	// It's only goal is to be a helper to builder code. A tree does not contain
	// huffmanBuildingNode instances
	type huffmanBuildingNode struct {
		left, right *huffmanBuildingNode
		symbol      byte
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
		right := queue.Pop()
		left := queue.Pop()
		queue.Push(pq.PQItem[*huffmanBuildingNode]{
			Value:    &huffmanBuildingNode{left: left.Value, right: right.Value},
			Priority: left.Priority + right.Priority,
		})
	}

	// traverse tree to find the codepoint for each leaf
	type stackItem struct {
		node      *huffmanBuildingNode
		accumCode []byte
	}

	// New trees have a "hidden" root that makes all valid codes start with 1
	root := queue.Pop().Value
	actualRoot := huffmanBuildingNode{left: nil, right: root}
	nodeStack := []stackItem{{&actualRoot, []byte{}}}
	leaves := make([]*huffmanLeaf, 0)

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
			leaves = append(leaves, &huffmanLeaf{Symbol: node.symbol, Code: hcode})
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
	return NewHuffmanTree(leaves), nil
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

func (t HuffmanTree) decode(codes []byte, out []byte) (usedBits, writtenBytes int, err error) {
	if len(t.LeavesByCode) == 0 {
		return 0, 0, ErrEmptyTree
	}
	if len(codes) == 0 {
		return 0, 0, nil
	}

	// Skip leading zeros
	bitN := bits.LeadingZeros8(codes[0])
	if bitN == 8 {
		return 8, 0, nil
	}
	usedBits += bitN

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
				return usedBits, writtenBytes, ErrInvalidCode{hcode.Codepoint}
			}
			hcode.Codepoint = (hcode.Codepoint << 1) + codepoint(bit)
			leaf, ok := t.leaf(hcode.Codepoint)
			if !ok {
				continue
			}
			// Only update usedBits when a sympol is decoded
			usedBits = 8*i + bitN + 1

			out[writtenBytes] = leaf.Symbol
			writtenBytes++

			// if output has no space left
			if writtenBytes == len(out) {
				return usedBits, writtenBytes, nil
			}

			hcode = huffmanCode{}
		}
	}
	return usedBits, writtenBytes, nil
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

func (l huffmanLeaf) String() string {
	return fmt.Sprintf("{%c, 0x%x}", l.Symbol, l.Code.Codepoint)
}

type symbolCount struct {
	Symbol byte
	Count  int
}

const codepointMaxLength = 16

type codepoint uint16

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
