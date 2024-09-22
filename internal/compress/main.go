package compress

import (
	"bytes"
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
		return 0, errors.New("must implement processing of pending bytes")
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

	return hw.w.Write(packCodes(codes))
}

type ErrInvalidCode struct {
	code byte
}

func (e ErrInvalidCode) Error() string {
	return fmt.Sprintf("invalid code %x", e.code)
}

type ErrNoChild struct {
	movement huffmanMovement
}

func (e ErrNoChild) Error() string {
	return fmt.Sprintf("node has no child at side %v", e.movement)
}

var (
	ErrEmptyTree      = errors.New("tree has no root")
	ErrInvalidPadding = errors.New("invalid padding")
)

type HuffmanTree struct {
	root   *huffmanNode
	leaves map[byte]*huffmanNode
}

func newHuffmanTree(root huffmanNode) HuffmanTree {
	type stackItem struct {
		node      *huffmanNode
		accumCode []byte
	}

	// New trees have a "hidden" root that makes all valid codes start with 1
	actualRoot := newHuffmanInternalNode(nil, &root)

	children := make(map[byte]*huffmanNode, 0)
	nodeStack := []stackItem{{actualRoot, []byte{}}}

	for len(nodeStack) != 0 {
		item := nodeStack[len(nodeStack)-1]
		nodeStack = nodeStack[:len(nodeStack)-1]

		node := item.node
		if node.isLeaf() {
			children[node.symbol] = node
			var codept codepoint
			for _, b := range item.accumCode {
				codept = (codept << 1) + codepoint(b)
			}
			node.code = huffmanCode{Codepoint: codept, Length: len(item.accumCode)}
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
	return HuffmanTree{root: actualRoot, leaves: children}
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
	return buildHuffmanTreeFromCounts(freqs)
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
	for symbol := range byte(math.MaxUint8) {
		if !presentSymbols[symbol] {
			symbols = append(symbols, symbol)
		}
	}
	freqs := symbolCounts(symbols)
	return buildHuffmanTreeFromCounts(freqs)
}

func buildHuffmanTreeFromCounts(symbolFrequencies []symbolCount) (HuffmanTree, error) {
	if len(symbolFrequencies) == 0 {
		return HuffmanTree{}, errors.New("empty symbolFrequencies")
	}

	items := make([]pq.PQItem[*huffmanNode], len(symbolFrequencies))
	for i, sf := range symbolFrequencies {
		items[i] = pq.PQItem[*huffmanNode]{
			Value:    newHuffmanLeaf(sf.symbol),
			Priority: -int64(sf.count), // negate to make lowest count come first
		}
	}
	queue := pq.NewPriorityQueue(items)
	for queue.Len() >= 2 {
		node1 := queue.Pop()
		node2 := queue.Pop()
		queue.Push(pq.PQItem[*huffmanNode]{
			Value:    newHuffmanInternalNode(node1.Value, node2.Value),
			Priority: node1.Priority + node2.Priority,
		})
	}
	return newHuffmanTree(*queue.Pop().Value), nil
}

func (t HuffmanTree) MarshalJSON() ([]byte, error) {
	trueRoot := t.root.right // discard the hidden root
	return json.Marshal(trueRoot)
}

func (t *HuffmanTree) UnmarshalJSON(data []byte) error {
	root := huffmanNode{}
	err := json.Unmarshal(data, &root)
	if err != nil {
		return err
	}
	*t = newHuffmanTree(root)
	return nil
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
	node := t.root
	if node == nil {
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

	var bit uint8
	for i, code := range codes {
		for bitN %= 8; bitN < 8; bitN++ {
			if (code & (1 << (8 - bitN - 1))) == 0 {
				bit = 0
			} else {
				bit = 1
			}
			child, err := node.child(huffmanMovement(bit))
			if err != nil {
				if (err == ErrNoChild{huffmanMovement(bit)}) {
					return used, written, ErrInvalidCode{code}
				}
				return used, written, err
			}
			node = child

			if node.isLeaf() {
				out[written] = node.symbol
				written++
				node = t.root

				// if the rest of the byte is padding
				if bitN < 8-1 && (code&((1<<(8-bitN-1))-1) == 0) {
					if i == len(codes)-1 {
						// valid padding, update and return
						used = i + 1
						return used, written, nil
					}
					// invalid padding
					return used, written, ErrInvalidPadding
				}
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
			}
		}
	}
	return used, written, nil
}

func (t HuffmanTree) symbolCode(symbol byte) (huffmanCode, error) {
	leaf, ok := t.leaves[symbol]
	if !ok {
		return huffmanCode{}, fmt.Errorf("symbol 0x%x not present in tree", symbol)
	}
	return leaf.code, nil
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

type huffmanMovement int

const (
	left  huffmanMovement = 0
	right huffmanMovement = 1
)

// huffmanNode represents a node in a Huffman tree
// Do not use this struct directly. Use newHuffmanInternalNode and newHuffmanLeaf instead,
// as they ensure that the struct is correctly initialized.
type huffmanNode struct {
	left, right *huffmanNode
	symbol      byte
	code        huffmanCode
}

func newHuffmanInternalNode(left, right *huffmanNode) *huffmanNode {
	return &huffmanNode{left: left, right: right}
}

func newHuffmanLeaf(symbol byte) *huffmanNode {
	return &huffmanNode{symbol: symbol}
}

func (n *huffmanNode) isLeaf() bool {
	return n.left == nil && n.right == nil
}

func (n huffmanNode) child(movement huffmanMovement) (*huffmanNode, error) {
	var node *huffmanNode
	switch movement {
	case left:
		node = n.left
	case right:
		node = n.right
	default:
		return nil, fmt.Errorf("invalid movement %v", movement)
	}
	if node == nil {
		return nil, ErrNoChild{movement}
	}
	return node, nil
}

func (n huffmanNode) MarshalJSON() ([]byte, error) {
	if n.isLeaf() {
		code, err := json.Marshal(n.code)
		if err != nil {
			return nil, err
		}
		return []byte(fmt.Sprintf(`{"symbol":%d,"code":%s}`, n.symbol, code)), nil
	}
	buffer := bytes.Buffer{}
	buffer.Write([]byte{'{'})
	if n.left != nil {
		buffer.WriteString(`"left":`)
		nested, err := json.Marshal(n.left)
		if err != nil {
			return nil, err
		}
		buffer.Write(nested)
	}
	if n.right != nil {
		if n.left != nil {
			buffer.Write([]byte{','})
		}
		buffer.WriteString(`"right":`)
		nested, err := json.Marshal(n.right)
		if err != nil {
			return nil, err
		}
		buffer.Write(nested)
	}
	buffer.Write([]byte{'}'})
	return buffer.Bytes(), nil
}

func (n *huffmanNode) UnmarshalJSON(data []byte) error {
	var node struct {
		Symbol byte
		Code   huffmanCode
		Left   *huffmanNode
		Right  *huffmanNode
	}
	err := json.Unmarshal(data, &node)
	if err != nil {
		return err
	}
	if node.Left != nil {
		n.left = node.Left
	}
	if node.Right != nil {
		n.right = node.Right
	}
	n.symbol = node.Symbol
	n.code = node.Code
	return nil
}

type symbolCount struct {
	symbol byte
	count  int
}

func (s symbolCount) String() string {
	if unicode.IsSpace(rune(s.symbol)) {
		return fmt.Sprintf("<space>:%d", s.count)
	}
	return fmt.Sprintf("%c:%d", s.symbol, s.count)
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
		unique[i] = symbolCount{symbol: sym, count: count}
		i++
	}
	return unique
}
