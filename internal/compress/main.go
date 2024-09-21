package compress

import (
	"errors"
	"fmt"
	"io"
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
)

type HuffmanDecoder struct {
	rd      io.Reader
	tree    *huffmanTree
	pending []byte
}

func NewHuffmanDecoder(rd io.Reader) *HuffmanDecoder {
	return &HuffmanDecoder{
		rd:      rd,
		tree:    nil,
		pending: make([]byte, 0, decoderBufferLen),
	}
}

func (hd *HuffmanDecoder) SetTree(t *huffmanTree) {
	hd.tree = t
}

// Read reads packed codepoints from hd.rd and writes decoded symbols to buffer
func (hd *HuffmanDecoder) Read(buffer []byte) (int, error) {
	if hd.tree == nil {
		return 0, errors.New("on-the-fly tree generation not implemented yet")
	}
	if len(hd.pending) > 0 {
		return 0, errors.New("must implement processing of pending bytes")
	}

	readbuff := make([]byte, decoderBufferLen)
	readbuffStart := 0
	totalN := 0

	for {
		n, err := hd.rd.Read(readbuff[readbuffStart:])
		if err != nil && err != io.EOF {
			return totalN, err
		}
		n += readbuffStart

		// Decode
		used, written, err := hd.tree.decode(readbuff[:n], buffer[totalN:])
		totalN += written
		if totalN == len(buffer) {
			// No more space left in output buffer, save pending
			hd.pending = readbuff[used:]
			break
		}
		if err != nil {
			return totalN, err
		}
		if err == io.EOF {
			break
		}
		if used < n {
			copy(readbuff, readbuff[used:n])
			readbuffStart = n - used
		}
	}
	return totalN, nil
}

type HuffmanEncoder struct {
	rd   io.Reader
	tree *huffmanTree
}

func NewHuffmanEncoder(rd io.Reader) *HuffmanEncoder {
	return &HuffmanEncoder{
		rd:   rd,
		tree: nil,
	}
}

func (he *HuffmanEncoder) SetTree(t *huffmanTree) {
	he.tree = t
}

// Read reads symbols from he.rd and writes resulting encoded bytes to buffer
func (he *HuffmanEncoder) Read(buffer []byte) (int, error) {
	if he.tree == nil {
		return 0, errors.New("on-the-fly tree generation not implemented yet")
	}

	readbuff := make([]byte, encoderBufferLen)
	codes := make([]huffmanCode, 0, encoderBufferLen)
	totalN := 0

	for {
		n, err := he.rd.Read(readbuff)
		if err != nil && err != io.EOF {
			return totalN, err
		}

		for _, symbol := range readbuff[:n] {
			code, err := he.tree.symbolCode(symbol)
			if err != nil {
				return totalN, err
			}
			codes = append(codes, code)
		}
		packed := packCodes(codes)
		copy(buffer[totalN:], packed)
		totalN += len(packed)
		codes = codes[:0] // clear codes without freeing memory

		if err == io.EOF {
			break
		}
	}
	return totalN, nil
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

type huffmanTree struct {
	root   *huffmanNode
	leaves map[byte]*huffmanNode
}

func newHuffmanTree(root huffmanNode) huffmanTree {
	type stackItem struct {
		node      *huffmanNode
		accumCode []codepoint
	}

	// New trees have a "hidden" root that makes all valid codes start with 1
	actualRoot := newHuffmanInternalNode(nil, &root)

	children := make(map[byte]*huffmanNode, 0)
	nodeStack := []stackItem{{actualRoot, []codepoint{}}}

	for len(nodeStack) != 0 {
		item := nodeStack[len(nodeStack)-1]
		nodeStack = nodeStack[:len(nodeStack)-1]

		node := item.node
		if node.isLeaf() {
			children[node.symbol] = node
			var codept codepoint
			for _, b := range item.accumCode {
				codept = (codept << 1) + b
			}
			node.code = huffmanCode{codepoint: codept, length: len(item.accumCode)}
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
	return huffmanTree{root: actualRoot, leaves: children}
}

func buildHuffmanTree(symbolFrequencies []symbolCount) (huffmanTree, error) {
	if len(symbolFrequencies) == 0 {
		return huffmanTree{}, errors.New("empty symbolFrequencies")
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

func (t huffmanTree) decode(codes []byte, out []byte) (used, written int, err error) {
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

func (t huffmanTree) symbolCode(symbol byte) (huffmanCode, error) {
	leaf, ok := t.leaves[symbol]
	if !ok {
		return huffmanCode{}, fmt.Errorf("symbol 0x%x not present in tree", symbol)
	}
	return leaf.code, nil
}

const codepointMaxLength = 8

type codepoint byte // TODO: This should be uint16

type huffmanCode struct {
	codepoint codepoint
	length    int
}

// packCodes turns a slice of codes into a slice of bytes, properly packed
// to save space. The last code is aligned to the left and padded.
func packCodes(codes []huffmanCode) []byte {
	result := make([]byte, 0)
	var currentCode codepoint
	spaceLeft := codepointMaxLength
	for _, code := range codes {
		if code.length >= spaceLeft {
			currentCode += code.codepoint >> codepoint(code.length-spaceLeft)
			result = append(result, byte(currentCode))
			currentCode = 0
			spaceLeft = codepointMaxLength
		} else {
			currentCode += code.codepoint << codepoint(spaceLeft-code.length)
			spaceLeft -= code.length
		}
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
