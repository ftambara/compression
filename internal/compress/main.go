package compress

import (
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"slices"
	"unicode"
)

type HuffmanDecoder struct {
	rd      io.Reader
	tree    *huffmanTree
	pending []byte
}

const (
	// codeBufferBits defines number of bits in code processing buffers
	codeBufferBits   = 64
	decoderBufferLen = 8 * 1024
)

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

func (hd *HuffmanDecoder) Read(buffer []byte) (int, error) {
	if hd.tree == nil {
		return 0, errors.New("on-the-fly tree generation not implemented yet")
	}
	if len(hd.pending) > 0 {
		return 0, errors.New("must implement processing of pending bytes")
	}

	readbuff := make([]byte, decoderBufferLen)
	totalN := 0

	var code uint64
	for {
		n, err := hd.rd.Read(readbuff)
		if err != nil && err != io.EOF {
			return totalN, err
		}

		// Convert read bytes to code/s
		for i := 0; i < n; i += 8 {
			var fromBuf []byte
			if i+8 > n {
				// Would get an error, write to zero'd buffer
				fromBuf = make([]byte, 8)
				copy(fromBuf, readbuff[i:n])
			} else {
				fromBuf = readbuff[i : i+8]
			}
			code = binary.BigEndian.Uint64(fromBuf)

			// Decode
			written, err := hd.tree.decode(code, buffer[totalN:])

			if written+totalN > len(buffer) {
				// No more space left in output buffer
				copy(hd.pending[:n-i], fromBuf)
				return totalN, nil
			}

			totalN += written
			if err != nil {
				return totalN, err
			}
		}

		if err == io.EOF {
			break
		}
	}
	return totalN, nil
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

type huffmanMovement int

const (
	left  huffmanMovement = 0
	right huffmanMovement = 1
)

type errInvalidCode struct {
	code uint64
}

func (e errInvalidCode) Error() string {
	return fmt.Sprintf("invalid code %x", e.code)
}

var (
	errEmptyTree = errors.New("tree has no root")
	errEmptyNode = errors.New("node has no children")
)

type huffmanTree struct {
	root   *huffmanNode
	leaves map[byte]*huffmanNode
}

func newHuffmanTree(root huffmanNode) huffmanTree {
	type stackItem struct {
		node      *huffmanNode
		accumCode []byte
	}

	children := make(map[byte]*huffmanNode, 0)
	nodeStack := []stackItem{
		{&root, []byte{1}}, // start accumCode with 1 because 0 is padding
	}
	for len(nodeStack) != 0 {
		item := nodeStack[len(nodeStack)-1]
		nodeStack = nodeStack[:len(nodeStack)-1]

		node := item.node
		if node.isLeaf() {
			children[node.symbol] = node
			var codepoint byte
			for _, b := range item.accumCode {
				codepoint = (codepoint << 1) + b
			}
			node.code = huffmanCode{codepoint: codepoint, length: len(item.accumCode)}
			continue
		}
		if node.left != nil {
			nodeStack = append(
				nodeStack,
				stackItem{node.left, append(slices.Clone(item.accumCode), 0)},
			)
		}
		if node.right != nil {
			// I don't need to clone accumcode again since this will be the only
			// potential reference left to the original
			nodeStack = append(nodeStack, stackItem{node.right, append(item.accumCode, 1)})
		}
	}
	return huffmanTree{root: &root, leaves: children}
}

func (t huffmanTree) decode(code uint64, out []byte) (written int, err error) {
	node := t.root
	if node == nil {
		return 0, errEmptyTree
	}

	var mask uint64 = 1 << (codeBufferBits - 1)

	if (code & mask) == 0 {
		return 0, errInvalidCode{code}
	}

	// Skip the first 1 bit
	mask >>= 1
	readBits := 1

	var bit int8
	for {
		// Reached the end and we don't have a symbol
		if readBits == codeBufferBits {
			return written, errInvalidCode{code}
		}

		if (code & mask) == 0 {
			bit = 0
		} else {
			bit = 1
		}
		movement := huffmanMovement(bit)

		node, err = node.child(movement)
		if err != nil {
			return written, err
		}
		mask >>= 1
		readBits++

		if node.isLeaf() {
			out[written] = node.symbol
			written++
			node = t.root
			if readBits == codeBufferBits {
				break
			}
			// check for padding
			if (code & mask) == 0 {
				// if the rest of the code is 0, we are done
				if code&(mask-1) == 0 {
					return written, nil
				}
				return written, errInvalidCode{code}
			} else {
				// skip 1 of next code point
				readBits++
				mask >>= 1
			}
		}
	}
	return written, nil
}

const codepointMaxLength = 8

type huffmanCode struct {
	codepoint byte // TODO: This should be uint16
	length    int
}

func packCodes(codes []huffmanCode) []byte {
	result := make([]byte, 0)
	var currentCode byte
	spaceLeft := 0
	for _, code := range codes {
		if code.length >= spaceLeft {
			currentCode += code.codepoint >> byte(code.length-spaceLeft)
			result = append(result, currentCode)
			currentCode = 0
			spaceLeft = codepointMaxLength
		} else {
			currentCode += code.codepoint << byte(spaceLeft-code.length)
			spaceLeft -= code.length
		}
	}
	if currentCode != 0 {
		result = append(result, currentCode)
	}
	return result
}

func (t huffmanTree) symbolCode(symbol byte) (huffmanCode, error) {
	leaf, ok := t.leaves[symbol]
	if !ok {
		return huffmanCode{}, fmt.Errorf("symbol 0x%x not present in tree", symbol)
	}
	return leaf.code, nil
}

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
		return nil, errEmptyNode
	}
	return node, nil
}
