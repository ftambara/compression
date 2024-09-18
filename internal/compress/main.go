package compress

import (
	"errors"
	"fmt"
	"unicode"
)

// codeBufferBits defines number of bits in code processing buffers
const codeBufferBits = 64

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
	root *huffmanNode
}

func newHuffmanTree(root *huffmanNode) huffmanTree {
	return huffmanTree{root: root}
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

// huffmanNode represents a node in a Huffman tree
// Do not use this struct directly. Use newHuffmanInternalNode and newHuffmanLeaf instead,
// as they ensure that the struct is correctly initialized.
type huffmanNode struct {
	left, right *huffmanNode
	symbol      byte
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
