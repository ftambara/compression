package compress

import (
	"fmt"
	"unicode"
)

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
