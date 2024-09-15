package compress

import (
	"slices"
	"testing"
)

func assertSliceEqual[T comparable](t *testing.T, expected, got []T) {
	if !slices.Equal(expected, got) {
		t.Errorf("expected %v, got %v", expected, got)
	}
}

func assertSliceEqualSort[T comparable](t *testing.T, cmp func(a, b T) int, expected, got []T) {
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
