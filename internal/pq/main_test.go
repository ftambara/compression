package pq

import (
	"testing"
)

func TestPriorityQueue(t *testing.T) {
	pq := NewPriorityQueue(
		[]PQItem[string]{
			{"banana", 3},
			{"apple", 2},
			{"pear", 4},
			{"orange", 5},
		},
	)

	expected := []PQItem[string]{
		{"orange", 5},
		{"pear", 4},
		{"banana", 3},
		{"apple", 2},
	}

	for i := range pq.Len() {
		got := pq.Pop()
		if expected[i] != got {
			t.Errorf("expected=%+v, got=%+v\n", expected[i], got)
		}
	}
}
