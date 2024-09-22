package pq

import (
	"container/heap"
)

type PQItem[T any] struct {
	Value    T
	Priority int64
}

type PriorityQueue[T any] struct {
	iq internalQueue[T]
}

func NewPriorityQueue[T any](items []PQItem[T]) *PriorityQueue[T] {
	var iq internalQueue[T] = make([]*internalItem[T], len(items))
	for i, item := range items {
		iq[i] = &internalItem[T]{PQItem: item}
	}
	heap.Init(&iq)
	return &PriorityQueue[T]{iq: iq}
}

func (pq *PriorityQueue[T]) Push(item PQItem[T]) {
	heap.Push(&pq.iq, &internalItem[T]{PQItem: item})
}

func (pq *PriorityQueue[T]) Pop() PQItem[T] {
	return heap.Pop(&pq.iq).(*internalItem[T]).PQItem
}

func (pq *PriorityQueue[T]) Len() int { return len(pq.iq) }

// Underlying implementation source:
// https://cs.opensource.google/go/go/+/refs/tags/go1.23.1:src/container/heap/example_pq_test.go

type internalItem[T any] struct {
	PQItem[T]
	index int
}

type internalQueue[T any] []*internalItem[T]

func (iq internalQueue[T]) Len() int { return len(iq) }

func (iq internalQueue[T]) Less(i, j int) bool {
	// We want Pop to give us the highest, not lowest, priority so we use greater than here.
	return iq[i].Priority > iq[j].Priority
}

func (iq internalQueue[T]) Swap(i, j int) {
	iq[i], iq[j] = iq[j], iq[i]
	iq[i].index = i
	iq[j].index = j
}

func (iq *internalQueue[T]) Push(x any) {
	n := len(*iq)
	item := x.(*internalItem[T])
	item.index = n
	*iq = append(*iq, item)
}

func (iq *internalQueue[T]) Pop() any {
	old := *iq
	n := len(old)
	item := old[n-1]
	old[n-1] = nil  // don't stop the GC from reclaiming the item eventually
	item.index = -1 // for safety
	*iq = old[0 : n-1]
	return item
}
