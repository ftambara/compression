package main

import (
	"fmt"

	"github.com/ftambara/compression/internal/compression"
)

func main() {
	fmt.Println("Compressing files...")
	compression.Compress(nil, nil)
}
