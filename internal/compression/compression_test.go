package compression

import (
	"bytes"
	"testing"
)

func TestCompress(t *testing.T) {
	bytesIn := bytes.NewReader([]byte{1, 2, 3, 4, 5})
	bytesOut := &bytes.Buffer{}
	err := Compress(bytesIn, bytesOut)
	if err != nil {
		t.Errorf("Compress() failed: %v", err)
	}
	if bytesOut.Len() == 0 {
		t.Errorf("Compress() failed: output is empty")
	}
}
