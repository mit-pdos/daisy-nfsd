package machine

// Bytes wraps a byte slice []byte
type Bytes struct {
	data []byte
}

func NewBytes(sz uint64) *Bytes {
	return &Bytes{data: make([]byte, sz)}
}

func (bs *Bytes) Get(i uint64) byte {
	return bs.data[i]
}

func (bs *Bytes) Append(b byte) {
	bs.data = append(bs.data, b)
}
