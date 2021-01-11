package bytes

// Bytes wraps a byte slice []byte
type Bytes struct {
	Data []byte
}

func NewBytes(sz uint64) *Bytes {
	return &Bytes{Data: make([]byte, sz)}
}

func Data(data []byte) *Bytes {
	return &Bytes{Data: data}
}

func (bs *Bytes) Len() uint64 {
	return uint64(len(bs.Data))
}

func (bs *Bytes) Get(i uint64) byte {
	return bs.Data[i]
}

func (bs *Bytes) Append(b byte) {
	bs.Data = append(bs.Data, b)
}

func (bs *Bytes) AppendBytes(other *Bytes) {
	if other == bs {
		panic("attempt to append to self")
	}
	bs.Data = append(bs.Data, other.Data...)
}

func (bs *Bytes) Set(i uint64, b byte) {
	bs.Data[i] = b
}

func (bs *Bytes) Subslice(start uint64, end uint64) {
	bs.Data = bs.Data[start:end]
}
