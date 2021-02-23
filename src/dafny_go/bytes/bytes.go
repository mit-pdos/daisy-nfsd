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

func (bs *Bytes) Set(i uint64, b byte) {
	bs.Data[i] = b
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

func (bs *Bytes) Subslice(start uint64, end uint64) {
	bs.Data = bs.Data[start:end]
}

func (bs *Bytes) CopyTo(start uint64, other *Bytes) {
	if other == bs {
		panic("attempt to CopyTo self")
	}
	copy(bs.Data[start:], other.Data)
}

func (bs *Bytes) CopyFrom(other *Bytes, off uint64, count uint64) {
	if other == bs {
		panic("attempt to CopyFrom self")
	}
	copy(bs.Data, other.Data[off:count])
}

func (bs *Bytes) Split(off uint64) *Bytes {
	// this "full slice expression" is necessary to make the two Bytes
	// independent (otherwise bs will have the returned Bytes as its capacity,
	// which is overwritten by Append)
	//
	// see https://golang.org/ref/spec#Slice_expressions
	first := bs.Data[:off:off]
	second := bs.Data[off:]
	bs.Data = first
	return &Bytes{Data: second}
}
