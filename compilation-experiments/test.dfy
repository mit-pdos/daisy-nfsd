const pow64: int := 0x10000000000000000
newtype {:nativeType "ulong"} u64  = x:int | 0 <= x < 0x10000000000000000

newtype {:nativeType "byte"} byte  = x:int | 0 <= x < 256

method add2(x: u64, y: u64) returns (z:u64) {
    assert (x as int + y as int)%pow64 < pow64;
    return ((x as int + y as int)%pow64) as u64;
}

method array_idx(xs: array<byte>) returns (x:byte)
requires xs.Length > 0
 {
    return xs[0];
}