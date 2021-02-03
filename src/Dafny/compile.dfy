include "examples/bank.dfy"
include "examples/fs/byte_fs.dfy"

datatype Addr = Addr(blkno: int, off: int)
