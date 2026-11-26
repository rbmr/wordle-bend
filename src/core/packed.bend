# Packed feedback table read.
#
# The table is a flat `Array<U32>` holding four 8-bit response codes per cell,
# little byte first: response `i` is byte `i & 3` of word `i >> 2`. This is the
# layout of the prototype's feedback table (`proto2/m1/src/tab.bend`,
# `pack_fb`) and of `proto2/m1/src/prof.bend` `dn_go` phase 1.
#
# `peek` uses only constant shifts, because Bend has no shift by a `U32`
# amount; the byte index selects the shift with arithmetic. The state machine
# of `dcount.bend` reads through this function, so the packed arithmetic is in
# one place.
import Base

# Byte `b & 3` of a word, inlined: `hi` shifts 16 when the byte index is 2 or
# 3, then `b & 1` shifts another 8 for an odd index, then the low byte is
# masked. Keeping this in one helper matters: a non-recursive Bend def is a C
# call, and this is the per-candidate hot path.
def peek_go(r: Array<U32> & U32, +i: U32) -> Array<U32> & U32:
  (t1, +w) = r
  +b = U32.and(i, 3)
  +hi = U32.sub(1, U32.shrn(U32.sub(b, 2), 31n))
  +u1 = U32.add(w, U32.mul(hi, U32.sub(U32.shrn(w, 16n), w)))
  +u2 = U32.add(u1, U32.mul(U32.and(b, 1), U32.sub(U32.shrn(u1, 8n), u1)))
  (t1, U32.and(u2, 255))

# Response code `i` of the packed table. The array is returned as the first
# component so the caller can keep reading it without a copy.
def peek(tbl: Array<U32>, +i: U32) -> Array<U32> & U32:
  peek_go(Array.get(U32, tbl, U32.shrn(i, 2n)), i)

def at_go(r: Array<U32> & U32, +i: U32) -> U32:
  (t1, +w) = r
  +b = U32.and(i, 3)
  +hi = U32.sub(1, U32.shrn(U32.sub(b, 2), 31n))
  +u1 = U32.add(w, U32.mul(hi, U32.sub(U32.shrn(w, 16n), w)))
  +u2 = U32.add(u1, U32.mul(U32.and(b, 1), U32.sub(U32.shrn(u1, 8n), u1)))
  U32.and(u2, 255)

# A pure read specification: the code a correctly filled table must hold at the
# flat index `i`.
def at(tbl: Array<U32>, +i: U32) -> U32:
  at_go(Array.get(U32, tbl, U32.shrn(i, 2n)), i)
