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

# 1 when b >= 2, else 0.
def ge2(+b: U32) -> U32:
  U32.sub(1, U32.shrn(U32.sub(b, 2), 31n))

# Byte `b & 3` of a word. `hi` shifts 16 when the byte index is 2 or 3, then
# `b & 1` shifts another 8 for an odd index, then the low byte is masked.
def byte4(+w: U32, +b: U32) -> U32:
  +hi = ge2(b)
  +t1 = U32.add(w, U32.mul(hi, U32.sub(U32.shrn(w, 16n), w)))
  +t2 = U32.add(t1, U32.mul(U32.and(b, 1), U32.sub(U32.shrn(t1, 8n), t1)))
  U32.and(t2, 255)

# Destructure a word read and extract the byte. The read result is passed in as
# a parameter, so Bend's "a match cannot scrutinize a computed value" rule is
# satisfied without an extra function in the hot path.
def peek_go(r: Array<U32> & U32, +i: U32) -> Array<U32> & U32:
  (t1, +w) = r
  (t1, byte4(w, U32.and(i, 3)))

# Response code `i` of the packed table. The array is returned as the first
# component so the caller can keep reading it without a copy.
def peek(tbl: Array<U32>, +i: U32) -> Array<U32> & U32:
  peek_go(Array.get(U32, tbl, U32.shrn(i, 2n)), i)

# A pure read specification: the code a correctly filled table must hold at the
# flat index `i`.
def at_go(r: Array<U32> & U32, +i: U32) -> U32:
  (t1, +w) = r
  byte4(w, U32.and(i, 3))

def at(tbl: Array<U32>, +i: U32) -> U32:
  at_go(Array.get(U32, tbl, U32.shrn(i, 2n)), i)
