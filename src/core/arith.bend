# Branchless 0/1 predicates for the flat-array core.
#
# Same shapes as the prototype's `proto2/m1/src/arith.bend`: the hot loops
# compute 0/1 U32s from the sign bit of a wrapping difference, so no Bool is
# matched inside a loop and the emitted C stays straight-line.
import Base

# 1 when a == b, else 0.
def eq01(+a: U32, +b: U32) -> U32:
  U32.sub(1, U32.shrn(U32.or(U32.sub(a, b), U32.sub(b, a)), 31n))

# 1 when x != 0, else 0.
def nz(+x: U32) -> U32:
  U32.shrn(U32.or(x, U32.sub(0, x)), 31n)

# 1 when a < b, else 0, for a difference below 2^31.
def lt01(+a: U32, +b: U32) -> U32:
  U32.shrn(U32.sub(a, b), 31n)

# 1 when a >= b, else 0.
def ge01(+a: U32, +b: U32) -> U32:
  U32.sub(1, U32.shrn(U32.sub(a, b), 31n))

# f ? a : b for 0/1 f.
def sel(f: U32, +a: U32, +b: U32) -> U32:
  U32.add(b, U32.mul(f, U32.sub(a, b)))
