# Branchless 0/1 predicates and selects.
#
# The hot loops in this prototype read the state array, and a read hand back as
# a pair must be consumed by a callee, so every read is one call of the loop
# def. A call per read makes function calls expensive, hence: decisions inside
# a loop are computed as 0/1 U32s with the arithmetic below and the *phase
# number* of the next call is selected arithmetically. No Bool is ever matched
# in a hot loop.
import Base

# 1 when a == b, else 0. Works for any a, b: a < b wraps to a huge value.
def eq01(+a: U32, +b: U32) -> U32:
  U32.sub(1, U32.min(1, U32.sub(a, b)))

# 1 when a != b, else 0.
def ne01(+a: U32, +b: U32) -> U32:
  U32.min(1, U32.sub(a, b))

# 1 when x != 0, else 0.
def nz(+x: U32) -> U32:
  U32.min(1, x)

# 1 when a < b, else 0, for any a, b with a difference below 2^31. Dividing by
# 2^31 just reads the sign bit: the difference wraps above 2^31 exactly when a
# is smaller.
def lt01(+a: U32, +b: U32) -> U32:
  U32.div(U32.sub(a, b), 2147483648)

# 1 when a >= b, else 0.
def ge01(+a: U32, +b: U32) -> U32:
  U32.sub(1, lt01(a, b))

# 1 when a > b, else 0.
def gt01b(+a: U32, +b: U32) -> U32:
  lt01(b, a)

# f ? a : b, with f a 0/1 U32.
def sel(f: U32, +a: U32, +b: U32) -> U32:
  U32.add(b, U32.mul(f, U32.sub(a, b)))

# f ? a : b for Nats.
def seln(f: U32, a: Nat, b: Nat) -> Nat:
  match f:
    case 0:
      b
    case _:
      a
