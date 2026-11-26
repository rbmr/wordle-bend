# Small `U32` facts the flat core machine proofs need.
#
# Every array index in the machine is `U32.from_nat` of a `Nat` shadow, so the
# arithmetic that has to be replayed in the proofs is: successor, addition, and
# the two closed constants the machine uses (`1` for a count cell, `0` for the
# cleared cell and the empty flag).
import Base
import ./fast_tbl.bend as FT

# The successor of a `from_nat` is the `from_nat` of the successor: this is
# `U32.from_nat`'s own recursion, so it is definitional.
def CA.u32_inc_from_nat(+k: Nat) ->
  {U32.inc(U32.from_nat(k)) == U32.from_nat(1n+k) : U32}:
  {==}

# Adding zero on the right.
def CA.u32_add_zero_r(+a: U32) -> {U32.add(a, 0) == a : U32}:
  Equal.trans(U32, U32.add(a, 0), U32.add(0, a), a,
    U32.add_comm(a, 0), FT.FT.u32_add_zero_l(a))

# `from_nat` of a sum is the sum of the `from_nat`s (this is `FT`'s lemma under
# a name the core proofs use consistently).
def CA.u32_add_from_nat(+a: Nat, +b: Nat) ->
  {U32.add(U32.from_nat(a), U32.from_nat(b)) == U32.from_nat(Nat.add(a, b))
   : U32}:
  FT.FT.u32_add_from_nat(a, b)

# The constants the machine writes.
def CA.u32_one() -> {U32.from_nat(1n) == 1 : U32}:
  {==}

def CA.u32_zero() -> {U32.from_nat(0n) == 0 : U32}:
  {==}

def CA.u32_256() -> {U32.from_nat(256n) == 256 : U32}:
  {==}

def CA.u32_512() -> {U32.from_nat(512n) == 512 : U32}:
  {==}

def CA.bool_to_u32_true() -> {Bool.to_u32(True{}) == 1 : U32}:
  {==}

def CA.bool_to_u32_false() -> {Bool.to_u32(False{}) == 0 : U32}:
  {==}

def CA.u32_sub_one_one() -> {U32.sub(1, 1) == 0 : U32}:
  {==}

def CA.u32_sub_one_zero() -> {U32.sub(1, 0) == 1 : U32}:
  {==}
