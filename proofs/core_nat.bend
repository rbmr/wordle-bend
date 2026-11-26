# `Nat` comparison facts the flat core proofs need beyond `proofs/nat.bend`.
#
# The core keeps every array index as a `Nat` (or as `U32.from_nat` of one) in
# its ghost state.  A write outside a cell range is expressed with
# `Nat.is_lt`, while the list model tests indices with `Nat.is_eq`, so the
# proofs need the bridge between the two: a strict comparison is a disequality.
import Base
import ./logic.bend as Logic
import ./nat.bend as NatProof

# `a < b` implies `a != b`.
def core_nat_eq_false_of_lt(a: Nat, b: Nat,
    +h: {Nat.is_lt(a, b) == True{} : Bool}) ->
  {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool},
        Logic.Proof.false_ne_true(h))
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_eq(1n+ap, 0n) == False{} : Bool},
        Logic.Proof.false_ne_true(h))
    case 1n+ap 1n+bp:
      core_nat_eq_false_of_lt(ap, bp, h)

# `a != b` is symmetric.
def core_nat_ne_sym(a: Nat, b: Nat, eqb: Bool,
    +he: {eqb == Nat.is_eq(b, a) : Bool},
    +h: {Nat.is_eq(a, b) == False{} : Bool}) ->
  {Nat.is_eq(b, a) == False{} : Bool}:
  match eqb:
    case False{}:
      Equal.sym(Bool, False{}, Nat.is_eq(b, a), he)
    case True{}:
      +et : {Nat.is_eq(b, a) == True{} : Bool} =
        Equal.sym(Bool, True{}, Nat.is_eq(b, a), he)
      +es : {Nat.is_eq(a, b) == True{} : Bool} =
        NatProof.NatPrf.is_eq_sym(b, a, et)
      Empty.absurd({Nat.is_eq(b, a) == False{} : Bool},
        Logic.Proof.false_ne_true(
          Equal.trans(Bool, False{}, Nat.is_eq(a, b), True{},
            Equal.sym(Bool, Nat.is_eq(a, b), False{}, h), es)))

def core_nat_eq_false_sym(+a: Nat, +b: Nat,
    +h: {Nat.is_eq(a, b) == False{} : Bool}) ->
  {Nat.is_eq(b, a) == False{} : Bool}:
  core_nat_ne_sym(a, b, Nat.is_eq(b, a), {==}, h)

# `b <= a` and `a < c` give `b < c`; the store lemmas pass from a subtree
# range to a single cell.
def core_nat_lt_of_le_lt(a: Nat, b: Nat, c: Nat,
    +h1: {Nat.is_le(a, b) == True{} : Bool},
    +h2: {Nat.is_lt(b, c) == True{} : Bool}) ->
  {Nat.is_lt(a, c) == True{} : Bool}:
  NatProof.Nat.is_le_lt_trans(a, b, c, h1, h2)

# A `Bool` that is `False` is not `True`.
def core_bool_false_ne_true(+h: {False{} == True{} : Bool}) -> Empty:
  Logic.Proof.false_ne_true(h)
