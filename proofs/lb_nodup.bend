# Lower bounds for valid trees, part 4: candidate lists without duplicates.
#
# The capacity bound counts the candidates that end at each depth, and that
# count is only an upper bound on the number of classes when two candidates
# cannot end at the same node. A node ends the candidates equal to its guess, so
# no two distinct candidates end at one node, but two *occurrences* of the same
# word do. A duplicate-free candidate list is therefore where the capacity bound
# is sharp.
#
# This module states duplicate-freeness with the largest multiplicity
# (`LB.maxMult` of `lb_twice.bend`): a list is duplicate-free when no word
# occurs twice, which is `maxMult(S) <= 1`. Every multiplicity is then at most
# one, the fact the capacity argument uses to replace the multiplicity of the
# root guess by one. The predicate is a boolean equality, so a proof of it can
# be reused as often as a proof needs, which is what makes it practical to carry
# through the per-class recursion.
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./classbound_nat.bend as CB
import ./lb_twice.bend as Twice

# Duplicate-free: no word occurs more than once.
def LB.Nodup(+S: +List<+List<Nat>>) -> Type:
  {Nat.is_le(Twice.LB.maxMult(S), 1n) == True{} : Bool}

# The empty list is duplicate-free.
def LB.nodup_nil() -> LB.Nodup(Nil{}):
  NatProof.Nat.is_le_zero_l(1n)

# The multiplicity of any word is at most one.
def LB.nodup_mult(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +d: {Nat.is_le(Twice.LB.maxMult(S), 1n) == True{} : Bool}) ->
  {Nat.is_le(Twice.LB.mult(g, S), 1n) == True{} : Bool}:
  NatProof.Nat.is_le_trans(Twice.LB.mult(g, S), Twice.LB.maxMult(S), 1n,
    Twice.LB.mult_le_maxMult(g, S), d)

# The whole list counts a word at least as often as its tail does.
def LB.maxMult_tail(+h: +List<Nat>, +t: +List<+List<Nat>>) ->
  {Nat.is_le(Twice.LB.maxMult(t), Twice.LB.maxMult(h <> t)) == True{} : Bool}:
  +e : {Twice.LB.maxMult(h <> t)
        == Nat.max(Twice.LB.mult(h, h <> t), Twice.LB.maxMult(t)) : Nat} =
    {==}
  NatProof.Nat.is_le_eq_r(Twice.LB.maxMult(t),
    Nat.max(Twice.LB.mult(h, h <> t), Twice.LB.maxMult(t)), Twice.LB.maxMult(h <> t),
    Equal.sym(Nat, Twice.LB.maxMult(h <> t),
      Nat.max(Twice.LB.mult(h, h <> t), Twice.LB.maxMult(t)), e),
    CB.CB.is_le_of_ge(Nat.max(Twice.LB.mult(h, h <> t), Twice.LB.maxMult(t)),
      Twice.LB.maxMult(t), Nat.max_ge_r(Twice.LB.mult(h, h <> t), Twice.LB.maxMult(t))))

# `max a b <= c` from both bounds.
def LB.max_le(a: Nat, b: Nat, c: Nat,
    ha: {Nat.is_le(a, c) == True{} : Bool},
    hb: {Nat.is_le(b, c) == True{} : Bool}) ->
  {Nat.is_le(Nat.max(a, b), c) == True{} : Bool}:
  match a b:
    case 0n _:
      hb
    case 1n+ap 0n:
      ha
    case 1n++ap 1n++bp:
      match c:
        case 0n:
          Empty.absurd({Nat.is_le(Nat.max(1n+ap, 1n+bp), 0n) == True{} : Bool},
            Logic.Proof.false_ne_true(ha))
        case 1n++cp:
          +ha2 : {Nat.is_le(ap, cp) == True{} : Bool} =
            NatProof.Nat.is_le_succ_inv(ap, cp, ha)
          +hb2 : {Nat.is_le(bp, cp) == True{} : Bool} =
            NatProof.Nat.is_le_succ_inv(bp, cp, hb)
          NatProof.Nat.is_le_succ(Nat.max(ap, bp), cp,
            LB.max_le(ap, bp, cp, ha2, hb2))
