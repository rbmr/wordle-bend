# Exact statement of the distinct-response count slice (next proof slice).
#
# This file is NOT imported by PROOF.bend as a law: the count-loop induction is
# not proved yet.  It fixes the predicates and the theorem so the next slice
# proves exactly the claim the plan names.  The proven foundation is in
# `core_list.bend`; the array read/write lemmas it will use are in `array.bend`.
import Base
import ../src/feedback.bend as Feedback
import ../src/core/packed.bend as Packed
import ./array.bend as Arr
import ./core_list.bend as CS
import ./nat.bend as NatProof
import ./fast_fb5.bend as FF5

# The ghost candidate word list helper (the proof-only analogue of `C`).
def DC.nth_word(+ws: +List<+List<Nat>>, i: Nat) -> +List<Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, rest}:
      match i:
        case 0n:
          w
        case 1n+p:
          DC.nth_word(rest, p)

# `Cells(a, i, n, xs)` says cells `i .. i+n-1` of `a` hold the ghost list `xs`
# (positions `i .. i+n-1`).
def DC.Cells(+i: Nat, +n: Nat, a: Array<U32>, +xs: +List<U32>) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+np:
      {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a, U32.from_nat(i)))
       == CS.CS.nth(xs, i) : U32} & DC.Cells(1n+i, np, a, xs)

# `SetCells(a, o, k, idxs)` says the candidate index range `o .. o+k-1` holds
# the ghost indices `idxs` in order (a special case of `Cells`).
def DC.SetCells(+o: Nat, +k: Nat, a: Array<U32>, +idxs: +List<U32>) -> Type:
  DC.Cells(o, k, a, idxs)

# `PackedOk(a, fb, idxs, codes)` says that for every candidate index `ci` in
# `idxs`, the packed table read at flat slot `fb + ci` is the code `codes[ci]`.
# `Packed.at` is the same constant-shift extraction the machine runs in phases
# 1 and 2, so this predicate is exactly "the table is filled correctly for
# this guess row".  The fill obligation (next slice) is
#   PackedOk(fill_packed(G, C), g*|C|, all candidate indices, codes)
# where `codes[ci] = FF5.encode_fb5_list(Feedback.feedback(G[g], C[ci]))`.
def DC.CodesOk(+fb: U32, a: Array<U32>, +idxs: +List<U32>,
    +codes: +List<U32>) -> Type:
  match idxs:
    case Nil{}:
      Unit
    case Con{ci, rest}:
      {Packed.at(a, U32.add(fb, ci)) == CS.CS.nth(codes, U32.to_nat(ci)) : U32}
      & DC.CodesOk(fb, a, rest, codes)

# `CodesFromFeedback(G, C, g, idxs, codes)` says every code is the 10-bit
# encoding of exactly `Feedback.feedback(G[g], C[ci])`.  This is the bridge
# from the packed table to the specification the theorem is stated in.
def DC.CodesFromFeedback(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +g: Nat,
    +idxs: +List<U32>, +codes: +List<U32>) -> Type:
  match idxs:
    case Nil{}:
      Unit
    case Con{ci, rest}:
      {CS.CS.nth(codes, U32.to_nat(ci))
       == FF5.FF5.encode_fb5_list(
            Feedback.feedback(DC.nth_word(G, g), DC.nth_word(C, U32.to_nat(ci))))
       : U32}
      & DC.CodesFromFeedback(G, C, g, rest, codes)

# `CodeSmall(codes)` says every packed response code is below 256, so the count
# cell index is inside the 256-cell count region.
def DC.CodeSmall(+codes: +List<U32>) -> Type:
  match codes:
    case Nil{}:
      Unit
    case Con{c, rest}:
      {Nat.is_lt(U32.to_nat(c), 256n) == True{} : Bool} & DC.CodeSmall(rest)

# `SameFrom(a0, a1, i, n)` says cells `i .. i+n-1` are unchanged.
def DC.SameFrom(+i: Nat, +n: Nat, a0: Array<U32>, a1: Array<U32>) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+np:
      {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a1, U32.from_nat(i)))
       == Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a0, U32.from_nat(i))) : U32}
      & DC.SameFrom(1n+i, np, a0, a1)

# The exact slice theorem.  Given:
#   - the candidate-index range cells `o..o+k-1` hold `idxs` (`SetCells`),
#   - the packed table row is correct for those indices (`PackedOk`),
#   - `codes` are the feedback encodings (`CodesFromFeedback`) and are < 256,
#   - the count/touched/result cells start at the zero model and the table/set
#     cells outside the scratch region are arbitrary but fixed,
# the machine result is `t` with:
#   - `t = |dedup(codes)|` (the number of distinct feedbacks),
#   - every count cell `0..255` is `0`,
#   - the result cell is `t`,
#   - every cell from `768` on is unchanged (`SameFrom`).
# The loop invariant also carries `DC.Cells(256, len T, a, T)` for the touched
# list `T`, which is what makes the clear pass total.
def DC.DCountSpec(+t: U32, +codes: +List<U32>, a0: Array<U32>,
    a1: Array<U32>, +n: Nat, +o: Nat, +k: Nat, +idxs: +List<U32>) -> Type:
  {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a1, 512)) == t : U32}
  & {CS.CS.len(CS.CS.dedup(codes)) == U32.to_nat(t) : Nat}
  & DC.Cells(0n, 256n, a1, CS.CS.zeros(256n))
  & DC.SameFrom(768n, n, a0, a1)
