import Base
import ../src/groups.bend as Groups
import ../src/solve_fast.bend as SolveFast
import ./fast_hist5.bend as FH
import ./nat.bend as NatProof
import ./logic.bend as Logic
import ./fast_tbl.bend as FT
import ./array.bend as Arr

# ---------------------------------------------------------------------------
# Obligation B: the class branching factor counted by `class_k_start`
# ---------------------------------------------------------------------------
#
# This file states the specification that attaches the implementation's `k` to
# the logic; it is deliberately not imported by `PROOF.bend` yet, because the
# induction over the guess list is the remaining work. Nothing here is assumed:
# every definition below is constructive, and the lemmas that are present are
# proved. The intended theorem is
#
#   CK.loop_spec: for a guess suffix processed by `ck_loop`, the returned `k`
#   is at least `CK.prefmax(G, ws, i)` (the largest number of feedback groups
#   any guess up to `i` produces on the class `ws`), and the table invariant is
#   preserved.
#
# `class_k_start` calls the proved `hist5_go` fold once per guess, so the count
# for one guess is `Hist5Ok`'s `k`, which `FH.hist5_go_spec` gives as the
# number of feedback groups of that guess on the class. The fold then only has
# to keep the maximum over the guess list.

def CK.len(+xs: +List<+List<Nat>>) -> Nat:
  List.length(&2, +List<Nat>, xs)

# The number of feedback groups of `g` on the class `ws`.
def CK.count(+g: +List<Nat>, +ws: +List<+List<Nat>>) -> Nat:
  FH.FH.fgroups_count(SolveFast.fgroups_build_fast(g, ws, Nil{}))

# The largest count over the first `i` guesses.
def CK.prefmax(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
               +i: Nat) -> Nat:
  match i:
    case 0n:
      0n
    case 1n+p:
      Nat.max(CK.count(FT.FT.nth_word(G, p), ws), CK.prefmax(G, ws, p))

# `max a b <= c` from both bounds.
def CK.max_le(a: Nat, b: Nat, c: Nat,
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
            CK.max_le(ap, bp, cp, ha2, hb2))

# The state invariant of the scan: the current generation stamp, the table and
# the invariant that every cell is stamped below the generation the next
# histogram pass will use.
def CK.HistOk(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +gen: Nat, +fg: +List<SolveFast.FGroup>, hist: SolveFast.Hist5Res) -> Data:
  match hist:
    case SolveFast.Hist5Pruned{seen, tbl}:
      Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, fg),
        FT.FT.TblOk(G, C, n_root, tbl)>
    case SolveFast.Hist5Ok{seen, tbl, m, k, budget}:
      Arr.Arr.DPair<FH.FH.SeenTree(10n, 0, seen, gen, fg),
        FT.FT.TblOk(G, C, n_root, tbl)>

# The scan's postcondition: the table is still valid and `k` covers the largest
# count up to the processed index.
def CK.CkSpec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +ws: +List<+List<Nat>>, +i: Nat, r: SolveFast.CKRes) -> Data:
  match r:
    case SolveFast.CKRes{seen, tbl, k}:
      Arr.Arr.DPair<FT.FT.TblOk(G, C, n_root, tbl),
        {Nat.is_le(CK.prefmax(G, ws, i), k) == True{} : Bool}>
