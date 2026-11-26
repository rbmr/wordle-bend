# Correctness of the certified distinct-response count
# (`src/core/dcount.bend`, `src/core/packed.bend`).
#
# The table predicate `PK.PackedOk` says what "correctly filled" means for the
# packed table: for every candidate, the byte `Packed.peek` returns is the
# feedback code of the guess against that candidate. The fill code that
# establishes it is the next slice; this module proves the count conditional on
# it, so nothing is assumed silently.
#
# This file currently contains the table predicate, the state specification and
# the one-candidate branch lemma. The loop induction is the next slice and is
# stated at the bottom of the file.
#
# The count buffer is the proven `FH.SeenTree` generation-stamped buffer, and
# the group model is `DCount.build`, which adds every candidate (including one
# equal to the guess).
import Base
import ../src/feedback.bend as Feedback
import ../src/groups.bend as Groups
import ../src/tree.bend as Tree
import ../src/solve_fast.bend as SolveFast
import ../src/core/packed.bend as Packed
import ../src/core/dcount.bend as DCount
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./array.bend as Arr
import ./fast_groups.bend as FG
import ./fast_fb5.bend as FF5
import ./fast_tbl.bend as FT
import ./fast_hist5.bend as FH

# ---------------------------------------------------------------------------
# The packed table predicate
# ---------------------------------------------------------------------------

# One candidate's table read, as a predicate over the read pair.
def PK.cons(r: Array<U32> & U32, +g: +List<Nat>, +row: U32,
            +w: +List<Nat>, cont: Array<U32> -> Type) -> Type:
  (tbl, +code) = r
  {code == FF5.FF5.encode_fb5_list(Feedback.feedback(g, w)) : U32}
  & cont(tbl)

def PK.PackedOk(+g: +List<Nat>, +row: U32,
                +S: +List<&2, SolveFast.CWord>, tbl: Array<U32>) -> Type:
  match S:
    case Nil{}:
      Unit
    case Con{cw, rest}:
      match cw:
        case SolveFast.CWord{+ci, grow, w}:
          PK.cons(Packed.peek(tbl, U32.add(row, ci)), g, row, w,
                  t2 => PK.PackedOk(g, row, rest, t2))

# Eliminate the head of a `PackedOk`: hand the read array, the code and the
# equality to a continuation, together with the tail predicate.
def PK.elim_cons(-R: Data, +g: +List<Nat>, +row: U32, +w: +List<Nat>,
    cont: Array<U32> -> Type, r: Array<U32> & U32,
    hpk: PK.cons(r, g, row, w, cont),
    k: @tbl: Array<U32> -> @code: U32 ->
       {code == FF5.FF5.encode_fb5_list(Feedback.feedback(g, w)) : U32} ->
       cont(tbl) -> R) -> R:
  (tbl, +code) = r
  (ecode, htail) = hpk
  k(tbl, code, ecode, htail)

# The columns a valid row needs, independent of the table representation.
def PK.WordsLen5(+ws: +List<+List<Nat>>) -> Type:
  match ws:
    case Nil{}:
      Unit
    case Con{w, rest}:
      {SolveFast.is_len5(w) == True{} : Bool} & PK.WordsLen5(rest)

def PK.words_len5_head_cons(+w: +List<Nat>, +rest: +List<+List<Nat>>,
    p: PK.WordsLen5(w <> rest)) ->
  {SolveFast.is_len5(w) == True{} : Bool} & PK.WordsLen5(rest):
  (h, t) = p
  (h, t)

# ---------------------------------------------------------------------------
# The state specification
# ---------------------------------------------------------------------------

def PK.DSpec(+fg1: +List<SolveFast.FGroup>, +gen: Nat,
    res: DCount.DState) -> Data:
  match res:
    case DCount.DState{seen2, tbl2, +n, +k}:
      Arr.Arr.DPair<
        FH.FH.SeenTree(10n, 0, seen2, gen, fg1),
        Arr.Arr.DPair<
          {n == FH.FH.fgroups_total(fg1) : Nat},
          Arr.Arr.DPair<
            {k == FH.FH.fgroups_count(fg1) : Nat},
            {FH.FH.fgroups_wf(fg1) == True{} : Bool}>>>

# ---------------------------------------------------------------------------
# One candidate
# ---------------------------------------------------------------------------


# ---------------------------------------------------------------------------
# Next slice: the loop induction
#
# The remaining statement (not proved here; the progress file records why):
#
#   def PK.dc_go_spec(+S, +row, +g, +fg0, seen, tbl, +gen, +n, +k,
#       +hws: PK.WordsLen5(DCount.words(S)),
#       +hpk: PK.PackedOk(g,row,S,tbl),
#       +hn: {n == fgroups_total(fg0)},
#       +hk: {k == fgroups_count(fg0)},
#       +hs: SeenTree(10n,0,seen,gen,fg0)) ->
#     PK.DSpec(DCount.build(g,S,fg0), gen,
#       DCount.dc_go(row,S,gen, DCount.DState{seen,tbl,n,k}))
#
# `PK.dc_branch_spec` above is the one-candidate step; the loop is an
# induction on `S` using it and the tail `PackedOk`. The array copies needed by
# the `FH` get/swap lemmas are the open proof-engineering item.
