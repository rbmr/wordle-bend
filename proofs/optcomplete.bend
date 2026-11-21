# Completeness: a valid tree makes the search finite and small.
#
# The law `solve_optimal` has to exhibit the tree the solver returns, so the
# stored cost must be below infinity. This module proves that: if a valid tree
# for the candidate list exists, the search at that list has a finite cost, and
# that cost fits the square of the candidate count. The proof is the same fuel
# induction as the optimality bound, with the per-class tree facts supplied by
# the valid tree itself. An unusable root descends structurally into the class
# that holds the whole candidate list, so the same fuel applies again.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./bestok.bend as BO
import ./children.bend as CH
import ./classbound.bend as CBProof
import ./classbound_nat.bend as CBN
import ./classbound_sum.bend as CBS
import ./classbound_kids.bend as CBK
import ./optimalvalue.bend as OV
import ./optsum.bend as Sums
import ./optfold.bend as Fold
import ./optnode.bend as Node
import ./optind.bend as Ind
import ./optcost.bend as Cost
import ./groupsmeasure.bend as GM
import ./groupsdistinct.bend as GD
import ./groupcost.bend as GC
import ./nodecost.bend as NodeCost
import ./solvevalid.bend as SV
import ./mainvalid.bend as MV
import ./cover.bend as Cover
import ./cover_oracle.bend as Cora
import ./cover_groups.bend as Cgrp
import ./cover_list.bend as Clist
import ./cover_kids.bend as Ckids
import ./kids.bend as KidPr
import ./groups.bend as Grp
import ./validbag.bend as VB

# Eliminate a computed pair with a continuation.
def FC.use_pair(-R: Type, -A: Type, -B: Type, p: A & B,
    k: A -> B -> R) -> R:
  match p:
    case (a, b):
      k(a, b)

# A number below `n` has its square below `n*n`, which is below infinity.
def FC.sq_lt(+inf: Nat, +m: Nat, +n: Nat,
    e: {Nat.is_lt(m, n) == True{} : Bool},
    hz: {Nat.is_lt(Nat.mul(n, n), inf) == True{} : Bool}) ->
  {Nat.is_lt(Nat.mul(m, m), inf) == True{} : Bool}:
  +le : {Nat.is_le(m, n) == True{} : Bool} = NatProof.Nat.is_le_of_lt(m, n, e)
  +h1 : {Nat.is_le(Nat.mul(m, m), Nat.mul(n, m)) == True{} : Bool} =
    CBN.CB.is_le_mul_l(m, n, m, le)
  +h2 : {Nat.is_le(Nat.mul(n, m), Nat.mul(n, n)) == True{} : Bool} =
    CBN.CB.is_le_mul_r(m, n, n, le)
  +h3 : {Nat.is_le(Nat.mul(m, m), Nat.mul(n, n)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(Nat.mul(m, m), Nat.mul(n, m), Nat.mul(n, n), h1, h2)
  NatProof.Nat.is_le_lt_trans(Nat.mul(m, m), Nat.mul(n, n), inf, h3, hz)

# A saturating fold is at most the plain sum, with the accumulator up front.
def FC.sumL_le(+inf: Nat, +cs: +List<Nat>, +acc: Nat) ->
  {Nat.is_le(OV.OV.sumL(inf, cs, acc), Nat.add(acc, CBN.CB.sum(cs))) == True{}
   : Bool}:
  match cs:
    case Nil{}:
      NatProof.Nat.is_le_eq_r(acc, acc, Nat.add(acc, 0n),
        Equal.sym(Nat, Nat.add(acc, 0n), acc, NatProof.NatPrf.add_zero(acc)),
        NatProof.Nat.is_le_refl(acc))
    case Con{c, t}:
      +ih : {Nat.is_le(OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c)),
                 Nat.add(SolveRef.sat_add(inf, acc, c), CBN.CB.sum(t)))
             == True{} : Bool} =
        FC.sumL_le(inf, t, SolveRef.sat_add(inf, acc, c))
      +sat : {Nat.is_le(SolveRef.sat_add(inf, acc, c), Nat.add(acc, c))
              == True{} : Bool} =
        Sums.OQ.sat_add_le_add(inf, acc, c)
      +step : {Nat.is_le(Nat.add(SolveRef.sat_add(inf, acc, c), CBN.CB.sum(t)),
                  Nat.add(Nat.add(acc, c), CBN.CB.sum(t))) == True{} : Bool} =
        NatProof.Nat.is_le_add_r(SolveRef.sat_add(inf, acc, c),
          Nat.add(acc, c), CBN.CB.sum(t), sat)
      +mid : {Nat.is_le(OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c)),
                  Nat.add(Nat.add(acc, c), CBN.CB.sum(t))) == True{} : Bool} =
        NatProof.Nat.is_le_trans(
          OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c)),
          Nat.add(SolveRef.sat_add(inf, acc, c), CBN.CB.sum(t)),
          Nat.add(Nat.add(acc, c), CBN.CB.sum(t)), ih, step)
      NatProof.Nat.is_le_eq_r(
        OV.OV.sumL(inf, Con{c, t}, acc),
        Nat.add(Nat.add(acc, c), CBN.CB.sum(t)),
        Nat.add(acc, CBN.CB.sum(Con{c, t})),
        NatProof.NatPrf.add_assoc(acc, c, CBN.CB.sum(t)), mid)

# The completeness obligation for one candidate list.
def FC.FinJob(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>) -> Type:
  @hz: {Nat.is_lt(Nat.mul(Groups.len_words(S), Groups.len_words(S)), inf)
        == True{} : Bool}
  -> @T: Tree.Tree -> Tree.Valid(T, G, S)
  -> {Nat.is_lt(Eval.Eval.cost_of(SolveRef.step(fuel, SolveRef.mk_schedule(G, S),
        G, S, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
        Eval.Eval.dummy_zero())), inf) == True{} : Bool}
     & {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(fuel,
          SolveRef.mk_schedule(G, S), G, S, inf, Nil{}, Nil{}, 0n,
          Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())),
        Nat.mul(Groups.len_words(S), Groups.len_words(S))) == True{} : Bool}

# The conjunction of the obligations over a list of candidate lists.
def FC.FinFlat(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    jobs: +List<+List<+List<Nat>>>) -> Type:
  match jobs:
    case Nil{}:
      Unit
    case Con{S, t}:
      FC.FinJob(fuel, inf, G, S) & FC.FinFlat(fuel, inf, G, t)

# The obligations of one guess's classes.
def FC.FinClass(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          FC.FinJob(fuel, inf, G, ws) & FC.FinClass(fuel, inf, G, rest)

# The class obligations of one guess, only when the guess is usable.
def FC.FinClassIf(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>, b: Bool,
    +groups: +List<Groups.Group>) -> Type:
  match b:
    case True{}:
      FC.FinClass(fuel, inf, G, groups)
    case False{}:
      Unit

# The class obligations of every guess in a guess list, in guess order.
def FC.FinByGs(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{g, t}:
      FC.FinClassIf(fuel, inf, G,
        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
        Groups.groups_build(g, S, Nil{}))
      & FC.FinByGs(fuel, inf, G, S, t)
