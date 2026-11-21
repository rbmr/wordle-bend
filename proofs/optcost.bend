# The stored cost is the cost of the tree the machine returns.
#
# The solver keeps a `Best`: a tree and a numeric cost. The cost is built with
# the saturating sum over the class results, and infinity marks a class that ran
# out of fuel. This module proves that when the stored cost is finite it is the
# tree's own cost: the saturating sum is then a plain sum, and the returned tree
# is the node whose children are the class results, so the candidate count plus
# the class costs is exactly `Tree.cost`.
#
# The proof has the same shape as the validity induction: a fuel induction over
# the flat conjunction of jobs, and inside each job the guess fold. The class
# facts are `Bool` equalities below a finiteness hypothesis, so each is used at
# most once but can be passed around freely.
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
import ./solvevalid.bend as SV
import ./mainvalid.bend as MV

# Eliminate a computed pair with a continuation, so it is destructured once.
def OC.use_pair(-R: Type, -A: Type, -B: Type, p: A & B,
    k: A -> B -> R) -> R:
  match p:
    case (a, b):
      k(a, b)

# From a finite saturating total, the plain form of one accumulation step.
#
# The accumulator and the new part are finite in the only branch where the
# total can be finite, so the saturating sum there is the plain sum. The same
# branch also delivers the finiteness of the new part, which is what the class
# list of `plain_lt` needs.
def OC.step_facts(+inf: Nat, +acc: Nat, +c: Nat, +S: Nat, ga: Bool, gb: Bool,
    +ea: {ga == Nat.is_ge(acc, inf) : Bool},
    +eb: {gb == Nat.is_ge(c, inf) : Bool},
    h: {Nat.is_lt(Nat.add(Feedback.Bool.case(Nat, ga, inf,
          Feedback.Bool.case(Nat, gb, inf, Nat.add(acc, c))), S), inf)
        == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(acc, Nat.add(c, S)), inf) == True{} : Bool}
  & {Nat.is_lt(c, inf) == True{} : Bool}:
  match ga gb:
    case True{} _:
      +le : {Nat.is_le(inf, Nat.add(inf, S)) == True{} : Bool} =
        Fold.OQ.is_le_add_self_r(inf, S)
      +bad : {Nat.is_lt(inf, inf) == True{} : Bool} =
        NatProof.Nat.is_le_lt_trans(inf, Nat.add(inf, S), inf, le, h)
      Empty.absurd(
        {Nat.is_lt(Nat.add(acc, Nat.add(c, S)), inf) == True{} : Bool}
        & {Nat.is_lt(c, inf) == True{} : Bool},
        NatProof.Nat.not_lt_self(inf, bad))
    case False{} True{}:
      +le : {Nat.is_le(inf, Nat.add(inf, S)) == True{} : Bool} =
        Fold.OQ.is_le_add_self_r(inf, S)
      +bad : {Nat.is_lt(inf, inf) == True{} : Bool} =
        NatProof.Nat.is_le_lt_trans(inf, Nat.add(inf, S), inf, le, h)
      Empty.absurd(
        {Nat.is_lt(Nat.add(acc, Nat.add(c, S)), inf) == True{} : Bool}
        & {Nat.is_lt(c, inf) == True{} : Bool},
        NatProof.Nat.not_lt_self(inf, bad))
    case False{} False{}:
      +c_lt : {Nat.is_lt(c, inf) == True{} : Bool} =
        Sat.SB.lt_of_ge_false(c, inf,
          Equal.sym(Bool, False{}, Nat.is_ge(c, inf), eb))
      +e3 : {Nat.is_lt(Nat.add(acc, Nat.add(c, S)), inf) == True{} : Bool} =
        CBN.CB.lt_eq_l(inf, Nat.add(Nat.add(acc, c), S),
          Nat.add(acc, Nat.add(c, S)),
          NatProof.NatPrf.add_assoc(acc, c, S), h)
      (e3, c_lt)

# A finite saturating fold has a finite plain sum, and every part is finite.
def OC.plain_lt(+inf: Nat, +cs: +List<Nat>, +acc: Nat,
    e: {Nat.is_lt(OV.OV.sumL(inf, cs, acc), inf) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(acc, CBN.CB.sum(cs)), inf) == True{} : Bool}
  & CBS.CU.AllLt(inf, cs):
  match cs:
    case Nil{}:
      +e0 : {Nat.is_lt(Nat.add(acc, CBN.CB.sum(Nil{})), inf) == True{} : Bool} =
        CBN.CB.lt_eq_l(inf, acc, Nat.add(acc, 0n),
          Equal.sym(Nat, Nat.add(acc, 0n), acc, NatProof.NatPrf.add_zero(acc)), e)
      (e0, Unit{})
    case Con{c, t}:
      +e1 : {Nat.is_lt(OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c)), inf)
             == True{} : Bool} = e
      OC.use_pair(
        {Nat.is_lt(Nat.add(acc, CBN.CB.sum(Con{c, t})), inf) == True{} : Bool}
        & CBS.CU.AllLt(inf, Con{c, t}),
        {Nat.is_lt(Nat.add(SolveRef.sat_add(inf, acc, c), CBN.CB.sum(t)), inf)
         == True{} : Bool},
        CBS.CU.AllLt(inf, t),
        OC.plain_lt(inf, t, SolveRef.sat_add(inf, acc, c), e1),
        ih_lt => ih_all =>
          OC.use_pair(
            {Nat.is_lt(Nat.add(acc, CBN.CB.sum(Con{c, t})), inf) == True{} : Bool}
            & CBS.CU.AllLt(inf, Con{c, t}),
            {Nat.is_lt(Nat.add(acc, Nat.add(c, CBN.CB.sum(t))), inf) == True{}
             : Bool},
            {Nat.is_lt(c, inf) == True{} : Bool},
            OC.step_facts(inf, acc, c, CBN.CB.sum(t), Nat.is_ge(acc, inf),
              Nat.is_ge(c, inf), {==}, {==}, ih_lt),
            e3 => c_lt => (e3, (c_lt, ih_all))))

# The stored cost of a result is the cost of its tree, when the cost is finite.
def OC.CostOK(+inf: Nat, best: SolveRef.Best, +S: +List<+List<Nat>>) -> Type:
  @e: {Nat.is_lt(Eval.Eval.cost_of(best), inf) == True{} : Bool}
  -> {Tree.cost(Eval.Eval.tree_of(best), S) == Eval.Eval.cost_of(best) : Nat}

# A result moved along an equality of results.
def OC.transport(+inf: Nat, +b1: SolveRef.Best, +b2: SolveRef.Best,
    +S: +List<+List<Nat>>, e: {b1 == b2 : SolveRef.Best},
    c: OC.CostOK(inf, b1, S)) -> OC.CostOK(inf, b2, S):
  %e : OC.CostOK(inf, _, S)
  c

# `better` keeps the cost/tree correspondence when the candidate has it.
def OC.better_go(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    +tree: Tree.Tree, +cost: Nat, +S: +List<+List<Nat>>, b: Bool,
    +eb: {b == Nat.is_lt(candCost, cost) : Bool},
    hc: OC.CostOK(inf, SolveRef.Best{candTree, candCost}, S),
    hb: OC.CostOK(inf, SolveRef.Best{tree, cost}, S)) ->
  OC.CostOK(inf, Feedback.Bool.case(SolveRef.Best, b,
    SolveRef.Best{candTree, candCost}, SolveRef.Best{tree, cost}), S):
  match b:
    case True{}:
      hc
    case False{}:
      hb

def OC.better_cost(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    best: SolveRef.Best, +S: +List<+List<Nat>>,
    hc: OC.CostOK(inf, SolveRef.Best{candTree, candCost}, S),
    hb: OC.CostOK(inf, best, S)) ->
  OC.CostOK(inf, SolveRef.better(candCost, candTree, best), S):
  match best:
    case SolveRef.Best{+tree, +cost}:
      OC.better_go(inf, candCost, candTree, tree, cost, S,
        Nat.is_lt(candCost, cost), {==}, hc, hb)
