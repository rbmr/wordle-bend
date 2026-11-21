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

# A saturating fold that starts at infinity stays at infinity.
def OC.sumL_inf(+inf: Nat, +cs: +List<Nat>) ->
  {OV.OV.sumL(inf, cs, inf) == inf : Nat}:
  match cs:
    case Nil{}:
      {==}
    case Con{c, t}:
      +e1 : {SolveRef.sat_add(inf, inf, c) == inf : Nat} =
        OV.OV.sat_inf_l(inf, inf, c, Nat.ge_refl(inf))
      +e2 : {OV.OV.sumL(inf, t, SolveRef.sat_add(inf, inf, c))
             == OV.OV.sumL(inf, t, inf) : Nat} =
        Equal.cong(Nat, Nat, x => OV.OV.sumL(inf, t, x),
          SolveRef.sat_add(inf, inf, c), inf, e1)
      Equal.trans(Nat, OV.OV.sumL(inf, Con{c, t}, inf),
        OV.OV.sumL(inf, t, inf), inf,
        Equal.trans(Nat, OV.OV.sumL(inf, Con{c, t}, inf),
          OV.OV.sumL(inf, t, SolveRef.sat_add(inf, inf, c)),
          OV.OV.sumL(inf, t, inf), {==}, e2),
        OC.sumL_inf(inf, t))

# A finite saturating sum has two finite sides and is the plain sum.
def OC.sat_split(+inf: Nat, +a: Nat, +b: Nat, ga: Bool, gb: Bool,
    +ea: {ga == Nat.is_ge(a, inf) : Bool},
    +eb: {gb == Nat.is_ge(b, inf) : Bool},
    e: {Nat.is_lt(SolveRef.sat_add(inf, a, b), inf) == True{} : Bool}) ->
  {Nat.is_lt(a, inf) == True{} : Bool}
  & {Nat.is_lt(b, inf) == True{} : Bool}
  & {SolveRef.sat_add(inf, a, b) == Nat.add(a, b) : Nat}:
  match ga gb:
    case True{} _:
      +sat_inf : {SolveRef.sat_add(inf, a, b) == inf : Nat} =
        OV.OV.sat_inf_l(inf, a, b, Equal.sym(Bool, True{}, Nat.is_ge(a, inf), ea))
      +bad : {Nat.is_lt(inf, inf) == True{} : Bool} =
        CBN.CB.lt_eq_l(inf, SolveRef.sat_add(inf, a, b), inf, sat_inf, e)
      Empty.absurd(
        {Nat.is_lt(a, inf) == True{} : Bool}
        & {Nat.is_lt(b, inf) == True{} : Bool}
        & {SolveRef.sat_add(inf, a, b) == Nat.add(a, b) : Nat},
        NatProof.Nat.not_lt_self(inf, bad))
    case False{} True{}:
      +sat_inf : {SolveRef.sat_add(inf, a, b) == inf : Nat} =
        OV.OV.sat_inf_r(inf, a, b,
          Equal.sym(Bool, False{}, Nat.is_ge(a, inf), ea),
          Equal.sym(Bool, True{}, Nat.is_ge(b, inf), eb))
      +bad : {Nat.is_lt(inf, inf) == True{} : Bool} =
        CBN.CB.lt_eq_l(inf, SolveRef.sat_add(inf, a, b), inf, sat_inf, e)
      Empty.absurd(
        {Nat.is_lt(a, inf) == True{} : Bool}
        & {Nat.is_lt(b, inf) == True{} : Bool}
        & {SolveRef.sat_add(inf, a, b) == Nat.add(a, b) : Nat},
        NatProof.Nat.not_lt_self(inf, bad))
    case False{} False{}:
      +a_lt : {Nat.is_lt(a, inf) == True{} : Bool} =
        Sat.SB.lt_of_ge_false(a, inf,
          Equal.sym(Bool, False{}, Nat.is_ge(a, inf), ea))
      +b_lt : {Nat.is_lt(b, inf) == True{} : Bool} =
        Sat.SB.lt_of_ge_false(b, inf,
          Equal.sym(Bool, False{}, Nat.is_ge(b, inf), eb))
      (a_lt,
       (b_lt,
        OV.OV.sat_fin(inf, a, b, OV.OV.ge_false_of_lt(a, inf, a_lt),
          OV.OV.ge_false_of_lt(b, inf, b_lt))))

# The last regrouping of the plain bound and the fold equality.
def OC.plain_finish(+inf: Nat, +c: Nat, +t: +List<Nat>, +acc: Nat,
    c_lt: {Nat.is_lt(c, inf) == True{} : Bool},
    all_t: CBS.CU.AllLt(inf, t),
    acc_lt: {Nat.is_lt(acc, inf) == True{} : Bool},
    plain3: {Nat.is_lt(Nat.add(Nat.add(acc, c), CBN.CB.sum(t)), inf) == True{}
             : Bool},
    sumL2: {OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c))
            == Nat.add(Nat.add(acc, c), CBN.CB.sum(t)) : Nat}) ->
  {Nat.is_lt(Nat.add(acc, CBN.CB.sum(Con{c, t})), inf) == True{} : Bool}
  & CBS.CU.AllLt(inf, Con{c, t})
  & {OV.OV.sumL(inf, Con{c, t}, acc)
     == Nat.add(acc, CBN.CB.sum(Con{c, t})) : Nat}
  & {Nat.is_lt(acc, inf) == True{} : Bool}:
  +plain4 : {Nat.is_lt(Nat.add(acc, Nat.add(c, CBN.CB.sum(t))), inf) == True{}
             : Bool} =
    CBN.CB.lt_eq_l(inf, Nat.add(Nat.add(acc, c), CBN.CB.sum(t)),
      Nat.add(acc, Nat.add(c, CBN.CB.sum(t))),
      NatProof.NatPrf.add_assoc(acc, c, CBN.CB.sum(t)), plain3)
  +sumL3 : {OV.OV.sumL(inf, Con{c, t}, acc)
            == Nat.add(acc, Nat.add(c, CBN.CB.sum(t))) : Nat} =
    Equal.trans(Nat, OV.OV.sumL(inf, Con{c, t}, acc),
      Nat.add(Nat.add(acc, c), CBN.CB.sum(t)),
      Nat.add(acc, Nat.add(c, CBN.CB.sum(t))), sumL2,
      NatProof.NatPrf.add_assoc(acc, c, CBN.CB.sum(t)))
  (plain4, ((c_lt, all_t), (sumL3, acc_lt)))

# The plain bound after one saturating accumulation step.
def OC.plain_step(+inf: Nat, +c: Nat, +t: +List<Nat>, +acc: Nat,
    sat_lt: {Nat.is_lt(SolveRef.sat_add(inf, acc, c), inf) == True{} : Bool},
    plain_t: {Nat.is_lt(Nat.add(SolveRef.sat_add(inf, acc, c), CBN.CB.sum(t)), inf)
              == True{} : Bool},
    all_t: CBS.CU.AllLt(inf, t),
    sumL_t: {OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c))
             == Nat.add(SolveRef.sat_add(inf, acc, c), CBN.CB.sum(t)) : Nat}) ->
  {Nat.is_lt(Nat.add(acc, CBN.CB.sum(Con{c, t})), inf) == True{} : Bool}
  & CBS.CU.AllLt(inf, Con{c, t})
  & {OV.OV.sumL(inf, Con{c, t}, acc)
     == Nat.add(acc, CBN.CB.sum(Con{c, t})) : Nat}
  & {Nat.is_lt(acc, inf) == True{} : Bool}:
  OC.use_pair(
    {Nat.is_lt(Nat.add(acc, CBN.CB.sum(Con{c, t})), inf) == True{} : Bool}
    & CBS.CU.AllLt(inf, Con{c, t})
    & {OV.OV.sumL(inf, Con{c, t}, acc)
       == Nat.add(acc, CBN.CB.sum(Con{c, t})) : Nat}
    & {Nat.is_lt(acc, inf) == True{} : Bool},
    {Nat.is_lt(acc, inf) == True{} : Bool},
    {Nat.is_lt(c, inf) == True{} : Bool}
    & {SolveRef.sat_add(inf, acc, c) == Nat.add(acc, c) : Nat},
    OC.sat_split(inf, acc, c, Nat.is_ge(acc, inf), Nat.is_ge(c, inf), {==}, {==},
      sat_lt),
    acc_lt => r =>
      OC.use_pair(
        {Nat.is_lt(Nat.add(acc, CBN.CB.sum(Con{c, t})), inf) == True{} : Bool}
        & CBS.CU.AllLt(inf, Con{c, t})
        & {OV.OV.sumL(inf, Con{c, t}, acc)
           == Nat.add(acc, CBN.CB.sum(Con{c, t})) : Nat}
        & {Nat.is_lt(acc, inf) == True{} : Bool},
        {Nat.is_lt(c, inf) == True{} : Bool},
        {SolveRef.sat_add(inf, acc, c) == Nat.add(acc, c) : Nat},
        r,
        c_lt => sat_eq =>
          +clt : {Nat.is_lt(c, inf) == True{} : Bool} = c_lt
          +sa : {SolveRef.sat_add(inf, acc, c) == Nat.add(acc, c) : Nat} = sat_eq
          +plain3 : {Nat.is_lt(Nat.add(Nat.add(acc, c), CBN.CB.sum(t)), inf)
                     == True{} : Bool} =
            CBN.CB.lt_eq_l(inf,
              Nat.add(SolveRef.sat_add(inf, acc, c), CBN.CB.sum(t)),
              Nat.add(Nat.add(acc, c), CBN.CB.sum(t)),
              Equal.cong(Nat, Nat, x => Nat.add(x, CBN.CB.sum(t)),
                SolveRef.sat_add(inf, acc, c), Nat.add(acc, c), sa), plain_t)
          +sumL2 : {OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c))
                    == Nat.add(Nat.add(acc, c), CBN.CB.sum(t)) : Nat} =
            Equal.trans(Nat,
              OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c)),
              Nat.add(SolveRef.sat_add(inf, acc, c), CBN.CB.sum(t)),
              Nat.add(Nat.add(acc, c), CBN.CB.sum(t)), sumL_t,
              Equal.cong(Nat, Nat, x => Nat.add(x, CBN.CB.sum(t)),
                SolveRef.sat_add(inf, acc, c), Nat.add(acc, c), sa))
          OC.plain_finish(inf, c, t, acc, clt, all_t, acc_lt, plain3, sumL2)))

# A finite saturating fold: the plain bound, the parts, the equality with the
# plain sum, and the finiteness of the accumulator, from one traversal.
def OC.plain_both(+inf: Nat, +cs: +List<Nat>, +acc: Nat,
    e: {Nat.is_lt(OV.OV.sumL(inf, cs, acc), inf) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(acc, CBN.CB.sum(cs)), inf) == True{} : Bool}
  & CBS.CU.AllLt(inf, cs)
  & {OV.OV.sumL(inf, cs, acc) == Nat.add(acc, CBN.CB.sum(cs)) : Nat}
  & {Nat.is_lt(acc, inf) == True{} : Bool}:
  match cs:
    case Nil{}:
      +e0 : {Nat.is_lt(Nat.add(acc, CBN.CB.sum(Nil{})), inf) == True{} : Bool} =
        CBN.CB.lt_eq_l(inf, acc, Nat.add(acc, 0n),
          Equal.sym(Nat, Nat.add(acc, 0n), acc, NatProof.NatPrf.add_zero(acc)), e)
      (e0, (Unit{},
        (Equal.sym(Nat, Nat.add(acc, CBN.CB.sum(Nil{})), acc,
           NatProof.NatPrf.add_zero(acc)),
         CBS.CU.acc_part_lt(inf, acc, Nil{}, e0))))
    case Con{c, t}:
      OC.use_pair(
        {Nat.is_lt(Nat.add(acc, CBN.CB.sum(Con{c, t})), inf) == True{} : Bool}
        & CBS.CU.AllLt(inf, Con{c, t})
        & {OV.OV.sumL(inf, Con{c, t}, acc)
           == Nat.add(acc, CBN.CB.sum(Con{c, t})) : Nat}
        & {Nat.is_lt(acc, inf) == True{} : Bool},
        {Nat.is_lt(Nat.add(SolveRef.sat_add(inf, acc, c), CBN.CB.sum(t)), inf)
         == True{} : Bool},
        CBS.CU.AllLt(inf, t)
        & {OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c))
           == Nat.add(SolveRef.sat_add(inf, acc, c), CBN.CB.sum(t)) : Nat}
        & {Nat.is_lt(SolveRef.sat_add(inf, acc, c), inf) == True{} : Bool},
        OC.plain_both(inf, t, SolveRef.sat_add(inf, acc, c), e),
        plain_t => r2 =>
          OC.use_pair(
            {Nat.is_lt(Nat.add(acc, CBN.CB.sum(Con{c, t})), inf) == True{} : Bool}
            & CBS.CU.AllLt(inf, Con{c, t})
            & {OV.OV.sumL(inf, Con{c, t}, acc)
               == Nat.add(acc, CBN.CB.sum(Con{c, t})) : Nat}
            & {Nat.is_lt(acc, inf) == True{} : Bool},
            CBS.CU.AllLt(inf, t),
            {OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c))
             == Nat.add(SolveRef.sat_add(inf, acc, c), CBN.CB.sum(t)) : Nat}
            & {Nat.is_lt(SolveRef.sat_add(inf, acc, c), inf) == True{} : Bool},
            r2,
            all_t => r3 =>
              OC.use_pair(
                {Nat.is_lt(Nat.add(acc, CBN.CB.sum(Con{c, t})), inf) == True{}
                 : Bool}
                & CBS.CU.AllLt(inf, Con{c, t})
                & {OV.OV.sumL(inf, Con{c, t}, acc)
                   == Nat.add(acc, CBN.CB.sum(Con{c, t})) : Nat}
                & {Nat.is_lt(acc, inf) == True{} : Bool},
                {OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c))
                 == Nat.add(SolveRef.sat_add(inf, acc, c), CBN.CB.sum(t)) : Nat},
                {Nat.is_lt(SolveRef.sat_add(inf, acc, c), inf) == True{} : Bool},
                r3,
                sumL_t => sat_lt =>
                  OC.plain_step(inf, c, t, acc, sat_lt, plain_t, all_t, sumL_t))))
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
