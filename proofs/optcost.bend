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
import ./groupcost.bend as GC
import ./nodecost.bend as NodeCost
import ./depth.bend as DepthProof
import ./optimalvalue.bend as OV
import ./optsum.bend as Sums
import ./optfold.bend as Fold
import ./optnode.bend as Node
import ./optind.bend as Ind
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
# The tree of a result costs at most the stored cost, when the cost is finite.
def OC.CostOK(+inf: Nat, best: SolveRef.Best, +S: +List<+List<Nat>>) -> Type:
  @e: {Nat.is_lt(Eval.Eval.cost_of(best), inf) == True{} : Bool}
  -> {Nat.is_le(Tree.cost(Eval.Eval.tree_of(best), S), Eval.Eval.cost_of(best))
      == True{} : Bool}

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

# The class results of one group list, with their cost/tree correspondence.
def OC.CClass(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          OC.CostOK(inf, SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
            Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()), ws)
          & OC.CClass(p, inf, G, rest)

# A bumped default is at most one plus the default.
def OC.bump_default_le(m: Maybe<Nat>) ->
  {Nat.is_le(Maybe.default(&1, Nat, Tree.depth.bump(m), 0n),
             Nat.add(1n, Maybe.default(&1, Nat, m, 0n))) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      NatProof.Nat.is_le_refl(Nat.add(1n, n))

# One candidate's depth at a node is at most one plus its child's cost.
def OC.depth_le_kid(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    b: Bool, +eb: {b == Feedback.word_eq(g, w) : Bool}) ->
  {Nat.is_le(Maybe.default(&1, Nat, NodeCost.NodeCost.node_depth_of(g, kids, w, b), 0n),
             Nat.add(1n, NodeCost.NodeCost.kid_cost_of(g, kids, w, b))) == True{}
   : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      +fb : +List<Feedback.Color> = Feedback.feedback(g, w)
      +e_go : {Maybe.default(&1, Nat, Tree.depth.go(kids, fb, w), 0n)
               == NodeCost.NodeCost.maybe_depth(Tree.lookup(fb, kids), w) : Nat} =
        Equal.trans(Nat, Maybe.default(&1, Nat, Tree.depth.go(kids, fb, w), 0n),
          Maybe.default(&1, Nat,
            DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w), 0n),
          NodeCost.NodeCost.maybe_depth(Tree.lookup(fb, kids), w),
          Equal.cong(Maybe<Nat>, Nat, x => Maybe.default(&1, Nat, x, 0n),
            Tree.depth.go(kids, fb, w),
            DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w),
            DepthProof.DepthProof.depth_go_lookup(kids, fb, w)),
          Equal.sym(Nat, NodeCost.NodeCost.maybe_depth(Tree.lookup(fb, kids), w),
            Maybe.default(&1, Nat,
              DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w), 0n),
            NodeCost.NodeCost.maybe_depth_default(Tree.lookup(fb, kids), w)))
      +le_go : {Nat.is_le(Maybe.default(&1, Nat, Tree.depth.go(kids, fb, w), 0n),
                   NodeCost.NodeCost.maybe_depth(Tree.lookup(fb, kids), w))
                 == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(
          Maybe.default(&1, Nat, Tree.depth.go(kids, fb, w), 0n),
          Maybe.default(&1, Nat, Tree.depth.go(kids, fb, w), 0n),
          NodeCost.NodeCost.maybe_depth(Tree.lookup(fb, kids), w), e_go,
          NatProof.Nat.is_le_refl(Maybe.default(&1, Nat, Tree.depth.go(kids, fb, w), 0n)))
      +e_add : {Nat.is_le(
                  Nat.add(1n, Maybe.default(&1, Nat, Tree.depth.go(kids, fb, w), 0n)),
                  Nat.add(1n, NodeCost.NodeCost.maybe_depth(Tree.lookup(fb, kids), w)))
                == True{} : Bool} =
        NatProof.Nat.is_le_add_l(Maybe.default(&1, Nat, Tree.depth.go(kids, fb, w), 0n),
          NodeCost.NodeCost.maybe_depth(Tree.lookup(fb, kids), w), 1n, le_go)
      NatProof.Nat.is_le_trans(
        Maybe.default(&1, Nat, Tree.depth.bump(Tree.depth.go(kids, fb, w)), 0n),
        Nat.add(1n, Maybe.default(&1, Nat, Tree.depth.go(kids, fb, w), 0n)),
        Nat.add(1n, NodeCost.NodeCost.maybe_depth(Tree.lookup(fb, kids), w)),
        OC.bump_default_le(Tree.depth.go(kids, fb, w)), e_add)

# The node cost is at most the candidate count plus the children's cost.
def OC.cost_node_le(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>) ->
  {Nat.is_le(Tree.cost(Tree.Node{g, kids}, S),
             Nat.add(Groups.len_words(S), NodeCost.NodeCost.kid_sum(g, kids, S)))
   == True{} : Bool}:
  match S:
    case Nil{}:
      NatProof.Nat.is_le_refl(0n)
    case Con{h, t}:
      +ih : {Nat.is_le(Tree.cost(Tree.Node{g, kids}, t),
                 Nat.add(Groups.len_words(t),
                   NodeCost.NodeCost.kid_sum(g, kids, t))) == True{} : Bool} =
        OC.cost_node_le(g, kids, t)
      +hd : {Nat.is_le(Maybe.default(&1, Nat, Tree.depth(Tree.Node{g, kids}, h), 0n),
                 Nat.add(1n, NodeCost.NodeCost.kid_cost(g, kids, h)))
               == True{} : Bool} =
        OC.depth_le_kid(g, kids, h, Feedback.word_eq(g, h), {==})
      +sum : {Nat.is_le(
                Nat.add(Maybe.default(&1, Nat, Tree.depth(Tree.Node{g, kids}, h), 0n),
                  Tree.cost(Tree.Node{g, kids}, t)),
                Nat.add(Nat.add(1n, NodeCost.NodeCost.kid_cost(g, kids, h)),
                  Nat.add(Groups.len_words(t),
                    NodeCost.NodeCost.kid_sum(g, kids, t)))) == True{} : Bool} =
        CBN.CB.is_le_add(
          Maybe.default(&1, Nat, Tree.depth(Tree.Node{g, kids}, h), 0n),
          Nat.add(1n, NodeCost.NodeCost.kid_cost(g, kids, h)),
          Tree.cost(Tree.Node{g, kids}, t),
          Nat.add(Groups.len_words(t), NodeCost.NodeCost.kid_sum(g, kids, t)),
          hd, ih)
      Fold.OQ.le_cong_r(
        Nat.add(Maybe.default(&1, Nat, Tree.depth(Tree.Node{g, kids}, h), 0n),
          Tree.cost(Tree.Node{g, kids}, t)),
        Nat.add(Nat.add(1n, NodeCost.NodeCost.kid_cost(g, kids, h)),
          Nat.add(Groups.len_words(t), NodeCost.NodeCost.kid_sum(g, kids, t))),
        Nat.add(Groups.len_words(Con{h, t}),
          NodeCost.NodeCost.kid_sum(g, kids, Con{h, t})),
        CBN.CB.add4(1n, NodeCost.NodeCost.kid_cost(g, kids, h),
          Groups.len_words(t), NodeCost.NodeCost.kid_sum(g, kids, t)), sum)

# The class costs fit the stored class costs pointwise.
def OC.class_costs_le(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +groups: +List<Groups.Group>, +inf: Nat,
    cc: OC.CClass(p, inf, G, groups),
    cl: CBS.CU.AllLt(inf, Sat.SB.child_costs(p, G, groups, inf))) ->
  CBN.CB.PointLe(CBK.CBK.class_costs(p, G, S, groups, inf),
    Sat.SB.child_costs(p, G, groups, inf)):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          (ch, ct) = cc
          (lh, lt) = cl
          (ch(lh), OC.class_costs_le(p, G, S, rest, inf, ct, lt))

# The children's cost of a finished node is at most the stored class costs.
def OC.kid_sum_le(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat,
    cc: OC.CClass(p, inf, G, Groups.groups_build(g, S, Nil{})),
    cl: CBS.CU.AllLt(inf, Sat.SB.child_costs(p, G,
          Groups.groups_build(g, S, Nil{}), inf)),
    +kids_eq: {SolveRef.rev_kids(CH.CH.kids_of(Eval.Eval.items(p, G, S, g,
                 Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), Nil{})
               == CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf)
               : +List<Tree.Child>}) ->
  {Nat.is_le(NodeCost.NodeCost.kid_sum(g, SolveRef.rev_kids(CH.CH.kids_of(
     Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
     Nil{}), S),
     CBN.CB.sum(Sat.SB.child_costs(p, G, Groups.groups_build(g, S, Nil{}), inf)))
   == True{} : Bool}:
  +gb : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
  +rev : +List<Tree.Child> = SolveRef.rev_kids(CH.CH.kids_of(
    Eval.Eval.items(p, G, S, g, gb, Nil{}, 0n, inf)), Nil{})
  +ch : +List<Tree.Child> = CH.CH.children(p, G, S, gb, inf)
  +e1 : {NodeCost.NodeCost.kid_sum(g, rev, S) == GC.GC.Total(rev, gb) : Nat} =
    Equal.sym(Nat, GC.GC.Total(rev, gb), NodeCost.NodeCost.kid_sum(g, rev, S),
      GC.GC.groups_build_total(g, rev, S))
  +e2 : {GC.GC.Total(rev, gb) == GC.GC.Total(ch, gb) : Nat} =
    Equal.cong(+List<Tree.Child>, Nat, l => GC.GC.Total(l, gb), rev, ch, kids_eq)
  +e3 : {GC.GC.Total(ch, gb) == CBN.CB.sum(CBK.CBK.class_costs(p, G, S, gb, inf))
         : Nat} =
    CBK.CBK.total_children(p, G, S, gb, inf, CBK.CBK.distinctB_build(g, S))
  +kidsum_eq : {NodeCost.NodeCost.kid_sum(g, rev, S)
                == CBN.CB.sum(CBK.CBK.class_costs(p, G, S, gb, inf)) : Nat} =
    Equal.trans(Nat, NodeCost.NodeCost.kid_sum(g, rev, S), GC.GC.Total(rev, gb),
      CBN.CB.sum(CBK.CBK.class_costs(p, G, S, gb, inf)), e1,
      Equal.trans(Nat, GC.GC.Total(rev, gb), GC.GC.Total(ch, gb),
        CBN.CB.sum(CBK.CBK.class_costs(p, G, S, gb, inf)), e2, e3))
  pts : CBN.CB.PointLe(CBK.CBK.class_costs(p, G, S, gb, inf),
    Sat.SB.child_costs(p, G, gb, inf)) =
    OC.class_costs_le(p, G, S, gb, inf, cc, cl)
  +sle : {Nat.is_le(CBN.CB.sum(CBK.CBK.class_costs(p, G, S, gb, inf)),
                    CBN.CB.sum(Sat.SB.child_costs(p, G, gb, inf))) == True{}
          : Bool} =
    CBN.CB.sum_le(CBK.CBK.class_costs(p, G, S, gb, inf),
      Sat.SB.child_costs(p, G, gb, inf), pts)
  Fold.OQ.le_cong_l(NodeCost.NodeCost.kid_sum(g, rev, S),
    CBN.CB.sum(CBK.CBK.class_costs(p, G, S, gb, inf)),
    CBN.CB.sum(Sat.SB.child_costs(p, G, gb, inf)), kidsum_eq, sle)

# The node of a class fold, spelled with the folded child list.
def OC.ks_tree_unfold(+g: +List<Nat>, ks: Eval.KS) ->
  {Fold.OQ.ks_tree(g, ks)
   == Tree.Node{g, SolveRef.rev_kids(CH.CH.kids_of(ks), Nil{})} : Tree.Tree}:
  match ks:
    case Eval.KS{kids, sum}:
      {==}

# The candidate `Best` of one guess carries the cost of its tree, when finite.
def OC.cand_cost_ok(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>,
    cc: OC.CClass(p, inf, G, Groups.groups_build(g, S, Nil{}))) ->
  OC.CostOK(inf,
    SolveRef.Best{
      Fold.OQ.ks_tree(g, Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}),
        Nil{}, 0n, inf)),
      Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
        Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf))}, S):
  e =>
    +gb : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
    +items : Eval.KS = Eval.Eval.items(p, G, S, g, gb, Nil{}, 0n, inf)
    +cs : +List<Nat> = Sat.SB.child_costs(p, G, gb, inf)
    +rev : +List<Tree.Child> = SolveRef.rev_kids(CH.CH.kids_of(items), Nil{})
    +eSat : {Nat.is_lt(SolveRef.sat_add(inf, Groups.len_words(S),
               Sat.SB.ks_sum(items)), inf) == True{} : Bool} =
      CBN.CB.lt_eq_l(inf, Fold.OQ.ks_cost(inf, S, items),
        SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(items)),
        Node.OQ.ks_cost_unfold(inf, S, items), e)
    +es : {Nat.is_lt(Sat.SB.ks_sum(items), inf) == True{} : Bool} =
      Sat.SB.sat_add_lt_r(inf, Groups.len_words(S), Sat.SB.ks_sum(items), eSat)
    +esL : {Nat.is_lt(OV.OV.sumL(inf, cs, 0n), inf) == True{} : Bool} =
      CBN.CB.lt_eq_l(inf, Sat.SB.ks_sum(items), OV.OV.sumL(inf, cs, 0n),
        OV.OV.sum_fold(p, G, S, g, gb, Nil{}, 0n, inf), es)
    OC.use_pair(
      {Nat.is_le(Tree.cost(Fold.OQ.ks_tree(g, items), S),
       Fold.OQ.ks_cost(inf, S, items)) == True{} : Bool},
      {Nat.is_lt(Nat.add(0n, CBN.CB.sum(cs)), inf) == True{} : Bool},
      CBS.CU.AllLt(inf, cs)
      & {OV.OV.sumL(inf, cs, 0n) == Nat.add(0n, CBN.CB.sum(cs)) : Nat}
      & {Nat.is_lt(0n, inf) == True{} : Bool},
      OC.plain_both(inf, cs, 0n, esL),
      _tot => r =>
        OC.use_pair(
          {Nat.is_le(Tree.cost(Fold.OQ.ks_tree(g, items), S),
       Fold.OQ.ks_cost(inf, S, items)) == True{} : Bool},
          CBS.CU.AllLt(inf, cs),
          {OV.OV.sumL(inf, cs, 0n) == Nat.add(0n, CBN.CB.sum(cs)) : Nat}
          & {Nat.is_lt(0n, inf) == True{} : Bool},
          r,
          all => r2 =>
            OC.use_pair(
              {Nat.is_le(Tree.cost(Fold.OQ.ks_tree(g, items), S),
       Fold.OQ.ks_cost(inf, S, items)) == True{} : Bool},
              {OV.OV.sumL(inf, cs, 0n) == Nat.add(0n, CBN.CB.sum(cs)) : Nat},
              {Nat.is_lt(0n, inf) == True{} : Bool},
              r2,
              plain => _zlt =>
                +sum_eq : {Sat.SB.ks_sum(items) == CBN.CB.sum(cs) : Nat} =
                  Equal.trans(Nat, Sat.SB.ks_sum(items), OV.OV.sumL(inf, cs, 0n),
                    CBN.CB.sum(cs),
                    OV.OV.sum_fold(p, G, S, g, gb, Nil{}, 0n, inf),
                    Equal.trans(Nat, OV.OV.sumL(inf, cs, 0n),
                      Nat.add(0n, CBN.CB.sum(cs)), CBN.CB.sum(cs), plain, {==}))
                +e1 : {CH.CH.kids_of(items)
                        == SolveRef.rev_kids(CH.CH.children(p, G, S, gb, inf), Nil{})
                        : +List<Tree.Child>} =
                  CH.CH.items_kids(p, G, S, g, gb, Nil{}, 0n, inf)
                +e2 : {rev == SolveRef.rev_kids(SolveRef.rev_kids(
                          CH.CH.children(p, G, S, gb, inf), Nil{}), Nil{})
                        : +List<Tree.Child>} =
                  Equal.cong(+List<Tree.Child>, +List<Tree.Child>,
                    l => SolveRef.rev_kids(l, Nil{}), CH.CH.kids_of(items),
                    SolveRef.rev_kids(CH.CH.children(p, G, S, gb, inf), Nil{}), e1)
                +e3 : {SolveRef.rev_kids(SolveRef.rev_kids(
                          CH.CH.children(p, G, S, gb, inf), Nil{}), Nil{})
                        == CH.CH.children(p, G, S, gb, inf) : +List<Tree.Child>} =
                  CH.CH.rev_rev(CH.CH.children(p, G, S, gb, inf))
                +kids_eq : {rev == CH.CH.children(p, G, S, gb, inf)
                            : +List<Tree.Child>} =
                  Equal.trans(+List<Tree.Child>, rev,
                    SolveRef.rev_kids(SolveRef.rev_kids(
                      CH.CH.children(p, G, S, gb, inf), Nil{}), Nil{}),
                    CH.CH.children(p, G, S, gb, inf), e2, e3)
                +kle : {Nat.is_le(NodeCost.NodeCost.kid_sum(g, rev, S),
                           CBN.CB.sum(cs)) == True{} : Bool} =
                  OC.kid_sum_le(p, G, S, g, inf, cc, all, kids_eq)
                +cle : {Nat.is_le(Tree.cost(Tree.Node{g, rev}, S),
                           Nat.add(Groups.len_words(S),
                             NodeCost.NodeCost.kid_sum(g, rev, S))) == True{}
                        : Bool} =
                  OC.cost_node_le(g, rev, S)
                +cle2 : {Nat.is_le(Tree.cost(Tree.Node{g, rev}, S),
                            Nat.add(Groups.len_words(S), CBN.CB.sum(cs)))
                         == True{} : Bool} =
                  NatProof.Nat.is_le_trans(Tree.cost(Tree.Node{g, rev}, S),
                    Nat.add(Groups.len_words(S),
                      NodeCost.NodeCost.kid_sum(g, rev, S)),
                    Nat.add(Groups.len_words(S), CBN.CB.sum(cs)), cle,
                    NatProof.Nat.is_le_add_l(NodeCost.NodeCost.kid_sum(g, rev, S),
                      CBN.CB.sum(cs), Groups.len_words(S), kle))
                +n_lt : {Nat.is_lt(Groups.len_words(S), inf) == True{} : Bool} =
                  Sat.SB.sat_add_lt_l(inf, Groups.len_words(S),
                    Sat.SB.ks_sum(items), eSat)
                +sum_lt : {Nat.is_lt(Sat.SB.ks_sum(items), inf) == True{} : Bool} = es
                +sat_eq : {SolveRef.sat_add(inf, Groups.len_words(S),
                             Sat.SB.ks_sum(items))
                           == Nat.add(Groups.len_words(S), CBN.CB.sum(cs)) : Nat} =
                  Equal.trans(Nat,
                    SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(items)),
                    Nat.add(Groups.len_words(S), Sat.SB.ks_sum(items)),
                    Nat.add(Groups.len_words(S), CBN.CB.sum(cs)),
                    OV.OV.sat_fin(inf, Groups.len_words(S), Sat.SB.ks_sum(items),
                      OV.OV.ge_false_of_lt(Groups.len_words(S), inf, n_lt),
                      OV.OV.ge_false_of_lt(Sat.SB.ks_sum(items), inf, sum_lt)),
                    Equal.cong(Nat, Nat, x => Nat.add(Groups.len_words(S), x),
                      Sat.SB.ks_sum(items), CBN.CB.sum(cs), sum_eq))
                +kc_eq : {Fold.OQ.ks_cost(inf, S, items)
                          == Nat.add(Groups.len_words(S), CBN.CB.sum(cs)) : Nat} =
                  Equal.trans(Nat, Fold.OQ.ks_cost(inf, S, items),
                    SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(items)),
                    Nat.add(Groups.len_words(S), CBN.CB.sum(cs)),
                    Node.OQ.ks_cost_unfold(inf, S, items), sat_eq)
                +cle3 : {Nat.is_le(Tree.cost(Tree.Node{g, rev}, S),
                            Fold.OQ.ks_cost(inf, S, items)) == True{} : Bool} =
                  Fold.OQ.le_cong_r(Tree.cost(Tree.Node{g, rev}, S),
                    Nat.add(Groups.len_words(S), CBN.CB.sum(cs)),
                    Fold.OQ.ks_cost(inf, S, items),
                    Equal.sym(Nat, Fold.OQ.ks_cost(inf, S, items),
                      Nat.add(Groups.len_words(S), CBN.CB.sum(cs)), kc_eq), cle2)
                Fold.OQ.le_cong_l(Tree.cost(Fold.OQ.ks_tree(g, items), S),
                  Tree.cost(Tree.Node{g, rev}, S),
                  Fold.OQ.ks_cost(inf, S, items),
                  Equal.cong(Tree.Tree, Nat, t => Tree.cost(t, S),
                    Fold.OQ.ks_tree(g, items), Tree.Node{g, rev},
                    OC.ks_tree_unfold(g, items)),
                  cle3))))

def OC.CJob(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>) -> Type:
  OC.CostOK(inf, SolveRef.step(fuel, SolveRef.mk_schedule(G, S), G, S, inf,
    Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()), S)

# The conjunction of the job obligations over a list of candidate lists.
def OC.CFlat(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    jobs: +List<+List<+List<Nat>>>) -> Type:
  match jobs:
    case Nil{}:
      Unit
    case Con{S, t}:
      OC.CJob(fuel, inf, G, S) & OC.CFlat(fuel, inf, G, t)

# The class results of one guess, only when the guess is usable.
def OC.CClassIf(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>, b: Bool,
    +groups: +List<Groups.Group>) -> Type:
  match b:
    case True{}:
      OC.CClass(fuel, inf, G, groups)
    case False{}:
      Unit

# The class results of every guess in a guess list, in guess order.
def OC.CByGs(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{g, t}:
      OC.CClassIf(fuel, inf, G,
        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
        Groups.groups_build(g, S, Nil{}))
      & OC.CByGs(fuel, inf, G, S, t)

# The zero-fuel fold over a cost-zero accumulator stays at cost zero.
def OC.zero_fold_cost(+G: +List<+List<Nat>>, +inf: Nat, +gs: +List<+List<Nat>>,
    +tree: Tree.Tree,
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool}) ->
  {Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, gs,
     SolveRef.Best{tree, 0n})) == 0n : Nat}:
  match gs:
    case Nil{}:
      {==}
    case Con{g, t}:
      +e1 : {SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(Nil{}),
                SolveRef.Best{tree, 0n}) == SolveRef.Best{tree, 0n}
             : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          SolveRef.finish_guess(inf, g, Nil{}, 0n, 0n,
            SolveRef.Best{tree, 0n}),
          SolveRef.better(0n, Tree.Node{g, Nil{}}, SolveRef.Best{tree, 0n}),
          SolveRef.Best{tree, 0n},
          Equal.cong(Nat, SolveRef.Best,
            x => SolveRef.better(x, Tree.Node{g, SolveRef.rev_kids(Nil{}, Nil{})},
              SolveRef.Best{tree, 0n}),
            SolveRef.sat_add(inf, 0n, 0n), 0n, Ind.OQ.sat_zero(inf, hz)),
          Ind.OQ.better0_keep(Tree.Node{g, Nil{}}, tree))
      +eq : {Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, t,
                SolveRef.finish_guess(inf, g, Nil{}, 0n,
                  Groups.len_words(Nil{}), SolveRef.Best{tree, 0n})))
              == Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, t,
                   SolveRef.Best{tree, 0n})) : Nat} =
        Equal.cong(SolveRef.Best, Nat,
          b => Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, t, b)),
          SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(Nil{}),
            SolveRef.Best{tree, 0n}),
          SolveRef.Best{tree, 0n}, e1)
      Equal.trans(Nat,
        Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, g <> t,
          SolveRef.Best{tree, 0n})),
        Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, t,
          SolveRef.Best{tree, 0n})),
        0n, eq, OC.zero_fold_cost(G, inf, t, tree, hz))

# The first guess of a zero-fuel fold replaces the dummy accumulator by a
# cost-zero node.
def OC.zero_first_cost(+G: +List<+List<Nat>>, +inf: Nat,
    +g: +List<Nat>, +t: +List<+List<Nat>>,
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool}) ->
  {Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, g <> t,
     Eval.Eval.dummy_inf(inf))) == 0n : Nat}:
  +fin_eq : {SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(Nil{}),
                 Eval.Eval.dummy_inf(inf))
              == SolveRef.Best{Tree.Node{g, Nil{}}, 0n} : SolveRef.Best} =
    Equal.trans(SolveRef.Best,
      SolveRef.finish_guess(inf, g, Nil{}, 0n, 0n, Eval.Eval.dummy_inf(inf)),
      SolveRef.better(0n, Tree.Node{g, Nil{}}, Eval.Eval.dummy_inf(inf)),
      SolveRef.Best{Tree.Node{g, Nil{}}, 0n},
      Equal.cong(Nat, SolveRef.Best,
        x => SolveRef.better(x, Tree.Node{g, SolveRef.rev_kids(Nil{}, Nil{})},
          Eval.Eval.dummy_inf(inf)),
        SolveRef.sat_add(inf, 0n, 0n), 0n, Ind.OQ.sat_zero(inf, hz)),
      Ind.OQ.better0_eq(inf, Tree.Node{g, Nil{}}, hz))
  +e1 : {Eval.Eval.guesses(0n, G, Nil{}, inf, g <> t, Eval.Eval.dummy_inf(inf))
          == Eval.Eval.guesses(0n, G, Nil{}, inf, t,
               SolveRef.Best{Tree.Node{g, Nil{}}, 0n}) : SolveRef.Best} =
    Equal.trans(SolveRef.Best,
      Eval.Eval.guesses(0n, G, Nil{}, inf, g <> t, Eval.Eval.dummy_inf(inf)),
      Eval.Eval.guesses(0n, G, Nil{}, inf, t,
        SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(Nil{}),
          Eval.Eval.dummy_inf(inf))),
      Eval.Eval.guesses(0n, G, Nil{}, inf, t,
        SolveRef.Best{Tree.Node{g, Nil{}}, 0n}),
      {==},
      Equal.cong(SolveRef.Best, SolveRef.Best,
        b => Eval.Eval.guesses(0n, G, Nil{}, inf, t, b),
        SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(Nil{}),
          Eval.Eval.dummy_inf(inf)),
        SolveRef.Best{Tree.Node{g, Nil{}}, 0n}, fin_eq))
  Equal.trans(Nat,
    Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, g <> t,
      Eval.Eval.dummy_inf(inf))),
    Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, t,
      SolveRef.Best{Tree.Node{g, Nil{}}, 0n})),
    0n,
    Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
      Eval.Eval.guesses(0n, G, Nil{}, inf, g <> t, Eval.Eval.dummy_inf(inf)),
      Eval.Eval.guesses(0n, G, Nil{}, inf, t,
        SolveRef.Best{Tree.Node{g, Nil{}}, 0n}), e1),
    OC.zero_fold_cost(G, inf, t, Tree.Node{g, Nil{}}, hz))

# Zero fuel at the empty candidate list: the search result is cost zero, or its
# stored cost is infinite (only when there are no guesses at all).
def OC.cjob_zero_nil(+inf: Nat, +G: +List<+List<Nat>>,
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool}) ->
  OC.CJob(0n, inf, G, Nil{}):
  match G:
    case Nil{}:
      e =>
        +eb : {SolveRef.step(0n, SolveRef.mk_schedule(Nil{}, Nil{}), Nil{}, Nil{},
                  inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
                  Eval.Eval.dummy_zero())
                == Eval.Eval.guesses(0n, Nil{}, Nil{}, inf, Nil{},
                     Eval.Eval.dummy_inf(inf)) : SolveRef.Best} =
          Eval.Eval.guesses_zero(Nil{}, inf, Nil{}, Eval.Eval.dummy_inf(inf))
        +ec : {Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(Nil{}, Nil{}),
                    Nil{}, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
                    Eval.Eval.dummy_zero()))
                == Eval.Eval.cost_of(Eval.Eval.guesses(0n, Nil{}, Nil{}, inf, Nil{},
                     Eval.Eval.dummy_inf(inf))) : Nat} =
          Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
            SolveRef.step(0n, SolveRef.mk_schedule(Nil{}, Nil{}), Nil{}, Nil{}, inf,
              Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()),
            Eval.Eval.guesses(0n, Nil{}, Nil{}, inf, Nil{}, Eval.Eval.dummy_inf(inf)),
            eb)
        +bad : {Nat.is_lt(inf, inf) == True{} : Bool} =
          CBN.CB.lt_eq_l(inf,
            Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(Nil{}, Nil{}),
              Nil{}, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
              Eval.Eval.dummy_zero())),
            inf,
            Equal.trans(Nat,
              Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(Nil{}, Nil{}),
                Nil{}, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
                Eval.Eval.dummy_zero())),
              Eval.Eval.cost_of(Eval.Eval.guesses(0n, Nil{}, Nil{}, inf, Nil{},
                Eval.Eval.dummy_inf(inf))),
              inf, ec, {==}), e)
        Empty.absurd(
          {Nat.is_le(Tree.cost(Eval.Eval.tree_of(SolveRef.step(0n,
             SolveRef.mk_schedule(Nil{}, Nil{}), Nil{}, Nil{}, inf, Nil{}, Nil{},
             0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())), Nil{}),
             Eval.Eval.cost_of(SolveRef.step(0n,
               SolveRef.mk_schedule(Nil{}, Nil{}), Nil{}, Nil{}, inf, Nil{},
               Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())))
           == True{} : Bool},
          NatProof.Nat.not_lt_self(inf, bad))
    case Con{g, t}:
      e =>
        +eb : {SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{},
                  inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
                  Eval.Eval.dummy_zero())
                == Eval.Eval.guesses(0n, g <> t, Nil{}, inf, g <> t,
                     Eval.Eval.dummy_inf(inf)) : SolveRef.Best} =
          Eval.Eval.guesses_zero(g <> t, inf, g <> t, Eval.Eval.dummy_inf(inf))
        +ec : {Eval.Eval.cost_of(SolveRef.step(0n,
                    SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf,
                    Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
                    Eval.Eval.dummy_zero()))
                == Eval.Eval.cost_of(Eval.Eval.guesses(0n, g <> t, Nil{}, inf,
                     g <> t, Eval.Eval.dummy_inf(inf))) : Nat} =
          Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
            SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{},
              inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
              Eval.Eval.dummy_zero()),
            Eval.Eval.guesses(0n, g <> t, Nil{}, inf, g <> t,
              Eval.Eval.dummy_inf(inf)), eb)
        +ec2 : {Eval.Eval.cost_of(Eval.Eval.guesses(0n, g <> t, Nil{}, inf, g <> t,
                   Eval.Eval.dummy_inf(inf))) == 0n : Nat} =
          OC.zero_first_cost(g <> t, inf, g, t, hz)
        +ec3 : {Eval.Eval.cost_of(SolveRef.step(0n,
                   SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf,
                   Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
                   Eval.Eval.dummy_zero())) == 0n : Nat} =
          Equal.trans(Nat,
            Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}),
              g <> t, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
              Eval.Eval.dummy_zero())),
            Eval.Eval.cost_of(Eval.Eval.guesses(0n, g <> t, Nil{}, inf, g <> t,
              Eval.Eval.dummy_inf(inf))),
            0n, ec, ec2)
        +e0 : {Tree.cost(Eval.Eval.tree_of(SolveRef.step(0n,
                   SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf,
                   Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
                   Eval.Eval.dummy_zero())), Nil{}) == 0n : Nat} = {==}
        +l1 : {Nat.is_le(Tree.cost(Eval.Eval.tree_of(SolveRef.step(0n,
                    SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf,
                    Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
                    Eval.Eval.dummy_zero())), Nil{}), 0n) == True{} : Bool} =
          NatProof.Nat.is_le_eq_l(0n, 0n,
            Tree.cost(Eval.Eval.tree_of(SolveRef.step(0n,
              SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf, Nil{}, Nil{},
              0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())), Nil{}),
            Equal.sym(Nat, Tree.cost(Eval.Eval.tree_of(SolveRef.step(0n,
              SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf, Nil{}, Nil{},
              0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())), Nil{}), 0n, e0),
            NatProof.Nat.is_le_refl(0n))
        NatProof.Nat.is_le_eq_r(
          Tree.cost(Eval.Eval.tree_of(SolveRef.step(0n,
            SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf, Nil{}, Nil{},
            0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())), Nil{}),
          0n,
          Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}),
            g <> t, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
            Eval.Eval.dummy_zero())),
          Equal.sym(Nat, Eval.Eval.cost_of(SolveRef.step(0n,
            SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf, Nil{}, Nil{},
            0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())), 0n, ec3),
          l1)

# A job moved to an equal candidate list.
def OC.cjob_transport(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S1: +List<+List<Nat>>, +S2: +List<+List<Nat>>,
    e: {S1 == S2 : +List<+List<Nat>>},
    c: OC.CJob(fuel, inf, G, S1)) -> OC.CJob(fuel, inf, G, S2):
  %e : OC.CJob(fuel, inf, G, _)
  c

# A zero-length candidate list is empty, so its job is the zero-fuel base case.
def OC.cjob_zero(+inf: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    le: {Nat.is_le(Groups.len_words(S), 0n) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool}) -> OC.CJob(0n, inf, G, S):
  +eS : {S == Nil{} : +List<+List<Nat>>} =
    MV.MV.nil_of_len_zero(S, NatProof.Nat.eq_zero_of_le_zero(Groups.len_words(S), le))
  OC.cjob_transport(0n, inf, G, Nil{}, S,
    Equal.sym(+List<+List<Nat>>, S, Nil{}, eS), OC.cjob_zero_nil(inf, G, hz))

# The dummy accumulator has an infinite cost, so the finiteness premise is
# contradictory.
def OC.dummy_ok(+inf: Nat, +S: +List<+List<Nat>>) ->
  OC.CostOK(inf, Eval.Eval.dummy_inf(inf), S):
  e =>
    Empty.absurd(
      {Nat.is_le(Tree.cost(Eval.Eval.tree_of(Eval.Eval.dummy_inf(inf)), S),
         Eval.Eval.cost_of(Eval.Eval.dummy_inf(inf))) == True{} : Bool},
      NatProof.Nat.not_lt_self(inf, e))

# One guess keeps the cost correspondence.
def OC.guess_cost(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +best: SolveRef.Best, b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    ccif: OC.CClassIf(p, inf, G, b, Groups.groups_build(g, S, Nil{})),
    wg: Tree.WordIn(g, G),
    cb: OC.CostOK(inf, best, S)) ->
  OC.CostOK(inf,
    Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf, b, best),
    S):
  match b:
    case True{}:
      cand : OC.CostOK(inf,
        SolveRef.Best{
          Fold.OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf))}, S) =
        OC.cand_cost_ok(p, inf, G, S, g, ccif)
      h : OC.CostOK(inf, SolveRef.better(
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
          Fold.OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), best), S) =
        OC.better_cost(inf,
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
          Fold.OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), best, S, cand, cb)
      +e1 : {Eval.Eval.block(p, G, S, g, inf, Groups.groups_build(g, S, Nil{}), best)
              == SolveRef.better(
                   Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                     Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
                   Fold.OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
                     Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), best)
             : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          Eval.Eval.block(p, G, S, g, inf, Groups.groups_build(g, S, Nil{}), best),
          Eval.Eval.finish_ks(inf, g, S,
            Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}), Nil{}, 0n,
              inf), best),
          SolveRef.better(
            Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
              Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
            Fold.OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
              Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), best),
          Fold.OQ.block_unfold(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf, best),
          Fold.OQ.block_eq(inf, g, S,
            Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}), Nil{}, 0n,
              inf), best))
      +e2 : {Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf,
               b, best)
              == Eval.Eval.block(p, G, S, g, inf, Groups.groups_build(g, S, Nil{}),
                   best) : SolveRef.Best} = {==}
      +e3 : {Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf,
               b, best)
              == SolveRef.better(
                   Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                     Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
                   Fold.OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
                     Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), best)
             : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf, b,
            best),
          Eval.Eval.block(p, G, S, g, inf, Groups.groups_build(g, S, Nil{}), best),
          SolveRef.better(
            Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
              Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
            Fold.OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
              Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), best), e2, e1)
      OC.transport(inf,
        SolveRef.better(
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
          Fold.OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), best),
        Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf, b,
          best), S, Equal.sym(SolveRef.Best,
          Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf, b,
            best),
          SolveRef.better(
            Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
              Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
            Fold.OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
              Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), best), e3), h)
    case False{}:
      cb

# The guess fold keeps the cost correspondence.
def OC.guesses_cost(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +gs: +List<+List<Nat>>, +best: SolveRef.Best,
    cbygs: OC.CByGs(p, inf, G, S, gs),
    every: BO.BO.EveryIn(gs, G),
    cb: OC.CostOK(inf, best, S)) ->
  OC.CostOK(inf, Eval.Eval.guesses(1n+p, G, S, inf, gs, best), S):
  match gs:
    case Nil{}:
      cb
    case Con{g, t}:
      (ccf, cbt) = cbygs
      (wg, ev) = every
      nc : OC.CostOK(inf, Eval.Eval.guess(p, G, S, g, inf, best), S) =
        OC.guess_cost(p, G, S, g, inf, best,
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==},
          ccf, wg, cb)
      OC.guesses_cost(p, G, S, inf, t, Eval.Eval.guess(p, G, S, g, inf, best),
        cbt, ev, nc)

# One step of the fuel: the job obligation at the next level.
def OC.cjob_succ(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, cbygs: OC.CByGs(p, inf, G, S, G)) -> OC.CJob(1n+p, inf, G, S):
  OC.transport(inf,
    Eval.Eval.guesses(1n+p, G, S, inf, G, Eval.Eval.dummy_inf(inf)),
    SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S, inf, Nil{}, Nil{}, 0n,
      Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()), S,
    Equal.sym(SolveRef.Best,
      SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()),
      Eval.Eval.guesses(1n+p, G, S, inf, G, Eval.Eval.dummy_inf(inf)),
      Eval.Eval.guesses_step(p, G, S, inf, G, Eval.Eval.dummy_inf(inf))),
    OC.guesses_cost(p, G, S, inf, G, Eval.Eval.dummy_inf(inf), cbygs,
      BO.BO.every_in_self(G), OC.dummy_ok(inf, S)))

# Split the flat conjunction at an append.
def OC.cflat_append(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +xs: +List<+List<+List<Nat>>>, +ys: +List<+List<+List<Nat>>>,
    f: OC.CFlat(fuel, inf, G,
        List.append(&2, +List<+List<Nat>>, xs, ys))) ->
  OC.CFlat(fuel, inf, G, xs) & OC.CFlat(fuel, inf, G, ys):
  match xs:
    case Nil{}:
      Tuple{Unit{}, f}
    case Con{S, t}:
      (j, fr) = f
      MV.MV.use_pair(
        OC.CFlat(fuel, inf, G, S <> t) & OC.CFlat(fuel, inf, G, ys),
        OC.CFlat(fuel, inf, G, t), OC.CFlat(fuel, inf, G, ys),
        OC.cflat_append(fuel, inf, G, t, ys, fr),
        ft => fys => Tuple{Tuple{j, ft}, fys})

# The class conjunction read from a flat conjunction over its classes.
def OC.cclass_of_flat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>,
    f: OC.CFlat(fuel, inf, G, MV.MV.next_groups(groups))) ->
  OC.CClass(fuel, inf, G, groups):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          (fh, ft) = f
          (fh, OC.cclass_of_flat(fuel, inf, G, rest, ft))

# A filtered class conjunction is a class conjunction when the test is true.
def OC.cclassif_of_flat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    f: OC.CFlat(fuel, inf, G,
         MV.MV.classes_b(b, Groups.groups_build(g, S, Nil{})))) ->
  OC.CClassIf(fuel, inf, G, b, Groups.groups_build(g, S, Nil{})):
  match b:
    case True{}:
      OC.cclass_of_flat(fuel, inf, G, Groups.groups_build(g, S, Nil{}), f)
    case False{}:
      Unit{}

# The per-guess class conjunction of a job, from the flat conjunction.
def OC.cbygs_of_flat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>,
    f: OC.CFlat(fuel, inf, G, MV.MV.next_guess(gs, S))) ->
  OC.CByGs(fuel, inf, G, S, gs):
  match gs:
    case Nil{}:
      Unit{}
    case Con{g, t}:
      MV.MV.use_pair(
        OC.CByGs(fuel, inf, G, S, g <> t),
        OC.CFlat(fuel, inf, G, MV.MV.classes(g, S)),
        OC.CFlat(fuel, inf, G, MV.MV.next_guess(t, S)),
        OC.cflat_append(fuel, inf, G, MV.MV.classes(g, S), MV.MV.next_guess(t, S),
          f),
        fg => ft =>
          (OC.cclassif_of_flat(fuel, inf, G, S, g,
             Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==}, fg),
           OC.cbygs_of_flat(fuel, inf, G, S, t, ft)))

# Zero fuel: every job is empty, and the validity conjunction too.
def OC.c_flat_zero_both(+inf: Nat, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>, bounds: MV.MV.Bounds(0n, jobs),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool}) ->
  OC.CFlat(0n, inf, G, jobs) & MV.MV.Flat(0n, inf, G, jobs):
  match jobs:
    case Nil{}:
      Tuple{Unit{}, Unit{}}
    case Con{S, t}:
      (ble0, bt) = bounds
      +ble : {Nat.is_le(Groups.len_words(S), 0n) == True{} : Bool} = ble0
      MV.MV.use_pair(
        OC.CFlat(0n, inf, G, jobs) & MV.MV.Flat(0n, inf, G, jobs),
        OC.CFlat(0n, inf, G, t), MV.MV.Flat(0n, inf, G, t),
        OC.c_flat_zero_both(inf, G, t, bt, hz),
        cf => mf =>
          Tuple{Tuple{OC.cjob_zero(inf, G, S, ble, hz), cf},
                Tuple{MV.MV.job_zero(inf, G, S, ble), mf}})

# One step of the fuel, both conjunctions together.
def OC.c_flat_step_both(+inf: Nat, +p: Nat, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>,
    both: OC.CFlat(p, inf, G, MV.MV.next_jobs(G, jobs))
          & MV.MV.Flat(p, inf, G, MV.MV.next_jobs(G, jobs))) ->
  OC.CFlat(1n+p, inf, G, jobs) & MV.MV.Flat(1n+p, inf, G, jobs):
  match jobs:
    case Nil{}:
      Tuple{Unit{}, Unit{}}
    case Con{S, t}:
      MV.MV.use_pair(
        OC.CFlat(1n+p, inf, G, jobs) & MV.MV.Flat(1n+p, inf, G, jobs),
        OC.CFlat(p, inf, G, MV.MV.next_jobs(G, jobs)),
        MV.MV.Flat(p, inf, G, MV.MV.next_jobs(G, jobs)),
        both,
        cf => mf =>
          MV.MV.use_pair(
            OC.CFlat(1n+p, inf, G, jobs) & MV.MV.Flat(1n+p, inf, G, jobs),
            OC.CFlat(p, inf, G, MV.MV.next_guess(G, S)),
            OC.CFlat(p, inf, G, MV.MV.next_jobs(G, t)),
            OC.cflat_append(p, inf, G, MV.MV.next_guess(G, S),
              MV.MV.next_jobs(G, t), cf),
            fS => ft =>
              MV.MV.use_pair(
                OC.CFlat(1n+p, inf, G, jobs) & MV.MV.Flat(1n+p, inf, G, jobs),
                MV.MV.Flat(p, inf, G, MV.MV.next_guess(G, S)),
                MV.MV.Flat(p, inf, G, MV.MV.next_jobs(G, t)),
                MV.MV.flat_append(p, inf, G, MV.MV.next_guess(G, S),
                  MV.MV.next_jobs(G, t), mf),
                mS => mt =>
                  MV.MV.use_pair(
                    OC.CFlat(1n+p, inf, G, jobs) & MV.MV.Flat(1n+p, inf, G, jobs),
                    OC.CFlat(1n+p, inf, G, t), MV.MV.Flat(1n+p, inf, G, t),
                    OC.c_flat_step_both(inf, p, G, t, Tuple{ft, mt}),
                    cft => mft =>
                      Tuple{
                        Tuple{OC.cjob_succ(p, G, S, inf,
                                OC.cbygs_of_flat(p, inf, G, S, G, fS)), cft},
                        Tuple{MV.MV.step_to_fold(inf, p, G, S,
                                MV.MV.by_gs(p, inf, G, S, G, mS)), mft}}))))

# The fuel induction on the flat conjunction of jobs, with the validity
# conjunction alongside it.
def OC.c_flat_both(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>, bounds: MV.MV.Bounds(fuel, jobs),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool}) ->
  OC.CFlat(fuel, inf, G, jobs) & MV.MV.Flat(fuel, inf, G, jobs):
  match fuel:
    case 0n:
      OC.c_flat_zero_both(inf, G, jobs, bounds, hz)
    case 1n+p:
      OC.c_flat_step_both(inf, p, G, jobs,
        OC.c_flat_both(p, inf, G, MV.MV.next_jobs(G, jobs),
          MV.MV.next_bounds(p, G, jobs, bounds), hz))

# The cost conjunction alone.
def OC.c_flat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>, bounds: MV.MV.Bounds(fuel, jobs),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool}) ->
  OC.CFlat(fuel, inf, G, jobs):
  MV.MV.use_pair(OC.CFlat(fuel, inf, G, jobs),
    OC.CFlat(fuel, inf, G, jobs), MV.MV.Flat(fuel, inf, G, jobs),
    OC.c_flat_both(fuel, inf, G, jobs, bounds, hz),
    cf => mf => cf)

# The tree the solver returns costs at most the cost it stores.
def OC.machine_cost(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>) ->
  OC.CostOK(SolveRef.inf_of(Groups.len_words(C)), MV.MV.solve_best(G, C), C):
  +n : Nat = Groups.len_words(C)
  +inf : Nat = SolveRef.inf_of(n)
  +hz : {Nat.is_lt(0n, inf) == True{} : Bool} =
    Ind.OQ.zero_lt_succ_add(Nat.mul(n, n))
  +le : {Nat.is_le(Groups.len_words(C), n) == True{} : Bool} =
    NatProof.Nat.is_le_refl(n)
  MV.MV.use_pair(OC.CostOK(inf, MV.MV.solve_best(G, C), C),
    OC.CJob(n, inf, G, C), OC.CFlat(n, inf, G, Nil{}),
    OC.c_flat(n, inf, G, C <> Nil{}, Tuple{le, Unit{}}, hz),
    j => u => j)

# A finite stored cost turns the result into the tree it carries.
def OC.best_to_maybe_fin(+inf: Nat, best: SolveRef.Best,
    +e: {Nat.is_lt(Eval.Eval.cost_of(best), inf) == True{} : Bool}) ->
  {SolveRef.best_to_maybe(inf, best) == Some{Eval.Eval.tree_of(best)}
   : Maybe<Tree.Tree>}:
  match best:
    case SolveRef.Best{tree, +cost}:
      Equal.cong(Bool, Maybe<Tree.Tree>,
        x => Feedback.Bool.case(Maybe<Tree.Tree>, x, None{}, Some{tree}),
        Nat.is_ge(cost, inf), False{}, OV.OV.ge_false_of_lt(cost, inf, e))
