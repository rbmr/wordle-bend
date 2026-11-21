# The node cost of a finished guess, split over its feedback classes.
#
# `finish_guess` builds `Node{g, rev_kids(kids)}`, whose ordered child list is
# exactly `CH.CH.children(groups)`: one child per class, in class order. This module
# proves that the cost of that tree is the candidate count plus the sum of the
# class costs, so the cost field of the finished `Best` and the tree it carries
# agree whenever the cost is finite.
#
# The scan of `Tree.lookup` finds a class's own child because the groups have
# pairwise different feedbacks. That fact is carried as the boolean
# `CBK.distinctB`, so `Bool.and` splits and `Bool.not` inversions can be reused
# along both the head-skip and the recursive call instead of consuming a
# `Type`-valued list once.
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ../src/groups.bend as Groups
import ../src/solve_ref.bend as SolveRef
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as Fb
import ./groupsdistinct.bend as GD
import ./eval.bend as Eval
import ./children.bend as CH
import ./groupcost.bend as GC
import ./nodecost.bend as NodeCost
import ./classbound_nat.bend as CBN
import ./sat.bend as Sat
import ./classbound.bend as CBProof
import ./classbound_sum.bend as CBS

# Every group feedback differs from `fb`.
def CBK.allNe(+fb: +List<Feedback.Color>, +gs: +List<Groups.Group>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          Bool.and(Bool.not(Feedback.feedback_eq(fb, f)), CBK.allNe(fb, t))

# The groups have pairwise different feedbacks, as a boolean.
def CBK.distinctB(+gs: +List<Groups.Group>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          Bool.and(CBK.allNe(f, t), CBK.distinctB(t))

# Eliminate a computed pair with a continuation, so it is destructured once.
def CBK.use_pair(-R: Type, -A: Type, -B: Type, p: A & B,
    k: A -> B -> R) -> R:
  match p:
    case (a, b):
      k(a, b)

# A negation that is true means the test is false, and conversely.
def CBK.not_false(b: Bool, e: {b == False{} : Bool}) ->
  {Bool.not(b) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Bool.not(True{}) == True{} : Bool},
                   Logic.Proof.true_ne_false(e))
    case False{}:
      {==}

def CBK.not_true(b: Bool, e: {Bool.not(b) == True{} : Bool}) ->
  {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Logic.Proof.false_ne_true(e))
    case False{}:
      {==}

# The boolean distinctness of a group list.
def CBK.allNe_of(+fb: +List<Feedback.Color>, +gs: +List<Groups.Group>,
    d: GD.GD.NotFb(fb, gs)) -> {CBK.allNe(fb, gs) == True{} : Bool}:
  match gs:
    case Nil{}:
      {==}
    case Con{gp, t}:
      match gp:
        case Groups.Group{+f, +ws}:
          (nf, nft) = d
          +e1 : {Bool.not(Feedback.feedback_eq(fb, f)) == True{} : Bool} =
            CBK.not_false(Feedback.feedback_eq(fb, f), nf)
          +e2 : {CBK.allNe(fb, t) == True{} : Bool} = CBK.allNe_of(fb, t, nft)
          Logic.Proof.and_intro(Bool.not(Feedback.feedback_eq(fb, f)),
                                CBK.allNe(fb, t), e1, e2)

def CBK.distinctB_of(+gs: +List<Groups.Group>, d: GD.GD.Distinct(gs)) ->
  {CBK.distinctB(gs) == True{} : Bool}:
  match gs:
    case Nil{}:
      {==}
    case Con{gp, t}:
      match gp:
        case Groups.Group{+f, +ws}:
          (nf, dt) = d
          +e1 : {CBK.allNe(f, t) == True{} : Bool} = CBK.allNe_of(f, t, nf)
          +e2 : {CBK.distinctB(t) == True{} : Bool} = CBK.distinctB_of(t, dt)
          Logic.Proof.and_intro(CBK.allNe(f, t), CBK.distinctB(t), e1, e2)

# The groups `groups_build` produces are distinct, as a reusable boolean.
def CBK.distinctB_build(+g: +List<Nat>, +S: +List<+List<Nat>>) ->
  {CBK.distinctB(Groups.groups_build(g, S, Nil{})) == True{} : Bool}:
  CBK.distinctB_of(Groups.groups_build(g, S, Nil{}), GD.GD.groups_distinct(g, S))

# The result tree of one class.
def CBK.tree_of_class(+p: Nat, +G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +inf: Nat) -> Tree.Tree:
  Eval.Eval.tree_of(SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
    Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()))

# The costs of the class results, in class order.
def CBK.class_costs(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +groups: +List<Groups.Group>, +inf: Nat) -> +List<Nat>:
  match groups:
    case Nil{}:
      Nil{}
    case Con{gp, t}:
      match gp:
        case Groups.Group{+f, +ws}:
          Tree.cost(CBK.tree_of_class(p, G, ws, inf), ws)
          <> CBK.class_costs(p, G, S, t, inf)

# A lookup whose feedback differs from the head reaches the tail.
def CBK.lookup_skip(+fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    child: Tree.Tree, +rest: +List<Tree.Child>,
    +e: {Feedback.feedback_eq(fb, f) == False{} : Bool}) ->
  {Tree.lookup(fb, Tree.Child{f, child} <> rest) == Tree.lookup(fb, rest)
   : Maybe<Tree.Tree>}:
  Equal.cong(Bool, Maybe<Tree.Tree>,
    x => Feedback.Bool.case(Maybe<Tree.Tree>, x, Some{child}, Tree.lookup(fb, rest)),
    Feedback.feedback_eq(fb, f), False{}, e)

# A lookup of the head's own feedback finds the head.
def CBK.lookup_head(+fb: +List<Feedback.Color>, child: Tree.Tree,
    +rest: +List<Tree.Child>) ->
  {Tree.lookup(fb, Tree.Child{fb, child} <> rest) == Some{child} : Maybe<Tree.Tree>}:
  Equal.cong(Bool, Maybe<Tree.Tree>,
    x => Feedback.Bool.case(Maybe<Tree.Tree>, x, Some{child}, Tree.lookup(fb, rest)),
    Feedback.feedback_eq(fb, fb), True{}, Fb.FbPrf.feedback_eq_refl(fb))

# A feedback absent from every group misses the whole child list.
def CBK.lookup_none(+fb: +List<Feedback.Color>, +p: Nat,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +gs: +List<Groups.Group>,
    +inf: Nat, +e: {CBK.allNe(fb, gs) == True{} : Bool}) ->
  {Tree.lookup(fb, CH.CH.children(p, G, S, gs, inf)) == None{} : Maybe<Tree.Tree>}:
  match gs:
    case Nil{}:
      {==}
    case Con{gp, t}:
      match gp:
        case Groups.Group{+f, +ws}:
          CBK.use_pair(
            {Tree.lookup(fb, CH.CH.children(p, G, S, gs, inf)) == None{} : Maybe<Tree.Tree>},
            {Bool.not(Feedback.feedback_eq(fb, f)) == True{} : Bool},
            {CBK.allNe(fb, t) == True{} : Bool},
            Logic.Proof.and_split(Bool.not(Feedback.feedback_eq(fb, f)),
                                  CBK.allNe(fb, t), e),
            e1 => e2 =>
              +ef : {Feedback.feedback_eq(fb, f) == False{} : Bool} =
                CBK.not_true(Feedback.feedback_eq(fb, f), e1)
              +e_skip : {Tree.lookup(fb,
                           CH.CH.kid(p, G, S, f, ws, inf)
                           <> CH.CH.children(p, G, S, t, inf))
                         == Tree.lookup(fb, CH.CH.children(p, G, S, t, inf))
                         : Maybe<Tree.Tree>} =
                CBK.lookup_skip(fb, f, CBK.tree_of_class(p, G, ws, inf),
                                CH.CH.children(p, G, S, t, inf), ef)
              +ih : {Tree.lookup(fb, CH.CH.children(p, G, S, t, inf)) == None{}
                     : Maybe<Tree.Tree>} =
                CBK.lookup_none(fb, p, G, S, t, inf, e2)
              Equal.trans(Maybe<Tree.Tree>,
                Tree.lookup(fb, CH.CH.children(p, G, S, gs, inf)),
                Tree.lookup(fb, CH.CH.children(p, G, S, t, inf)), None{}, e_skip, ih))

# The group cost only reads the child list through the lookup.
def CBK.group_cost_irrel(+kids1: +List<Tree.Child>, +kids2: +List<Tree.Child>,
    +ws: +List<+List<Nat>>, m: Maybe<Tree.Tree>) ->
  {GC.GC.group_cost_of(kids1, ws, m) == GC.GC.group_cost_of(kids2, ws, m) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      {==}

# Per-group lookup equalities between two child lists.
def CBK.LkEqs(+kids1: +List<Tree.Child>, +kids2: +List<Tree.Child>,
    +gs: +List<Groups.Group>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          {Tree.lookup(f, kids1) == Tree.lookup(f, kids2) : Maybe<Tree.Tree>}
          & CBK.LkEqs(kids1, kids2, t)

# A head child with a feedback absent from the tail can be skipped for every
# tail group, so the two child lists look the same to every tail group.
def CBK.skip_eqs(+fb: +List<Feedback.Color>, +child: Tree.Tree,
    +kids: +List<Tree.Child>, +gs: +List<Groups.Group>,
    +e: {CBK.allNe(fb, gs) == True{} : Bool}) ->
  CBK.LkEqs(Tree.Child{fb, child} <> kids, kids, gs):
  match gs:
    case Nil{}:
      Unit{}
    case Con{gp, t}:
      match gp:
        case Groups.Group{+f, +ws}:
          CBK.use_pair(
            CBK.LkEqs(Tree.Child{fb, child} <> kids, kids, gs),
            {Bool.not(Feedback.feedback_eq(fb, f)) == True{} : Bool},
            {CBK.allNe(fb, t) == True{} : Bool},
            Logic.Proof.and_split(Bool.not(Feedback.feedback_eq(fb, f)),
                                  CBK.allNe(fb, t), e),
            e1 => e2 =>
              +ef : {Feedback.feedback_eq(fb, f) == False{} : Bool} =
                CBK.not_true(Feedback.feedback_eq(fb, f), e1)
              +efs : {Feedback.feedback_eq(f, fb) == False{} : Bool} =
                GD.GD.fb_false_sym(fb, f, ef)
              (CBK.lookup_skip(f, fb, child, kids, efs),
               CBK.skip_eqs(fb, child, kids, t, e2)))

# The total cost only reads the child lists through the lookups.
def CBK.total_lk_eqs(+kids1: +List<Tree.Child>, +kids2: +List<Tree.Child>,
    +gs: +List<Groups.Group>, eqs: CBK.LkEqs(kids1, kids2, gs)) ->
  {GC.GC.Total(kids1, gs) == GC.GC.Total(kids2, gs) : Nat}:
  match gs:
    case Nil{}:
      {==}
    case Con{gp, t}:
      match gp:
        case Groups.Group{+f, +ws}:
          (eh, et) = eqs
          +ih : {GC.GC.Total(kids1, t) == GC.GC.Total(kids2, t) : Nat} =
            CBK.total_lk_eqs(kids1, kids2, t, et)
          +g1 : {GC.GC.GroupCost(kids1, Groups.Group{f, ws})
                 == GC.GC.group_cost_of(kids1, ws, Tree.lookup(f, kids2)) : Nat} =
            Equal.cong(Maybe<Tree.Tree>, Nat,
              m => GC.GC.group_cost_of(kids1, ws, m),
              Tree.lookup(f, kids1), Tree.lookup(f, kids2), eh)
          +g2 : {GC.GC.group_cost_of(kids1, ws, Tree.lookup(f, kids2))
                 == GC.GC.GroupCost(kids2, Groups.Group{f, ws}) : Nat} =
            CBK.group_cost_irrel(kids1, kids2, ws, Tree.lookup(f, kids2))
          +g : {GC.GC.GroupCost(kids1, Groups.Group{f, ws})
                == GC.GC.GroupCost(kids2, Groups.Group{f, ws}) : Nat} =
            Equal.trans(Nat, GC.GC.GroupCost(kids1, Groups.Group{f, ws}),
              GC.GC.group_cost_of(kids1, ws, Tree.lookup(f, kids2)),
              GC.GC.GroupCost(kids2, Groups.Group{f, ws}), g1, g2)
          Equal.trans(Nat,
            Nat.add(GC.GC.GroupCost(kids1, Groups.Group{f, ws}), GC.GC.Total(kids1, t)),
            Nat.add(GC.GC.GroupCost(kids2, Groups.Group{f, ws}), GC.GC.Total(kids1, t)),
            Nat.add(GC.GC.GroupCost(kids2, Groups.Group{f, ws}), GC.GC.Total(kids2, t)),
            Equal.cong(Nat, Nat,
              x => Nat.add(x, GC.GC.Total(kids1, t)),
              GC.GC.GroupCost(kids1, Groups.Group{f, ws}),
              GC.GC.GroupCost(kids2, Groups.Group{f, ws}), g),
            Equal.cong(Nat, Nat,
              x => Nat.add(GC.GC.GroupCost(kids2, Groups.Group{f, ws}), x),
              GC.GC.Total(kids1, t), GC.GC.Total(kids2, t), ih))

# The total of the ordered children is the sum of the class costs.
def CBK.total_children(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +groups: +List<Groups.Group>, +inf: Nat,
    +d: {CBK.distinctB(groups) == True{} : Bool}) ->
  {GC.GC.Total(CH.CH.children(p, G, S, groups, inf), groups)
   == CBN.CB.sum(CBK.class_costs(p, G, S, groups, inf)) : Nat}:
  match groups:
    case Nil{}:
      {==}
    case Con{gp, t}:
      match gp:
        case Groups.Group{+f, +ws}:
          +tc : Tree.Tree = CBK.tree_of_class(p, G, ws, inf)
          CBK.use_pair(
            {GC.GC.Total(CH.CH.children(p, G, S, groups, inf), groups)
             == CBN.CB.sum(CBK.class_costs(p, G, S, groups, inf)) : Nat},
            {CBK.allNe(f, t) == True{} : Bool},
            {CBK.distinctB(t) == True{} : Bool},
            Logic.Proof.and_split(CBK.allNe(f, t), CBK.distinctB(t), d),
            d1 => d2 =>
          +head : {GC.GC.GroupCost(CH.CH.children(p, G, S, groups, inf), Groups.Group{f, ws})
                   == Tree.cost(tc, ws) : Nat} =
            Equal.cong(Maybe<Tree.Tree>, Nat,
              m => GC.GC.group_cost_of(CH.CH.children(p, G, S, groups, inf), ws, m),
              Tree.lookup(f, CH.CH.children(p, G, S, groups, inf)),
              Some{tc},
              CBK.lookup_head(f, tc, CH.CH.children(p, G, S, t, inf)))
          +tail_eq : {GC.GC.Total(CH.CH.children(p, G, S, groups, inf), t)
                      == GC.GC.Total(CH.CH.children(p, G, S, t, inf), t) : Nat} =
            CBK.total_lk_eqs(CH.CH.children(p, G, S, groups, inf),
              CH.CH.children(p, G, S, t, inf), t,
              CBK.skip_eqs(f, tc, CH.CH.children(p, G, S, t, inf), t, d1))
          +ih : {GC.GC.Total(CH.CH.children(p, G, S, t, inf), t)
                 == CBN.CB.sum(CBK.class_costs(p, G, S, t, inf)) : Nat} =
            CBK.total_children(p, G, S, t, inf, d2)
          Equal.trans(Nat,
            Nat.add(GC.GC.GroupCost(CH.CH.children(p, G, S, groups, inf), Groups.Group{f, ws}),
                    GC.GC.Total(CH.CH.children(p, G, S, groups, inf), t)),
            Nat.add(Tree.cost(tc, ws),
                    GC.GC.Total(CH.CH.children(p, G, S, groups, inf), t)),
            Nat.add(Tree.cost(tc, ws), CBN.CB.sum(CBK.class_costs(p, G, S, t, inf))),
            Equal.cong(Nat, Nat,
              x => Nat.add(x, GC.GC.Total(CH.CH.children(p, G, S, groups, inf), t)),
              GC.GC.GroupCost(CH.CH.children(p, G, S, groups, inf), Groups.Group{f, ws}),
              Tree.cost(tc, ws), head),
            Equal.trans(Nat,
              Nat.add(Tree.cost(tc, ws), GC.GC.Total(CH.CH.children(p, G, S, groups, inf), t)),
              Nat.add(Tree.cost(tc, ws), GC.GC.Total(CH.CH.children(p, G, S, t, inf), t)),
              Nat.add(Tree.cost(tc, ws), CBN.CB.sum(CBK.class_costs(p, G, S, t, inf))),
              Equal.cong(Nat, Nat, x => Nat.add(Tree.cost(tc, ws), x),
                GC.GC.Total(CH.CH.children(p, G, S, groups, inf), t),
                GC.GC.Total(CH.CH.children(p, G, S, t, inf), t), tail_eq),
              Equal.cong(Nat, Nat, x => Nat.add(Tree.cost(tc, ws), x),
                GC.GC.Total(CH.CH.children(p, G, S, t, inf), t),
                CBN.CB.sum(CBK.class_costs(p, G, S, t, inf)), ih))))

# The cost of a finished guess's node is the candidate count plus the sum of the
# class costs.
def CBK.node_cost(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat,
    v: Tree.AllHaveDepth(
         Tree.Node{g, CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf)}, S),
    +d: {CBK.distinctB(Groups.groups_build(g, S, Nil{})) == True{} : Bool}) ->
  {Tree.cost(Tree.Node{g, CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf)}, S)
   == Nat.add(Groups.len_words(S),
        CBN.CB.sum(CBK.class_costs(p, G, S, Groups.groups_build(g, S, Nil{}), inf))) : Nat}:
  +kids : +List<Tree.Child> =
    CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf)
  +groups : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
  +sum : Nat = CBN.CB.sum(CBK.class_costs(p, G, S, groups, inf))
  +cn : {Tree.cost(Tree.Node{g, kids}, S)
         == Nat.add(Groups.len_words(S), NodeCost.NodeCost.kid_sum(g, kids, S)) : Nat} =
    NodeCost.NodeCost.cost_node(g, kids, S, v)
  +gt : {GC.GC.Total(kids, groups) == NodeCost.NodeCost.kid_sum(g, kids, S) : Nat} =
    GC.GC.groups_build_total(g, kids, S)
  +tc : {GC.GC.Total(kids, groups) == sum : Nat} =
    CBK.total_children(p, G, S, groups, inf, d)
  +ek : {NodeCost.NodeCost.kid_sum(g, kids, S) == sum : Nat} =
    Equal.trans(Nat, NodeCost.NodeCost.kid_sum(g, kids, S), GC.GC.Total(kids, groups),
                sum, Equal.sym(Nat, GC.GC.Total(kids, groups),
                               NodeCost.NodeCost.kid_sum(g, kids, S), gt), tc)
  Equal.trans(Nat, Tree.cost(Tree.Node{g, kids}, S),
              Nat.add(Groups.len_words(S), NodeCost.NodeCost.kid_sum(g, kids, S)),
              Nat.add(Groups.len_words(S), sum), cn,
              Equal.cong(Nat, Nat, x => Nat.add(Groups.len_words(S), x),
                         NodeCost.NodeCost.kid_sum(g, kids, S), sum, ek))

# Depth facts survive a syntactic change of the child list.
def CBK.depths_transport(+g: +List<Nat>, +k1: +List<Tree.Child>,
    +k2: +List<Tree.Child>, +S: +List<+List<Nat>>,
    e: {k1 == k2 : +List<Tree.Child>}, v: Tree.AllHaveDepth(Tree.Node{g, k1}, S)) ->
  Tree.AllHaveDepth(Tree.Node{g, k2}, S):
  %e : Tree.AllHaveDepth(Tree.Node{g, _}, S)
  v

# The cost of two equal trees is the same.
def CBK.cost_tree_eq(+T1: Tree.Tree, +T2: Tree.Tree, +S: +List<+List<Nat>>,
    e: {T1 == T2 : Tree.Tree}) ->
  {Tree.cost(T1, S) == Tree.cost(T2, S) : Nat}:
  Equal.cong(Tree.Tree, Nat, t => Tree.cost(t, S), T1, T2, e)

# One class's stored cost equals the cost of the tree it carries.
def CBK.CostEqs(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +groups: +List<Groups.Group>, +inf: Nat) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          {Sat.SB.child_cost(p, G, ws, inf)
           == Tree.cost(CBK.tree_of_class(p, G, ws, inf), ws) : Nat}
          & CBK.CostEqs(p, G, S, t, inf)

# With that, the fold's cost list is the class-cost list of the node.
def CBK.costs_eq(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +groups: +List<Groups.Group>, +inf: Nat,
    eq: CBK.CostEqs(p, G, S, groups, inf)) ->
  {Sat.SB.child_costs(p, G, groups, inf)
   == CBK.class_costs(p, G, S, groups, inf) : +List<Nat>}:
  match groups:
    case Nil{}:
      {==}
    case Con{gp, t}:
      match gp:
        case Groups.Group{+f, +ws}:
          (eh, et) = eq
          +ih : {Sat.SB.child_costs(p, G, t, inf)
                 == CBK.class_costs(p, G, S, t, inf) : +List<Nat>} =
            CBK.costs_eq(p, G, S, t, inf, et)
          +e1 : {Sat.SB.child_cost(p, G, ws, inf) <> Sat.SB.child_costs(p, G, t, inf)
                 == Tree.cost(CBK.tree_of_class(p, G, ws, inf), ws)
                    <> Sat.SB.child_costs(p, G, t, inf) : +List<Nat>} =
            Equal.cong(Nat, +List<Nat>,
              x => x <> Sat.SB.child_costs(p, G, t, inf),
              Sat.SB.child_cost(p, G, ws, inf),
              Tree.cost(CBK.tree_of_class(p, G, ws, inf), ws), eh)
          Equal.trans(+List<Nat>,
            Sat.SB.child_cost(p, G, ws, inf) <> Sat.SB.child_costs(p, G, t, inf),
            Tree.cost(CBK.tree_of_class(p, G, ws, inf), ws)
              <> Sat.SB.child_costs(p, G, t, inf),
            Tree.cost(CBK.tree_of_class(p, G, ws, inf), ws)
              <> CBK.class_costs(p, G, S, t, inf), e1,
            Equal.cong(+List<Nat>, +List<Nat>,
              x => Tree.cost(CBK.tree_of_class(p, G, ws, inf), ws) <> x,
              Sat.SB.child_costs(p, G, t, inf),
              CBK.class_costs(p, G, S, t, inf), ih))

# The cost of the tree `finish_guess` builds from the accumulator. The machine's
# child list is the reverse of the class children, and the stored cost list is
# the class-cost list, so this is `CBK.node_cost` transported to the exact tree
# and cost the solver holds.
def CBK.machine_cost(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +kids: +List<Tree.Child>,
    depths: Tree.AllHaveDepth(Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, S),
    +kids_eq: {SolveRef.rev_kids(kids, Nil{})
               == CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf)
               : +List<Tree.Child>},
    costEq: CBK.CostEqs(p, G, S, Groups.groups_build(g, S, Nil{}), inf)) ->
  {Tree.cost(Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, S)
   == Nat.add(Groups.len_words(S),
        CBN.CB.sum(Sat.SB.child_costs(p, G, Groups.groups_build(g, S, Nil{}), inf)))
   : Nat}:
  +groups : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
  +kids2 : +List<Tree.Child> = CH.CH.children(p, G, S, groups, inf)
  d2 : Tree.AllHaveDepth(Tree.Node{g, kids2}, S) =
    CBK.depths_transport(g, SolveRef.rev_kids(kids, Nil{}), kids2, S, kids_eq, depths)
  +nc : {Tree.cost(Tree.Node{g, kids2}, S)
         == Nat.add(Groups.len_words(S),
              CBN.CB.sum(CBK.class_costs(p, G, S, groups, inf))) : Nat} =
    CBK.node_cost(p, G, S, g, inf, d2, CBK.distinctB_build(g, S))
  +ct : {Sat.SB.child_costs(p, G, groups, inf)
         == CBK.class_costs(p, G, S, groups, inf) : +List<Nat>} =
    CBK.costs_eq(p, G, S, groups, inf, costEq)
  +cs : {CBN.CB.sum(CBK.class_costs(p, G, S, groups, inf))
         == CBN.CB.sum(Sat.SB.child_costs(p, G, groups, inf)) : Nat} =
    Equal.cong(+List<Nat>, Nat, l => CBN.CB.sum(l),
      CBK.class_costs(p, G, S, groups, inf),
      Sat.SB.child_costs(p, G, groups, inf),
      Equal.sym(+List<Nat>, Sat.SB.child_costs(p, G, groups, inf),
                CBK.class_costs(p, G, S, groups, inf), ct))
  +e_add : {Nat.add(Groups.len_words(S),
              CBN.CB.sum(CBK.class_costs(p, G, S, groups, inf)))
            == Nat.add(Groups.len_words(S),
                 CBN.CB.sum(Sat.SB.child_costs(p, G, groups, inf))) : Nat} =
    Equal.cong(Nat, Nat, x => Nat.add(Groups.len_words(S), x),
               CBN.CB.sum(CBK.class_costs(p, G, S, groups, inf)),
               CBN.CB.sum(Sat.SB.child_costs(p, G, groups, inf)), cs)
  +e_tree : {Tree.Node{g, SolveRef.rev_kids(kids, Nil{})} == Tree.Node{g, kids2}
             : Tree.Tree} =
    Equal.cong(+List<Tree.Child>, Tree.Tree, ks => Tree.Node{g, ks},
               SolveRef.rev_kids(kids, Nil{}), kids2, kids_eq)
  +e_cost : {Tree.cost(Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, S)
             == Tree.cost(Tree.Node{g, kids2}, S) : Nat} =
    CBK.cost_tree_eq(Tree.Node{g, SolveRef.rev_kids(kids, Nil{})},
      Tree.Node{g, kids2}, S, e_tree)
  Equal.trans(Nat, Tree.cost(Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, S),
    Tree.cost(Tree.Node{g, kids2}, S),
    Nat.add(Groups.len_words(S),
      CBN.CB.sum(Sat.SB.child_costs(p, G, groups, inf))),
    e_cost, Equal.trans(Nat, Tree.cost(Tree.Node{g, kids2}, S),
      Nat.add(Groups.len_words(S),
        CBN.CB.sum(CBK.class_costs(p, G, S, groups, inf))),
      Nat.add(Groups.len_words(S),
        CBN.CB.sum(Sat.SB.child_costs(p, G, groups, inf))), nc, e_add))

# The per-class facts that bound a node: the class is strictly smaller than the
# candidate list, and its stored cost fits its own square.
def CBK.ClassFits(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +groups: +List<Groups.Group>, +inf: Nat, +n: Nat) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          {Nat.is_lt(Groups.len_words(ws), n) == True{} : Bool}
          & {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
                Nat.mul(Groups.len_words(ws), Groups.len_words(ws))) == True{} : Bool}
          & CBK.ClassFits(p, G, S, t, inf, n)

# Turn the per-class facts into the arithmetic bound of `classbound.bend`.
def CBK.bounds_of(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +groups: +List<Groups.Group>, +inf: Nat, +n: Nat,
    f: CBK.ClassFits(p, G, S, groups, inf, n)) ->
  CBProof.CB.Bounds(n, groups, Sat.SB.child_costs(p, G, groups, inf)):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, t}:
      match gp:
        case Groups.Group{+f2, +ws}:
          (fh, fr) = f
          (fl, ft) = fr
          (fh, (fl, CBK.bounds_of(p, G, S, t, inf, n, ft)))

# The finished guess's node cost stays below the solver's infinity, from the
# per-class size and cost bounds.
def CBK.node_bound(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +N: Nat,
    f: CBK.ClassFits(p, G, S, Groups.groups_build(g, S, Nil{}), inf,
      Groups.len_words(S)),
    +leN: {Nat.is_le(Groups.len_words(S), N) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(Groups.len_words(S),
      CBN.CB.sum(Sat.SB.child_costs(p, G, Groups.groups_build(g, S, Nil{}), inf))),
     Nat.add(Nat.mul(N, N), 1n)) == True{} : Bool}:
  CBProof.CB.fits_inf_classes(N, S, g,
    Sat.SB.child_costs(p, G, Groups.groups_build(g, S, Nil{}), inf),
    CBK.bounds_of(p, G, S, Groups.groups_build(g, S, Nil{}), inf,
      Groups.len_words(S), f),
    leN)

# The same node cost fits the square of the candidate count.
def CBK.node_bound_sq(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat,
    f: CBK.ClassFits(p, G, S, Groups.groups_build(g, S, Nil{}), inf,
      Groups.len_words(S))) ->
  {Nat.is_le(Nat.add(Groups.len_words(S),
      CBN.CB.sum(Sat.SB.child_costs(p, G, Groups.groups_build(g, S, Nil{}), inf))),
     Nat.mul(Groups.len_words(S), Groups.len_words(S))) == True{} : Bool}:
  CBProof.CB.bound_groups(Groups.len_words(S),
    Groups.groups_build(g, S, Nil{}),
    Sat.SB.child_costs(p, G, Groups.groups_build(g, S, Nil{}), inf),
    CBK.bounds_of(p, G, S, Groups.groups_build(g, S, Nil{}), inf,
      Groups.len_words(S), f),
    CBProof.CB.partition_le(g, S))

# The stored candidate cost fits the square of the top-level candidate count.
# This is the upper half of the optimality invariant: below infinity the guess
# cost is a plain sum, and the class bounds place it under `N*N`.
def CBK.sat_node_upper(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +N: Nat,
    f: CBK.ClassFits(p, G, S, Groups.groups_build(g, S, Nil{}), inf,
      Groups.len_words(S)),
    +leN: {Nat.is_le(Groups.len_words(S), N) == True{} : Bool}) ->
  {Nat.is_le(SolveRef.sat_add(inf, Groups.len_words(S),
     CBN.CB.sum(Sat.SB.child_costs(p, G, Groups.groups_build(g, S, Nil{}), inf))),
     Nat.mul(N, N)) == True{} : Bool}:
  +le1 : {Nat.is_le(SolveRef.sat_add(inf, Groups.len_words(S),
             CBN.CB.sum(Sat.SB.child_costs(p, G, Groups.groups_build(g, S, Nil{}), inf))),
            Nat.add(Groups.len_words(S),
             CBN.CB.sum(Sat.SB.child_costs(p, G, Groups.groups_build(g, S, Nil{}), inf))))
          == True{} : Bool} =
    CBS.CU.sat_add_le_add(inf, Groups.len_words(S),
      CBN.CB.sum(Sat.SB.child_costs(p, G, Groups.groups_build(g, S, Nil{}), inf)))
  +le2 : {Nat.is_le(Nat.add(Groups.len_words(S),
             CBN.CB.sum(Sat.SB.child_costs(p, G, Groups.groups_build(g, S, Nil{}), inf))),
            Nat.mul(Groups.len_words(S), Groups.len_words(S))) == True{} : Bool} =
    CBK.node_bound_sq(p, G, S, g, inf, f)
  +le3a : {Nat.is_le(Nat.mul(Groups.len_words(S), Groups.len_words(S)),
             Nat.mul(N, Groups.len_words(S))) == True{} : Bool} =
    CBN.CB.is_le_mul_l(Groups.len_words(S), N, Groups.len_words(S), leN)
  +le3b : {Nat.is_le(Nat.mul(N, Groups.len_words(S)), Nat.mul(N, N))
           == True{} : Bool} =
    CBN.CB.is_le_mul_r(Groups.len_words(S), N, N, leN)
  +le3 : {Nat.is_le(Nat.mul(Groups.len_words(S), Groups.len_words(S)),
            Nat.mul(N, N)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(Nat.mul(Groups.len_words(S), Groups.len_words(S)),
      Nat.mul(N, Groups.len_words(S)), Nat.mul(N, N), le3a, le3b)
  NatProof.Nat.is_le_trans(SolveRef.sat_add(inf, Groups.len_words(S),
      CBN.CB.sum(Sat.SB.child_costs(p, G, Groups.groups_build(g, S, Nil{}), inf))),
    Nat.add(Groups.len_words(S),
      CBN.CB.sum(Sat.SB.child_costs(p, G, Groups.groups_build(g, S, Nil{}), inf))),
    Nat.mul(N, N), le1,
    NatProof.Nat.is_le_trans(Nat.add(Groups.len_words(S),
        CBN.CB.sum(Sat.SB.child_costs(p, G, Groups.groups_build(g, S, Nil{}), inf))),
      Nat.mul(Groups.len_words(S), Groups.len_words(S)), Nat.mul(N, N), le2, le3))
