# The node step of the optimality induction.
#
# For a valid tree `Node g kids` whose guess is usable, the children are the
# class children of `g`, so the node's cost splits into one guess per candidate
# plus the classes' costs (the `cover` modules). Each class result is below its
# child's cost by the induction hypothesis at the smaller fuel, and the class
# sum is below the children's total. This module states that step.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./groupcost.bend as GC
import ./nodecost.bend as NodeCost
import ./cover.bend as Cover
import ./cover_oracle.bend as Cora
import ./optimalvalue.bend as OV
import ./optsum.bend as Sums
import ./optfold.bend as Fold

# Whether the root guess of a tree is usable for a candidate list.
def OQ.root_ok(+S: +List<+List<Nat>>, T: Tree.Tree) -> Bool:
  match T:
    case Tree.Node{+g, kids}:
      Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))

# The optimality bound at one fuel: every valid tree costs at least the search.
def OQ.AJob(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>) -> Type:
  @T: Tree.Tree -> Tree.Valid(T, G, S)
  -> {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(fuel, SolveRef.mk_schedule(G, S),
        G, S, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
        Eval.Eval.dummy_zero())), Tree.cost(T, S)) == True{} : Bool}

# The class obligations of one guess at one fuel.
def OQ.AClass(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          OQ.AJob(fuel, inf, G, ws) & OQ.AClass(fuel, inf, G, rest)

# The class obligations of every guess in a guess list.
def OQ.AByGs(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{g, t}:
      OQ.AClass(fuel, inf, G, Groups.groups_build(g, S, Nil{}))
      & OQ.AByGs(fuel, inf, G, S, t)

# The conjunction of the job obligations over a list of candidate lists.
def OQ.AFlat(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    jobs: +List<+List<+List<Nat>>>) -> Type:
  match jobs:
    case Nil{}:
      Unit
    case Con{S, t}:
      OQ.AJob(fuel, inf, G, S) & OQ.AFlat(fuel, inf, G, t)

# Every class of a guess's groups is below the cost of its child.
def OQ.class_le_pf(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>, +kids: +List<Tree.Child>,
    jobs: OQ.AClass(p, inf, G, groups),
    gk: Cora.Cover.GroupKids(G, kids, groups)) ->
  Sums.OQ.ClassLe(p, G, inf, groups, kids):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          (jh, jt) = jobs
          (kh, kt) = gk
          match kh:
            case Tuple{+T, kp}:
              (e_look, valid) = kp
              +le1 : {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf), Tree.cost(T, ws))
                      == True{} : Bool} =
                jh(T, valid)
              +gc : {GC.GC.GroupCost(kids, Groups.Group{fb, ws})
                     == Tree.cost(T, ws) : Nat} =
                Cover.Cover.group_cost_some(kids, fb, ws, T, e_look)
              (Fold.OQ.le_cong_r(Sat.SB.child_cost(p, G, ws, inf),
                 Tree.cost(T, ws), GC.GC.GroupCost(kids, Groups.Group{fb, ws}),
                 Equal.sym(Nat, GC.GC.GroupCost(kids, Groups.Group{fb, ws}),
                   Tree.cost(T, ws), gc), le1),
               OQ.class_le_pf(p, inf, G, rest, kids, jt, kt))

# The candidate cost unfolds into the saturating sum of the class costs.
def OQ.ks_cost_unfold(+inf: Nat, +S: +List<+List<Nat>>, ks: Eval.KS) ->
  {Fold.OQ.ks_cost(inf, S, ks)
   == SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(ks)) : Nat}:
  match ks:
    case Eval.KS{kids, sum}:
      {==}

# The usable node step: the candidate cost is below the node's cost.
def OQ.node_le(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +groups: +List<Groups.Group>,
    +kids: +List<Tree.Child>,
    +eg : {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    jobs: OQ.AClass(p, inf, G, groups),
    gk: Cora.Cover.GroupKids(G, kids, groups)) ->
  {Nat.is_le(Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, groups,
      Nil{}, 0n, inf)), Tree.cost(Tree.Node{g, kids}, S)) == True{} : Bool}:
  le : Sums.OQ.ClassLe(p, G, inf, groups, kids) =
    OQ.class_le_pf(p, inf, G, groups, kids, jobs, gk)
  +h0 : {Nat.is_le(0n, 0n) == True{} : Bool} = NatProof.Nat.is_le_refl(0n)
  +sl : {Nat.is_le(OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n),
                  Nat.add(0n, GC.GC.Total(kids, groups))) == True{} : Bool} =
    Sums.OQ.sumL_le_total(p, G, inf, groups, kids, 0n, 0n, h0, le)
  +ez : {Nat.add(0n, GC.GC.Total(kids, groups)) == GC.GC.Total(kids, groups)
         : Nat} = {==}
  +sl2 : {Nat.is_le(OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n),
                   GC.GC.Total(kids, groups)) == True{} : Bool} =
    Fold.OQ.le_cong_r(OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n),
      Nat.add(0n, GC.GC.Total(kids, groups)), GC.GC.Total(kids, groups), ez, sl)
  +gtot : {GC.GC.Total(kids, groups)
           == NodeCost.NodeCost.kid_sum(g, kids, S) : Nat} =
    Equal.trans(Nat, GC.GC.Total(kids, groups),
      GC.GC.Total(kids, Groups.groups_build(g, S, Nil{})),
      NodeCost.NodeCost.kid_sum(g, kids, S),
      Equal.cong(+List<Groups.Group>, Nat, z => GC.GC.Total(kids, z),
        groups, Groups.groups_build(g, S, Nil{}), eg),
      GC.GC.groups_build_total(g, kids, S))
  +sl3 : {Nat.is_le(OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n),
                   NodeCost.NodeCost.kid_sum(g, kids, S)) == True{} : Bool} =
    Fold.OQ.le_cong_r(OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n),
      GC.GC.Total(kids, groups), NodeCost.NodeCost.kid_sum(g, kids, S), gtot, sl2)
  +sat : {Nat.is_le(SolveRef.sat_add(inf, Groups.len_words(S),
              OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n)),
            Nat.add(Groups.len_words(S),
              OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n)))
          == True{} : Bool} =
    Sums.OQ.sat_add_le_add(inf, Groups.len_words(S),
      OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n))
  +addl : {Nat.is_le(Nat.add(Groups.len_words(S),
                OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n)),
              Nat.add(Groups.len_words(S),
                NodeCost.NodeCost.kid_sum(g, kids, S))) == True{} : Bool} =
    NatProof.Nat.is_le_add_l(
      OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n),
      NodeCost.NodeCost.kid_sum(g, kids, S), Groups.len_words(S), sl3)
  +cn : {Tree.cost(Tree.Node{g, kids}, S)
         == Nat.add(Groups.len_words(S),
              NodeCost.NodeCost.kid_sum(g, kids, S)) : Nat} =
    Equal.trans(Nat, Tree.cost(Tree.Node{g, kids}, S),
      Nat.add(List.length(&2, +List<Nat>, S),
        NodeCost.NodeCost.kid_sum(g, kids, S)),
      Nat.add(Groups.len_words(S), NodeCost.NodeCost.kid_sum(g, kids, S)),
      NodeCost.NodeCost.cost_node(g, kids, S, depths), {==})
  +tot : {Nat.is_le(Nat.add(Groups.len_words(S),
               OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n)),
              Tree.cost(Tree.Node{g, kids}, S)) == True{} : Bool} =
    Fold.OQ.le_cong_r(Nat.add(Groups.len_words(S),
        OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n)),
      Nat.add(Groups.len_words(S), NodeCost.NodeCost.kid_sum(g, kids, S)),
      Tree.cost(Tree.Node{g, kids}, S), Equal.sym(Nat,
        Tree.cost(Tree.Node{g, kids}, S),
        Nat.add(Groups.len_words(S), NodeCost.NodeCost.kid_sum(g, kids, S)), cn),
      addl)
  +ks : {Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))
         == OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n) : Nat} =
    OV.OV.sum_fold(p, G, S, g, groups, Nil{}, 0n, inf)
  +leks : {Nat.is_le(Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)),
               NodeCost.NodeCost.kid_sum(g, kids, S)) == True{} : Bool} =
    Fold.OQ.le_cong_l(
      Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)),
      OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n),
      NodeCost.NodeCost.kid_sum(g, kids, S),
      ks, sl3)
  +sa : {Nat.is_le(SolveRef.sat_add(inf, Groups.len_words(S),
              Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))),
            Nat.add(Groups.len_words(S),
              Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))))
          == True{} : Bool} =
    Sums.OQ.sat_add_le_add(inf, Groups.len_words(S),
      Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)))
  +ad : {Nat.is_le(Nat.add(Groups.len_words(S),
               Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))),
              Nat.add(Groups.len_words(S),
                NodeCost.NodeCost.kid_sum(g, kids, S))) == True{} : Bool} =
    NatProof.Nat.is_le_add_l(
      Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)),
      NodeCost.NodeCost.kid_sum(g, kids, S), Groups.len_words(S), leks)
  +totx : {Nat.is_le(Nat.add(Groups.len_words(S),
                Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))),
               Tree.cost(Tree.Node{g, kids}, S)) == True{} : Bool} =
    Fold.OQ.le_cong_r(
      Nat.add(Groups.len_words(S),
        Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))),
      Nat.add(Groups.len_words(S), NodeCost.NodeCost.kid_sum(g, kids, S)),
      Tree.cost(Tree.Node{g, kids}, S), Equal.sym(Nat,
        Tree.cost(Tree.Node{g, kids}, S),
        Nat.add(Groups.len_words(S), NodeCost.NodeCost.kid_sum(g, kids, S)), cn),
      ad)
  +total_le : {Nat.is_le(SolveRef.sat_add(inf, Groups.len_words(S),
                   Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))),
                  Tree.cost(Tree.Node{g, kids}, S)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(
      SolveRef.sat_add(inf, Groups.len_words(S),
        Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))),
      Nat.add(Groups.len_words(S),
        Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))),
      Tree.cost(Tree.Node{g, kids}, S), sa, totx)
  +u : {Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))
        == SolveRef.sat_add(inf, Groups.len_words(S),
             Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)))
        : Nat} =
    OQ.ks_cost_unfold(inf, S, Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))
  Fold.OQ.le_cong_l(
    Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)),
    SolveRef.sat_add(inf, Groups.len_words(S),
      Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))),
    Tree.cost(Tree.Node{g, kids}, S), u, total_le)
