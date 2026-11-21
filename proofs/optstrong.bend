# Optimality and finiteness from one traversal of the given tree.
#
# The law exhibits the tree the solver returns, so it needs two facts about the
# same valid tree: the search costs at most that tree (the optimality bound) and
# the search's stored cost is finite (completeness). Both proofs walk the tree
# and read the same per-class child subtrees out of it, so this module merges
# the two walks: one class traversal produces the cost comparison and the class
# size/cost bounds together, and one structural recursion carries both facts.
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
import ./optguess.bend as Guess
import ./optcost.bend as Cost
import ./optcomplete.bend as Comp
import ./groupsmeasure.bend as GM
import ./groupcost.bend as GC
import ./nodecost.bend as NodeCost
import ./solvevalid.bend as SV
import ./mainvalid.bend as MV
import ./cover.bend as Cover
import ./cover_oracle.bend as Cora
import ./cover_kids.bend as Ckids
import ./kids.bend as KidPr

# The merged node bound: the class comparison is a hypothesis.
def F2.node_le_pre(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +groups: +List<Groups.Group>,
    +kids: +List<Tree.Child>,
    +eg : {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    le: Sums.OQ.ClassLe(p, G, inf, groups, kids)) ->
  {Nat.is_le(Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, groups,
      Nil{}, 0n, inf)), Tree.cost(Tree.Node{g, kids}, S)) == True{} : Bool}:
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
  +cn : {Tree.cost(Tree.Node{g, kids}, S)
         == Nat.add(Groups.len_words(S),
              NodeCost.NodeCost.kid_sum(g, kids, S)) : Nat} =
    Equal.trans(Nat, Tree.cost(Tree.Node{g, kids}, S),
      Nat.add(List.length(&2, +List<Nat>, S),
        NodeCost.NodeCost.kid_sum(g, kids, S)),
      Nat.add(Groups.len_words(S), NodeCost.NodeCost.kid_sum(g, kids, S)),
      NodeCost.NodeCost.cost_node(g, kids, S, depths), {==})
  +ks : {Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))
         == OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n) : Nat} =
    OV.OV.sum_fold(p, G, S, g, groups, Nil{}, 0n, inf)
  +leks : {Nat.is_le(Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)),
               NodeCost.NodeCost.kid_sum(g, kids, S)) == True{} : Bool} =
    Fold.OQ.le_cong_l(
      Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)),
      OV.OV.sumL(inf, Sat.SB.child_costs(p, G, groups, inf), 0n),
      NodeCost.NodeCost.kid_sum(g, kids, S), ks, sl3)
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
    Node.OQ.ks_cost_unfold(inf, S, Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))
  Fold.OQ.le_cong_l(
    Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)),
    SolveRef.sat_add(inf, Groups.len_words(S),
      Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))),
    Tree.cost(Tree.Node{g, kids}, S), u, total_le)

# The two facts about one tree at the next fuel.
def F2.Strong(p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, T: Tree.Tree) -> Type:
  {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S),
     G, S, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
     Eval.Eval.dummy_zero())), Tree.cost(T, S)) == True{} : Bool}
  & Comp.FC.Facts(1n+p, inf, G, S)

# The same, stated about the guess-fold expression the node step produces.
def F2.StrongGuess(p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, T: Tree.Tree) -> Type:
  {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
     Eval.Eval.dummy_inf(inf))), Tree.cost(T, S)) == True{} : Bool}
  & Comp.FC.GuessFacts(p, inf, G, S)

# Eliminate a computed pair with a continuation.
def F2.use_pair(-R: Type, -A: Type, -B: Type, p: A & B,
    k: A -> B -> R) -> R:
  match p:
    case (a, b):
      k(a, b)

# Convert the node step's facts to the job's facts.
def F2.strong_of_guess(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +T: Tree.Tree, f: F2.StrongGuess(p, inf, G, S, T)) ->
  F2.Strong(p, inf, G, S, T):
  +e : {SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())
       == Eval.Eval.guesses(1n+p, G, S, inf, G, Eval.Eval.dummy_inf(inf))
       : SolveRef.Best} =
    Eval.Eval.guesses_step(p, G, S, inf, G, Eval.Eval.dummy_inf(inf))
  F2.use_pair(F2.Strong(p, inf, G, S, T),
    {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
       Eval.Eval.dummy_inf(inf))), Tree.cost(T, S)) == True{} : Bool},
    Comp.FC.GuessFacts(p, inf, G, S), f,
    fo => ff =>
      (Fold.OQ.le_cong_l(
        Eval.Eval.cost_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S,
          inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
          Eval.Eval.dummy_zero())),
        Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
          Eval.Eval.dummy_inf(inf))),
        Tree.cost(T, S),
        Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
          SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S, inf, Nil{}, Nil{},
            0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()),
          Eval.Eval.guesses(1n+p, G, S, inf, G, Eval.Eval.dummy_inf(inf)), e),
        fo),
      Comp.FC.facts_of_guesses(p, G, S, inf, ff)))

# One class: its cost comparison and its size/cost bounds.
def F2.kid_both(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +kids: +List<Tree.Child>,
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +lt: {Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{} : Bool},
    kid: Cora.Cover.GroupKid(G, kids, Groups.Group{fb, ws}),
    job: Node.OQ.AJob(p, inf, G, ws),
    fjn: Comp.FC.FinJob(p, inf, G, ws),
    +hzw: {Nat.is_lt(Nat.mul(Groups.len_words(ws), Groups.len_words(ws)), inf)
           == True{} : Bool}) ->
  {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
     GC.GC.GroupCost(kids, Groups.Group{fb, ws})) == True{} : Bool}
  & ({Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{} : Bool}
     & {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
          Nat.mul(Groups.len_words(ws), Groups.len_words(ws))) == True{} : Bool}):
  match kid:
    case Tuple{T, kp}:
      (e_look, valid) = kp
      +hc : {GC.GC.GroupCost(kids, Groups.Group{fb, ws})
             == Tree.cost(T, ws) : Nat} =
        Cover.Cover.group_cost_some(kids, fb, ws, T, e_look)
      +o : {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
              Tree.cost(T, ws)) == True{} : Bool} =
        job(T, valid)
      +le : {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
                GC.GC.GroupCost(kids, Groups.Group{fb, ws})) == True{} : Bool} =
        Fold.OQ.le_cong_r(Sat.SB.child_cost(p, G, ws, inf), Tree.cost(T, ws),
          GC.GC.GroupCost(kids, Groups.Group{fb, ws}), Equal.sym(Nat,
            GC.GC.GroupCost(kids, Groups.Group{fb, ws}), Tree.cost(T, ws), hc), o)
      Comp.FC.use_pair(
        {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
           GC.GC.GroupCost(kids, Groups.Group{fb, ws})) == True{} : Bool}
        & ({Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{} : Bool}
           & {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
                Nat.mul(Groups.len_words(ws), Groups.len_words(ws))) == True{}
              : Bool}),
        {Nat.is_lt(Sat.SB.child_cost(p, G, ws, inf), inf) == True{} : Bool},
        {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
           Nat.mul(Groups.len_words(ws), Groups.len_words(ws))) == True{} : Bool},
        fjn(hzw)(T)(valid),
        fl => fr => (le, (lt, fr)))

# Every class: the cost comparison and the class bounds, from one walk.
def F2.class_both(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +kids: +List<Tree.Child>, +groups: +List<Groups.Group>,
    gk: Cora.Cover.GroupKids(G, kids, groups),
    jobs: Node.OQ.AClass(p, inf, G, groups),
    fj: Comp.FC.FinClass(p, inf, G, groups),
    sm: GM.GM.GroupsSmaller(S, groups),
    +hz: {Nat.is_lt(Nat.mul(Groups.len_words(S), Groups.len_words(S)), inf)
          == True{} : Bool}) ->
  Sums.OQ.ClassLe(p, G, inf, groups, kids)
  & CBK.CBK.ClassFits(p, G, S, groups, inf, Groups.len_words(S)):
  match groups:
    case Nil{}:
      (Unit{}, Unit{})
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          (kid, gkt) = gk
          (job, jt) = jobs
          (fjn, fjt) = fj
          (lt0, smt) = sm
          +lt : {Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{}
                 : Bool} = lt0
          +hzw : {Nat.is_lt(Nat.mul(Groups.len_words(ws), Groups.len_words(ws)),
                    inf) == True{} : Bool} =
            Comp.FC.sq_lt(inf, Groups.len_words(ws), Groups.len_words(S), lt, hz)
          Comp.FC.use_pair(
            Sums.OQ.ClassLe(p, G, inf, groups, kids)
            & CBK.CBK.ClassFits(p, G, S, groups, inf, Groups.len_words(S)),
            {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
               GC.GC.GroupCost(kids, Groups.Group{f, ws})) == True{} : Bool},
            ({Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{}
              : Bool}
             & {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
                  Nat.mul(Groups.len_words(ws), Groups.len_words(ws))) == True{}
                : Bool}),
            F2.kid_both(p, inf, G, S, kids, f, ws, lt, kid, job, fjn, hzw),
            lh => fh =>
              Comp.FC.use_pair(
                Sums.OQ.ClassLe(p, G, inf, groups, kids)
                & CBK.CBK.ClassFits(p, G, S, groups, inf, Groups.len_words(S)),
                Sums.OQ.ClassLe(p, G, inf, rest, kids),
                CBK.CBK.ClassFits(p, G, S, rest, inf, Groups.len_words(S)),
                F2.class_both(p, inf, G, S, kids, rest, gkt, jt, fjt, smt, hz),
                lr => fr => ((lh, lr), (fh, fr))))
