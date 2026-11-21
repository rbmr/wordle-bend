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
import ./cover_list.bend as Clist
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

# One tree's two facts at one fuel, uniformly over the candidate list.
def F2.SF(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, T: Tree.Tree) -> Type:
  {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(fuel, SolveRef.mk_schedule(G, S),
     G, S, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
     Eval.Eval.dummy_zero())), Tree.cost(T, S)) == True{} : Bool}
  & Comp.FC.Facts(fuel, inf, G, S)

# The obligation for one candidate list.
def F2.StrongJob(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>) -> Type:
  @hz: {Nat.is_lt(Nat.mul(Groups.len_words(S), Groups.len_words(S)), inf)
        == True{} : Bool}
  -> @T: Tree.Tree -> Tree.Valid(T, G, S) -> F2.SF(fuel, inf, G, S, T)

# The conjunction of the obligations over a list of candidate lists.
def F2.StrongFlat(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    jobs: +List<+List<+List<Nat>>>) -> Type:
  match jobs:
    case Nil{}:
      Unit
    case Con{S, t}:
      F2.StrongJob(fuel, inf, G, S) & F2.StrongFlat(fuel, inf, G, t)

# The obligations of one guess's classes.
def F2.StrongClass(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          F2.StrongJob(fuel, inf, G, ws) & F2.StrongClass(fuel, inf, G, rest)

# The class obligations of one guess, only when the guess is usable.
def F2.StrongClassIf(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>, b: Bool,
    +groups: +List<Groups.Group>) -> Type:
  match b:
    case True{}:
      F2.StrongClass(fuel, inf, G, groups)
    case False{}:
      Unit

# Move a filtered strong obligation to an equal test.
def F2.classif_b(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    b1: Bool, b2: Bool, +eb: {b1 == b2 : Bool}, +groups: +List<Groups.Group>,
    f: F2.StrongClassIf(fuel, inf, G, b1, groups)) ->
  F2.StrongClassIf(fuel, inf, G, b2, groups):
  %eb : F2.StrongClassIf(fuel, inf, G, _, groups)
  f

# Move a strong obligation to an equal group list.
def F2.classif_g(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>, +b: Bool,
    +g1: +List<Groups.Group>, +g2: +List<Groups.Group>,
    e: {g1 == g2 : +List<Groups.Group>},
    f: F2.StrongClassIf(fuel, inf, G, b, g1)) ->
  F2.StrongClassIf(fuel, inf, G, b, g2):
  %e : F2.StrongClassIf(fuel, inf, G, b, _)
  f

# The class obligations of every guess in a guess list.
def F2.StrongByGs(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{g, t}:
      F2.StrongClassIf(fuel, inf, G,
        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
        Groups.groups_build(g, S, Nil{}))
      & F2.StrongByGs(fuel, inf, G, S, t)

# One class: its cost comparison and its size/cost bounds from one application.
def F2.kid_both(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +kids: +List<Tree.Child>,
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +lt: {Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{} : Bool},
    kid: Cora.Cover.GroupKid(G, kids, Groups.Group{fb, ws}),
    sjob: F2.StrongJob(p, inf, G, ws),
    +hzw: {Nat.is_lt(Nat.mul(Groups.len_words(ws), Groups.len_words(ws)), inf)
           == True{} : Bool}) ->
  {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
     GC.GC.GroupCost(kids, Groups.Group{fb, ws})) == True{} : Bool}
  & ({Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{} : Bool}
     & {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
          Nat.mul(Groups.len_words(ws), Groups.len_words(ws))) == True{} : Bool}):
  match kid:
    case Tuple{+T, kp}:
      (e_look, valid) = kp
      +hc : {GC.GC.GroupCost(kids, Groups.Group{fb, ws})
             == Tree.cost(T, ws) : Nat} =
        Cover.Cover.group_cost_some(kids, fb, ws, T, e_look)
      Comp.FC.use_pair(
        {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
           GC.GC.GroupCost(kids, Groups.Group{fb, ws})) == True{} : Bool}
        & ({Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{} : Bool}
           & {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
                Nat.mul(Groups.len_words(ws), Groups.len_words(ws))) == True{}
              : Bool}),
        {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf), Tree.cost(T, ws)) == True{}
         : Bool},
        Comp.FC.Facts(p, inf, G, ws),
        sjob(hzw)(T)(valid),
        o => facts =>
          Comp.FC.use_pair(
            {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
               GC.GC.GroupCost(kids, Groups.Group{fb, ws})) == True{} : Bool}
            & ({Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{}
                : Bool}
               & {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
                    Nat.mul(Groups.len_words(ws), Groups.len_words(ws))) == True{}
                  : Bool}),
            {Nat.is_lt(Sat.SB.child_cost(p, G, ws, inf), inf) == True{} : Bool},
            {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
               Nat.mul(Groups.len_words(ws), Groups.len_words(ws))) == True{}
             : Bool},
            facts,
            fl => fr =>
              (Fold.OQ.le_cong_r(Sat.SB.child_cost(p, G, ws, inf),
                 Tree.cost(T, ws),
                 GC.GC.GroupCost(kids, Groups.Group{fb, ws}),
                 Equal.sym(Nat, GC.GC.GroupCost(kids, Groups.Group{fb, ws}),
                   Tree.cost(T, ws), hc), o),
               (lt, fr))))

# Every class: the cost comparison and the class bounds, from one walk.
def F2.class_both(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +kids: +List<Tree.Child>, +groups: +List<Groups.Group>,
    gk: Cora.Cover.GroupKids(G, kids, groups),
    sjobs: F2.StrongClass(p, inf, G, groups),
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
          (sjob, sjt) = sjobs
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
            F2.kid_both(p, inf, G, S, kids, f, ws, lt, kid, sjob, hzw),
            lh => fh =>
              Comp.FC.use_pair(
                Sums.OQ.ClassLe(p, G, inf, groups, kids)
                & CBK.CBK.ClassFits(p, G, S, groups, inf, Groups.len_words(S)),
                {Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{}
                 : Bool},
                {Nat.is_le(Sat.SB.child_cost(p, G, ws, inf),
                   Nat.mul(Groups.len_words(ws), Groups.len_words(ws))) == True{}
                 : Bool},
                fh,
                lt2 => fr2 =>
                  Comp.FC.use_pair(
                    Sums.OQ.ClassLe(p, G, inf, groups, kids)
                    & CBK.CBK.ClassFits(p, G, S, groups, inf,
                        Groups.len_words(S)),
                    Sums.OQ.ClassLe(p, G, inf, rest, kids),
                    CBK.CBK.ClassFits(p, G, S, rest, inf, Groups.len_words(S)),
                    F2.class_both(p, inf, G, S, kids, rest, gkt, sjt, smt, hz),
                    lr => fr => ((lh, lr), (lt2, (fr2, fr))))))


# The two facts of one tree, uniformly over the candidate list.
def F2.StrongBound(p: Nat, +inf: Nat, +G: +List<+List<Nat>>, T: Tree.Tree) -> Type:
  @S: +List<+List<Nat>> -> F2.StrongByGs(p, inf, G, S, G)
  -> @hz: {Nat.is_lt(Nat.mul(Groups.len_words(S), Groups.len_words(S)), inf)
           == True{} : Bool}
  -> Tree.Valid(T, G, S) -> F2.SF(1n+p, inf, G, S, T)

def F2.AllStrongBound(p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +kids: +List<Tree.Child>) -> Type:
  match kids:
    case Nil{}:
      Unit
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          F2.StrongBound(p, inf, G, child) & F2.AllStrongBound(p, inf, G, rest)

# A tree bound moved along an equality of trees.
def F2.strongbound_transport(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +t1: Tree.Tree, +t2: Tree.Tree, e: {t1 == t2 : Tree.Tree},
    b: F2.StrongBound(p, inf, G, t1)) -> F2.StrongBound(p, inf, G, t2):
  %e : F2.StrongBound(p, inf, G, _)
  b

# The lookup decision at the head child, with the test as a parameter.
def F2.strong_pick_head(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +child: Tree.Tree, +rest: +List<Tree.Child>,
    head: F2.StrongBound(p, inf, G, child), +T: Tree.Tree,
    e: {Tree.lookup(fb, Tree.Child{f, child} <> rest) == Some{T} : Maybe<Tree.Tree>},
    b: Bool, +eb: {b == Feedback.feedback_eq(fb, f) : Bool},
    k: {Tree.lookup(fb, rest) == Some{T} : Maybe<Tree.Tree>}
       -> F2.StrongBound(p, inf, G, T)) -> F2.StrongBound(p, inf, G, T):
  match b:
    case True{}:
      +e1 : {Some{child} == Cover.Cover.lookup_of(fb, f, child, rest,
                  Feedback.feedback_eq(fb, f)) : Maybe<&1, Tree.Tree>} =
        Cover.Cover.lk_true(fb, f, child, rest, eb)
      +e2 : {Some{child} == Some{T} : Maybe<&1, Tree.Tree>} =
        Cover.Cover.mtrans(Some{child},
          Cover.Cover.lookup_of(fb, f, child, rest, Feedback.feedback_eq(fb, f)),
          Some{T}, e1, e)
      +ec : {child == T : Tree.Tree} = KidPr.KidsProof.some_inj(child, T, e2)
      F2.strongbound_transport(p, inf, G, child, T, ec, head)
    case False{}:
      +e1 : {Tree.lookup(fb, rest) == Cover.Cover.lookup_of(fb, f, child, rest,
                  Feedback.feedback_eq(fb, f)) : Maybe<&1, Tree.Tree>} =
        Cover.Cover.lk_false(fb, f, child, rest, eb)
      +e2 : {Tree.lookup(fb, rest) == Some{T} : Maybe<&1, Tree.Tree>} =
        Cover.Cover.mtrans(Tree.lookup(fb, rest),
          Cover.Cover.lookup_of(fb, f, child, rest, Feedback.feedback_eq(fb, f)),
          Some{T}, e1, e)
      k(e2)

def F2.strong_pick(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +fb: +List<Feedback.Color>, +kids: +List<Tree.Child>,
    all: F2.AllStrongBound(p, inf, G, kids), +T: Tree.Tree,
    e: {Tree.lookup(fb, kids) == Some{T} : Maybe<&1, Tree.Tree>}) ->
  F2.StrongBound(p, inf, G, T):
  match kids:
    case Nil{}:
      Empty.absurd(F2.StrongBound(p, inf, G, T),
        KidPr.KidsProof.none_ne_some(T, e))
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          (head, tail) = all
          F2.strong_pick_head(p, inf, G, fb, f, child, rest, head, T, e,
            Feedback.feedback_eq(fb, f), {==},
            e2 => F2.strong_pick(p, inf, G, fb, rest, tail, T, e2))

# The unusable root: the bad class's valid child carries both facts.
def F2.strong_unusable(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +kids: +List<Tree.Child>,
    res: Ind.OQ.KidRes(G, S, g, kids),
    flatS: F2.StrongByGs(p, inf, G, S, G),
    all: F2.AllStrongBound(p, inf, G, kids),
    +hz: {Nat.is_lt(Nat.mul(Groups.len_words(S), Groups.len_words(S)), inf)
          == True{} : Bool}) -> F2.SF(1n+p, inf, G, S, Tree.Node{g, kids}):
  match res:
    case Tuple{+T2, r}:
      (valid_S, r2) = r
      (le2, r3) = r2
      (fb2, el2) = r3
      Comp.FC.use_pair(
        F2.SF(1n+p, inf, G, S, Tree.Node{g, kids}),
        {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S),
           G, S, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
           Eval.Eval.dummy_zero())), Tree.cost(T2, S)) == True{} : Bool},
        Comp.FC.Facts(1n+p, inf, G, S),
        F2.strong_pick(p, inf, G, fb2, kids, all, T2, el2)(S, flatS, hz, valid_S),
        o => f =>
          (NatProof.Nat.is_le_trans(
             Eval.Eval.cost_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S,
               inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
               Eval.Eval.dummy_zero())),
             Tree.cost(T2, S), Tree.cost(Tree.Node{g, kids}, S), o, le2),
           f))

# The class obligation of the guess a membership points at.
def F2.sbygs_head(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +h: +List<Nat>, +t: +List<+List<Nat>>,
    +g: +List<Nat>, +mem: {Tree.member_word(g, h <> t) == True{} : Bool},
    head: F2.StrongClassIf(fuel, inf, G,
      Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{})),
      Groups.groups_build(h, S, Nil{})),
    b: Bool, +eb: {b == Feedback.word_eq(g, h) : Bool},
    k: {Tree.member_word(g, t) == True{} : Bool}
       -> F2.StrongClassIf(fuel, inf, G,
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            Groups.groups_build(g, S, Nil{}))) ->
  F2.StrongClassIf(fuel, inf, G,
    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
    Groups.groups_build(g, S, Nil{})):
  match b:
    case True{}:
      +egh : {g == h : +List<Nat>} =
        Clist.Cover.word_eq_true(g, h,
          Equal.sym(Bool, True{}, Feedback.word_eq(g, h), eb))
      +egrp : {Groups.groups_build(g, S, Nil{})
               == Groups.groups_build(h, S, Nil{}) : +List<Groups.Group>} =
        Equal.cong(+List<Nat>, +List<Groups.Group>,
          x => Groups.groups_build(x, S, Nil{}), g, h, egh)
      +e_back : {Groups.groups_build(h, S, Nil{})
                 == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>} =
        Equal.sym(+List<Groups.Group>, Groups.groups_build(g, S, Nil{}),
          Groups.groups_build(h, S, Nil{}), egrp)
      +ebk : {Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{}))
              == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
              : Bool} =
        Equal.cong(+List<Groups.Group>, Bool, z => Groups.groups_smaller(S, z),
          Groups.groups_build(h, S, Nil{}), Groups.groups_build(g, S, Nil{}), e_back)
      F2.classif_b(fuel, inf, G,
        Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{})),
        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), ebk,
        Groups.groups_build(g, S, Nil{}),
        F2.classif_g(fuel, inf, G,
          Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{})),
          Groups.groups_build(h, S, Nil{}), Groups.groups_build(g, S, Nil{}),
          e_back, head))
    case False{}:
      +mt : {Tree.member_word(g, t) == True{} : Bool} =
        Cora.Cover.member_tail(g, h, t, b, eb, {==}, mem)
      k(mt)

def F2.sbygs_at(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>, +g: +List<Nat>,
    +mem: {Tree.member_word(g, gs) == True{} : Bool},
    f: F2.StrongByGs(fuel, inf, G, S, gs)) ->
  F2.StrongClassIf(fuel, inf, G,
    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
    Groups.groups_build(g, S, Nil{})):
  match gs:
    case Nil{}:
      Empty.absurd(
        F2.StrongClassIf(fuel, inf, G,
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
          Groups.groups_build(g, S, Nil{})),
        Logic.Proof.false_ne_true(mem))
    case Con{h, t}:
      (fh, ft) = f
      F2.sbygs_head(fuel, inf, G, S, h, t, g, mem, fh, Feedback.word_eq(g, h), {==},
        mt => F2.sbygs_at(fuel, inf, G, S, t, g, mt, ft))
