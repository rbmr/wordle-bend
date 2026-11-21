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

# A filtered strong obligation with a true test is a strong obligation.
def F2.sclassif_true(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    +us: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{}
         : Bool},
    f: F2.StrongClassIf(fuel, inf, G, b, Groups.groups_build(g, S, Nil{}))) ->
  F2.StrongClass(fuel, inf, G, Groups.groups_build(g, S, Nil{})):
  match b:
    case True{}:
      f
    case False{}:
      Empty.absurd(F2.StrongClass(fuel, inf, G, Groups.groups_build(g, S, Nil{})),
        Logic.Proof.false_ne_true(Equal.trans(Bool, False{},
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), True{}, eb, us)))

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

# The node step's guess-fold facts, as the tree's two facts.
def F2.finish_pack(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +T: Tree.Tree,
    o: {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
         Eval.Eval.dummy_inf(inf))), Tree.cost(T, S)) == True{} : Bool},
    fl: {Nat.is_lt(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
          Eval.Eval.dummy_inf(inf))), inf) == True{} : Bool},
    fr: {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
          Eval.Eval.dummy_inf(inf))),
          Nat.mul(Groups.len_words(S), Groups.len_words(S))) == True{} : Bool}) ->
  F2.SF(1n+p, inf, G, S, T):
  +e : {SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())
       == Eval.Eval.guesses(1n+p, G, S, inf, G, Eval.Eval.dummy_inf(inf))
       : SolveRef.Best} =
    Eval.Eval.guesses_step(p, G, S, inf, G, Eval.Eval.dummy_inf(inf))
  +ec : {Eval.Eval.cost_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S,
            inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
            Eval.Eval.dummy_zero()))
          == Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
               Eval.Eval.dummy_inf(inf))) : Nat} =
    Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
      SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()),
      Eval.Eval.guesses(1n+p, G, S, inf, G, Eval.Eval.dummy_inf(inf)), e)
  (Fold.OQ.le_cong_l(
     Eval.Eval.cost_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S, inf,
       Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())),
     Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
       Eval.Eval.dummy_inf(inf))), Tree.cost(T, S), ec, o),
   (CBN.CB.lt_eq_l(inf,
      Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
        Eval.Eval.dummy_inf(inf))),
      Eval.Eval.cost_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S, inf,
        Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())),
      Equal.sym(Nat,
        Eval.Eval.cost_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S,
          inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
          Eval.Eval.dummy_zero())),
        Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
          Eval.Eval.dummy_inf(inf))), ec), fl),
    NatProof.Nat.is_le_eq_l(
      Nat.mul(Groups.len_words(S), Groups.len_words(S)),
      Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
        Eval.Eval.dummy_inf(inf))),
      Eval.Eval.cost_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S, inf,
        Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())),
      Equal.sym(Nat,
        Eval.Eval.cost_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S,
          inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
          Eval.Eval.dummy_zero())),
        Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
          Eval.Eval.dummy_inf(inf))), ec), fr)))

# A job moved along an equality of candidate lists.
def F2.strongjob_transport(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S1: +List<+List<Nat>>, +S2: +List<+List<Nat>>,
    e: {S1 == S2 : +List<+List<Nat>>},
    j: F2.StrongJob(fuel, inf, G, S1)) -> F2.StrongJob(fuel, inf, G, S2):
  %e : F2.StrongJob(fuel, inf, G, _)
  j

# The node step of the merged induction.
def F2.strong_at(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +kids: +List<Tree.Child>,
    flatS: F2.StrongByGs(p, inf, G, S, G),
    v: Tree.Valid(Tree.Node{g, kids}, G, S), b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    all: F2.AllStrongBound(p, inf, G, kids),
    +hz: {Nat.is_lt(Nat.mul(Groups.len_words(S), Groups.len_words(S)), inf)
          == True{} : Bool}) -> F2.SF(1n+p, inf, G, S, Tree.Node{g, kids}):
  ((wg, kidsin), depths) = v
  match b:
    case True{}:
      +wgm : {Tree.member_word(g, G) == True{} : Bool} = wg
      +n : Nat = Groups.len_words(S)
      +gb : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
      +items : Eval.KS = Eval.Eval.items(p, G, S, g, gb, Nil{}, 0n, inf)
      +cs : +List<Nat> = Sat.SB.child_costs(p, G, gb, inf)
      +us : {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{}
             : Bool} =
        Equal.sym(Bool, b, Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
          eb)
      sclass : F2.StrongClass(p, inf, G, gb) =
        F2.sclassif_true(p, inf, G, S, g,
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==}, us,
          F2.sbygs_at(p, inf, G, S, G, g, wgm, flatS))
      +leg : {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
                  Eval.Eval.dummy_inf(inf))),
                  Fold.OQ.ks_cost(inf, S, items)) == True{} : Bool} =
        Guess.OQ.guesses_le_cand(p, G, S, inf, G, g, Eval.Eval.dummy_inf(inf),
          wgm, us)
      Cover.Cover.depths_agd(
        F2.SF(1n+p, inf, G, S, Tree.Node{g, kids}),
        g, kids, S, Nil{}, depths, Unit{},
        ok => d2 =>
          Cover.Cover.depths_agd(
            F2.SF(1n+p, inf, G, S, Tree.Node{g, kids}),
            g, kids, S, Nil{}, d2, Unit{},
            ok2 => d3 =>
              +neokb : {Ckids.Cover.all_ne(gb) == True{} : Bool} =
                Ckids.Cover.groups_build_ne(g, S, Nil{}, {==})
              +kb : {Ckids.Cover.kids_in_b(kids, G) == True{} : Bool} =
                Ckids.Cover.kids_in_to_b(kids, G, kidsin)
              Ckids.Cover.groupkids_from(
                F2.SF(1n+p, inf, G, S, Tree.Node{g, kids}),
                G, g, kids, gb, kb, neokb, ok2,
                gk =>
                  sm : GM.GM.GroupsSmaller(S, gb) =
                    GM.GM.groups_smaller_sound(S, gb, us)
                  Comp.FC.use_pair(
                    F2.SF(1n+p, inf, G, S, Tree.Node{g, kids}),
                    Sums.OQ.ClassLe(p, G, inf, gb, kids),
                    CBK.CBK.ClassFits(p, G, S, gb, inf, n),
                    F2.class_both(p, inf, G, S, kids, gb, gk, sclass, sm, hz),
                    le => fits =>
                      +bsq : {Nat.is_le(Nat.add(n, CBN.CB.sum(cs)), Nat.mul(n, n))
                              == True{} : Bool} =
                        CBK.CBK.node_bound_sq(p, G, S, g, inf, fits)
                      +leks : {Nat.is_le(Fold.OQ.ks_cost(inf, S, items),
                                  Nat.add(n, CBN.CB.sum(cs))) == True{} : Bool} =
                        Fold.OQ.le_cong_l(Fold.OQ.ks_cost(inf, S, items),
                          SolveRef.sat_add(inf, n, Sat.SB.ks_sum(items)),
                          Nat.add(n, CBN.CB.sum(cs)),
                          Node.OQ.ks_cost_unfold(inf, S, items),
                          NatProof.Nat.is_le_trans(
                            SolveRef.sat_add(inf, n, Sat.SB.ks_sum(items)),
                            Nat.add(n, Sat.SB.ks_sum(items)),
                            Nat.add(n, CBN.CB.sum(cs)),
                            Sums.OQ.sat_add_le_add(inf, n, Sat.SB.ks_sum(items)),
                            NatProof.Nat.is_le_add_l(Sat.SB.ks_sum(items),
                              CBN.CB.sum(cs), n,
                              Fold.OQ.le_cong_l(Sat.SB.ks_sum(items),
                                OV.OV.sumL(inf, cs, 0n), CBN.CB.sum(cs),
                                OV.OV.sum_fold(p, G, S, g, gb, Nil{}, 0n, inf),
                                Fold.OQ.le_cong_r(OV.OV.sumL(inf, cs, 0n),
                                  Nat.add(0n, CBN.CB.sum(cs)), CBN.CB.sum(cs), {==},
                                  Comp.FC.sumL_le(inf, cs, 0n))))))
                      +f2 : {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G,
                               S, inf, G, Eval.Eval.dummy_inf(inf))), Nat.mul(n, n))
                             == True{} : Bool} =
                        NatProof.Nat.is_le_trans(
                          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
                            Eval.Eval.dummy_inf(inf))),
                          Nat.add(n, CBN.CB.sum(cs)), Nat.mul(n, n),
                          NatProof.Nat.is_le_trans(
                            Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
                              Eval.Eval.dummy_inf(inf))),
                            Fold.OQ.ks_cost(inf, S, items),
                            Nat.add(n, CBN.CB.sum(cs)), leg, leks),
                          bsq)
                      F2.finish_pack(p, G, S, inf, Tree.Node{g, kids},
                        NatProof.Nat.is_le_trans(
                          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
                            Eval.Eval.dummy_inf(inf))),
                          Fold.OQ.ks_cost(inf, S, items),
                          Tree.cost(Tree.Node{g, kids}, S), leg,
                          F2.node_le_pre(p, inf, G, S, g, gb, kids, {==}, d3, le)),
                        NatProof.Nat.is_le_lt_trans(
                          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
                            Eval.Eval.dummy_inf(inf))),
                          Nat.mul(n, n), inf, f2, hz),
                        f2)))))
    case False{}:
      +ef : {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
             == False{} : Bool} =
        Equal.sym(Bool, b, Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
          eb)
      F2.strong_unusable(p, inf, G, S, g, kids,
        Ind.OQ.unusable_kid(G, S, g, kids, Groups.groups_build(g, S, Nil{})
          , {==}, depths, kidsin, ef),
        flatS, all, hz)

# The bounds for every child of a list, by structural recursion.
def F2.strong_bounds(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +kids: +List<Tree.Child>) -> F2.AllStrongBound(p, inf, G, kids):
  match kids:
    case Nil{}:
      Unit{}
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          match child:
            case Tree.Node{+g, +ckids}:
              ((+S => flatS => hz => v =>
                  F2.strong_at(p, inf, G, S, g, ckids, flatS, v,
                    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                    {==}, F2.strong_bounds(p, inf, G, ckids), hz)),
               F2.strong_bounds(p, inf, G, rest))

# Split the strong conjunction at an append.
def F2.strongflat_append(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +xs: +List<+List<+List<Nat>>>, +ys: +List<+List<+List<Nat>>>,
    f: F2.StrongFlat(fuel, inf, G,
        List.append(&2, +List<+List<Nat>>, xs, ys))) ->
  F2.StrongFlat(fuel, inf, G, xs) & F2.StrongFlat(fuel, inf, G, ys):
  match xs:
    case Nil{}:
      Tuple{Unit{}, f}
    case Con{S, t}:
      (j, fr) = f
      Comp.FC.use_pair(
        F2.StrongFlat(fuel, inf, G, S <> t) & F2.StrongFlat(fuel, inf, G, ys),
        F2.StrongFlat(fuel, inf, G, t), F2.StrongFlat(fuel, inf, G, ys),
        F2.strongflat_append(fuel, inf, G, t, ys, fr),
        ft => fys => Tuple{Tuple{j, ft}, fys})

# The strong class conjunction read from a flat conjunction.
def F2.strongclass_of_flat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>,
    f: F2.StrongFlat(fuel, inf, G, MV.MV.next_groups(groups))) ->
  F2.StrongClass(fuel, inf, G, groups):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          (fh, ft) = f
          (fh, F2.strongclass_of_flat(fuel, inf, G, rest, ft))

# A filtered strong conjunction is a strong conjunction when the test is true.
def F2.strongclassif_of_flat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    f: F2.StrongFlat(fuel, inf, G,
         MV.MV.classes_b(b, Groups.groups_build(g, S, Nil{})))) ->
  F2.StrongClassIf(fuel, inf, G, b, Groups.groups_build(g, S, Nil{})):
  match b:
    case True{}:
      F2.strongclass_of_flat(fuel, inf, G, Groups.groups_build(g, S, Nil{}), f)
    case False{}:
      Unit{}

# The per-guess class conjunction of a job, from the flat conjunction.
def F2.strongbygs_of_flat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>,
    f: F2.StrongFlat(fuel, inf, G, MV.MV.next_guess(gs, S))) ->
  F2.StrongByGs(fuel, inf, G, S, gs):
  match gs:
    case Nil{}:
      Unit{}
    case Con{g, t}:
      Comp.FC.use_pair(
        F2.StrongByGs(fuel, inf, G, S, g <> t),
        F2.StrongFlat(fuel, inf, G, MV.MV.classes(g, S)),
        F2.StrongFlat(fuel, inf, G, MV.MV.next_guess(t, S)),
        F2.strongflat_append(fuel, inf, G, MV.MV.classes(g, S),
          MV.MV.next_guess(t, S), f),
        fg => ft =>
          (F2.strongclassif_of_flat(fuel, inf, G, S, g,
             Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==}, fg),
           F2.strongbygs_of_flat(fuel, inf, G, S, t, ft)))

# The zero-fuel cost of a nonempty guess list is zero.
def F2.zero_cost_cons(+inf: Nat, +g: +List<Nat>, +t: +List<+List<Nat>>,
    +hz: {Nat.is_lt(Nat.mul(Groups.len_words(Nil{}), Groups.len_words(Nil{})), inf)
          == True{} : Bool}) ->
  {Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}),
     g <> t, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
     Eval.Eval.dummy_zero())) == 0n : Nat}:
  +eb : {SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf,
            Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())
          == Eval.Eval.guesses(0n, g <> t, Nil{}, inf, g <> t,
               Eval.Eval.dummy_inf(inf)) : SolveRef.Best} =
    Eval.Eval.guesses_zero(g <> t, inf, g <> t, Eval.Eval.dummy_inf(inf))
  +ec : {Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}),
              g <> t, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
              Eval.Eval.dummy_zero()))
          == Eval.Eval.cost_of(Eval.Eval.guesses(0n, g <> t, Nil{}, inf, g <> t,
               Eval.Eval.dummy_inf(inf))) : Nat} =
    Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
      SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf,
        Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()),
      Eval.Eval.guesses(0n, g <> t, Nil{}, inf, g <> t, Eval.Eval.dummy_inf(inf)), eb)
  Equal.trans(Nat,
    Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}),
      g <> t, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
      Eval.Eval.dummy_zero())),
    Eval.Eval.cost_of(Eval.Eval.guesses(0n, g <> t, Nil{}, inf, g <> t,
      Eval.Eval.dummy_inf(inf))),
    0n, ec, Cost.OC.zero_first_cost(g <> t, inf, g, t, hz))

# Zero fuel with no guesses cannot have a valid tree.
def F2.strong_zero_empty(+inf: Nat, T: Tree.Tree, v: Tree.Valid(T, Nil{}, Nil{}),
    +hz: {Nat.is_lt(Nat.mul(Groups.len_words(Nil{}), Groups.len_words(Nil{})), inf)
          == True{} : Bool}) -> F2.SF(0n, inf, Nil{}, Nil{}, T):
  match T:
    case Tree.Node{g, kids}:
      (ti, ad) = v
      (wg, kidsin) = ti
      Empty.absurd(F2.SF(0n, inf, Nil{}, Nil{}, Tree.Node{g, kids}),
        Logic.Proof.false_ne_true(wg))

# Zero fuel with a nonempty guess list: cost zero for an empty candidate list.
def F2.strong_zero_cons(+inf: Nat, +g: +List<Nat>, +t: +List<+List<Nat>>,
    +T: Tree.Tree,
    +hz: {Nat.is_lt(Nat.mul(Groups.len_words(Nil{}), Groups.len_words(Nil{})), inf)
          == True{} : Bool}) -> F2.SF(0n, inf, g <> t, Nil{}, T):
  +ec : {Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}),
             g <> t, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
             Eval.Eval.dummy_zero())) == 0n : Nat} =
    F2.zero_cost_cons(inf, g, t, hz)
  (NatProof.Nat.is_le_eq_l(0n, 0n,
     Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(g <> t, Nil{}),
       g <> t, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
       Eval.Eval.dummy_zero())),
     Equal.sym(Nat, Eval.Eval.cost_of(SolveRef.step(0n,
       SolveRef.mk_schedule(g <> t, Nil{}), g <> t, Nil{}, inf, Nil{}, Nil{}, 0n,
       Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())), 0n, ec),
     NatProof.Nat.is_le_refl(0n)),
   Comp.FC.fin_zero_cons(inf, g, t, hz))

# Zero fuel: every job is empty.
def F2.strong_zero(+inf: Nat, +G: +List<+List<Nat>>) ->
  F2.StrongJob(0n, inf, G, Nil{}):
  match G:
    case Nil{}:
      hz => T => v => F2.strong_zero_empty(inf, T, v, hz)
    case Con{g, t}:
      hz => T => v => F2.strong_zero_cons(inf, g, t, T, hz)

# One step of the fuel: every job at the next level gets its obligation.
def F2.strong_job_at(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, T: Tree.Tree, v: Tree.Valid(T, G, S),
    flatS: F2.StrongByGs(p, inf, G, S, G),
    +hz: {Nat.is_lt(Nat.mul(Groups.len_words(S), Groups.len_words(S)), inf)
          == True{} : Bool}) -> F2.SF(1n+p, inf, G, S, T):
  match T:
    case Tree.Node{+g, +kids}:
      F2.strong_at(p, inf, G, S, g, kids, flatS, v,
        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==},
        F2.strong_bounds(p, inf, G, kids), hz)

def F2.strong_job_wrap(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, flatS: F2.StrongByGs(p, inf, G, S, G)) ->
  F2.StrongJob(1n+p, inf, G, S):
  hz => T => v => F2.strong_job_at(p, inf, G, S, T, v, flatS, hz)

# One step of the fuel on the flat conjunction.
def F2.strong_step(+inf: Nat, +p: Nat, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>,
    ff: F2.StrongFlat(p, inf, G, MV.MV.next_jobs(G, jobs))) ->
  F2.StrongFlat(1n+p, inf, G, jobs):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{S, t}:
      Comp.FC.use_pair(
        F2.StrongFlat(1n+p, inf, G, S <> t),
        F2.StrongFlat(p, inf, G, MV.MV.next_guess(G, S)),
        F2.StrongFlat(p, inf, G, MV.MV.next_jobs(G, t)),
        F2.strongflat_append(p, inf, G, MV.MV.next_guess(G, S),
          MV.MV.next_jobs(G, t), ff),
        fS => ft =>
          Tuple{F2.strong_job_wrap(p, inf, G, S,
                  F2.strongbygs_of_flat(p, inf, G, S, G, fS)),
                F2.strong_step(inf, p, G, t, ft)})

# Zero fuel: every job is the empty candidate list.
def F2.strong_flat_zero(+inf: Nat, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>, bounds: MV.MV.Bounds(0n, jobs)) ->
  F2.StrongFlat(0n, inf, G, jobs):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{S, t}:
      (ble, bt) = bounds
      +eS : {S == Nil{} : +List<+List<Nat>>} =
        MV.MV.nil_of_len_zero(S,
          NatProof.Nat.eq_zero_of_le_zero(Groups.len_words(S), ble))
      Tuple{F2.strongjob_transport(0n, inf, G, Nil{}, S,
               Equal.sym(+List<+List<Nat>>, S, Nil{}, eS), F2.strong_zero(inf, G)),
            F2.strong_flat_zero(inf, G, t, bt)}

# The fuel induction on the flat conjunction of jobs.
def F2.strong_flat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>, bounds: MV.MV.Bounds(fuel, jobs)) ->
  F2.StrongFlat(fuel, inf, G, jobs):
  match fuel:
    case 0n:
      F2.strong_flat_zero(inf, G, jobs, bounds)
    case 1n+p:
      F2.strong_step(inf, p, G, jobs,
        F2.strong_flat(p, inf, G, MV.MV.next_jobs(G, jobs),
          MV.MV.next_bounds(p, G, jobs, bounds)))


# Optimality and finiteness from one traversal of the given valid tree.
def F2.optimal_and_finite(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +T2: Tree.Tree, v: Tree.Valid(T2, G, C)) ->
  {Nat.is_le(Eval.Eval.cost_of(MV.MV.solve_best(G, C)), Tree.cost(T2, C))
   == True{} : Bool}
  & {Nat.is_lt(Eval.Eval.cost_of(MV.MV.solve_best(G, C)),
      SolveRef.inf_of(Groups.len_words(C))) == True{} : Bool}:
  match C:
    case Nil{}:
      Comp.FC.use_pair(
        {Nat.is_le(Eval.Eval.cost_of(MV.MV.solve_best(G, Nil{})),
           Tree.cost(T2, Nil{})) == True{} : Bool}
        & {Nat.is_lt(Eval.Eval.cost_of(MV.MV.solve_best(G, Nil{})),
            SolveRef.inf_of(Groups.len_words(Nil{}))) == True{} : Bool},
        {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(G, Nil{}),
           G, Nil{}, SolveRef.inf_of(Groups.len_words(Nil{})), Nil{}, Nil{}, 0n,
           Eval.Eval.dummy_inf(SolveRef.inf_of(Groups.len_words(Nil{}))),
           Eval.Eval.dummy_zero())), Tree.cost(T2, Nil{})) == True{} : Bool},
        Comp.FC.Facts(0n, SolveRef.inf_of(Groups.len_words(Nil{})), G, Nil{}),
        F2.strong_zero(SolveRef.inf_of(Groups.len_words(Nil{})), G)(CBN.CB.lt_add_one(Nat.mul(Groups.len_words(Nil{}), Groups.len_words(Nil{}))))(T2)(v),
        o => far =>
          Comp.FC.use_pair(
            {Nat.is_le(Eval.Eval.cost_of(MV.MV.solve_best(G, Nil{})),
               Tree.cost(T2, Nil{})) == True{} : Bool}
            & {Nat.is_lt(Eval.Eval.cost_of(MV.MV.solve_best(G, Nil{})),
                SolveRef.inf_of(Groups.len_words(Nil{}))) == True{} : Bool},
            {Nat.is_lt(Eval.Eval.cost_of(SolveRef.step(0n,
               SolveRef.mk_schedule(G, Nil{}), G, Nil{},
               SolveRef.inf_of(Groups.len_words(Nil{})), Nil{}, Nil{}, 0n,
               Eval.Eval.dummy_inf(SolveRef.inf_of(Groups.len_words(Nil{}))),
               Eval.Eval.dummy_zero())),
               SolveRef.inf_of(Groups.len_words(Nil{}))) == True{} : Bool},
            {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(0n,
               SolveRef.mk_schedule(G, Nil{}), G, Nil{},
               SolveRef.inf_of(Groups.len_words(Nil{})), Nil{}, Nil{}, 0n,
               Eval.Eval.dummy_inf(SolveRef.inf_of(Groups.len_words(Nil{}))),
               Eval.Eval.dummy_zero())),
               Nat.mul(Groups.len_words(Nil{}), Groups.len_words(Nil{}))) == True{}
             : Bool},
            far,
            fl => fr => (o, fl)))
    case Con{g0, t0}:
      +p : Nat = Groups.len_words(t0)
      +n : Nat = Groups.len_words(g0 <> t0)
      +inf : Nat = SolveRef.inf_of(n)
      bounds : MV.MV.Bounds(1n+p, (g0 <> t0) <> Nil{}) =
        Tuple{NatProof.Nat.is_le_refl(n), Unit{}}
      nb : MV.MV.Bounds(p, MV.MV.next_jobs(G, (g0 <> t0) <> Nil{})) =
        MV.MV.next_bounds(p, G, (g0 <> t0) <> Nil{}, bounds)
      ff : F2.StrongFlat(p, inf, G, MV.MV.next_jobs(G, (g0 <> t0) <> Nil{})) =
        F2.strong_flat(p, inf, G, MV.MV.next_jobs(G, (g0 <> t0) <> Nil{}), nb)
      +hz : {Nat.is_lt(Nat.mul(n, n), inf) == True{} : Bool} =
        CBN.CB.lt_add_one(Nat.mul(n, n))
      Comp.FC.use_pair(
        {Nat.is_le(Eval.Eval.cost_of(MV.MV.solve_best(G, g0 <> t0)),
           Tree.cost(T2, g0 <> t0)) == True{} : Bool}
        & {Nat.is_lt(Eval.Eval.cost_of(MV.MV.solve_best(G, g0 <> t0)),
            SolveRef.inf_of(Groups.len_words(g0 <> t0))) == True{} : Bool},
        F2.StrongFlat(p, inf, G, MV.MV.next_guess(G, g0 <> t0)),
        F2.StrongFlat(p, inf, G, MV.MV.next_jobs(G, Nil{})),
        F2.strongflat_append(p, inf, G, MV.MV.next_guess(G, g0 <> t0),
          MV.MV.next_jobs(G, Nil{}), ff),
        fS => ft =>
          sb0 : F2.StrongByGs(p, inf, G, g0 <> t0, G) =
            F2.strongbygs_of_flat(p, inf, G, g0 <> t0, G, fS)
          Comp.FC.use_pair(
            {Nat.is_le(Eval.Eval.cost_of(MV.MV.solve_best(G, g0 <> t0)),
               Tree.cost(T2, g0 <> t0)) == True{} : Bool}
            & {Nat.is_lt(Eval.Eval.cost_of(MV.MV.solve_best(G, g0 <> t0)),
                SolveRef.inf_of(Groups.len_words(g0 <> t0))) == True{} : Bool},
            {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(1n+p,
               SolveRef.mk_schedule(G, g0 <> t0), G, g0 <> t0, inf, Nil{},
               Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())),
               Tree.cost(T2, g0 <> t0)) == True{} : Bool},
            Comp.FC.Facts(1n+p, inf, G, g0 <> t0),
            F2.strong_job_at(p, inf, G, g0 <> t0, T2, v, sb0, hz),
            o => far =>
              Comp.FC.use_pair(
                {Nat.is_le(Eval.Eval.cost_of(MV.MV.solve_best(G, g0 <> t0)),
                   Tree.cost(T2, g0 <> t0)) == True{} : Bool}
                & {Nat.is_lt(Eval.Eval.cost_of(MV.MV.solve_best(G, g0 <> t0)),
                    SolveRef.inf_of(Groups.len_words(g0 <> t0))) == True{} : Bool},
                {Nat.is_lt(Eval.Eval.cost_of(SolveRef.step(1n+p,
                   SolveRef.mk_schedule(G, g0 <> t0), G, g0 <> t0, inf, Nil{},
                   Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())),
                   inf) == True{} : Bool},
                {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(1n+p,
                   SolveRef.mk_schedule(G, g0 <> t0), G, g0 <> t0, inf, Nil{},
                   Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())),
                   Nat.mul(Groups.len_words(g0 <> t0),
                     Groups.len_words(g0 <> t0))) == True{} : Bool},
                far,
                fl => fr => (o, fl))))

