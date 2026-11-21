# The fuel induction of the optimality bound.
#
# The bound is proved at every fuel: if the candidate lists at the next level
# have at most `fuel` words, the search at that fuel costs at most any valid
# tree. The induction hands every class of every guess its own obligation at
# the smaller fuel, in one conjunction, and the node step of `optnode` reads
# them off. All the facts are `Bool` equalities, so they can be reused.
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
import ./cover_groups.bend as Cgrp
import ./cover_kids.bend as Ckids
import ./groups.bend as Grp
import ./cover_list.bend as Clist
import ./optimalvalue.bend as OV
import ./optsum.bend as Sums
import ./optfold.bend as Fold
import ./optnode.bend as Node
import ./optguess.bend as Guess
import ./kids.bend as KidPr
import ./mainvalid.bend as MV

# The class obligations of one guess, only when the guess is usable.
def OQ.AClassIf(b: Bool, fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>) -> Type:
  match b:
    case True{}:
      Node.OQ.AClass(fuel, inf, G, groups)
    case False{}:
      Unit

# The class obligations of every guess in a guess list, in guess order.
def OQ.AByGs(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{g, t}:
      OQ.AClassIf(Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
        fuel, inf, G, Groups.groups_build(g, S, Nil{}))
      & OQ.AByGs(fuel, inf, G, S, t)

# Split a flat conjunction of jobs at an append.
def OQ.aflat_append(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +xs: +List<+List<+List<Nat>>>, +ys: +List<+List<+List<Nat>>>,
    f: Node.OQ.AFlat(fuel, inf, G,
        List.append(&2, +List<+List<Nat>>, xs, ys))) ->
  Node.OQ.AFlat(fuel, inf, G, xs) & Node.OQ.AFlat(fuel, inf, G, ys):
  match xs:
    case Nil{}:
      Tuple{Unit{}, f}
    case Con{S, t}:
      (jh, jt) = f
      MV.MV.use_pair(
        (Node.OQ.AJob(fuel, inf, G, S) & Node.OQ.AFlat(fuel, inf, G, t))
        & Node.OQ.AFlat(fuel, inf, G, ys),
        Node.OQ.AFlat(fuel, inf, G, t), Node.OQ.AFlat(fuel, inf, G, ys),
        OQ.aflat_append(fuel, inf, G, t, ys, jt),
        ft => fys => Tuple{Tuple{jh, ft}, fys})

# A class list conjunction read from a flat conjunction over its classes.
def OQ.aclass_of_flat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>,
    f: Node.OQ.AFlat(fuel, inf, G, MV.MV.next_groups(groups))) ->
  Node.OQ.AClass(fuel, inf, G, groups):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          (fh, ft) = f
          (fh, OQ.aclass_of_flat(fuel, inf, G, rest, ft))

# A filtered class conjunction is a class conjunction when the test is true.
def OQ.aclass_if(+b: Bool, +eb: {b == True{} : Bool}, fuel: Nat, +inf: Nat,
    +G: +List<+List<Nat>>, +groups: +List<Groups.Group>,
    f: OQ.AClassIf(b, fuel, inf, G, groups)) ->
  Node.OQ.AClass(fuel, inf, G, groups):
  match b:
    case True{}:
      f
    case False{}:
      Empty.absurd(Node.OQ.AClass(fuel, inf, G, groups),
        Logic.Proof.true_ne_false(Equal.sym(Bool, b, True{}, eb)))

# Transport a class conjunction along an equality of group lists.
def OQ.aclass_transport(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +gs1: +List<Groups.Group>, +gs2: +List<Groups.Group>,
    e: {gs1 == gs2 : +List<Groups.Group>},
    f: Node.OQ.AClass(fuel, inf, G, gs1)) ->
  Node.OQ.AClass(fuel, inf, G, gs2):
  %e : Node.OQ.AClass(fuel, inf, G, _)
  f

# The head of the combined search: the class obligations of the guess that the
# membership points at, together with the fold's cost bound for it.
def OQ.jobs_le_head(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +h: +List<Nat>, +t: +List<+List<Nat>>,
    +g: +List<Nat>, +mem: {Tree.member_word(g, h <> t) == True{} : Bool},
    +us: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{}
         : Bool},
    b: Bool, +eb: {b == Feedback.word_eq(g, h) : Bool},
    f: OQ.AByGs(p, inf, G, S, h <> t), +best: SolveRef.Best,
    k: OQ.AByGs(p, inf, G, S, t) -> {Tree.member_word(g, t) == True{} : Bool}
       -> (Node.OQ.AClass(p, inf, G, Groups.groups_build(g, S, Nil{}))
           & {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf,
                 t, Eval.Eval.guess(p, G, S, h, inf, best))),
                 Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                   Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)))
               == True{} : Bool})) ->
  (Node.OQ.AClass(p, inf, G, Groups.groups_build(g, S, Nil{}))
   & {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf,
         h <> t, best)),
         Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
           Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)))
       == True{} : Bool}):
  match b:
    case True{}:
      (fh, ft) = f
      +egh : {g == h : +List<Nat>} =
        Clist.Cover.word_eq_true(g, h,
          Equal.sym(Bool, True{}, Feedback.word_eq(g, h), eb))
      +egrp : {Groups.groups_build(g, S, Nil{})
               == Groups.groups_build(h, S, Nil{}) : +List<Groups.Group>} =
        Equal.cong(+List<Nat>, +List<Groups.Group>,
          x => Groups.groups_build(x, S, Nil{}), g, h, egh)
      +ush : {Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{}))
              == True{} : Bool} =
        Equal.trans(Bool,
          Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{})),
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), True{},
          Equal.cong(+List<Groups.Group>, Bool,
            z => Groups.groups_smaller(S, z),
            Groups.groups_build(h, S, Nil{}), Groups.groups_build(g, S, Nil{}),
            Equal.sym(+List<Groups.Group>, Groups.groups_build(g, S, Nil{}),
              Groups.groups_build(h, S, Nil{}), egrp)),
          us)
      fac : Node.OQ.AClass(p, inf, G, Groups.groups_build(h, S, Nil{})) =
        OQ.aclass_if(Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{})),
          ush, p, inf, G, Groups.groups_build(h, S, Nil{}), fh)
      jobs : Node.OQ.AClass(p, inf, G, Groups.groups_build(g, S, Nil{})) =
        OQ.aclass_transport(p, inf, G, Groups.groups_build(h, S, Nil{}),
          Groups.groups_build(g, S, Nil{}),
          Equal.sym(+List<Groups.Group>, Groups.groups_build(g, S, Nil{}),
            Groups.groups_build(h, S, Nil{}), egrp), fac)
      +le_g : {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, h, inf, best)),
                 Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, h,
                   Groups.groups_build(h, S, Nil{}), Nil{}, 0n, inf)))
               == True{} : Bool} =
        Guess.OQ.guess_le_cand(p, G, S, h, inf, best, ush)
      +ceq1 : {Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, h,
                  Groups.groups_build(h, S, Nil{}), Nil{}, 0n, inf))
                == Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, h,
                  Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)) : Nat} =
        Equal.cong(+List<Groups.Group>, Nat,
          z => Fold.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, h, z, Nil{}, 0n, inf)),
          Groups.groups_build(h, S, Nil{}), Groups.groups_build(g, S, Nil{}),
          Equal.sym(+List<Groups.Group>, Groups.groups_build(g, S, Nil{}),
            Groups.groups_build(h, S, Nil{}), egrp))
      +ceq2 : {Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, h,
                  Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf))
                == Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                  Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)) : Nat} =
        Equal.cong(+List<Nat>, Nat,
          x => Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, x,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), h, g,
          Equal.sym(+List<Nat>, g, h, egh))
      +ceq : {Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, h,
                 Groups.groups_build(h, S, Nil{}), Nil{}, 0n, inf))
              == Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                   Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)) : Nat} =
        Equal.trans(Nat,
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, h,
            Groups.groups_build(h, S, Nil{}), Nil{}, 0n, inf)),
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, h,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), ceq1, ceq2)
      +le_g2 : {Nat.is_le(
                  Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, h, inf, best)),
                  Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                    Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)))
                == True{} : Bool} =
        Fold.OQ.le_cong_r(
          Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, h, inf, best)),
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, h,
            Groups.groups_build(h, S, Nil{}), Nil{}, 0n, inf)),
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), ceq, le_g)
      +bound : {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf,
                     h <> t, best)),
                   Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                     Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)))
                 == True{} : Bool} =
        NatProof.Nat.is_le_trans(
          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, h <> t, best)),
          Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, h, inf, best)),
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
          Fold.OQ.guesses_cost_le_acc(p, G, S, inf, t,
            Eval.Eval.guess(p, G, S, h, inf, best)),
          le_g2)
      (jobs, bound)
    case False{}:
      (fh, ft) = f
      +mt : {Tree.member_word(g, t) == True{} : Bool} =
        Cora.Cover.member_tail(g, h, t, b, eb, {==}, mem)
      k(ft, mt)

# The class obligations of the guess a membership points at, and the fold's
# cost bound for that same guess, from one traversal.
def OQ.jobs_le(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>, +g: +List<Nat>,
    +mem: {Tree.member_word(g, gs) == True{} : Bool},
    +us: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{}
         : Bool},
    f: OQ.AByGs(p, inf, G, S, gs), +best: SolveRef.Best) ->
  (Node.OQ.AClass(p, inf, G, Groups.groups_build(g, S, Nil{}))
   & {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, gs, best)),
        Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
          Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)))
       == True{} : Bool}):
  match gs:
    case Nil{}:
      Empty.absurd(
        (Node.OQ.AClass(p, inf, G, Groups.groups_build(g, S, Nil{}))
         & {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf,
               Nil{}, best)),
               Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                 Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)))
             == True{} : Bool}),
        Logic.Proof.false_ne_true(mem))
    case Con{h, t}:
      OQ.jobs_le_head(p, inf, G, S, h, t, g, mem, us,
        Feedback.word_eq(g, h), {==}, f, best,
        ft => mt => OQ.jobs_le(p, inf, G, S, t, g, mt, us, ft,
          Eval.Eval.guess(p, G, S, h, inf, best)))

# The usable node: the guess fold is below the node's cost.
def OQ.node_bound(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +kids: +List<Tree.Child>,
    jl: (Node.OQ.AClass(p, inf, G, Groups.groups_build(g, S, Nil{}))
         & {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
               Eval.Eval.dummy_inf(inf))),
               Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                 Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)))
             == True{} : Bool}),
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    kidsin: Tree.KidsIn(kids, G)) ->
  {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
      Eval.Eval.dummy_inf(inf))), Tree.cost(Tree.Node{g, kids}, S))
   == True{} : Bool}:
  (jobs, le_guess) = jl
  Cover.Cover.depths_agd(
    {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
        Eval.Eval.dummy_inf(inf))), Tree.cost(Tree.Node{g, kids}, S))
     == True{} : Bool},
    g, kids, S, Nil{}, depths, Unit{},
    ok => d2 =>
      Cover.Cover.depths_agd(
        {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
            Eval.Eval.dummy_inf(inf))), Tree.cost(Tree.Node{g, kids}, S))
         == True{} : Bool},
        g, kids, S, Nil{}, d2, Unit{},
        ok2 => d3 =>
          +neokb : {Ckids.Cover.all_ne(Groups.groups_build(g, S, Nil{}))
                    == True{} : Bool} =
            Ckids.Cover.groups_build_ne(g, S, Nil{}, {==})
          +kb : {Ckids.Cover.kids_in_b(kids, G) == True{} : Bool} =
            Ckids.Cover.kids_in_to_b(kids, G, kidsin)
          agd2 : Grp.Grp.AllGroupDepths(g, kids,
            Groups.groups_build(g, S, Nil{})) = ok2
          Ckids.Cover.groupkids_from(
            {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
                Eval.Eval.dummy_inf(inf))), Tree.cost(Tree.Node{g, kids}, S))
             == True{} : Bool},
            G, g, kids, Groups.groups_build(g, S, Nil{}), kb, neokb, agd2,
            kidsok =>
              +le_cand : {Nat.is_le(Fold.OQ.ks_cost(inf, S,
                    Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}),
                      Nil{}, 0n, inf)), Tree.cost(Tree.Node{g, kids}, S))
                          == True{} : Bool} =
                Node.OQ.node_le(p, inf, G, S, g,
                  Groups.groups_build(g, S, Nil{}), kids, {==}, d3, jobs, kidsok)
              NatProof.Nat.is_le_trans(
                Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
                  Eval.Eval.dummy_inf(inf))),
                Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                  Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
                Tree.cost(Tree.Node{g, kids}, S), le_guess, le_cand))))

# The child of the bad class, with its validity, its cost bound and the lookup.
def OQ.KidRes(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +g: +List<Nat>,
    +kids: +List<Tree.Child>) -> Type:
  Sigma<&2, &1, Tree.Tree, T =>
    Tree.Valid(T, G, S)
    & {Nat.is_le(Tree.cost(T, S), Tree.cost(Tree.Node{g, kids}, S)) == True{}
       : Bool}
    & Sigma<&2, &1, +List<Feedback.Color>,
        fb => {Tree.lookup(fb, kids) == Some{T} : Maybe<&1, Tree.Tree>}>>

# The kid of the bad class costs at most the node.
def OQ.unusable_take(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +kids: +List<Tree.Child>, +groups: +List<Groups.Group>,
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +ws_eq: {ws == S : +List<+List<Nat>>},
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    kid: Cora.Cover.GroupKid(G, kids, Groups.Group{fb, ws}),
    +eg: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    +total_le: {Nat.is_le(GC.GC.GroupCost(kids, Groups.Group{fb, ws}),
                   GC.GC.Total(kids, groups)) == True{} : Bool}) ->
  OQ.KidRes(G, S, g, kids):
  match kid:
    case Tuple{+T, kp}:
      (+e_look, valid_ws) = kp
      valid_S : Tree.Valid(T, G, S) =
        Cover.Cover.valid_transport(G, T, ws, S, ws_eq, valid_ws)
      +gc_eq : {GC.GC.GroupCost(kids, Groups.Group{fb, ws})
                == Tree.cost(T, ws) : Nat} =
        Cover.Cover.group_cost_some(kids, fb, ws, T, e_look)
      +cost_eq : {Tree.cost(T, ws) == Tree.cost(T, S) : Nat} =
        Equal.cong(+List<+List<Nat>>, Nat, z => Tree.cost(T, z), ws, S, ws_eq)
      +gc_cost : {GC.GC.GroupCost(kids, Groups.Group{fb, ws})
                  == Tree.cost(T, S) : Nat} =
        Equal.trans(Nat, GC.GC.GroupCost(kids, Groups.Group{fb, ws}),
          Tree.cost(T, ws), Tree.cost(T, S), gc_eq, cost_eq)
      +le_cost : {Nat.is_le(Tree.cost(T, S), GC.GC.Total(kids, groups))
                  == True{} : Bool} =
        Fold.OQ.le_cong_l(Tree.cost(T, S),
          GC.GC.GroupCost(kids, Groups.Group{fb, ws}),
          GC.GC.Total(kids, groups),
          Equal.sym(Nat, GC.GC.GroupCost(kids, Groups.Group{fb, ws}),
            Tree.cost(T, S), gc_cost), total_le)
      +cn : {Tree.cost(Tree.Node{g, kids}, S)
             == Nat.add(Groups.len_words(S),
                  NodeCost.NodeCost.kid_sum(g, kids, S)) : Nat} =
        NodeCost.NodeCost.cost_node(g, kids, S, depths)
      +gt : {GC.GC.Total(kids, groups)
             == NodeCost.NodeCost.kid_sum(g, kids, S) : Nat} =
        Equal.trans(Nat, GC.GC.Total(kids, groups),
          GC.GC.Total(kids, Groups.groups_build(g, S, Nil{})),
          NodeCost.NodeCost.kid_sum(g, kids, S),
          Equal.cong(+List<Groups.Group>, Nat, z => GC.GC.Total(kids, z),
            groups, Groups.groups_build(g, S, Nil{}), eg),
          GC.GC.groups_build_total(g, kids, S))
      +le_tot : {Nat.is_le(GC.GC.Total(kids, groups),
                    Nat.add(Groups.len_words(S),
                      NodeCost.NodeCost.kid_sum(g, kids, S))) == True{} : Bool} =
        Fold.OQ.le_cong_l(GC.GC.Total(kids, groups),
          NodeCost.NodeCost.kid_sum(g, kids, S),
          Nat.add(Groups.len_words(S), NodeCost.NodeCost.kid_sum(g, kids, S)),
          gt, NatProof.Nat.is_le_add_self_l(Groups.len_words(S),
            NodeCost.NodeCost.kid_sum(g, kids, S)))
      +le_mid : {Nat.is_le(Tree.cost(T, S),
                    Nat.add(Groups.len_words(S),
                      NodeCost.NodeCost.kid_sum(g, kids, S))) == True{} : Bool} =
        NatProof.Nat.is_le_trans(Tree.cost(T, S), GC.GC.Total(kids, groups),
          Nat.add(Groups.len_words(S), NodeCost.NodeCost.kid_sum(g, kids, S)),
          le_cost, le_tot)
      +le_node : {Nat.is_le(Tree.cost(T, S), Tree.cost(Tree.Node{g, kids}, S))
                  == True{} : Bool} =
        Fold.OQ.le_cong_r(Tree.cost(T, S),
          Nat.add(Groups.len_words(S), NodeCost.NodeCost.kid_sum(g, kids, S)),
          Tree.cost(Tree.Node{g, kids}, S),
          Equal.sym(Nat, Tree.cost(Tree.Node{g, kids}, S),
            Nat.add(Groups.len_words(S), NodeCost.NodeCost.kid_sum(g, kids, S)),
            cn), le_mid)
      (T, (valid_S, (le_node, (fb, e_look))))

# The bad class of an unusable root and its kid.
def OQ.unusable_bad(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +kids: +List<Tree.Child>, +groups: +List<Groups.Group>,
    +eg: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    kidsok: Cora.Cover.GroupKids(G, kids, groups),
    bad: Sigma<&2, &1, Groups.Group,
            gp => Cgrp.Cover.BadFacts(g, kids, groups, S, gp)>) ->
  OQ.KidRes(G, S, g, kids):
  match bad:
    case Tuple{+gp, bf}:
      match gp:
        case Groups.Group{fb, ws}:
          (wd, r2) = bf
          (sub, r3) = r2
          (notlt, mem) = r3
          +ws_eq : {ws == S : +List<+List<Nat>>} =
            Clist.Cover.subseq_eq_of_not_lt(ws, S, sub, notlt)
          Cover.Cover.kid_and_bound(OQ.KidRes(G, S, g, kids), G, kids, groups,
            Groups.Group{fb, ws}, kidsok, mem,
            kid => total_le =>
              OQ.unusable_take(G, S, g, kids, groups, fb, ws, ws_eq,
                depths, kid, eg, total_le))

# The unusable root: a class holds all of `S`, so its valid child costs at most
# the node, and the same fuel applies to that child.
def OQ.unusable_kid(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +kids: +List<Tree.Child>, +groups: +List<Groups.Group>,
    +eg: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    kidsin: Tree.KidsIn(kids, G),
    +ef: {Groups.groups_smaller(S, groups) == False{} : Bool}) ->
  OQ.KidRes(G, S, g, kids):
  Cover.Cover.depths_agd(OQ.KidRes(G, S, g, kids), g, kids, S, Nil{}, depths,
    Unit{},
    ok => d2 =>
      Cover.Cover.depths_agd(OQ.KidRes(G, S, g, kids), g, kids, S, Nil{}, d2,
        Unit{},
        ok2 => d3 =>
          +neokb : {Ckids.Cover.all_ne(Groups.groups_build(g, S, Nil{}))
                    == True{} : Bool} =
            Ckids.Cover.groups_build_ne(g, S, Nil{}, {==})
          +neok : {Ckids.Cover.all_ne(groups) == True{} : Bool} =
            Equal.trans(Bool, Ckids.Cover.all_ne(groups),
              Ckids.Cover.all_ne(Groups.groups_build(g, S, Nil{})), True{},
              Equal.cong(+List<Groups.Group>, Bool, z => Ckids.Cover.all_ne(z),
                groups, Groups.groups_build(g, S, Nil{}), eg), neokb)
          +kb : {Ckids.Cover.kids_in_b(kids, G) == True{} : Bool} =
            Ckids.Cover.kids_in_to_b(kids, G, kidsin)
          agd1 : Grp.Grp.AllGroupDepths(g, kids, groups) =
            Cora.Cover.allgd_eq(g, kids, Groups.groups_build(g, S, Nil{}),
              groups, Equal.sym(+List<Groups.Group>, groups,
                Groups.groups_build(g, S, Nil{}), eg), ok)
          agd2 : Grp.Grp.AllGroupDepths(g, kids, groups) =
            Cora.Cover.allgd_eq(g, kids, Groups.groups_build(g, S, Nil{}),
              groups, Equal.sym(+List<Groups.Group>, groups,
                Groups.groups_build(g, S, Nil{}), eg), ok2)
          allsubb : Cgrp.Cover.AllSubseq(Groups.groups_build(g, S, Nil{}), S) =
            Cgrp.Cover.all_subseq_nil(g, S)
          allsub : Cgrp.Cover.AllSubseq(groups, S) =
            Cgrp.Cover.groups_subseq_eq(S,
              Groups.groups_build(g, S, Nil{}), groups,
              Equal.sym(+List<Groups.Group>, groups,
                Groups.groups_build(g, S, Nil{}), eg), allsubb)
          data : Cgrp.Cover.ClassData(g, kids, S, groups) =
            Cgrp.Cover.class_data(g, kids, S, groups, agd1, allsub)
          fd = Cgrp.Cover.find_bad(g, kids, S, groups, data, ef)
          Ckids.Cover.groupkids_from(OQ.KidRes(G, S, g, kids), G, g, kids,
            groups, kb, neok, agd2,
            kidsok =>
              OQ.unusable_bad(G, S, g, kids, groups, eg, d3, kidsok, fd))))

# The bound for one tree, uniformly over the candidate list and the class facts.
def OQ.ABound(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>, T: Tree.Tree) -> Type:
  @S: +List<+List<Nat>> -> OQ.AByGs(p, inf, G, S, G) -> Tree.Valid(T, G, S)
  -> {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S),
        G, S, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
        Eval.Eval.dummy_zero())), Tree.cost(T, S)) == True{} : Bool}

def OQ.AllBound(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +kids: +List<Tree.Child>) -> Type:
  match kids:
    case Nil{}:
      Unit
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          OQ.ABound(p, inf, G, child) & OQ.AllBound(p, inf, G, rest)

def OQ.abound_eq(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +t1: Tree.Tree, +t2: Tree.Tree, e: {t1 == t2 : Tree.Tree},
    b: OQ.ABound(p, inf, G, t1)) -> OQ.ABound(p, inf, G, t2):
  %e : OQ.ABound(p, inf, G, _)
  b

# One child bound, split on its feedback.
def OQ.pick_head(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +fb: +List<Feedback.Color>, +f: +List<Feedback.Color>, +child: Tree.Tree,
    +rest: +List<Tree.Child>, head: OQ.ABound(p, inf, G, child), +T: Tree.Tree,
    e: {Tree.lookup(fb, Tree.Child{f, child} <> rest) == Some{T}
        : Maybe<&1, Tree.Tree>},
    b: Bool, +eb: {b == Feedback.feedback_eq(fb, f) : Bool},
    k: {Tree.lookup(fb, rest) == Some{T} : Maybe<&1, Tree.Tree>}
       -> OQ.ABound(p, inf, G, T)) -> OQ.ABound(p, inf, G, T):
  match b:
    case True{}:
      +e1 : {Some{child} == Cover.Cover.lookup_of(fb, f, child, rest,
                  Feedback.feedback_eq(fb, f)) : Maybe<&1, Tree.Tree>} =
        Cover.Cover.lk_true(fb, f, child, rest, eb)
      +e2 : {Some{child} == Some{T} : Maybe<&1, Tree.Tree>} =
        Cover.Cover.mtrans(Some{child},
          Cover.Cover.lookup_of(fb, f, child, rest,
            Feedback.feedback_eq(fb, f)), Some{T}, e1, e)
      +ec : {child == T : Tree.Tree} =
        KidPr.KidsProof.some_inj(child, T, e2)
      OQ.abound_eq(p, inf, G, child, T, ec, head)
    case False{}:
      +e1 : {Tree.lookup(fb, rest) == Cover.Cover.lookup_of(fb, f, child, rest,
                  Feedback.feedback_eq(fb, f)) : Maybe<&1, Tree.Tree>} =
        Cover.Cover.lk_false(fb, f, child, rest, eb)
      +e2 : {Tree.lookup(fb, rest) == Some{T} : Maybe<&1, Tree.Tree>} =
        Cover.Cover.mtrans(Tree.lookup(fb, rest),
          Cover.Cover.lookup_of(fb, f, child, rest,
            Feedback.feedback_eq(fb, f)), Some{T}, e1, e)
      k(e2)

# Select the child bound that the lookup equation points to.
def OQ.pick(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +fb: +List<Feedback.Color>, +kids: +List<Tree.Child>,
    all: OQ.AllBound(p, inf, G, kids), +T: Tree.Tree,
    e: {Tree.lookup(fb, kids) == Some{T} : Maybe<&1, Tree.Tree>}) ->
  OQ.ABound(p, inf, G, T):
  match kids:
    case Nil{}:
      Empty.absurd(OQ.ABound(p, inf, G, T),
        KidPr.KidsProof.none_ne_some(T, e))
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          (head, tail) = all
          OQ.pick_head(p, inf, G, fb, f, child, rest, head, T, e,
            Feedback.feedback_eq(fb, f), {==},
            e2 => OQ.pick(p, inf, G, fb, rest, tail, T, e2))

# The unusable root: the child selected by the bad class costs at most the node.
def OQ.kid_finish(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +kids: +List<Tree.Child>,
    all: OQ.AllBound(p, inf, G, kids), flatS: OQ.AByGs(p, inf, G, S, G),
    res: OQ.KidRes(G, S, g, kids)) ->
  {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S),
      G, S, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
      Eval.Eval.dummy_zero())), Tree.cost(Tree.Node{g, kids}, S))
   == True{} : Bool}:
  match res:
    case Tuple{+T, r}:
      (v2, r2) = r
      (le2, look) = r2
      match look:
        case Tuple{+fb2, el2}:
          +rec : {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(1n+p,
                SolveRef.mk_schedule(G, S), G, S, inf, Nil{}, Nil{}, 0n,
                Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())),
                Tree.cost(T, S)) == True{} : Bool} =
            OQ.pick(p, inf, G, fb2, kids, all, T, el2)(S, flatS, v2)
          NatProof.Nat.is_le_trans(
            Eval.Eval.cost_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S),
              G, S, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
              Eval.Eval.dummy_zero())),
            Tree.cost(T, S), Tree.cost(Tree.Node{g, kids}, S), rec, le2)

# The node step of the tree induction, with the children's bounds as a
# hypothesis. The unusable root selects its child's bound by the lookup.
def OQ.a_node(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +kids: +List<Tree.Child>,
    flatS: OQ.AByGs(p, inf, G, S, G),
    v: Tree.Valid(Tree.Node{g, kids}, G, S), b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
          : Bool},
    all: OQ.AllBound(p, inf, G, kids)) ->
  {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S),
      G, S, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
      Eval.Eval.dummy_zero())), Tree.cost(Tree.Node{g, kids}, S))
   == True{} : Bool}:
  ((wg, kidsin), depths) = v
  match b:
    case True{}:
      +us : {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
             == True{} : Bool} =
        Equal.sym(Bool, b,
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), eb)
      jl = OQ.jobs_le(p, inf, G, S, G, g, wg, us, flatS,
        Eval.Eval.dummy_inf(inf))
      +bound : {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S,
            inf, G, Eval.Eval.dummy_inf(inf))),
            Tree.cost(Tree.Node{g, kids}, S)) == True{} : Bool} =
        OQ.node_bound(p, inf, G, S, g, kids, jl, depths, kidsin)
      +lhs : {Eval.Eval.cost_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S),
                G, S, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
                Eval.Eval.dummy_zero()))
              == Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
                   Eval.Eval.dummy_inf(inf))) : Nat} =
        Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
          SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S, inf,
            Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()),
          Eval.Eval.guesses(1n+p, G, S, inf, G, Eval.Eval.dummy_inf(inf)),
          Eval.Eval.guesses_step(p, G, S, inf, G, Eval.Eval.dummy_inf(inf)))
      Fold.OQ.le_cong_l(
        Eval.Eval.cost_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S),
          G, S, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
          Eval.Eval.dummy_zero())),
        Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
          Eval.Eval.dummy_inf(inf))),
        Tree.cost(Tree.Node{g, kids}, S), lhs, bound)
    case False{}:
      +ef : {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
             == False{} : Bool} =
        Equal.sym(Bool, b,
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), eb)
      res : OQ.KidRes(G, S, g, kids) =
        OQ.unusable_kid(G, S, g, kids, Groups.groups_build(g, S, Nil{}), {==},
          depths, kidsin, ef)
      OQ.kid_finish(p, inf, G, S, g, kids, all, flatS, res)

# Every child of a list satisfies the bound, by structural recursion.
def OQ.allbounds(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +kids: +List<Tree.Child>) -> OQ.AllBound(p, inf, G, kids):
  match kids:
    case Nil{}:
      Unit{}
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          match child:
            case Tree.Node{g, ckids}:
              ((+S => flatS => v =>
                  OQ.a_node(p, inf, G, S, g, ckids, flatS, v,
                    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
                    {==}, OQ.allbounds(p, inf, G, ckids))),
               OQ.allbounds(p, inf, G, rest))

# The bound for one tree.
def OQ.a_bound(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>, t: Tree.Tree) ->
  OQ.ABound(p, inf, G, t):
  match t:
    case Tree.Node{+g, +kids}:
      +S => flatS => v =>
        OQ.a_node(p, inf, G, S, g, kids, flatS, v,
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==},
          OQ.allbounds(p, inf, G, kids))

# A class conjunction read from the flat conjunction at the classes of a guess.
def OQ.aclassif_of_flat_go(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    f: Node.OQ.AFlat(fuel, inf, G,
         MV.MV.classes_b(b, Groups.groups_build(g, S, Nil{})))) ->
  OQ.AClassIf(b, fuel, inf, G, Groups.groups_build(g, S, Nil{})):
  match b:
    case True{}:
      OQ.aclass_of_flat(fuel, inf, G, Groups.groups_build(g, S, Nil{}), f)
    case False{}:
      Unit{}

# The per-guess class conjunction of a job, from the flat conjunction.
def OQ.abgs_of_flat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>,
    f: Node.OQ.AFlat(fuel, inf, G, MV.MV.next_guess(gs, S))) ->
  OQ.AByGs(fuel, inf, G, S, gs):
  match gs:
    case Nil{}:
      Unit{}
    case Con{g, t}:
      MV.MV.use_pair(
        (OQ.AClassIf(Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
           fuel, inf, G, Groups.groups_build(g, S, Nil{}))
         & OQ.AByGs(fuel, inf, G, S, t)),
        Node.OQ.AFlat(fuel, inf, G, MV.MV.classes(g, S)),
        Node.OQ.AFlat(fuel, inf, G, MV.MV.next_guess(t, S)),
        OQ.aflat_append(fuel, inf, G, MV.MV.classes(g, S),
          MV.MV.next_guess(t, S), f),
        fg => ft =>
          (OQ.aclassif_of_flat_go(fuel, inf, G, S, g,
             Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==},
             fg),
           OQ.abgs_of_flat(fuel, inf, G, S, t, ft)))

# Zero is below `1 + n`, the shape of the solver's infinity bound.
def OQ.zero_lt_succ_add(m: Nat) ->
  {Nat.is_lt(0n, Nat.add(m, 1n)) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

# The saturating sum of two zeroes is zero, below infinity.
def OQ.sat_zero(+inf: Nat, +hz: {Nat.is_lt(0n, inf) == True{} : Bool}) ->
  {SolveRef.sat_add(inf, 0n, 0n) == 0n : Nat}:
  +g0 : {Nat.is_ge(0n, inf) == False{} : Bool} = OV.OV.ge_false_of_lt(0n, inf, hz)
  +h1 : {Feedback.Bool.case(Nat, Nat.is_ge(0n, inf), inf,
             Feedback.Bool.case(Nat, Nat.is_ge(0n, inf), inf, Nat.add(0n, 0n)))
          == Feedback.Bool.case(Nat, False{}, inf,
               Feedback.Bool.case(Nat, Nat.is_ge(0n, inf), inf,
                 Nat.add(0n, 0n))) : Nat} =
    Equal.cong(Bool, Nat,
      x => Feedback.Bool.case(Nat, x, inf,
        Feedback.Bool.case(Nat, Nat.is_ge(0n, inf), inf, Nat.add(0n, 0n))),
      Nat.is_ge(0n, inf), False{}, g0)
  +h2 : {Feedback.Bool.case(Nat, False{}, inf,
             Feedback.Bool.case(Nat, Nat.is_ge(0n, inf), inf, Nat.add(0n, 0n)))
          == Feedback.Bool.case(Nat, False{}, inf,
               Feedback.Bool.case(Nat, False{}, inf, Nat.add(0n, 0n))) : Nat} =
    Equal.cong(Bool, Nat,
      x => Feedback.Bool.case(Nat, False{}, inf,
        Feedback.Bool.case(Nat, x, inf, Nat.add(0n, 0n))),
      Nat.is_ge(0n, inf), False{}, g0)
  Equal.trans(Nat,
    Feedback.Bool.case(Nat, Nat.is_ge(0n, inf), inf,
      Feedback.Bool.case(Nat, Nat.is_ge(0n, inf), inf, Nat.add(0n, 0n))),
    Feedback.Bool.case(Nat, False{}, inf,
      Feedback.Bool.case(Nat, Nat.is_ge(0n, inf), inf, Nat.add(0n, 0n))),
    0n, h1,
    Equal.trans(Nat,
      Feedback.Bool.case(Nat, False{}, inf,
        Feedback.Bool.case(Nat, Nat.is_ge(0n, inf), inf, Nat.add(0n, 0n))),
      Feedback.Bool.case(Nat, False{}, inf,
        Feedback.Bool.case(Nat, False{}, inf, Nat.add(0n, 0n))),
      0n, h2, {==}))

# A zero candidate below infinity wins the empty comparison.
def OQ.better0_eq(+inf: Nat, +node: Tree.Tree,
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool}) ->
  {SolveRef.better(0n, node, Eval.Eval.dummy_inf(inf))
   == SolveRef.Best{node, 0n} : SolveRef.Best}:
  Equal.cong(Bool, SolveRef.Best,
    x => Feedback.Bool.case(SolveRef.Best, x, SolveRef.Best{node, 0n},
      SolveRef.Best{Tree.Node{Nil{}, Nil{}}, inf}),
    Nat.is_lt(0n, inf), True{}, hz)

# A zero candidate keeps the stored tree at cost zero.
def OQ.better0_keep(+node: Tree.Tree, +tree: Tree.Tree) ->
  {SolveRef.better(0n, node, SolveRef.Best{tree, 0n})
   == SolveRef.Best{tree, 0n} : SolveRef.Best}:
  {==}

# The zero-fuel fold at a zero cost stays at cost zero.
def OQ.guesses0_le0(+G: +List<+List<Nat>>, +inf: Nat,
    +gs: +List<+List<Nat>>, +node: Tree.Tree,
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, gs,
      SolveRef.Best{node, 0n})), 0n) == True{} : Bool}:
  match gs:
    case Nil{}:
      NatProof.Nat.is_le_refl(0n)
    case Con{g, t}:
      +e1 : {SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(Nil{}),
                SolveRef.Best{node, 0n}) == SolveRef.Best{node, 0n}
             : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          SolveRef.finish_guess(inf, g, Nil{}, 0n, 0n,
            SolveRef.Best{node, 0n}),
          SolveRef.better(0n, Tree.Node{g, Nil{}}, SolveRef.Best{node, 0n}),
          SolveRef.Best{node, 0n},
          Equal.cong(Nat, SolveRef.Best,
            x => SolveRef.better(x, Tree.Node{g, SolveRef.rev_kids(Nil{}, Nil{})},
              SolveRef.Best{node, 0n}),
            SolveRef.sat_add(inf, 0n, 0n), 0n, OQ.sat_zero(inf, hz)),
          OQ.better0_keep(Tree.Node{g, Nil{}}, node))
      +eq : {Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, t,
                SolveRef.finish_guess(inf, g, Nil{}, 0n,
                  Groups.len_words(Nil{}), SolveRef.Best{node, 0n})))
              == Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, t,
                   SolveRef.Best{node, 0n})) : Nat} =
        Equal.cong(SolveRef.Best, Nat,
          b => Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, t, b)),
          SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(Nil{}),
            SolveRef.Best{node, 0n}),
          SolveRef.Best{node, 0n}, e1)
      Fold.OQ.le_cong_l(
        Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, g <> t,
          SolveRef.Best{node, 0n})),
        Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, t,
          SolveRef.Best{node, 0n})),
        0n, eq, OQ.guesses0_le0(G, inf, t, node, hz))

# The empty candidate list at zero fuel: a member guess makes the fold cost zero.
def OQ.nil_bound(+inf: Nat, +G: +List<+List<Nat>>, +g: +List<Nat>,
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +wg: {Tree.member_word(g, G) == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(0n,
      SolveRef.mk_schedule(G, Nil{}), G, Nil{}, inf, Nil{}, Nil{}, 0n,
      Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())), 0n) == True{} : Bool}:
  match G:
    case Nil{}:
      Empty.absurd(
        {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(0n,
            SolveRef.mk_schedule(Nil{}, Nil{}), Nil{}, Nil{}, inf, Nil{}, Nil{},
            0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())), 0n)
         == True{} : Bool},
        Logic.Proof.false_ne_true(wg))
    case Con{h, t}:
      +e1 : {Eval.Eval.guesses(0n, G, Nil{}, inf, h <> t,
                Eval.Eval.dummy_inf(inf))
              == Eval.Eval.guesses(0n, G, Nil{}, inf, t,
                   SolveRef.finish_guess(inf, h, Nil{}, 0n,
                     Groups.len_words(Nil{}), Eval.Eval.dummy_inf(inf)))
             : SolveRef.Best} = {==}
      +e2 : {SolveRef.finish_guess(inf, h, Nil{}, 0n, Groups.len_words(Nil{}),
                Eval.Eval.dummy_inf(inf))
              == SolveRef.Best{Tree.Node{h, Nil{}}, 0n} : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          SolveRef.finish_guess(inf, h, Nil{}, 0n, 0n,
            Eval.Eval.dummy_inf(inf)),
          SolveRef.better(0n, Tree.Node{h, Nil{}}, Eval.Eval.dummy_inf(inf)),
          SolveRef.Best{Tree.Node{h, Nil{}}, 0n},
          Equal.cong(Nat, SolveRef.Best,
            x => SolveRef.better(x, Tree.Node{h, SolveRef.rev_kids(Nil{}, Nil{})},
              Eval.Eval.dummy_inf(inf)),
            SolveRef.sat_add(inf, 0n, 0n), 0n, OQ.sat_zero(inf, hz)),
          OQ.better0_eq(inf, Tree.Node{h, Nil{}}, hz))
      +le : {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, t,
                SolveRef.Best{Tree.Node{h, Nil{}}, 0n})), 0n) == True{}
             : Bool} =
        OQ.guesses0_le0(G, inf, t, Tree.Node{h, Nil{}}, hz)
      +ee : {Eval.Eval.guesses(0n, G, Nil{}, inf, h <> t,
                 Eval.Eval.dummy_inf(inf))
               == Eval.Eval.guesses(0n, G, Nil{}, inf, t,
                    SolveRef.Best{Tree.Node{h, Nil{}}, 0n}) : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          Eval.Eval.guesses(0n, G, Nil{}, inf, h <> t, Eval.Eval.dummy_inf(inf)),
          Eval.Eval.guesses(0n, G, Nil{}, inf, t,
            SolveRef.finish_guess(inf, h, Nil{}, 0n, Groups.len_words(Nil{}),
              Eval.Eval.dummy_inf(inf))),
          Eval.Eval.guesses(0n, G, Nil{}, inf, t,
            SolveRef.Best{Tree.Node{h, Nil{}}, 0n}),
          e1,
          Equal.cong(SolveRef.Best, SolveRef.Best,
            b => Eval.Eval.guesses(0n, G, Nil{}, inf, t, b),
            SolveRef.finish_guess(inf, h, Nil{}, 0n, Groups.len_words(Nil{}),
              Eval.Eval.dummy_inf(inf)),
            SolveRef.Best{Tree.Node{h, Nil{}}, 0n}, e2))
      +eq : {Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, h <> t,
                Eval.Eval.dummy_inf(inf)))
              == Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, t,
                   SolveRef.Best{Tree.Node{h, Nil{}}, 0n})) : Nat} =
        Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
          Eval.Eval.guesses(0n, G, Nil{}, inf, h <> t, Eval.Eval.dummy_inf(inf)),
          Eval.Eval.guesses(0n, G, Nil{}, inf, t,
            SolveRef.Best{Tree.Node{h, Nil{}}, 0n}), ee)
      +gz : {Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(G, Nil{}),
                G, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
                Eval.Eval.dummy_zero()))
              == Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, G,
                   Eval.Eval.dummy_inf(inf))) : Nat} =
        Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
          SolveRef.step(0n, SolveRef.mk_schedule(G, Nil{}), G, Nil{}, inf,
            Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
            Eval.Eval.dummy_zero()),
          Eval.Eval.guesses(0n, G, Nil{}, inf, G, Eval.Eval.dummy_inf(inf)),
          Eval.Eval.guesses_zero(G, inf, G, Eval.Eval.dummy_inf(inf)))
      Fold.OQ.le_cong_l(
        Eval.Eval.cost_of(SolveRef.step(0n, SolveRef.mk_schedule(G, Nil{}),
          G, Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
          Eval.Eval.dummy_zero())),
        Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, G,
          Eval.Eval.dummy_inf(inf))),
        0n, gz, Fold.OQ.le_cong_l(
          Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, G,
            Eval.Eval.dummy_inf(inf))),
          Eval.Eval.cost_of(Eval.Eval.guesses(0n, G, Nil{}, inf, t,
            SolveRef.Best{Tree.Node{h, Nil{}}, 0n})),
          0n, eq, le))

# The base job: an empty candidate list at zero fuel.
def OQ.ajob_nil_at(+inf: Nat, +G: +List<+List<Nat>>, T: Tree.Tree,
    v: Tree.Valid(T, G, Nil{}),
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(SolveRef.step(0n,
      SolveRef.mk_schedule(G, Nil{}), G, Nil{}, inf, Nil{}, Nil{}, 0n,
      Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())), Tree.cost(T, Nil{}))
   == True{} : Bool}:
  match T:
    case Tree.Node{g, kids}:
      (ti, depths) = v
      (wg, kidsin) = ti
      OQ.nil_bound(inf, G, g, hz, wg)

def OQ.ajob_nil(+inf: Nat, +G: +List<+List<Nat>>,
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool}) ->
  Node.OQ.AJob(0n, inf, G, Nil{}):
  T => v => OQ.ajob_nil_at(inf, G, T, v, hz)
