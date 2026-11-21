# The cover lemma: a valid tree costs at least the oracle's minimum.
#
# The optimality proof compares the solver's tree with an arbitrary valid tree
# `T2`. For a node `Node g kids` the candidate list splits into the feedback
# classes of `g`. If `g` is usable, every class is strictly smaller than `S`,
# so the oracle bounds each class's child and the node's cost is at least the
# value of `g`, hence at least the minimum over the guesses. If `g` is not
# usable, one class has all of `S` and the node's child for that class is a
# valid tree for the same `S`, so the induction hypothesis applies to it. This
# module proves that step, taking the per-class valid children and the child
# bounds as hypotheses.
import Base
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./groups.bend as Grp
import ./kids.bend as Kids
import ./nodecost.bend as NodeCost
import ./groupcost.bend as GC
import ./cover_maybe.bend as CoverMaybe
import ./cover_list.bend as CoverList
import ./cover_oracle.bend as CoverOracle
import ./cover_groups.bend as CoverGroups
import ./cover_kids.bend as CoverKids

# The bound for one tree, with the value already computed from the oracle.
def Cover.Stmt(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>, T: Tree.Tree) -> Type:
  CoverOracle.Cover.Oracle(G, S, G, entries)
  -> Tree.Valid(T, G, S)
  -> CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
                          Some{Tree.cost(T, S)})

# The conjunction of the bounds over a child list.
def Cover.AllCover(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>,
    +kids: +List<Tree.Child>) -> Type:
  match kids:
    case Nil{}:
      Unit
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          Cover.Stmt(G, S, entries, child) & Cover.AllCover(G, S, entries, rest)

# Transport a statement along a tree equality.
def Cover.stmt_eq(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>, +T1: Tree.Tree, +T2: Tree.Tree,
    e: {T1 == T2 : Tree.Tree}, p: Cover.Stmt(G, S, entries, T1)) ->
  Cover.Stmt(G, S, entries, T2):
  %e : Cover.Stmt(G, S, entries, _)
  p

# Transport validity along an equality of candidate lists.
def Cover.valid_transport(+G: +List<+List<Nat>>, +T: Tree.Tree,
    +S1: +List<+List<Nat>>, +S2: +List<+List<Nat>>,
    e: {S1 == S2 : +List<+List<Nat>>}, v: Tree.Valid(T, G, S1)) ->
  Tree.Valid(T, G, S2):
  %e : Tree.Valid(T, G, _)
  v

# Transport an entry oracle along an equality of class lists.
def Cover.entryok_eq(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +os: +List<Maybe<&2, Nat>>, +g1: +List<Groups.Group>,
    +g2: +List<Groups.Group>, e: {g1 == g2 : +List<Groups.Group>},
    ok: CoverOracle.Cover.EntryOK(G, S, os, g1)) ->
  CoverOracle.Cover.EntryOK(G, S, os, g2):
  %e : CoverOracle.Cover.EntryOK(G, S, os, _)
  ok

# The explicit class list version of the guess value.
def Cover.guessvalue_of_eq(+S: +List<+List<Nat>>, +g: +List<Nat>,
    +os: +List<Maybe<&2, Nat>>, +g1: +List<Groups.Group>,
    +g2: +List<Groups.Group>, e: {g1 == g2 : +List<Groups.Group>}) ->
  {CoverOracle.Cover.GuessValueOf(S, g, os, g1)
   == CoverOracle.Cover.GuessValueOf(S, g, os, g2) : Maybe<&2, Nat>}:
  Equal.cong(+List<Groups.Group>, Maybe<&2, Nat>,
    z => CoverOracle.Cover.GuessValueOf(S, g, os, z), g1, g2, e)

# The lookup decision at the head child, with the test as a parameter.
def Cover.lookup_of(+fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    child: Tree.Tree, +rest: +List<Tree.Child>, b: Bool) -> Maybe<&1, Tree.Tree>:
  Feedback.Bool.case(Maybe<&1, Tree.Tree>, b, Some{child}, Tree.lookup(fb, rest))

# Small equality helpers for the tree `Maybe`, which the parser handles less
# happily as a bare first argument to `Equal.sym` and `Equal.trans`.
def Cover.msym(a: Maybe<&1, Tree.Tree>, b: Maybe<&1, Tree.Tree>,
    e: {a == b : Maybe<&1, Tree.Tree>}) -> {b == a : Maybe<&1, Tree.Tree>}:
  Equal.sym(Maybe<&1, Tree.Tree>, a, b, e)

def Cover.mtrans(a: Maybe<&1, Tree.Tree>, b: Maybe<&1, Tree.Tree>,
    c: Maybe<&1, Tree.Tree>,
    e1: {a == b : Maybe<&1, Tree.Tree>}, e2: {b == c : Maybe<&1, Tree.Tree>}) ->
  {a == c : Maybe<&1, Tree.Tree>}:
  Equal.trans(Maybe<&1, Tree.Tree>, a, b, c, e1, e2)

# The two branches of the head lookup, as equalities.
def Cover.lk_true(+fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    child: Tree.Tree, +rest: +List<Tree.Child>,
    +eb: {True{} == Feedback.feedback_eq(fb, f) : Bool}) ->
  {Some{child} == Cover.lookup_of(fb, f, child, rest,
                                   Feedback.feedback_eq(fb, f)) : Maybe<&1, Tree.Tree>}:
  Equal.cong(Bool, Maybe<&1, Tree.Tree>,
    x => Cover.lookup_of(fb, f, child, rest, x),
    True{}, Feedback.feedback_eq(fb, f), eb)

def Cover.lk_false(+fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    child: Tree.Tree, +rest: +List<Tree.Child>,
    +eb: {False{} == Feedback.feedback_eq(fb, f) : Bool}) ->
  {Tree.lookup(fb, rest) == Cover.lookup_of(fb, f, child, rest,
                                            Feedback.feedback_eq(fb, f))
   : Maybe<&1, Tree.Tree>}:
  Equal.cong(Bool, Maybe<&1, Tree.Tree>,
    x => Cover.lookup_of(fb, f, child, rest, x),
    False{}, Feedback.feedback_eq(fb, f), eb)

# One child of the list, split on its feedback.
def Cover.pick_head(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>, +fb: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, +child: Tree.Tree, +rest: +List<Tree.Child>,
    head: Cover.Stmt(G, S, entries, child),
    +T: Tree.Tree, e: {Tree.lookup(fb, Tree.Child{f, child} <> rest) == Some{T}
                       : Maybe<&1, Tree.Tree>},
    b: Bool, +eb: {b == Feedback.feedback_eq(fb, f) : Bool},
    k: {Tree.lookup(fb, rest) == Some{T} : Maybe<&1, Tree.Tree>}
       -> Cover.Stmt(G, S, entries, T)) ->
  Cover.Stmt(G, S, entries, T):
  match b:
    case True{}:
      e1 = Cover.lk_true(fb, f, child, rest, eb)
      e2 = Cover.mtrans(Some{child},
        Cover.lookup_of(fb, f, child, rest, Feedback.feedback_eq(fb, f)),
        Some{T}, e1, e)
      +ec : {child == T : Tree.Tree} = Kids.KidsProof.some_inj(child, T, e2)
      Cover.stmt_eq(G, S, entries, child, T, ec, head)
    case False{}:
      e1 = Cover.lk_false(fb, f, child, rest, eb)
      e2 = Cover.mtrans(Tree.lookup(fb, rest),
        Cover.lookup_of(fb, f, child, rest, Feedback.feedback_eq(fb, f)),
        Some{T}, e1, e)
      k(e2)

# Select the child bound that the lookup equation points to.
def Cover.pick(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>, +fb: +List<Feedback.Color>,
    +kids: +List<Tree.Child>, all: Cover.AllCover(G, S, entries, kids),
    +T: Tree.Tree,
    e: {Tree.lookup(fb, kids) == Some{T} : Maybe<&1, Tree.Tree>}) ->
  Cover.Stmt(G, S, entries, T):
  match kids:
    case Nil{}:
      Empty.absurd(Cover.Stmt(G, S, entries, T),
        Kids.KidsProof.none_ne_some(T, e))
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          (head, tail) = all
          Cover.pick_head(G, S, entries, fb, f, child, rest, head, T, e,
            Feedback.feedback_eq(fb, f), {==},
            e2 => Cover.pick(G, S, entries, fb, rest, tail, T, e2))

# Select the class child for a member class.
def Cover.kid_at(+G: +List<+List<Nat>>, +kids: +List<Tree.Child>,
    +groups: +List<Groups.Group>, gp: Groups.Group,
    m: CoverGroups.Cover.MemGroup(gp, groups),
    gk: CoverOracle.Cover.GroupKids(G, kids, groups)) ->
  CoverOracle.Cover.GroupKid(G, kids, gp):
  match groups:
    case Nil{}:
      Empty.absurd(CoverOracle.Cover.GroupKid(G, kids, gp), m)
    case Con{q, rest}:
      match m:
        case Inl{e}:
          (kh, kt) = gk
          %Equal.sym(Groups.Group, gp, q, e) :
            CoverOracle.Cover.GroupKid(G, kids, _)
          kh
        case Inr{m2}:
          (kh, kt) = gk
          Cover.kid_at(G, kids, rest, gp, m2, kt)

# Transport a class child along an equality of groups.
def Cover.groupkid_transport(+G: +List<+List<Nat>>, +kids: +List<Tree.Child>,
    +gp: Groups.Group, +q: Groups.Group, e: {gp == q : Groups.Group},
    k: CoverOracle.Cover.GroupKid(G, kids, q)) ->
  CoverOracle.Cover.GroupKid(G, kids, gp):
  %Equal.sym(Groups.Group, gp, q, e) : CoverOracle.Cover.GroupKid(G, kids, _)
  k

# A member class's child and its cost bound, from a single traversal.
def Cover.kid_and_bound(-R: Type, +G: +List<+List<Nat>>,
    +kids: +List<Tree.Child>, +groups: +List<Groups.Group>, +gp: Groups.Group,
    gk: CoverOracle.Cover.GroupKids(G, kids, groups),
    m: CoverGroups.Cover.MemGroup(gp, groups),
    k: CoverOracle.Cover.GroupKid(G, kids, gp)
       -> {Nat.is_le(GC.GC.GroupCost(kids, gp),
                     GC.GC.Total(kids, groups)) == True{} : Bool}
       -> R) -> R:
  match groups:
    case Nil{}:
      match m:
    case Con{q, rest}:
      (kh, kt) = gk
      match m:
        case Inl{+e}:
          kid : CoverOracle.Cover.GroupKid(G, kids, gp) =
            Cover.groupkid_transport(G, kids, gp, q, e, kh)
          +gc : Nat = GC.GC.GroupCost(kids, q)
          +tr : Nat = GC.GC.Total(kids, rest)
          +e_comm : {Nat.add(gc, tr) == Nat.add(tr, gc) : Nat} =
            NatProof.NatPrf.add_comm(gc, tr)
          +le : {Nat.is_le(gc, Nat.add(tr, gc)) == True{} : Bool} =
            NatProof.Nat.is_le_add_self_l(tr, gc)
          +le2 : {Nat.is_le(gc, Nat.add(gc, tr)) == True{} : Bool} =
            Equal.trans(Bool, Nat.is_le(gc, Nat.add(gc, tr)),
              Nat.is_le(gc, Nat.add(tr, gc)), True{},
              Equal.cong(Nat, Bool, x => Nat.is_le(gc, x),
                Nat.add(gc, tr), Nat.add(tr, gc), e_comm), le)
          +egc : {GC.GC.GroupCost(kids, gp) == GC.GC.GroupCost(kids, q) : Nat} =
            Equal.cong(Groups.Group, Nat, z => GC.GC.GroupCost(kids, z),
              gp, q, e)
          +le_gp : {Nat.is_le(GC.GC.GroupCost(kids, gp),
                       Nat.add(GC.GC.GroupCost(kids, q),
                         GC.GC.Total(kids, rest))) == True{} : Bool} =
            NatProof.Nat.is_le_eq_l(Nat.add(GC.GC.GroupCost(kids, q),
                GC.GC.Total(kids, rest)),
              GC.GC.GroupCost(kids, q), GC.GC.GroupCost(kids, gp),
              Equal.sym(Nat, GC.GC.GroupCost(kids, gp),
                GC.GC.GroupCost(kids, q), egc), le2)
          k(kid, le_gp)
        case Inr{m2}:
          Cover.kid_and_bound(R, G, kids, rest, gp, kt, m2,
            kid2 => le2 =>
              k(kid2, NatProof.Nat.is_le_trans(GC.GC.GroupCost(kids, gp),
                GC.GC.Total(kids, rest),
                Nat.add(GC.GC.GroupCost(kids, q), GC.GC.Total(kids, rest)),
                le2,
                NatProof.Nat.is_le_add_self_l(GC.GC.GroupCost(kids, q),
                  GC.GC.Total(kids, rest)))))

# One group's cost equals the looked-up child's cost.
def Cover.group_cost_some(+kids: +List<Tree.Child>, +fb: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, T: Tree.Tree,
    e: {Tree.lookup(fb, kids) == Some{T} : Maybe<&1, Tree.Tree>}) ->
  {GC.GC.GroupCost(kids, Groups.Group{fb, ws}) == Tree.cost(T, ws) : Nat}:
  Equal.cong(Maybe<&1, Tree.Tree>, Nat,
    m => GC.GC.group_cost_of(kids, ws, m),
    Tree.lookup(fb, kids), Some{T}, e)

# `Some` congruence for costs.
def Cover.some_eq(+a: Nat, +b: Nat, e: {a == b : Nat}) ->
  {Some{a} == Some{b} : Maybe<&2, Nat>}:
  Equal.cong(Nat, Maybe<&2, Nat>, x => Some{x}, a, b, e)

# The final cost comparison of the unusable branch.
def Cover.cover_unusable_cost(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>,
    +g: +List<Nat>, +kids: +List<Tree.Child>, +groups: +List<Groups.Group>,
    +eg3: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +ws_eq: {ws == S : +List<+List<Nat>>}, +T: Tree.Tree,
    e_look: {Tree.lookup(fb, kids) == Some{T} : Maybe<&1, Tree.Tree>},
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    +total_le : {Nat.is_le(GC.GC.GroupCost(kids, Groups.Group{fb, ws}),
                   GC.GC.Total(kids, groups)) == True{} : Bool},
    ih: CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
          Some{Tree.cost(T, S)})) ->
  CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
    Some{Tree.cost(Tree.Node{g, kids}, S)}):
  +gc_eq : {GC.GC.GroupCost(kids, Groups.Group{fb, ws}) == Tree.cost(T, ws) : Nat} =
    Cover.group_cost_some(kids, fb, ws, T, e_look)
  +cost_eq : {Tree.cost(T, ws) == Tree.cost(T, S) : Nat} =
    Equal.cong(+List<+List<Nat>>, Nat, z => Tree.cost(T, z), ws, S, ws_eq)
  +gc_cost : {GC.GC.GroupCost(kids, Groups.Group{fb, ws})
              == Tree.cost(T, S) : Nat} =
    Equal.trans(Nat, GC.GC.GroupCost(kids, Groups.Group{fb, ws}),
      Tree.cost(T, ws), Tree.cost(T, S), gc_eq, cost_eq)
  +le_cost : {Nat.is_le(Tree.cost(T, S), GC.GC.Total(kids, groups)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_l(GC.GC.Total(kids, groups),
      GC.GC.GroupCost(kids, Groups.Group{fb, ws}), Tree.cost(T, S),
      gc_cost, total_le)
  +cn : {Tree.cost(Tree.Node{g, kids}, S)
         == Nat.add(Groups.len_words(S),
              NodeCost.NodeCost.kid_sum(g, kids, S)) : Nat} =
    NodeCost.NodeCost.cost_node(g, kids, S, depths)
  gt : {GC.GC.Total(kids, groups) == NodeCost.NodeCost.kid_sum(g, kids, S) : Nat} =
    Equal.trans(Nat, GC.GC.Total(kids, groups),
      GC.GC.Total(kids, Groups.groups_build(g, S, Nil{})),
      NodeCost.NodeCost.kid_sum(g, kids, S),
      Equal.cong(+List<Groups.Group>, Nat, z => GC.GC.Total(kids, z),
        groups, Groups.groups_build(g, S, Nil{}), eg3),
      GC.GC.groups_build_total(g, kids, S))
  +e_add : {Nat.add(Groups.len_words(S), GC.GC.Total(kids, groups))
            == Tree.cost(Tree.Node{g, kids}, S) : Nat} =
    Equal.trans(Nat, Nat.add(Groups.len_words(S), GC.GC.Total(kids, groups)),
      Nat.add(Groups.len_words(S), NodeCost.NodeCost.kid_sum(g, kids, S)),
      Tree.cost(Tree.Node{g, kids}, S),
      Equal.cong(Nat, Nat, x => Nat.add(Groups.len_words(S), x),
        GC.GC.Total(kids, groups), NodeCost.NodeCost.kid_sum(g, kids, S), gt),
      Equal.sym(Nat, Tree.cost(Tree.Node{g, kids}, S),
        Nat.add(Groups.len_words(S), NodeCost.NodeCost.kid_sum(g, kids, S)), cn))
  +le_self : {Nat.is_le(GC.GC.Total(kids, groups),
                Nat.add(Groups.len_words(S), GC.GC.Total(kids, groups))) == True{} : Bool} =
    NatProof.Nat.is_le_add_self_l(Groups.len_words(S), GC.GC.Total(kids, groups))
  +le_node : {Nat.is_le(Tree.cost(T, S),
                Tree.cost(Tree.Node{g, kids}, S)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(Tree.cost(T, S),
      Nat.add(Groups.len_words(S), GC.GC.Total(kids, groups)),
      Tree.cost(Tree.Node{g, kids}, S),
      e_add,
      NatProof.Nat.is_le_trans(Tree.cost(T, S), GC.GC.Total(kids, groups),
        Nat.add(Groups.len_words(S), GC.GC.Total(kids, groups)),
        le_cost, le_self))
  CoverMaybe.Cover.MLe_trans(CoverOracle.Cover.BestValue(G, S, entries),
    Some{Tree.cost(T, S)}, Some{Tree.cost(Tree.Node{g, kids}, S)}, ih, le_node)

def Cover.cover_unusable_kid(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>, +g: +List<Nat>,
    +kids: +List<Tree.Child>, +groups: +List<Groups.Group>,
    +eg3: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    oracle: CoverOracle.Cover.Oracle(G, S, G, entries),
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +ws_eq: {ws == S : +List<+List<Nat>>},
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    all: Cover.AllCover(G, S, entries, kids),
    kid: CoverOracle.Cover.GroupKid(G, kids, Groups.Group{fb, ws}),
    +total_le: {Nat.is_le(GC.GC.GroupCost(kids, Groups.Group{fb, ws}),
                   GC.GC.Total(kids, groups)) == True{} : Bool}) ->
  CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
    Some{Tree.cost(Tree.Node{g, kids}, S)}):
  match kid:
    case Tuple{+T, kp}:
      (+e_look, valid_ws) = kp
      valid_S : Tree.Valid(T, G, S) =
        Cover.valid_transport(G, T, ws, S, ws_eq, valid_ws)
      stmt = Cover.pick(G, S, entries, fb, kids, all, T, e_look)
      ih : CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
             Some{Tree.cost(T, S)}) = stmt(oracle)(valid_S)
      Cover.cover_unusable_cost(G, S, entries, g, kids, groups, eg3, fb, ws,
        ws_eq, T, e_look, depths, total_le, ih)

def Cover.cover_unusable_bad(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>, +g: +List<Nat>,
    +kids: +List<Tree.Child>, +groups: +List<Groups.Group>,
    +eg3: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    oracle: CoverOracle.Cover.Oracle(G, S, G, entries),
    kidsok: CoverOracle.Cover.GroupKids(G, kids, groups),
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    all: Cover.AllCover(G, S, entries, kids),
    bad: Sigma<&2, &1, Groups.Group,
            gp => CoverGroups.Cover.BadFacts(g, kids, groups, S, gp)>) ->
  CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
    Some{Tree.cost(Tree.Node{g, kids}, S)}):
  match bad:
    case Tuple{+gp, bf}:
      match gp:
        case Groups.Group{fb, ws}:
          (wd, r2) = bf
          (sub, r3) = r2
          (notlt, mem) = r3
          +ws_eq : {ws == S : +List<+List<Nat>>} =
            CoverList.Cover.subseq_eq_of_not_lt(ws, S, sub, notlt)
          Cover.kid_and_bound(
            CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
              Some{Tree.cost(Tree.Node{g, kids}, S)}),
            G, kids, groups, Groups.Group{fb, ws}, kidsok, mem,
            kid => total_le =>
              Cover.cover_unusable_kid(G, S, entries, g, kids, groups, eg3,
                oracle, fb, ws, ws_eq, depths, all, kid, total_le))

# Transport per-group depth facts along an equality of group lists.
def Cover.allgd_transport(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +g1: +List<Groups.Group>, +g2: +List<Groups.Group>,
    e: {g1 == g2 : +List<Groups.Group>},
    ok: Grp.Grp.AllGroupDepths(g, kids, g1)) ->
  Grp.Grp.AllGroupDepths(g, kids, g2):
  %e : Grp.Grp.AllGroupDepths(g, kids, _)
  ok

# Branch of `depths_agd`, split on the word test. The continuation receives the
# group list built so far, an equality aligning its depth facts with the whole
# list, and the depth evidence for the tail.
def Cover.depths_agd_go(-R: Type, +g: +List<Nat>, +kids: +List<Tree.Child>,
    +w: +List<Nat>, +t: +List<+List<Nat>>, +acc: +List<Groups.Group>, b: Bool,
    +eb: {b == Feedback.word_eq(g, w) : Bool},
    +dw: {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool},
    dt: Tree.AllHaveDepth(Tree.Node{g, kids}, t),
    acc_ok: Grp.Grp.AllGroupDepths(g, kids, acc),
    k: @a: +List<Groups.Group>
       -> @e: {Groups.groups_build(g, t, a)
               == Groups.groups_build(g, w <> t, acc) : +List<Groups.Group>}
       -> Grp.Grp.AllGroupDepths(g, kids, a)
       -> Tree.AllHaveDepth(Tree.Node{g, kids}, t) -> R) -> R:
  match b:
    case True{}:
      +etrue : {Feedback.word_eq(g, w) == True{} : Bool} =
        Equal.trans(Bool, Feedback.word_eq(g, w), b, True{},
          Equal.sym(Bool, b, Feedback.word_eq(g, w), eb), {==})
      +ecase : {Feedback.Bool.case(+List<Groups.Group>, Feedback.word_eq(g, w),
                   Groups.groups_build(g, t, acc),
                   Groups.groups_build(g, t,
                     Groups.group_add(w, Feedback.feedback(g, w), acc)))
                == Groups.groups_build(g, t, acc) : +List<Groups.Group>} =
        CoverOracle.Cover.bool_case_true(+List<Groups.Group>, Feedback.word_eq(g, w),
          Groups.groups_build(g, t, acc),
          Groups.groups_build(g, t, Groups.group_add(w, Feedback.feedback(g, w), acc)),
          etrue)
      k(acc, Equal.sym(+List<Groups.Group>,
        Feedback.Bool.case(+List<Groups.Group>, Feedback.word_eq(g, w),
          Groups.groups_build(g, t, acc),
          Groups.groups_build(g, t,
            Groups.group_add(w, Feedback.feedback(g, w), acc))),
        Groups.groups_build(g, t, acc), ecase), acc_ok, dt)
    case False{}:
      +ne : {Feedback.word_eq(g, w) == False{} : Bool} =
        Equal.sym(Bool, b, Feedback.word_eq(g, w), eb)
      +efalse : {Feedback.word_eq(g, w) == False{} : Bool} = ne
      +ecase : {Feedback.Bool.case(+List<Groups.Group>, Feedback.word_eq(g, w),
                   Groups.groups_build(g, t, acc),
                   Groups.groups_build(g, t,
                     Groups.group_add(w, Feedback.feedback(g, w), acc)))
                == Groups.groups_build(g, t,
                     Groups.group_add(w, Feedback.feedback(g, w), acc))
                : +List<Groups.Group>} =
        CoverOracle.Cover.bool_case_false(+List<Groups.Group>, Feedback.word_eq(g, w),
          Groups.groups_build(g, t, acc),
          Groups.groups_build(g, t, Groups.group_add(w, Feedback.feedback(g, w), acc)),
          efalse)
      local : Grp.Grp.WordDepths(g, kids, Feedback.feedback(g, w), w) =
        (ne, (FbProof.FbPrf.feedback_eq_refl(Feedback.feedback(g, w)), dw))
      k(Groups.group_add(w, Feedback.feedback(g, w), acc),
        Equal.sym(+List<Groups.Group>,
          Feedback.Bool.case(+List<Groups.Group>, Feedback.word_eq(g, w),
            Groups.groups_build(g, t, acc),
            Groups.groups_build(g, t,
              Groups.group_add(w, Feedback.feedback(g, w), acc))),
          Groups.groups_build(g, t, Groups.group_add(w, Feedback.feedback(g, w), acc)),
          ecase),
        Grp.Grp.group_add_depths(g, kids, w, Feedback.feedback(g, w), acc,
          local, acc_ok),
        dt)

# Per-class word/depth facts, returning the depth evidence unchanged so the
# caller can still decompose the node's cost.
def Cover.depths_agd(-R: Type, +g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>, +acc: +List<Groups.Group>,
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    acc_ok: Grp.Grp.AllGroupDepths(g, kids, acc),
    k: Grp.Grp.AllGroupDepths(g, kids, Groups.groups_build(g, S, acc))
       -> Tree.AllHaveDepth(Tree.Node{g, kids}, S) -> R) -> R:
  match S:
    case Nil{}:
      k(acc_ok, Unit{})
    case Con{w, t}:
      (+dw, dt) = depths
      Cover.depths_agd_go(R, g, kids, w, t, acc, Feedback.word_eq(g, w),
        {==}, dw, dt, acc_ok,
        +a => e => ok => d =>
          Cover.depths_agd(R, g, kids, t, a, d, ok,
            ok2 => d2 => k(Cover.allgd_transport(g, kids,
              Groups.groups_build(g, t, a), Groups.groups_build(g, w <> t, acc),
              e, ok2), (dw, d2))))

# The unusable root, once the per-class depth facts are available.
def Cover.cover_unusable_agd(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>, +g: +List<Nat>,
    +kids: +List<Tree.Child>, +groups: +List<Groups.Group>,
    +eg1: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    +eg2: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    +eg3: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    oracle: CoverOracle.Cover.Oracle(G, S, G, entries),
    kidsok: CoverOracle.Cover.GroupKids(G, kids, groups),
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    agd: Grp.Grp.AllGroupDepths(g, kids, groups),
    all: Cover.AllCover(G, S, entries, kids),
    +ef: {Groups.groups_smaller(S, groups) == False{} : Bool}) ->
  CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
    Some{Tree.cost(Tree.Node{g, kids}, S)}):
  allsubb : CoverGroups.Cover.AllSubseq(Groups.groups_build(g, S, Nil{}), S) =
    CoverGroups.Cover.all_subseq_nil(g, S)
  allsub : CoverGroups.Cover.AllSubseq(groups, S) =
    CoverGroups.Cover.groups_subseq_eq(S,
      Groups.groups_build(g, S, Nil{}), groups,
      Equal.sym(+List<Groups.Group>, groups, Groups.groups_build(g, S, Nil{}), eg2),
      allsubb)
  data : CoverGroups.Cover.ClassData(g, kids, S, groups) =
    CoverGroups.Cover.class_data(g, kids, S, groups, agd, allsub)
  bad = CoverGroups.Cover.find_bad(g, kids, S, groups, data, ef)
  Cover.cover_unusable_bad(G, S, entries, g, kids, groups, eg3, oracle, kidsok,
    depths, all, bad)

# The unusable root: a class holds all of `S`, so the node costs at least that
# class's valid child.
def Cover.cover_unusable(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>, +g: +List<Nat>,
    +kids: +List<Tree.Child>, +groups: +List<Groups.Group>,
    +eg1: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    +eg2: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    +eg3: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    oracle: CoverOracle.Cover.Oracle(G, S, G, entries),
    kidsok: CoverOracle.Cover.GroupKids(G, kids, groups),
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    all: Cover.AllCover(G, S, entries, kids),
    +ef: {Groups.groups_smaller(S, groups) == False{} : Bool}) ->
  CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
    Some{Tree.cost(Tree.Node{g, kids}, S)}):
  Cover.depths_agd(
    CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
      Some{Tree.cost(Tree.Node{g, kids}, S)}),
    g, kids, S, Nil{}, depths, Unit{},
    ok => d2 =>
      Cover.cover_unusable_agd(G, S, entries, g, kids, groups, eg1, eg2, eg3,
        oracle, kidsok, d2,
        CoverOracle.Cover.allgd_eq(g, kids, Groups.groups_build(g, S, Nil{}),
          groups, Equal.sym(+List<Groups.Group>, groups,
            Groups.groups_build(g, S, Nil{}), eg1), ok),
        all, ef))

def Cover.mle_eq_r(+a: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>,
    e: {b == c : Maybe<&2, Nat>},
    p: CoverMaybe.Cover.MLe(a, b)) -> CoverMaybe.Cover.MLe(a, c):
  %e : CoverMaybe.Cover.MLe(a, _)
  p

def Cover.cover_usable_found(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>, +g: +List<Nat>,
    +kids: +List<Tree.Child>, +groups: +List<Groups.Group>,
    +eg1: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    +eg2: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    +eg3: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    kidsok: CoverOracle.Cover.GroupKids(G, kids, groups),
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    +us: {Groups.groups_smaller(S, groups) == True{} : Bool},
    small: CoverOracle.Cover.GroupSmall(S, groups),
    found: CoverOracle.Cover.Find(G, S, g, G, entries)) ->
  CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
    Some{Tree.cost(Tree.Node{g, kids}, S)}):
  match found:
    case Tuple{+es, r}:
      (of, ok) = r
      okg : CoverOracle.Cover.EntryOK(G, S, es, groups) =
        Cover.entryok_eq(G, S, es, Groups.groups_build(g, S, Nil{}), groups,
          Equal.sym(+List<Groups.Group>, groups, Groups.groups_build(g, S, Nil{}),
            eg1), ok)
      bbe = CoverOracle.Cover.best_value_le_entry(S, g, G, entries, es, of)
      +gveq : {CoverOracle.Cover.GuessValue(S, g, es)
               == CoverOracle.Cover.GuessValueOf(S, g, es, groups) : Maybe<&2, Nat>} =
        Cover.guessvalue_of_eq(S, g, es,
          Groups.groups_build(g, S, Nil{}), groups,
          Equal.sym(+List<Groups.Group>, groups, Groups.groups_build(g, S, Nil{}),
            eg3))
      gvle = CoverOracle.Cover.guess_value_le(G, S, g, es, kids, groups, eg2,
        depths, us, okg, small, kidsok)
      CoverMaybe.Cover.MLe_trans(CoverOracle.Cover.BestValue(G, S, entries),
        CoverOracle.Cover.GuessValueOf(S, g, es, groups),
        Some{Tree.cost(Tree.Node{g, kids}, S)},
        Cover.mle_eq_r(CoverOracle.Cover.BestValue(G, S, entries),
          CoverOracle.Cover.GuessValue(S, g, es),
          CoverOracle.Cover.GuessValueOf(S, g, es, groups), gveq, bbe),
        gvle)

# The usable root: the node costs at least the guess's value.
def Cover.cover_usable(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>, +g: +List<Nat>,
    +kids: +List<Tree.Child>, +groups: +List<Groups.Group>,
    +eg1: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    +eg2: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    +eg3: {groups == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    oracle: CoverOracle.Cover.Oracle(G, S, G, entries),
    kidsok: CoverOracle.Cover.GroupKids(G, kids, groups),
    wg: Tree.WordIn(g, G),
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    +us: {Groups.groups_smaller(S, groups) == True{} : Bool}) ->
  CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
    Some{Tree.cost(Tree.Node{g, kids}, S)}):
  small : CoverOracle.Cover.GroupSmall(S, groups) =
    CoverOracle.Cover.groups_smaller_sound(S, groups, us)
  found = CoverOracle.Cover.find(G, S, G, entries, oracle, g, wg)
  Cover.cover_usable_found(G, S, entries, g, kids, groups, eg1, eg2, eg3,
    kidsok, depths, us, small, found)

# The node step of the structural induction.

def Cover.cover_node_dispatch(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>, +g: +List<Nat>,
    +kids: +List<Tree.Child>,
    oracle: CoverOracle.Cover.Oracle(G, S, G, entries),
    all: Cover.AllCover(G, S, entries, kids),
    wg: Tree.WordIn(g, G),
    kidsok: CoverOracle.Cover.GroupKids(G, kids, Groups.groups_build(g, S, Nil{})),
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool}) ->
  CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
    Some{Tree.cost(Tree.Node{g, kids}, S)}):
  match b:
    case True{}:
      +us : {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{} : Bool} =
        Equal.sym(Bool, True{},
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), eb)
      Cover.cover_usable(G, S, entries, g, kids,
        Groups.groups_build(g, S, Nil{}), {==}, {==}, {==},
        oracle, kidsok, wg, depths, us)
    case False{}:
      +ef : {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == False{} : Bool} =
        Equal.sym(Bool, False{},
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), eb)
      Cover.cover_unusable(G, S, entries, g, kids,
        Groups.groups_build(g, S, Nil{}), {==}, {==}, {==}, oracle, kidsok,
        depths, all, ef)

def Cover.cover_node_go(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>, +g: +List<Nat>,
    +kids: +List<Tree.Child>,
    oracle: CoverOracle.Cover.Oracle(G, S, G, entries),
    all: Cover.AllCover(G, S, entries, kids),
    v: Tree.Valid(Tree.Node{g, kids}, G, S),
    b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool}) ->
  CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
    Some{Tree.cost(Tree.Node{g, kids}, S)}):
  match v:
    case Tuple{ti, depths}:
      match ti:
        case Tuple{wg, kidsin}:
          Cover.depths_agd(
            CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
              Some{Tree.cost(Tree.Node{g, kids}, S)}),
            g, kids, S, Nil{}, depths, Unit{},
            ok => d2 =>
              +neok : {CoverKids.Cover.all_ne(Groups.groups_build(g, S, Nil{}))
                       == True{} : Bool} =
                CoverKids.Cover.groups_build_ne(g, S, Nil{}, {==})
              +kb : {CoverKids.Cover.kids_in_b(kids, G) == True{} : Bool} =
                CoverKids.Cover.kids_in_to_b(kids, G, kidsin)
              CoverKids.Cover.groupkids_from(
                CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
                  Some{Tree.cost(Tree.Node{g, kids}, S)}),
                G, g, kids, Groups.groups_build(g, S, Nil{}), kb, neok, ok,
                kidsok =>
                  Cover.cover_node_dispatch(G, S, entries, g, kids, oracle,
                    all, wg, kidsok, d2, b, eb)))

# The node step of the structural induction.
def Cover.cover_node(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>, +g: +List<Nat>,
    +kids: +List<Tree.Child>,
    all: Cover.AllCover(G, S, entries, kids)) ->
  Cover.Stmt(G, S, entries, Tree.Node{g, kids}):
  oracle => valid =>
    Cover.cover_node_go(G, S, entries, g, kids,
      oracle, all, valid,
      Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==})

# The cover bound for one tree, uniformly over the candidate list and oracle.
def Cover.BoundAll(+G: +List<+List<Nat>>, t: Tree.Tree) -> Type:
  @S: +List<+List<Nat>> -> @entries: +List<+List<Maybe<&2, Nat>>>
  -> CoverOracle.Cover.Oracle(G, S, G, entries)
  -> Tree.Valid(t, G, S)
  -> CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
                          Some{Tree.cost(t, S)})

# The bound for every child in a list.
def Cover.AllBound(+G: +List<+List<Nat>>, +kids: +List<Tree.Child>) -> Type:
  match kids:
    case Nil{}:
      Unit
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          Cover.BoundAll(G, child) & Cover.AllBound(G, rest)

def Cover.cover_apply(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>,
    oracle: CoverOracle.Cover.Oracle(G, S, G, entries), +t: Tree.Tree,
    b: Cover.BoundAll(G, t), v: Tree.Valid(t, G, S)) ->
  CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
    Some{Tree.cost(t, S)}):
  b(S, entries, oracle, v)

# Turn the uniform bounds into the fixed-list induction hypothesis.
def Cover.allcover_of(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>,
    +kids: +List<Tree.Child>, b: Cover.AllBound(G, kids)) ->
  Cover.AllCover(G, S, entries, kids):
  match kids:
    case Nil{}:
      Unit{}
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          (bh, bt) = b
          (bh(S, entries), Cover.allcover_of(G, S, entries, rest, bt))

# Every child in the list satisfies the bound, by structural recursion.
def Cover.bounds(+G: +List<+List<Nat>>, +kids: +List<Tree.Child>) ->
  Cover.AllBound(G, kids):
  match kids:
    case Nil{}:
      Unit{}
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          match child:
            case Tree.Node{g, ckids}:
              ((S => entries => oracle => v =>
                  +S2 : +List<+List<Nat>> = S
                  +entries2 : +List<+List<Maybe<&2, Nat>>> = entries
                  Cover.cover_node(G, S2, entries2, g, ckids,
                    Cover.allcover_of(G, S2, entries2, ckids,
                      Cover.bounds(G, ckids)))(oracle)(v)),
               Cover.bounds(G, rest))

# The cover lemma: a valid tree costs at least the best guess value.
def Cover.bound(+G: +List<+List<Nat>>, t: Tree.Tree) -> Cover.BoundAll(G, t):
  match t:
    case Tree.Node{g, kids}:
      S => entries => oracle => v =>
        +S2 : +List<+List<Nat>> = S
        +entries2 : +List<+List<Maybe<&2, Nat>>> = entries
        +kids2 : +List<Tree.Child> = kids
        Cover.cover_node(G, S2, entries2, g, kids2,
          Cover.allcover_of(G, S2, entries2, kids2,
            Cover.bounds(G, kids2)))(oracle)(v)

def Cover.cover(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>,
    oracle: CoverOracle.Cover.Oracle(G, S, G, entries),
    t: Tree.Tree, v: Tree.Valid(t, G, S)) ->
  CoverMaybe.Cover.MLe(CoverOracle.Cover.BestValue(G, S, entries),
    Some{Tree.cost(t, S)}):
  Cover.bound(G, t)(S, entries, oracle, v)
