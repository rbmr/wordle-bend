# Depth of a candidate through a list of feedback groups.
#
# `Tree.depth.go` scans the children of a node and follows the one whose
# feedback matches. The children of a guess are in group order, and the groups
# built from a candidate list have pairwise different feedbacks. This module
# proves that a candidate in some group is found by that scan.
#
# The affine bookkeeping is the point of the `AbsentDepth` lemma. The membership
# proof of the candidate is needed twice in the recursive case: once to know
# that the head group has a different feedback (so the scan skips it) and once
# for the recursive call. Both facts are produced in one traversal, by threading
# the feedbacks of the groups still above the candidate as a list (`AllNotFb`)
# and returning the matching inequalities for all of them (`AllFalse`).
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ../src/groups.bend as Groups
import ../src/solve_ref.bend as SolveRef
import ./logic.bend as Logic
import ./feedback.bend as Fb
import ./groupsdistinct.bend as GD
import ./nodevalid.bend as NV
import ./children.bend as CH
import ./eval.bend as Eval
import ./kids.bend as KidsProof
import ./nodecost.bend as NodeCost

# The depth half of validity.
def DG.valid_depth(t: Tree.Tree, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    v: Tree.Valid(t, G, S)) -> Tree.AllHaveDepth(t, S):
  match v:
    case (ti, ad):
      ad

# Every feedback in the list differs from `fb`.
def DG.AllFalse(+fs: +List<+List<Feedback.Color>>,
    +fb: +List<Feedback.Color>) -> Type:
  match fs:
    case Nil{}:
      Unit
    case Con{f, t}:
      {Feedback.feedback_eq(f, fb) == False{} : Bool} & DG.AllFalse(t, fb)

# Every feedback in the list is absent from every group.
def DG.AllNotFb(+fs: +List<+List<Feedback.Color>>,
    +gs: +List<Groups.Group>) -> Type:
  match fs:
    case Nil{}:
      Unit
    case Con{f, t}:
      GD.GD.NotFb(f, gs) & DG.AllNotFb(t, gs)

# `fb` and `f` are equal feedbacks, and every element of `fs` is absent from
# the group list headed by `f`.
def DG.all_not_fb_tail(+fs: +List<+List<Feedback.Color>>,
    +f: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +rest: +List<Groups.Group>,
    nfs: DG.AllNotFb(fs, Groups.Group{f, ws} <> rest)) ->
  DG.AllNotFb(fs, rest):
  match fs:
    case Nil{}:
      Unit{}
    case Con{a, t}:
      (nf_a, tr) = nfs
      (h_af, nf_a_rest) = nf_a
      (nf_a_rest, DG.all_not_fb_tail(t, f, ws, rest, tr))

# Rewrite the head feedback of `AllNotFb` from `f` to the equal feedback `fb`.
def DG.all_false_cons(+a: +List<Feedback.Color>, +t: +List<+List<Feedback.Color>>,
    +f: +List<Feedback.Color>, +fb: +List<Feedback.Color>,
    h: {Feedback.feedback_eq(a, f) == False{} : Bool},
    ht: DG.AllFalse(t, fb),
    e: {f == fb : +List<Feedback.Color>}) ->
  DG.AllFalse(a <> t, fb):
  +h2 : {Feedback.feedback_eq(a, f) == Feedback.feedback_eq(a, fb) : Bool} =
    Equal.cong(+List<Feedback.Color>, Bool, x => Feedback.feedback_eq(a, x), f, fb, e)
  (Equal.trans(Bool, Feedback.feedback_eq(a, fb), Feedback.feedback_eq(a, f), False{},
     Equal.sym(Bool, Feedback.feedback_eq(a, f), Feedback.feedback_eq(a, fb), h2), h),
   ht)

def DG.all_false_of_not_fb(+fs: +List<+List<Feedback.Color>>,
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +rest: +List<Groups.Group>,
    nfs: DG.AllNotFb(fs, Groups.Group{fb, ws} <> rest)) ->
  DG.AllFalse(fs, fb):
  match fs:
    case Nil{}:
      Unit{}
    case Con{a, t}:
      (nf_a, tr) = nfs
      (h_af, nf_a_rest) = nf_a
      (h_af, DG.all_false_of_not_fb(t, fb, ws, rest, tr))

# Transport the absence of a group's feedback along an equality of group lists.
def DG.allnotfb_transport(+fs: +List<+List<Feedback.Color>>,
    +gs: +List<Groups.Group>, +gs2: +List<Groups.Group>,
    e: {gs == gs2 : +List<Groups.Group>}, nfs: DG.AllNotFb(fs, gs)) ->
  DG.AllNotFb(fs, gs2):
  %e : DG.AllNotFb(fs, _)
  nfs

# Eliminate the paired result of `AbsentDepth`.
def DG.use_result(-R: Type, +p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +rest: +List<Groups.Group>, +fs: +List<+List<Feedback.Color>>,
    +fb: +List<Feedback.Color>, +w: +List<Nat>,
    r: DG.AllFalse(fs, fb)
       & {Maybe.is_some(&1, Nat,
           Tree.depth.go(CH.CH.children(p, G, S, rest, inf), fb, w)) == True{} : Bool},
    k: DG.AllFalse(fs, fb)
       -> {Maybe.is_some(&1, Nat,
            Tree.depth.go(CH.CH.children(p, G, S, rest, inf), fb, w)) == True{} : Bool}
       -> R) -> R:
  match r:
    case (a, g):
      k(a, g)

# Split the head of an `AllFalse` conjunction.
def DG.use_allfalse_cons(-R: Type, +f: +List<Feedback.Color>,
    +fs: +List<+List<Feedback.Color>>, +fb: +List<Feedback.Color>,
    a: DG.AllFalse(f <> fs, fb),
    k: {Feedback.feedback_eq(f, fb) == False{} : Bool}
       -> DG.AllFalse(fs, fb) -> R) -> R:
  match a:
    case (e, t):
      k(e, t)

# The scan over the children of a group list for `fb` finds a candidate `w`
# that lies in one of the groups with that feedback.
def DG.AbsentDepth(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +gs: +List<Groups.Group>, +fs: +List<+List<Feedback.Color>>,
    +fb: +List<Feedback.Color>, +w: +List<Nat>,
    nfs: DG.AllNotFb(fs, gs), d: GD.GD.Distinct(gs),
    cv: NV.NV.ChildrenValid(p, G, S, gs, inf),
    m: NV.NV.InGroupsFb(w, fb, gs)) ->
  DG.AllFalse(fs, fb)
  & {Maybe.is_some(&1, Nat,
      Tree.depth.go(CH.CH.children(p, G, S, gs, inf), fb, w)) == True{} : Bool}:
  match gs:
    case Nil{}:
      match m:
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          (nf_head, d_tail) = d
          (valid_head, cv_tail) = cv
          match m:
            case Inl{pin}:
              (iw, e_fb) = pin
              +e_f : {f == fb : +List<Feedback.Color>} =
                Equal.sym(+List<Feedback.Color>, fb, f,
                  Fb.FbPrf.feedback_eq_true(fb, f, e_fb))
              e_group : {Groups.Group{f, ws} == Groups.Group{fb, ws}
                          : Groups.Group} =
                Equal.cong(+List<Feedback.Color>, Groups.Group,
                  x => Groups.Group{x, ws}, f, fb, e_f)
              e_groups : {Groups.Group{f, ws} <> rest
                           == Groups.Group{fb, ws} <> rest
                           : +List<Groups.Group>} =
                Equal.cong(Groups.Group, +List<Groups.Group>, x => x <> rest,
                  Groups.Group{f, ws}, Groups.Group{fb, ws}, e_group)
              nfs_fb : DG.AllNotFb(fs, Groups.Group{fb, ws} <> rest) =
                DG.allnotfb_transport(fs, Groups.Group{f, ws} <> rest,
                  Groups.Group{fb, ws} <> rest, e_groups, nfs)
              afs : DG.AllFalse(fs, fb) =
                DG.all_false_of_not_fb(fs, fb, ws, rest, nfs_fb)
              +e_sym : {Feedback.feedback_eq(f, fb) == True{} : Bool} =
                Equal.trans(Bool, Feedback.feedback_eq(f, fb), Feedback.feedback_eq(f, f),
                  True{},
                  Equal.cong(+List<Feedback.Color>, Bool,
                    x => Feedback.feedback_eq(f, x), fb, f,
                    Equal.sym(+List<Feedback.Color>, f, fb, e_f)),
                  Fb.FbPrf.feedback_eq_refl(f))
              +e_head : {Tree.depth.go(
                    Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                    <> CH.CH.children(p, G, S, rest, inf), fb, w)
                  == Tree.depth(NV.NV.kid_tree(p, G, ws, inf), w) : Maybe<Nat>} =
                NV.NV.depth_go_head_at(w, fb, f, NV.NV.kid_tree(p, G, ws, inf),
                  CH.CH.children(p, G, S, rest, inf), e_sym)
              ad_head : Tree.AllHaveDepth(NV.NV.kid_tree(p, G, ws, inf), ws) =
                DG.valid_depth(NV.NV.kid_tree(p, G, ws, inf), G, ws, valid_head)
              +e_kid : {Maybe.is_some(&1, Nat,
                    Tree.depth(NV.NV.kid_tree(p, G, ws, inf), w)) == True{} : Bool} =
                KidsProof.KidsProof.all_have_depth_mem(NV.NV.kid_tree(p, G, ws, inf), ws, ad_head, w, iw)
              +e_is : {Maybe.is_some(&1, Nat,
                    Tree.depth.go(Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                      <> CH.CH.children(p, G, S, rest, inf), fb, w))
                  == Maybe.is_some(&1, Nat,
                       Tree.depth(NV.NV.kid_tree(p, G, ws, inf), w)) : Bool} =
                Equal.cong(Maybe<Nat>, Bool, x => Maybe.is_some(&1, Nat, x),
                  Tree.depth.go(Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                    <> CH.CH.children(p, G, S, rest, inf), fb, w),
                  Tree.depth(NV.NV.kid_tree(p, G, ws, inf), w), e_head)
              (afs,
               Equal.trans(Bool,
                 Maybe.is_some(&1, Nat,
                   Tree.depth.go(Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                     <> CH.CH.children(p, G, S, rest, inf), fb, w)),
                 Maybe.is_some(&1, Nat, Tree.depth(NV.NV.kid_tree(p, G, ws, inf), w)),
                 True{}, e_is, e_kid))
            case Inr{pt}:
              nfs2 : DG.AllNotFb(f <> fs, rest) =
                (nf_head,
                 DG.all_not_fb_tail(fs, f, ws, rest, nfs))
              DG.use_result(
                DG.AllFalse(fs, fb)
                & {Maybe.is_some(&1, Nat,
                    Tree.depth.go(Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                      <> CH.CH.children(p, G, S, rest, inf), fb, w)) == True{} : Bool},
                p, G, S, inf, rest, f <> fs, fb, w,
                DG.AbsentDepth(p, G, S, inf, rest, f <> fs, fb, w,
                  nfs2, d_tail, cv_tail, pt),
                af => go_rest =>
                  DG.use_allfalse_cons(
                    DG.AllFalse(fs, fb)
                    & {Maybe.is_some(&1, Nat,
                        Tree.depth.go(Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                          <> CH.CH.children(p, G, S, rest, inf), fb, w)) == True{} : Bool},
                    f, fs, fb, af,
                    e_f => afs =>
                      +e_skip : {Tree.depth.go(
                            Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                            <> CH.CH.children(p, G, S, rest, inf), fb, w)
                          == Tree.depth.go(CH.CH.children(p, G, S, rest, inf), fb, w)
                          : Maybe<Nat>} =
                        NV.NV.depth_go_skip(w, fb, f, NV.NV.kid_tree(p, G, ws, inf),
                          CH.CH.children(p, G, S, rest, inf), e_f)
                      +e_is : {Maybe.is_some(&1, Nat,
                            Tree.depth.go(Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                              <> CH.CH.children(p, G, S, rest, inf), fb, w))
                          == Maybe.is_some(&1, Nat,
                               Tree.depth.go(CH.CH.children(p, G, S, rest, inf), fb, w))
                          : Bool} =
                        Equal.cong(Maybe<Nat>, Bool, x => Maybe.is_some(&1, Nat, x),
                          Tree.depth.go(Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                            <> CH.CH.children(p, G, S, rest, inf), fb, w),
                          Tree.depth.go(CH.CH.children(p, G, S, rest, inf), fb, w), e_skip)
                      (afs,
                       Equal.trans(Bool,
                         Maybe.is_some(&1, Nat,
                           Tree.depth.go(Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                             <> CH.CH.children(p, G, S, rest, inf), fb, w)),
                         Maybe.is_some(&1, Nat,
                           Tree.depth.go(CH.CH.children(p, G, S, rest, inf), fb, w)),
                         True{}, e_is, go_rest))))

# The scan finds a candidate whose feedback is the guess's feedback.
def DG.depth_groups(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +groups: +List<Groups.Group>, +g: +List<Nat>, +w: +List<Nat>,
    d: GD.GD.Distinct(groups), cv: NV.NV.ChildrenValid(p, G, S, groups, inf),
    m: NV.NV.InGroupsFb(w, Feedback.feedback(g, w), groups)) ->
  {Maybe.is_some(&1, Nat,
     Tree.depth.go(CH.CH.children(p, G, S, groups, inf),
       Feedback.feedback(g, w), w)) == True{} : Bool}:
  DG.use_result(
    {Maybe.is_some(&1, Nat,
       Tree.depth.go(CH.CH.children(p, G, S, groups, inf),
         Feedback.feedback(g, w), w)) == True{} : Bool},
    p, G, S, inf, groups, Nil{}, Feedback.feedback(g, w), w,
    DG.AbsentDepth(p, G, S, inf, groups, Nil{}, Feedback.feedback(g, w), w,
      Unit{}, d, cv, m),
    af => go => go)

# The node depth of a candidate follows from the scan.
def DG.node_depth_bool(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    b: Bool, +eb: {b == Feedback.word_eq(g, w) : Bool},
    +go: {Maybe.is_some(&1, Nat,
          Tree.depth.go(kids, Feedback.feedback(g, w), w)) == True{} : Bool}) ->
  {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool}:
  match b:
    case True{}:
      +eq : {Tree.depth(Tree.Node{g, kids}, w)
             == NodeCost.NodeCost.node_depth_of(g, kids, w, True{}) : Maybe<Nat>} =
        Equal.cong(Bool, Maybe<Nat>,
          x => NodeCost.NodeCost.node_depth_of(g, kids, w, x),
          Feedback.word_eq(g, w), True{},
          Equal.sym(Bool, True{}, Feedback.word_eq(g, w), eb))
      Equal.trans(Bool,
        Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)),
        Maybe.is_some(&1, Nat, NodeCost.NodeCost.node_depth_of(g, kids, w, True{})),
        True{},
        Equal.cong(Maybe<Nat>, Bool, x => Maybe.is_some(&1, Nat, x),
          Tree.depth(Tree.Node{g, kids}, w),
          NodeCost.NodeCost.node_depth_of(g, kids, w, True{}), eq),
        {==})
    case False{}:
      +eq : {Tree.depth(Tree.Node{g, kids}, w)
             == NodeCost.NodeCost.node_depth_of(g, kids, w, False{}) : Maybe<Nat>} =
        Equal.cong(Bool, Maybe<Nat>,
          x => NodeCost.NodeCost.node_depth_of(g, kids, w, x),
          Feedback.word_eq(g, w), False{},
          Equal.sym(Bool, False{}, Feedback.word_eq(g, w), eb))
      +e_bump : {Maybe.is_some(&1, Nat,
                   NodeCost.NodeCost.node_depth_of(g, kids, w, False{}))
                 == Maybe.is_some(&1, Nat,
                      Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)))
                 : Bool} =
        {==}
      +e_is : {Maybe.is_some(&1, Nat,
                 Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)))
               == Maybe.is_some(&1, Nat,
                    Tree.depth.go(kids, Feedback.feedback(g, w), w)) : Bool} =
        NodeCost.NodeCost.is_some_bump(
          Tree.depth.go(kids, Feedback.feedback(g, w), w))
      Equal.trans(Bool,
        Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)),
        Maybe.is_some(&1, Nat, NodeCost.NodeCost.node_depth_of(g, kids, w, False{})),
        True{},
        Equal.cong(Maybe<Nat>, Bool, x => Maybe.is_some(&1, Nat, x),
          Tree.depth(Tree.Node{g, kids}, w),
          NodeCost.NodeCost.node_depth_of(g, kids, w, False{}), eq),
        Equal.trans(Bool,
          Maybe.is_some(&1, Nat, NodeCost.NodeCost.node_depth_of(g, kids, w, False{})),
          Maybe.is_some(&1, Nat,
            Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))),
          True{}, e_bump,
          Equal.trans(Bool,
            Maybe.is_some(&1, Nat,
              Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))),
            Maybe.is_some(&1, Nat,
              Tree.depth.go(kids, Feedback.feedback(g, w), w)),
            True{}, e_is, go)))

# A candidate in a group has a depth in the node built from the groups.
def DG.node_depth_group(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +groups: +List<Groups.Group>, +g: +List<Nat>, +w: +List<Nat>,
    d: GD.GD.Distinct(groups), cv: NV.NV.ChildrenValid(p, G, S, groups, inf),
    m: NV.NV.InGroupsFb(w, Feedback.feedback(g, w), groups)) ->
  {Maybe.is_some(&1, Nat,
     Tree.depth(Tree.Node{g, CH.CH.children(p, G, S, groups, inf)}, w))
   == True{} : Bool}:
  +go : {Maybe.is_some(&1, Nat,
          Tree.depth.go(CH.CH.children(p, G, S, groups, inf),
            Feedback.feedback(g, w), w)) == True{} : Bool} =
    DG.depth_groups(p, G, S, inf, groups, g, w, d, cv, m)
  DG.node_depth_bool(g, CH.CH.children(p, G, S, groups, inf), w,
    Feedback.word_eq(g, w), {==}, go)

# The scan finds a candidate whose group is selected by a one-shot
# continuation. The continuation is called exactly once, at the group that
# contains the candidate, which lets the caller recompute that group's child
# validity without sharing a proof.
def DG.AbsentDepthTarget(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +gs: +List<Groups.Group>, +fs: +List<+List<Feedback.Color>>,
    +fb: +List<Feedback.Color>, +w: +List<Nat>,
    nfs: DG.AllNotFb(fs, gs), d: GD.GD.Distinct(gs),
    k: @f: +List<Feedback.Color> -> @ws: +List<+List<Nat>> ->
       {Feedback.feedback_eq(f, fb) == True{} : Bool} ->
       {Maybe.is_some(&1, Nat, Tree.depth(NV.NV.kid_tree(p, G, ws, inf), w))
        == True{} : Bool},
    m: NV.NV.InGroupsFb(w, fb, gs)) ->
  DG.AllFalse(fs, fb)
  & {Maybe.is_some(&1, Nat,
      Tree.depth.go(CH.CH.children(p, G, S, gs, inf), fb, w)) == True{} : Bool}:
  match gs:
    case Nil{}:
      match m:
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          (nf_head, d_tail) = d
          match m:
            case Inl{pin}:
              (iw, e_fb) = pin
              +e_f : {f == fb : +List<Feedback.Color>} =
                Equal.sym(+List<Feedback.Color>, fb, f,
                  Fb.FbPrf.feedback_eq_true(fb, f, e_fb))
              +e_sym : {Feedback.feedback_eq(f, fb) == True{} : Bool} =
                Equal.trans(Bool, Feedback.feedback_eq(f, fb), Feedback.feedback_eq(f, f),
                  True{},
                  Equal.cong(+List<Feedback.Color>, Bool,
                    x => Feedback.feedback_eq(f, x), fb, f,
                    Equal.sym(+List<Feedback.Color>, f, fb, e_f)),
                  Fb.FbPrf.feedback_eq_refl(f))
              afs : DG.AllFalse(fs, fb) =
                DG.all_false_of_not_fb(fs, fb, ws, rest,
                  DG.allnotfb_transport(fs, Groups.Group{f, ws} <> rest,
                    Groups.Group{fb, ws} <> rest,
                    Equal.cong(Groups.Group, +List<Groups.Group>, x => x <> rest,
                      Groups.Group{f, ws}, Groups.Group{fb, ws},
                      Equal.cong(+List<Feedback.Color>, Groups.Group,
                        x => Groups.Group{x, ws}, f, fb, e_f)),
                    nfs))
              +e_head : {Tree.depth.go(
                    Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                    <> CH.CH.children(p, G, S, rest, inf), fb, w)
                  == Tree.depth(NV.NV.kid_tree(p, G, ws, inf), w) : Maybe<Nat>} =
                NV.NV.depth_go_head_at(w, fb, f, NV.NV.kid_tree(p, G, ws, inf),
                  CH.CH.children(p, G, S, rest, inf), e_sym)
              +e_kid : {Maybe.is_some(&1, Nat,
                    Tree.depth(NV.NV.kid_tree(p, G, ws, inf), w)) == True{} : Bool} =
                k(f, ws, e_sym)
              +e_is : {Maybe.is_some(&1, Nat,
                    Tree.depth.go(Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                      <> CH.CH.children(p, G, S, rest, inf), fb, w))
                  == Maybe.is_some(&1, Nat,
                       Tree.depth(NV.NV.kid_tree(p, G, ws, inf), w)) : Bool} =
                Equal.cong(Maybe<Nat>, Bool, x => Maybe.is_some(&1, Nat, x),
                  Tree.depth.go(Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                    <> CH.CH.children(p, G, S, rest, inf), fb, w),
                  Tree.depth(NV.NV.kid_tree(p, G, ws, inf), w), e_head)
              (afs,
               Equal.trans(Bool,
                 Maybe.is_some(&1, Nat,
                   Tree.depth.go(Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                     <> CH.CH.children(p, G, S, rest, inf), fb, w)),
                 Maybe.is_some(&1, Nat, Tree.depth(NV.NV.kid_tree(p, G, ws, inf), w)),
                 True{}, e_is, e_kid))
            case Inr{pt}:
              nfs2 : DG.AllNotFb(f <> fs, rest) =
                (nf_head, DG.all_not_fb_tail(fs, f, ws, rest, nfs))
              DG.use_result(
                DG.AllFalse(fs, fb)
                & {Maybe.is_some(&1, Nat,
                    Tree.depth.go(Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                      <> CH.CH.children(p, G, S, rest, inf), fb, w)) == True{} : Bool},
                p, G, S, inf, rest, f <> fs, fb, w,
                DG.AbsentDepthTarget(p, G, S, inf, rest, f <> fs, fb, w,
                  nfs2, d_tail, k, pt),
                af => go_rest =>
                  DG.use_allfalse_cons(
                    DG.AllFalse(fs, fb)
                    & {Maybe.is_some(&1, Nat,
                        Tree.depth.go(Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                          <> CH.CH.children(p, G, S, rest, inf), fb, w)) == True{} : Bool},
                    f, fs, fb, af,
                    e_f => afs =>
                      +e_skip : {Tree.depth.go(
                            Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                            <> CH.CH.children(p, G, S, rest, inf), fb, w)
                          == Tree.depth.go(CH.CH.children(p, G, S, rest, inf), fb, w)
                          : Maybe<Nat>} =
                        NV.NV.depth_go_skip(w, fb, f, NV.NV.kid_tree(p, G, ws, inf),
                          CH.CH.children(p, G, S, rest, inf), e_f)
                      +e_is : {Maybe.is_some(&1, Nat,
                            Tree.depth.go(Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                              <> CH.CH.children(p, G, S, rest, inf), fb, w))
                          == Maybe.is_some(&1, Nat,
                               Tree.depth.go(CH.CH.children(p, G, S, rest, inf), fb, w))
                          : Bool} =
                        Equal.cong(Maybe<Nat>, Bool, x => Maybe.is_some(&1, Nat, x),
                          Tree.depth.go(Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                            <> CH.CH.children(p, G, S, rest, inf), fb, w),
                          Tree.depth.go(CH.CH.children(p, G, S, rest, inf), fb, w), e_skip)
                      (afs,
                       Equal.trans(Bool,
                         Maybe.is_some(&1, Nat,
                           Tree.depth.go(Tree.Child{f, NV.NV.kid_tree(p, G, ws, inf)}
                             <> CH.CH.children(p, G, S, rest, inf), fb, w)),
                         Maybe.is_some(&1, Nat,
                           Tree.depth.go(CH.CH.children(p, G, S, rest, inf), fb, w)),
                         True{}, e_is, go_rest))))
