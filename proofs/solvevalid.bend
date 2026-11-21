# Validity of the solver at every fuel.
#
# The fused search `step` returns a `Best` whose cost is either infinity or a
# valid tree. That invariant is proved by induction on the fuel, with no bound
# on the candidate count: too little fuel only ever turns a class into infinity,
# and infinity is the case where validity is vacuous. The per-class results are
# then folded into a node, and the candidates recover their depths from the
# classes they belong to.
#
# This module holds the arithmetic and fold plumbing. The group walk and the
# node construction follow below it.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as Fb
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./bestok.bend as BO
import ./children.bend as CH
import ./kids.bend as KidsProof
import ./nodecost.bend as NodeCost
import ./depthgroups.bend as DG
import ./nodevalid.bend as NV
import ./groupsdistinct.bend as GD
import ./groups.bend as Grp
import ./validbag.bend as VB

# A cost that is below infinity cannot also be at least infinity.
def SV.lt_ge_absurd_go(+a: Nat, +b: Nat, c: Cmp,
    +ec: {c == Nat.cmp(a, b) : Cmp},
    lt: {Cmp.is_lt(c) == True{} : Bool},
    ge: {Cmp.is_ge(c) == True{} : Bool}) -> Empty:
  match c:
    case LT{}:
      Logic.Proof.false_ne_true(ge)
    case EQ{}:
      Logic.Proof.false_ne_true(lt)
    case GT{}:
      Logic.Proof.false_ne_true(lt)

def SV.lt_ge_absurd(+a: Nat, +b: Nat,
    lt: {Nat.is_lt(a, b) == True{} : Bool},
    ge: {Nat.is_ge(a, b) == True{} : Bool}) -> Empty:
  SV.lt_ge_absurd_go(a, b, Nat.cmp(a, b), {==}, lt, ge)

# The tree of a finite best result is valid.
def SV.valid_of_ok_lt(+inf: Nat, best: SolveRef.Best,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    lt: {Nat.is_lt(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    ok: BO.BO.BestOK(inf, best, G, S)) -> Tree.Valid(Eval.Eval.tree_of(best), G, S):
  match best:
    case SolveRef.Best{tree, +cost}:
      match ok:
        case Inl{ge}:
          Empty.absurd(Tree.Valid(tree, G, S),
                       SV.lt_ge_absurd(cost, inf, lt, ge))
        case Inr{p}:
          (lt2, v) = p
          v

# A candidate result is OK when its tree is valid whenever its cost is finite.
def SV.cand_ok_go(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, b: Bool,
    +eb: {b == Nat.is_ge(candCost, inf) : Bool},
    cond: {Nat.is_lt(candCost, inf) == True{} : Bool} -> Tree.Valid(candTree, G, S)) ->
  BO.BO.BestOK(inf, SolveRef.Best{candTree, candCost}, G, S):
  match b:
    case True{}:
      Inl{Equal.sym(Bool, b, Nat.is_ge(candCost, inf), eb)}
    case False{}:
      Inr{(Sat.SB.lt_of_ge_false(candCost, inf,
             Equal.sym(Bool, b, Nat.is_ge(candCost, inf), eb)),
           cond(Sat.SB.lt_of_ge_false(candCost, inf,
             Equal.sym(Bool, b, Nat.is_ge(candCost, inf), eb))))}

def SV.cand_ok(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    cond: {Nat.is_lt(candCost, inf) == True{} : Bool} -> Tree.Valid(candTree, G, S)) ->
  BO.BO.BestOK(inf, SolveRef.Best{candTree, candCost}, G, S):
  SV.cand_ok_go(inf, candCost, candTree, G, S, Nat.is_ge(candCost, inf), {==}, cond)

# `better` keeps the invariant when the candidate is valid on its finite costs.
def SV.better_cond_go(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +tree: Tree.Tree, +cost: Nat,
    b: Bool, +eb: {b == Nat.is_lt(candCost, cost) : Bool},
    cond: {Nat.is_lt(candCost, inf) == True{} : Bool} -> Tree.Valid(candTree, G, S),
    ok: BO.BO.BestOK(inf, SolveRef.Best{tree, cost}, G, S)) ->
  BO.BO.BestOK(inf,
    Feedback.Bool.case(SolveRef.Best, b,
      SolveRef.Best{candTree, candCost}, SolveRef.Best{tree, cost}), G, S):
  match b:
    case True{}:
      SV.cand_ok(inf, candCost, candTree, G, S, cond)
    case False{}:
      ok

def SV.better_cond(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    best: SolveRef.Best, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    cond: {Nat.is_lt(candCost, inf) == True{} : Bool} -> Tree.Valid(candTree, G, S),
    ok: BO.BO.BestOK(inf, best, G, S)) ->
  BO.BO.BestOK(inf, SolveRef.better(candCost, candTree, best), G, S):
  match best:
    case SolveRef.Best{tree, +cost}:
      SV.better_cond_go(inf, candCost, candTree, G, S, tree, cost,
        Nat.is_lt(candCost, cost), {==}, cond, ok)

# The feedbacks of a group list, in order. The scan over a node's children
# needs exactly these, because a child's feedback is its group's feedback.
def SV.Fbs(+gs: +List<Groups.Group>) -> +List<+List<Feedback.Color>>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          f <> SV.Fbs(t)

# A membership in a suffix is a membership in any list ending with it.
def SV.in_groups_weaken(+prefix: +List<Groups.Group>, +suffix: +List<Groups.Group>,
    +w: +List<Nat>, +fb: +List<Feedback.Color>,
    m: NV.NV.InGroupsFb(w, fb, suffix)) ->
  NV.NV.InGroupsFb(w, fb, List.append(&2, Groups.Group, prefix, suffix)):
  match prefix:
    case Nil{}:
      m
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          Inr{SV.in_groups_weaken(t, suffix, w, fb, m)}

# The children of an appended group list are the appended children.
def SV.children_append(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +xs: +List<Groups.Group>, +ys: +List<Groups.Group>, +inf: Nat) ->
  {CH.CH.children(p, G, S, List.append(&2, Groups.Group, xs, ys), inf)
   == List.append(&2, Tree.Child,
        CH.CH.children(p, G, S, xs, inf), CH.CH.children(p, G, S, ys, inf))
   : +List<Tree.Child>}:
  match xs:
    case Nil{}:
      {==}
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          Equal.cong(+List<Tree.Child>, +List<Tree.Child>,
            l => CH.CH.kid(p, G, S, f, ws, inf) <> l,
            CH.CH.children(p, G, S, List.append(&2, Groups.Group, t, ys), inf),
            List.append(&2, Tree.Child,
              CH.CH.children(p, G, S, t, inf), CH.CH.children(p, G, S, ys, inf)),
            SV.children_append(p, G, S, t, ys, inf))

# A list with no matching feedback in the groups before the target is skipped.
def SV.skip_children(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +before: +List<Groups.Group>, +suffix: +List<Groups.Group>,
    +fb: +List<Feedback.Color>, +w: +List<Nat>,
    afs: DG.DG.AllFalse(SV.Fbs(before), fb)) ->
  {Tree.depth.go(List.append(&2, Tree.Child,
      CH.CH.children(p, G, S, before, inf), CH.CH.children(p, G, S, suffix, inf)), fb, w)
   == Tree.depth.go(CH.CH.children(p, G, S, suffix, inf), fb, w) : Maybe<Nat>}:
  match before:
    case Nil{}:
      {==}
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          (h, afs2) = afs
          Equal.trans(Maybe<Nat>,
            Tree.depth.go(List.append(&2, Tree.Child,
              CH.CH.children(p, G, S, Groups.Group{f, ws} <> t, inf),
              CH.CH.children(p, G, S, suffix, inf)), fb, w),
            Tree.depth.go(List.append(&2, Tree.Child,
              CH.CH.children(p, G, S, t, inf),
              CH.CH.children(p, G, S, suffix, inf)), fb, w),
            Tree.depth.go(CH.CH.children(p, G, S, suffix, inf), fb, w),
            NV.NV.depth_go_skip(w, fb, f, NV.NV.kid_tree(p, G, ws, inf),
              List.append(&2, Tree.Child,
                CH.CH.children(p, G, S, t, inf),
                CH.CH.children(p, G, S, suffix, inf)), h),
            SV.skip_children(p, G, S, inf, t, suffix, fb, w, afs2))

# Membership of a word at the end of a word prefix.
def SV.in_words_at(+wpre: +List<+List<Nat>>, +w: +List<Nat>,
    +wt: +List<+List<Nat>>) ->
  Grp.Grp.InWords(w, List.append(&2, +List<Nat>, wpre, w <> wt)):
  match wpre:
    case Nil{}:
      Inl{{==}}
    case Con{h, t}:
      Inr{SV.in_words_at(t, w, wt)}

# A membership of the word at the end of a word prefix, inside the group at the
# end of a group prefix.
def SV.mem_at(+prefix: +List<Groups.Group>, +f: +List<Feedback.Color>,
    +gws: +List<+List<Nat>>, +wpre: +List<+List<Nat>>, +w: +List<Nat>,
    +wt: +List<+List<Nat>>, +rest: +List<Groups.Group>,
    +fb: +List<Feedback.Color>,
    +efb: {Feedback.feedback_eq(fb, f) == True{} : Bool},
    +eGws: {gws == List.append(&2, +List<Nat>, wpre, w <> wt) : +List<+List<Nat>>}) ->
  NV.NV.InGroupsFb(w, fb,
    List.append(&2, Groups.Group, prefix, Groups.Group{f, gws} <> rest)):
  match prefix:
    case Nil{}:
      iw : Grp.Grp.InWords(w, gws) =
        %Equal.sym(+List<+List<Nat>>, gws,
           List.append(&2, +List<Nat>, wpre, w <> wt), eGws)
        : Grp.Grp.InWords(w, _)
        SV.in_words_at(wpre, w, wt)
      Inl{(iw, efb)}
    case Con{gp, t}:
      match gp:
        case Groups.Group{f2, ws2}:
          Inr{SV.mem_at(t, f, gws, wpre, w, wt, rest, fb, efb, eGws)}

# The groups before the target all have a different feedback, for a word at the
# end of a word prefix of the target group.
def SV.prefix_false(+before: +List<Groups.Group>, +f: +List<Feedback.Color>,
    +gws: +List<+List<Nat>>, +wpre: +List<+List<Nat>>, +w: +List<Nat>,
    +wt: +List<+List<Nat>>, +rest: +List<Groups.Group>,
    +fb: +List<Feedback.Color>,
    +efb: {Feedback.feedback_eq(fb, f) == True{} : Bool},
    +eGws: {gws == List.append(&2, +List<Nat>, wpre, w <> wt) : +List<+List<Nat>>},
    d: GD.GD.Distinct(List.append(&2, Groups.Group, before,
         Groups.Group{f, gws} <> rest))) ->
  DG.DG.AllFalse(SV.Fbs(before), fb):
  match before:
    case Nil{}:
      Unit{}
    case Con{gp, t}:
      match gp:
        case Groups.Group{f2, ws2}:
          (nf, dt) = d
          (NV.NV.not_fb_value(f2, fb,
             List.append(&2, Groups.Group, t, Groups.Group{f, gws} <> rest), w, nf,
             SV.mem_at(t, f, gws, wpre, w, wt, rest, fb, efb, eGws)),
           SV.prefix_false(t, f, gws, wpre, w, wt, rest, fb, efb, eGws, dt))

# Rewrite the group list under a distinctness proof.
def SV.distinct_transport(+a: +List<Groups.Group>, +b: +List<Groups.Group>,
    e: {a == b : +List<Groups.Group>}, d: GD.GD.Distinct(a)) ->
  GD.GD.Distinct(b):
  %e : GD.GD.Distinct(_)
  d

# `wpre ++ (w :: wt)` is `(wpre ++ [w]) ++ wt`.
def SV.append_singleton(+wpre: +List<+List<Nat>>, +w: +List<Nat>,
    +wt: +List<+List<Nat>>) ->
  {List.append(&2, +List<Nat>, wpre, w <> wt)
   == List.append(&2, +List<Nat>,
        List.append(&2, +List<Nat>, wpre, w <> Nil{}), wt)
   : +List<+List<Nat>>}:
  match wpre:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>, l => h <> l,
        List.append(&2, +List<Nat>, t, w <> wt),
        List.append(&2, +List<Nat>,
          List.append(&2, +List<Nat>, t, w <> Nil{}), wt),
        SV.append_singleton(t, w, wt))

# The children of the full group list split at a group.
def SV.children_full(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +full: +List<Groups.Group>, +before: +List<Groups.Group>,
    +f: +List<Feedback.Color>, +gws: +List<+List<Nat>>, +rest: +List<Groups.Group>,
    +eFull: {full == List.append(&2, Groups.Group, before,
               Groups.Group{f, gws} <> rest) : +List<Groups.Group>}) ->
  {CH.CH.children(p, G, S, full, inf)
   == List.append(&2, Tree.Child, CH.CH.children(p, G, S, before, inf),
        CH.CH.children(p, G, S, Groups.Group{f, gws} <> rest, inf))
   : List<&2, Tree.Child>}:
  Equal.trans(List<&2, Tree.Child>, CH.CH.children(p, G, S, full, inf),
    CH.CH.children(p, G, S,
      List.append(&2, Groups.Group, before, Groups.Group{f, gws} <> rest), inf),
    List.append(&2, Tree.Child, CH.CH.children(p, G, S, before, inf),
      CH.CH.children(p, G, S, Groups.Group{f, gws} <> rest, inf)),
    Equal.cong(List<&2, Groups.Group>, List<&2, Tree.Child>,
      l => CH.CH.children(p, G, S, l, inf), full,
      List.append(&2, Groups.Group, before, Groups.Group{f, gws} <> rest), eFull),
    SV.children_append(p, G, S, before, Groups.Group{f, gws} <> rest, inf))

# The words of a group all produce the group's feedback.
def SV.WsFb(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>) -> Type:
  match ws:
    case Nil{}:
      Unit
    case Con{w, t}:
      {Feedback.feedback_eq(Feedback.feedback(g, w), f) == True{} : Bool}
      & SV.WsFb(g, f, t)

def SV.WordsFb(+g: +List<Nat>, +gs: +List<Groups.Group>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{gp, t}:
      match gp:
        case Groups.Group{fb, ws}:
          SV.WsFb(g, fb, ws) & SV.WordsFb(g, t)

def SV.wsfb_append(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +xs: +List<+List<Nat>>, +ys: +List<+List<Nat>>,
    px: SV.WsFb(g, f, xs), py: SV.WsFb(g, f, ys)) ->
  SV.WsFb(g, f, List.append(&2, +List<Nat>, xs, ys)):
  match xs:
    case Nil{}:
      py
    case Con{h, t}:
      (ph, pt) = px
      (ph, SV.wsfb_append(g, f, t, ys, pt, py))

# Branch of `words_fb_add`, split on the feedback test.
def SV.words_fb_add_branch(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +t: +List<Groups.Group>, b: Bool,
    +eb: {b == Feedback.feedback_eq(fb, f) : Bool},
    +local: {Feedback.feedback_eq(Feedback.feedback(g, w), fb) == True{} : Bool},
    a_w: SV.WsFb(g, f, ws), a_t: SV.WordsFb(g, t),
    k: SV.WordsFb(g, t) -> SV.WordsFb(g, Groups.group_add(w, fb, t))) ->
  SV.WordsFb(g, Feedback.Bool.case(+List<Groups.Group>, b,
    Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])} <> t,
    Groups.Group{f, ws} <> Groups.group_add(w, fb, t))):
  match b:
    case True{}:
      e_list : {fb == f : List<&2, Feedback.Color>} =
        Fb.FbPrf.feedback_eq_true(fb, f,
          Equal.sym(Bool, b, Feedback.feedback_eq(fb, f), eb))
      e_w : {Feedback.feedback_eq(Feedback.feedback(g, w), f) == True{} : Bool} =
        Equal.trans(Bool,
          Feedback.feedback_eq(Feedback.feedback(g, w), f),
          Feedback.feedback_eq(Feedback.feedback(g, w), fb),
          True{}, Equal.sym(Bool,
            Feedback.feedback_eq(Feedback.feedback(g, w), fb),
            Feedback.feedback_eq(Feedback.feedback(g, w), f),
            Equal.cong(+List<Feedback.Color>, Bool,
              x => Feedback.feedback_eq(Feedback.feedback(g, w), x), fb, f, e_list)),
          local)
      (SV.wsfb_append(g, f, ws, [w], a_w, (e_w, Unit{})), a_t)
    case False{}:
      (a_w, k(a_t))

# Adding a word keeps the word-feedback invariant of the groups.
def SV.words_fb_add(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +t: +List<Groups.Group>,
    +local: {Feedback.feedback_eq(Feedback.feedback(g, w), fb) == True{} : Bool},
    acc: SV.WordsFb(g, t)) ->
  SV.WordsFb(g, Groups.group_add(w, fb, t)):
  match t:
    case Nil{}:
      ((local, Unit{}), Unit{})
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          (a_w, a_t) = acc
          SV.words_fb_add_branch(g, w, fb, f, ws, rest,
            Feedback.feedback_eq(fb, f), {==}, local, a_w, a_t,
            a => SV.words_fb_add(g, w, fb, rest, local, a))

# Branch of `words_fb_build`, split on the word test.
def SV.words_fb_build_branch(+g: +List<Nat>, +w: +List<Nat>,
    +t: +List<+List<Nat>>, +acc: +List<Groups.Group>, b: Bool,
    +eb: {b == Feedback.word_eq(g, w) : Bool},
    acc_ok: SV.WordsFb(g, acc),
    k_t: SV.WordsFb(g, acc) -> SV.WordsFb(g, Groups.groups_build(g, t, acc)),
    k_f: SV.WordsFb(g, acc) -> SV.WordsFb(g, Groups.groups_build(g, t,
      Groups.group_add(w, Feedback.feedback(g, w), acc)))) ->
  SV.WordsFb(g, Feedback.Bool.case(+List<Groups.Group>, b,
    Groups.groups_build(g, t, acc),
    Groups.groups_build(g, t,
      Groups.group_add(w, Feedback.feedback(g, w), acc)))):
  match b:
    case True{}:
      k_t(acc_ok)
    case False{}:
      k_f(acc_ok)

def SV.words_fb_build(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +acc: +List<Groups.Group>, acc_ok: SV.WordsFb(g, acc)) ->
  SV.WordsFb(g, Groups.groups_build(g, S, acc)):
  match S:
    case Nil{}:
      acc_ok
    case Con{w, t}:
      SV.words_fb_build_branch(g, w, t, acc, Feedback.word_eq(g, w), {==}, acc_ok,
        aok => SV.words_fb_build(g, t, acc, aok),
        aok => SV.words_fb_build(g, t,
          Groups.group_add(w, Feedback.feedback(g, w), acc),
          SV.words_fb_add(g, w, Feedback.feedback(g, w), acc,
            Fb.FbPrf.feedback_eq_refl(Feedback.feedback(g, w)), aok)))

def SV.words_fb(+g: +List<Nat>, +S: +List<+List<Nat>>) ->
  SV.WordsFb(g, Groups.groups_build(g, S, Nil{})):
  SV.words_fb_build(g, S, Nil{}, Unit{})

# Drop the groups before the wanted one.
def SV.words_fb_skip(+g: +List<Nat>, +before: +List<Groups.Group>,
    +rest: +List<Groups.Group>,
    wfb: SV.WordsFb(g, List.append(&2, Groups.Group, before, rest))) ->
  SV.WordsFb(g, rest):
  match before:
    case Nil{}:
      wfb
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          (_, wfb2) = wfb
          SV.words_fb_skip(g, t, rest, wfb2)

# The head group's word-feedback facts.
def SV.words_fb_head(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +t: +List<Groups.Group>,
    wfb: SV.WordsFb(g, Groups.Group{f, ws} <> t)) -> SV.WsFb(g, f, ws):
  (w, _) = wfb
  w

# The depth fact of one candidate at its group.
def SV.cand_at_group(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +full: +List<Groups.Group>,
    +before: +List<Groups.Group>, +f: +List<Feedback.Color>,
    +gws: +List<+List<Nat>>, +wpre: +List<+List<Nat>>, +w: +List<Nat>,
    +wt: +List<+List<Nat>>, +rest: +List<Groups.Group>,
    +eGws: {gws == List.append(&2, +List<Nat>, wpre, w <> wt) : +List<+List<Nat>>},
    +eFull: {full == List.append(&2, Groups.Group, before,
               Groups.Group{f, gws} <> rest) : +List<Groups.Group>},
    +eFull0: {full == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    +efb: {Feedback.feedback_eq(Feedback.feedback(g, w), f) == True{} : Bool},
    dk: {Maybe.is_some(&1, Nat, Tree.depth(NV.NV.kid_tree(p, G, gws, inf), w))
         == True{} : Bool}) ->
  {Maybe.is_some(&1, Nat,
     Tree.depth(Tree.Node{g, CH.CH.children(p, G, S, full, inf)}, w)) == True{} : Bool}:
  d : GD.GD.Distinct(List.append(&2, Groups.Group, before,
         Groups.Group{f, gws} <> rest)) =
    SV.distinct_transport(Groups.groups_build(g, S, Nil{}),
      List.append(&2, Groups.Group, before, Groups.Group{f, gws} <> rest),
      Equal.trans(+List<Groups.Group>, Groups.groups_build(g, S, Nil{}), full,
        List.append(&2, Groups.Group, before, Groups.Group{f, gws} <> rest),
        Equal.sym(+List<Groups.Group>, full, Groups.groups_build(g, S, Nil{}), eFull0),
        eFull),
      GD.GD.groups_distinct(g, S))
  +fbw : +List<Feedback.Color> = Feedback.feedback(g, w)
  eCh = SV.children_full(p, G, S, inf, full, before, f, gws, rest, eFull)
  eSkip = SV.skip_children(p, G, S, inf, before, Groups.Group{f, gws} <> rest,
    Feedback.feedback(g, w), w,
    SV.prefix_false(before, f, gws, wpre, w, wt, rest,
      Feedback.feedback(g, w), efb, eGws, d))
  eHead = NV.NV.depth_go_head_at(w, Feedback.feedback(g, w), f,
    NV.NV.kid_tree(p, G, gws, inf), CH.CH.children(p, G, S, rest, inf),
    Fb.FeedbackProof.feedback_eq_sym(Feedback.feedback(g, w), f, efb))
  c1 = Equal.cong(List<&2, Tree.Child>, Bool,
    x => Maybe.is_some(&1, Nat, Tree.depth.go(x, Feedback.feedback(g, w), w)),
    CH.CH.children(p, G, S, full, inf),
    List.append(&2, Tree.Child, CH.CH.children(p, G, S, before, inf),
      CH.CH.children(p, G, S, Groups.Group{f, gws} <> rest, inf)),
    eCh)
  c2 = Equal.cong(Maybe<Nat>, Bool, x => Maybe.is_some(&1, Nat, x),
    Tree.depth.go(List.append(&2, Tree.Child,
      CH.CH.children(p, G, S, before, inf),
      CH.CH.children(p, G, S, Groups.Group{f, gws} <> rest, inf)),
      Feedback.feedback(g, w), w),
    Tree.depth.go(CH.CH.children(p, G, S, Groups.Group{f, gws} <> rest, inf),
      Feedback.feedback(g, w), w), eSkip)
  c3 = Equal.cong(Maybe<Nat>, Bool, x => Maybe.is_some(&1, Nat, x),
    Tree.depth.go(CH.CH.children(p, G, S, Groups.Group{f, gws} <> rest, inf),
      Feedback.feedback(g, w), w),
    Tree.depth(NV.NV.kid_tree(p, G, gws, inf), w), eHead)
  go = Equal.trans(Bool,
    Maybe.is_some(&1, Nat, Tree.depth.go(CH.CH.children(p, G, S, full, inf),
      Feedback.feedback(g, w), w)),
    Maybe.is_some(&1, Nat, Tree.depth(NV.NV.kid_tree(p, G, gws, inf), w)),
    True{},
    Equal.trans(Bool,
      Maybe.is_some(&1, Nat, Tree.depth.go(CH.CH.children(p, G, S, full, inf),
        Feedback.feedback(g, w), w)),
      Maybe.is_some(&1, Nat, Tree.depth.go(CH.CH.children(p, G, S,
        Groups.Group{f, gws} <> rest, inf), Feedback.feedback(g, w), w)),
      Maybe.is_some(&1, Nat, Tree.depth(NV.NV.kid_tree(p, G, gws, inf), w)),
      Equal.trans(Bool,
        Maybe.is_some(&1, Nat, Tree.depth.go(CH.CH.children(p, G, S, full, inf),
          Feedback.feedback(g, w), w)),
        Maybe.is_some(&1, Nat, Tree.depth.go(List.append(&2, Tree.Child,
          CH.CH.children(p, G, S, before, inf),
          CH.CH.children(p, G, S, Groups.Group{f, gws} <> rest, inf)),
          Feedback.feedback(g, w), w)),
        Maybe.is_some(&1, Nat, Tree.depth.go(CH.CH.children(p, G, S,
          Groups.Group{f, gws} <> rest, inf), Feedback.feedback(g, w), w)),
        c1, c2),
      c3),
    dk)
  DG.DG.node_depth_bool(g, CH.CH.children(p, G, S, full, inf), w,
    Feedback.word_eq(g, w), {==}, go)

# The node depth of every word of one group, from its child's depths.
def SV.group_depths(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +full: +List<Groups.Group>,
    +before: +List<Groups.Group>, +f: +List<Feedback.Color>,
    +gws: +List<+List<Nat>>, +ws: +List<+List<Nat>>, +wpre: +List<+List<Nat>>,
    +rest: +List<Groups.Group>,
    +eGws: {gws == List.append(&2, +List<Nat>, wpre, ws) : +List<+List<Nat>>},
    +eFull: {full == List.append(&2, Groups.Group, before,
               Groups.Group{f, gws} <> rest) : +List<Groups.Group>},
    +eFull0: {full == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    wsfb: SV.WsFb(g, f, ws),
    kidAd: Tree.AllHaveDepth(NV.NV.kid_tree(p, G, gws, inf), ws)) ->
  Tree.AllHaveDepth(Tree.Node{g, CH.CH.children(p, G, S, full, inf)}, ws):
  match ws:
    case Nil{}:
      Unit{}
    case Con{w, wt}:
      (efb, wsfb2) = wsfb
      (dk, kidAd2) = kidAd
      +eGws2 : {gws == List.append(&2, +List<Nat>,
                   List.append(&2, +List<Nat>, wpre, w <> Nil{}), wt)
                : +List<+List<Nat>>} =
        Equal.trans(+List<+List<Nat>>, gws,
          List.append(&2, +List<Nat>, wpre, w <> wt),
          List.append(&2, +List<Nat>,
            List.append(&2, +List<Nat>, wpre, w <> Nil{}), wt),
          eGws, SV.append_singleton(wpre, w, wt))
      (SV.cand_at_group(p, G, S, g, inf, full, before, f, gws, wpre, w, wt, rest,
         eGws, eFull, eFull0, efb, dk),
       SV.group_depths(p, G, S, g, inf, full, before, f, gws, wt,
         List.append(&2, +List<Nat>, wpre, w <> Nil{}), rest,
         eGws2, eFull, eFull0, wsfb2, kidAd2))

# The conjunction of the class results of a group list, in order.
def SV.Oks(+p: Nat, +G: +List<+List<Nat>>, +inf: Nat,
    +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          BO.BO.BestOK(inf,
            SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
              Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()),
            G, ws)
          & SV.Oks(p, G, inf, rest)

# The words of the groups, concatenated.
def SV.flatWords(+groups: +List<Groups.Group>) -> +List<+List<Nat>>:
  match groups:
    case Nil{}:
      Nil{}
    case Con{gp, t}:
      match gp:
        case Groups.Group{fb, ws}:
          List.append(&2, +List<Nat>, ws, SV.flatWords(t))

# A word in the right summand is in the append.
def SV.in_words_right(+w: +List<Nat>, +xs: +List<+List<Nat>>,
    +ys: +List<+List<Nat>>, m: Grp.Grp.InWords(w, ys)) ->
  Grp.Grp.InWords(w, List.append(&2, +List<Nat>, xs, ys)):
  match xs:
    case Nil{}:
      m
    case Con{h, t}:
      Inr{SV.in_words_right(w, t, ys, m)}

# A group membership is a membership in the concatenation.
def SV.flat_mem(+groups: +List<Groups.Group>, +w: +List<Nat>,
    m: Grp.Grp.InGroups(w, groups)) -> Grp.Grp.InWords(w, SV.flatWords(groups)):
  match groups:
    case Nil{}:
      Empty.absurd(Grp.Grp.InWords(w, Nil{}), m)
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          match m:
            case Inl{iw}:
              Grp.Grp.in_words_append_l(w, ws, SV.flatWords(t), iw)
            case Inr{m2}:
              SV.in_words_right(w, ws, SV.flatWords(t), SV.flat_mem(t, w, m2))

# A guess candidate has depth one.
def SV.fact_guess(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    e: {Feedback.word_eq(g, w) == True{} : Bool}) -> VB.VB.Fact(g, kids, w):
  +e_d : {Tree.depth(Tree.Node{g, kids}, w)
          == Feedback.Bool.case(Maybe<Nat>, True{}, Some{1n},
               Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)))
          : Maybe<Nat>} =
    Equal.cong(Bool, Maybe<Nat>,
      b => Feedback.Bool.case(Maybe<Nat>, b, Some{1n},
        Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))),
      Feedback.word_eq(g, w), True{}, e)
  +e_s : {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w))
          == Maybe.is_some(&1, Nat, Some{1n}) : Bool} =
    Equal.cong(Maybe<Nat>, Bool, x => Maybe.is_some(&1, Nat, x),
      Tree.depth(Tree.Node{g, kids}, w),
      Feedback.Bool.case(Maybe<Nat>, True{}, Some{1n},
        Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))), e_d)
  Equal.trans(Bool, Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)),
    Maybe.is_some(&1, Nat, Some{1n}), True{}, e_s, {==})

# A bag of facts for a list of words with their depths.
def SV.bag_of_cons(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    f: VB.VB.Fact(g, kids, w), +t: +List<+List<Nat>>,
    s: &bag: VB.VB.Bag(g, kids) ->
       {VB.VB.words(g, kids, bag) == t : +List<+List<Nat>>}) ->
  &bag: VB.VB.Bag(g, kids) ->
    {VB.VB.words(g, kids, bag) == w <> t : +List<+List<Nat>>}:
  match s:
    case Tuple{bt, et}:
      (VB.VB.entry(g, kids, w, f) <> bt,
       Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>, l => w <> l,
         VB.VB.words(g, kids, bt), t, et))

def SV.bag_of(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +ws: +List<+List<Nat>>, ad: Tree.AllHaveDepth(Tree.Node{g, kids}, ws)) ->
  &bag: VB.VB.Bag(g, kids) ->
    {VB.VB.words(g, kids, bag) == ws : +List<+List<Nat>>}:
  match ws:
    case Nil{}:
      (Nil{}, {==})
    case Con{w, t}:
      (f, ad2) = ad
      SV.bag_of_cons(g, kids, w, f, t, SV.bag_of(g, kids, t, ad2))

# The word-feedback fact of one group of a built group list.
def SV.group_wsfb(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +before: +List<Groups.Group>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +rest: +List<Groups.Group>,
    +full: +List<Groups.Group>,
    +eFull0: {full == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    +eFull: {full == List.append(&2, Groups.Group, before,
               Groups.Group{f, ws} <> rest) : +List<Groups.Group>}) ->
  SV.WsFb(g, f, ws):
  e : {Groups.groups_build(g, S, Nil{})
       == List.append(&2, Groups.Group, before, Groups.Group{f, ws} <> rest)
       : +List<Groups.Group>} =
    Equal.trans(+List<Groups.Group>, Groups.groups_build(g, S, Nil{}), full,
      List.append(&2, Groups.Group, before, Groups.Group{f, ws} <> rest),
      Equal.sym(+List<Groups.Group>, full, Groups.groups_build(g, S, Nil{}), eFull0),
      eFull)
  wfb : SV.WordsFb(g, List.append(&2, Groups.Group, before,
          Groups.Group{f, ws} <> rest)) =
    %e : SV.WordsFb(g, _)
    SV.words_fb(g, S)
  SV.words_fb_head(g, f, ws, rest,
    SV.words_fb_skip(g, before, Groups.Group{f, ws} <> rest, wfb))

# Split a validity proof into its two halves.
def SV.use_valid(-R: Type, +kid: Tree.Tree, +G: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, v: Tree.Valid(kid, G, ws),
    k: Tree.TreeIn(kid, G) -> Tree.AllHaveDepth(kid, ws) -> R) -> R:
  match v:
    case (ti, ad):
      k(ti, ad)

# Split the bag-of-facts existential.
def SV.use_bagof(-R: Type, +g: +List<Nat>, +kids: +List<Tree.Child>,
    +ws: +List<+List<Nat>>,
    s: &bag: VB.VB.Bag(g, kids) ->
       {VB.VB.words(g, kids, bag) == ws : +List<+List<Nat>>},
    k: @bag: VB.VB.Bag(g, kids) ->
       {VB.VB.words(g, kids, bag) == ws : +List<+List<Nat>>} -> R) -> R:
  match s:
    case Tuple{bag, e}:
      k(bag, e)

# `before ++ (gp :: rest)` is `(before ++ [gp]) ++ rest`.
def SV.group_assoc(+before: +List<Groups.Group>, gp: Groups.Group,
    +rest: +List<Groups.Group>) ->
  {List.append(&2, Groups.Group, before, gp <> rest)
   == List.append(&2, Groups.Group,
        List.append(&2, Groups.Group, before, gp <> Nil{}), rest)
   : +List<Groups.Group>}:
  match before:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(+List<Groups.Group>, +List<Groups.Group>, l => h <> l,
        List.append(&2, Groups.Group, t, gp <> rest),
        List.append(&2, Groups.Group,
          List.append(&2, Groups.Group, t, gp <> Nil{}), rest),
        SV.group_assoc(t, gp, rest))

# The class search result of a group.
def SV.classResult(+p: Nat, +G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +inf: Nat) -> SolveRef.Best:
  SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
    Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())

