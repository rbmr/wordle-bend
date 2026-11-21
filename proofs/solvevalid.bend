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

# A membership of the head word in any list that ends at its group. The head
# word is literal, so the proof is rebuilt at every prefix step instead of being
# shared.
def SV.mem_head(+prefix: +List<Groups.Group>, +f: +List<Feedback.Color>,
    +w: +List<Nat>, +wt: +List<+List<Nat>>, +rest: +List<Groups.Group>,
    +fb: +List<Feedback.Color>,
    +efb: {Feedback.feedback_eq(fb, f) == True{} : Bool}) ->
  NV.NV.InGroupsFb(w, fb,
    List.append(&2, Groups.Group, prefix, Groups.Group{f, w <> wt} <> rest)):
  match prefix:
    case Nil{}:
      Inl{(Inl{{==}}, efb)}
    case Con{gp, t}:
      match gp:
        case Groups.Group{f2, ws2}:
          Inr{SV.mem_head(t, f, w, wt, rest, fb, efb)}

# The groups before the target all have a different feedback. The target group
# is the current one and its head word is the candidate, so its membership is
# literal at every step.
def SV.prefix_false(+before: +List<Groups.Group>, +f: +List<Feedback.Color>,
    +w: +List<Nat>, +wt: +List<+List<Nat>>, +rest: +List<Groups.Group>,
    +fb: +List<Feedback.Color>,
    +efb: {Feedback.feedback_eq(fb, f) == True{} : Bool},
    d: GD.GD.Distinct(List.append(&2, Groups.Group, before,
         Groups.Group{f, w <> wt} <> rest))) ->
  DG.DG.AllFalse(SV.Fbs(before), fb):
  match before:
    case Nil{}:
      Unit{}
    case Con{gp, t}:
      match gp:
        case Groups.Group{f2, ws2}:
          (nf, dt) = d
          m2 : NV.NV.InGroupsFb(w, fb,
                  List.append(&2, Groups.Group, t,
                    Groups.Group{f, w <> wt} <> rest)) =
            SV.mem_head(t, f, w, wt, rest, fb, efb)
          (NV.NV.not_fb_value(f2, fb,
             List.append(&2, Groups.Group, t, Groups.Group{f, w <> wt} <> rest), w, nf, m2),
           SV.prefix_false(t, f, w, wt, rest, fb, efb, dt))

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
