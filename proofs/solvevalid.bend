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
