# Feedback groups have pairwise different patterns.
#
# `groups_build` adds a word to the first group with the same feedback, and
# only opens a new group when no earlier group matches. That means a child list
# built from the groups has at most one child per feedback, so `Tree.lookup`
# and `Tree.depth` scan to the intended child. This module proves the list
# invariant that carries that fact through `group_add` and `groups_build`.
import Base
import ../src/feedback.bend as Feedback
import ../src/groups.bend as Groups
import ./feedback.bend as FbProof
import ./logic.bend as Logic

# A feedback different from every group's feedback.
def GD.NotFb(+fb: +List<Feedback.Color>, +gs: +List<Groups.Group>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          {Feedback.feedback_eq(fb, f) == False{} : Bool} & GD.NotFb(fb, t)

# Every pair of groups has different feedbacks.
def GD.Distinct(+gs: +List<Groups.Group>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{gp, t}:
      match gp:
        case Groups.Group{fb, ws}:
          GD.NotFb(fb, t) & GD.Distinct(t)

def GD.not_fb_head(+fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +t: +List<Groups.Group>,
    p: GD.NotFb(fb, Groups.Group{f, ws} <> t)) ->
  {Feedback.feedback_eq(fb, f) == False{} : Bool}:
  (p2, rest) = p
  p2

def GD.not_fb_tail(+fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +t: +List<Groups.Group>,
    p: GD.NotFb(fb, Groups.Group{f, ws} <> t)) ->
  GD.NotFb(fb, t):
  (p2, rest) = p
  rest

def GD.distinct_head(+fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +t: +List<Groups.Group>, p: GD.Distinct(Groups.Group{fb, ws} <> t)) ->
  GD.NotFb(fb, t):
  (p2, rest) = p
  p2

def GD.distinct_tail(+fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +t: +List<Groups.Group>, p: GD.Distinct(Groups.Group{fb, ws} <> t)) ->
  GD.Distinct(t):
  (p2, rest) = p
  rest

# Feedback equality false in one orientation is false in the other.
def GD.fb_false_sym(+a: +List<Feedback.Color>, +b: +List<Feedback.Color>,
    e: {Feedback.feedback_eq(a, b) == False{} : Bool}) ->
  {Feedback.feedback_eq(b, a) == False{} : Bool}:
  +eq : {Feedback.feedback_eq(b, a) == Feedback.feedback_eq(a, b) : Bool} =
    FbProof.FeedbackProof.feedback_eq_sym_bool(b, a)
  Equal.trans(Bool, Feedback.feedback_eq(b, a), Feedback.feedback_eq(a, b),
              False{}, eq, e)

# `group_add` keeps a feedback absent.
def GD.group_add_not_fb_go(+f0: +List<Feedback.Color>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +t: +List<Groups.Group>, b: Bool,
    +eb: {b == Feedback.feedback_eq(fb, f) : Bool},
    nf: GD.NotFb(f0, Groups.Group{f, ws} <> t),
    nfb: {Feedback.feedback_eq(f0, fb) == False{} : Bool},
    k: GD.NotFb(f0, t) -> GD.NotFb(f0, Groups.group_add(w, fb, t))) ->
  GD.NotFb(f0,
    Feedback.Bool.case(+List<Groups.Group>, b,
      Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])} <> t,
      Groups.Group{f, ws} <> Groups.group_add(w, fb, t))):
  match b:
    case True{}:
      nf
    case False{}:
      (h, tl) = nf
      (h, k(tl))

def GD.group_add_not_fb(+f0: +List<Feedback.Color>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +gs: +List<Groups.Group>,
    nf: GD.NotFb(f0, gs),
    +nfb: {Feedback.feedback_eq(f0, fb) == False{} : Bool}) ->
  GD.NotFb(f0, Groups.group_add(w, fb, gs)):
  match gs:
    case Nil{}:
      (nfb, Unit{})
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          GD.group_add_not_fb_go(f0, w, fb, f, ws, t,
            Feedback.feedback_eq(fb, f), {==}, nf, nfb,
            tl => GD.group_add_not_fb(f0, w, fb, t, tl, nfb))

# `group_add` keeps the list distinct.
def GD.group_add_distinct_go(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +t: +List<Groups.Group>, b: Bool,
    +eb: {b == Feedback.feedback_eq(fb, f) : Bool},
    d: GD.Distinct(Groups.Group{f, ws} <> t),
    k: GD.Distinct(t) -> GD.Distinct(Groups.group_add(w, fb, t))) ->
  GD.Distinct(
    Feedback.Bool.case(+List<Groups.Group>, b,
      Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])} <> t,
      Groups.Group{f, ws} <> Groups.group_add(w, fb, t))):
  match b:
    case True{}:
      d
    case False{}:
      (nf, dt) = d
      +nfb : {Feedback.feedback_eq(f, fb) == False{} : Bool} =
        GD.fb_false_sym(fb, f, Equal.sym(Bool, b, Feedback.feedback_eq(fb, f), eb))
      (GD.group_add_not_fb(f, w, fb, t, nf, nfb), k(dt))

def GD.group_add_distinct(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +gs: +List<Groups.Group>, d: GD.Distinct(gs)) ->
  GD.Distinct(Groups.group_add(w, fb, gs)):
  match gs:
    case Nil{}:
      (Unit{}, Unit{})
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          GD.group_add_distinct_go(w, fb, f, ws, t,
            Feedback.feedback_eq(fb, f), {==}, d,
            dt => GD.group_add_distinct(w, fb, t, dt))

# `groups_build` keeps the list distinct.
def GD.groups_build_distinct_go(+g: +List<Nat>, +w: +List<Nat>,
    +t: +List<+List<Nat>>, +acc: +List<Groups.Group>, b: Bool,
    +eb: {b == Feedback.word_eq(g, w) : Bool},
    d: GD.Distinct(acc),
    k: GD.Distinct(acc) -> GD.Distinct(Groups.group_add(w, Feedback.feedback(g, w), acc)),
    kt: @a: +List<Groups.Group> -> GD.Distinct(a) -> GD.Distinct(Groups.groups_build(g, t, a))) ->
  GD.Distinct(Feedback.Bool.case(+List<Groups.Group>, b,
    Groups.groups_build(g, t, acc),
    Groups.groups_build(g, t,
      Groups.group_add(w, Feedback.feedback(g, w), acc)))):
  match b:
    case True{}:
      kt(acc, d)
    case False{}:
      kt(Groups.group_add(w, Feedback.feedback(g, w), acc), k(d))

def GD.groups_build_distinct(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +acc: +List<Groups.Group>, d: GD.Distinct(acc)) ->
  GD.Distinct(Groups.groups_build(g, S, acc)):
  match S:
    case Nil{}:
      d
    case Con{w, t}:
      GD.groups_build_distinct_go(g, w, t, acc,
        Feedback.word_eq(g, w), {==}, d,
        d2 => GD.group_add_distinct(w, Feedback.feedback(g, w), acc, d2),
        a => d2 => GD.groups_build_distinct(g, t, a, d2))

# The groups built from no accumulator are distinct.
def GD.groups_distinct(+g: +List<Nat>, +S: +List<+List<Nat>>) ->
  GD.Distinct(Groups.groups_build(g, S, Nil{})):
  GD.groups_build_distinct(g, S, Nil{}, Unit{})
