# A node built from a guess and its group children is valid.
#
# `groups_build` partitions the candidates of a guess into feedback classes.
# A tree node whose children are the per-class search results is therefore
# valid: the guess is in the input list, every non-guess candidate belongs to a
# class, and the class child gives that candidate a depth. This module proves
# the membership and depth facts, using the pairwise distinct feedbacks to make
# `lookup` and `depth.go` land on the intended child.
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ../src/groups.bend as Groups
import ../src/solve_ref.bend as SolveRef
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as Fb
import ./groups.bend as Grp
import ./groupsdistinct.bend as GD
import ./children.bend as CH
import ./nodecost.bend as NodeCost
import ./kids.bend as KidsProof
import ./eval.bend as Eval

# A word lies in a group with the given feedback.
def NV.InGroupsFb(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +gs: +List<Groups.Group>) -> Type:
  match gs:
    case Nil{}:
      Empty
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          (Grp.Grp.InWords(w, ws) & {Feedback.feedback_eq(fb, f) == True{} : Bool})
          | NV.InGroupsFb(w, fb, t)

# `group_add` puts the new word in a group with its own feedback.
def NV.group_add_contains_fb_go(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, +ws: +List<+List<Nat>>, +t: +List<Groups.Group>,
    b: Bool, +eb: {b == Feedback.feedback_eq(fb, f) : Bool},
    k: Unit -> NV.InGroupsFb(w, fb, Groups.group_add(w, fb, t))) ->
  NV.InGroupsFb(w, fb,
    Feedback.Bool.case(+List<Groups.Group>, b,
      Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])} <> t,
      Groups.Group{f, ws} <> Groups.group_add(w, fb, t))):
  match b:
    case True{}:
      Inl{(Grp.Grp.in_words_snoc(w, ws),
           Equal.sym(Bool, b, Feedback.feedback_eq(fb, f), eb))}
    case False{}:
      Inr{k(Unit{})}

def NV.group_add_contains_fb(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +gs: +List<Groups.Group>) ->
  NV.InGroupsFb(w, fb, Groups.group_add(w, fb, gs)):
  match gs:
    case Nil{}:
      Inl{(Inl{{==}}, Fb.FbPrf.feedback_eq_refl(fb))}
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          NV.group_add_contains_fb_go(w, fb, f, ws, t,
            Feedback.feedback_eq(fb, f), {==},
            u => NV.group_add_contains_fb(w, fb, t))

# Feedback absence contradicts membership with that feedback.
def NV.not_fb_absurd(+fb: +List<Feedback.Color>, +gs: +List<Groups.Group>,
    +w: +List<Nat>, nf: GD.GD.NotFb(fb, gs),
    p: NV.InGroupsFb(w, fb, gs)) -> Empty:
  match gs:
    case Nil{}:
      match p:
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          (h, tl) = nf
          match p:
            case Inl{pin}:
              (iw, e) = pin
              +ef : {Feedback.feedback_eq(fb, f) == False{} : Bool} = h
              +et : {Feedback.feedback_eq(fb, f) == True{} : Bool} = e
              Logic.Proof.true_ne_false(
                Equal.trans(Bool, True{}, Feedback.feedback_eq(fb, f), False{},
                  Equal.sym(Bool, Feedback.feedback_eq(fb, f), True{}, et), ef))
            case Inr{pt}:
              NV.not_fb_absurd(fb, t, w, tl, pt)

# The head group of a distinct list is the only group with its feedback.
def NV.in_groups_fb_head(+fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +t: +List<Groups.Group>, +w: +List<Nat>,
    d: GD.GD.Distinct(Groups.Group{fb, ws} <> t),
    p: NV.InGroupsFb(w, fb, Groups.Group{fb, ws} <> t)) ->
  Grp.Grp.InWords(w, ws):
  match p:
    case Inl{pin}:
      (iw, e) = pin
      iw
    case Inr{pt}:
      Empty.absurd(Grp.Grp.InWords(w, ws),
        NV.not_fb_absurd(fb, t, w, GD.GD.distinct_head(fb, ws, t, d), pt))


# Transport the feedback of a group along a word equality. One rewrite moves
# both the word and the feedback it produced.
def NV.in_groups_fb_map(+w: +List<Nat>, +w0: +List<Nat>, +g: +List<Nat>,
    +acc: +List<Groups.Group>, e: {w0 == w : +List<Nat>},
    p: NV.InGroupsFb(w0, Feedback.feedback(g, w0), acc)) ->
  NV.InGroupsFb(w, Feedback.feedback(g, w), acc):
  %e :
    NV.InGroupsFb(_, Feedback.feedback(g, _), acc)
  p

def NV.fb_transport(+w: +List<Nat>, +w0: +List<Nat>, +g: +List<Nat>,
    +acc: +List<Groups.Group>, e: {w == w0 : +List<Nat>},
    +ne : {Feedback.word_eq(g, w) == False{} : Bool},
    p: NV.InGroupsFb(w0, Feedback.feedback(g, w0), acc)) ->
  NV.InGroupsFb(w, Feedback.feedback(g, w), acc):
  NV.in_groups_fb_map(w, w0, g, acc, Equal.sym(+List<Nat>, w, w0, e), p)

# Adding a group keeps membership of an earlier feedback.
def NV.in_groups_fb_weaken_go(+w0: +List<Nat>, +fb0: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, +ws: +List<+List<Nat>>, +t: +List<Groups.Group>,
    +w: +List<Nat>, +fb: +List<Feedback.Color>, b: Bool,
    +eb: {b == Feedback.feedback_eq(fb0, f) : Bool},
    p: NV.InGroupsFb(w, fb, Groups.Group{f, ws} <> t),
    k: NV.InGroupsFb(w, fb, t) -> NV.InGroupsFb(w, fb, Groups.group_add(w0, fb0, t))) ->
  NV.InGroupsFb(w, fb,
    Feedback.Bool.case(+List<Groups.Group>, b,
      Groups.Group{f, List.append(&2, +List<Nat>, ws, [w0])} <> t,
      Groups.Group{f, ws} <> Groups.group_add(w0, fb0, t))):
  match b:
    case True{}:
      match p:
        case Inl{pin}:
          (iw, efb) = pin
          Inl{(Grp.Grp.in_words_append_l(w, ws, [w0], iw), efb)}
        case Inr{pt}:
          Inr{pt}
    case False{}:
      match p:
        case Inl{pin}:
          Inl{pin}
        case Inr{pt}:
          Inr{k(pt)}

def NV.in_groups_fb_weaken(+w0: +List<Nat>, +fb0: +List<Feedback.Color>,
    +gs: +List<Groups.Group>, +w: +List<Nat>, +fb: +List<Feedback.Color>,
    p: NV.InGroupsFb(w, fb, gs)) ->
  NV.InGroupsFb(w, fb, Groups.group_add(w0, fb0, gs)):
  match gs:
    case Nil{}:
      match p:
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          NV.in_groups_fb_weaken_go(w0, fb0, f, ws, t, w, fb,
            Feedback.feedback_eq(fb0, f), {==}, p,
            pt => NV.in_groups_fb_weaken(w0, fb0, t, w, fb, pt))

# Membership is preserved when the groups are built.
def NV.groups_build_extends_fb_go(+g: +List<Nat>, +w0: +List<Nat>,
    +t: +List<+List<Nat>>, +acc: +List<Groups.Group>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, b: Bool,
    +eb: {b == Feedback.word_eq(g, w0) : Bool},
    p: NV.InGroupsFb(w, fb, acc),
    k: @a: +List<Groups.Group> -> NV.InGroupsFb(w, fb, a)
       -> NV.InGroupsFb(w, fb, Groups.groups_build(g, t, a))) ->
  NV.InGroupsFb(w, fb,
    Feedback.Bool.case(+List<Groups.Group>, b,
      Groups.groups_build(g, t, acc),
      Groups.groups_build(g, t,
        Groups.group_add(w0, Feedback.feedback(g, w0), acc)))):
  match b:
    case True{}:
      k(acc, p)
    case False{}:
      k(Groups.group_add(w0, Feedback.feedback(g, w0), acc),
        NV.in_groups_fb_weaken(w0, Feedback.feedback(g, w0), acc, w, fb, p))

def NV.groups_build_extends_fb(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +acc: +List<Groups.Group>, +w: +List<Nat>, +fb: +List<Feedback.Color>,
    p: NV.InGroupsFb(w, fb, acc)) ->
  NV.InGroupsFb(w, fb, Groups.groups_build(g, S, acc)):
  match S:
    case Nil{}:
      p
    case Con{w0, t}:
      NV.groups_build_extends_fb_go(g, w0, t, acc, w, fb,
        Feedback.word_eq(g, w0), {==}, p,
        a => p2 => NV.groups_build_extends_fb(g, t, a, w, fb, p2))

# Every non-guess candidate is in a group with its own feedback.
def NV.groups_build_contains_fb_branch(+g: +List<Nat>, +rest: +List<+List<Nat>>,
    +w0: +List<Nat>, +w: +List<Nat>, b: Bool,
    +eb: {b == Feedback.word_eq(g, w0) : Bool},
    +ne : {Feedback.word_eq(g, w) == False{} : Bool},
    +e : {w == w0 : +List<Nat>},
    +acc: +List<Groups.Group>) ->
  NV.InGroupsFb(w, Feedback.feedback(g, w),
    Feedback.Bool.case(+List<Groups.Group>, b,
      Groups.groups_build(g, rest, acc),
      Groups.groups_build(g, rest,
        Groups.group_add(w0, Feedback.feedback(g, w0), acc)))):
  match b:
    case True{}:
      +trueq : {True{} == Feedback.word_eq(g, w0) : Bool} = eb
      Empty.absurd(NV.InGroupsFb(w, Feedback.feedback(g, w),
        Groups.groups_build(g, rest, acc)),
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, Feedback.word_eq(g, w0), False{},
            trueq,
            Equal.trans(Bool, Feedback.word_eq(g, w0), Feedback.word_eq(g, w), False{},
              Grp.Grp.word_eq_eq_r(g, w0, w, Equal.sym(+List<Nat>, w, w0, e)), ne))))
    case False{}:
      NV.groups_build_extends_fb(g, rest,
        Groups.group_add(w0, Feedback.feedback(g, w0), acc), w,
        Feedback.feedback(g, w),
        NV.fb_transport(w, w0, g,
          Groups.group_add(w0, Feedback.feedback(g, w0), acc), e, ne,
          NV.group_add_contains_fb(w0, Feedback.feedback(g, w0), acc)))


def NV.groups_build_contains_fb_rest_go(+g: +List<Nat>, +t: +List<+List<Nat>>,
    +w0: +List<Nat>, +w: +List<Nat>, b: Bool,
    +eb: {b == Feedback.word_eq(g, w0) : Bool},
    +acc: +List<Groups.Group>,
    k: @a: +List<Groups.Group> ->
       NV.InGroupsFb(w, Feedback.feedback(g, w), Groups.groups_build(g, t, a))) ->
  NV.InGroupsFb(w, Feedback.feedback(g, w),
    Feedback.Bool.case(+List<Groups.Group>, b,
      Groups.groups_build(g, t, acc),
      Groups.groups_build(g, t,
        Groups.group_add(w0, Feedback.feedback(g, w0), acc)))):
  match b:
    case True{}:
      k(acc)
    case False{}:
      k(Groups.group_add(w0, Feedback.feedback(g, w0), acc))

def NV.groups_build_contains_fb(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +w: +List<Nat>, m: Grp.Grp.InWords(w, S),
    +ne : {Feedback.word_eq(g, w) == False{} : Bool}) ->
  @acc: +List<Groups.Group> ->
    NV.InGroupsFb(w, Feedback.feedback(g, w), Groups.groups_build(g, S, acc)):
  match S:
    case Nil{}:
      Empty.absurd(@acc: +List<Groups.Group> ->
        NV.InGroupsFb(w, Feedback.feedback(g, w), Groups.groups_build(g, Nil{}, acc)), m)
    case Con{w0, t}:
      match m:
        case Inl{e}:
          acc => NV.groups_build_contains_fb_branch(g, t, w0, w,
            Feedback.word_eq(g, w0), {==}, ne, e, acc)
        case Inr{mt}:
          acc => NV.groups_build_contains_fb_rest_go(g, t, w0, w,
            Feedback.word_eq(g, w0), {==}, acc,
            a => NV.groups_build_contains_fb(g, t, w, mt, ne, a))

# The tree of one group's child search.
def NV.kid_tree(+p: Nat, +G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +inf: Nat) -> Tree.Tree:
  Eval.Eval.tree_of(SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
    Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()))

def NV.ChildrenValid(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +groups: +List<Groups.Group>, +inf: Nat) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          Tree.Valid(NV.kid_tree(p, G, ws, inf), G, ws)
          & NV.ChildrenValid(p, G, S, rest, inf)

# A feedback different from a group feedback is also false in the other order.
def NV.fb_true_sym(+a: +List<Feedback.Color>, +b: +List<Feedback.Color>,
    e: {Feedback.feedback_eq(a, b) == True{} : Bool}) ->
  {Feedback.feedback_eq(b, a) == True{} : Bool}:
  Fb.FeedbackProof.feedback_eq_sym(a, b, e)

# The head child of `depth.go` is the child's depth when its feedback matches.
def NV.depth_go_head_go(+a: +List<Nat>, +fb: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, child: Tree.Tree, +rest: +List<Tree.Child>, b: Bool,
    +eb: {b == Feedback.feedback_eq(f, fb) : Bool},
    +e: {Feedback.feedback_eq(f, fb) == True{} : Bool}) ->
  {Feedback.Bool.case(Maybe<Nat>, b,
      Tree.depth(child, a), Tree.depth.go(rest, fb, a))
   == Tree.depth(child, a) : Maybe<Nat>}:
  match child:
    case Tree.Node{g, kids}:
      match b:
        case True{}:
          {==}
        case False{}:
          Empty.absurd(
            {Feedback.Bool.case(Maybe<Nat>, False{}, Tree.depth(Tree.Node{g, kids}, a),
                Tree.depth.go(rest, fb, a))
             == Tree.depth(Tree.Node{g, kids}, a) : Maybe<Nat>},
            Logic.Proof.false_ne_true(
              Equal.trans(Bool, False{}, Feedback.feedback_eq(f, fb), True{},
                eb, e)))

def NV.depth_go_head(+a: +List<Nat>, +fb: +List<Feedback.Color>,
    child: Tree.Tree, +rest: +List<Tree.Child>) ->
  {Tree.depth.go(Tree.Child{fb, child} <> rest, fb, a) == Tree.depth(child, a)
   : Maybe<Nat>}:
  match child:
    case Tree.Node{g, kids}:
      NV.depth_go_head_go(a, fb, fb, Tree.Node{g, kids}, rest,
        Feedback.feedback_eq(fb, fb), {==}, Fb.FbPrf.feedback_eq_refl(fb))

def NV.depth_go_head_at(+a: +List<Nat>, +fb: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, child: Tree.Tree, +rest: +List<Tree.Child>,
    +e: {Feedback.feedback_eq(f, fb) == True{} : Bool}) ->
  {Tree.depth.go(Tree.Child{f, child} <> rest, fb, a) == Tree.depth(child, a)
   : Maybe<Nat>}:
  match child:
    case Tree.Node{g, kids}:
      NV.depth_go_head_go(a, fb, f, Tree.Node{g, kids}, rest,
        Feedback.feedback_eq(f, fb), {==}, e)

# A non-matching head is skipped.
def NV.depth_go_skip_go(+a: +List<Nat>, +fb: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, child: Tree.Tree, +rest: +List<Tree.Child>, b: Bool,
    +eb: {b == Feedback.feedback_eq(f, fb) : Bool},
    +e: {Feedback.feedback_eq(f, fb) == False{} : Bool}) ->
  {Feedback.Bool.case(Maybe<Nat>, b,
      Tree.depth(child, a), Tree.depth.go(rest, fb, a))
   == Tree.depth.go(rest, fb, a) : Maybe<Nat>}:
  match child:
    case Tree.Node{g, kids}:
      match b:
        case True{}:
          Empty.absurd(
            {Feedback.Bool.case(Maybe<Nat>, True{}, Tree.depth(Tree.Node{g, kids}, a),
                Tree.depth.go(rest, fb, a))
             == Tree.depth.go(rest, fb, a) : Maybe<Nat>},
            Logic.Proof.false_ne_true(
              Equal.trans(Bool, False{}, Feedback.feedback_eq(f, fb), True{},
                Equal.sym(Bool, Feedback.feedback_eq(f, fb), False{}, e),
                Equal.sym(Bool, True{}, Feedback.feedback_eq(f, fb), eb))))
        case False{}:
          {==}

def NV.depth_go_skip(+a: +List<Nat>, +fb: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, child: Tree.Tree, +rest: +List<Tree.Child>,
    +e: {Feedback.feedback_eq(f, fb) == False{} : Bool}) ->
  {Tree.depth.go(Tree.Child{f, child} <> rest, fb, a)
   == Tree.depth.go(rest, fb, a) : Maybe<Nat>}:
  match child:
    case Tree.Node{g, kids}:
      NV.depth_go_skip_go(a, fb, f, Tree.Node{g, kids}, rest,
        Feedback.feedback_eq(f, fb), {==}, e)

# From membership with feedback fb and absence of another feedback, extract the
# false comparison of the two.
def NV.not_fb_value(+f: +List<Feedback.Color>, +fb: +List<Feedback.Color>,
    +gs: +List<Groups.Group>, +w: +List<Nat>,
    nf: GD.GD.NotFb(f, gs), p: NV.InGroupsFb(w, fb, gs)) ->
  {Feedback.feedback_eq(f, fb) == False{} : Bool}:
  match gs:
    case Nil{}:
      match p:
    case Con{gp, t}:
      match gp:
        case Groups.Group{f2, ws}:
          (h, tl) = nf
          match p:
            case Inl{pin}:
              (iw, e) = pin
              Equal.trans(Bool, Feedback.feedback_eq(f, fb),
                Feedback.feedback_eq(f, f2), False{},
                Equal.cong(+List<Feedback.Color>, Bool,
                  x => Feedback.feedback_eq(f, x), fb, f2,
                  Fb.FbPrf.feedback_eq_true(fb, f2, e)), h)
            case Inr{pt}:
              NV.not_fb_value(f, fb, t, w, tl, pt)
