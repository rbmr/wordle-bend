# The child a group's feedback looks up, and the facts that make it valid.
#
# A group built by `groups_build` carries, for each of its words, the word test,
# the feedback test and the node depth. This module turns those facts into the
# validity of the looked-up child, without using the lookup equation more than
# once: everything is stated about the `Maybe` result first, then transported.
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ../src/groups.bend as Groups
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./depth.bend as DepthProof
import ./groups.bend as Grp
import ./nodecost.bend as NodeCost

# Membership of a tree in a child list, by the child constructor.
def KidsProof.ChildMem(t: Tree.Tree, +kids: +List<Tree.Child>) -> Type:
  match kids:
    case Nil{}:
      Empty
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          {t == child : Tree.Tree} | KidsProof.ChildMem(t, rest)

# The value of a `Some`, with an arbitrary default for `None`.
def KidsProof.maybe_val(m: Maybe<Tree.Tree>) -> Tree.Tree:
  match m:
    case None{}:
      Tree.Node{Nil{}, Nil{}}
    case Some{t}:
      t

def KidsProof.some_inj(x: Tree.Tree, y: Tree.Tree,
    e: {Some{x} == Some{y} : Maybe<Tree.Tree>}) -> {x == y : Tree.Tree}:
  Equal.cong(Maybe<Tree.Tree>, Tree.Tree, KidsProof.maybe_val, Some{x}, Some{y}, e)

def KidsProof.maybe_disc(m: Maybe<Tree.Tree>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{t}:
      Empty

def KidsProof.none_ne_some(t: Tree.Tree,
    e: {None{} == Some{t} : Maybe<Tree.Tree>}) -> Empty:
  %e : KidsProof.maybe_disc(_)
  Unit{}

# Branch of `lookup_mem` at a child, split on the feedback test.
def KidsProof.lookup_mem_cons(+fb: +List<Feedback.Color>, +rest: +List<Tree.Child>,
    +f: +List<Feedback.Color>, +child: Tree.Tree, +t: Tree.Tree, b: Bool,
    +eb: {b == Feedback.feedback_eq(fb, f) : Bool},
    e: {Feedback.Bool.case(Maybe<Tree.Tree>, b, Some{child}, Tree.lookup(fb, rest))
        == Some{t} : Maybe<Tree.Tree>},
    k: @x: Tree.Tree -> {Tree.lookup(fb, rest) == Some{x} : Maybe<Tree.Tree>}
       -> KidsProof.ChildMem(x, rest)) ->
  KidsProof.ChildMem(t, Tree.Child{f, child} <> rest):
  match b:
    case True{}:
      e2 : {child == t : Tree.Tree} = KidsProof.some_inj(child, t, e)
      Inl{Equal.sym(Tree.Tree, child, t, e2)}
    case False{}:
      Inr{k(t, e)}

# The tree a successful lookup finds is a member of the child list.
def KidsProof.lookup_mem(+fb: +List<Feedback.Color>, +kids: +List<Tree.Child>,
    +t: Tree.Tree, e: {Tree.lookup(fb, kids) == Some{t} : Maybe<Tree.Tree>}) ->
  KidsProof.ChildMem(t, kids):
  match kids:
    case Nil{}:
      Empty.absurd(KidsProof.ChildMem(t, Nil{}), KidsProof.none_ne_some(t, e))
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          KidsProof.lookup_mem_cons(fb, rest, f, child, t, Feedback.feedback_eq(fb, f),
            {==}, e, x => ex => KidsProof.lookup_mem(fb, rest, x, ex))

# Membership in the child list gives the node's tree-in-guesses property.
def KidsProof.kids_in_member(+kids: +List<Tree.Child>, +G: +List<+List<Nat>>,
    ci: Tree.KidsIn(kids, G), +t: Tree.Tree, mem: KidsProof.ChildMem(t, kids)) ->
  Tree.TreeIn(t, G):
  match kids:
    case Nil{}:
      Empty.absurd(Tree.TreeIn(t, G), mem)
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          (ti, ki) = ci
          match mem:
            case Inl{e}:
              %Equal.sym(Tree.Tree, t, child, e) : Tree.TreeIn(_, G)
              ti
            case Inr{m}:
              KidsProof.kids_in_member(rest, G, ki, t, m)

# A depth in a member word exists.
def KidsProof.all_have_depth_mem(+t: Tree.Tree, +ws: +List<+List<Nat>>,
    d: Tree.AllHaveDepth(t, ws), +w: +List<Nat>, m: Grp.Grp.InWords(w, ws)) ->
  {Maybe.is_some(&1, Nat, Tree.depth(t, w)) == True{} : Bool}:
  match ws:
    case Nil{}:
      Empty.absurd({Maybe.is_some(&1, Nat, Tree.depth(t, w)) == True{} : Bool}, m)
    case Con{h, tl}:
      (dh, dt) = d
      match m:
        case Inl{e}:
          %Equal.sym(+List<Nat>, w, h, e) : {Maybe.is_some(&1, Nat, Tree.depth(t, _)) == True{} : Bool}
          dh
        case Inr{m2}:
          KidsProof.all_have_depth_mem(t, tl, dt, w, m2)

def KidsProof.some_of_bump(m: Maybe<Nat>,
    s: {Maybe.is_some(&1, Nat, Tree.depth.bump(m)) == True{} : Bool}) ->
  {Maybe.is_some(&1, Nat, m) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Maybe.is_some(&1, Nat, None{}) == True{} : Bool},
                   Logic.Proof.false_ne_true(s))
    case Some{n}:
      {==}

# Every word in a class has a looked-up depth in the class's `Maybe` result.
def KidsProof.KidEvery(m: Maybe<Tree.Tree>, +ws: +List<+List<Nat>>) -> Type:
  match ws:
    case Nil{}:
      Unit
    case Con{h, t}:
      {Maybe.is_some(&1, Nat, DepthProof.DepthProof.lookup_depth(m, h)) == True{} : Bool}
      & KidsProof.KidEvery(m, t)

# From per-word looked-up depths, the `Some` child is valid for the class.
def KidsProof.kid_every_depth(+child: Tree.Tree, +ws: +List<+List<Nat>>,
    every: KidsProof.KidEvery(Some{child}, ws)) -> Tree.AllHaveDepth(child, ws):
  match ws:
    case Nil{}:
      Unit{}
    case Con{h, t}:
      (eh, et) = every
      e_step : {DepthProof.DepthProof.lookup_depth(Some{child}, h) == Tree.depth(child, h)
                : Maybe<Nat>} =
        NodeCost.NodeCost.step_is_depth(child, h)
      e_is : {Maybe.is_some(&1, Nat, DepthProof.DepthProof.lookup_depth(Some{child}, h))
              == Maybe.is_some(&1, Nat, Tree.depth(child, h)) : Bool} =
        Equal.cong(Maybe<Nat>, Bool,
                   x => Maybe.is_some(&1, Nat, x),
                   DepthProof.DepthProof.lookup_depth(Some{child}, h),
                   Tree.depth(child, h), e_step)
      eh2 : {Maybe.is_some(&1, Nat, Tree.depth(child, h)) == True{} : Bool} =
        Equal.trans(Bool, Maybe.is_some(&1, Nat, Tree.depth(child, h)),
                    Maybe.is_some(&1, Nat, DepthProof.DepthProof.lookup_depth(Some{child}, h)),
                    True{}, Equal.sym(Bool,
                      Maybe.is_some(&1, Nat, DepthProof.DepthProof.lookup_depth(Some{child}, h)),
                      Maybe.is_some(&1, Nat, Tree.depth(child, h)), e_is), eh)
      (eh2, KidsProof.kid_every_depth(child, t, et))

# The per-word facts of a group give the looked-up depths of its class.
def KidsProof.words_kid_every(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    gd: Grp.Grp.WordsDepths(g, kids, fb, ws)) ->
  KidsProof.KidEvery(Tree.lookup(fb, kids), ws):
  match ws:
    case Nil{}:
      Unit{}
    case Con{w, t}:
      ((pne, pfb, pd), pt) = gd
      e_nat : {Tree.depth(Tree.Node{g, kids}, w)
               == Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))
               : Maybe<Nat>} =
        Equal.cong(Bool, Maybe<Nat>,
          x => Feedback.Bool.case(Maybe<Nat>, x, Some{1n},
                 Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))),
          Feedback.word_eq(g, w), False{}, pne)
      e_fb : {Feedback.feedback(g, w) == fb : +List<Feedback.Color>} =
        FbProof.FbPrf.feedback_eq_true(Feedback.feedback(g, w), fb, pfb)
      e_go : {Tree.depth.go(kids, Feedback.feedback(g, w), w) == Tree.depth.go(kids, fb, w)
              : Maybe<Nat>} =
        Equal.cong(+List<Feedback.Color>, Maybe<Nat>,
                   x => Tree.depth.go(kids, x, w), Feedback.feedback(g, w), fb, e_fb)
      e_bump_go : {Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))
                   == Tree.depth.bump(Tree.depth.go(kids, fb, w)) : Maybe<Nat>} =
        Equal.cong(Maybe<Nat>, Maybe<Nat>, x => Tree.depth.bump(x),
                   Tree.depth.go(kids, Feedback.feedback(g, w), w),
                   Tree.depth.go(kids, fb, w), e_go)
      e_lookup : {Tree.depth.bump(Tree.depth.go(kids, fb, w))
                  == Tree.depth.bump(DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w))
                  : Maybe<Nat>} =
        Equal.cong(Maybe<Nat>, Maybe<Nat>, x => Tree.depth.bump(x),
                   Tree.depth.go(kids, fb, w),
                   DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w),
                   DepthProof.DepthProof.depth_go_lookup(kids, fb, w))
      e_all : {Tree.depth(Tree.Node{g, kids}, w)
               == Tree.depth.bump(DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w))
               : Maybe<Nat>} =
        Equal.trans(Maybe<Nat>, Tree.depth(Tree.Node{g, kids}, w),
                    Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)),
                    Tree.depth.bump(DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w)),
                    e_nat,
                    Equal.trans(Maybe<Nat>,
                      Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)),
                      Tree.depth.bump(Tree.depth.go(kids, fb, w)),
                      Tree.depth.bump(DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w)),
                      e_bump_go, e_lookup))
      e_is : {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w))
              == Maybe.is_some(&1, Nat, Tree.depth.bump(
                   DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w))) : Bool} =
        Equal.cong(Maybe<Nat>, Bool, x => Maybe.is_some(&1, Nat, x),
                   Tree.depth(Tree.Node{g, kids}, w),
                   Tree.depth.bump(DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w)),
                   e_all)
      e_bump : {Maybe.is_some(&1, Nat, Tree.depth.bump(
                  DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w))) == True{}
                : Bool} =
        Equal.trans(Bool, Maybe.is_some(&1, Nat, Tree.depth.bump(
                      DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w))),
                    Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)),
                    True{}, Equal.sym(Bool,
                      Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)),
                      Maybe.is_some(&1, Nat, Tree.depth.bump(
                        DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w))), e_is), pd)
      e_kid : {Maybe.is_some(&1, Nat,
                DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w)) == True{}
               : Bool} =
        KidsProof.some_of_bump(DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w), e_bump)
      (e_kid, KidsProof.words_kid_every(g, kids, fb, t, pt))
