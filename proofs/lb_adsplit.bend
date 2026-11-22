# Lower bounds for valid trees, part 7: validity splits over a class filter.
#
# The capacity bound recurses into the classes of a node's guess, and the child
# of a class must be a valid tree for the class words. The first step of that
# argument is this module: the depth facts of a candidate list split over the
# two filters of a child, so a node's depth information can be handed down class
# by class.
#
# `AllHaveDepth(t, S)` is a conjunction over the words of `S`, so splitting it
# takes one traversal over `S`, with the child's keep test as a parameter. The
# two halves then belong to the words the child keeps and to the words it passes
# on, which is what `classes` and `rem` consume.
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./lb_classes.bend as Part

# Transport the depth facts along an equality of candidate lists.
def LB.ad_eq(+t: Tree.Tree, +S1: +List<+List<Nat>>, +S2: +List<+List<Nat>>,
    e: {S1 == S2 : +List<+List<Nat>>}, p: Tree.AllHaveDepth(t, S1)) ->
  Tree.AllHaveDepth(t, S2):
  %e : Tree.AllHaveDepth(t, _)
  p

# The kept branch: the word stays with the kept words.
def LB.ad_true2(+t: Tree.Tree, +g: +List<Nat>, +f: +List<Feedback.Color>,
    +h: +List<Nat>, +tl: +List<+List<Nat>>,
    +eb: {True{} == Part.LB.keep(g, f, h) : Bool},
    sh: {Maybe.is_some(&1, Nat, Tree.depth(t, h)) == True{} : Bool},
    ih: Tree.AllHaveDepth(t, Part.LB.keepw_b(g, f, tl))
        & Tree.AllHaveDepth(t, Part.LB.remw(g, f, tl))) ->
  Tree.AllHaveDepth(t, Part.LB.keepw_b(g, f, h <> tl))
  & Tree.AllHaveDepth(t, Part.LB.remw(g, f, h <> tl)):
  (kh, kr) = ih
  +ek : {Part.LB.keepw_b(g, f, h <> tl) == h <> Part.LB.keepw_b(g, f, tl)
         : +List<+List<Nat>>} =
    Part.LB.keepw_eq(g, f, h, tl, True{}, eb)
  +er : {Part.LB.remw(g, f, h <> tl) == Part.LB.remw(g, f, tl) : +List<+List<Nat>>} =
    Part.LB.remw_eq(g, f, h, tl, True{}, eb)
  (LB.ad_eq(t, h <> Part.LB.keepw_b(g, f, tl), Part.LB.keepw_b(g, f, h <> tl),
     Equal.sym(+List<+List<Nat>>, Part.LB.keepw_b(g, f, h <> tl),
       h <> Part.LB.keepw_b(g, f, tl), ek), (sh, kh)),
   LB.ad_eq(t, Part.LB.remw(g, f, tl), Part.LB.remw(g, f, h <> tl),
     Equal.sym(+List<+List<Nat>>, Part.LB.remw(g, f, h <> tl),
       Part.LB.remw(g, f, tl), er), kr))

# The dropped branch: the word goes on to the later children.
def LB.ad_false2(+t: Tree.Tree, +g: +List<Nat>, +f: +List<Feedback.Color>,
    +h: +List<Nat>, +tl: +List<+List<Nat>>,
    +eb: {False{} == Part.LB.keep(g, f, h) : Bool},
    sh: {Maybe.is_some(&1, Nat, Tree.depth(t, h)) == True{} : Bool},
    ih: Tree.AllHaveDepth(t, Part.LB.keepw_b(g, f, tl))
        & Tree.AllHaveDepth(t, Part.LB.remw(g, f, tl))) ->
  Tree.AllHaveDepth(t, Part.LB.keepw_b(g, f, h <> tl))
  & Tree.AllHaveDepth(t, Part.LB.remw(g, f, h <> tl)):
  (kh, kr) = ih
  +ek : {Part.LB.keepw_b(g, f, h <> tl) == Part.LB.keepw_b(g, f, tl)
         : +List<+List<Nat>>} =
    Part.LB.keepw_eq(g, f, h, tl, False{}, eb)
  +er : {Part.LB.remw(g, f, h <> tl) == h <> Part.LB.remw(g, f, tl)
         : +List<+List<Nat>>} =
    Part.LB.remw_eq(g, f, h, tl, False{}, eb)
  (LB.ad_eq(t, Part.LB.keepw_b(g, f, tl), Part.LB.keepw_b(g, f, h <> tl),
     Equal.sym(+List<+List<Nat>>, Part.LB.keepw_b(g, f, h <> tl),
       Part.LB.keepw_b(g, f, tl), ek), kh),
   LB.ad_eq(t, h <> Part.LB.remw(g, f, tl), Part.LB.remw(g, f, h <> tl),
     Equal.sym(+List<+List<Nat>>, Part.LB.remw(g, f, h <> tl),
       h <> Part.LB.remw(g, f, tl), er), (sh, kr)))

# The split, with the keep test as a parameter.
def LB.ad_split_go(+t: Tree.Tree, +g: +List<Nat>, +f: +List<Feedback.Color>,
    +h: +List<Nat>, +tl: +List<+List<Nat>>, +b: Bool,
    +eb: {b == Part.LB.keep(g, f, h) : Bool},
    ih: Tree.AllHaveDepth(t, Part.LB.keepw_b(g, f, tl))
        & Tree.AllHaveDepth(t, Part.LB.remw(g, f, tl)),
    sh: {Maybe.is_some(&1, Nat, Tree.depth(t, h)) == True{} : Bool}) ->
  Tree.AllHaveDepth(t, Part.LB.keepw_b(g, f, h <> tl))
  & Tree.AllHaveDepth(t, Part.LB.remw(g, f, h <> tl)):
  match b:
    case True{}:
      LB.ad_true2(t, g, f, h, tl, eb, sh, ih)
    case False{}:
      LB.ad_false2(t, g, f, h, tl, eb, sh, ih)

# The depth facts split over the two filters of a child.
def LB.ad_split(+t: Tree.Tree, +g: +List<Nat>, +f: +List<Feedback.Color>,
    +S: +List<+List<Nat>>, ad: Tree.AllHaveDepth(t, S)) ->
  Tree.AllHaveDepth(t, Part.LB.keepw_b(g, f, S))
  & Tree.AllHaveDepth(t, Part.LB.remw(g, f, S)):
  match S:
    case Nil{}:
      (Unit{}, Unit{})
    case Con{h, tl}:
      (sh, st) = ad
      LB.ad_split_go(t, g, f, h, tl, Part.LB.keep(g, f, h), {==},
        LB.ad_split(t, g, f, tl, st), sh)
