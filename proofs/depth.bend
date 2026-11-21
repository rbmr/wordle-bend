# `lookup` and `depth.go` scan a child list the same way.
#
# `tree.depth` follows a feedback with `depth.go`, which tests the child's
# feedback against the requested one, while `tree.lookup` tests them in the
# opposite order. This module proves that the two scans find the same child,
# which is the bridge between `Valid` (defined with `depth`) and a tree built
# from per-class subtrees (selected with `lookup`).
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ./feedback.bend as FbProof
import ./logic.bend as Logic

# The depth contribution of the child that a lookup finds.
def DepthProof.step(+child: Tree.Tree, +a: +List<Nat>) -> Maybe<Nat>:
  match child:
    case Tree.Node{+g, kids}:
      Feedback.Bool.case(Maybe<Nat>, Feedback.word_eq(g, a),
                         Some{1n},
                         Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, a), a)))

def DepthProof.lookup_depth(m: Maybe<Tree.Tree>, +a: +List<Nat>) -> Maybe<Nat>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      DepthProof.step(t, a)

# Case split on the shared feedback test. The child is known to be a node here
# because the caller has already matched it.
def DepthProof.lookup_depth_bool(b: Bool, +child: Tree.Tree, +rest: +List<Tree.Child>,
    +fb: +List<Feedback.Color>, +a: +List<Nat>,
    +ih: {Tree.depth.go(rest, fb, a) == DepthProof.lookup_depth(Tree.lookup(fb, rest), a) : Maybe<Nat>}) ->
  {Feedback.Bool.case(Maybe<Nat>, b, DepthProof.step(child, a),
                      Tree.depth.go(rest, fb, a))
   == DepthProof.lookup_depth(
        Feedback.Bool.case(Maybe<Tree.Tree>, b, Some{child}, Tree.lookup(fb, rest)), a)
   : Maybe<Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def DepthProof.depth_go_lookup(+kids: +List<Tree.Child>, +fb: +List<Feedback.Color>,
    +a: +List<Nat>) ->
  {Tree.depth.go(kids, fb, a) == DepthProof.lookup_depth(Tree.lookup(fb, kids), a) : Maybe<Nat>}:
  match kids:
    case Nil{}:
      {==}
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          match child:
            case Tree.Node{+g, ckids}:
              +ih : {Tree.depth.go(rest, fb, a)
                     == DepthProof.lookup_depth(Tree.lookup(fb, rest), a) : Maybe<Nat>} =
                DepthProof.depth_go_lookup(rest, fb, a)
              +e_bool : {Feedback.feedback_eq(f, fb) == Feedback.feedback_eq(fb, f) : Bool} =
                FbProof.FeedbackProof.feedback_eq_sym_bool(f, fb)
              %e_bool : {
                Tree.depth.go(Tree.Child{f, Tree.Node{g, ckids}} <> rest, fb, a)
                == DepthProof.lookup_depth(
                     Feedback.Bool.case(Maybe<Tree.Tree>, _, Some{Tree.Node{g, ckids}},
                                        Tree.lookup(fb, rest)), a)
                : Maybe<Nat>}
              DepthProof.lookup_depth_bool(Feedback.feedback_eq(f, fb),
                Tree.Node{g, ckids}, rest, fb, a, ih)
