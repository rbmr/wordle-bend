# The decision tree and its properties.
#
# A Tree node holds the guess and one Child per distinct feedback pattern. A
# Child pairs a feedback with the subtree to use after that feedback.
import Base
import ./feedback.bend as Feedback

type Tree is Data:
  Node{guess: +List<Nat>, kids: +List<Child>}

type Child is Data:
  Child{feedback: +List<Feedback.Color>, tree: Tree}

# The first child whose feedback matches fb.
def lookup(+fb: +List<Feedback.Color>, +kids: +List<Child>) -> Maybe<Tree>:
  match kids:
    case Nil{}:
      None{}
    case Con{c, rest}:
      match c:
        case Child{f, child}:
          Feedback.Bool.case(Maybe<Tree>, Feedback.feedback_eq(fb, f), Some{child}, lookup(fb, rest))

# The number of guesses needed to reach a, following the tree. None when the
# feedback from a node's guess is not one of its children. depth.go walks the
# children of one node; its first argument is the list being searched, so the
# structural termination check accepts the descent into a child.
def depth.bump(d: Maybe<Nat>) -> Maybe<Nat>:
  match d:
    case None{}:
      None{}
    case Some{n}:
      Some{1n+n}

def depth.go(kids: +List<Child>, +fb: +List<Feedback.Color>, +a: +List<Nat>) -> Maybe<Nat>:
  match kids:
    case Nil{}:
      None{}
    case Con{c, rest}:
      match c:
        case Child{f, child}:
          match child:
            case Node{+g, ckids}:
              Feedback.Bool.case(Maybe<Nat>, Feedback.feedback_eq(f, fb),
                                 Feedback.Bool.case(Maybe<Nat>, Feedback.word_eq(g, a),
                                                    Some{1n},
                                                    depth.bump(depth.go(ckids, Feedback.feedback(g, a), a))),
                                 depth.go(rest, fb, a))

def depth(t: Tree, +a: +List<Nat>) -> Maybe<Nat>:
  match t:
    case Node{+g, kids}:
      Feedback.Bool.case(Maybe<Nat>, Feedback.word_eq(g, a),
                         Some{1n},
                         depth.bump(depth.go(kids, Feedback.feedback(g, a), a)))

# The total number of guesses over all candidates, with duplicates counted. On
# a valid tree every depth is Some; elsewhere a missing depth counts as zero.
def cost(+t: Tree, +c: +List<+List<Nat>>) -> Nat:
  match c:
    case Nil{}:
      0n
    case Con{h, tail}:
      d = Maybe.default(&1, Nat, depth(t, h), 0n)
      Nat.add(d, cost(t, tail))

def member_word(+w: +List<Nat>, +guesses: +List<+List<Nat>>) -> Bool:
  match guesses:
    case Nil{}:
      False{}
    case Con{+h, +t}:
      Feedback.Bool.case(Bool, Feedback.word_eq(w, h), True{}, member_word(w, t))

def WordIn(w: +List<Nat>, guesses: +List<+List<Nat>>) -> Type:
  {member_word(w, guesses) == True{} : Bool}

# Every node's guess is in the guesses list.
def TreeIn(t: Tree, guesses: +List<+List<Nat>>) -> Type:
  match t:
    case Node{+g, kids}:
      WordIn(g, guesses) & KidsIn(kids, guesses)

def KidsIn(kids: +List<Child>, guesses: +List<+List<Nat>>) -> Type:
  match kids:
    case Nil{}:
      Unit
    case Con{c, rest}:
      match c:
        case Child{f, child}:
          TreeIn(child, guesses) & KidsIn(rest, guesses)

# Every candidate has a Some depth in the tree.
def AllHaveDepth(t: Tree, candidates: +List<+List<Nat>>) -> Type:
  match candidates:
    case Nil{}:
      Unit
    case Con{h, tail}:
      {Maybe.is_some(&1, Nat, depth(t, h)) == True{} : Bool} & AllHaveDepth(t, tail)

def Valid(t: Tree, guesses: +List<+List<Nat>>, candidates: +List<+List<Nat>>) -> Type:
  TreeIn(t, guesses) & AllHaveDepth(t, candidates)
