# The feedback classes a guess splits a candidate list into.
#
# For a guess g, every candidate other than g belongs to the class of its
# feedback(g, .). A class records the feedback pattern and its candidates in the
# order they occur in the input. Both the solver and its proofs use this module.
import Base
import ./feedback.bend as Feedback

# One feedback class: the feedback pattern and the candidates that produce it,
# in the order they occur in S.
type Group is Data:
  Group{fb: +List<Feedback.Color>, words: +List<+List<Nat>>}

def len_words(+ws: +List<+List<Nat>>) -> Nat:
  List.length(&2, +List<Nat>, ws)

# Add a word to the first group with the same feedback, or append a new group.
def group_add(+w: +List<Nat>, +fb: +List<Feedback.Color>, +groups: +List<Group>) -> +List<Group>:
  match groups:
    case Nil{}:
      Group{fb, [w]} <> Nil{}
    case Con{gp, rest}:
      match gp:
        case Group{+f, +ws}:
          Feedback.Bool.case(+List<Group>, Feedback.feedback_eq(fb, f),
                              Group{f, List.append(&2, +List<Nat>, ws, [w])} <> rest,
                              Group{f, ws} <> group_add(w, fb, rest))

# Partition S into feedback classes for the guess g, dropping the candidates
# equal to g. The first occurrence of a feedback fixes the child order.
def groups_build(+g: +List<Nat>, +S: +List<+List<Nat>>, +acc: +List<Group>) -> +List<Group>:
  match S:
    case Nil{}:
      acc
    case Con{+w, +rest}:
      Feedback.Bool.case(+List<Group>, Feedback.word_eq(g, w),
                          groups_build(g, rest, acc),
                          groups_build(g, rest, group_add(w, Feedback.feedback(g, w), acc)))

# Every class must be strictly shorter than S (no-progress guesses are skipped).
def groups_smaller(+S: +List<+List<Nat>>, +groups: +List<Group>) -> Bool:
  match groups:
    case Nil{}:
      True{}
    case Con{gp, rest}:
      match gp:
        case Group{f, ws}:
          Bool.and(Nat.is_lt(len_words(ws), len_words(S)), groups_smaller(S, rest))
