# Tree <-> JSON text.
#
# The encoding is arrays only:
#   tree     = [ guess, kids ]
#   guess    = [ letter, ... ]
#   kids     = [ child, ... ]
#   child    = [ feedback, tree ]
#   feedback = [ colour, ... ]
# A letter is a decimal Nat. A colour is 0 (Gray), 1 (Yellow), or 2 (Green).
import Base
import ./feedback.bend as Feedback
import ./tree.bend as Tree

def Color.code(c: Feedback.Color) -> String:
  match c:
    case Feedback.Gray{}:
      "0"
    case Feedback.Yellow{}:
      "1"
    case Feedback.Green{}:
      "2"

def join(parts: List<String>, +sep: String) -> String:
  match parts:
    case Nil{}:
      ""
    case Con{h, t}:
      match t:
        case Nil{}:
          h
        case Con{ht, tt}:
          h ++ sep ++ join(ht <> tt, sep)

def show_nats.tail(xs: +List<Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      "," ++ Nat.show(h) ++ show_nats.tail(t)

def show_nats(xs: +List<Nat>) -> String:
  match xs:
    case Nil{}:
      "[]"
    case Con{h, t}:
      "[" ++ Nat.show(h) ++ show_nats.tail(t) ++ "]"

def show_feedback.tail(xs: +List<Feedback.Color>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      "," ++ Color.code(h) ++ show_feedback.tail(t)

def show_feedback(xs: +List<Feedback.Color>) -> String:
  match xs:
    case Nil{}:
      "[]"
    case Con{h, t}:
      "[" ++ Color.code(h) ++ show_feedback.tail(t) ++ "]"

def show_forest(kids: +List<Tree.Child>, prefix: String) -> String:
  match kids:
    case Nil{}:
      ""
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          match child:
            case Tree.Node{g, ckids}:
              prefix ++ "[" ++ show_feedback(f) ++ ",[" ++ show_nats(g) ++ "," ++ show_forest(ckids, "") ++ "]]" ++ show_forest(rest, ",")

def print(t: Tree.Tree) -> String:
  match t:
    case Tree.Node{g, kids}:
      "[" ++ show_nats(g) ++ "," ++ show_forest(kids, "") ++ "]"

# The inverse parser is not implemented yet. It is the subject of law 6 in
# LAWS.bend, which is still open; until then parse rejects every input.
def parse(s: String) -> Maybe<Tree.Tree>:
  None{}
