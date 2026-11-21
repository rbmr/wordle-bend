# Tree <-> JSON text.
#
# The encoding is arrays only:
#   tree     = [ guess, kids ]
#   guess    = [ letter, ... ]
#   kids     = [ child, ... ]
#   child    = [ feedback, tree ]
#   feedback = [ colour, ... ]
# A colour is the decimal digit 0 (Gray), 1 (Yellow) or 2 (Green).
#
# A letter is a Nat written in unary as a JSON number: n ones then a zero.
# So 0 is "0", 1 is "10", 2 is "110", 3 is "1110". The trailing zero is part
# of the number and ends it, so the parser knows where a letter stops without
# looking at what follows. Every letter token is a valid JSON number.
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

# Printing
# --------

# n ones then a zero.
def show_letter(n: Nat) -> String:
  match n:
    case 0n:
      "0"
    case 1n+p:
      "1" ++ show_letter(p)

def show_nats.more(xs: +List<Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      "," ++ show_letter(h) ++ show_nats.more(t)

def show_nats.body(xs: +List<Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      show_letter(h) ++ show_nats.more(t)

def show_nats(xs: +List<Nat>) -> String:
  "[" ++ show_nats.body(xs) ++ "]"

def show_feedback.more(xs: +List<Feedback.Color>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      "," ++ Color.code(h) ++ show_feedback.more(t)

def show_feedback.body(xs: +List<Feedback.Color>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      Color.code(h) ++ show_feedback.more(t)

def show_feedback(xs: +List<Feedback.Color>) -> String:
  "[" ++ show_feedback.body(xs) ++ "]"

# The body of an array of children: each child is [feedback, tree], and every
# child after the first is prefixed with a comma.
def show_kids.body(kids: +List<Tree.Child>, prefix: String) -> String:
  match kids:
    case Nil{}:
      ""
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          match child:
            case Tree.Node{g, ckids}:
              prefix ++ "[" ++ show_feedback(f) ++ ",[" ++ show_nats(g) ++ ",[" ++ show_kids.body(ckids, "") ++ "]]]" ++ show_kids.body(rest, ",")

def show_kids(kids: +List<Tree.Child>) -> String:
  "[" ++ show_kids.body(kids, "") ++ "]"

def print(t: Tree.Tree) -> String:
  match t:
    case Tree.Node{g, kids}:
      "[" ++ show_nats(g) ++ "," ++ show_kids(kids) ++ "]"

# Parsing
# -------
#
# One state machine over the characters. Every recursive call works on a tail
# of its string, so it is structurally smaller. `frames` is the stack of
# enclosing children, `cur` the children of the current array built so far,
# `fb` the feedback of the current child and `nums` its guess, both built so
# far. `k` counts the ones of the number being read.

type Mode is Data:
  MStart{}
  MNatsOpen{}
  MNatsBody{}
  MNatsDigits{}
  MNatsNext{}
  MNatsDone{}
  MKidsStart{}
  MKidsBody{}
  MKidsNext{}
  MKidsClosed{}
  MChildClosed{}
  MChildOpen{}
  MFbBody{}
  MFbNext{}
  MFbDone{}
  MTreeOpen{}

type Frame is Data:
  Frame{kids: +List<Tree.Child>, feedback: +List<Feedback.Color>, guess: +List<Nat>}

def one_nat(n: Nat) -> +List<Nat>:
  n <> Nil{}

def one_color(c: Feedback.Color) -> +List<Feedback.Color>:
  c <> Nil{}

def parse.go(
  s: String,
  mode: Mode,
  frames: +List<Frame>,
  cur: +List<Tree.Child>,
  fb: +List<Feedback.Color>,
  nums: +List<Nat>,
  k: Nat
) -> Maybe<&1, Tree.Tree & String>:
  match s:
    case SCon{'[', t}:
      match mode:
        case MStart{}:
          parse.go(t, MNatsOpen{}, frames, cur, fb, nums, k)
        case MNatsOpen{}:
          parse.go(t, MNatsBody{}, frames, cur, fb, nums, 0n)
        case MKidsStart{}:
          parse.go(t, MKidsBody{}, frames, cur, fb, nums, k)
        case MKidsBody{}:
          parse.go(t, MChildOpen{}, Frame{cur, fb, nums} <> frames, Nil{}, Nil{}, Nil{}, k)
        case MChildOpen{}:
          parse.go(t, MFbBody{}, frames, cur, fb, nums, k)
        case MTreeOpen{}:
          parse.go(t, MNatsOpen{}, frames, cur, fb, nums, k)
        case _:
          None{}
    case SCon{']', t}:
      match mode:
        case MNatsBody{}:
          parse.go(t, MNatsDone{}, frames, cur, fb, nums, 0n)
        case MNatsNext{}:
          parse.go(t, MNatsDone{}, frames, cur, fb, nums, 0n)
        case MKidsBody{}:
          parse.go(t, MKidsClosed{}, frames, cur, fb, nums, k)
        case MKidsNext{}:
          parse.go(t, MKidsClosed{}, frames, cur, fb, nums, k)
        case MKidsClosed{}:
          match frames:
            case Nil{}:
              Some{(Tree.Node{nums, cur}, t)}
            case Con{fr, rest}:
              parse.go(t, MChildClosed{}, frames, cur, fb, nums, k)
        case MChildClosed{}:
          match frames:
            case Nil{}:
              None{}
            case Con{fr, rest}:
              match fr:
                case Frame{pkids, pfb, pnums}:
                  parse.go(t, MKidsNext{}, rest, List.append(&2, Tree.Child, pkids, Tree.Child{fb, Tree.Node{nums, cur}} <> Nil{}), pfb, pnums, 0n)
        case MFbBody{}:
          parse.go(t, MFbDone{}, frames, cur, fb, nums, k)
        case MFbNext{}:
          parse.go(t, MFbDone{}, frames, cur, fb, nums, k)
        case _:
          None{}
    case SCon{',', t}:
      match mode:
        case MNatsNext{}:
          parse.go(t, MNatsBody{}, frames, cur, fb, nums, 0n)
        case MNatsDone{}:
          parse.go(t, MKidsStart{}, frames, cur, fb, nums, 0n)
        case MKidsNext{}:
          parse.go(t, MKidsBody{}, frames, cur, fb, nums, k)
        case MFbNext{}:
          parse.go(t, MFbBody{}, frames, cur, fb, nums, k)
        case MFbDone{}:
          parse.go(t, MTreeOpen{}, frames, cur, fb, nums, k)
        case _:
          None{}
    case SCon{'0', t}:
      match mode:
        case MNatsBody{}:
          parse.go(t, MNatsNext{}, frames, cur, fb, List.append(&2, Nat, nums, one_nat(0n)), 0n)
        case MNatsDigits{}:
          parse.go(t, MNatsNext{}, frames, cur, fb, List.append(&2, Nat, nums, one_nat(k)), 0n)
        case MFbBody{}:
          parse.go(t, MFbNext{}, frames, cur, List.append(&2, Feedback.Color, fb, one_color(Feedback.Gray{})), nums, k)
        case _:
          None{}
    case SCon{'1', t}:
      match mode:
        case MNatsBody{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, 1n)
        case MNatsDigits{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, 1n+k)
        case MFbBody{}:
          parse.go(t, MFbNext{}, frames, cur, List.append(&2, Feedback.Color, fb, one_color(Feedback.Yellow{})), nums, k)
        case _:
          None{}
    case SCon{'2', t}:
      match mode:
        case MFbBody{}:
          parse.go(t, MFbNext{}, frames, cur, List.append(&2, Feedback.Color, fb, one_color(Feedback.Green{})), nums, k)
        case _:
          None{}
    case _:
      None{}

# Keep the tree only when the text ends exactly where the tree ends.
def finish(m: Maybe<&1, Tree.Tree & String>) -> Maybe<Tree.Tree>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      match p:
        case (t, SNil{}):
          Some{t}
        case _:
          None{}

def parse(s: String) -> Maybe<Tree.Tree>:
  finish(parse.go(s, MStart{}, Nil{}, Nil{}, Nil{}, Nil{}, 0n))
