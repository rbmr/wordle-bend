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
# A letter is a Nat written as an ordinary decimal numeral: no sign, no
# leading zeros, and "0" for zero. So 'a', code point 97, is the JSON number
# 97. The parser reads a run of decimal digits as the Nat it denotes.
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

# One decimal digit. Keeping the ten cases apart is what lets the printer and
# the proof treat a digit as an object rather than as a number below ten.
type Digit is Data:
  D0{}
  D1{}
  D2{}
  D3{}
  D4{}
  D5{}
  D6{}
  D7{}
  D8{}
  D9{}

def Digit.nat(d: Digit) -> Nat:
  match d:
    case D0{}:
      0n
    case D1{}:
      1n
    case D2{}:
      2n
    case D3{}:
      3n
    case D4{}:
      4n
    case D5{}:
      5n
    case D6{}:
      6n
    case D7{}:
      7n
    case D8{}:
      8n
    case D9{}:
      9n

def Digit.char(d: Digit) -> String:
  match d:
    case D0{}:
      "0"
    case D1{}:
      "1"
    case D2{}:
      "2"
    case D3{}:
      "3"
    case D4{}:
      "4"
    case D5{}:
      "5"
    case D6{}:
      "6"
    case D7{}:
      "7"
    case D8{}:
      "8"
    case D9{}:
      "9"

# Digits least significant first. Adding one carries toward the tail, so a
# numeral is built by adding one as many times as the number says. The base
# list is [D0], which prints as "0"; every later list starts with a nonzero
# most significant digit, so no numeral has a leading zero.
def digits_inc(ds: +List<Digit>) -> +List<Digit>:
  match ds:
    case Nil{}:
      Con{D1{}, Nil{}}
    case Con{d, t}:
      match d:
        case D0{}:
          Con{D1{}, t}
        case D1{}:
          Con{D2{}, t}
        case D2{}:
          Con{D3{}, t}
        case D3{}:
          Con{D4{}, t}
        case D4{}:
          Con{D5{}, t}
        case D5{}:
          Con{D6{}, t}
        case D6{}:
          Con{D7{}, t}
        case D7{}:
          Con{D8{}, t}
        case D8{}:
          Con{D9{}, t}
        case D9{}:
          Con{D0{}, digits_inc(t)}

def digits_lsb(n: Nat) -> +List<Digit>:
  match n:
    case 0n:
      Con{D0{}, Nil{}}
    case 1n+p:
      digits_inc(digits_lsb(p))

# A least-significant-first digit list as a numeral, most significant first.
def digits_show(ds: +List<Digit>) -> String:
  match ds:
    case Nil{}:
      ""
    case Con{d, t}:
      String.append(digits_show(t), Digit.char(d))

def show_letter(n: Nat) -> String:
  digits_show(digits_lsb(n))

# The number a least-significant-first digit list denotes. This is the same
# left-to-right fold the parser performs while it reads the digits.
def digits_value(ds: +List<Digit>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{d, t}:
      Nat.add(Nat.mul(10n, digits_value(t)), Digit.nat(d))

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
# far. `ds` collects the digits of the number being read, least significant
# first: in MNatsBody the first digit is pushed onto it and in MNatsDigits each
# later digit is pushed on top, so a complete numeral leaves `ds` equal to
# digits_lsb(n) and digits_value(ds) is the number.

type Mode is Data:
  MStart{}
  MNatsOpen{}
  MNatsBody{}
  MNatsDigits{}
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
  ds: +List<Digit>
) -> Maybe<&1, Tree.Tree & String>:
  match s:
    case SCon{'[', t}:
      match mode:
        case MStart{}:
          parse.go(t, MNatsOpen{}, frames, cur, fb, nums, ds)
        case MNatsOpen{}:
          parse.go(t, MNatsBody{}, frames, cur, fb, nums, Nil{})
        case MKidsStart{}:
          parse.go(t, MKidsBody{}, frames, cur, fb, nums, ds)
        case MKidsBody{}:
          parse.go(t, MChildOpen{}, Frame{cur, fb, nums} <> frames, Nil{}, Nil{}, Nil{}, Nil{})
        case MChildOpen{}:
          parse.go(t, MFbBody{}, frames, cur, fb, nums, ds)
        case MTreeOpen{}:
          parse.go(t, MNatsOpen{}, frames, cur, fb, nums, ds)
        case _:
          None{}
    case SCon{']', t}:
      match mode:
        case MNatsBody{}:
          parse.go(t, MNatsDone{}, frames, cur, fb, nums, ds)
        case MNatsDigits{}:
          parse.go(t, MNatsDone{}, frames, cur, fb, List.append(&2, Nat, nums, one_nat(digits_value(ds))), Nil{})
        case MKidsBody{}:
          parse.go(t, MKidsClosed{}, frames, cur, fb, nums, ds)
        case MKidsNext{}:
          parse.go(t, MKidsClosed{}, frames, cur, fb, nums, ds)
        case MKidsClosed{}:
          match frames:
            case Nil{}:
              Some{(Tree.Node{nums, cur}, t)}
            case Con{fr, rest}:
              parse.go(t, MChildClosed{}, frames, cur, fb, nums, ds)
        case MChildClosed{}:
          match frames:
            case Nil{}:
              None{}
            case Con{fr, rest}:
              match fr:
                case Frame{pkids, pfb, pnums}:
                  parse.go(t, MKidsNext{}, rest, List.append(&2, Tree.Child, pkids, Tree.Child{fb, Tree.Node{nums, cur}} <> Nil{}), pfb, pnums, Nil{})
        case MFbBody{}:
          parse.go(t, MFbDone{}, frames, cur, fb, nums, ds)
        case MFbNext{}:
          parse.go(t, MFbDone{}, frames, cur, fb, nums, ds)
        case _:
          None{}
    case SCon{',', t}:
      match mode:
        case MNatsDigits{}:
          parse.go(t, MNatsBody{}, frames, cur, fb, List.append(&2, Nat, nums, one_nat(digits_value(ds))), Nil{})
        case MNatsDone{}:
          parse.go(t, MKidsStart{}, frames, cur, fb, nums, ds)
        case MKidsNext{}:
          parse.go(t, MKidsBody{}, frames, cur, fb, nums, ds)
        case MFbNext{}:
          parse.go(t, MFbBody{}, frames, cur, fb, nums, ds)
        case MFbDone{}:
          parse.go(t, MTreeOpen{}, frames, cur, fb, nums, ds)
        case _:
          None{}
    case SCon{'0', t}:
      match mode:
        case MNatsBody{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D0{}, ds})
        case MNatsDigits{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D0{}, ds})
        case MFbBody{}:
          parse.go(t, MFbNext{}, frames, cur, List.append(&2, Feedback.Color, fb, one_color(Feedback.Gray{})), nums, ds)
        case _:
          None{}
    case SCon{'1', t}:
      match mode:
        case MNatsBody{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D1{}, ds})
        case MNatsDigits{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D1{}, ds})
        case MFbBody{}:
          parse.go(t, MFbNext{}, frames, cur, List.append(&2, Feedback.Color, fb, one_color(Feedback.Yellow{})), nums, ds)
        case _:
          None{}
    case SCon{'2', t}:
      match mode:
        case MNatsBody{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D2{}, ds})
        case MNatsDigits{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D2{}, ds})
        case MFbBody{}:
          parse.go(t, MFbNext{}, frames, cur, List.append(&2, Feedback.Color, fb, one_color(Feedback.Green{})), nums, ds)
        case _:
          None{}
    case SCon{'3', t}:
      match mode:
        case MNatsBody{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D3{}, ds})
        case MNatsDigits{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D3{}, ds})
        case _:
          None{}
    case SCon{'4', t}:
      match mode:
        case MNatsBody{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D4{}, ds})
        case MNatsDigits{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D4{}, ds})
        case _:
          None{}
    case SCon{'5', t}:
      match mode:
        case MNatsBody{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D5{}, ds})
        case MNatsDigits{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D5{}, ds})
        case _:
          None{}
    case SCon{'6', t}:
      match mode:
        case MNatsBody{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D6{}, ds})
        case MNatsDigits{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D6{}, ds})
        case _:
          None{}
    case SCon{'7', t}:
      match mode:
        case MNatsBody{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D7{}, ds})
        case MNatsDigits{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D7{}, ds})
        case _:
          None{}
    case SCon{'8', t}:
      match mode:
        case MNatsBody{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D8{}, ds})
        case MNatsDigits{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D8{}, ds})
        case _:
          None{}
    case SCon{'9', t}:
      match mode:
        case MNatsBody{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D9{}, ds})
        case MNatsDigits{}:
          parse.go(t, MNatsDigits{}, frames, cur, fb, nums, Con{D9{}, ds})
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
  finish(parse.go(s, MStart{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}))
