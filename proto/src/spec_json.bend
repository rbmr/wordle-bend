# The JSON text specification, written independently of the printer.
#
# This module is the reference for the text the CLI prints. It does not import
# `src/json.bend` and shares no helper with it: the renderer below is the
# obvious translation of the documented format, and `well_formed` is a
# recogniser for exactly the JSON subset that format uses.
#
# The subset is arrays and non-negative decimal integers:
#
#   value  = array | number
#   array  = '[' ']' | '[' value (',' value)* ']'
#   number = '0' | nonzero-digit digit*
#
# There is no whitespace, no sign, no fraction and no exponent. Recognition
# succeeds only when the whole string is consumed.
import Base
import ./feedback.bend as Feedback
import ./tree.bend as Tree

# Rendering
# ---------
#
# The format, straight from docs/cli.md:
#
#   tree     = "[" guess "," kids "]"
#   guess    = "[" n1 "," n2 ... "]"        ("[]" if empty)
#   kids     = "[" child "," child ... "]"  ("[]" if empty)
#   child    = "[" feedback "," tree "]"
#   feedback = "[" c1 "," c2 ... "]"        ("[]" if empty)
#
# A colour is "0" Gray, "1" Yellow or "2" Green. A letter is its code point as
# an ordinary decimal numeral: most significant digit first, no leading zeros,
# and "0" for zero. `decimal` below is that numeral, written out directly.

def render_color(c: Feedback.Color) -> String:
  match c:
    case Feedback.Gray{}:
      "0"
    case Feedback.Yellow{}:
      "1"
    case Feedback.Green{}:
      "2"

def render_feedback.more(xs: +List<Feedback.Color>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      "," ++ render_color(h) ++ render_feedback.more(t)

def render_feedback.body(xs: +List<Feedback.Color>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      render_color(h) ++ render_feedback.more(t)

def render_feedback(xs: +List<Feedback.Color>) -> String:
  "[" ++ render_feedback.body(xs) ++ "]"

# Decimal numerals
# -----------------
#
# A numeral is the digits of the number in base ten, most significant first.
# `decimal.digits` peels the number with `Nat.divmod(n, 10)`: the quotient is
# rendered first and the remainder is the digit appended last. A single-digit
# number stops after that one digit, so there is no leading zero; zero itself
# is the one-character string "0".

def digit_char(n: Nat) -> String:
  match n:
    case 0n:
      "0"
    case 1n+p:
      match p:
        case 0n:
          "1"
        case 1n+q:
          match q:
            case 0n:
              "2"
            case 1n+r:
              match r:
                case 0n:
                  "3"
                case 1n+s:
                  match s:
                    case 0n:
                      "4"
                    case 1n+t:
                      match t:
                        case 0n:
                          "5"
                        case 1n+u:
                          match u:
                            case 0n:
                              "6"
                            case 1n+v:
                              match v:
                                case 0n:
                                  "7"
                                case 1n+w:
                                  match w:
                                    case 0n:
                                      "8"
                                    case 1n+x:
                                      match x:
                                        case 0n:
                                          "9"
                                        case 1n++_:
                                          ""

def decimal.digits(fuel: Nat, n: Nat, qr: Nat & Nat) -> +List<Nat>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match n:
        case 0n:
          Nil{}
        case 1n+p:
          match qr:
            case (q, r):
              match q:
                case 0n:
                  Con{r, Nil{}}
                case 1n++_:
                  List.append(&2, Nat, decimal.digits(f, q, Nat.divmod(q, 10n)), Con{r, Nil{}})

def decimal.chars(xs: +List<Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      String.append(digit_char(h), decimal.chars(t))

def decimal(n: Nat) -> String:
  match n:
    case 0n:
      "0"
    case 1n++p:
      decimal.chars(decimal.digits(1n+p, 1n+p, Nat.divmod(1n+p, 10n)))

def render_nats.more(xs: +List<Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      "," ++ decimal(h) ++ render_nats.more(t)

def render_nats.body(xs: +List<Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      decimal(h) ++ render_nats.more(t)

def render_nats(xs: +List<Nat>) -> String:
  "[" ++ render_nats.body(xs) ++ "]"

# One child, inlined so that the renderer is a single self-recursive def:
# Bend has no mutual recursion. `prefix` is "" for the first child and "," for
# every later one.
def render_kids.body(kids: +List<Tree.Child>, prefix: String) -> String:
  match kids:
    case Nil{}:
      ""
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          match child:
            case Tree.Node{g, ckids}:
              prefix ++ "[" ++ render_feedback(f)
                     ++ ",[" ++ render_nats(g)
                     ++ ",[" ++ render_kids.body(ckids, "")
                     ++ "]]]"
                     ++ render_kids.body(rest, ",")

def render_kids(kids: +List<Tree.Child>) -> String:
  "[" ++ render_kids.body(kids, "") ++ "]"

def render(t: Tree.Tree) -> String:
  match t:
    case Tree.Node{g, kids}:
      "[" ++ render_nats(g) ++ "," ++ render_kids(kids) ++ "]"

# Recognition
# -----------
#
# A single left-to-right machine. `stack` records the enclosing arrays that
# still have to be closed: one unit per open '['. Every state consumes one
# character, so the recursion is structurally smaller at each step.
#
#   SValue    expecting the start of a value (top level or after a comma)
#   SOpen     just after '[': a value or an immediate ']'
#   SDigits   inside a number that began with a nonzero digit
#   SAfter    just after a value: ',' or ']', or the end at top level

type State is Data:
  SValue{}
  SOpen{}
  SDigits{}
  SAfter{}

def recognise.go(s: String, state: State, stack: +List<Unit>) -> Maybe<String>:
  match s:
    case SNil{}:
      match state stack:
        case SAfter{} Nil{}:
          Some{SNil{}}
        case _ _:
          None{}
    case SCon{c, t}:
      match c:
        case '[':
          match state:
            case SValue{}:
              recognise.go(t, SOpen{}, Unit{} <> stack)
            case SOpen{}:
              recognise.go(t, SOpen{}, Unit{} <> stack)
            case _:
              None{}
        case ']':
          match state:
            case SOpen{}:
              match stack:
                case Nil{}:
                  Some{t}
                case Con{_, rest}:
                  recognise.go(t, SAfter{}, rest)
            case SDigits{}:
              match stack:
                case Nil{}:
                  Some{t}
                case Con{_, rest}:
                  recognise.go(t, SAfter{}, rest)
            case SAfter{}:
              match stack:
                case Nil{}:
                  Some{t}
                case Con{_, rest}:
                  recognise.go(t, SAfter{}, rest)
            case SValue{}:
              None{}
        case ',':
          match state:
            case SDigits{}:
              match stack:
                case Nil{}:
                  None{}
                case _:
                  recognise.go(t, SValue{}, stack)
            case SAfter{}:
              match stack:
                case Nil{}:
                  None{}
                case _:
                  recognise.go(t, SValue{}, stack)
            case _:
              None{}
        case '0':
          match state:
            case SValue{}:
              recognise.go(t, SAfter{}, stack)
            case SOpen{}:
              recognise.go(t, SAfter{}, stack)
            case SDigits{}:
              recognise.go(t, SDigits{}, stack)
            case _:
              None{}
        case '1':
          match state:
            case SValue{}:
              recognise.go(t, SDigits{}, stack)
            case SOpen{}:
              recognise.go(t, SDigits{}, stack)
            case SDigits{}:
              recognise.go(t, SDigits{}, stack)
            case _:
              None{}
        case '2':
          match state:
            case SValue{}:
              recognise.go(t, SDigits{}, stack)
            case SOpen{}:
              recognise.go(t, SDigits{}, stack)
            case SDigits{}:
              recognise.go(t, SDigits{}, stack)
            case _:
              None{}
        case '3':
          match state:
            case SValue{}:
              recognise.go(t, SDigits{}, stack)
            case SOpen{}:
              recognise.go(t, SDigits{}, stack)
            case SDigits{}:
              recognise.go(t, SDigits{}, stack)
            case _:
              None{}
        case '4':
          match state:
            case SValue{}:
              recognise.go(t, SDigits{}, stack)
            case SOpen{}:
              recognise.go(t, SDigits{}, stack)
            case SDigits{}:
              recognise.go(t, SDigits{}, stack)
            case _:
              None{}
        case '5':
          match state:
            case SValue{}:
              recognise.go(t, SDigits{}, stack)
            case SOpen{}:
              recognise.go(t, SDigits{}, stack)
            case SDigits{}:
              recognise.go(t, SDigits{}, stack)
            case _:
              None{}
        case '6':
          match state:
            case SValue{}:
              recognise.go(t, SDigits{}, stack)
            case SOpen{}:
              recognise.go(t, SDigits{}, stack)
            case SDigits{}:
              recognise.go(t, SDigits{}, stack)
            case _:
              None{}
        case '7':
          match state:
            case SValue{}:
              recognise.go(t, SDigits{}, stack)
            case SOpen{}:
              recognise.go(t, SDigits{}, stack)
            case SDigits{}:
              recognise.go(t, SDigits{}, stack)
            case _:
              None{}
        case '8':
          match state:
            case SValue{}:
              recognise.go(t, SDigits{}, stack)
            case SOpen{}:
              recognise.go(t, SDigits{}, stack)
            case SDigits{}:
              recognise.go(t, SDigits{}, stack)
            case _:
              None{}
        case '9':
          match state:
            case SValue{}:
              recognise.go(t, SDigits{}, stack)
            case SOpen{}:
              recognise.go(t, SDigits{}, stack)
            case SDigits{}:
              recognise.go(t, SDigits{}, stack)
            case _:
              None{}
        case _:
          None{}

def whole(m: Maybe<String>) -> Bool:
  match m:
    case Some{rest}:
      match rest:
        case SNil{}:
          True{}
        case SCon{_, _}:
          False{}
    case None{}:
      False{}

def well_formed(s: String) -> Bool:
  whole(recognise.go(s, SValue{}, Nil{}))
