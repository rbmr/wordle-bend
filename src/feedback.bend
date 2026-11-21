# Wordle feedback.
#
# A letter is a Nat (its code point), a word is a list of letters, and a
# feedback is a list of colours. The lists are reusable (Data) so the same word
# can be inspected more than once without copying by hand.
import Base

type Color is Data:
  Gray{}
  Yellow{}
  Green{}

def Bool.case(~A: Type, b: Bool, t: A, f: A) -> A:
  match b:
    case True{}:
      t
    case False{}:
      f

def Color.eq(a: Color, b: Color) -> Bool:
  match a b:
    case Gray{} Gray{}:
      True{}
    case Yellow{} Yellow{}:
      True{}
    case Green{} Green{}:
      True{}
    case _ _:
      False{}

def Color.num(c: Color) -> Nat:
  match c:
    case Gray{}:
      0n
    case Yellow{}:
      1n
    case Green{}:
      2n

def pair_color_eq(p: Color & Color) -> Bool:
  (a, b) = p
  Color.eq(a, b)

def feedback_eq(+a: +List<Color>, +b: +List<Color>) -> Bool:
  same_len = Nat.is_eq(List.length(&2, Color, a), List.length(&2, Color, b))
  zs = List.zip(&2, Color, &2, Color, a, b)
  all_same = List.all(&1, Color & Color, pair_color_eq, zs)
  Bool.and(same_len, all_same)

def pair_nat_eq(p: Nat & Nat) -> Bool:
  (a, b) = p
  Nat.is_eq(a, b)

def word_eq(+a: +List<Nat>, +b: +List<Nat>) -> Bool:
  same_len = Nat.is_eq(List.length(&2, Nat, a), List.length(&2, Nat, b))
  zs = List.zip(&2, Nat, &2, Nat, a, b)
  all_same = List.all(&1, Nat & Nat, pair_nat_eq, zs)
  Bool.and(same_len, all_same)

# Whether x equals the first letter of pool.
def next_letter_same(x: Nat, pool: +List<Nat>) -> Bool:
  match pool:
    case Nil{}:
      False{}
    case Con{h, t}:
      Nat.is_eq(x, h)

# Whether the first letters of guess and answer are equal.
def next_same(guess: +List<Nat>, answer: +List<Nat>) -> Bool:
  match guess:
    case Nil{}:
      False{}
    case Con{g, t}:
      match answer:
        case Nil{}:
          False{}
        case Con{a, at}:
          Nat.is_eq(g, a)

# The answer letters still available for non-green guess positions: the answer
# positions where the guess and the answer differ. Positions past the end of
# either word contribute nothing.
def non_green(+guess: +List<Nat>, +answer: +List<Nat>) -> +List<Nat>:
  match guess:
    case Nil{}:
      Nil{}
    case Con{+g, +t}:
      match answer:
        case Nil{}:
          Nil{}
        case Con{+a, +at}:
          Bool.case(+List<Nat>, Nat.is_eq(g, a), non_green(t, at), a <> non_green(t, at))

# The colour for a non-green position: Yellow when the letter is available in
# pool, Gray otherwise.
def consume_color(+x: Nat, +pool: +List<Nat>, same: Bool) -> Color:
  match pool:
    case Nil{}:
      Gray{}
    case Con{+h, +t}:
      Bool.case(Color, same, Yellow{}, consume_color(x, t, next_letter_same(x, t)))

# pool with one occurrence of x removed when same is true.
def consume_pool(+x: Nat, +pool: +List<Nat>, same: Bool) -> +List<Nat>:
  match pool:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      Bool.case(+List<Nat>, same, t, h <> consume_pool(x, t, next_letter_same(x, t)))

# feedback.go walks the guess and the answer together. same says whether the
# current heads are equal; pool holds the answer letters not yet consumed by
# an earlier non-green guess position. Once the answer is exhausted every
# remaining position is Gray.
def feedback.go(+guess: +List<Nat>, +answer: +List<Nat>, +pool: +List<Nat>, same: Bool) -> +List<Color>:
  match guess:
    case Nil{}:
      Nil{}
    case Con{+g, +t}:
      match answer:
        case Nil{}:
          Gray{} <> feedback.go(t, Nil{}, Nil{}, False{})
        case Con{+a, +at}:
          Bool.case(+List<Color>, same,
                    Green{} <> feedback.go(t, at, pool, next_same(t, at)),
                    consume_color(g, pool, next_letter_same(g, pool)) <> feedback.go(t, at, consume_pool(g, pool, next_letter_same(g, pool)), next_same(t, at)))

def feedback(+guess: +List<Nat>, +answer: +List<Nat>) -> +List<Color>:
  feedback.go(guess, answer, non_green(guess, answer), next_same(guess, answer))

# A feedback list is all Green when every colour in it is Green.
def AllGreen(fb: +List<Color>) -> Type:
  match fb:
    case Nil{}:
      Unit
    case Con{h, t}:
      {h == Green{} : Color} & AllGreen(t)
