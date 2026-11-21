# Small logical helpers shared by the solver proofs.
import Base

# The type family that turns `b == False` into `Empty` and `b == True` into
# `Unit`, used to refute boolean clashes by rewriting.
def Bool.disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

# `Empty` from a false equality between booleans.
def Proof.false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.disc(_)
  Unit{}

def Proof.true_ne_false(e: {True{} == False{} : Bool}) -> Empty:
  Proof.false_ne_true(Equal.sym(Bool, True{}, False{}, e))

# A proposition that is provable exactly when the boolean is `True`.
def Proof.is_true(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def Proof.true_intro(b: Bool, e: {b == True{} : Bool}) -> Proof.is_true(b):
  %Equal.sym(Bool, b, True{}, e) : Proof.is_true(_)
  Unit{}

def Proof.true_elim(b: Bool, p: Proof.is_true(b)) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      match p:

# Conjunction on booleans.
def Proof.and_true_l(a: Bool, b: Bool,
    e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Proof.false_ne_true(e))

def Proof.and_true_r(a: Bool, b: Bool,
    e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, Proof.false_ne_true(e))

def Proof.and_intro(a: Bool, b: Bool,
    ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) ->
  {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool},
                   Proof.false_ne_true(ea))

# Split one conjunction proof into both facts, consuming the proof once.
def Proof.and_split(a: Bool, b: Bool,
    e: {Bool.and(a, b) == True{} : Bool}) ->
  {a == True{} : Bool} & {b == True{} : Bool}:
  match a:
    case True{}:
      ({==}, e)
    case False{}:
      Empty.absurd({a == True{} : Bool} & {b == True{} : Bool},
                   Proof.false_ne_true(e))
