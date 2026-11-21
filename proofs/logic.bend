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
