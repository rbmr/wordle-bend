# `Maybe Nat` with `None` as infinity.
#
# A class with no valid tree has no cost, so the search carries `Maybe Nat`
# costs. `None` is above every number: it only compares below `None`, and the
# minimum of a list treats it as the identity.
import Base
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof

# Saturating addition: a missing cost makes the sum missing.
def MB.MAdd(a: Maybe<Nat>, b: Maybe<Nat>) -> Maybe<Nat>:
  match a:
    case None{}:
      None{}
    case Some{+x}:
      match b:
        case None{}:
          None{}
        case Some{+y}:
          Some{Nat.add(x, y)}

# Cost order, with `None` on top.
def MB.MLe(a: Maybe<Nat>, b: Maybe<Nat>) -> Type:
  match a:
    case None{}:
      match b:
        case None{}:
          Unit
        case Some{+y}:
          Empty
    case Some{+x}:
      match b:
        case None{}:
          Unit
        case Some{+y}:
          {Nat.is_le(x, y) == True{} : Bool}

# Minimum of two costs.
def MB.min(a: Maybe<Nat>, b: Maybe<Nat>) -> Maybe<Nat>:
  match a:
    case None{}:
      b
    case Some{+x}:
      match b:
        case None{}:
          Some{x}
        case Some{+y}:
          Feedback.Bool.case(Maybe<Nat>, Nat.is_le(x, y), Some{x}, Some{y})

def MB.MLe_refl(a: Maybe<Nat>) -> MB.MLe(a, a):
  match a:
    case None{}:
      Unit{}
    case Some{+x}:
      NatProof.Nat.is_le_refl(x)

def MB.MLe_trans(a: Maybe<Nat>, b: Maybe<Nat>, c: Maybe<Nat>,
    ab: MB.MLe(a, b), bc: MB.MLe(b, c)) -> MB.MLe(a, c):
  match a b:
    case None{} None{}:
      match c:
        case None{}:
          Unit{}
        case Some{z}:
          bc
    case None{} Some{y}:
      Empty.absurd(MB.MLe(None{}, c), ab)
    case Some{x} None{}:
      match c:
        case None{}:
          Unit{}
        case Some{z}:
          Empty.absurd(MB.MLe(Some{x}, Some{z}), bc)
    case Some{x} Some{y}:
      match c:
        case None{}:
          Unit{}
        case Some{z}:
          NatProof.Nat.is_le_trans(x, y, z, ab, bc)

# Branch of `min_le_l` on the comparison.
def MB.min_le_l_go(x: Nat, y: Nat, b: Bool, +eb: {b == Nat.is_le(x, y) : Bool}) ->
  MB.MLe(Feedback.Bool.case(Maybe<Nat>, b, Some{x}, Some{y}), Some{x}):
  match b:
    case True{}:
      MB.MLe_refl(Some{x})
    case False{}:
      NatProof.NatPrf.is_le_swap_of_false(x, y,
        Equal.sym(Bool, b, Nat.is_le(x, y), eb))

# The minimum is below its left argument.
def MB.min_le_l(a: Maybe<Nat>, b: Maybe<Nat>) -> MB.MLe(MB.min(a, b), a):
  match a:
    case None{}:
      match b:
        case None{}:
          Unit{}
        case Some{y}:
          Unit{}
    case Some{+x}:
      match b:
        case None{}:
          MB.MLe_refl(Some{x})
        case Some{+y}:
          MB.min_le_l_go(x, y, Nat.is_le(x, y), {==})

# Branch of `min_le_r` on the comparison.
def MB.min_le_r_go(x: Nat, y: Nat, b: Bool, +eb: {b == Nat.is_le(x, y) : Bool}) ->
  MB.MLe(Feedback.Bool.case(Maybe<Nat>, b, Some{x}, Some{y}), Some{y}):
  match b:
    case True{}:
      Equal.sym(Bool, b, Nat.is_le(x, y), eb)
    case False{}:
      MB.MLe_refl(Some{y})

# The minimum is below its right argument.
def MB.min_le_r(a: Maybe<Nat>, b: Maybe<Nat>) -> MB.MLe(MB.min(a, b), b):
  match a:
    case None{}:
      MB.MLe_refl(b)
    case Some{+x}:
      match b:
        case None{}:
          Unit{}
        case Some{+y}:
          MB.min_le_r_go(x, y, Nat.is_le(x, y), {==})

# A sum of bounded costs is bounded.
def MB.MAdd_le_some(a: Maybe<Nat>, b: Maybe<Nat>, +x: Nat, +y: Nat,
    pa: MB.MLe(a, Some{x}), pb: MB.MLe(b, Some{y})) ->
  MB.MLe(MB.MAdd(a, b), Some{Nat.add(x, y)}):
  match a:
    case None{}:
      Empty.absurd(MB.MLe(None{}, Some{Nat.add(x, y)}), pa)
    case Some{+a0}:
      match b:
        case None{}:
          Empty.absurd(MB.MLe(None{}, Some{Nat.add(x, y)}), pb)
        case Some{+b0}:
          +e1 : {Nat.is_le(Nat.add(a0, b0), Nat.add(x, b0)) == True{} : Bool} =
            NatProof.Nat.is_le_add_r(a0, x, b0, pa)
          +e2 : {Nat.is_le(Nat.add(x, b0), Nat.add(x, y)) == True{} : Bool} =
            NatProof.Nat.is_le_add_l(b0, y, x, pb)
          NatProof.Nat.is_le_trans(Nat.add(a0, b0), Nat.add(x, b0), Nat.add(x, y), e1, e2)

# A `Some` cost bounded by `Some x` is a number at most `x`.
def MB.some_of_le(a: Maybe<Nat>, x: Nat, p: MB.MLe(a, Some{x})) ->
  Sigma<&1, &1, Nat, y => {a == Some{y} : Maybe<Nat>} & {Nat.is_le(y, x) == True{} : Bool}>:
  match a:
    case None{}:
      Empty.absurd(Sigma<&1, &1, Nat, y => {None{} == Some{y} : Maybe<Nat>}
                                     & {Nat.is_le(y, x) == True{} : Bool}>, p)
    case Some{y}:
      (y, ({==}, p))
