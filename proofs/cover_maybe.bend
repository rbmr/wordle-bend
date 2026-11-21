# Costs as a copyable `Maybe Nat`, with `None` on top.
#
# The oracle carries class costs inside reusable lists, so the optional value
# must itself be a `Data` type. `Maybe<&2, Nat>` is that type; the arithmetic
# and order lemmas are the same as `Maybe<Nat>`'s, re-stated here so the oracle
# can copy its entries freely.
import Base
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof

def Cover.MAdd(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match a:
    case None{}:
      None{}
    case Some{+x}:
      match b:
        case None{}:
          None{}
        case Some{+y}:
          Some{Nat.add(x, y)}

def Cover.MLe(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Type:
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

def Cover.MMin(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match a:
    case None{}:
      b
    case Some{+x}:
      match b:
        case None{}:
          Some{x}
        case Some{+y}:
          Feedback.Bool.case(Maybe<&2, Nat>, Nat.is_le(x, y), Some{x}, Some{y})

def Cover.MLe_refl(a: Maybe<&2, Nat>) -> Cover.MLe(a, a):
  match a:
    case None{}:
      Unit{}
    case Some{+x}:
      NatProof.Nat.is_le_refl(x)

def Cover.MLe_trans(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>, c: Maybe<&2, Nat>,
    ab: Cover.MLe(a, b), bc: Cover.MLe(b, c)) -> Cover.MLe(a, c):
  match a b:
    case None{} None{}:
      match c:
        case None{}:
          Unit{}
        case Some{z}:
          bc
    case None{} Some{y}:
      Empty.absurd(Cover.MLe(None{}, c), ab)
    case Some{x} None{}:
      match c:
        case None{}:
          Unit{}
        case Some{z}:
          Empty.absurd(Cover.MLe(Some{x}, Some{z}), bc)
    case Some{x} Some{y}:
      match c:
        case None{}:
          Unit{}
        case Some{z}:
          NatProof.Nat.is_le_trans(x, y, z, ab, bc)

def Cover.MMin_le_l_go(x: Nat, y: Nat, b: Bool,
    +eb: {b == Nat.is_le(x, y) : Bool}) ->
  Cover.MLe(Feedback.Bool.case(Maybe<&2, Nat>, b, Some{x}, Some{y}), Some{x}):
  match b:
    case True{}:
      Cover.MLe_refl(Some{x})
    case False{}:
      NatProof.NatPrf.is_le_swap_of_false(x, y,
        Equal.sym(Bool, b, Nat.is_le(x, y), eb))

def Cover.MMin_le_l(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) ->
  Cover.MLe(Cover.MMin(a, b), a):
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
          Cover.MLe_refl(Some{x})
        case Some{+y}:
          Cover.MMin_le_l_go(x, y, Nat.is_le(x, y), {==})

def Cover.MMin_le_r_go(x: Nat, y: Nat, b: Bool,
    +eb: {b == Nat.is_le(x, y) : Bool}) ->
  Cover.MLe(Feedback.Bool.case(Maybe<&2, Nat>, b, Some{x}, Some{y}), Some{y}):
  match b:
    case True{}:
      Equal.sym(Bool, b, Nat.is_le(x, y), eb)
    case False{}:
      Cover.MLe_refl(Some{y})

def Cover.MMin_le_r(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) ->
  Cover.MLe(Cover.MMin(a, b), b):
  match a:
    case None{}:
      Cover.MLe_refl(b)
    case Some{+x}:
      match b:
        case None{}:
          Unit{}
        case Some{+y}:
          Cover.MMin_le_r_go(x, y, Nat.is_le(x, y), {==})

def Cover.MAdd_le_some(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>, +x: Nat, +y: Nat,
    pa: Cover.MLe(a, Some{x}), pb: Cover.MLe(b, Some{y})) ->
  Cover.MLe(Cover.MAdd(a, b), Some{Nat.add(x, y)}):
  match a:
    case None{}:
      Empty.absurd(Cover.MLe(None{}, Some{Nat.add(x, y)}), pa)
    case Some{+a0}:
      match b:
        case None{}:
          Empty.absurd(Cover.MLe(None{}, Some{Nat.add(x, y)}), pb)
        case Some{+b0}:
          +e1 : {Nat.is_le(Nat.add(a0, b0), Nat.add(x, b0)) == True{} : Bool} =
            NatProof.Nat.is_le_add_r(a0, x, b0, pa)
          +e2 : {Nat.is_le(Nat.add(x, b0), Nat.add(x, y)) == True{} : Bool} =
            NatProof.Nat.is_le_add_l(b0, y, x, pb)
          NatProof.Nat.is_le_trans(Nat.add(a0, b0), Nat.add(x, b0),
            Nat.add(x, y), e1, e2)
