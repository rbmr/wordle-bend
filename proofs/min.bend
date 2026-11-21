# The minimum of a list, with the bounds the solver needs.
#
# The search for a tree picks the cheapest guess. That is a fold with `Nat.min`
# over the guess list, and its correctness rests on three facts proved here: the
# fold is below its accumulator, it is below every member, and its result is
# either the accumulator or a member.
import Base
import ./logic.bend as Logic
import ./nat.bend as NatProof

# Membership in a list of numbers.
def Mem(x: Nat, +xs: +List<Nat>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case Con{h, t}:
      {x == h : Nat} | Mem(x, t)

# The left fold over a list with `Nat.min`. The list comes first so that the
# termination check sees it shrink.
def Nat.fold_min(+xs: +List<Nat>, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      Nat.fold_min(t, Nat.min(acc, h))

def Nat.succ_eq(a: Nat, m: Nat, e: {m == a : Nat}) ->
  {1n+m == 1n+a : Nat}:
  %e : {1n+m == 1n+_ : Nat}
  {==}

# `Nat.min` is below each argument.
def Nat.min_le_l(+a: Nat, +b: Nat) ->
  {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      NatProof.Nat.is_le_refl(0n)
    case 1n+ap 0n:
      NatProof.Nat.is_le_zero_l(1n+ap)
    case 1n+ap 1n+bp:
      NatProof.Nat.is_le_succ(Nat.min(ap, bp), ap, Nat.min_le_l(ap, bp))

def Nat.min_le_r(+a: Nat, +b: Nat) ->
  {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n _:
      NatProof.Nat.is_le_zero_l(b)
    case 1n+ap 0n:
      NatProof.Nat.is_le_refl(0n)
    case 1n+ap 1n+bp:
      NatProof.Nat.is_le_succ(Nat.min(ap, bp), bp, Nat.min_le_r(ap, bp))

# `Nat.min` is one of its arguments.
def Nat.min_arg_succ(+ap: Nat, +bp: Nat,
    r: {Nat.min(ap, bp) == ap : Nat} | {Nat.min(ap, bp) == bp : Nat}) ->
  {Nat.min(1n+ap, 1n+bp) == 1n+ap : Nat}
  | {Nat.min(1n+ap, 1n+bp) == 1n+bp : Nat}:
  match r:
    case Inl{e}:
      Inl{Nat.succ_eq(ap, Nat.min(ap, bp), e)}
    case Inr{e}:
      Inr{Nat.succ_eq(bp, Nat.min(ap, bp), e)}

def Nat.min_is_arg(+a: Nat, +b: Nat) ->
  {Nat.min(a, b) == a : Nat} | {Nat.min(a, b) == b : Nat}:
  match a b:
    case 0n _:
      Inl{{==}}
    case 1n+ap 0n:
      Inr{{==}}
    case 1n+ap 1n+bp:
      Nat.min_arg_succ(ap, bp, Nat.min_is_arg(ap, bp))

# The fold's value is below the accumulator.
def Nat.fold_min_le_acc(+xs: +List<Nat>, +acc: Nat) ->
  {Nat.is_le(Nat.fold_min(xs, acc), acc) == True{} : Bool}:
  match xs:
    case Nil{}:
      NatProof.Nat.is_le_refl(acc)
    case Con{h, t}:
      NatProof.Nat.is_le_trans(Nat.fold_min(t, Nat.min(acc, h)), Nat.min(acc, h), acc,
        Nat.fold_min_le_acc(t, Nat.min(acc, h)),
        Nat.min_le_l(acc, h))

# The fold's value is below every member.
def Nat.fold_min_le_mem(+xs: +List<Nat>, +acc: Nat, +x: Nat, m: Mem(x, xs)) ->
  {Nat.is_le(Nat.fold_min(xs, acc), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({Nat.is_le(Nat.fold_min(Nil{}, acc), x) == True{} : Bool}, m)
    case Con{h, t}:
      match m:
        case Inl{e}:
          NatProof.Nat.is_le_eq_r(Nat.fold_min(h <> t, acc), h, x,
            Equal.sym(Nat, x, h, e),
            NatProof.Nat.is_le_trans(Nat.fold_min(t, Nat.min(acc, h)), Nat.min(acc, h), h,
              Nat.fold_min_le_acc(t, Nat.min(acc, h)),
              Nat.min_le_r(acc, h)))
        case Inr{rest}:
          Nat.fold_min_le_mem(t, Nat.min(acc, h), x, rest)

# Helpers for `fold_min_mem`, because a computed value cannot be the scrutinee.
def Nat.fold_min_mem_acc(+h: Nat, +t: +List<Nat>, +acc: Nat, v: Nat,
    e: {v == Nat.min(acc, h) : Nat},
    r: {Nat.min(acc, h) == acc : Nat})
  -> {v == acc : Nat} | Mem(v, h <> t):
  Inl{Equal.trans(Nat, v, Nat.min(acc, h), acc, e, r)}

def Nat.fold_min_mem_head(+h: Nat, +t: +List<Nat>, +acc: Nat, v: Nat,
    e: {v == Nat.min(acc, h) : Nat},
    r: {Nat.min(acc, h) == h : Nat})
  -> {v == acc : Nat} | Mem(v, h <> t):
  Inr{Inl{Equal.trans(Nat, v, Nat.min(acc, h), h, e, r)}}

def Nat.fold_min_mem_min(+h: Nat, +t: +List<Nat>, +acc: Nat, v: Nat,
    e: {v == Nat.min(acc, h) : Nat},
    r: {Nat.min(acc, h) == acc : Nat} | {Nat.min(acc, h) == h : Nat})
  -> {v == acc : Nat} | Mem(v, h <> t):
  match r:
    case Inl{r2}:
      Nat.fold_min_mem_acc(h, t, acc, v, e, r2)
    case Inr{r2}:
      Nat.fold_min_mem_head(h, t, acc, v, e, r2)

def Nat.fold_min_mem_step(+h: Nat, +t: +List<Nat>, +acc: Nat,
    r: {Nat.fold_min(t, Nat.min(acc, h)) == Nat.min(acc, h) : Nat}
       | Mem(Nat.fold_min(t, Nat.min(acc, h)), t))
  -> {Nat.fold_min(h <> t, acc) == acc : Nat} | Mem(Nat.fold_min(h <> t, acc), h <> t):
  match r:
    case Inl{e}:
      Nat.fold_min_mem_min(h, t, acc, Nat.fold_min(t, Nat.min(acc, h)), e,
        Nat.min_is_arg(acc, h))
    case Inr{m}:
      Inr{Inr{m}}

# The fold's value is the accumulator or a member.
def Nat.fold_min_mem(+xs: +List<Nat>, +acc: Nat) ->
  {Nat.fold_min(xs, acc) == acc : Nat} | Mem(Nat.fold_min(xs, acc), xs):
  match xs:
    case Nil{}:
      Inl{{==}}
    case Con{h, t}:
      Nat.fold_min_mem_step(h, t, acc,
        Nat.fold_min_mem(t, Nat.min(acc, h)))
