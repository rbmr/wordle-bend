# Ghost `List<U32>` model used by the flat-array core proofs.
#
# The certified kernel keeps its runtime state in one flat `Array<U32>`.  The
# proofs relate that array to a ghost list of `U32` cells: `CS.nth(xs, i)` is
# the value cell `i` is required to hold, and `CS.set(xs, i, v)` is the list
# after a write.  Lists and `Nat` indices appear only here and in the proof
# predicates; no runtime code uses them.
import Base
import ./logic.bend as Logic
import ./nat.bend as NatProof

def CS.nth(+xs: +List<U32>, +i: Nat) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{x, rest}:
      match i:
        case 0n:
          x
        case 1n+p:
          CS.nth(rest, p)

def CS.set(+xs: +List<U32>, +i: Nat, +v: U32) -> +List<U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      match i:
        case 0n:
          v <> rest
        case 1n+p:
          x <> CS.set(rest, p, v)

def CS.mem(+x: U32, +xs: +List<U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(U32.is_eq(x, y), CS.mem(x, rest))

def CS.dedup_cons(+x: U32, b: Bool, +d: +List<U32>) -> +List<U32>:
  match b:
    case True{}:
      d
    case False{}:
      x <> d

def CS.dedup(+xs: +List<U32>) -> +List<U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      +d = CS.dedup(rest)
      CS.dedup_cons(x, CS.mem(x, rest), d)

def CS.zeros(+n: Nat) -> +List<U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+np:
      0 <> CS.zeros(np)

def CS.len(+xs: +List<U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, rest}:
      Nat.add(1n, CS.len(rest))

def CS.len_set(+xs: +List<U32>, +i: Nat, +v: U32) ->
  {CS.len(CS.set(xs, i, v)) == CS.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match i:
        case 0n:
          {==}
        case 1n+p:
          Equal.cong(Nat, Nat, n => Nat.add(1n, n), CS.len(CS.set(rest, p, v)),
            CS.len(rest), CS.len_set(rest, p, v))

def CS.nth_set_same(+xs: +List<U32>, +i: Nat, +v: U32,
    +hlt: {Nat.is_lt(i, CS.len(xs)) == True{} : Bool}) ->
  {CS.nth(CS.set(xs, i, v), i) == v : U32}:
  match xs:
    case Nil{}:
      Empty.absurd({CS.nth(CS.set(Nil{}, i, v), i) == v : U32},
        NatProof.Nat.not_lt_zero(i, hlt))
    case Con{x, rest}:
      match i:
        case 0n:
          {==}
        case 1n+p:
          CS.nth_set_same(rest, p, v, hlt)

def CS.nth_set_diff(+xs: +List<U32>, +i: Nat, +j: Nat, +v: U32,
    +hne: {Nat.is_eq(i, j) == False{} : Bool}) ->
  {CS.nth(CS.set(xs, i, v), j) == CS.nth(xs, j) : U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match i j:
        case 0n 0n:
          Empty.absurd(
            {CS.nth(CS.set(x <> rest, 0n, v), 0n) == CS.nth(x <> rest, 0n) : U32},
            Logic.Proof.true_ne_false(hne))
        case 0n 1n+jp:
          {==}
        case 1n+ip 0n:
          {==}
        case 1n+ip 1n+jp:
          CS.nth_set_diff(rest, ip, jp, v, hne)
