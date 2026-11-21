# Nat order and arithmetic lemmas used by the solver proofs.
#
# Base gives `Nat.cmp` and the `is_lt` / `is_le` / `is_ge` predicates but
# proves almost nothing about them, so the solver proofs carry their own.
import Base
import ./logic.bend as Logic

# 1. Reflexivity.
def Nat.is_le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.is_le_refl(p)

def Nat.is_lt_succ_self(a: Nat) -> {Nat.is_lt(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.is_lt_succ_self(p)

# Zero is below every number. `Nat.cmp 0 c` is stuck on `c`, so this is a
# separate induction.
def Nat.is_le_zero_l(c: Nat) -> {Nat.is_le(0n, c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+cp:
      {==}

# Nothing is below zero.
def Nat.not_lt_zero(a: Nat, e: {Nat.is_lt(a, 0n) == True{} : Bool}) -> Empty:
  match a:
    case 0n:
      Logic.Proof.false_ne_true(e)
    case 1n+ap:
      Logic.Proof.false_ne_true(e)

# 2. Transitivity of `<=`.
def Nat.is_le_trans(a: Nat, b: Nat, c: Nat,
    ab: {Nat.is_le(a, b) == True{} : Bool},
    bc: {Nat.is_le(b, c) == True{} : Bool}) ->
  {Nat.is_le(a, c) == True{} : Bool}:
  match a b:
    case 0n _:
      Nat.is_le_zero_l(c)
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool},
                   Logic.Proof.false_ne_true(ab))
    case 1n+ap 1n+bp:
      match c:
        case 0n:
          Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool},
                       Logic.Proof.false_ne_true(bc))
        case 1n+cp:
          Nat.is_le_trans(ap, bp, cp, ab, bc)

# `a < b` and `b <= c` give `a < c`.
def Nat.is_lt_le_trans(a: Nat, b: Nat, c: Nat,
    ab: {Nat.is_lt(a, b) == True{} : Bool},
    bc: {Nat.is_le(b, c) == True{} : Bool}) ->
  {Nat.is_lt(a, c) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, c) == True{} : Bool},
                   Logic.Proof.false_ne_true(ab))
    case 0n 1n+bp:
      match c:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool},
                       Logic.Proof.false_ne_true(bc))
        case 1n+cp:
          {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, c) == True{} : Bool},
                   Logic.Proof.false_ne_true(ab))
    case 1n+ap 1n+bp:
      match c:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool},
                       Logic.Proof.false_ne_true(bc))
        case 1n+cp:
          Nat.is_lt_le_trans(ap, bp, cp, ab, bc)

# `a <= b` and `b < c` give `a < c`.
def Nat.is_le_lt_trans(a: Nat, b: Nat, c: Nat,
    ab: {Nat.is_le(a, b) == True{} : Bool},
    bc: {Nat.is_lt(b, c) == True{} : Bool}) ->
  {Nat.is_lt(a, c) == True{} : Bool}:
  match a b:
    case 0n 0n:
      bc
    case 0n 1n+bp:
      match c:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool},
                       Logic.Proof.false_ne_true(bc))
        case 1n+cp:
          {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, c) == True{} : Bool},
                   Logic.Proof.false_ne_true(ab))
    case 1n+ap 1n+bp:
      match c:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+bp, 0n) == True{} : Bool},
                       Logic.Proof.false_ne_true(bc))
        case 1n+cp:
          Nat.is_le_lt_trans(ap, bp, cp, ab, bc)

# Successor preserves and reflects `<=`.
def Nat.is_le_succ(a: Nat, b: Nat,
    e: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Nat.is_le(1n+a, 1n+b) == True{} : Bool}:
  e

def Nat.is_le_succ_inv(a: Nat, b: Nat,
    e: {Nat.is_le(1n+a, 1n+b) == True{} : Bool}) ->
  {Nat.is_le(a, b) == True{} : Bool}:
  e

# `a < b` gives `a <= b`.
def Nat.is_le_of_lt(a: Nat, b: Nat,
    e: {Nat.is_lt(a, b) == True{} : Bool}) ->
  {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == True{} : Bool},
                   Logic.Proof.false_ne_true(e))
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool},
                   Logic.Proof.false_ne_true(e))
    case 1n+ap 1n+bp:
      Nat.is_le_of_lt(ap, bp, e)

# 3. `a` is below the successor of any `b` at least `a`.
def Nat.is_lt_succ_of_le(a: Nat, b: Nat,
    e: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 1n) == True{} : Bool},
                   Logic.Proof.false_ne_true(e))
    case 1n+ap 1n+bp:
      Nat.is_lt_succ_of_le(ap, bp, e)

# `a < 1+b` gives `a <= b`.
def Nat.is_le_of_lt_succ(a: Nat, b: Nat,
    e: {Nat.is_lt(a, 1n+b) == True{} : Bool}) ->
  {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n _:
      Nat.is_le_zero_l(b)
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool},
                   Nat.not_lt_zero(ap, e))
    case 1n+ap 1n+bp:
      Nat.is_le_of_lt_succ(ap, bp, e)

# 4. `a <= 0` forces `a = 0`.
def Nat.eq_zero_of_le_zero(a: Nat,
    e: {Nat.is_le(a, 0n) == True{} : Bool}) -> {a == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      Empty.absurd({1n+ap == 0n : Nat}, Logic.Proof.false_ne_true(e))

# 5. A number is below its successor; a number below itself is impossible.
def Nat.lt_succ(a: Nat) -> {Nat.is_lt(a, 1n+a) == True{} : Bool}:
  Nat.is_lt_succ_self(a)

def Nat.not_lt_self(a: Nat, e: {Nat.is_lt(a, a) == True{} : Bool}) -> Empty:
  match a:
    case 0n:
      Logic.Proof.false_ne_true(e)
    case 1n+p:
      Nat.not_lt_self(p, e)

# 6. Addition is monotone on both sides.
def Nat.is_le_add_l(a: Nat, b: Nat, +c: Nat,
    e: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  match c:
    case 0n:
      e
    case 1n+cp:
      Nat.is_le_add_l(a, b, cp, e)

# `c <= b + c`.
def Nat.is_le_add_self_l(+b: Nat, +c: Nat) ->
  {Nat.is_le(c, Nat.add(b, c)) == True{} : Bool}:
  match b:
    case 0n:
      Nat.is_le_refl(c)
    case 1n+bp:
      Nat.is_le_of_lt(c, 1n+Nat.add(bp, c),
        Nat.is_lt_succ_of_le(c, Nat.add(bp, c),
          Nat.is_le_add_self_l(bp, c)))

def Nat.is_le_add_r(a: Nat, b: Nat, +c: Nat,
    e: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  match a b:
    case 0n _:
      Nat.is_le_add_self_l(b, c)
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(Nat.add(1n+ap, c), c) == True{} : Bool},
                   Logic.Proof.false_ne_true(e))
    case 1n+ap 1n+bp:
      Nat.is_le_add_r(ap, bp, c, e)

# 7. Substitution in the second argument of `is_le`.
def Nat.is_le_eq_r(a: Nat, b: Nat, c: Nat, e: {b == c : Nat},
    p: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Nat.is_le(a, c) == True{} : Bool}:
  %e : {Nat.is_le(a, _) == True{} : Bool}
  p

def Nat.is_le_eq_l(a: Nat, b: Nat, c: Nat, e: {b == c : Nat},
    p: {Nat.is_le(b, a) == True{} : Bool}) ->
  {Nat.is_le(c, a) == True{} : Bool}:
  %e : {Nat.is_le(_, a) == True{} : Bool}
  p

# 8. From `m < n <= 1+fuel` conclude `m <= fuel`, the fuel arithmetic of the
# recursive solver.
def Nat.le_fuel(+m: Nat, +n: Nat, +fuel: Nat,
    lt: {Nat.is_lt(m, n) == True{} : Bool},
    le: {Nat.is_le(n, 1n+fuel) == True{} : Bool}) ->
  {Nat.is_le(m, fuel) == True{} : Bool}:
  Nat.is_le_of_lt_succ(m, fuel,
    Nat.is_lt_le_trans(m, n, 1n+fuel, lt, le))

# 9. Propositional forms of the numeric equalities.
def NatPrf.is_eq_refl(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      NatPrf.is_eq_refl(p)

def NatPrf.succ_disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def NatPrf.zero_ne_succ(n: Nat, e: {0n == 1n+n : Nat}) -> Empty:
  e2 = Equal.sym(Nat, 0n, 1n+n, e)
  %e2 : NatPrf.succ_disc(_)
  Unit{}

def NatPrf.is_eq_true(a: Nat, b: Nat,
    e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, Logic.Proof.false_ne_true(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, Logic.Proof.false_ne_true(e))
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, n => 1n+n, ap, bp, NatPrf.is_eq_true(ap, bp, e))

def NatPrf.is_eq_sym(+a: Nat, +b: Nat,
    e: {Nat.is_eq(a, b) == True{} : Bool}) ->
  {Nat.is_eq(b, a) == True{} : Bool}:
  +ab = NatPrf.is_eq_true(a, b, e)
  %Equal.sym(Nat, a, b, ab) : {Nat.is_eq(b, _) == True{} : Bool}
  NatPrf.is_eq_refl(b)

# 10. The predecessor, to cancel a successor on both sides of an equality.
def NatPrf.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def NatPrf.pred_succ(a: Nat, b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, NatPrf.pred, 1n+a, 1n+b, e)

# 11. Addition on the left, for regrouping sums of costs.
def NatPrf.add_succ(a: Nat, b: Nat) ->
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %NatPrf.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def NatPrf.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %NatPrf.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def NatPrf.add_assoc(a: Nat, b: Nat, c: Nat) ->
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                 Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)),
                 NatPrf.add_assoc(p, b, c))

def NatPrf.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, NatPrf.add_zero(b))
    case 1n++p:
      e1 = Equal.cong(Nat, Nat, x => Nat.add(1n, x),
             Nat.add(p, b), Nat.add(b, p), NatPrf.add_comm(p, b))
      e2 = Equal.sym(Nat, Nat.add(b, 1n+p), Nat.add(1n, Nat.add(b, p)),
             NatPrf.add_succ(b, p))
      Equal.trans(Nat, Nat.add(1n+p, b), Nat.add(1n, Nat.add(b, p)),
                  Nat.add(b, 1n+p), e1, e2)

# (a + b) + (c + d) = (a + c) + (b + d).
def NatPrf.add4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) ->
  {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  e1 = NatPrf.add_assoc(a, b, Nat.add(c, d))
  i1 = Equal.sym(Nat, Nat.add(Nat.add(b, c), d), Nat.add(b, Nat.add(c, d)),
                 NatPrf.add_assoc(b, c, d))
  i2 = Equal.cong(Nat, Nat, x => Nat.add(x, d),
                  Nat.add(b, c), Nat.add(c, b), NatPrf.add_comm(b, c))
  i3 = NatPrf.add_assoc(c, b, d)
  inner = Equal.trans(Nat, Nat.add(b, Nat.add(c, d)), Nat.add(Nat.add(b, c), d),
                      Nat.add(c, Nat.add(b, d)), i1,
                      Equal.trans(Nat, Nat.add(Nat.add(b, c), d),
                                  Nat.add(Nat.add(c, b), d),
                                  Nat.add(c, Nat.add(b, d)), i2, i3))
  e2 = Equal.cong(Nat, Nat, x => Nat.add(a, x),
                  Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), inner)
  e3 = Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)),
                 Nat.add(a, Nat.add(c, Nat.add(b, d))),
                 NatPrf.add_assoc(a, c, Nat.add(b, d)))
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)),
              Nat.add(a, Nat.add(b, Nat.add(c, d))),
              Nat.add(Nat.add(a, c), Nat.add(b, d)), e1,
              Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))),
                          Nat.add(a, Nat.add(c, Nat.add(b, d))),
                          Nat.add(Nat.add(a, c), Nat.add(b, d)), e2, e3))
