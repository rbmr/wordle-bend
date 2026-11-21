# Arithmetic for decimal numerals.
import Base
import ./logic.bend as L
import ./nat.bend as NP

# --- from exp3

# Minimal arithmetic copied from PROOF.bend for the experiment.
def AddS.add_succ(a: Nat, b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %AddS.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def AddS.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %AddS.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def AddS.add_one(+a: Nat) -> {Nat.add(a, 1n) == 1n+a : Nat}:
  e1 = AddS.add_succ(a, 0n)
  e2 = Equal.cong(Nat, Nat, m => 1n+m, Nat.add(a, 0n), a, AddS.add_zero(a))
  Equal.trans(Nat, Nat.add(a, 1n), 1n+Nat.add(a, 0n), 1n+a, e1, e2)

def AddS.add_assoc(a: Nat, b: Nat, c: Nat) ->
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                 Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)),
                 AddS.add_assoc(p, b, c))

def AddS.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, AddS.add_zero(b))
    case 1n++p:
      e1 = Equal.cong(Nat, Nat, x => Nat.add(1n, x),
             Nat.add(p, b), Nat.add(b, p), AddS.add_comm(p, b))
      e2 = Equal.sym(Nat, Nat.add(b, 1n+p), Nat.add(1n, Nat.add(b, p)),
             AddS.add_succ(b, p))
      Equal.trans(Nat, Nat.add(1n+p, b), Nat.add(1n, Nat.add(b, p)),
                  Nat.add(b, 1n+p), e1, e2)

def AddS.regroup(+a: Nat, +b: Nat, +c: Nat, +d: Nat) ->
  {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  e1 = AddS.add_assoc(a, b, Nat.add(c, d))
  i1 = Equal.sym(Nat, Nat.add(Nat.add(b, c), d), Nat.add(b, Nat.add(c, d)),
                 AddS.add_assoc(b, c, d))
  i2 = Equal.cong(Nat, Nat, x => Nat.add(x, d),
                  Nat.add(b, c), Nat.add(c, b), AddS.add_comm(b, c))
  i3 = AddS.add_assoc(c, b, d)
  inner = Equal.trans(Nat, Nat.add(b, Nat.add(c, d)), Nat.add(Nat.add(b, c), d),
                      Nat.add(c, Nat.add(b, d)), i1,
                      Equal.trans(Nat, Nat.add(Nat.add(b, c), d),
                                  Nat.add(Nat.add(c, b), d),
                                  Nat.add(c, Nat.add(b, d)), i2, i3))
  e2 = Equal.cong(Nat, Nat, x => Nat.add(a, x),
                  Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), inner)
  e3 = Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)),
                 Nat.add(a, Nat.add(c, Nat.add(b, d))),
                 AddS.add_assoc(a, c, Nat.add(b, d)))
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)),
              Nat.add(a, Nat.add(b, Nat.add(c, d))),
              Nat.add(Nat.add(a, c), Nat.add(b, d)), e1,
              Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))),
                          Nat.add(a, Nat.add(c, Nat.add(b, d))),
                          Nat.add(Nat.add(a, c), Nat.add(b, d)), e2, e3))

def MulS.mul_add(+a: Nat, +b: Nat, +c: Nat) ->
  {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      e1 = Equal.cong(Nat, Nat, x => Nat.add(Nat.add(b, c), x),
             Nat.mul(p, Nat.add(b, c)), Nat.add(Nat.mul(p, b), Nat.mul(p, c)),
             MulS.mul_add(p, b, c))
      e2 = AddS.regroup(b, c, Nat.mul(p, b), Nat.mul(p, c))
      Equal.trans(Nat, Nat.mul(1n+p, Nat.add(b, c)),
                  Nat.add(Nat.add(b, c), Nat.add(Nat.mul(p, b), Nat.mul(p, c))),
                  Nat.add(Nat.add(b, Nat.mul(p, b)), Nat.add(c, Nat.mul(p, c))),
                  e1, e2)

def MulS.mul_one(a: Nat) -> {Nat.mul(a, 1n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                 Nat.mul(p, 1n), p, MulS.mul_one(p))

def MulS.mul_ten_succ(+x: Nat) ->
  {Nat.mul(10n, Nat.add(x, 1n)) == Nat.add(Nat.mul(10n, x), 10n) : Nat}:
  e1 = MulS.mul_add(10n, x, 1n)
  e2 = Equal.cong(Nat, Nat, y => Nat.add(Nat.mul(10n, x), y),
                  Nat.mul(10n, 1n), 10n, MulS.mul_one(10n))
  Equal.trans(Nat, Nat.mul(10n, Nat.add(x, 1n)),
              Nat.add(Nat.mul(10n, x), Nat.mul(10n, 1n)),
              Nat.add(Nat.mul(10n, x), 10n), e1, e2)

# --- from exp4

def DivS.sum10(p: Nat & Nat) -> Nat:
  (q, r) = p
  Nat.add(Nat.mul(10n, q), r)

def DivS.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# m + r = 9 gives r < 10.
def DivS.r_lt(+a: Nat, +b: Nat, +e: {Nat.add(a, b) == 9n : Nat}) ->
  {Nat.is_lt(b, 10n) == True{} : Bool}:
  p1 = NP.Nat.is_lt_succ_of_le(b, Nat.add(a, b), NP.Nat.is_le_add_self_l(a, b))
  e2 = Equal.cong(Nat, Bool, x => Nat.is_lt(b, 1n+x), Nat.add(a, b), 9n, e)
  Equal.trans(Bool, Nat.is_lt(b, 10n), Nat.is_lt(b, 1n+Nat.add(a, b)),
              True{}, Equal.sym(Bool, Nat.is_lt(b, 1n+Nat.add(a, b)), Nat.is_lt(b, 10n), e2), p1)

# 10*(1+d) = 10d+10
def DivS.mul_ten_one_add(+d: Nat) ->
  {Nat.mul(10n, Nat.add(1n, d)) == Nat.add(Nat.mul(10n, d), 10n) : Nat}:
  e1 = MulS.mul_add(10n, 1n, d)
  e2 = Equal.cong(Nat, Nat, y => Nat.add(y, Nat.mul(10n, d)),
                  Nat.mul(10n, 1n), 10n, MulS.mul_one(10n))
  e3 = AddS.add_comm(10n, Nat.mul(10n, d))
  Equal.trans(Nat, Nat.mul(10n, Nat.add(1n, d)),
              Nat.add(Nat.mul(10n, 1n), Nat.mul(10n, d)),
              Nat.add(Nat.mul(10n, d), 10n),
              Equal.trans(Nat, Nat.mul(10n, Nat.add(1n, d)),
                          Nat.add(Nat.mul(10n, 1n), Nat.mul(10n, d)),
                          Nat.add(10n, Nat.mul(10n, d)), e1, e2),
              e3)

# ((10*(1+d))+0)+p = (10d+10)+p
def DivS.m0_lhs(+d: Nat, +p: Nat) ->
  {Nat.add(Nat.add(Nat.mul(10n, Nat.add(1n, d)), 0n), p)
    == Nat.add(Nat.add(Nat.mul(10n, d), 10n), p) : Nat}:
  m1 = DivS.mul_ten_one_add(d)
  e1 = Equal.cong(Nat, Nat, x => Nat.add(Nat.add(x, 0n), p),
                  Nat.mul(10n, Nat.add(1n, d)), Nat.add(Nat.mul(10n, d), 10n), m1)
  e2 = Equal.cong(Nat, Nat, y => Nat.add(y, p),
                  Nat.add(Nat.add(Nat.mul(10n, d), 10n), 0n),
                  Nat.add(Nat.mul(10n, d), 10n),
                  AddS.add_zero(Nat.add(Nat.mul(10n, d), 10n)))
  Equal.trans(Nat,
              Nat.add(Nat.add(Nat.mul(10n, Nat.add(1n, d)), 0n), p),
              Nat.add(Nat.add(Nat.add(Nat.mul(10n, d), 10n), 0n), p),
              Nat.add(Nat.add(Nat.mul(10n, d), 10n), p), e1, e2)

# (10d+10)+p = (10d+9)+(1+p)
def DivS.m0_rhs(+d: Nat, +p: Nat) ->
  {Nat.add(Nat.add(Nat.mul(10n, d), 10n), p)
    == Nat.add(Nat.add(Nat.mul(10n, d), 9n), Nat.add(1n, p)) : Nat}:
  +A : Nat = Nat.mul(10n, d)
  h1 : {Nat.add(9n, Nat.add(1n, p)) == Nat.add(10n, p) : Nat} = {==}
  h2 = Equal.cong(Nat, Nat, x => Nat.add(A, x), Nat.add(9n, Nat.add(1n, p)), Nat.add(10n, p), h1)
  h3 = AddS.add_assoc(A, 9n, Nat.add(1n, p))
  h4 = AddS.add_assoc(A, 10n, p)
  Equal.trans(Nat, Nat.add(Nat.add(A, 10n), p), Nat.add(A, Nat.add(10n, p)),
              Nat.add(Nat.add(A, 9n), Nat.add(1n, p)),
              h4,
              Equal.trans(Nat, Nat.add(A, Nat.add(10n, p)),
                          Nat.add(A, Nat.add(9n, Nat.add(1n, p))),
                          Nat.add(Nat.add(A, 9n), Nat.add(1n, p)),
                          Equal.sym(Nat, Nat.add(A, Nat.add(9n, Nat.add(1n, p))),
                                    Nat.add(A, Nat.add(10n, p)), h2),
                          Equal.sym(Nat, Nat.add(Nat.add(A, 9n), Nat.add(1n, p)),
                                    Nat.add(A, Nat.add(9n, Nat.add(1n, p))), h3)))

def DivS.m0(+d: Nat, +r: Nat, +p: Nat, +e: {r == 9n : Nat}) ->
  {Nat.add(Nat.add(Nat.mul(10n, Nat.add(1n, d)), 0n), p)
    == Nat.add(Nat.add(Nat.mul(10n, d), r), Nat.add(1n, p)) : Nat}:
  h9 = Equal.trans(Nat,
         Nat.add(Nat.add(Nat.mul(10n, Nat.add(1n, d)), 0n), p),
         Nat.add(Nat.add(Nat.mul(10n, d), 10n), p),
         Nat.add(Nat.add(Nat.mul(10n, d), 9n), Nat.add(1n, p)),
         DivS.m0_lhs(d, p), DivS.m0_rhs(d, p))
  hcong = Equal.cong(Nat, Nat,
            x => Nat.add(Nat.add(Nat.mul(10n, d), x), Nat.add(1n, p)),
            r, 9n, e)
  Equal.trans(Nat,
              Nat.add(Nat.add(Nat.mul(10n, Nat.add(1n, d)), 0n), p),
              Nat.add(Nat.add(Nat.mul(10n, d), 9n), Nat.add(1n, p)),
              Nat.add(Nat.add(Nat.mul(10n, d), r), Nat.add(1n, p)),
              h9, Equal.sym(Nat,
                Nat.add(Nat.add(Nat.mul(10n, d), r), Nat.add(1n, p)),
                Nat.add(Nat.add(Nat.mul(10n, d), 9n), Nat.add(1n, p)), hcong))

def DivS.m1(+d: Nat, +r: Nat, +p: Nat) ->
  {Nat.add(Nat.add(Nat.mul(10n, d), Nat.add(1n, r)), p)
    == Nat.add(Nat.add(Nat.mul(10n, d), r), Nat.add(1n, p)) : Nat}:
  +A : Nat = Nat.mul(10n, d)
  h1 = Equal.cong(Nat, Nat, x => Nat.add(x, p),
                  Nat.add(A, Nat.add(1n, r)), Nat.add(1n, Nat.add(A, r)),
                  AddS.add_succ(A, r))
  h2 = AddS.add_assoc(1n, Nat.add(A, r), p)
  h3 = Equal.sym(Nat, Nat.add(Nat.add(A, r), Nat.add(1n, p)),
                 Nat.add(1n, Nat.add(Nat.add(A, r), p)),
                 AddS.add_succ(Nat.add(A, r), p))
  Equal.trans(Nat, Nat.add(Nat.add(A, Nat.add(1n, r)), p),
              Nat.add(1n, Nat.add(Nat.add(A, r), p)),
              Nat.add(Nat.add(A, r), Nat.add(1n, p)),
              Equal.trans(Nat, Nat.add(Nat.add(A, Nat.add(1n, r)), p),
                          Nat.add(Nat.add(1n, Nat.add(A, r)), p),
                          Nat.add(1n, Nat.add(Nat.add(A, r), p)), h1, h2),
              h3)

def DivS.prem_m1(+mp: Nat, +r: Nat, +inv: {Nat.add(Nat.add(1n, mp), r) == 9n : Nat}) ->
  {Nat.add(mp, Nat.add(1n, r)) == 9n : Nat}:
  p1 = Equal.cong(Nat, Nat, DivS.pred, Nat.add(1n, Nat.add(mp, r)), 9n, inv)
  Equal.trans(Nat, Nat.add(mp, Nat.add(1n, r)), Nat.add(1n, Nat.add(mp, r)), 9n,
              AddS.add_succ(mp, r),
              Equal.cong(Nat, Nat, x => Nat.add(1n, x), Nat.add(mp, r), 8n, p1))

def DivS.spec_eq(n: Nat, m: Nat, +d: Nat, +r: Nat,
    +inv: {Nat.add(m, r) == 9n : Nat}) ->
  {DivS.sum10(Nat.divmod.go(n, m, d, r))
    == Nat.add(Nat.add(Nat.mul(10n, d), r), n) : Nat}:
  match n m:
    case 0n mm:
      +x : Nat = Nat.add(Nat.mul(10n, d), r)
      Equal.sym(Nat, Nat.add(x, 0n), x, AddS.add_zero(x))
    case 1n++p 0n:
      ih = DivS.spec_eq(p, r, Nat.add(1n, d), 0n,
                        Equal.trans(Nat, Nat.add(r, 0n), r, 9n, AddS.add_zero(r), inv))
      Equal.trans(Nat, DivS.sum10(Nat.divmod.go(p, r, Nat.add(1n, d), 0n)),
                  Nat.add(Nat.add(Nat.mul(10n, Nat.add(1n, d)), 0n), p),
                  Nat.add(Nat.add(Nat.mul(10n, d), r), Nat.add(1n, p)),
                  ih, DivS.m0(d, r, p, inv))
    case 1n++p 1n++mp:
      ih = DivS.spec_eq(p, mp, d, Nat.add(1n, r), DivS.prem_m1(mp, r, inv))
      Equal.trans(Nat, DivS.sum10(Nat.divmod.go(p, mp, d, Nat.add(1n, r))),
                  Nat.add(Nat.add(Nat.mul(10n, d), Nat.add(1n, r)), p),
                  Nat.add(Nat.add(Nat.mul(10n, d), r), Nat.add(1n, p)),
                  ih, DivS.m1(d, r, p))

def DivS.spec_bound(n: Nat, m: Nat, +d: Nat, +r: Nat,
    +inv: {Nat.add(m, r) == 9n : Nat}) ->
  {Nat.is_lt(Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)), 10n) == True{} : Bool}:
  match n m:
    case 0n mm:
      DivS.r_lt(mm, r, inv)
    case 1n++p 0n:
      DivS.spec_bound(p, r, Nat.add(1n, d), 0n,
                      Equal.trans(Nat, Nat.add(r, 0n), r, 9n, AddS.add_zero(r), inv))
    case 1n++p 1n++mp:
      DivS.spec_bound(p, mp, d, Nat.add(1n, r), DivS.prem_m1(mp, r, inv))

# --- from exp5

# a + b = a + c gives b = c.
def Cancel.add_l(a: Nat, b: Nat, c: Nat,
    e: {Nat.add(a, b) == Nat.add(a, c) : Nat}) -> {b == c : Nat}:
  match a:
    case 0n:
      e
    case 1n+p:
      Cancel.add_l(p, b, c,
        Equal.cong(Nat, Nat, DivS.pred, Nat.add(1n+p, b), Nat.add(1n+p, c), e))

# r < k excludes r = k + z.
def Small.lt_ne_add(+k: Nat, +r: Nat, +z: Nat,
    lt: {Nat.is_lt(r, k) == True{} : Bool},
    e: {r == Nat.add(k, z) : Nat}) -> Empty:
  match k r:
    case 0n rr:
      NP.Nat.not_lt_zero(rr, lt)
    case 1n+kp 0n:
      NP.NatPrf.zero_ne_succ(Nat.add(kp, z), e)
    case 1n+kp 1n+rp:
      Small.lt_ne_add(kp, rp, z, lt,
        Equal.cong(Nat, Nat, DivS.pred, Nat.add(1n, rp),
                   Nat.add(Nat.add(1n, kp), z), e))

# r < 10 excludes r = 10 + z.
def Small.lt_ten_ne(+r: Nat, +z: Nat,
    lt: {Nat.is_lt(r, 10n) == True{} : Bool},
    e: {r == Nat.add(10n, z) : Nat}) -> Empty:
  Small.lt_ne_add(10n, r, z, lt, e)

# 10*(1+v) + d = 10 + (10*v + d).
def Small.mul_ten_succ_add(+v: Nat, +d: Nat) ->
  {Nat.add(Nat.mul(10n, Nat.add(1n, v)), d)
    == Nat.add(10n, Nat.add(Nat.mul(10n, v), d)) : Nat}:
  e1 = DivS.mul_ten_one_add(v)
  e2 = Equal.cong(Nat, Nat, x => Nat.add(x, d),
                  Nat.mul(10n, Nat.add(1n, v)), Nat.add(Nat.mul(10n, v), 10n), e1)
  e3 = AddS.add_comm(Nat.mul(10n, v), 10n)
  e4 = Equal.cong(Nat, Nat, x => Nat.add(x, d),
                  Nat.add(Nat.mul(10n, v), 10n), Nat.add(10n, Nat.mul(10n, v)), e3)
  e5 = AddS.add_assoc(10n, Nat.mul(10n, v), d)
  Equal.trans(Nat,
              Nat.add(Nat.mul(10n, Nat.add(1n, v)), d),
              Nat.add(Nat.add(10n, Nat.mul(10n, v)), d),
              Nat.add(10n, Nat.add(Nat.mul(10n, v), d)),
              Equal.trans(Nat,
                Nat.add(Nat.mul(10n, Nat.add(1n, v)), d),
                Nat.add(Nat.add(Nat.mul(10n, v), 10n), d),
                Nat.add(Nat.add(10n, Nat.mul(10n, v)), d), e2, e4),
              e5)

def Small.pred_n(n: Nat, x: Nat) -> Nat:
  match n:
    case 0n:
      x
    case 1n+p:
      Small.pred_n(p, DivS.pred(x))

def Small.strip10(+x: Nat) -> {Small.pred_n(10n, Nat.add(10n, x)) == x : Nat}:
  {==}

# q = v from 10q + r = 10v + d with both remainders below ten.
def Small.quot_eq(q: Nat, v: Nat, +r: Nat, +d: Nat,
    ltr: {Nat.is_lt(r, 10n) == True{} : Bool},
    ltd: {Nat.is_lt(d, 10n) == True{} : Bool},
    +e: {Nat.add(Nat.mul(10n, q), r) == Nat.add(Nat.mul(10n, v), d) : Nat}) ->
  {q == v : Nat}:
  match q v:
    case 0n 0n:
      {==}
    case 0n 1n++vp:
      e1p = Equal.trans(Nat, r,
             Nat.add(Nat.mul(10n, Nat.add(1n, vp)), d),
             Nat.add(10n, Nat.add(Nat.mul(10n, vp), d)),
             e, Small.mul_ten_succ_add(vp, d))
      Empty.absurd({0n == 1n+vp : Nat},
        Small.lt_ten_ne(r, Nat.add(Nat.mul(10n, vp), d), ltr, e1p))
    case 1n++qp 0n:
      e1p = Equal.trans(Nat, d,
             Nat.add(Nat.mul(10n, Nat.add(1n, qp)), r),
             Nat.add(10n, Nat.add(Nat.mul(10n, qp), r)),
             Equal.sym(Nat, Nat.add(Nat.mul(10n, Nat.add(1n, qp)), r),
                       Nat.add(Nat.mul(10n, 0n), d), e),
             Small.mul_ten_succ_add(qp, r))
      Empty.absurd({1n+qp == 0n : Nat},
        Small.lt_ten_ne(d, Nat.add(Nat.mul(10n, qp), r), ltd, e1p))
    case 1n++qp 1n++vp:
      e1 = Small.mul_ten_succ_add(qp, r)
      e2 = Small.mul_ten_succ_add(vp, d)
      e1p = Equal.trans(Nat, Nat.add(10n, Nat.add(Nat.mul(10n, qp), r)),
              Nat.add(Nat.mul(10n, Nat.add(1n, qp)), r),
              Nat.add(Nat.mul(10n, Nat.add(1n, vp)), d),
              Equal.sym(Nat, Nat.add(Nat.mul(10n, Nat.add(1n, qp)), r),
                        Nat.add(10n, Nat.add(Nat.mul(10n, qp), r)), e1),
              e)
      e2p = Equal.trans(Nat, Nat.add(10n, Nat.add(Nat.mul(10n, qp), r)),
               Nat.add(Nat.mul(10n, Nat.add(1n, vp)), d),
               Nat.add(10n, Nat.add(Nat.mul(10n, vp), d)), e1p, e2)
      e3p = Equal.cong(Nat, Nat, x => Small.pred_n(10n, x),
                       Nat.add(10n, Nat.add(Nat.mul(10n, qp), r)),
                       Nat.add(10n, Nat.add(Nat.mul(10n, vp), d)), e2p)
      e4p = Equal.trans(Nat, Nat.add(Nat.mul(10n, qp), r),
               Small.pred_n(10n, Nat.add(10n, Nat.add(Nat.mul(10n, qp), r))),
               Nat.add(Nat.mul(10n, vp), d),
               Equal.sym(Nat, Small.pred_n(10n, Nat.add(10n, Nat.add(Nat.mul(10n, qp), r))),
                         Nat.add(Nat.mul(10n, qp), r),
                         Small.strip10(Nat.add(Nat.mul(10n, qp), r))),
               Equal.trans(Nat,
                 Small.pred_n(10n, Nat.add(10n, Nat.add(Nat.mul(10n, qp), r))),
                 Small.pred_n(10n, Nat.add(10n, Nat.add(Nat.mul(10n, vp), d))),
                 Nat.add(Nat.mul(10n, vp), d),
                 e3p,
                 Small.strip10(Nat.add(Nat.mul(10n, vp), d))))
      Equal.cong(Nat, Nat, x => Nat.add(1n, x), qp, vp,
                 Small.quot_eq(qp, vp, r, d, ltr, ltd, e4p))

# r = d from 10q + r = 10q + d.
def Small.rem_eq(+q: Nat, +v: Nat, +r: Nat, +d: Nat,
    ltr: {Nat.is_lt(r, 10n) == True{} : Bool},
    ltd: {Nat.is_lt(d, 10n) == True{} : Bool},
    +e: {Nat.add(Nat.mul(10n, q), r) == Nat.add(Nat.mul(10n, v), d) : Nat}) ->
  {r == d : Nat}:
  qv = Small.quot_eq(q, v, r, d, ltr, ltd, e)
  e2 = Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(10n, x), r), q, v, qv)
  e3 = Equal.trans(Nat, Nat.add(Nat.mul(10n, v), r), Nat.add(Nat.mul(10n, q), r),
                   Nat.add(Nat.mul(10n, v), d), Equal.sym(Nat,
                     Nat.add(Nat.mul(10n, q), r), Nat.add(Nat.mul(10n, v), r), e2), e)
  Cancel.add_l(Nat.mul(10n, v), r, d, e3)

# --- from exp6

def PairProof.eta(-A: Type, -B: Type, p: A & B) ->
  {p == (Pair.fst(A, B, p), Pair.snd(A, B, p)) : A & B}:
  match p:
    case (a, b):
      {==}

def PairProof.pair_cong(-A: Type, -B: Type,
    x1: A, y1: B, x2: A, y2: B,
    e1: {x1 == x2 : A}, e2: {y1 == y2 : B}) -> {(x1, y1) == (x2, y2) : A & B}:
  e3 = Equal.cong(A, A & B, x => (x, y1), x1, x2, e1)
  e4 = Equal.cong(B, A & B, y => (x2, y), y1, y2, e2)
  Equal.trans(A & B, (x1, y1), (x2, y1), (x2, y2), e3, e4)

# --- from exp7

def DivS.sum10_form(p: Nat & Nat) ->
  {DivS.sum10(p) == Nat.add(Nat.mul(10n, Pair.fst(Nat, Nat, p)),
                             Pair.snd(Nat, Nat, p)) : Nat}:
  match p:
    case (q, r):
      {==}

def DivS.divmod10(+v: Nat, +d: Nat,
    +ltd: {Nat.is_lt(d, 10n) == True{} : Bool}) ->
  {Nat.divmod(Nat.add(Nat.mul(10n, v), d), 10n) == (v, d) : Nat & Nat}:
  +a : Nat = Nat.add(Nat.mul(10n, v), d)
  +er0 : {DivS.sum10(Nat.divmod(a, 10n)) == a : Nat} = DivS.spec_eq(a, 9n, 0n, 0n, {==})
  +er : {Nat.add(Nat.mul(10n, Pair.fst(Nat, Nat, Nat.divmod(a, 10n))),
               Pair.snd(Nat, Nat, Nat.divmod(a, 10n))) == a : Nat} =
    Equal.trans(Nat, Nat.add(Nat.mul(10n, Pair.fst(Nat, Nat, Nat.divmod(a, 10n))),
                             Pair.snd(Nat, Nat, Nat.divmod(a, 10n))),
                DivS.sum10(Nat.divmod(a, 10n)), a,
                Equal.sym(Nat, DivS.sum10(Nat.divmod(a, 10n)),
                  Nat.add(Nat.mul(10n, Pair.fst(Nat, Nat, Nat.divmod(a, 10n))),
                          Pair.snd(Nat, Nat, Nat.divmod(a, 10n))),
                  DivS.sum10_form(Nat.divmod(a, 10n))), er0)
  +lr : {Nat.is_lt(Pair.snd(Nat, Nat, Nat.divmod(a, 10n)), 10n) == True{} : Bool} =
    DivS.spec_bound(a, 9n, 0n, 0n, {==})
  +qv : {Pair.fst(Nat, Nat, Nat.divmod(a, 10n)) == v : Nat} =
    Small.quot_eq(Pair.fst(Nat, Nat, Nat.divmod(a, 10n)), v,
                    Pair.snd(Nat, Nat, Nat.divmod(a, 10n)), d, lr, ltd, er)
  +rd : {Pair.snd(Nat, Nat, Nat.divmod(a, 10n)) == d : Nat} =
    Small.rem_eq(Pair.fst(Nat, Nat, Nat.divmod(a, 10n)), v,
                   Pair.snd(Nat, Nat, Nat.divmod(a, 10n)), d, lr, ltd, er)
  Equal.trans(Nat & Nat, Nat.divmod(a, 10n),
              (Pair.fst(Nat, Nat, Nat.divmod(a, 10n)), Pair.snd(Nat, Nat, Nat.divmod(a, 10n))),
              (v, d),
              PairProof.eta(Nat, Nat, Nat.divmod(a, 10n)),
              PairProof.pair_cong(Nat, Nat,
                Pair.fst(Nat, Nat, Nat.divmod(a, 10n)),
                Pair.snd(Nat, Nat, Nat.divmod(a, 10n)), v, d, qv, rd))

# --- from exp9

# 10n = n + 9n
def Ord.ten_eq(n: Nat) -> {Nat.mul(10n, n) == Nat.add(n, Nat.mul(9n, n)) : Nat}:
  {==}

# 9n + n = 10n
def Ord.nine_add(+n: Nat) -> {Nat.add(Nat.mul(9n, n), n) == Nat.mul(10n, n) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(9n, n), n), Nat.add(n, Nat.mul(9n, n)),
              Nat.mul(10n, n), AddS.add_comm(Nat.mul(9n, n), n), Ord.ten_eq(n))

def Ord.le_ten_add_one(+n: Nat) -> {Nat.is_le(n, Nat.add(Nat.mul(10n, n), 1n)) == True{} : Bool}:
  e1 = NP.Nat.is_le_add_self_l(Nat.mul(9n, n), n)
  e2 = Equal.cong(Nat, Bool, x => Nat.is_le(n, x),
                  Nat.add(Nat.mul(9n, n), n), Nat.mul(10n, n), Ord.nine_add(n))
  e3 = NP.Nat.is_le_add_self_l(1n, Nat.mul(10n, n))
  e4 = Equal.cong(Nat, Bool, x => Nat.is_le(Nat.mul(10n, n), x),
                  Nat.add(1n, Nat.mul(10n, n)), Nat.add(Nat.mul(10n, n), 1n),
                  AddS.add_comm(1n, Nat.mul(10n, n)))
  e5 = NP.Nat.is_le_trans(n, Nat.mul(10n, n), Nat.add(Nat.mul(10n, n), 1n),
                          Equal.trans(Bool, Nat.is_le(n, Nat.mul(10n, n)),
                                      Nat.is_le(n, Nat.add(Nat.mul(9n, n), n)), True{},
                                      Equal.sym(Bool, Nat.is_le(n, Nat.add(Nat.mul(9n, n), n)),
                                                Nat.is_le(n, Nat.mul(10n, n)), e2), e1),
                          Equal.trans(Bool, Nat.is_le(Nat.mul(10n, n), Nat.add(Nat.mul(10n, n), 1n)),
                                      Nat.is_le(Nat.mul(10n, n), Nat.add(1n, Nat.mul(10n, n))), True{},
                                      Equal.sym(Bool, Nat.is_le(Nat.mul(10n, n), Nat.add(1n, Nat.mul(10n, n))),
                                                Nat.is_le(Nat.mul(10n, n), Nat.add(Nat.mul(10n, n), 1n)), e4), e3))
  e5

# --- from exp10

# 10*(1+n) = 10 + 10*n
def Ord.ten_mul_add(+n: Nat) ->
  {Nat.mul(10n, Nat.add(1n, n)) == Nat.add(10n, Nat.mul(10n, n)) : Nat}:
  Equal.trans(Nat, Nat.mul(10n, Nat.add(1n, n)), Nat.add(Nat.mul(10n, n), 10n),
              Nat.add(10n, Nat.mul(10n, n)),
              DivS.mul_ten_one_add(n), AddS.add_comm(Nat.mul(10n, n), 10n))

# (9 + 9n) + (1 + n) = 10 + 10n
def Ord.sum_9_1(+n: Nat) ->
  {Nat.add(Nat.add(9n, Nat.mul(9n, n)), Nat.add(1n, n))
    == Nat.add(10n, Nat.mul(10n, n)) : Nat}:
  e1 = Equal.sym(Nat, Nat.add(Nat.add(9n, 1n), Nat.add(Nat.mul(9n, n), n)),
                 Nat.add(Nat.add(9n, Nat.mul(9n, n)), Nat.add(1n, n)),
                 AddS.regroup(9n, 1n, Nat.mul(9n, n), n))
  e2 = Equal.cong(Nat, Nat, x => Nat.add(10n, x),
                  Nat.add(Nat.mul(9n, n), n), Nat.mul(10n, n),
                  Ord.nine_add(n))
  Equal.trans(Nat, Nat.add(Nat.add(9n, Nat.mul(9n, n)), Nat.add(1n, n)),
              Nat.add(Nat.add(9n, 1n), Nat.add(Nat.mul(9n, n), n)),
              Nat.add(10n, Nat.mul(10n, n)), e1, e2)

# (8 + 9n) + (2 + n) = 10 + 10n
def Ord.sum_8_2(+n: Nat) ->
  {Nat.add(Nat.add(8n, Nat.mul(9n, n)), Nat.add(2n, n))
    == Nat.add(10n, Nat.mul(10n, n)) : Nat}:
  e1 = Equal.sym(Nat, Nat.add(Nat.add(8n, 2n), Nat.add(Nat.mul(9n, n), n)),
                 Nat.add(Nat.add(8n, Nat.mul(9n, n)), Nat.add(2n, n)),
                 AddS.regroup(8n, 2n, Nat.mul(9n, n), n))
  e2 = Equal.cong(Nat, Nat, x => Nat.add(10n, x),
                  Nat.add(Nat.mul(9n, n), n), Nat.mul(10n, n),
                  Ord.nine_add(n))
  Equal.trans(Nat, Nat.add(Nat.add(8n, Nat.mul(9n, n)), Nat.add(2n, n)),
              Nat.add(Nat.add(8n, 2n), Nat.add(Nat.mul(9n, n), n)),
              Nat.add(10n, Nat.mul(10n, n)), e1, e2)

# --- from exp11

# n <= 10n for n > 0.
def Ord.le_ten(+n: Nat, pos: {Nat.is_lt(0n, n) == True{} : Bool}) ->
  {Nat.is_le(n, Nat.mul(10n, n)) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(0n, Nat.mul(10n, 0n)) == True{} : Bool}, L.Proof.false_ne_true(pos))
    case 1n++np:
      e_le = NP.Nat.is_le_add_self_l(Nat.add(9n, Nat.mul(9n, np)), Nat.add(1n, np))
      e_eq = Ord.sum_9_1(np)
      e_ten = Ord.ten_mul_add(np)
      h1 = Equal.cong(Nat, Bool, x => Nat.is_le(Nat.add(1n, np), x),
                      Nat.add(Nat.add(9n, Nat.mul(9n, np)), Nat.add(1n, np)),
                      Nat.add(10n, Nat.mul(10n, np)), e_eq)
      h2 = Equal.cong(Nat, Bool, x => Nat.is_le(Nat.add(1n, np), x),
                      Nat.add(10n, Nat.mul(10n, np)), Nat.mul(10n, Nat.add(1n, np)),
                      Equal.sym(Nat, Nat.mul(10n, Nat.add(1n, np)),
                                Nat.add(10n, Nat.mul(10n, np)), e_ten))
      h = Equal.trans(Bool, Nat.is_le(Nat.add(1n, np), Nat.add(Nat.add(9n, Nat.mul(9n, np)), Nat.add(1n, np))),
                      Nat.is_le(Nat.add(1n, np), Nat.add(10n, Nat.mul(10n, np))),
                      Nat.is_le(Nat.add(1n, np), Nat.mul(10n, Nat.add(1n, np))), h1, h2)
      Equal.trans(Bool, Nat.is_le(Nat.add(1n, np), Nat.mul(10n, Nat.add(1n, np))),
                  Nat.is_le(Nat.add(1n, np), Nat.add(Nat.add(9n, Nat.mul(9n, np)), Nat.add(1n, np))),
                  True{}, Equal.sym(Bool,
                    Nat.is_le(Nat.add(1n, np), Nat.add(Nat.add(9n, Nat.mul(9n, np)), Nat.add(1n, np))),
                    Nat.is_le(Nat.add(1n, np), Nat.mul(10n, Nat.add(1n, np))), h), e_le)

# n + 1 <= 10n for n > 0.
def Ord.le_succ_ten(+n: Nat, pos: {Nat.is_lt(0n, n) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(n, 1n), Nat.mul(10n, n)) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(Nat.add(0n, 1n), Nat.mul(10n, 0n)) == True{} : Bool}, L.Proof.false_ne_true(pos))
    case 1n++np:
      e_le = NP.Nat.is_le_add_self_l(Nat.add(8n, Nat.mul(9n, np)), Nat.add(2n, np))
      e_eq = Ord.sum_8_2(np)
      e_ten = Ord.ten_mul_add(np)
      h1 = Equal.cong(Nat, Bool, x => Nat.is_le(Nat.add(2n, np), x),
                      Nat.add(Nat.add(8n, Nat.mul(9n, np)), Nat.add(2n, np)),
                      Nat.add(10n, Nat.mul(10n, np)), e_eq)
      h2 = Equal.cong(Nat, Bool, x => Nat.is_le(Nat.add(2n, np), x),
                      Nat.add(10n, Nat.mul(10n, np)), Nat.mul(10n, Nat.add(1n, np)),
                      Equal.sym(Nat, Nat.mul(10n, Nat.add(1n, np)),
                                Nat.add(10n, Nat.mul(10n, np)), e_ten))
      h = Equal.trans(Bool, Nat.is_le(Nat.add(2n, np), Nat.add(Nat.add(8n, Nat.mul(9n, np)), Nat.add(2n, np))),
                      Nat.is_le(Nat.add(2n, np), Nat.add(10n, Nat.mul(10n, np))),
                      Nat.is_le(Nat.add(2n, np), Nat.mul(10n, Nat.add(1n, np))), h1, h2)
      e_a = AddS.add_assoc(1n, np, 1n)
      e_b = Equal.cong(Nat, Nat, x => Nat.add(1n, x), Nat.add(np, 1n), Nat.add(1n, np),
                       AddS.add_one(np))
      e_n = Equal.trans(Nat, Nat.add(Nat.add(1n, np), 1n), Nat.add(1n, Nat.add(np, 1n)),
                        Nat.add(2n, np), e_a, e_b)
      e_n2 = Equal.cong(Nat, Bool, x => Nat.is_le(x, Nat.mul(10n, Nat.add(1n, np))),
                        Nat.add(2n, np), Nat.add(Nat.add(1n, np), 1n),
                        Equal.sym(Nat, Nat.add(Nat.add(1n, np), 1n), Nat.add(2n, np), e_n))
      Equal.trans(Bool, Nat.is_le(Nat.add(Nat.add(1n, np), 1n), Nat.mul(10n, Nat.add(1n, np))),
                  Nat.is_le(Nat.add(2n, np), Nat.mul(10n, Nat.add(1n, np))),
                  True{}, Equal.sym(Bool, Nat.is_le(Nat.add(2n, np), Nat.mul(10n, Nat.add(1n, np))),
                                    Nat.is_le(Nat.add(Nat.add(1n, np), 1n), Nat.mul(10n, Nat.add(1n, np))), e_n2),
                  Equal.trans(Bool, Nat.is_le(Nat.add(2n, np), Nat.mul(10n, Nat.add(1n, np))),
                              Nat.is_le(Nat.add(2n, np), Nat.add(Nat.add(8n, Nat.mul(9n, np)), Nat.add(2n, np))),
                              True{}, Equal.sym(Bool,
                                Nat.is_le(Nat.add(2n, np), Nat.add(Nat.add(8n, Nat.mul(9n, np)), Nat.add(2n, np))),
                                Nat.is_le(Nat.add(2n, np), Nat.mul(10n, Nat.add(1n, np))), h), e_le))


# --- quotient of a positive number is below it

# q + 1 <= 10q + r for q > 0.
def Ord.le_succ_quot(+q: Nat, +r: Nat, pos: {Nat.is_lt(0n, q) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(q, 1n), Nat.add(Nat.mul(10n, q), r)) == True{} : Bool}:
  e1 = Ord.le_succ_ten(q, pos)
  e2 = NP.Nat.is_le_add_self_l(r, Nat.mul(10n, q))
  e3 = Equal.cong(Nat, Bool, x => Nat.is_le(Nat.mul(10n, q), x),
                  Nat.add(r, Nat.mul(10n, q)), Nat.add(Nat.mul(10n, q), r),
                  AddS.add_comm(r, Nat.mul(10n, q)))
  e2b = Equal.trans(Bool, Nat.is_le(Nat.mul(10n, q), Nat.add(Nat.mul(10n, q), r)),
                    Nat.is_le(Nat.mul(10n, q), Nat.add(r, Nat.mul(10n, q))), True{},
                    Equal.sym(Bool, Nat.is_le(Nat.mul(10n, q), Nat.add(r, Nat.mul(10n, q))),
                              Nat.is_le(Nat.mul(10n, q), Nat.add(Nat.mul(10n, q), r)), e3), e2)
  NP.Nat.is_le_trans(Nat.add(q, 1n), Nat.mul(10n, q), Nat.add(Nat.mul(10n, q), r), e1, e2b)

# --- divmod by ten

def ShowS.fst(+n: Nat) -> Nat:
  Pair.fst(Nat, Nat, Nat.divmod(n, 10n))

def ShowS.snd(+n: Nat) -> Nat:
  Pair.snd(Nat, Nat, Nat.divmod(n, 10n))

def ShowS.dm_eq(+n: Nat) ->
  {Nat.divmod(n, 10n) == (ShowS.fst(n), ShowS.snd(n)) : Nat & Nat}:
  PairProof.eta(Nat, Nat, Nat.divmod(n, 10n))

def ShowS.dm_sum(+n: Nat) ->
  {Nat.add(Nat.mul(10n, ShowS.fst(n)), ShowS.snd(n)) == n : Nat}:
  e0 = DivS.spec_eq(n, 9n, 0n, 0n, {==})
  Equal.trans(Nat, Nat.add(Nat.mul(10n, ShowS.fst(n)), ShowS.snd(n)),
              DivS.sum10(Nat.divmod.go(n, 9n, 0n, 0n)), n,
              Equal.sym(Nat, DivS.sum10(Nat.divmod.go(n, 9n, 0n, 0n)),
                        Nat.add(Nat.mul(10n, Pair.fst(Nat, Nat, Nat.divmod.go(n, 9n, 0n, 0n))),
                                Pair.snd(Nat, Nat, Nat.divmod.go(n, 9n, 0n, 0n))),
                        DivS.sum10_form(Nat.divmod.go(n, 9n, 0n, 0n))),
              e0)

def ShowS.dm_snd_lt(+n: Nat) ->
  {Nat.is_lt(ShowS.snd(n), 10n) == True{} : Bool}:
  DivS.spec_bound(n, 9n, 0n, 0n, {==})

# q < 10q + r = n for a positive quotient q.
def ShowS.div_lt_self_pos(+n: Nat, +q: Nat, +r: Nat,
    pos: {Nat.is_lt(0n, q) == True{} : Bool},
    sum: {Nat.add(Nat.mul(10n, q), r) == n : Nat}) ->
  {Nat.is_lt(q, n) == True{} : Bool}:
  e1 = Ord.le_succ_quot(q, r, pos)
  e2 = Equal.cong(Nat, Bool, x => Nat.is_le(Nat.add(q, 1n), x),
                  Nat.add(Nat.mul(10n, q), r), n, sum)
  e3 = Equal.trans(Bool, Nat.is_le(Nat.add(q, 1n), n),
                   Nat.is_le(Nat.add(q, 1n), Nat.add(Nat.mul(10n, q), r)), True{},
                   Equal.sym(Bool, Nat.is_le(Nat.add(q, 1n), Nat.add(Nat.mul(10n, q), r)),
                             Nat.is_le(Nat.add(q, 1n), n), e2), e1)
  ltq1cong = Equal.cong(Nat, Bool, x => Nat.is_lt(q, x),
                        Nat.add(1n, q), Nat.add(q, 1n),
                        Equal.sym(Nat, Nat.add(q, 1n), Nat.add(1n, q), AddS.add_one(q)))
  ltq1 = Equal.trans(Bool, Nat.is_lt(q, Nat.add(q, 1n)), Nat.is_lt(q, Nat.add(1n, q)), True{},
                     Equal.sym(Bool, Nat.is_lt(q, Nat.add(1n, q)), Nat.is_lt(q, Nat.add(q, 1n)), ltq1cong),
                     NP.Nat.is_lt_succ_self(q))
  NP.Nat.is_lt_le_trans(q, Nat.add(q, 1n), n, ltq1, e3)

def ShowS.div_lt_self_go(+n: Nat, q: Nat, +r: Nat,
    pos: {Nat.is_lt(0n, n) == True{} : Bool},
    sum: {Nat.add(Nat.mul(10n, q), r) == n : Nat}) ->
  {Nat.is_lt(q, n) == True{} : Bool}:
  match q:
    case 0n:
      pos
    case 1n++qp:
      ShowS.div_lt_self_pos(n, 1n+qp, r, {==}, sum)

def ShowS.div_lt_self(+n: Nat, pos: {Nat.is_lt(0n, n) == True{} : Bool}) ->
  {Nat.is_lt(ShowS.fst(n), n) == True{} : Bool}:
  ShowS.div_lt_self_go(n, ShowS.fst(n), ShowS.snd(n), pos, ShowS.dm_sum(n))
