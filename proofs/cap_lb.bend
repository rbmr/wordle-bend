# The capacity lower bound of a class list.
#
# `src/solve_fast.bend` computes the capacity bound with a truncated sequence
# (`cap_go` keeps `min(n, 1 + k * cap)`), while `proofs/lb_capacity.bend`
# proves the soundness theorem for the untruncated sequence `G`. The first part
# of this module shows that the two functions agree.
import Base
import ../src/solve_fast.bend as SolveFast
import ../src/groups.bend as Groups
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./min.bend as Min
import ./classbound_nat.bend as CBN
import ./lb_capacity.bend as CapProof
import ./lb_capacity_sound.bend as LBS
import ./cover_list.bend as CoverList
import ./fast_cutoff.bend as FC
import ./fast_hist5.bend as FH

# ---------------------------------------------------------------------------
# Truncation helpers
# ---------------------------------------------------------------------------

# `min a b == a` when `a <= b`.
def CP.min_eq_l_go(+a: Nat, +b: Nat,
    r: {Nat.min(a, b) == a : Nat} | {Nat.min(a, b) == b : Nat},
    h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match r:
    case Inl{e}:
      e
    case Inr{+e2}:
      +hba : {Nat.is_le(b, a) == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(a, Nat.min(a, b), b, e2, Min.Nat.min_le_l(a, b))
      +eab : {a == b : Nat} = CoverList.Cover.is_le_antisym(a, b, h, hba)
      Equal.trans(Nat, Nat.min(a, b), b, a, e2, Equal.sym(Nat, a, b, eab))

def CP.min_eq_l(+a: Nat, +b: Nat,
    h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  CP.min_eq_l_go(a, b, Min.Nat.min_is_arg(a, b), h)

# `min a b == b` when `b <= a`.
def CP.min_eq_r_go(+a: Nat, +b: Nat,
    r: {Nat.min(a, b) == a : Nat} | {Nat.min(a, b) == b : Nat},
    h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.min(a, b) == b : Nat}:
  match r:
    case Inl{+e2}:
      +hab : {Nat.is_le(a, b) == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(b, Nat.min(a, b), a, e2, Min.Nat.min_le_r(a, b))
      +eba : {b == a : Nat} = CoverList.Cover.is_le_antisym(b, a, h, hab)
      Equal.trans(Nat, Nat.min(a, b), a, b, e2, Equal.sym(Nat, b, a, eba))
    case Inr{e}:
      e

def CP.min_eq_r(+a: Nat, +b: Nat,
    h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.min(a, b) == b : Nat}:
  CP.min_eq_r_go(a, b, Min.Nat.min_is_arg(a, b), h)

# `n - n == 0`.
def CP.sub_self(n: Nat) -> {Nat.sub(n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      CP.sub_self(p)

# `n - min(n, g) == n - g`.
def CP.sub_min_b(+n: Nat, +g: Nat, le: Bool,
    +e: {le == Nat.is_le(g, n) : Bool}) ->
  {Nat.sub(n, Nat.min(n, g)) == Nat.sub(n, g) : Nat}:
  match le:
    case True{}:
      +h : {Nat.is_le(g, n) == True{} : Bool} =
        Equal.sym(Bool, True{}, Nat.is_le(g, n), e)
      Equal.cong(Nat, Nat, x => Nat.sub(n, x), Nat.min(n, g), g,
        CP.min_eq_r(n, g, h))
    case False{}:
      +hf : {Nat.is_le(g, n) == False{} : Bool} =
        Equal.sym(Bool, False{}, Nat.is_le(g, n), e)
      +hlt : {Nat.is_lt(n, g) == True{} : Bool} = FC.FC.lt_of_le_false(g, n, hf)
      +hle : {Nat.is_le(n, g) == True{} : Bool} =
        NatProof.Nat.is_le_of_lt(n, g, hlt)
      +hn : {Nat.min(n, g) == n : Nat} = CP.min_eq_l(n, g, hle)
      Equal.trans(Nat, Nat.sub(n, Nat.min(n, g)), Nat.sub(n, n), Nat.sub(n, g),
        Equal.cong(Nat, Nat, x => Nat.sub(n, x), Nat.min(n, g), n, hn),
        Equal.trans(Nat, Nat.sub(n, n), 0n, Nat.sub(n, g),
          CP.sub_self(n),
          Equal.sym(Nat, Nat.sub(n, g), 0n,
            LBS.LBS.sub_eq_zero(n, g, hle))))

def CP.sub_min(+n: Nat, +g: Nat) ->
  {Nat.sub(n, Nat.min(n, g)) == Nat.sub(n, g) : Nat}:
  CP.sub_min_b(n, g, Nat.is_le(g, n), {==})

# `x <= 1 + (x + q * x)`.
def CP.le_one_add_mul(+q: Nat, +x: Nat) ->
  {Nat.is_le(x, Nat.add(1n, Nat.add(x, Nat.mul(q, x)))) == True{} : Bool}:
  +t : Nat = Nat.add(x, Nat.mul(q, x))
  +ht : {Nat.is_le(x, t) == True{} : Bool} =
    CBN.CB.is_le_add_self_r(x, Nat.mul(q, x))
  +ht2 : {Nat.is_le(t, Nat.add(1n, t)) == True{} : Bool} =
    NatProof.Nat.is_le_of_lt(t, Nat.add(1n, t),
      NatProof.Nat.is_lt_succ_self(t))
  NatProof.Nat.is_le_trans(x, t, Nat.add(1n, t), ht, ht2)

# `min(n, 1 + (x + q * x)) == n` when `n <= x`: the truncated sequence never
# grows past the candidate count.
def CP.min_mul_ge(+n: Nat, +q: Nat, +x: Nat,
    h: {Nat.is_le(n, x) == True{} : Bool}) ->
  {Nat.min(n, Nat.add(1n, Nat.add(x, Nat.mul(q, x)))) == n : Nat}:
  +t : Nat = Nat.add(x, Nat.mul(q, x))
  +hx : {Nat.is_le(x, Nat.add(1n, t)) == True{} : Bool} =
    CP.le_one_add_mul(q, x)
  CP.min_eq_l(n, Nat.add(1n, t),
    NatProof.Nat.is_le_trans(n, x, Nat.add(1n, t), h, hx))

# `min(n, 1 + k * min(n, g)) == min(n, 1 + k * g)`.
def CP.min_mul_trunc_b(+n: Nat, +k: Nat, +g: Nat, le: Bool,
    +e: {le == Nat.is_le(g, n) : Bool}) ->
  {Nat.min(n, Nat.add(1n, Nat.mul(k, Nat.min(n, g))))
   == Nat.min(n, Nat.add(1n, Nat.mul(k, g))) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      match le:
        case True{}:
          +h : {Nat.is_le(g, n) == True{} : Bool} =
            Equal.sym(Bool, True{}, Nat.is_le(g, n), e)
          Equal.cong(Nat, Nat,
            x => Nat.min(n, Nat.add(1n, Nat.add(x, Nat.mul(q, x)))),
            Nat.min(n, g), g, CP.min_eq_r(n, g, h))
        case False{}:
          +hf : {Nat.is_le(g, n) == False{} : Bool} =
            Equal.sym(Bool, False{}, Nat.is_le(g, n), e)
          +hlt : {Nat.is_lt(n, g) == True{} : Bool} = FC.FC.lt_of_le_false(g, n, hf)
          +hng : {Nat.min(n, g) == n : Nat} =
            CP.min_eq_l(n, g, NatProof.Nat.is_le_of_lt(n, g, hlt))
          +hnn : {Nat.min(n, Nat.add(1n, Nat.add(n, Nat.mul(q, n)))) == n : Nat} =
            CP.min_mul_ge(n, q, n, NatProof.Nat.is_le_refl(n))
          +hgg : {Nat.min(n, Nat.add(1n, Nat.add(g, Nat.mul(q, g)))) == n : Nat} =
            CP.min_mul_ge(n, q, g, NatProof.Nat.is_le_of_lt(n, g, hlt))
          +el : Nat =
            Nat.min(n, Nat.add(1n, Nat.add(Nat.min(n, g), Nat.mul(q, Nat.min(n, g)))))
          +em : Nat = Nat.min(n, Nat.add(1n, Nat.add(n, Nat.mul(q, n))))
          +er : Nat = Nat.min(n, Nat.add(1n, Nat.add(g, Nat.mul(q, g))))
          +emid : {el == em : Nat} =
            Equal.cong(Nat, Nat,
              x => Nat.min(n, Nat.add(1n, Nat.add(x, Nat.mul(q, x)))),
              Nat.min(n, g), n, hng)
          Equal.trans(Nat, el, n, er,
            Equal.trans(Nat, el, em, n, emid, hnn),
            Equal.sym(Nat, er, n, hgg))

def CP.min_mul_trunc(+n: Nat, +k: Nat, +g: Nat) ->
  {Nat.min(n, Nat.add(1n, Nat.mul(k, Nat.min(n, g))))
   == Nat.min(n, Nat.add(1n, Nat.mul(k, g))) : Nat}:
  CP.min_mul_trunc_b(n, k, g, Nat.is_le(g, n), {==})

# `(a + b) + c == b + (a + c)`.
def CP.add_rot(+a: Nat, +b: Nat, +c: Nat) ->
  {Nat.add(Nat.add(a, b), c) == Nat.add(b, Nat.add(a, c)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)),
    Nat.add(b, Nat.add(a, c)),
    NatProof.NatPrf.add_assoc(a, b, c),
    Equal.trans(Nat, Nat.add(a, Nat.add(b, c)),
      Nat.add(a, Nat.add(c, b)), Nat.add(b, Nat.add(a, c)),
      Equal.cong(Nat, Nat, x => Nat.add(a, x), Nat.add(b, c),
        Nat.add(c, b), NatProof.NatPrf.add_comm(b, c)),
      Equal.trans(Nat, Nat.add(a, Nat.add(c, b)), Nat.add(Nat.add(a, c), b),
        Nat.add(b, Nat.add(a, c)),
        Equal.sym(Nat, Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)),
          NatProof.NatPrf.add_assoc(a, c, b)),
        NatProof.NatPrf.add_comm(Nat.add(a, c), b))))

# ---------------------------------------------------------------------------
# The truncated sequence agrees with `G`
# ---------------------------------------------------------------------------

# The accumulator form of `SolveFast.cap_go`: after `rem` steps the
# accumulator is `acc + capSum(n, k, rem, j)`, provided the running cap is
# `min(n, G(k, j))`.
def CP.cap_go_eq(+rem: Nat, +n: Nat, +k: Nat, +j: Nat, +cap: Nat, +acc: Nat,
    +eq: {cap == Nat.min(n, CapProof.LB.G(k, j)) : Nat}) ->
  {SolveFast.cap_go(rem, n, k, cap, acc)
   == Nat.add(acc, CapProof.LB.capSum(n, k, rem, j)) : Nat}:
  match rem:
    case 0n:
      Equal.sym(Nat, Nat.add(acc, 0n), acc, NatProof.NatPrf.add_zero(acc))
    case 1n+p:
      +cap2 : Nat = Nat.min(n, Nat.add(1n, Nat.mul(k, cap)))
      +acc2 : Nat = Nat.add(Nat.sub(n, cap), acc)
      +eq2 : {cap2 == Nat.min(n, CapProof.LB.G(k, Nat.add(1n, j))) : Nat} =
        Equal.trans(Nat, cap2,
          Nat.min(n, Nat.add(1n, Nat.mul(k, Nat.min(n, CapProof.LB.G(k, j))))),
          Nat.min(n, CapProof.LB.G(k, Nat.add(1n, j))),
          Equal.cong(Nat, Nat,
            x => Nat.min(n, Nat.add(1n, Nat.mul(k, x))),
            cap, Nat.min(n, CapProof.LB.G(k, j)), eq),
          CP.min_mul_trunc(n, k, CapProof.LB.G(k, j)))
      +ih : {SolveFast.cap_go(p, n, k, cap2, acc2)
             == Nat.add(acc2, CapProof.LB.capSum(n, k, p, Nat.add(1n, j))) : Nat} =
        CP.cap_go_eq(p, n, k, Nat.add(1n, j), cap2, acc2, eq2)
      +esub : {Nat.sub(n, cap) == Nat.sub(n, CapProof.LB.G(k, j)) : Nat} =
        Equal.trans(Nat, Nat.sub(n, cap),
          Nat.sub(n, Nat.min(n, CapProof.LB.G(k, j))),
          Nat.sub(n, CapProof.LB.G(k, j)),
          Equal.cong(Nat, Nat, x => Nat.sub(n, x), cap,
            Nat.min(n, CapProof.LB.G(k, j)), eq),
          CP.sub_min(n, CapProof.LB.G(k, j)))
      +et : Nat = CapProof.LB.capSum(n, k, p, Nat.add(1n, j))
      +es : Nat = Nat.sub(n, CapProof.LB.G(k, j))
      +e1 : {Nat.add(acc2, et) == Nat.add(Nat.add(es, acc), et) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(x, et), acc2,
          Nat.add(es, acc),
          Equal.cong(Nat, Nat, x => Nat.add(x, acc), Nat.sub(n, cap), es, esub))
      +e2 : {Nat.add(Nat.add(es, acc), et)
             == Nat.add(acc, CapProof.LB.capSum(n, k, Nat.add(1n, p), j)) : Nat} =
        CP.add_rot(es, acc, et)
      Equal.trans(Nat, SolveFast.cap_go(p, n, k, cap2, acc2),
        Nat.add(acc2, et),
        Nat.add(acc, CapProof.LB.capSum(n, k, Nat.add(1n, p), j)),
        ih, Equal.trans(Nat, Nat.add(acc2, et), Nat.add(Nat.add(es, acc), et),
          Nat.add(acc, CapProof.LB.capSum(n, k, Nat.add(1n, p), j)), e1, e2))

# `G(k, 1) == 1`.
def CP.g_one(+k: Nat) -> {CapProof.LB.G(k, 1n) == 1n : Nat}:
  Equal.trans(Nat, CapProof.LB.G(k, 1n), Nat.add(1n, Nat.mul(k, 0n)), 1n,
    {==},
    Equal.trans(Nat, Nat.add(1n, Nat.mul(k, 0n)), Nat.add(1n, 0n), 1n,
      Equal.cong(Nat, Nat, x => Nat.add(1n, x), Nat.mul(k, 0n), 0n,
        CBN.CB.mul_zero(k)),
      NatProof.NatPrf.add_zero(1n)))

# `min(n, G(k, 1)) == 1` for `n` at least one.
def CP.min_g_one(+n: Nat, +k: Nat,
    h: {Nat.is_le(1n, n) == True{} : Bool}) ->
  {Nat.min(n, CapProof.LB.G(k, 1n)) == 1n : Nat}:
  Equal.trans(Nat, Nat.min(n, CapProof.LB.G(k, 1n)), Nat.min(n, 1n), 1n,
    Equal.cong(Nat, Nat, x => Nat.min(n, x), CapProof.LB.G(k, 1n), 1n,
      CP.g_one(k)),
    CP.min_eq_r(n, 1n, h))

# The two capacity bound functions agree.
def CP.capbound_eq(+n: Nat, +k: Nat) ->
  {SolveFast.capbound(n, k) == CapProof.LB.capbound(n, k) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      Equal.cong(Nat, Nat, x => Nat.add(1n+m, x), SolveFast.cap_go(1n+m, 1n+m, k, 1n, 0n),
        CapProof.LB.capSum(1n+m, k, 1n+m, 1n),
        CP.cap_go_eq(1n+m, 1n+m, k, 1n, 1n, 0n,
          Equal.sym(Nat, Nat.min(1n+m, CapProof.LB.G(k, 1n)), 1n,
            CP.min_g_one(1n+m, k, NatProof.Nat.is_le_succ(0n, m,
              NatProof.Nat.is_le_zero_l(m))))))
