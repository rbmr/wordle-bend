# The arithmetic of the class cost bound.
#
# A guess of a candidate list `S` splits `S` into feedback classes, all strictly
# shorter than `S`. If a class of size `m` costs at most `m*m`, the node costs at
# most `|S| + (|S|-1)*|S| = |S|*|S|`, which is below the solver's infinity
# `|C|*|C|+1`. This module supplies the multiplication lemmas that argument
# needs on top of `nat.bend`: distributivity, commutativity, monotonicity, and
# the fold of a multiplied list.
import Base
import ./logic.bend as Logic
import ./nat.bend as NatProof

# The predecessor, used as the size of the largest proper class.
def CB.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# The plain sum of a list of numbers.
def CB.sum(+xs: +List<Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(h, CB.sum(t))

# Every number of a list times a fixed factor.
def CB.mulAll(+q: Nat, +xs: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Nat.mul(h, q) <> CB.mulAll(q, t)

# (a + b) + (c + d) = (a + c) + (b + d).
def CB.add4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) ->
  {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  e1 = NatProof.NatPrf.add_assoc(a, b, Nat.add(c, d))
  i1 = Equal.sym(Nat, Nat.add(Nat.add(b, c), d), Nat.add(b, Nat.add(c, d)),
                 NatProof.NatPrf.add_assoc(b, c, d))
  i2 = Equal.cong(Nat, Nat, x => Nat.add(x, d),
                  Nat.add(b, c), Nat.add(c, b), NatProof.NatPrf.add_comm(b, c))
  i3 = NatProof.NatPrf.add_assoc(c, b, d)
  inner = Equal.trans(Nat, Nat.add(b, Nat.add(c, d)), Nat.add(Nat.add(b, c), d),
                      Nat.add(c, Nat.add(b, d)), i1,
                      Equal.trans(Nat, Nat.add(Nat.add(b, c), d),
                                  Nat.add(Nat.add(c, b), d),
                                  Nat.add(c, Nat.add(b, d)), i2, i3))
  e2 = Equal.cong(Nat, Nat, x => Nat.add(a, x),
                  Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), inner)
  e3 = Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)),
                 Nat.add(a, Nat.add(c, Nat.add(b, d))),
                 NatProof.NatPrf.add_assoc(a, c, Nat.add(b, d)))
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)),
              Nat.add(a, Nat.add(b, Nat.add(c, d))),
              Nat.add(Nat.add(a, c), Nat.add(b, d)), e1,
              Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))),
                          Nat.add(a, Nat.add(c, Nat.add(b, d))),
                          Nat.add(Nat.add(a, c), Nat.add(b, d)), e2, e3))

# a * (b + c) = a*b + a*c.
def CB.mul_add(+a: Nat, +b: Nat, +c: Nat) ->
  {Nat.mul(a, Nat.add(b, c))
   == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      +ih : {Nat.mul(p, Nat.add(b, c))
             == Nat.add(Nat.mul(p, b), Nat.mul(p, c)) : Nat} =
        CB.mul_add(p, b, c)
      +e1 : {Nat.add(Nat.add(b, c), Nat.mul(p, Nat.add(b, c)))
             == Nat.add(Nat.add(b, c), Nat.add(Nat.mul(p, b), Nat.mul(p, c)))
             : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(Nat.add(b, c), x),
                   Nat.mul(p, Nat.add(b, c)),
                   Nat.add(Nat.mul(p, b), Nat.mul(p, c)), ih)
      +e2 : {Nat.add(Nat.add(b, c), Nat.add(Nat.mul(p, b), Nat.mul(p, c)))
             == Nat.add(Nat.add(b, Nat.mul(p, b)), Nat.add(c, Nat.mul(p, c)))
             : Nat} =
        CB.add4(b, c, Nat.mul(p, b), Nat.mul(p, c))
      Equal.trans(Nat, Nat.add(Nat.add(b, c), Nat.mul(p, Nat.add(b, c))),
                  Nat.add(Nat.add(b, c), Nat.add(Nat.mul(p, b), Nat.mul(p, c))),
                  Nat.add(Nat.add(b, Nat.mul(p, b)), Nat.add(c, Nat.mul(p, c))),
                  e1, e2)

# (a + b) * c = a*c + b*c.
def CB.mul_add_l(+a: Nat, +b: Nat, +c: Nat) ->
  {Nat.mul(Nat.add(a, b), c)
   == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      +ih : {Nat.mul(Nat.add(p, b), c)
             == Nat.add(Nat.mul(p, c), Nat.mul(b, c)) : Nat} =
        CB.mul_add_l(p, b, c)
      +e1 : {Nat.add(c, Nat.mul(Nat.add(p, b), c))
             == Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(c, x),
                   Nat.mul(Nat.add(p, b), c),
                   Nat.add(Nat.mul(p, c), Nat.mul(b, c)), ih)
      +e2 : {Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c)))
             == Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)) : Nat} =
        Equal.sym(Nat, Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)),
                  Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))),
                  NatProof.NatPrf.add_assoc(c, Nat.mul(p, c), Nat.mul(b, c)))
      Equal.trans(Nat, Nat.add(c, Nat.mul(Nat.add(p, b), c)),
                  Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))),
                  Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)), e1, e2)

# a * 0 = 0.
def CB.mul_zero(a: Nat) -> {Nat.mul(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      +ih : {Nat.mul(p, 0n) == 0n : Nat} = CB.mul_zero(p)
      Equal.cong(Nat, Nat, x => Nat.add(0n, x), Nat.mul(p, 0n), 0n, ih)

# 0 * a = 0.
def CB.mul_zero_l(+a: Nat) -> {Nat.mul(0n, a) == 0n : Nat}:
  {==}

# a * 1 = a.
def CB.mul_one(a: Nat) -> {Nat.mul(a, 1n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      +ih : {Nat.mul(p, 1n) == p : Nat} = CB.mul_one(p)
      +e : {Nat.add(1n, Nat.mul(p, 1n)) == Nat.add(1n, p) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(1n, x), Nat.mul(p, 1n), p, ih)
      e

# 1 * a = a.
def CB.mul_one_l(+a: Nat) -> {Nat.mul(1n, a) == a : Nat}:
  NatProof.NatPrf.add_zero(a)

# a * b = b * a.
def CB.mul_comm(a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.mul(b, 0n), 0n, CB.mul_zero(b))
    case 1n++p:
      +ih : {Nat.mul(p, b) == Nat.mul(b, p) : Nat} = CB.mul_comm(p, b)
      +e1 : {Nat.mul(b, 1n+p) == Nat.add(Nat.mul(b, 1n), Nat.mul(b, p)) : Nat} =
        CB.mul_add(b, 1n, p)
      +h1 : {Nat.add(b, Nat.mul(p, b))
             == Nat.add(Nat.mul(b, 1n), Nat.mul(b, p)) : Nat} =
        Equal.trans(Nat, Nat.add(b, Nat.mul(p, b)),
                    Nat.add(Nat.mul(b, 1n), Nat.mul(p, b)),
                    Nat.add(Nat.mul(b, 1n), Nat.mul(b, p)),
                    Equal.cong(Nat, Nat, x => Nat.add(x, Nat.mul(p, b)),
                               b, Nat.mul(b, 1n), Equal.sym(Nat, Nat.mul(b, 1n), b, CB.mul_one(b))),
                    Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(b, 1n), x),
                               Nat.mul(p, b), Nat.mul(b, p), ih))
      Equal.trans(Nat, Nat.add(b, Nat.mul(p, b)),
                  Nat.add(Nat.mul(b, 1n), Nat.mul(b, p)),
                  Nat.mul(b, 1n+p), h1,
                  Equal.sym(Nat, Nat.mul(b, 1n+p),
                            Nat.add(Nat.mul(b, 1n), Nat.mul(b, p)), e1))

# a <= b and c <= d give a + c <= b + d.
def CB.is_le_add(+a: Nat, +b: Nat, +c: Nat, +d: Nat,
    ab: {Nat.is_le(a, b) == True{} : Bool},
    cd: {Nat.is_le(c, d) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  +e1 : {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool} =
    NatProof.Nat.is_le_add_r(a, b, c, ab)
  +e2 : {Nat.is_le(Nat.add(b, c), Nat.add(b, d)) == True{} : Bool} =
    NatProof.Nat.is_le_add_l(c, d, b, cd)
  NatProof.Nat.is_le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), e1, e2)

# A pointwise order on two lists of the same length.
def CB.PointLe(+xs: +List<Nat>, +ys: +List<Nat>) -> Type:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          Unit
        case Con{y, yt}:
          Empty
    case Con{x, xt}:
      match ys:
        case Nil{}:
          Empty
        case Con{y, yt}:
          {Nat.is_le(x, y) == True{} : Bool} & CB.PointLe(xt, yt)

# The sum of a pointwise ordered pair of lists.
def CB.sum_le(+xs: +List<Nat>, +ys: +List<Nat>,
    p: CB.PointLe(xs, ys)) ->
  {Nat.is_le(CB.sum(xs), CB.sum(ys)) == True{} : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      NatProof.Nat.is_le_refl(0n)
    case Nil{} Con{y, yt}:
      match p:
    case Con{x, xt} Nil{}:
      match p:
    case Con{x, xt} Con{y, yt}:
      (ph, pt) = p
      +ih : {Nat.is_le(CB.sum(xt), CB.sum(yt)) == True{} : Bool} =
        CB.sum_le(xt, yt, pt)
      CB.is_le_add(x, y, CB.sum(xt), CB.sum(yt), ph, ih)

# Multiplication is monotone in its second argument.
def CB.is_le_mul_r(+a: Nat, +b: Nat, +c: Nat,
    +e: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Nat.is_le(Nat.mul(c, a), Nat.mul(c, b)) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+cp:
      +ih : {Nat.is_le(Nat.mul(cp, a), Nat.mul(cp, b)) == True{} : Bool} =
        CB.is_le_mul_r(a, b, cp, e)
      CB.is_le_add(a, b, Nat.mul(cp, a), Nat.mul(cp, b), e, ih)

# Multiplication is monotone in its first argument.
def CB.is_le_mul_l(a: Nat, b: Nat, +c: Nat,
    e: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      NatProof.Nat.is_le_zero_l(Nat.mul(1n+bp, c))
    case 1n++ap 0n:
      Empty.absurd({Nat.is_le(Nat.mul(1n+ap, c), Nat.mul(0n, c)) == True{} : Bool},
                   Logic.Proof.false_ne_true(e))
    case 1n++ap 1n++bp:
      +ih : {Nat.is_le(Nat.mul(ap, c), Nat.mul(bp, c)) == True{} : Bool} =
        CB.is_le_mul_l(ap, bp, c, e)
      CB.is_le_add(c, c, Nat.mul(ap, c), Nat.mul(bp, c), NatProof.Nat.is_le_refl(c), ih)

# The sum of a multiplied list.
def CB.sum_mul(+q: Nat, +xs: +List<Nat>) ->
  {CB.sum(CB.mulAll(q, xs)) == Nat.mul(CB.sum(xs), q) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      +ih : {CB.sum(CB.mulAll(q, t)) == Nat.mul(CB.sum(t), q) : Nat} =
        CB.sum_mul(q, t)
      +e1 : {Nat.add(Nat.mul(h, q), CB.sum(CB.mulAll(q, t)))
             == Nat.add(Nat.mul(h, q), Nat.mul(CB.sum(t), q)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(h, q), x),
                   CB.sum(CB.mulAll(q, t)), Nat.mul(CB.sum(t), q), ih)
      +e2 : {Nat.add(Nat.mul(h, q), Nat.mul(CB.sum(t), q))
             == Nat.mul(Nat.add(h, CB.sum(t)), q) : Nat} =
        Equal.sym(Nat, Nat.mul(Nat.add(h, CB.sum(t)), q),
                  Nat.add(Nat.mul(h, q), Nat.mul(CB.sum(t), q)),
                  CB.mul_add_l(h, CB.sum(t), q))
      Equal.trans(Nat, CB.sum(CB.mulAll(q, h <> t)),
                  Nat.add(Nat.mul(h, q), CB.sum(CB.mulAll(q, t))),
                  Nat.mul(CB.sum(h <> t), q), {==}, Equal.trans(Nat,
                    Nat.add(Nat.mul(h, q), CB.sum(CB.mulAll(q, t))),
                    Nat.add(Nat.mul(h, q), Nat.mul(CB.sum(t), q)),
                    Nat.mul(Nat.add(h, CB.sum(t)), q), e1, e2))

# The sum of an append.
def CB.sum_append(+xs: +List<Nat>, +ys: +List<Nat>) ->
  {CB.sum(List.append(&2, Nat, xs, ys))
   == Nat.add(CB.sum(xs), CB.sum(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      +ih : {CB.sum(List.append(&2, Nat, t, ys))
             == Nat.add(CB.sum(t), CB.sum(ys)) : Nat} =
        CB.sum_append(t, ys)
      +e1 : {Nat.add(h, CB.sum(List.append(&2, Nat, t, ys)))
             == Nat.add(h, Nat.add(CB.sum(t), CB.sum(ys))) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(h, x),
                   CB.sum(List.append(&2, Nat, t, ys)),
                   Nat.add(CB.sum(t), CB.sum(ys)), ih)
      +e2 : {Nat.add(h, Nat.add(CB.sum(t), CB.sum(ys)))
             == Nat.add(Nat.add(h, CB.sum(t)), CB.sum(ys)) : Nat} =
        Equal.sym(Nat, Nat.add(Nat.add(h, CB.sum(t)), CB.sum(ys)),
                  Nat.add(h, Nat.add(CB.sum(t), CB.sum(ys))),
                  NatProof.NatPrf.add_assoc(h, CB.sum(t), CB.sum(ys)))
      Equal.trans(Nat, Nat.add(h, CB.sum(List.append(&2, Nat, t, ys))),
                  Nat.add(h, Nat.add(CB.sum(t), CB.sum(ys))),
                  Nat.add(Nat.add(h, CB.sum(t)), CB.sum(ys)), e1, e2)

# A prefix costs no more than the whole list.
def CB.sum_prefix_le(+xs: +List<Nat>, +ys: +List<Nat>) ->
  {Nat.is_le(CB.sum(xs), CB.sum(List.append(&2, Nat, xs, ys))) == True{} : Bool}:
  +e : {Nat.add(CB.sum(xs), CB.sum(ys))
        == CB.sum(List.append(&2, Nat, xs, ys)) : Nat} =
    Equal.sym(Nat, CB.sum(List.append(&2, Nat, xs, ys)),
              Nat.add(CB.sum(xs), CB.sum(ys)), CB.sum_append(xs, ys))
  +h : {Nat.is_le(CB.sum(xs), Nat.add(CB.sum(ys), CB.sum(xs))) == True{} : Bool} =
    NatProof.Nat.is_le_add_self_l(CB.sum(ys), CB.sum(xs))
  +e2 : {Nat.add(CB.sum(ys), CB.sum(xs))
         == Nat.add(CB.sum(xs), CB.sum(ys)) : Nat} =
    NatProof.NatPrf.add_comm(CB.sum(ys), CB.sum(xs))
  NatProof.Nat.is_le_eq_r(CB.sum(xs), Nat.add(CB.sum(xs), CB.sum(ys)),
    CB.sum(List.append(&2, Nat, xs, ys)), e,
    NatProof.Nat.is_le_eq_r(CB.sum(xs), Nat.add(CB.sum(ys), CB.sum(xs)),
      Nat.add(CB.sum(xs), CB.sum(ys)), e2, h))

# m < n gives m <= pred n.
def CB.le_pred_of_lt(m: Nat, n: Nat,
    h: {Nat.is_lt(m, n) == True{} : Bool}) ->
  {Nat.is_le(m, CB.pred(n)) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(m, CB.pred(0n)) == True{} : Bool},
                   NatProof.Nat.not_lt_zero(m, h))
    case 1n+p:
      NatProof.Nat.is_le_of_lt_succ(m, p, h)

# A class cost bounded by its square and a size below n is bounded by size*pred n.
def CB.cost_le_size_pred(+m: Nat, +c: Nat, +n: Nat,
    sq: {Nat.is_le(c, Nat.mul(m, m)) == True{} : Bool},
    sm: {Nat.is_lt(m, n) == True{} : Bool}) ->
  {Nat.is_le(c, Nat.mul(m, CB.pred(n))) == True{} : Bool}:
  +mp : {Nat.is_le(m, CB.pred(n)) == True{} : Bool} =
    CB.le_pred_of_lt(m, n, sm)
  +h : {Nat.is_le(Nat.mul(m, m), Nat.mul(m, CB.pred(n))) == True{} : Bool} =
    CB.is_le_mul_r(m, CB.pred(n), m, mp)
  NatProof.Nat.is_le_trans(c, Nat.mul(m, m), Nat.mul(m, CB.pred(n)), sq, h)

# Pointwise `c <= m*q` over two equal-length lists.
def CB.PointLeMul(+q: Nat, +ms: +List<Nat>, +cs: +List<Nat>) -> Type:
  match ms:
    case Nil{}:
      match cs:
        case Nil{}:
          Unit
        case Con{c, ct}:
          Empty
    case Con{m, mt}:
      match cs:
        case Nil{}:
          Empty
        case Con{c, ct}:
          {Nat.is_le(c, Nat.mul(m, q)) == True{} : Bool}
          & CB.PointLeMul(q, mt, ct)

# The sum of pointwise bounded class costs.
def CB.sum_le_mul_sum(+q: Nat, +ms: +List<Nat>, +cs: +List<Nat>,
    p: CB.PointLeMul(q, ms, cs)) ->
  {Nat.is_le(CB.sum(cs), Nat.mul(CB.sum(ms), q)) == True{} : Bool}:
  match ms cs:
    case Nil{} Nil{}:
      NatProof.Nat.is_le_refl(0n)
    case Nil{} Con{c, ct}:
      match p:
    case Con{m, mt} Nil{}:
      match p:
    case Con{m, mt} Con{c, ct}:
      (ph, pt) = p
      +ih : {Nat.is_le(CB.sum(ct), Nat.mul(CB.sum(mt), q)) == True{} : Bool} =
        CB.sum_le_mul_sum(q, mt, ct, pt)
      +h1 : {Nat.is_le(Nat.add(c, CB.sum(ct)),
                Nat.add(Nat.mul(m, q), Nat.mul(CB.sum(mt), q))) == True{} : Bool} =
        CB.is_le_add(c, Nat.mul(m, q), CB.sum(ct), Nat.mul(CB.sum(mt), q), ph, ih)
      +e : {Nat.add(Nat.mul(m, q), Nat.mul(CB.sum(mt), q))
            == Nat.mul(Nat.add(m, CB.sum(mt)), q) : Nat} =
        Equal.sym(Nat, Nat.mul(Nat.add(m, CB.sum(mt)), q),
                  Nat.add(Nat.mul(m, q), Nat.mul(CB.sum(mt), q)),
                  CB.mul_add_l(m, CB.sum(mt), q))
      NatProof.Nat.is_le_eq_r(Nat.add(c, CB.sum(ct)),
        Nat.add(Nat.mul(m, q), Nat.mul(CB.sum(mt), q)),
        Nat.mul(Nat.add(m, CB.sum(mt)), q), e, h1)

# Pointwise `c <= m*pred n`: the shape the class bound consumes.
def CB.PointLeP(+n: Nat, +ms: +List<Nat>, +cs: +List<Nat>) -> Type:
  match ms:
    case Nil{}:
      match cs:
        case Nil{}:
          Unit
        case Con{c, ct}:
          Empty
    case Con{m, mt}:
      match cs:
        case Nil{}:
          Empty
        case Con{c, ct}:
          {Nat.is_le(c, Nat.mul(m, CB.pred(n))) == True{} : Bool}
          & CB.PointLeP(n, mt, ct)

# Read the class bound as the generic pointwise bound at `pred n`.
def CB.point_le_p_to_mul(n: Nat, +ms: +List<Nat>, +cs: +List<Nat>,
    p: CB.PointLeP(n, ms, cs)) -> CB.PointLeMul(CB.pred(n), ms, cs):
  match ms cs:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{c, ct}:
      match p:
    case Con{m, mt} Nil{}:
      match p:
    case Con{m, mt} Con{c, ct}:
      (ph, pt) = p
      (ph, CB.point_le_p_to_mul(n, mt, ct, pt))

# `pred` at a successor.
def CB.pred_succ(q: Nat) -> {CB.pred(1n+q) == q : Nat}:
  {==}

# `pred` at zero.
def CB.pred_zero() -> {CB.pred(0n) == 0n : Nat}:
  {==}

# a < a + 1.
def CB.lt_add_one(a: Nat) -> {Nat.is_lt(a, Nat.add(a, 1n)) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      CB.lt_add_one(p)

# The class bound: if the classes of a list of size n fit inside n and each
# class cost fits its own square, the node cost fits n*n.
def CB.bound(n: Nat, +ms: +List<Nat>, +cs: +List<Nat>,
    p: CB.PointLeP(n, ms, cs),
    +part: {Nat.is_le(CB.sum(ms), n) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(n, CB.sum(cs)), Nat.mul(n, n)) == True{} : Bool}:
  match n:
    case 0n:
      pm : CB.PointLeMul(CB.pred(0n), ms, cs) = CB.point_le_p_to_mul(0n, ms, cs, p)
      +h : {Nat.is_le(CB.sum(cs), Nat.mul(CB.sum(ms), CB.pred(0n))) == True{} : Bool} =
        CB.sum_le_mul_sum(CB.pred(0n), ms, cs, pm)
      +hq : {CB.pred(0n) == 0n : Nat} = CB.pred_zero()
      +h0 : {Nat.is_le(CB.sum(cs), Nat.mul(CB.sum(ms), 0n)) == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(CB.sum(cs),
          Nat.mul(CB.sum(ms), CB.pred(0n)), Nat.mul(CB.sum(ms), 0n),
          Equal.cong(Nat, Nat, x => Nat.mul(CB.sum(ms), x), CB.pred(0n), 0n, hq),
          h)
      NatProof.Nat.is_le_eq_r(CB.sum(cs), Nat.mul(CB.sum(ms), 0n), 0n,
        CB.mul_zero(CB.sum(ms)), h0)
    case 1n++q:
      pm : CB.PointLeMul(CB.pred(1n+q), ms, cs) = CB.point_le_p_to_mul(1n+q, ms, cs, p)
      +h : {Nat.is_le(CB.sum(cs), Nat.mul(CB.sum(ms), CB.pred(1n+q))) == True{} : Bool} =
        CB.sum_le_mul_sum(CB.pred(1n+q), ms, cs, pm)
      +hq : {CB.pred(1n+q) == q : Nat} = CB.pred_succ(q)
      +h0 : {Nat.is_le(CB.sum(cs), Nat.mul(CB.sum(ms), q)) == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(CB.sum(cs),
          Nat.mul(CB.sum(ms), CB.pred(1n+q)), Nat.mul(CB.sum(ms), q),
          Equal.cong(Nat, Nat, x => Nat.mul(CB.sum(ms), x), CB.pred(1n+q), q, hq),
          h)
      +h1 : {Nat.is_le(CB.sum(cs), Nat.mul(1n+q, q)) == True{} : Bool} =
        NatProof.Nat.is_le_trans(CB.sum(cs), Nat.mul(CB.sum(ms), q),
          Nat.mul(1n+q, q), h0,
          CB.is_le_mul_l(CB.sum(ms), 1n+q, q, part))
      +h2 : {Nat.is_le(Nat.add(1n+q, CB.sum(cs)),
                Nat.add(1n+q, Nat.mul(1n+q, q))) == True{} : Bool} =
        CB.is_le_add(1n+q, 1n+q, CB.sum(cs), Nat.mul(1n+q, q),
          NatProof.Nat.is_le_refl(1n+q), h1)
      +e0 : {Nat.add(1n+q, Nat.mul(1n+q, q))
             == Nat.add(1n+q, Nat.mul(q, 1n+q)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(1n+q, x),
                   Nat.mul(1n+q, q), Nat.mul(q, 1n+q), CB.mul_comm(1n+q, q))
      +e : {Nat.add(1n+q, Nat.mul(1n+q, q)) == Nat.mul(1n+q, 1n+q) : Nat} =
        Equal.trans(Nat, Nat.add(1n+q, Nat.mul(1n+q, q)),
                    Nat.add(1n+q, Nat.mul(q, 1n+q)),
                    Nat.mul(1n+q, 1n+q), e0, {==})
      NatProof.Nat.is_le_eq_r(Nat.add(1n+q, CB.sum(cs)),
        Nat.add(1n+q, Nat.mul(1n+q, q)), Nat.mul(1n+q, 1n+q), e, h2)

# Substitution in the arguments of `is_lt`.
def CB.lt_eq_r(a: Nat, b: Nat, c: Nat, e: {b == c : Nat},
    p: {Nat.is_lt(a, b) == True{} : Bool}) ->
  {Nat.is_lt(a, c) == True{} : Bool}:
  %e : {Nat.is_lt(a, _) == True{} : Bool}
  p

def CB.lt_eq_l(a: Nat, b: Nat, c: Nat, e: {b == c : Nat},
    p: {Nat.is_lt(b, a) == True{} : Bool}) ->
  {Nat.is_lt(c, a) == True{} : Bool}:
  %e : {Nat.is_lt(_, a) == True{} : Bool}
  p
