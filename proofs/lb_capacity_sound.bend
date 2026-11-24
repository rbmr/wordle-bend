# Lower bounds for valid trees, part 8: the capacity bound is a lower bound.
#
# `lb_capacity.bend` defines
#
#   capbound(n, k) = n + sum over j = 1 .. n of (n - (1 + k + ... + k^(j-1)))+
#
# and proves the facts a pruning rule needs about the bound itself. This module
# proves the soundness statement: a valid tree whose nodes have at most `k`
# children costs at least `capbound(|S|, k)` on a candidate list `S` without
# duplicates.
#
# The argument is an induction over the tree, with the capacity sequence as the
# numeric input. A node of a valid tree costs one per candidate plus its
# children's depths, and the first-match partition of `lb_classes.bend` groups
# the candidates by the child that reaches them, so the node costs at least
#
#   |S| + sum over the classes of cost(child, words)
#
# With at most `k` children, each class of size `m` costs at least
# `capbound(m, k)` by the induction hypothesis, and the numeric step
#
#   capSum(n, k, n, 1) <= sum over the class sizes of capbound(m, k)
#
# is the level shift: level `j + 1` of the parent holds at most `1 + k * G_j`
# candidates, and the classes hold all but one of the parent's candidates, so
# the candidates level `j + 1` cannot hold are already counted by the classes
# one level up.
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ../src/groups.bend as Groups
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./classbound_nat.bend as CB
import ./lb_twice.bend as Twice
import ./lb_nodup.bend as NodupProof
import ./lb_classes.bend as Part
import ./nodecost.bend as NodeCost
import ./depth.bend as DepthProof
import ./lb_decomp.bend as Decomp
import ./lb_capacity.bend as Cap
import ./cover_list.bend as CoverList

# Every node has at most `k` children: the child-list half of the width
# condition the capacity bound needs.
def LBS.WidKids(+kids: +List<Tree.Child>, k: Nat) -> Type:
  match kids:
    case Nil{}:
      Unit
    case Con{c, rest}:
      match c:
        case Tree.Child{f, t}:
          LBS.Wid(t, k) & LBS.WidKids(rest, k)

# A tree all of whose nodes have at most `k` children.
def LBS.Wid(t: Tree.Tree, k: Nat) -> Type:
  match t:
    case Tree.Node{g, kids}:
      {Nat.is_le(List.length(&2, Tree.Child, kids), k) == True{} : Bool}
      & LBS.WidKids(kids, k)

# The width bound of one step of the class list.
def LBS.wid_classes_go(+kids: +List<Tree.Child>, k: Nat,
    w: LBS.WidKids(kids, k)) ->
  LBS.WidKids(kids, k):
  w

# A truncated subtraction is zero once nothing is left to subtract.
def LBS.sub_eq_zero(a: Nat, b: Nat,
    e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.sub(a, b) == 0n : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, Logic.Proof.false_ne_true(e))
    case 1n++ap 1n++bp:
      LBS.sub_eq_zero(ap, bp, e)

# A truncated subtraction is at most the number it subtracts from.
def LBS.sub_le_self(+a: Nat, +b: Nat) ->
  {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      NatProof.Nat.is_le_refl(0n)
    case 1n++ap 0n:
      NatProof.Nat.is_le_refl(1n+ap)
    case 1n++ap 1n++bp:
      NatProof.Nat.is_le_trans(Nat.sub(ap, bp), ap, 1n+ap,
        LBS.sub_le_self(ap, bp),
        NatProof.Nat.is_le_of_lt(ap, 1n+ap, NatProof.Nat.is_lt_succ_self(ap)))

# `x <= a + (x - a)`.
def LBS.le_add_sub(b: Nat, +a: Nat) ->
  {Nat.is_le(b, Nat.add(a, Nat.sub(b, a))) == True{} : Bool}:
  match b a:
    case 0n _:
      NatProof.Nat.is_le_zero_l(Nat.add(a, Nat.sub(0n, a)))
    case 1n++bp 0n:
      NatProof.Nat.is_le_refl(1n+bp)
    case 1n++bp 1n++ap:
      LBS.le_add_sub(bp, ap)

# From `a <= b + c` conclude `a - c <= b`.
def LBS.sub_le_of_le_add(+a: Nat, +b: Nat, +c: Nat,
    +e: {Nat.is_le(a, Nat.add(b, c)) == True{} : Bool}) ->
  {Nat.is_le(Nat.sub(a, c), b) == True{} : Bool}:
  match a c:
    case 0n _:
      NatProof.Nat.is_le_zero_l(b)
    case 1n++ap 0n:
      +e0 : {Nat.is_le(1n+ap, b) == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(1n+ap, Nat.add(b, 0n), b,
          NatProof.NatPrf.add_zero(b), e)
      NatProof.Nat.is_le_eq_l(b, 1n+ap, Nat.sub(1n+ap, 0n), {==}, e0)
    case 1n++ap 1n++cp:
      +e1 : {Nat.is_le(1n+ap, Nat.add(b, 1n+cp)) == True{} : Bool} = e
      +e2 : {Nat.is_le(1n+ap, 1n+Nat.add(b, cp)) == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(1n+ap, Nat.add(b, 1n+cp), 1n+Nat.add(b, cp),
          NatProof.NatPrf.add_succ(b, cp), e1)
      +e3 : {Nat.is_le(ap, Nat.add(b, cp)) == True{} : Bool} =
        NatProof.Nat.is_le_succ_inv(ap, Nat.add(b, cp), e2)
      LBS.sub_le_of_le_add(ap, b, cp, e3)

# `x - c` shrinks when `c` grows.
def LBS.sub_le_r(+a: Nat, +c1: Nat, +c2: Nat,
    h: {Nat.is_le(c2, c1) == True{} : Bool}) ->
  {Nat.is_le(Nat.sub(a, c1), Nat.sub(a, c2)) == True{} : Bool}:
  match a c1:
    case 0n _:
      NatProof.Nat.is_le_refl(0n)
    case 1n++ap 0n:
      +h0 : {Nat.is_le(c2, 0n) == True{} : Bool} = h
      +e : {c2 == 0n : Nat} = NatProof.Nat.eq_zero_of_le_zero(c2, h0)
      NatProof.Nat.is_le_eq_r(1n+ap, 1n+ap, Nat.sub(1n+ap, c2),
        Equal.sym(Nat, Nat.sub(1n+ap, c2), 1n+ap,
          Equal.trans(Nat, Nat.sub(1n+ap, c2), Nat.sub(1n+ap, 0n), 1n+ap,
            Equal.cong(Nat, Nat, x => Nat.sub(1n+ap, x), c2, 0n, e), {==})),
        NatProof.Nat.is_le_refl(1n+ap))
    case 1n++ap 1n++cp:
      match c2:
        case 0n:
          +sub_le : {Nat.is_le(Nat.sub(ap, cp), ap) == True{} : Bool} =
            LBS.sub_le_self(ap, cp)
          NatProof.Nat.is_le_trans(Nat.sub(ap, cp), ap, 1n+ap, sub_le,
            NatProof.Nat.is_le_of_lt(ap, 1n+ap, NatProof.Nat.is_lt_succ_self(ap)))
        case 1n++c2p:
          LBS.sub_le_r(ap, cp, c2p, NatProof.Nat.is_le_succ_inv(c2p, cp, h))

# The sum of the candidates each level cannot hold, over one level list.
def LBS.posSum(+xs: +List<Nat>, +a: Nat) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(Nat.sub(h, a), LBS.posSum(t, a))

# A list is at most its length times the level plus the candidates it cannot
# hold at that level, one term at a time.
def LBS.sum_le_mul_add(+xs: +List<Nat>, +a: Nat) ->
  {Nat.is_le(CB.CB.sum(xs),
             Nat.add(Nat.mul(List.length(&2, Nat, xs), a), LBS.posSum(xs, a)))
   == True{} : Bool}:
  match xs:
    case Nil{}:
      NatProof.Nat.is_le_refl(0n)
    case Con{h, t}:
      +ih : {Nat.is_le(CB.CB.sum(t),
                Nat.add(Nat.mul(List.length(&2, Nat, t), a), LBS.posSum(t, a)))
             == True{} : Bool} =
        LBS.sum_le_mul_add(t, a)
      +per : {Nat.is_le(h, Nat.add(a, Nat.sub(h, a))) == True{} : Bool} =
        LBS.le_add_sub(h, a)
      +comb : {Nat.is_le(Nat.add(h, CB.CB.sum(t)),
                  Nat.add(Nat.add(a, Nat.sub(h, a)),
                          Nat.add(Nat.mul(List.length(&2, Nat, t), a),
                                   LBS.posSum(t, a)))) == True{} : Bool} =
        CB.CB.is_le_add(h, Nat.add(a, Nat.sub(h, a)), CB.CB.sum(t),
          Nat.add(Nat.mul(List.length(&2, Nat, t), a), LBS.posSum(t, a)), per, ih)
      +emul : {Nat.mul(List.length(&2, Nat, h <> t), a)
               == Nat.add(a, Nat.mul(List.length(&2, Nat, t), a)) : Nat} =
        Equal.trans(Nat, Nat.mul(List.length(&2, Nat, h <> t), a),
          Nat.mul(Nat.add(1n, List.length(&2, Nat, t)), a),
          Nat.add(a, Nat.mul(List.length(&2, Nat, t), a)),
          {==},
          Equal.trans(Nat, Nat.mul(Nat.add(1n, List.length(&2, Nat, t)), a),
            Nat.add(Nat.mul(1n, a), Nat.mul(List.length(&2, Nat, t), a)),
            Nat.add(a, Nat.mul(List.length(&2, Nat, t), a)),
            CB.CB.mul_add_l(1n, List.length(&2, Nat, t), a),
            Equal.cong(Nat, Nat,
              x => Nat.add(x, Nat.mul(List.length(&2, Nat, t), a)),
              Nat.mul(1n, a), a, CB.CB.mul_one_l(a))))
      +e4 : {Nat.add(Nat.add(a, Nat.sub(h, a)),
                      Nat.add(Nat.mul(List.length(&2, Nat, t), a),
                              LBS.posSum(t, a)))
             == Nat.add(Nat.add(a, Nat.mul(List.length(&2, Nat, t), a)),
                        Nat.add(Nat.sub(h, a), LBS.posSum(t, a))) : Nat} =
        CB.CB.add4(a, Nat.sub(h, a), Nat.mul(List.length(&2, Nat, t), a),
                LBS.posSum(t, a))
      +etarget : {Nat.add(Nat.add(a, Nat.sub(h, a)),
                          Nat.add(Nat.mul(List.length(&2, Nat, t), a),
                                  LBS.posSum(t, a)))
                  == Nat.add(Nat.mul(List.length(&2, Nat, h <> t), a),
                             LBS.posSum(h <> t, a)) : Nat} =
        Equal.trans(Nat,
          Nat.add(Nat.add(a, Nat.sub(h, a)),
                  Nat.add(Nat.mul(List.length(&2, Nat, t), a), LBS.posSum(t, a))),
          Nat.add(Nat.add(a, Nat.mul(List.length(&2, Nat, t), a)),
                  Nat.add(Nat.sub(h, a), LBS.posSum(t, a))),
          Nat.add(Nat.mul(List.length(&2, Nat, h <> t), a), LBS.posSum(h <> t, a)),
          e4,
          Equal.sym(Nat,
            Nat.add(Nat.mul(List.length(&2, Nat, h <> t), a), LBS.posSum(h <> t, a)),
            Nat.add(Nat.add(a, Nat.mul(List.length(&2, Nat, t), a)),
                    Nat.add(Nat.sub(h, a), LBS.posSum(t, a))),
            Equal.cong(Nat, Nat,
              x => Nat.add(x, Nat.add(Nat.sub(h, a), LBS.posSum(t, a))),
              Nat.mul(List.length(&2, Nat, h <> t), a),
              Nat.add(a, Nat.mul(List.length(&2, Nat, t), a)), emul)))
      NatProof.Nat.is_le_eq_r(Nat.add(h, CB.CB.sum(t)),
        Nat.add(Nat.add(a, Nat.sub(h, a)),
                Nat.add(Nat.mul(List.length(&2, Nat, t), a), LBS.posSum(t, a))),
        Nat.add(Nat.mul(List.length(&2, Nat, h <> t), a), LBS.posSum(h <> t, a)),
        etarget, comb)

# The whole candidate count is at most its length times the level plus the
# terms the level cannot hold.
def LBS.sub_sum_le(+xs: +List<Nat>, +a: Nat) ->
  {Nat.is_le(Nat.sub(CB.CB.sum(xs), Nat.mul(List.length(&2, Nat, xs), a)),
             LBS.posSum(xs, a)) == True{} : Bool}:
  +h : {Nat.is_le(CB.CB.sum(xs),
           Nat.add(Nat.mul(List.length(&2, Nat, xs), a), LBS.posSum(xs, a)))
        == True{} : Bool} =
    LBS.sum_le_mul_add(xs, a)
  +hc : {Nat.is_le(CB.CB.sum(xs),
            Nat.add(LBS.posSum(xs, a), Nat.mul(List.length(&2, Nat, xs), a)))
         == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(CB.CB.sum(xs),
      Nat.add(Nat.mul(List.length(&2, Nat, xs), a), LBS.posSum(xs, a)),
      Nat.add(LBS.posSum(xs, a), Nat.mul(List.length(&2, Nat, xs), a)),
      NatProof.NatPrf.add_comm(Nat.mul(List.length(&2, Nat, xs), a), LBS.posSum(xs, a)),
      h)
  LBS.sub_le_of_le_add(CB.CB.sum(xs), LBS.posSum(xs, a),
    Nat.mul(List.length(&2, Nat, xs), a), hc)

# One level of the shift: the parent's term at level `i + 1` is at most the
# children's terms at level `i`.
def LBS.lvl_shift(+n: Nat, +ns: +List<Nat>, +k: Nat, +i: Nat,
    +le: {Nat.is_le(n, Nat.add(CB.CB.sum(ns), 1n)) == True{} : Bool},
    +len: {Nat.is_le(List.length(&2, Nat, ns), k) == True{} : Bool}) ->
  {Nat.is_le(Nat.sub(n, Cap.LB.G(k, Nat.add(1n, i))),
             LBS.posSum(ns, Cap.LB.G(k, i))) == True{} : Bool}:
  +a : Nat = Cap.LB.G(k, i)
  +g : Nat = Cap.LB.G(k, Nat.add(1n, i))
  +h_sub : {Nat.is_le(Nat.sub(n, g), Nat.sub(Nat.add(CB.CB.sum(ns), 1n), g))
            == True{} : Bool} =
    Cap.LB.sub_le_l(n, Nat.add(CB.CB.sum(ns), 1n), g, le)
  +h_eq : {Nat.sub(Nat.add(CB.CB.sum(ns), 1n), g)
           == Nat.sub(CB.CB.sum(ns), Nat.mul(k, a)) : Nat} =
    Equal.trans(Nat,
      Nat.sub(Nat.add(CB.CB.sum(ns), 1n), Nat.add(1n, Nat.mul(k, a))),
      Nat.sub(Nat.add(1n, CB.CB.sum(ns)), Nat.add(1n, Nat.mul(k, a))),
      Nat.sub(CB.CB.sum(ns), Nat.mul(k, a)),
      Equal.cong(Nat, Nat,
        x => Nat.sub(x, Nat.add(1n, Nat.mul(k, a))),
        Nat.add(CB.CB.sum(ns), 1n), Nat.add(1n, CB.CB.sum(ns)),
        NatProof.NatPrf.add_comm(CB.CB.sum(ns), 1n)),
      {==})
  +h_mid : {Nat.is_le(Nat.sub(n, g), Nat.sub(CB.CB.sum(ns), Nat.mul(k, a)))
            == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(Nat.sub(n, g), Nat.sub(Nat.add(CB.CB.sum(ns), 1n), g),
      Nat.sub(CB.CB.sum(ns), Nat.mul(k, a)), h_eq, h_sub)
  +h_sum : {Nat.is_le(Nat.sub(CB.CB.sum(ns), Nat.mul(k, a)),
                      Nat.sub(CB.CB.sum(ns), Nat.mul(List.length(&2, Nat, ns), a)))
            == True{} : Bool} =
    LBS.sub_le_r(CB.CB.sum(ns), Nat.mul(k, a),
      Nat.mul(List.length(&2, Nat, ns), a),
      CB.CB.is_le_mul_l(List.length(&2, Nat, ns), k, a, len))
  +h_pos : {Nat.is_le(Nat.sub(CB.CB.sum(ns), Nat.mul(List.length(&2, Nat, ns), a)),
                      LBS.posSum(ns, a)) == True{} : Bool} =
    LBS.sub_sum_le(ns, a)
  NatProof.Nat.is_le_trans(Nat.sub(n, g),
    Nat.sub(CB.CB.sum(ns), Nat.mul(k, a)), LBS.posSum(ns, a),
    h_mid,
    NatProof.Nat.is_le_trans(
      Nat.sub(CB.CB.sum(ns), Nat.mul(k, a)),
      Nat.sub(CB.CB.sum(ns), Nat.mul(List.length(&2, Nat, ns), a)),
      LBS.posSum(ns, a), h_sum, h_pos))

# The capacity sums of a list of sizes, at one level range.
def LBS.capKidLvl(+ns: +List<Nat>, +k: Nat, +fuel: Nat, +i: Nat) -> Nat:
  match ns:
    case Nil{}:
      0n
    case Con{x, t}:
      Nat.add(Cap.LB.capSum(x, k, fuel, i), LBS.capKidLvl(t, k, fuel, i))

# The capacity bounds of a list of sizes.
def LBS.capKidSum(+ns: +List<Nat>, +k: Nat) -> Nat:
  match ns:
    case Nil{}:
      0n
    case Con{x, t}:
      Nat.add(Cap.LB.capbound(x, k), LBS.capKidSum(t, k))

# One level of fuel splits into the level term plus the rest.
def LBS.capKidLvl_split(+ns: +List<Nat>, +k: Nat, +fuel: Nat, +i: Nat) ->
  {LBS.capKidLvl(ns, k, Nat.add(1n, fuel), i)
   == Nat.add(LBS.posSum(ns, Cap.LB.G(k, i)),
              LBS.capKidLvl(ns, k, fuel, Nat.add(1n, i))) : Nat}:
  match ns:
    case Nil{}:
      {==}
    case Con{x, t}:
      +ih : {LBS.capKidLvl(t, k, Nat.add(1n, fuel), i)
             == Nat.add(LBS.posSum(t, Cap.LB.G(k, i)),
                        LBS.capKidLvl(t, k, fuel, Nat.add(1n, i))) : Nat} =
        LBS.capKidLvl_split(t, k, fuel, i)
      +e4 : {Nat.add(Nat.add(Nat.sub(x, Cap.LB.G(k, i)),
                              Cap.LB.capSum(x, k, fuel, Nat.add(1n, i))),
                      Nat.add(LBS.posSum(t, Cap.LB.G(k, i)),
                              LBS.capKidLvl(t, k, fuel, Nat.add(1n, i))))
             == Nat.add(Nat.add(Nat.sub(x, Cap.LB.G(k, i)), LBS.posSum(t, Cap.LB.G(k, i))),
                        Nat.add(Cap.LB.capSum(x, k, fuel, Nat.add(1n, i)),
                                LBS.capKidLvl(t, k, fuel, Nat.add(1n, i)))) : Nat} =
        CB.CB.add4(Nat.sub(x, Cap.LB.G(k, i)),
          Cap.LB.capSum(x, k, fuel, Nat.add(1n, i)),
          LBS.posSum(t, Cap.LB.G(k, i)),
          LBS.capKidLvl(t, k, fuel, Nat.add(1n, i)))
      Equal.trans(Nat,
        LBS.capKidLvl(x <> t, k, Nat.add(1n, fuel), i),
        Nat.add(Nat.add(Nat.sub(x, Cap.LB.G(k, i)),
                        Cap.LB.capSum(x, k, fuel, Nat.add(1n, i))),
                LBS.capKidLvl(t, k, Nat.add(1n, fuel), i)),
        Nat.add(LBS.posSum(x <> t, Cap.LB.G(k, i)),
                LBS.capKidLvl(x <> t, k, fuel, Nat.add(1n, i))),
        {==},
        Equal.trans(Nat,
          Nat.add(Nat.add(Nat.sub(x, Cap.LB.G(k, i)),
                          Cap.LB.capSum(x, k, fuel, Nat.add(1n, i))),
                  LBS.capKidLvl(t, k, Nat.add(1n, fuel), i)),
          Nat.add(Nat.add(Nat.sub(x, Cap.LB.G(k, i)),
                          Cap.LB.capSum(x, k, fuel, Nat.add(1n, i))),
                  Nat.add(LBS.posSum(t, Cap.LB.G(k, i)),
                          LBS.capKidLvl(t, k, fuel, Nat.add(1n, i)))),
          Nat.add(LBS.posSum(x <> t, Cap.LB.G(k, i)),
                  LBS.capKidLvl(x <> t, k, fuel, Nat.add(1n, i))),
          Equal.cong(Nat, Nat,
            y => Nat.add(Nat.add(Nat.sub(x, Cap.LB.G(k, i)),
                                 Cap.LB.capSum(x, k, fuel, Nat.add(1n, i))), y),
            LBS.capKidLvl(t, k, Nat.add(1n, fuel), i),
            Nat.add(LBS.posSum(t, Cap.LB.G(k, i)),
                    LBS.capKidLvl(t, k, fuel, Nat.add(1n, i))), ih),
          e4))

# The shift at every fuel.
def LBS.cap_shift(+n: Nat, +ns: +List<Nat>, +k: Nat, +fuel: Nat, +i: Nat,
    +le: {Nat.is_le(n, Nat.add(CB.CB.sum(ns), 1n)) == True{} : Bool},
    +len: {Nat.is_le(List.length(&2, Nat, ns), k) == True{} : Bool}) ->
  {Nat.is_le(Cap.LB.capSum(n, k, fuel, Nat.add(1n, i)),
             LBS.capKidLvl(ns, k, fuel, i)) == True{} : Bool}:
  match fuel:
    case 0n:
      NatProof.Nat.is_le_zero_l(LBS.capKidLvl(ns, k, 0n, i))
    case 1n+pf:
      +hA : {Nat.is_le(Nat.sub(n, Cap.LB.G(k, Nat.add(1n, i))),
                       LBS.posSum(ns, Cap.LB.G(k, i))) == True{} : Bool} =
        LBS.lvl_shift(n, ns, k, i, le, len)
      +hB : {Nat.is_le(Cap.LB.capSum(n, k, pf, Nat.add(1n, Nat.add(1n, i))),
                       LBS.capKidLvl(ns, k, pf, Nat.add(1n, i))) == True{} : Bool} =
        LBS.cap_shift(n, ns, k, pf, Nat.add(1n, i), le, len)
      +hsum : {Nat.is_le(Nat.add(Nat.sub(n, Cap.LB.G(k, Nat.add(1n, i))),
                                 Cap.LB.capSum(n, k, pf, Nat.add(1n, Nat.add(1n, i)))),
                         Nat.add(LBS.posSum(ns, Cap.LB.G(k, i)),
                                 LBS.capKidLvl(ns, k, pf, Nat.add(1n, i))))
               == True{} : Bool} =
        CB.CB.is_le_add(Nat.sub(n, Cap.LB.G(k, Nat.add(1n, i))),
          LBS.posSum(ns, Cap.LB.G(k, i)),
          Cap.LB.capSum(n, k, pf, Nat.add(1n, Nat.add(1n, i))),
          LBS.capKidLvl(ns, k, pf, Nat.add(1n, i)), hA, hB)
      NatProof.Nat.is_le_eq_r(
        Nat.add(Nat.sub(n, Cap.LB.G(k, Nat.add(1n, i))),
                Cap.LB.capSum(n, k, pf, Nat.add(1n, Nat.add(1n, i)))),
        Nat.add(LBS.posSum(ns, Cap.LB.G(k, i)),
                LBS.capKidLvl(ns, k, pf, Nat.add(1n, i))),
        LBS.capKidLvl(ns, k, Nat.add(1n, pf), i),
        Equal.sym(Nat, LBS.capKidLvl(ns, k, Nat.add(1n, pf), i),
          Nat.add(LBS.posSum(ns, Cap.LB.G(k, i)),
                  LBS.capKidLvl(ns, k, pf, Nat.add(1n, i))),
          LBS.capKidLvl_split(ns, k, pf, i)),
        hsum)

# A truncated subtraction from zero is zero.
def LBS.sub_zero_l(b: Nat) -> {Nat.sub(0n, b) == 0n : Nat}:
  match b:
    case 0n:
      {==}
    case 1n+bp:
      {==}

# The all-zero capacity sum.
def LBS.capSum_zero(+k: Nat, +fuel: Nat, +i: Nat) ->
  {Cap.LB.capSum(0n, k, fuel, i) == 0n : Nat}:
  match fuel:
    case 0n:
      {==}
    case 1n+pf:
      Equal.trans(Nat, Cap.LB.capSum(0n, k, Nat.add(1n, pf), i),
        Cap.LB.capSum(0n, k, pf, Nat.add(1n, i)), 0n,
        Equal.cong(Nat, Nat,
          y => Nat.add(y, Cap.LB.capSum(0n, k, pf, Nat.add(1n, i))),
          Nat.sub(0n, Cap.LB.G(k, i)), 0n, LBS.sub_zero_l(Cap.LB.G(k, i))),
        LBS.capSum_zero(k, pf, Nat.add(1n, i)))

# A level beyond every candidate adds nothing to the sum.
def LBS.capSum_succ_zero(+x: Nat, +k: Nat, +a: Nat, +j: Nat,
    h: {Nat.is_le(x, Cap.LB.G(k, Nat.add(j, a))) == True{} : Bool}) ->
  {Cap.LB.capSum(x, k, Nat.add(1n, a), j) == Cap.LB.capSum(x, k, a, j) : Nat}:
  match a:
    case 0n:
      +h0 : {Nat.is_le(x, Cap.LB.G(k, j)) == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(x, Cap.LB.G(k, Nat.add(j, 0n)), Cap.LB.G(k, j),
          Equal.cong(Nat, Nat, y => Cap.LB.G(k, y), Nat.add(j, 0n), j,
            NatProof.NatPrf.add_zero(j)),
          h)
      +ez : {Nat.sub(x, Cap.LB.G(k, j)) == 0n : Nat} =
        LBS.sub_eq_zero(x, Cap.LB.G(k, j), h0)
      Equal.trans(Nat,
        Cap.LB.capSum(x, k, Nat.add(1n, 0n), j),
        Nat.add(Nat.sub(x, Cap.LB.G(k, j)), 0n), 0n,
        {==},
        Equal.trans(Nat, Nat.add(Nat.sub(x, Cap.LB.G(k, j)), 0n),
          Nat.sub(x, Cap.LB.G(k, j)), 0n,
          NatProof.NatPrf.add_zero(Nat.sub(x, Cap.LB.G(k, j))), ez))
    case 1n+ap:
      +e1 : {Nat.add(Nat.add(1n, j), ap) == Nat.add(1n, Nat.add(j, ap)) : Nat} =
        {==}
      +e2 : {Nat.add(1n, Nat.add(j, ap)) == Nat.add(j, Nat.add(1n, ap)) : Nat} =
        Equal.sym(Nat, Nat.add(j, Nat.add(1n, ap)), Nat.add(1n, Nat.add(j, ap)),
          NatProof.NatPrf.add_succ(j, ap))
      +eidx : {Nat.add(j, Nat.add(1n, ap)) == Nat.add(Nat.add(1n, j), ap) : Nat} =
        Equal.sym(Nat, Nat.add(Nat.add(1n, j), ap), Nat.add(j, Nat.add(1n, ap)),
          Equal.trans(Nat, Nat.add(Nat.add(1n, j), ap),
            Nat.add(1n, Nat.add(j, ap)), Nat.add(j, Nat.add(1n, ap)), e1, e2))
      +h2 : {Nat.is_le(x, Cap.LB.G(k, Nat.add(Nat.add(1n, j), ap))) == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(x, Cap.LB.G(k, Nat.add(j, Nat.add(1n, ap))),
          Cap.LB.G(k, Nat.add(Nat.add(1n, j), ap)),
          Equal.cong(Nat, Nat, y => Cap.LB.G(k, y),
            Nat.add(j, Nat.add(1n, ap)), Nat.add(Nat.add(1n, j), ap), eidx),
          h)
      +ih : {Cap.LB.capSum(x, k, Nat.add(1n, ap), Nat.add(1n, j))
             == Cap.LB.capSum(x, k, ap, Nat.add(1n, j)) : Nat} =
        LBS.capSum_succ_zero(x, k, ap, Nat.add(1n, j), h2)
      Equal.cong(Nat, Nat,
        y => Nat.add(Nat.sub(x, Cap.LB.G(k, j)), y),
        Cap.LB.capSum(x, k, Nat.add(1n, ap), Nat.add(1n, j)),
        Cap.LB.capSum(x, k, ap, Nat.add(1n, j)), ih)

# No level from `x` on can hold a candidate, so the sum over `x` levels is the
# whole sum, whatever the fuel.
def LBS.capSum_le_full(+x: Nat, +k: Nat, +fuel: Nat, +j: Nat,
    +hk: {Nat.is_le(1n, k) == True{} : Bool}) ->
  {Nat.is_le(Cap.LB.capSum(x, k, fuel, j), Cap.LB.capSum(x, k, x, j))
   == True{} : Bool}:
  match x:
    case 0n:
      NatProof.Nat.is_le_eq_l(0n, 0n, Cap.LB.capSum(0n, k, fuel, j),
        Equal.sym(Nat, Cap.LB.capSum(0n, k, fuel, j), 0n,
          LBS.capSum_zero(k, fuel, j)),
        NatProof.Nat.is_le_refl(0n))
    case 1n+xp:
      match fuel:
        case 0n:
          NatProof.Nat.is_le_zero_l(Cap.LB.capSum(1n+xp, k, 1n+xp, j))
        case 1n+pf:
          +a : Nat = Nat.sub(1n+xp, Cap.LB.G(k, j))
          +ih : {Nat.is_le(Cap.LB.capSum(1n+xp, k, pf, Nat.add(1n, j)),
                           Cap.LB.capSum(1n+xp, k, 1n+xp, Nat.add(1n, j)))
                 == True{} : Bool} =
            LBS.capSum_le_full(1n+xp, k, pf, Nat.add(1n, j), hk)
          +eidx : {Nat.add(j, 1n+xp) == Nat.add(Nat.add(1n, j), xp) : Nat} =
            Equal.trans(Nat, Nat.add(j, 1n+xp), Nat.add(1n, Nat.add(j, xp)),
              Nat.add(Nat.add(1n, j), xp),
              NatProof.NatPrf.add_succ(j, xp), {==})
          +hnat : {Nat.is_le(1n+xp, Nat.add(Nat.add(1n, j), xp)) == True{} : Bool} =
            NatProof.Nat.is_le_eq_r(1n+xp, Nat.add(j, 1n+xp), Nat.add(Nat.add(1n, j), xp),
              eidx, NatProof.Nat.is_le_add_self_l(j, 1n+xp))
          +xg : {Nat.is_le(1n+xp, Cap.LB.G(k, Nat.add(Nat.add(1n, j), xp)))
                 == True{} : Bool} =
            NatProof.Nat.is_le_trans(1n+xp, Nat.add(Nat.add(1n, j), xp),
              Cap.LB.G(k, Nat.add(Nat.add(1n, j), xp)),
              hnat, Cap.LB.G_ge(k, Nat.add(Nat.add(1n, j), xp), hk))
          +eabs : {Cap.LB.capSum(1n+xp, k, 1n+xp, Nat.add(1n, j))
                   == Cap.LB.capSum(1n+xp, k, xp, Nat.add(1n, j)) : Nat} =
            LBS.capSum_succ_zero(1n+xp, k, xp, Nat.add(1n, j), xg)
          +hstep : {Nat.is_le(
                      Nat.add(a, Cap.LB.capSum(1n+xp, k, pf, Nat.add(1n, j))),
                      Nat.add(a, Cap.LB.capSum(1n+xp, k, 1n+xp, Nat.add(1n, j))))
                    == True{} : Bool} =
            CB.CB.is_le_add(a, a,
              Cap.LB.capSum(1n+xp, k, pf, Nat.add(1n, j)),
              Cap.LB.capSum(1n+xp, k, 1n+xp, Nat.add(1n, j)),
              NatProof.Nat.is_le_refl(a), ih)
          NatProof.Nat.is_le_eq_r(
            Nat.add(a, Cap.LB.capSum(1n+xp, k, pf, Nat.add(1n, j))),
            Nat.add(a, Cap.LB.capSum(1n+xp, k, 1n+xp, Nat.add(1n, j))),
            Nat.add(a, Cap.LB.capSum(1n+xp, k, xp, Nat.add(1n, j))),
            Equal.cong(Nat, Nat, y => Nat.add(a, y),
              Cap.LB.capSum(1n+xp, k, 1n+xp, Nat.add(1n, j)),
              Cap.LB.capSum(1n+xp, k, xp, Nat.add(1n, j)), eabs),
            hstep)

# Subtracting zero leaves a number unchanged.
def LBS.sub_zero(b: Nat) -> {Nat.sub(b, 0n) == b : Nat}:
  match b:
    case 0n:
      {==}
    case 1n+bp:
      {==}

# Every class size counts with its own capacity bound.
def LBS.capKid_lvl_le(+ns: +List<Nat>, +k: Nat, +n: Nat,
    +hk: {Nat.is_le(1n, k) == True{} : Bool}) ->
  {Nat.is_le(LBS.capKidLvl(ns, k, n, 0n), LBS.capKidSum(ns, k)) == True{} : Bool}:
  match ns:
    case Nil{}:
      NatProof.Nat.is_le_refl(0n)
    case Con{x, t}:
      match n:
        case 0n:
          +hz : {Nat.is_le(Cap.LB.capSum(x, k, 0n, 0n),
                           Nat.add(x, Cap.LB.capSum(x, k, x, 1n))) == True{} : Bool} =
            NatProof.Nat.is_le_zero_l(Nat.add(x, Cap.LB.capSum(x, k, x, 1n)))
          CB.CB.is_le_add(Cap.LB.capSum(x, k, 0n, 0n), Cap.LB.capbound(x, k),
            LBS.capKidLvl(t, k, 0n, 0n), LBS.capKidSum(t, k),
            hz, LBS.capKid_lvl_le(t, k, 0n, hk))
        case 1n+pn:
          +hfull : {Nat.is_le(Cap.LB.capSum(x, k, pn, 1n),
                              Cap.LB.capSum(x, k, x, 1n)) == True{} : Bool} =
            LBS.capSum_le_full(x, k, pn, 1n, hk)
          +hx : {Nat.is_le(Nat.add(x, Cap.LB.capSum(x, k, pn, 1n)),
                           Nat.add(x, Cap.LB.capSum(x, k, x, 1n))) == True{} : Bool} =
            CB.CB.is_le_add(x, x, Cap.LB.capSum(x, k, pn, 1n),
              Cap.LB.capSum(x, k, x, 1n), NatProof.Nat.is_le_refl(x), hfull)
          +hx2 : {Nat.is_le(Cap.LB.capSum(x, k, Nat.add(1n, pn), 0n),
                            Cap.LB.capbound(x, k)) == True{} : Bool} =
            NatProof.Nat.is_le_eq_l(Nat.add(x, Cap.LB.capSum(x, k, x, 1n)),
              Nat.add(x, Cap.LB.capSum(x, k, pn, 1n)),
              Cap.LB.capSum(x, k, Nat.add(1n, pn), 0n),
              Equal.sym(Nat, Cap.LB.capSum(x, k, Nat.add(1n, pn), 0n),
                Nat.add(x, Cap.LB.capSum(x, k, pn, 1n)),
                Equal.cong(Nat, Nat,
                  y => Nat.add(y, Cap.LB.capSum(x, k, pn, 1n)),
                  Nat.sub(x, 0n), x, LBS.sub_zero(x))),
              hx)
          CB.CB.is_le_add(Cap.LB.capSum(x, k, Nat.add(1n, pn), 0n),
            Cap.LB.capbound(x, k),
            LBS.capKidLvl(t, k, Nat.add(1n, pn), 0n), LBS.capKidSum(t, k),
            hx2, LBS.capKid_lvl_le(t, k, Nat.add(1n, pn), hk))

# The numeric step: the capacity sum of the parent is at most the total of the
# class bounds, the classes of a node holding all but one of its candidates and
# numbering at most `k`.
def LBS.cap_num(+n: Nat, +ns: +List<Nat>, +k: Nat,
    +hk: {Nat.is_le(1n, k) == True{} : Bool},
    +le: {Nat.is_le(n, Nat.add(CB.CB.sum(ns), 1n)) == True{} : Bool},
    +len: {Nat.is_le(List.length(&2, Nat, ns), k) == True{} : Bool}) ->
  {Nat.is_le(Cap.LB.capSum(n, k, n, 1n), LBS.capKidSum(ns, k)) == True{} : Bool}:
  +s1 : {Nat.is_le(Cap.LB.capSum(n, k, n, Nat.add(1n, 0n)),
                   LBS.capKidLvl(ns, k, n, 0n)) == True{} : Bool} =
    LBS.cap_shift(n, ns, k, n, 0n, le, len)
  +s2 : {Nat.is_le(LBS.capKidLvl(ns, k, n, 0n), LBS.capKidSum(ns, k))
         == True{} : Bool} =
    LBS.capKid_lvl_le(ns, k, n, hk)
  NatProof.Nat.is_le_eq_l(LBS.capKidSum(ns, k),
    Cap.LB.capSum(n, k, n, Nat.add(1n, 0n)), Cap.LB.capSum(n, k, n, 1n),
    {==},
    NatProof.Nat.is_le_trans(Cap.LB.capSum(n, k, n, Nat.add(1n, 0n)),
      LBS.capKidLvl(ns, k, n, 0n), LBS.capKidSum(ns, k), s1, s2))

# --- Membership as a multiplicity ------------------------------------------

# Boolean disjunction facts, with the left side as a parameter so it can be
# matched.
def LBS.or_true_r(+a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def LBS.or_false_r(+a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def LBS.or_false_l(+b: Bool) -> {Bool.or(False{}, b) == b : Bool}:
  {==}

def LBS.or_intro_l(a: Bool, b: Bool, h: {a == True{} : Bool}) ->
  {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Bool.or(False{}, b) == True{} : Bool},
        Logic.Proof.false_ne_true(h))

def LBS.or_intro_r(+a: Bool, b: Bool, h: {b == True{} : Bool}) ->
  {Bool.or(a, b) == True{} : Bool}:
  match b:
    case True{}:
      LBS.or_true_r(a)
    case False{}:
      Empty.absurd({Bool.or(a, False{}) == True{} : Bool},
        Logic.Proof.false_ne_true(h))

def LBS.or_elim_r(a: Bool, b: Bool, e: {Bool.or(a, b) == True{} : Bool},
    f: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == True{} : Bool}, Logic.Proof.true_ne_false(f))
    case False{}:
      e

# The keep test, unfolded: a true keep is a non-guess word with the feedback.
def LBS.keep_true_l(bw: Bool, bf: Bool,
    e: {Part.LB.keepb(bw, bf) == True{} : Bool}) -> {bw == False{} : Bool}:
  match bw:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Logic.Proof.false_ne_true(e))
    case False{}:
      {==}

def LBS.keep_true_r(bw: Bool, bf: Bool,
    e: {Part.LB.keepb(bw, bf) == True{} : Bool}) -> {bf == True{} : Bool}:
  match bw:
    case True{}:
      Empty.absurd({bf == True{} : Bool}, Logic.Proof.false_ne_true(e))
    case False{}:
      e

def LBS.keep_false_r(bw: Bool, bf: Bool,
    e: {Part.LB.keepb(bw, bf) == False{} : Bool},
    f: {bw == False{} : Bool}) -> {bf == False{} : Bool}:
  match bw:
    case True{}:
      Empty.absurd({bf == False{} : Bool}, Logic.Proof.true_ne_false(f))
    case False{}:
      e

# A word that keeps survives no filter: its multiplicity in the leftover is
# zero.
def LBS.mult_remw_zero_go(+g: +List<Nat>, +f: +List<Feedback.Color>, +w: +List<Nat>,
    +h: +List<Nat>, +t: +List<+List<Nat>>, b: Bool,
    +eb: {b == Part.LB.keep(g, f, h) : Bool},
    ih: {Twice.LB.mult(w, Part.LB.remw(g, f, t)) == 0n : Nat},
    +hk: {Part.LB.keep(g, f, w) == True{} : Bool}) ->
  {Twice.LB.mult(w, Part.LB.remw_of(g, f, h, t, b)) == 0n : Nat}:
  match b:
    case True{}:
      ih
    case False{}:
      +ewh : {Feedback.word_eq(w, h) == False{} : Bool} =
        FbProof.BoolProof.false_of_not_true(Feedback.word_eq(w, h),
          ewt => Logic.Proof.true_ne_false(
            Equal.trans(Bool, True{}, Part.LB.keep(g, f, w), False{},
              Equal.sym(Bool, Part.LB.keep(g, f, w), True{}, hk),
              Equal.trans(Bool, Part.LB.keep(g, f, w), Part.LB.keep(g, f, h), False{},
                Equal.cong(+List<Nat>, Bool, x => Part.LB.keep(g, f, x), w, h,
                  CoverList.Cover.word_eq_true(w, h, ewt)),
                Equal.sym(Bool, False{}, Part.LB.keep(g, f, h), eb)))))
      +hit : {Twice.LB.hit(w, h) == 0n : Nat} =
        Equal.trans(Nat, Twice.LB.hit(w, h), Twice.LB.hit_bool(False{}), 0n,
          Twice.LB.hit_bool_eq(Feedback.word_eq(w, h), False{}, ewh), {==})
      Equal.trans(Nat,
        Twice.LB.mult(w, Part.LB.remw_of(g, f, h, t, False{})),
        Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, Part.LB.remw(g, f, t))),
        0n,
        {==},
        Equal.trans(Nat,
          Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, Part.LB.remw(g, f, t))),
          Nat.add(0n, Twice.LB.mult(w, Part.LB.remw(g, f, t))), 0n,
          Equal.cong(Nat, Nat,
            x => Nat.add(x, Twice.LB.mult(w, Part.LB.remw(g, f, t))),
            Twice.LB.hit(w, h), 0n, hit),
          Equal.trans(Nat,
            Nat.add(0n, Twice.LB.mult(w, Part.LB.remw(g, f, t))),
            Nat.add(0n, 0n), 0n,
            Equal.cong(Nat, Nat, x => Nat.add(0n, x),
              Twice.LB.mult(w, Part.LB.remw(g, f, t)), 0n, ih), {==})))

def LBS.mult_remw_zero(+g: +List<Nat>, +f: +List<Feedback.Color>, +w: +List<Nat>,
    +S: +List<+List<Nat>>, +hk: {Part.LB.keep(g, f, w) == True{} : Bool}) ->
  {Twice.LB.mult(w, Part.LB.remw(g, f, S)) == 0n : Nat}:
  match S:
    case Nil{}:
      {==}
    case Con{h, t}:
      +b : Bool = Part.LB.keep(g, f, h)
      +core : {Twice.LB.mult(w, Part.LB.remw_of(g, f, h, t, b)) == 0n : Nat} =
        LBS.mult_remw_zero_go(g, f, w, h, t, b, {==},
          LBS.mult_remw_zero(g, f, w, t, hk), hk)
      Equal.trans(Nat, Twice.LB.mult(w, Part.LB.remw(g, f, h <> t)),
        Twice.LB.mult(w, Part.LB.remw_of(g, f, h, t, b)), 0n,
        Equal.cong(+List<+List<Nat>>, Nat, x => Twice.LB.mult(w, x),
          Part.LB.remw(g, f, h <> t), Part.LB.remw_of(g, f, h, t, b),
          Part.LB.remw_eq(g, f, h, t, b, {==})),
        core)

# A word's multiplicity in the leftover is at most its multiplicity in the
# list.
def LBS.mult_rem_le(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    +S: +List<+List<Nat>>) ->
  {Nat.is_le(Twice.LB.mult(w, Part.LB.rem(g, kids, S)), Twice.LB.mult(w, S))
   == True{} : Bool}:
  match kids:
    case Nil{}:
      NatProof.Nat.is_le_refl(Twice.LB.mult(w, S))
    case Con{c, rest}:
      match c:
        case Tree.Child{f, t}:
          NatProof.Nat.is_le_trans(Twice.LB.mult(w, Part.LB.rem(g, rest, Part.LB.remw(g, f, S))),
            Twice.LB.mult(w, Part.LB.remw(g, f, S)), Twice.LB.mult(w, S),
            LBS.mult_rem_le(g, rest, w, Part.LB.remw(g, f, S)),
            Part.LB.mult_rem(w, g, f, S))

# A positive multiplicity is at least one.
def LBS.one_le_zero(+x: Nat, +e: {Nat.is_le(1n, x) == True{} : Bool},
    +z: {x == 0n : Nat}) -> Empty:
  +e0 : {Nat.is_le(1n, 0n) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(1n, x, 0n, z, e)
  Logic.Proof.false_ne_true(e0)

def LBS.not_one_le_zero(+x: Nat, +z: {x == 0n : Nat}) ->
  {Nat.is_le(1n, x) == False{} : Bool}:
  FbProof.BoolProof.false_of_not_true(Nat.is_le(1n, x),
    e => LBS.one_le_zero(x, e, z))

# A word with a positive multiplicity in a leftover filter fails that filter's
# keep test.
def LBS.keep_false_of_mult_remw(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +w: +List<Nat>, +S: +List<+List<Nat>>,
    +h: {Nat.is_le(1n, Twice.LB.mult(w, Part.LB.remw(g, f, S))) == True{} : Bool}) ->
  {Part.LB.keep(g, f, w) == False{} : Bool}:
  FbProof.BoolProof.false_of_not_true(Part.LB.keep(g, f, w),
    hk => LBS.one_le_zero(Twice.LB.mult(w, Part.LB.remw(g, f, S)), h,
      LBS.mult_remw_zero(g, f, w, S, hk)))

# One step of the positive-multiplicity induction, with the head's guess test
# as a parameter.
def LBS.mult_ad_go(t: Tree.Tree, +w: +List<Nat>, +h0: +List<Nat>,
    +tl: +List<+List<Nat>>, b: Bool,
    +eb: {b == Feedback.word_eq(w, h0) : Bool},
    sh0: {Maybe.is_some(&1, Nat, Tree.depth(t, h0)) == True{} : Bool},
    k: {Nat.is_le(1n, Twice.LB.mult(w, tl)) == True{} : Bool}
       -> {Maybe.is_some(&1, Nat, Tree.depth(t, w)) == True{} : Bool},
    h: {Nat.is_le(1n, Nat.add(Twice.LB.hit(w, h0), Twice.LB.mult(w, tl)))
        == True{} : Bool}) ->
  {Maybe.is_some(&1, Nat, Tree.depth(t, w)) == True{} : Bool}:
  match b:
    case True{}:
      +ew : {w == h0 : +List<Nat>} =
        CoverList.Cover.word_eq_true(w, h0,
          Equal.sym(Bool, True{}, Feedback.word_eq(w, h0), eb))
      Equal.trans(Bool,
        Maybe.is_some(&1, Nat, Tree.depth(t, w)),
        Maybe.is_some(&1, Nat, Tree.depth(t, h0)),
        True{},
        Equal.cong(+List<Nat>, Bool, x => Maybe.is_some(&1, Nat, Tree.depth(t, x)),
          w, h0, ew),
        sh0)
    case False{}:
      +hit0 : {Twice.LB.hit(w, h0) == 0n : Nat} =
        Equal.trans(Nat, Twice.LB.hit(w, h0), Twice.LB.hit_bool(False{}), 0n,
          Twice.LB.hit_bool_eq(Feedback.word_eq(w, h0), False{},
            Equal.sym(Bool, False{}, Feedback.word_eq(w, h0), eb)), {==})
      +hsub : {Nat.is_le(1n, Twice.LB.mult(w, tl)) == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(1n,
          Nat.add(Twice.LB.hit(w, h0), Twice.LB.mult(w, tl)), Twice.LB.mult(w, tl),
          Equal.trans(Nat,
            Nat.add(Twice.LB.hit(w, h0), Twice.LB.mult(w, tl)),
            Nat.add(0n, Twice.LB.mult(w, tl)), Twice.LB.mult(w, tl),
            Equal.cong(Nat, Nat, x => Nat.add(x, Twice.LB.mult(w, tl)),
              Twice.LB.hit(w, h0), 0n, hit0), {==}),
          h)
      k(hsub)

# A candidate of the list with positive multiplicity has a depth in the tree.
def LBS.mult_ad(+t: Tree.Tree, +w: +List<Nat>, +S: +List<+List<Nat>>,
    ad: Tree.AllHaveDepth(t, S),
    h: {Nat.is_le(1n, Twice.LB.mult(w, S)) == True{} : Bool}) ->
  {Maybe.is_some(&1, Nat, Tree.depth(t, w)) == True{} : Bool}:
  match S:
    case Nil{}:
      Empty.absurd({Maybe.is_some(&1, Nat, Tree.depth(t, w)) == True{} : Bool},
        LBS.one_le_zero(Twice.LB.mult(w, Nil{}), h, {==}))
    case Con{h0, tl}:
      (sh0, st) = ad
      LBS.mult_ad_go(t, w, h0, tl, Feedback.word_eq(w, h0), {==}, sh0,
        hs => LBS.mult_ad(t, w, tl, st, hs), h)

def LBS.or_elim_l(a: Bool, b: Bool, e: {Bool.or(a, b) == False{} : Bool}) ->
  {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool},
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, Bool.or(True{}, b), False{},
            Equal.sym(Bool, Bool.or(True{}, b), True{}, {==}), e)))
    case False{}:
      {==}

def LBS.or_elim_r_false(a: Bool, b: Bool, e: {Bool.or(a, b) == False{} : Bool},
    f: {a == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({b == False{} : Bool}, Logic.Proof.true_ne_false(f))
    case False{}:
      e

# A child list without a matching feedback looks nothing up.
def LBS.lookup_skip_go(+fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +t: Tree.Tree, +rest: +List<Tree.Child>, b: Bool,
    +eb: {b == Feedback.feedback_eq(fb, f) : Bool},
    hb: {b == False{} : Bool},
    ih: {Tree.lookup(fb, rest) == None{} : Maybe<&1, Tree.Tree>}) ->
  {Tree.lookup(fb, Tree.Child{f, t} <> rest) == None{} : Maybe<&1, Tree.Tree>}:
  match b:
    case True{}:
      Empty.absurd({Tree.lookup(fb, Tree.Child{f, t} <> rest) == None{}
                    : Maybe<&1, Tree.Tree>},
        Logic.Proof.true_ne_false(hb))
    case False{}:
      +e1 : {Tree.lookup(fb, Tree.Child{f, t} <> rest)
            == Feedback.Bool.case(Maybe<Tree.Tree>, Feedback.feedback_eq(fb, f),
                 Some{t}, Tree.lookup(fb, rest)) : Maybe<&1, Tree.Tree>} =
        {==}
      +e2 : {Feedback.Bool.case(Maybe<Tree.Tree>, Feedback.feedback_eq(fb, f),
                  Some{t}, Tree.lookup(fb, rest))
             == Tree.lookup(fb, rest) : Maybe<&1, Tree.Tree>} =
        Equal.cong(Bool, Maybe<Tree.Tree>,
          b2 => Feedback.Bool.case(Maybe<Tree.Tree>, b2, Some{t}, Tree.lookup(fb, rest)),
          Feedback.feedback_eq(fb, f), False{},
          Equal.trans(Bool, Feedback.feedback_eq(fb, f), b, False{},
            Equal.sym(Bool, b, Feedback.feedback_eq(fb, f), eb), hb))
      +e12 : {Tree.lookup(fb, Tree.Child{f, t} <> rest) == Tree.lookup(fb, rest)
              : Maybe<&1, Tree.Tree>} =
        Equal.trans(Maybe<&1, Tree.Tree>, Tree.lookup(fb, Tree.Child{f, t} <> rest),
          Feedback.Bool.case(Maybe<Tree.Tree>, Feedback.feedback_eq(fb, f),
            Some{t}, Tree.lookup(fb, rest)),
          Tree.lookup(fb, rest), e1, e2)
      Equal.trans(Maybe<&1, Tree.Tree>, Tree.lookup(fb, Tree.Child{f, t} <> rest),
        Tree.lookup(fb, rest), None{}, e12, ih)

# A leftover word with a false guess test finds no child.
def LBS.lookup_none_of_mult_rem(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +w: +List<Nat>, +S: +List<+List<Nat>>,
    +nf: {Feedback.word_eq(g, w) == False{} : Bool},
    +h: {Nat.is_le(1n, Twice.LB.mult(w, Part.LB.rem(g, kids, S))) == True{} : Bool}) ->
  {Tree.lookup(Feedback.feedback(g, w), kids) == None{} : Maybe<&1, Tree.Tree>}:
  match kids:
    case Nil{}:
      {==}
    case Con{c, rest}:
      match c:
        case Tree.Child{f, t}:
          +hm : {Nat.is_le(1n, Twice.LB.mult(w, Part.LB.remw(g, f, S))) == True{} : Bool} =
            NatProof.Nat.is_le_trans(1n,
              Twice.LB.mult(w, Part.LB.rem(g, rest, Part.LB.remw(g, f, S))),
              Twice.LB.mult(w, Part.LB.remw(g, f, S)), h,
              LBS.mult_rem_le(g, rest, w, Part.LB.remw(g, f, S)))
          +keepf : {Part.LB.keep(g, f, w) == False{} : Bool} =
            LBS.keep_false_of_mult_remw(g, f, w, S, hm)
          +efb : {Feedback.feedback_eq(f, Feedback.feedback(g, w)) == False{} : Bool} =
            LBS.keep_false_r(Feedback.word_eq(g, w),
              Feedback.feedback_eq(f, Feedback.feedback(g, w)), keepf, nf)
          +ebf : {Feedback.feedback_eq(Feedback.feedback(g, w), f) == False{} : Bool} =
            Equal.trans(Bool, Feedback.feedback_eq(Feedback.feedback(g, w), f),
              Feedback.feedback_eq(f, Feedback.feedback(g, w)), False{},
              FbProof.FeedbackProof.feedback_eq_sym_bool(Feedback.feedback(g, w), f), efb)
          LBS.lookup_skip_go(Feedback.feedback(g, w), f, t, rest,
            Feedback.feedback_eq(Feedback.feedback(g, w), f), {==}, ebf,
            LBS.lookup_none_of_mult_rem(g, rest, w, Part.LB.remw(g, f, S), nf, h))

# A non-guess word's depth at a node is the bump of its child scan.
def LBS.node_depth_false_go(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +w: +List<Nat>, b: Bool, +eb: {b == Feedback.word_eq(g, w) : Bool},
    nf: {b == False{} : Bool}) ->
  {Tree.depth(Tree.Node{g, kids}, w)
   == Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)) : Maybe<Nat>}:
  match b:
    case True{}:
      Empty.absurd({Tree.depth(Tree.Node{g, kids}, w)
                    == Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))
                    : Maybe<Nat>},
        Logic.Proof.true_ne_false(nf))
    case False{}:
      Equal.trans(Maybe<Nat>, Tree.depth(Tree.Node{g, kids}, w),
        Feedback.Bool.case(Maybe<Nat>, Feedback.word_eq(g, w), Some{1n},
          Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))),
        Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)),
        {==},
        Equal.trans(Maybe<Nat>,
          Feedback.Bool.case(Maybe<Nat>, Feedback.word_eq(g, w), Some{1n},
            Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))),
          Feedback.Bool.case(Maybe<Nat>, False{}, Some{1n},
            Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))),
          Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)),
          Equal.cong(Bool, Maybe<Nat>,
            b2 => Feedback.Bool.case(Maybe<Nat>, b2, Some{1n},
              Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))),
            Feedback.word_eq(g, w), False{},
            Equal.trans(Bool, Feedback.word_eq(g, w), b, False{},
              Equal.sym(Bool, b, Feedback.word_eq(g, w), eb), nf)),
          {==}))

def LBS.node_depth_false(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +w: +List<Nat>, +nf: {Feedback.word_eq(g, w) == False{} : Bool}) ->
  {Tree.depth(Tree.Node{g, kids}, w)
   == Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)) : Maybe<Nat>}:
  LBS.node_depth_false_go(g, kids, w, Feedback.word_eq(g, w), {==}, nf)

# No leftover word can differ from the root guess.
def LBS.rem_word_contra(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>, +w: +List<Nat>,
    +nf: {Feedback.word_eq(g, w) == False{} : Bool},
    +h: {Nat.is_le(1n, Twice.LB.mult(w, Part.LB.rem(g, kids, S))) == True{} : Bool},
    ad: Tree.AllHaveDepth(Tree.Node{g, kids}, S)) -> Empty:
  +lk : {Tree.lookup(Feedback.feedback(g, w), kids) == None{} : Maybe<&1, Tree.Tree>} =
    LBS.lookup_none_of_mult_rem(g, kids, w, S, nf, h)
  +mS : {Nat.is_le(1n, Twice.LB.mult(w, S)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(1n, Twice.LB.mult(w, Part.LB.rem(g, kids, S)),
      Twice.LB.mult(w, S), h, LBS.mult_rem_le(g, kids, w, S))
  +adw : {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool} =
    LBS.mult_ad(Tree.Node{g, kids}, w, S, ad, mS)
  +ed : {Tree.depth(Tree.Node{g, kids}, w)
         == Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))
         : Maybe<Nat>} =
    LBS.node_depth_false(g, kids, w, nf)
  +s1 : {Maybe.is_some(&1, Nat,
           Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)))
         == True{} : Bool} =
    Equal.trans(Bool,
      Maybe.is_some(&1, Nat,
        Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))),
      Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)),
      True{},
      Equal.cong(Maybe<Nat>, Bool, m2 => Maybe.is_some(&1, Nat, m2),
        Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)),
        Tree.depth(Tree.Node{g, kids}, w), Equal.sym(Maybe<Nat>,
          Tree.depth(Tree.Node{g, kids}, w),
          Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)), ed)),
      adw)
  +s2 : {Maybe.is_some(&1, Nat, Tree.depth.go(kids, Feedback.feedback(g, w), w))
         == True{} : Bool} =
    Equal.trans(Bool,
      Maybe.is_some(&1, Nat, Tree.depth.go(kids, Feedback.feedback(g, w), w)),
      Maybe.is_some(&1, Nat,
        Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))),
      True{},
      Equal.sym(Bool,
        Maybe.is_some(&1, Nat,
          Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))),
        Maybe.is_some(&1, Nat, Tree.depth.go(kids, Feedback.feedback(g, w), w)),
        NodeCost.NodeCost.is_some_bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))),
      s1)
  +ld : {DepthProof.DepthProof.lookup_depth(Tree.lookup(Feedback.feedback(g, w), kids), w)
          == DepthProof.DepthProof.lookup_depth(None{}, w) : Maybe<Nat>} =
    Equal.cong(Maybe<Tree.Tree>, Maybe<Nat>,
      m2 => DepthProof.DepthProof.lookup_depth(m2, w),
      Tree.lookup(Feedback.feedback(g, w), kids), None{}, lk)
  +ldn : {DepthProof.DepthProof.lookup_depth(None{}, w) == None{} : Maybe<Nat>} =
    {==}
  +ego : {Tree.depth.go(kids, Feedback.feedback(g, w), w) == None{} : Maybe<Nat>} =
    Equal.trans(Maybe<Nat>, Tree.depth.go(kids, Feedback.feedback(g, w), w),
      DepthProof.DepthProof.lookup_depth(Tree.lookup(Feedback.feedback(g, w), kids), w),
      None{},
      DepthProof.DepthProof.depth_go_lookup(kids, Feedback.feedback(g, w), w),
      Equal.trans(Maybe<Nat>,
        DepthProof.DepthProof.lookup_depth(Tree.lookup(Feedback.feedback(g, w), kids), w),
        DepthProof.DepthProof.lookup_depth(None{}, w), None{}, ld, ldn))
  +s3 : {Maybe.is_some(&1, Nat, None{}) == True{} : Bool} =
    Equal.trans(Bool, Maybe.is_some(&1, Nat, None{}),
      Maybe.is_some(&1, Nat, Tree.depth.go(kids, Feedback.feedback(g, w), w)),
      True{},
      Equal.cong(Maybe<Nat>, Bool, m2 => Maybe.is_some(&1, Nat, m2),
        None{}, Tree.depth.go(kids, Feedback.feedback(g, w), w),
        Equal.sym(Maybe<Nat>, Tree.depth.go(kids, Feedback.feedback(g, w), w),
          None{}, ego)),
      s2)
  Logic.Proof.false_ne_true(s3)

# A boolean that cannot be false is true.
def LBS.true_of_not_false(b: Bool, p: {b == False{} : Bool} -> Empty) ->
  {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, p({==}))

# Every word that survives a valid node's child list is the root guess.
def LBS.rem_word_g(+g: +List<Nat>, +kids: +List<Tree.Child>, +S: +List<+List<Nat>>,
    +w: +List<Nat>,
    +h: {Nat.is_le(1n, Twice.LB.mult(w, Part.LB.rem(g, kids, S))) == True{} : Bool},
    ad: Tree.AllHaveDepth(Tree.Node{g, kids}, S)) ->
  {Feedback.word_eq(g, w) == True{} : Bool}:
  LBS.true_of_not_false(Feedback.word_eq(g, w),
    nf => LBS.rem_word_contra(g, kids, S, w, nf, h, ad))

# The largest multiplicity of the leftover is at most that of the list.
def LBS.maxMult_rem_le(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>) ->
  {Nat.is_le(Twice.LB.maxMult(Part.LB.rem(g, kids, S)), Twice.LB.maxMult(S))
   == True{} : Bool}:
  match kids:
    case Nil{}:
      NatProof.Nat.is_le_refl(Twice.LB.maxMult(S))
    case Con{c, rest}:
      match c:
        case Tree.Child{f, t}:
          NatProof.Nat.is_le_trans(
            Twice.LB.maxMult(Part.LB.rem(g, rest, Part.LB.remw(g, f, S))),
            Twice.LB.maxMult(Part.LB.remw(g, f, S)), Twice.LB.maxMult(S),
            LBS.maxMult_rem_le(g, rest, Part.LB.remw(g, f, S)),
            Part.LB.maxMult_rem(g, f, S))

# Every word of a list that can still be reached by a child of `kids` is
# covered either as the guess or by a lookup in `kids`.
def LBS.mogW(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>) -> Type:
  {Bool.or(Feedback.word_eq(g, w),
     Maybe.is_some(&1, Tree.Tree, Tree.lookup(Feedback.feedback(g, w), kids)))
   == True{} : Bool}

def LBS.MogAll(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +W: +List<+List<Nat>>) -> Type:
  match W:
    case Nil{}:
      Unit
    case Con{h, t}:
      LBS.mogW(g, kids, h) & LBS.MogAll(g, kids, t)

# Transport the coverage along an equality of word lists.
def LBS.mog_eq(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +W1: +List<+List<Nat>>, +W2: +List<+List<Nat>>,
    e: {W1 == W2 : +List<+List<Nat>>}, p: LBS.MogAll(g, kids, W1)) ->
  LBS.MogAll(g, kids, W2):
  %e : LBS.MogAll(g, kids, _)
  p

# With no children left, coverage means every word is the guess, and such a
# list is no longer than the guess's multiplicity.
def LBS.mog_nil_len(+g: +List<Nat>, +W: +List<+List<Nat>>,
    p: LBS.MogAll(g, Nil{}, W)) ->
  {Nat.is_le(List.length(&2, +List<Nat>, W), Twice.LB.mult(g, W)) == True{} : Bool}:
  match W:
    case Nil{}:
      NatProof.Nat.is_le_refl(0n)
    case Con{a, t}:
      (ph, pt) = p
      +ew : {Feedback.word_eq(g, a) == True{} : Bool} =
        LBS.true_of_not_false(Feedback.word_eq(g, a),
          nf => Logic.Proof.true_ne_false(
            Equal.trans(Bool, True{},
              Bool.or(Feedback.word_eq(g, a),
                Maybe.is_some(&1, Tree.Tree, Tree.lookup(Feedback.feedback(g, a), Nil{}))),
              False{},
              Equal.sym(Bool,
                Bool.or(Feedback.word_eq(g, a),
                  Maybe.is_some(&1, Tree.Tree,
                    Tree.lookup(Feedback.feedback(g, a), Nil{}))), True{}, ph),
              Equal.trans(Bool,
                Bool.or(Feedback.word_eq(g, a),
                  Maybe.is_some(&1, Tree.Tree,
                    Tree.lookup(Feedback.feedback(g, a), Nil{}))),
                Bool.or(False{},
                  Maybe.is_some(&1, Tree.Tree,
                    Tree.lookup(Feedback.feedback(g, a), Nil{}))),
                False{},
                Equal.cong(Bool, Bool,
                  x => Bool.or(x, Maybe.is_some(&1, Tree.Tree,
                    Tree.lookup(Feedback.feedback(g, a), Nil{}))),
                  Feedback.word_eq(g, a), False{}, nf),
                Equal.trans(Bool,
                  Bool.or(False{},
                    Maybe.is_some(&1, Tree.Tree,
                      Tree.lookup(Feedback.feedback(g, a), Nil{}))),
                  Maybe.is_some(&1, Tree.Tree,
                    Tree.lookup(Feedback.feedback(g, a), Nil{})), False{},
                  LBS.or_false_l(Maybe.is_some(&1, Tree.Tree,
                    Tree.lookup(Feedback.feedback(g, a), Nil{}))),
                  {==})))))
      +hitg : {Twice.LB.hit(g, a) == 1n : Nat} =
        Equal.trans(Nat, Twice.LB.hit(g, a), Twice.LB.hit_bool(True{}), 1n,
          Twice.LB.hit_bool_eq(Feedback.word_eq(g, a), True{}, ew), {==})
      +ih : {Nat.is_le(List.length(&2, +List<Nat>, t), Twice.LB.mult(g, t))
             == True{} : Bool} =
        LBS.mog_nil_len(g, t, pt)
      NatProof.Nat.is_le_eq_r(
        Nat.add(1n, List.length(&2, +List<Nat>, t)),
        Nat.add(1n, Twice.LB.mult(g, t)),
        Nat.add(Twice.LB.hit(g, a), Twice.LB.mult(g, t)),
        Equal.sym(Nat, Nat.add(Twice.LB.hit(g, a), Twice.LB.mult(g, t)),
          Nat.add(1n, Twice.LB.mult(g, t)),
          Equal.cong(Nat, Nat, x => Nat.add(x, Twice.LB.mult(g, t)),
            Twice.LB.hit(g, a), 1n, hitg)),
        NatProof.Nat.is_le_succ(List.length(&2, +List<Nat>, t),
          Twice.LB.mult(g, t), ih))

# The node's depth facts give the coverage of its own child list.
def LBS.mog_init_go(+g: +List<Nat>, +kids: +List<Tree.Child>, +h: +List<Nat>,
    b: Bool, +eb: {b == Feedback.word_eq(g, h) : Bool},
    sh: {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, h)) == True{} : Bool}) ->
  LBS.mogW(g, kids, h):
  match b:
    case True{}:
      LBS.or_intro_l(Feedback.word_eq(g, h),
        Maybe.is_some(&1, Tree.Tree, Tree.lookup(Feedback.feedback(g, h), kids)),
        Equal.sym(Bool, b, Feedback.word_eq(g, h), eb))
    case False{}:
      +s1 : {Maybe.is_some(&1, Nat,
               Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, h), h)))
             == True{} : Bool} =
        Equal.trans(Bool,
          Maybe.is_some(&1, Nat,
            Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, h), h))),
          Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, h)), True{},
          Equal.cong(Maybe<Nat>, Bool, m2 => Maybe.is_some(&1, Nat, m2),
            Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, h), h)),
            Tree.depth(Tree.Node{g, kids}, h),
            Equal.sym(Maybe<Nat>, Tree.depth(Tree.Node{g, kids}, h),
              Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, h), h)),
              LBS.node_depth_false_go(g, kids, h, b, eb, {==}))),
          sh)
      +s2 : {Maybe.is_some(&1, Nat, Tree.depth.go(kids, Feedback.feedback(g, h), h))
             == True{} : Bool} =
        Equal.trans(Bool,
          Maybe.is_some(&1, Nat, Tree.depth.go(kids, Feedback.feedback(g, h), h)),
          Maybe.is_some(&1, Nat,
            Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, h), h))),
          True{},
          Equal.sym(Bool,
            Maybe.is_some(&1, Nat,
              Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, h), h))),
            Maybe.is_some(&1, Nat, Tree.depth.go(kids, Feedback.feedback(g, h), h)),
            NodeCost.NodeCost.is_some_bump(
              Tree.depth.go(kids, Feedback.feedback(g, h), h))),
          s1)
      +s2b : {Maybe.is_some(&1, Nat,
                 DepthProof.DepthProof.lookup_depth(
                   Tree.lookup(Feedback.feedback(g, h), kids), h)) == True{} : Bool} =
        Equal.trans(Bool,
          Maybe.is_some(&1, Nat,
            DepthProof.DepthProof.lookup_depth(
              Tree.lookup(Feedback.feedback(g, h), kids), h)),
          Maybe.is_some(&1, Nat, Tree.depth.go(kids, Feedback.feedback(g, h), h)),
          True{},
          Equal.cong(Maybe<Nat>, Bool, m2 => Maybe.is_some(&1, Nat, m2),
            DepthProof.DepthProof.lookup_depth(
              Tree.lookup(Feedback.feedback(g, h), kids), h),
            Tree.depth.go(kids, Feedback.feedback(g, h), h),
            Equal.sym(Maybe<Nat>, Tree.depth.go(kids, Feedback.feedback(g, h), h),
              DepthProof.DepthProof.lookup_depth(
                Tree.lookup(Feedback.feedback(g, h), kids), h),
              DepthProof.DepthProof.depth_go_lookup(kids, Feedback.feedback(g, h), h))),
          s2)
      +s3 : {Maybe.is_some(&1, Tree.Tree,
               Tree.lookup(Feedback.feedback(g, h), kids)) == True{} : Bool} =
        NodeCost.NodeCost.some_of_lookup_depth(
          Tree.lookup(Feedback.feedback(g, h), kids), h, s2b)
      LBS.or_intro_r(Feedback.word_eq(g, h),
        Maybe.is_some(&1, Tree.Tree, Tree.lookup(Feedback.feedback(g, h), kids)), s3)

def LBS.mog_init(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>,
    ad: Tree.AllHaveDepth(Tree.Node{g, kids}, S)) -> LBS.MogAll(g, kids, S):
  match S:
    case Nil{}:
      Unit{}
    case Con{h, t}:
      (sh, st) = ad
      (LBS.mog_init_go(g, kids, h, Feedback.word_eq(g, h), {==}, sh),
       LBS.mog_init(g, kids, t, st))

# A word the remaining children cannot reach is not reached by the whole list
# either.
def LBS.mog_keep_false_go(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +t: Tree.Tree, +rest: +List<Tree.Child>, +w: +List<Nat>, b: Bool,
    +eb: {b == Part.LB.keep(g, f, w) : Bool},
    hb: {b == False{} : Bool},
    x: Bool, +ex: {x == Feedback.word_eq(g, w) : Bool},
    hw: {Bool.or(x,
           Maybe.is_some(&1, Tree.Tree,
             Tree.lookup(Feedback.feedback(g, w), Tree.Child{f, t} <> rest)))
         == True{} : Bool}) ->
  {Bool.or(Feedback.word_eq(g, w),
     Maybe.is_some(&1, Tree.Tree, Tree.lookup(Feedback.feedback(g, w), rest)))
   == True{} : Bool}:
  match x:
    case True{}:
      +weq : {Feedback.word_eq(g, w) == True{} : Bool} =
        Equal.sym(Bool, x, Feedback.word_eq(g, w), ex)
      LBS.or_intro_l(Feedback.word_eq(g, w),
        Maybe.is_some(&1, Tree.Tree, Tree.lookup(Feedback.feedback(g, w), rest)), weq)
    case False{}:
      +weq : {Feedback.word_eq(g, w) == False{} : Bool} =
        Equal.sym(Bool, x, Feedback.word_eq(g, w), ex)
      +keepf : {Part.LB.keep(g, f, w) == False{} : Bool} =
        Equal.trans(Bool, Part.LB.keep(g, f, w), b, False{},
          Equal.sym(Bool, b, Part.LB.keep(g, f, w), eb), hb)
      +efb : {Feedback.feedback_eq(f, Feedback.feedback(g, w)) == False{} : Bool} =
        LBS.keep_false_r(Feedback.word_eq(g, w),
          Feedback.feedback_eq(f, Feedback.feedback(g, w)), keepf, weq)
      +ebf : {Feedback.feedback_eq(Feedback.feedback(g, w), f) == False{} : Bool} =
        Equal.trans(Bool, Feedback.feedback_eq(Feedback.feedback(g, w), f),
          Feedback.feedback_eq(f, Feedback.feedback(g, w)), False{},
          FbProof.FeedbackProof.feedback_eq_sym_bool(Feedback.feedback(g, w), f), efb)
      +lookup_eq : {Tree.lookup(Feedback.feedback(g, w), Tree.Child{f, t} <> rest)
                    == Tree.lookup(Feedback.feedback(g, w), rest)
                    : Maybe<&1, Tree.Tree>} =
        Equal.trans(Maybe<&1, Tree.Tree>,
          Tree.lookup(Feedback.feedback(g, w), Tree.Child{f, t} <> rest),
          Feedback.Bool.case(Maybe<Tree.Tree>,
            Feedback.feedback_eq(Feedback.feedback(g, w), f),
            Some{t}, Tree.lookup(Feedback.feedback(g, w), rest)),
          Tree.lookup(Feedback.feedback(g, w), rest),
          {==},
          Equal.cong(Bool, Maybe<Tree.Tree>,
            b2 => Feedback.Bool.case(Maybe<Tree.Tree>, b2, Some{t},
              Tree.lookup(Feedback.feedback(g, w), rest)),
            Feedback.feedback_eq(Feedback.feedback(g, w), f), False{}, ebf))
      +hAB : {Maybe.is_some(&1, Tree.Tree,
                Tree.lookup(Feedback.feedback(g, w), Tree.Child{f, t} <> rest))
              == Maybe.is_some(&1, Tree.Tree,
                   Tree.lookup(Feedback.feedback(g, w), rest)) : Bool} =
        Equal.cong(Maybe<&1, Tree.Tree>, Bool, m2 => Maybe.is_some(&1, Tree.Tree, m2),
          Tree.lookup(Feedback.feedback(g, w), Tree.Child{f, t} <> rest),
          Tree.lookup(Feedback.feedback(g, w), rest), lookup_eq)
      +hA : {Maybe.is_some(&1, Tree.Tree,
                Tree.lookup(Feedback.feedback(g, w), Tree.Child{f, t} <> rest))
              == True{} : Bool} =
        Equal.trans(Bool,
          Maybe.is_some(&1, Tree.Tree,
            Tree.lookup(Feedback.feedback(g, w), Tree.Child{f, t} <> rest)),
          Bool.or(False{}, Maybe.is_some(&1, Tree.Tree,
            Tree.lookup(Feedback.feedback(g, w), Tree.Child{f, t} <> rest))),
          True{},
          Equal.sym(Bool,
            Bool.or(False{}, Maybe.is_some(&1, Tree.Tree,
              Tree.lookup(Feedback.feedback(g, w), Tree.Child{f, t} <> rest))),
            Maybe.is_some(&1, Tree.Tree,
              Tree.lookup(Feedback.feedback(g, w), Tree.Child{f, t} <> rest)),
            LBS.or_false_l(Maybe.is_some(&1, Tree.Tree,
              Tree.lookup(Feedback.feedback(g, w), Tree.Child{f, t} <> rest)))),
          hw)
      +hB : {Maybe.is_some(&1, Tree.Tree,
                Tree.lookup(Feedback.feedback(g, w), rest)) == True{} : Bool} =
        Equal.trans(Bool,
          Maybe.is_some(&1, Tree.Tree, Tree.lookup(Feedback.feedback(g, w), rest)),
          Maybe.is_some(&1, Tree.Tree,
            Tree.lookup(Feedback.feedback(g, w), Tree.Child{f, t} <> rest)),
          True{}, Equal.sym(Bool,
            Maybe.is_some(&1, Tree.Tree,
              Tree.lookup(Feedback.feedback(g, w), Tree.Child{f, t} <> rest)),
            Maybe.is_some(&1, Tree.Tree, Tree.lookup(Feedback.feedback(g, w), rest)),
            hAB), hA)
      LBS.or_intro_r(Feedback.word_eq(g, w),
        Maybe.is_some(&1, Tree.Tree, Tree.lookup(Feedback.feedback(g, w), rest)), hB)

def LBS.mog_remw_go(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +t: Tree.Tree, +rest: +List<Tree.Child>, +h: +List<Nat>,
    +tl: +List<+List<Nat>>, b: Bool,
    +eb: {b == Part.LB.keep(g, f, h) : Bool},
    hw: LBS.mogW(g, Tree.Child{f, t} <> rest, h),
    ih: LBS.MogAll(g, rest, Part.LB.remw(g, f, tl))) ->
  LBS.MogAll(g, rest, Part.LB.remw_of(g, f, h, tl, b)):
  match b:
    case True{}:
      ih
    case False{}:
      hd : LBS.mogW(g, rest, h) =
        LBS.mog_keep_false_go(g, f, t, rest, h, False{}, eb, {==},
          Feedback.word_eq(g, h), {==}, hw)
      (hd, ih)

def LBS.mog_remw(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +t: Tree.Tree, +rest: +List<Tree.Child>, +W: +List<+List<Nat>>,
    p: LBS.MogAll(g, Tree.Child{f, t} <> rest, W)) ->
  LBS.MogAll(g, rest, Part.LB.remw(g, f, W)):
  match W:
    case Nil{}:
      Unit{}
    case Con{h, tl}:
      (hw, ht) = p
      +b : Bool = Part.LB.keep(g, f, h)
      core : LBS.MogAll(g, rest, Part.LB.remw_of(g, f, h, tl, b)) =
        LBS.mog_remw_go(g, f, t, rest, h, tl, b, {==}, hw,
          LBS.mog_remw(g, f, t, rest, tl, ht))
      LBS.mog_eq(g, rest, Part.LB.remw(g, f, h <> tl),
        Part.LB.remw_of(g, f, h, tl, b),
        Part.LB.remw_eq(g, f, h, tl, b, {==}), core)

# The coverage carried through the whole scan: the words left over at the end
# are all the guess.
def LBS.mog_scan(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +W: +List<+List<Nat>>, p: LBS.MogAll(g, kids, W)) ->
  LBS.MogAll(g, Nil{}, Part.LB.rem(g, kids, W)):
  match kids:
    case Nil{}:
      p
    case Con{c, rest}:
      match c:
        case Tree.Child{f, t}:
          LBS.mog_scan(g, rest, Part.LB.remw(g, f, W),
            LBS.mog_remw(g, f, t, rest, W, p))

# A valid node without duplicate candidates leaves at most one candidate
# outside its classes.
def LBS.len_rem_le_one(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>,
    +nd: {Nat.is_le(Twice.LB.maxMult(S), 1n) == True{} : Bool},
    ad: Tree.AllHaveDepth(Tree.Node{g, kids}, S)) ->
  {Nat.is_le(List.length(&2, +List<Nat>, Part.LB.rem(g, kids, S)), 1n)
   == True{} : Bool}:
  +h1 : {Nat.is_le(List.length(&2, +List<Nat>, Part.LB.rem(g, kids, S)),
                   Twice.LB.mult(g, Part.LB.rem(g, kids, S))) == True{} : Bool} =
    LBS.mog_nil_len(g, Part.LB.rem(g, kids, S),
      LBS.mog_scan(g, kids, S, LBS.mog_init(g, kids, S, ad)))
  +h2 : {Nat.is_le(Twice.LB.mult(g, Part.LB.rem(g, kids, S)),
                   Twice.LB.maxMult(Part.LB.rem(g, kids, S))) == True{} : Bool} =
    Twice.LB.mult_le_maxMult(g, Part.LB.rem(g, kids, S))
  +h3 : {Nat.is_le(Twice.LB.maxMult(Part.LB.rem(g, kids, S)),
                   Twice.LB.maxMult(S)) == True{} : Bool} =
    LBS.maxMult_rem_le(g, kids, S)
  NatProof.Nat.is_le_trans(List.length(&2, +List<Nat>, Part.LB.rem(g, kids, S)),
    Twice.LB.maxMult(Part.LB.rem(g, kids, S)), 1n,
    NatProof.Nat.is_le_trans(List.length(&2, +List<Nat>, Part.LB.rem(g, kids, S)),
      Twice.LB.mult(g, Part.LB.rem(g, kids, S)),
      Twice.LB.maxMult(Part.LB.rem(g, kids, S)), h1, h2),
    NatProof.Nat.is_le_trans(Twice.LB.maxMult(Part.LB.rem(g, kids, S)),
      Twice.LB.maxMult(S), 1n, h3, nd))

# --- The class scan --------------------------------------------------------

# A kept word's own depth facts at its node: a non-empty class is found by the
# node's lookup.
def LBS.keepw_head_some(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +fb: +List<Feedback.Color>, +h: +List<Nat>,
    sh: {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, h)) == True{} : Bool},
    +eb: {True{} == Part.LB.keep(g, fb, h) : Bool}) ->
  {Maybe.is_some(&1, Tree.Tree, Tree.lookup(fb, kids)) == True{} : Bool}:
  +nw : {Feedback.word_eq(g, h) == False{} : Bool} =
    LBS.keep_true_l(Feedback.word_eq(g, h),
      Feedback.feedback_eq(fb, Feedback.feedback(g, h)),
      Equal.sym(Bool, True{}, Part.LB.keep(g, fb, h), eb))
  +nf : {Feedback.feedback_eq(fb, Feedback.feedback(g, h)) == True{} : Bool} =
    LBS.keep_true_r(Feedback.word_eq(g, h),
      Feedback.feedback_eq(fb, Feedback.feedback(g, h)),
      Equal.sym(Bool, True{}, Part.LB.keep(g, fb, h), eb))
  +ef : {Feedback.feedback(g, h) == fb : +List<Feedback.Color>} =
    Equal.sym(+List<Feedback.Color>, fb, Feedback.feedback(g, h),
      FbProof.FbPrf.feedback_eq_true(fb, Feedback.feedback(g, h), nf))
  +s1 : {Maybe.is_some(&1, Nat,
           Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, h), h)))
         == True{} : Bool} =
    Equal.trans(Bool,
      Maybe.is_some(&1, Nat,
        Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, h), h))),
      Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, h)), True{},
      Equal.cong(Maybe<Nat>, Bool, m2 => Maybe.is_some(&1, Nat, m2),
        Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, h), h)),
        Tree.depth(Tree.Node{g, kids}, h),
        Equal.sym(Maybe<Nat>, Tree.depth(Tree.Node{g, kids}, h),
          Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, h), h)),
          LBS.node_depth_false_go(g, kids, h, Feedback.word_eq(g, h), {==}, nw))),
      sh)
  +s2 : {Maybe.is_some(&1, Nat, Tree.depth.go(kids, Feedback.feedback(g, h), h))
         == True{} : Bool} =
    Equal.trans(Bool,
      Maybe.is_some(&1, Nat, Tree.depth.go(kids, Feedback.feedback(g, h), h)),
      Maybe.is_some(&1, Nat,
        Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, h), h))),
      True{},
      Equal.sym(Bool,
        Maybe.is_some(&1, Nat,
          Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, h), h))),
        Maybe.is_some(&1, Nat, Tree.depth.go(kids, Feedback.feedback(g, h), h)),
        NodeCost.NodeCost.is_some_bump(
          Tree.depth.go(kids, Feedback.feedback(g, h), h))),
      s1)
  +s2b : {Maybe.is_some(&1, Nat,
             DepthProof.DepthProof.lookup_depth(
               Tree.lookup(Feedback.feedback(g, h), kids), h)) == True{} : Bool} =
    Equal.trans(Bool,
      Maybe.is_some(&1, Nat,
        DepthProof.DepthProof.lookup_depth(
          Tree.lookup(Feedback.feedback(g, h), kids), h)),
      Maybe.is_some(&1, Nat, Tree.depth.go(kids, Feedback.feedback(g, h), h)),
      True{},
      Equal.cong(Maybe<Nat>, Bool, m2 => Maybe.is_some(&1, Nat, m2),
        DepthProof.DepthProof.lookup_depth(
          Tree.lookup(Feedback.feedback(g, h), kids), h),
        Tree.depth.go(kids, Feedback.feedback(g, h), h),
        Equal.sym(Maybe<Nat>, Tree.depth.go(kids, Feedback.feedback(g, h), h),
          DepthProof.DepthProof.lookup_depth(
            Tree.lookup(Feedback.feedback(g, h), kids), h),
          DepthProof.DepthProof.depth_go_lookup(kids, Feedback.feedback(g, h), h))),
      s2)
  +s3 : {Maybe.is_some(&1, Tree.Tree,
           Tree.lookup(Feedback.feedback(g, h), kids)) == True{} : Bool} =
    NodeCost.NodeCost.some_of_lookup_depth(
      Tree.lookup(Feedback.feedback(g, h), kids), h, s2b)
  Equal.trans(Bool,
    Maybe.is_some(&1, Tree.Tree, Tree.lookup(fb, kids)),
    Maybe.is_some(&1, Tree.Tree, Tree.lookup(Feedback.feedback(g, h), kids)),
    True{},
    Equal.cong(+List<Feedback.Color>, Bool,
      x => Maybe.is_some(&1, Tree.Tree, Tree.lookup(x, kids)), fb,
      Feedback.feedback(g, h), Equal.sym(+List<Feedback.Color>,
        Feedback.feedback(g, h), fb, ef)),
    s3)

# A failed lookup is not a found child.
def LBS.lookup_some_ne_none(+fb: +List<Feedback.Color>, +kids: +List<Tree.Child>,
    lk: {Tree.lookup(fb, kids) == None{} : Maybe<&1, Tree.Tree>},
    s: {Maybe.is_some(&1, Tree.Tree, Tree.lookup(fb, kids)) == True{} : Bool}) -> Empty:
  +s0 : {Maybe.is_some(&1, Tree.Tree, None{}) == True{} : Bool} =
    Equal.trans(Bool, Maybe.is_some(&1, Tree.Tree, None{}),
      Maybe.is_some(&1, Tree.Tree, Tree.lookup(fb, kids)), True{},
      Equal.cong(Maybe<&1, Tree.Tree>, Bool, m2 => Maybe.is_some(&1, Tree.Tree, m2),
        None{}, Tree.lookup(fb, kids), Equal.sym(Maybe<&1, Tree.Tree>,
          Tree.lookup(fb, kids), None{}, lk)),
      s)
  Logic.Proof.false_ne_true(s0)

# A class that the lookup cannot find has no words.
def LBS.keepw_nil_go(+g: +List<Nat>, +fb: +List<Feedback.Color>,
    +kids: +List<Tree.Child>, +h: +List<Nat>, +tl: +List<+List<Nat>>, b: Bool,
    +eb: {b == Part.LB.keep(g, fb, h) : Bool},
    sh: {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, h)) == True{} : Bool},
    +lk: {Tree.lookup(fb, kids) == None{} : Maybe<&1, Tree.Tree>},
    ih: {Part.LB.keepw_b(g, fb, tl) == Nil{} : +List<+List<Nat>>})
    -> {Part.LB.keepw_of(g, fb, h, tl, b) == Nil{} : +List<+List<Nat>>}:
  match b:
    case True{}:
      Empty.absurd({Part.LB.keepw_of(g, fb, h, tl, True{}) == Nil{}
                    : +List<+List<Nat>>},
        LBS.lookup_some_ne_none(fb, kids, lk,
          LBS.keepw_head_some(g, kids, fb, h, sh, eb)))
    case False{}:
      ih

def LBS.keepw_nil(+g: +List<Nat>, +fb: +List<Feedback.Color>,
    +kids: +List<Tree.Child>, +W: +List<+List<Nat>>,
    ad: Tree.AllHaveDepth(Tree.Node{g, kids}, W),
    +lk: {Tree.lookup(fb, kids) == None{} : Maybe<&1, Tree.Tree>}) ->
  {Part.LB.keepw_b(g, fb, W) == Nil{} : +List<+List<Nat>>}:
  match W:
    case Nil{}:
      {==}
    case Con{h, tl}:
      (sh, st) = ad
      +b : Bool = Part.LB.keep(g, fb, h)
      +core : {Part.LB.keepw_of(g, fb, h, tl, b) == Nil{} : +List<+List<Nat>>} =
        LBS.keepw_nil_go(g, fb, kids, h, tl, b, {==}, sh, lk,
          LBS.keepw_nil(g, fb, kids, tl, st, lk))
      Equal.trans(+List<+List<Nat>>, Part.LB.keepw_b(g, fb, h <> tl),
        Part.LB.keepw_of(g, fb, h, tl, b), Nil{},
        Part.LB.keepw_eq(g, fb, h, tl, b, {==}), core)

# --- Membership and the first-match scan -----------------------------------

# Boolean membership of a word in a candidate list.
def LBS.mem(+w: +List<Nat>, +S: +List<+List<Nat>>) -> Bool:
  match S:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Feedback.word_eq(w, h), LBS.mem(w, t))

def LBS.or_true_l(+b: Bool) -> {Bool.or(True{}, b) == True{} : Bool}:
  {==}

# A member of the leftover filter is a member of the list.
def LBS.mem_remw_mem_go(+g: +List<Nat>, +f: +List<Feedback.Color>, +w: +List<Nat>,
    +h: +List<Nat>, +t: +List<+List<Nat>>, b: Bool,
    +eb: {b == Part.LB.keep(g, f, h) : Bool},
    x: Bool, +ex: {x == Feedback.word_eq(w, h) : Bool},
    k: @p: {LBS.mem(w, Part.LB.remw(g, f, t)) == True{} : Bool}
       -> {LBS.mem(w, t) == True{} : Bool},
    p: {LBS.mem(w, Part.LB.remw_of(g, f, h, t, b)) == True{} : Bool}) ->
  {Bool.or(x, LBS.mem(w, t)) == True{} : Bool}:
  match b:
    case True{}:
      match x:
        case True{}:
          LBS.or_true_l(LBS.mem(w, t))
        case False{}:
          +hm : {LBS.mem(w, Part.LB.remw(g, f, t)) == True{} : Bool} =
            LBS.or_elim_r(x, LBS.mem(w, Part.LB.remw(g, f, t)), p, {==})
          LBS.or_intro_r(x, LBS.mem(w, t), k(hm))
    case False{}:
      match x:
        case True{}:
          LBS.or_true_l(LBS.mem(w, t))
        case False{}:
          +ew : {Feedback.word_eq(w, h) == False{} : Bool} =
            Equal.sym(Bool, x, Feedback.word_eq(w, h), ex)
          +hm : {LBS.mem(w, Part.LB.remw(g, f, t)) == True{} : Bool} =
            LBS.or_elim_r(Feedback.word_eq(w, h), LBS.mem(w, Part.LB.remw(g, f, t)),
              p, ew)
          LBS.or_intro_r(x, LBS.mem(w, t), k(hm))

def LBS.mem_remw_mem(+g: +List<Nat>, +f: +List<Feedback.Color>, +w: +List<Nat>,
    +S: +List<+List<Nat>>, p: {LBS.mem(w, Part.LB.remw(g, f, S)) == True{} : Bool}) ->
  {LBS.mem(w, S) == True{} : Bool}:
  match S:
    case Nil{}:
      Empty.absurd({LBS.mem(w, Nil{}) == True{} : Bool},
        Logic.Proof.false_ne_true(p))
    case Con{h, t}:
      +b : Bool = Part.LB.keep(g, f, h)
      +x : Bool = Feedback.word_eq(w, h)
      +p2 : {LBS.mem(w, Part.LB.remw_of(g, f, h, t, b)) == True{} : Bool} =
        Equal.trans(Bool, LBS.mem(w, Part.LB.remw(g, f, h <> t)),
          LBS.mem(w, Part.LB.remw_of(g, f, h, t, b)), True{},
          Equal.cong(+List<+List<Nat>>, Bool, y => LBS.mem(w, y),
            Part.LB.remw(g, f, h <> t), Part.LB.remw_of(g, f, h, t, b),
            Part.LB.remw_eq(g, f, h, t, b, {==})),
          p)
      LBS.mem_remw_mem_go(g, f, w, h, t, b, {==}, x, {==},
        q => LBS.mem_remw_mem(g, f, w, t, q), p2)

# A word that survives the leftover filter fails that filter's keep test.
def LBS.mem_remw_keep_go(+g: +List<Nat>, +f: +List<Feedback.Color>, +w: +List<Nat>,
    +h: +List<Nat>, +t: +List<+List<Nat>>, b: Bool,
    +eb: {b == Part.LB.keep(g, f, h) : Bool},
    x: Bool, +ex: {x == Feedback.word_eq(w, h) : Bool},
    k: @p: {LBS.mem(w, Part.LB.remw(g, f, t)) == True{} : Bool}
       -> {Part.LB.keep(g, f, w) == False{} : Bool},
    p: {LBS.mem(w, Part.LB.remw_of(g, f, h, t, b)) == True{} : Bool}) ->
  {Part.LB.keep(g, f, w) == False{} : Bool}:
  match b:
    case True{}:
      k(p)
    case False{}:
      match x:
        case True{}:
          +eq : {w == h : +List<Nat>} =
            CoverList.Cover.word_eq_true(w, h, Equal.sym(Bool, x, Feedback.word_eq(w, h), ex))
          Equal.trans(Bool, Part.LB.keep(g, f, w), Part.LB.keep(g, f, h), False{},
            Equal.cong(+List<Nat>, Bool, y => Part.LB.keep(g, f, y), w, h, eq),
            Equal.sym(Bool, False{}, Part.LB.keep(g, f, h), eb))
        case False{}:
          +ew : {Feedback.word_eq(w, h) == False{} : Bool} =
            Equal.sym(Bool, x, Feedback.word_eq(w, h), ex)
          +hm : {LBS.mem(w, Part.LB.remw(g, f, t)) == True{} : Bool} =
            LBS.or_elim_r(Feedback.word_eq(w, h), LBS.mem(w, Part.LB.remw(g, f, t)),
              p, ew)
          k(hm)

def LBS.mem_remw_keep(+g: +List<Nat>, +f: +List<Feedback.Color>, +w: +List<Nat>,
    +S: +List<+List<Nat>>, p: {LBS.mem(w, Part.LB.remw(g, f, S)) == True{} : Bool}) ->
  {Part.LB.keep(g, f, w) == False{} : Bool}:
  match S:
    case Nil{}:
      Empty.absurd({Part.LB.keep(g, f, w) == False{} : Bool},
        Logic.Proof.false_ne_true(p))
    case Con{h, t}:
      +b : Bool = Part.LB.keep(g, f, h)
      +x : Bool = Feedback.word_eq(w, h)
      +p2 : {LBS.mem(w, Part.LB.remw_of(g, f, h, t, b)) == True{} : Bool} =
        Equal.trans(Bool, LBS.mem(w, Part.LB.remw(g, f, h <> t)),
          LBS.mem(w, Part.LB.remw_of(g, f, h, t, b)), True{},
          Equal.cong(+List<+List<Nat>>, Bool, y => LBS.mem(w, y),
            Part.LB.remw(g, f, h <> t), Part.LB.remw_of(g, f, h, t, b),
            Part.LB.remw_eq(g, f, h, t, b, {==})),
          p)
      LBS.mem_remw_keep_go(g, f, w, h, t, b, {==}, x, {==},
        q => LBS.mem_remw_keep(g, f, w, t, q), p2)


# The words no child of the prefix takes, from the whole candidate list.
def LBS.remFold(+g: +List<Nat>, +pre: +List<Tree.Child>,
    +S: +List<+List<Nat>>) -> +List<+List<Nat>>:
  match pre:
    case Nil{}:
      S
    case Con{c, rest}:
      match c:
        case Tree.Child{f, t}:
          LBS.remFold(g, rest, Part.LB.remw(g, f, S))

# Every child of the prefix fails its keep test on a leftover word.
def LBS.NoKeep(+g: +List<Nat>, +pre: +List<Tree.Child>,
    +w: +List<Nat>) -> Type:
  match pre:
    case Nil{}:
      Unit
    case Con{c, rest}:
      match c:
        case Tree.Child{f, t}:
          {Part.LB.keep(g, f, w) == False{} : Bool} & LBS.NoKeep(g, rest, w)

# No child of the prefix has this feedback.
def LBS.NoFB(+pre: +List<Tree.Child>, +f: +List<Feedback.Color>) -> Type:
  match pre:
    case Nil{}:
      Unit
    case Con{c, rest}:
      match c:
        case Tree.Child{f0, t}:
          {Feedback.feedback_eq(f0, f) == False{} : Bool} & LBS.NoFB(rest, f)

# A word of the prefix-filtered list is a word of the list.
def LBS.mem_remFold_mem(+g: +List<Nat>, +pre: +List<Tree.Child>,
    +S: +List<+List<Nat>>, +w: +List<Nat>,
    +p: {LBS.mem(w, LBS.remFold(g, pre, S)) == True{} : Bool}) ->
  {LBS.mem(w, S) == True{} : Bool}:
  match pre:
    case Nil{}:
      p
    case Con{c, rest}:
      match c:
        case Tree.Child{f, t}:
          LBS.mem_remw_mem(g, f, w, S,
            LBS.mem_remFold_mem(g, rest, Part.LB.remw(g, f, S), w, p))

# A leftover word of the prefix-filtered list fails every prefix keep test.
def LBS.remFold_keep(+g: +List<Nat>, +pre: +List<Tree.Child>,
    +S: +List<+List<Nat>>, +w: +List<Nat>,
    +p: {LBS.mem(w, LBS.remFold(g, pre, S)) == True{} : Bool}) ->
  LBS.NoKeep(g, pre, w):
  match pre:
    case Nil{}:
      Unit{}
    case Con{c, rest}:
      match c:
        case Tree.Child{f, t}:
          +hm : {LBS.mem(w, Part.LB.remw(g, f, S)) == True{} : Bool} =
            LBS.mem_remFold_mem(g, rest, Part.LB.remw(g, f, S), w, p)
          (LBS.mem_remw_keep(g, f, w, S, hm),
           LBS.remFold_keep(g, rest, Part.LB.remw(g, f, S), w, p))

# The head of a keep-failure conjunction.
def LBS.nokeep_head(+g: +List<Nat>, +f: +List<Feedback.Color>, +t: Tree.Tree,
    +rest: +List<Tree.Child>, +w: +List<Nat>,
    hk: LBS.NoKeep(g, Tree.Child{f, t} <> rest, w)) ->
  {Part.LB.keep(g, f, w) == False{} : Bool}:
  (kf, kr) = hk
  kf

# The prefix has no child with the class's feedback.
def LBS.remFold_nofb(+g: +List<Nat>, +pre: +List<Tree.Child>,
    +S: +List<+List<Nat>>, +w: +List<Nat>,
    +nf: {Feedback.word_eq(g, w) == False{} : Bool},
    +p: {LBS.mem(w, LBS.remFold(g, pre, S)) == True{} : Bool}) ->
  LBS.NoFB(pre, Feedback.feedback(g, w)):
  match pre:
    case Nil{}:
      Unit{}
    case Con{c, rest}:
      match c:
        case Tree.Child{f, t}:
          (LBS.keep_false_r(Feedback.word_eq(g, w),
             Feedback.feedback_eq(f, Feedback.feedback(g, w)),
             LBS.nokeep_head(g, f, t, rest, w, LBS.remFold_keep(g, pre, S, w, p)), nf),
           LBS.remFold_nofb(g, rest, Part.LB.remw(g, f, S), w, nf, p))

# A child list whose first child has the wanted feedback looks that child up.
def LBS.lookup_head_go(+fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +t: Tree.Tree, +rest: +List<Tree.Child>, b: Bool,
    +eb: {b == Feedback.feedback_eq(fb, f) : Bool},
    hb: {b == True{} : Bool}) ->
  {Tree.lookup(fb, Tree.Child{f, t} <> rest) == Some{t} : Maybe<&1, Tree.Tree>}:
  match b:
    case True{}:
      +e1 : {Tree.lookup(fb, Tree.Child{f, t} <> rest)
            == Feedback.Bool.case(Maybe<Tree.Tree>, Feedback.feedback_eq(fb, f),
                 Some{t}, Tree.lookup(fb, rest)) : Maybe<&1, Tree.Tree>} =
        {==}
      +e2 : {Feedback.Bool.case(Maybe<Tree.Tree>, Feedback.feedback_eq(fb, f),
                  Some{t}, Tree.lookup(fb, rest))
             == Some{t} : Maybe<&1, Tree.Tree>} =
        Equal.cong(Bool, Maybe<Tree.Tree>,
          b2 => Feedback.Bool.case(Maybe<Tree.Tree>, b2, Some{t}, Tree.lookup(fb, rest)),
          Feedback.feedback_eq(fb, f), True{},
          Equal.trans(Bool, Feedback.feedback_eq(fb, f), b, True{},
            Equal.sym(Bool, b, Feedback.feedback_eq(fb, f), eb), hb))
      Equal.trans(Maybe<&1, Tree.Tree>, Tree.lookup(fb, Tree.Child{f, t} <> rest),
        Feedback.Bool.case(Maybe<Tree.Tree>, Feedback.feedback_eq(fb, f),
          Some{t}, Tree.lookup(fb, rest)), Some{t}, e1, e2)
    case False{}:
      Empty.absurd({Tree.lookup(fb, Tree.Child{f, t} <> rest) == Some{t}
                    : Maybe<&1, Tree.Tree>},
        Logic.Proof.false_ne_true(hb))

def LBS.lookup_head(+f: +List<Feedback.Color>, +t: Tree.Tree,
    +rest: +List<Tree.Child>) ->
  {Tree.lookup(f, Tree.Child{f, t} <> rest) == Some{t} : Maybe<&1, Tree.Tree>}:
  LBS.lookup_head_go(f, f, t, rest, Feedback.feedback_eq(f, f), {==},
    FbProof.FbPrf.feedback_eq_refl(f))

# A prefix without the wanted feedback is skipped by the lookup.
def LBS.lookup_skip_any(+fb: +List<Feedback.Color>, +f0: +List<Feedback.Color>,
    +t0: Tree.Tree, +X: +List<Tree.Child>, M: Maybe<Tree.Tree>, b: Bool,
    +eb: {b == Feedback.feedback_eq(fb, f0) : Bool},
    hb: {b == False{} : Bool},
    ih: {Tree.lookup(fb, X) == M : Maybe<&1, Tree.Tree>}) ->
  {Tree.lookup(fb, Tree.Child{f0, t0} <> X) == M : Maybe<&1, Tree.Tree>}:
  match b:
    case True{}:
      Empty.absurd({Tree.lookup(fb, Tree.Child{f0, t0} <> X) == M : Maybe<&1, Tree.Tree>},
        Logic.Proof.true_ne_false(hb))
    case False{}:
      +e1 : {Tree.lookup(fb, Tree.Child{f0, t0} <> X)
            == Feedback.Bool.case(Maybe<Tree.Tree>, Feedback.feedback_eq(fb, f0),
                 Some{t0}, Tree.lookup(fb, X)) : Maybe<&1, Tree.Tree>} =
        {==}
      +e2 : {Feedback.Bool.case(Maybe<Tree.Tree>, Feedback.feedback_eq(fb, f0),
                  Some{t0}, Tree.lookup(fb, X))
             == Tree.lookup(fb, X) : Maybe<&1, Tree.Tree>} =
        Equal.cong(Bool, Maybe<Tree.Tree>,
          b2 => Feedback.Bool.case(Maybe<Tree.Tree>, b2, Some{t0}, Tree.lookup(fb, X)),
          Feedback.feedback_eq(fb, f0), False{},
          Equal.trans(Bool, Feedback.feedback_eq(fb, f0), b, False{},
            Equal.sym(Bool, b, Feedback.feedback_eq(fb, f0), eb), hb))
      +e12 : {Tree.lookup(fb, Tree.Child{f0, t0} <> X) == Tree.lookup(fb, X)
              : Maybe<&1, Tree.Tree>} =
        Equal.trans(Maybe<&1, Tree.Tree>, Tree.lookup(fb, Tree.Child{f0, t0} <> X),
          Feedback.Bool.case(Maybe<Tree.Tree>, Feedback.feedback_eq(fb, f0),
            Some{t0}, Tree.lookup(fb, X)), Tree.lookup(fb, X), e1, e2)
      Equal.trans(Maybe<&1, Tree.Tree>, Tree.lookup(fb, Tree.Child{f0, t0} <> X),
        Tree.lookup(fb, X), M, e12, ih)

def LBS.lookup_skip_pre(+f: +List<Feedback.Color>, +pre: +List<Tree.Child>,
    +X: +List<Tree.Child>, p: LBS.NoFB(pre, f)) ->
  {Tree.lookup(f, List.append(&2, Tree.Child, pre, X)) == Tree.lookup(f, X)
   : Maybe<&1, Tree.Tree>}:
  match pre:
    case Nil{}:
      {==}
    case Con{c, rest}:
      match c:
        case Tree.Child{f0, t0}:
          (nf0, nr) = p
          +ef0 : {Feedback.feedback_eq(f, f0) == False{} : Bool} =
            Equal.trans(Bool, Feedback.feedback_eq(f, f0),
              Feedback.feedback_eq(f0, f), False{},
              FbProof.FeedbackProof.feedback_eq_sym_bool(f, f0), nf0)
          +ih : {Tree.lookup(f, List.append(&2, Tree.Child, rest, X))
                 == Tree.lookup(f, X) : Maybe<&1, Tree.Tree>} =
            LBS.lookup_skip_pre(f, rest, X, nr)
          LBS.lookup_skip_any(f, f0, t0, List.append(&2, Tree.Child, rest, X),
            Tree.lookup(f, X), Feedback.feedback_eq(f, f0), {==}, ef0, ih)

# A member of the kept filter is a member of the list.
def LBS.mem_keepw_mem_go(+g: +List<Nat>, +f: +List<Feedback.Color>, +w: +List<Nat>,
    +h: +List<Nat>, +t: +List<+List<Nat>>, b: Bool,
    +eb: {b == Part.LB.keep(g, f, h) : Bool},
    x: Bool, +ex: {x == Feedback.word_eq(w, h) : Bool},
    k: @p: {LBS.mem(w, Part.LB.keepw_b(g, f, t)) == True{} : Bool}
       -> {LBS.mem(w, t) == True{} : Bool},
    p: {LBS.mem(w, Part.LB.keepw_of(g, f, h, t, b)) == True{} : Bool}) ->
  {Bool.or(x, LBS.mem(w, t)) == True{} : Bool}:
  match b:
    case True{}:
      match x:
        case True{}:
          LBS.or_true_l(LBS.mem(w, t))
        case False{}:
          +ew : {Feedback.word_eq(w, h) == False{} : Bool} =
            Equal.sym(Bool, x, Feedback.word_eq(w, h), ex)
          +hm : {LBS.mem(w, Part.LB.keepw_b(g, f, t)) == True{} : Bool} =
            LBS.or_elim_r(Feedback.word_eq(w, h),
              LBS.mem(w, Part.LB.keepw_b(g, f, t)), p, ew)
          LBS.or_intro_r(x, LBS.mem(w, t), k(hm))
    case False{}:
      LBS.or_intro_r(x, LBS.mem(w, t), k(p))

def LBS.mem_keepw_mem(+g: +List<Nat>, +f: +List<Feedback.Color>, +w: +List<Nat>,
    +S: +List<+List<Nat>>, p: {LBS.mem(w, Part.LB.keepw_b(g, f, S)) == True{} : Bool}) ->
  {LBS.mem(w, S) == True{} : Bool}:
  match S:
    case Nil{}:
      Empty.absurd({LBS.mem(w, Nil{}) == True{} : Bool}, Logic.Proof.false_ne_true(p))
    case Con{h, t}:
      +b : Bool = Part.LB.keep(g, f, h)
      +x : Bool = Feedback.word_eq(w, h)
      +p2 : {LBS.mem(w, Part.LB.keepw_of(g, f, h, t, b)) == True{} : Bool} =
        Equal.trans(Bool, LBS.mem(w, Part.LB.keepw_b(g, f, h <> t)),
          LBS.mem(w, Part.LB.keepw_of(g, f, h, t, b)), True{},
          Equal.cong(+List<+List<Nat>>, Bool, y => LBS.mem(w, y),
            Part.LB.keepw_b(g, f, h <> t), Part.LB.keepw_of(g, f, h, t, b),
            Part.LB.keepw_eq(g, f, h, t, b, {==})),
          p)
      LBS.mem_keepw_mem_go(g, f, w, h, t, b, {==}, x, {==},
        q => LBS.mem_keepw_mem(g, f, w, t, q), p2)

# The head of a non-empty list is a member.
def LBS.mem_head(+h: +List<Nat>, +tl: +List<+List<Nat>>) ->
  {LBS.mem(h, h <> tl) == True{} : Bool}:
  LBS.or_intro_l(Feedback.word_eq(h, h), LBS.mem(h, tl), FbProof.FbPrf.word_eq_refl(h))

# Transport the no-feedback condition along an equality of feedbacks.
def LBS.nofb_eq(+pre: +List<Tree.Child>, +f1: +List<Feedback.Color>,
    +f2: +List<Feedback.Color>, +e: {f1 == f2 : +List<Feedback.Color>},
    p: LBS.NoFB(pre, f1)) -> LBS.NoFB(pre, f2):
  match pre:
    case Nil{}:
      Unit{}
    case Con{c, rest}:
      match c:
        case Tree.Child{f0, t}:
          (nf0, nr) = p
          (Equal.trans(Bool, Feedback.feedback_eq(f0, f2), Feedback.feedback_eq(f0, f1),
             False{}, Equal.cong(+List<Feedback.Color>, Bool,
               y => Feedback.feedback_eq(f0, y), f2, f1, Equal.sym(+List<Feedback.Color>,
                 f1, f2, e)), nf0),
           LBS.nofb_eq(rest, f1, f2, e, nr))

# A non-empty class's tree is the child at its own position.
def LBS.cls_lookup(+g: +List<Nat>, +pre: +List<Tree.Child>,
    +f: +List<Feedback.Color>, +t: Tree.Tree, +rest: +List<Tree.Child>,
    +S: +List<+List<Nat>>, +h: +List<Nat>, +tl: +List<+List<Nat>>,
    +eq : {Part.LB.keepw_b(g, f, LBS.remFold(g, pre, S)) == h <> tl
           : +List<+List<Nat>>},
    +nw : {Feedback.word_eq(g, h) == False{} : Bool},
    +nf : {Feedback.feedback_eq(f, Feedback.feedback(g, h)) == True{} : Bool}) ->
  {Tree.lookup(f, List.append(&2, Tree.Child, pre, Tree.Child{f, t} <> rest))
   == Some{t} : Maybe<&1, Tree.Tree>}:
  +hmem1 : {LBS.mem(h, Part.LB.keepw_b(g, f, LBS.remFold(g, pre, S))) == True{} : Bool} =
    Equal.trans(Bool, LBS.mem(h, Part.LB.keepw_b(g, f, LBS.remFold(g, pre, S))),
      LBS.mem(h, h <> tl), True{},
      Equal.cong(+List<+List<Nat>>, Bool, y => LBS.mem(h, y),
        Part.LB.keepw_b(g, f, LBS.remFold(g, pre, S)), h <> tl, eq),
      LBS.mem_head(h, tl))
  +hmem : {LBS.mem(h, LBS.remFold(g, pre, S)) == True{} : Bool} =
    LBS.mem_keepw_mem(g, f, h, LBS.remFold(g, pre, S), hmem1)
  +efh : {Feedback.feedback(g, h) == f : +List<Feedback.Color>} =
    Equal.sym(+List<Feedback.Color>, f, Feedback.feedback(g, h),
      FbProof.FbPrf.feedback_eq_true(f, Feedback.feedback(g, h), nf))
  nofb : LBS.NoFB(pre, f) =
    LBS.nofb_eq(pre, Feedback.feedback(g, h), f, efh,
      LBS.remFold_nofb(g, pre, S, h, nw, hmem))
  +lk1 : {Tree.lookup(f, List.append(&2, Tree.Child, pre, Tree.Child{f, t} <> rest))
          == Tree.lookup(f, Tree.Child{f, t} <> rest) : Maybe<&1, Tree.Tree>} =
    LBS.lookup_skip_pre(f, pre, Tree.Child{f, t} <> rest, nofb)
  Equal.trans(Maybe<&1, Tree.Tree>,
    Tree.lookup(f, List.append(&2, Tree.Child, pre, Tree.Child{f, t} <> rest)),
    Tree.lookup(f, Tree.Child{f, t} <> rest), Some{t}, lk1,
    LBS.lookup_head(f, t, rest))

# The head facts of a class.
def LBS.kf_nw(+g: +List<Nat>, +f: +List<Feedback.Color>, +h: +List<Nat>,
    +tl: +List<+List<Nat>>, kf: Decomp.LB.KeepFacts(g, f, h <> tl)) ->
  {Feedback.word_eq(g, h) == False{} : Bool}:
  (nw, rest) = kf
  (nf, krest) = rest
  nw

def LBS.kf_nf(+g: +List<Nat>, +f: +List<Feedback.Color>, +h: +List<Nat>,
    +tl: +List<+List<Nat>>, kf: Decomp.LB.KeepFacts(g, f, h <> tl)) ->
  {Feedback.feedback_eq(f, Feedback.feedback(g, h)) == True{} : Bool}:
  (nw, rest) = kf
  (nf, krest) = rest
  nf

def LBS.kf_tail(+g: +List<Nat>, +f: +List<Feedback.Color>, +h: +List<Nat>,
    +tl: +List<+List<Nat>>, kf: Decomp.LB.KeepFacts(g, f, h <> tl)) ->
  Decomp.LB.KeepFacts(g, f, tl):
  (nw, rest) = kf
  (nf, krest) = rest
  krest

# One candidate's cost at a node is its depth in the looked-up child.
def LBS.kid_cost_false(+g: +List<Nat>, +kids0: +List<Tree.Child>, +h: +List<Nat>,
    b: Bool, +eb: {b == Feedback.word_eq(g, h) : Bool},
    hb: {b == False{} : Bool}) ->
  {NodeCost.NodeCost.kid_cost(g, kids0, h)
   == NodeCost.NodeCost.maybe_depth(
        Tree.lookup(Feedback.feedback(g, h), kids0), h) : Nat}:
  match b:
    case True{}:
      Empty.absurd({NodeCost.NodeCost.kid_cost(g, kids0, h)
                    == NodeCost.NodeCost.maybe_depth(
                         Tree.lookup(Feedback.feedback(g, h), kids0), h) : Nat},
        Logic.Proof.true_ne_false(hb))
    case False{}:
      +e1 : {NodeCost.NodeCost.kid_cost(g, kids0, h)
             == Feedback.Bool.case(Nat, Feedback.word_eq(g, h), 0n,
                  NodeCost.NodeCost.maybe_depth(
                    Tree.lookup(Feedback.feedback(g, h), kids0), h)) : Nat} =
        {==}
      +e2 : {Feedback.Bool.case(Nat, Feedback.word_eq(g, h), 0n,
                  NodeCost.NodeCost.maybe_depth(
                    Tree.lookup(Feedback.feedback(g, h), kids0), h))
             == Feedback.Bool.case(Nat, False{}, 0n,
                  NodeCost.NodeCost.maybe_depth(
                    Tree.lookup(Feedback.feedback(g, h), kids0), h)) : Nat} =
        Equal.cong(Bool, Nat,
          y => Feedback.Bool.case(Nat, y, 0n,
            NodeCost.NodeCost.maybe_depth(
              Tree.lookup(Feedback.feedback(g, h), kids0), h)),
          Feedback.word_eq(g, h), False{},
          Equal.trans(Bool, Feedback.word_eq(g, h), b, False{},
            Equal.sym(Bool, b, Feedback.word_eq(g, h), eb), hb))
      Equal.trans(Nat, NodeCost.NodeCost.kid_cost(g, kids0, h),
        Feedback.Bool.case(Nat, Feedback.word_eq(g, h), 0n,
          NodeCost.NodeCost.maybe_depth(
            Tree.lookup(Feedback.feedback(g, h), kids0), h)),
        NodeCost.NodeCost.maybe_depth(
          Tree.lookup(Feedback.feedback(g, h), kids0), h),
        e1, Equal.trans(Nat,
          Feedback.Bool.case(Nat, Feedback.word_eq(g, h), 0n,
            NodeCost.NodeCost.maybe_depth(
              Tree.lookup(Feedback.feedback(g, h), kids0), h)),
          Feedback.Bool.case(Nat, False{}, 0n,
            NodeCost.NodeCost.maybe_depth(
              Tree.lookup(Feedback.feedback(g, h), kids0), h)),
          NodeCost.NodeCost.maybe_depth(
            Tree.lookup(Feedback.feedback(g, h), kids0), h), e2, {==}))

def LBS.kid_cost_at(+g: +List<Nat>, +kids0: +List<Tree.Child>, +h: +List<Nat>,
    +t: Tree.Tree, +f: +List<Feedback.Color>,
    +nw: {Feedback.word_eq(g, h) == False{} : Bool},
    +nf: {Feedback.feedback_eq(f, Feedback.feedback(g, h)) == True{} : Bool},
    +lk: {Tree.lookup(f, kids0) == Some{t} : Maybe<&1, Tree.Tree>}) ->
  {NodeCost.NodeCost.kid_cost(g, kids0, h)
   == Maybe.default(&1, Nat, Tree.depth(t, h), 0n) : Nat}:
  +e1 : {NodeCost.NodeCost.kid_cost(g, kids0, h)
         == NodeCost.NodeCost.maybe_depth(
              Tree.lookup(Feedback.feedback(g, h), kids0), h) : Nat} =
    LBS.kid_cost_false(g, kids0, h, Feedback.word_eq(g, h), {==}, nw)
  +efh : {Feedback.feedback(g, h) == f : +List<Feedback.Color>} =
    Equal.sym(+List<Feedback.Color>, f, Feedback.feedback(g, h),
      FbProof.FbPrf.feedback_eq_true(f, Feedback.feedback(g, h), nf))
  Equal.trans(Nat, NodeCost.NodeCost.kid_cost(g, kids0, h),
    NodeCost.NodeCost.maybe_depth(Tree.lookup(Feedback.feedback(g, h), kids0), h),
    Maybe.default(&1, Nat, Tree.depth(t, h), 0n), e1,
    Equal.trans(Nat,
      NodeCost.NodeCost.maybe_depth(Tree.lookup(Feedback.feedback(g, h), kids0), h),
      NodeCost.NodeCost.maybe_depth(Tree.lookup(f, kids0), h),
      Maybe.default(&1, Nat, Tree.depth(t, h), 0n),
      Equal.cong(+List<Feedback.Color>, Nat,
        y => NodeCost.NodeCost.maybe_depth(Tree.lookup(y, kids0), h),
        Feedback.feedback(g, h), f, efh),
      Equal.trans(Nat, NodeCost.NodeCost.maybe_depth(Tree.lookup(f, kids0), h),
        NodeCost.NodeCost.maybe_depth(Some{t}, h),
        Maybe.default(&1, Nat, Tree.depth(t, h), 0n),
        Equal.cong(Maybe<&1, Tree.Tree>, Nat,
          y => NodeCost.NodeCost.maybe_depth(y, h), Tree.lookup(f, kids0), Some{t}, lk),
        {==})))

# The whole class costs what the child costs on it.
def LBS.cls_cost(+g: +List<Nat>, +kids0: +List<Tree.Child>,
    +f: +List<Feedback.Color>, +t: Tree.Tree, +ws: +List<+List<Nat>>,
    +lk: {Tree.lookup(f, kids0) == Some{t} : Maybe<&1, Tree.Tree>},
    kf: Decomp.LB.KeepFacts(g, f, ws)) ->
  {NodeCost.NodeCost.kid_sum(g, kids0, ws) == Tree.cost(t, ws) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, tl}:
      (nw, rest) = kf
      (nf, krest) = rest
      +ih : {NodeCost.NodeCost.kid_sum(g, kids0, tl) == Tree.cost(t, tl) : Nat} =
        LBS.cls_cost(g, kids0, f, t, tl, lk, krest)
      +eh : {NodeCost.NodeCost.kid_cost(g, kids0, h)
             == Maybe.default(&1, Nat, Tree.depth(t, h), 0n) : Nat} =
        LBS.kid_cost_at(g, kids0, h, t, f, nw, nf, lk)
      Equal.trans(Nat, NodeCost.NodeCost.kid_sum(g, kids0, h <> tl),
        Nat.add(Maybe.default(&1, Nat, Tree.depth(t, h), 0n),
                NodeCost.NodeCost.kid_sum(g, kids0, tl)),
        Tree.cost(t, h <> tl),
        Equal.cong(Nat, Nat,
          y => Nat.add(y, NodeCost.NodeCost.kid_sum(g, kids0, tl)),
          NodeCost.NodeCost.kid_cost(g, kids0, h),
          Maybe.default(&1, Nat, Tree.depth(t, h), 0n), eh),
        Equal.trans(Nat,
          Nat.add(Maybe.default(&1, Nat, Tree.depth(t, h), 0n),
                  NodeCost.NodeCost.kid_sum(g, kids0, tl)),
          Nat.add(Maybe.default(&1, Nat, Tree.depth(t, h), 0n), Tree.cost(t, tl)),
          Tree.cost(t, h <> tl),
          Equal.cong(Nat, Nat,
            y => Nat.add(Maybe.default(&1, Nat, Tree.depth(t, h), 0n), y),
            NodeCost.NodeCost.kid_sum(g, kids0, tl), Tree.cost(t, tl), ih),
          {==}))

# A class word's depth in the class's child exists.
def LBS.cls_ad_go(+g: +List<Nat>, +kids0: +List<Tree.Child>,
    +f: +List<Feedback.Color>, +t: Tree.Tree, +h: +List<Nat>,
    +tl: +List<+List<Nat>>,
    sh: {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids0}, h)) == True{} : Bool},
    +nw: {Feedback.word_eq(g, h) == False{} : Bool},
    +nf: {Feedback.feedback_eq(f, Feedback.feedback(g, h)) == True{} : Bool},
    +lk: {Tree.lookup(f, kids0) == Some{t} : Maybe<&1, Tree.Tree>},
    ih: Tree.AllHaveDepth(t, tl)) ->
  Tree.AllHaveDepth(t, h <> tl):
  +ed : {Tree.depth(Tree.Node{g, kids0}, h)
         == Tree.depth.bump(Tree.depth.go(kids0, Feedback.feedback(g, h), h))
         : Maybe<Nat>} =
    LBS.node_depth_false(g, kids0, h, nw)
  +s1 : {Maybe.is_some(&1, Nat,
           Tree.depth.bump(Tree.depth.go(kids0, Feedback.feedback(g, h), h)))
         == True{} : Bool} =
    Equal.trans(Bool, Maybe.is_some(&1, Nat,
        Tree.depth.bump(Tree.depth.go(kids0, Feedback.feedback(g, h), h))),
      Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids0}, h)), True{},
      Equal.cong(Maybe<Nat>, Bool, m2 => Maybe.is_some(&1, Nat, m2),
        Tree.depth.bump(Tree.depth.go(kids0, Feedback.feedback(g, h), h)),
        Tree.depth(Tree.Node{g, kids0}, h), Equal.sym(Maybe<Nat>,
          Tree.depth(Tree.Node{g, kids0}, h),
          Tree.depth.bump(Tree.depth.go(kids0, Feedback.feedback(g, h), h)), ed)),
      sh)
  +s2 : {Maybe.is_some(&1, Nat, Tree.depth.go(kids0, Feedback.feedback(g, h), h))
         == True{} : Bool} =
    Equal.trans(Bool,
      Maybe.is_some(&1, Nat, Tree.depth.go(kids0, Feedback.feedback(g, h), h)),
      Maybe.is_some(&1, Nat,
        Tree.depth.bump(Tree.depth.go(kids0, Feedback.feedback(g, h), h))),
      True{},
      Equal.sym(Bool,
        Maybe.is_some(&1, Nat,
          Tree.depth.bump(Tree.depth.go(kids0, Feedback.feedback(g, h), h))),
        Maybe.is_some(&1, Nat, Tree.depth.go(kids0, Feedback.feedback(g, h), h)),
        NodeCost.NodeCost.is_some_bump(
          Tree.depth.go(kids0, Feedback.feedback(g, h), h))),
      s1)
  +s3 : {Maybe.is_some(&1, Nat,
           DepthProof.DepthProof.lookup_depth(
             Tree.lookup(Feedback.feedback(g, h), kids0), h)) == True{} : Bool} =
    Equal.trans(Bool,
      Maybe.is_some(&1, Nat,
        DepthProof.DepthProof.lookup_depth(
          Tree.lookup(Feedback.feedback(g, h), kids0), h)),
      Maybe.is_some(&1, Nat, Tree.depth.go(kids0, Feedback.feedback(g, h), h)),
      True{},
      Equal.cong(Maybe<Nat>, Bool, m2 => Maybe.is_some(&1, Nat, m2),
        DepthProof.DepthProof.lookup_depth(
          Tree.lookup(Feedback.feedback(g, h), kids0), h),
        Tree.depth.go(kids0, Feedback.feedback(g, h), h),
        Equal.sym(Maybe<Nat>, Tree.depth.go(kids0, Feedback.feedback(g, h), h),
          DepthProof.DepthProof.lookup_depth(
            Tree.lookup(Feedback.feedback(g, h), kids0), h),
          DepthProof.DepthProof.depth_go_lookup(kids0, Feedback.feedback(g, h), h))),
      s2)
  +efh : {Feedback.feedback(g, h) == f : +List<Feedback.Color>} =
    Equal.sym(+List<Feedback.Color>, f, Feedback.feedback(g, h),
      FbProof.FbPrf.feedback_eq_true(f, Feedback.feedback(g, h), nf))
  +s4 : {Maybe.is_some(&1, Nat,
           DepthProof.DepthProof.lookup_depth(Tree.lookup(f, kids0), h))
         == True{} : Bool} =
    Equal.trans(Bool,
      Maybe.is_some(&1, Nat,
        DepthProof.DepthProof.lookup_depth(Tree.lookup(f, kids0), h)),
      Maybe.is_some(&1, Nat,
        DepthProof.DepthProof.lookup_depth(
          Tree.lookup(Feedback.feedback(g, h), kids0), h)),
      True{},
      Equal.cong(Maybe<Tree.Tree>, Bool,
        m2 => Maybe.is_some(&1, Nat, DepthProof.DepthProof.lookup_depth(m2, h)),
        Tree.lookup(f, kids0), Tree.lookup(Feedback.feedback(g, h), kids0),
        Equal.cong(+List<Feedback.Color>, Maybe<&1, Tree.Tree>,
          y => Tree.lookup(y, kids0), f, Feedback.feedback(g, h),
          Equal.sym(+List<Feedback.Color>, Feedback.feedback(g, h), f, efh))),
      s3)
  +s5 : {Maybe.is_some(&1, Nat,
           DepthProof.DepthProof.lookup_depth(Some{t}, h)) == True{} : Bool} =
    Equal.trans(Bool,
      Maybe.is_some(&1, Nat, DepthProof.DepthProof.lookup_depth(Some{t}, h)),
      Maybe.is_some(&1, Nat,
        DepthProof.DepthProof.lookup_depth(Tree.lookup(f, kids0), h)),
      True{},
      Equal.cong(Maybe<&1, Tree.Tree>, Bool,
        m2 => Maybe.is_some(&1, Nat, DepthProof.DepthProof.lookup_depth(m2, h)),
        Some{t}, Tree.lookup(f, kids0), Equal.sym(Maybe<&1, Tree.Tree>,
          Tree.lookup(f, kids0), Some{t}, lk)),
      s4)
  +s6 : {Maybe.is_some(&1, Nat, DepthProof.DepthProof.step(t, h)) == True{} : Bool} =
    s5
  +s7 : {Maybe.is_some(&1, Nat, Tree.depth(t, h)) == True{} : Bool} =
    Equal.trans(Bool, Maybe.is_some(&1, Nat, Tree.depth(t, h)),
      Maybe.is_some(&1, Nat, DepthProof.DepthProof.step(t, h)), True{},
      Equal.sym(Bool, Maybe.is_some(&1, Nat, DepthProof.DepthProof.step(t, h)),
        Maybe.is_some(&1, Nat, Tree.depth(t, h)),
        Equal.cong(Maybe<Nat>, Bool, m2 => Maybe.is_some(&1, Nat, m2),
          DepthProof.DepthProof.step(t, h), Tree.depth(t, h),
          NodeCost.NodeCost.step_is_depth(t, h))),
      s6)
  (s7, ih)

def LBS.cls_ad(+g: +List<Nat>, +kids0: +List<Tree.Child>,
    +f: +List<Feedback.Color>, +t: Tree.Tree, +ws: +List<+List<Nat>>,
    +lk: {Tree.lookup(f, kids0) == Some{t} : Maybe<&1, Tree.Tree>},
    kf: Decomp.LB.KeepFacts(g, f, ws),
    ad: Tree.AllHaveDepth(Tree.Node{g, kids0}, ws)) ->
  Tree.AllHaveDepth(t, ws):
  match ws:
    case Nil{}:
      Unit{}
    case Con{h, tl}:
      (nw, rest) = kf
      (nf, krest) = rest
      (sh, st) = ad
      LBS.cls_ad_go(g, kids0, f, t, h, tl, sh, nw, nf, lk,
        LBS.cls_ad(g, kids0, f, t, tl, lk, krest, st))
