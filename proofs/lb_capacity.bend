# Lower bounds for valid trees, part 3: the capacity bound function.
#
# A tree whose nodes have at most `k` children can hold only so many candidates
# at each depth: the root guess ends at most one candidate, one class can end a
# candidate at depth two, and every deeper node has at most `k` children. Level
# `j` of such a tree therefore holds at most `G_j = 1 + k + ... + k^(j-1)`
# candidates, and counting the candidates each level cannot hold gives
#
#   capbound(n, k) = n + sum over j = 1 .. n of (n - G_j)+
#
# where `x+` is `Nat.sub`. This module defines `G`, the truncated sum and
# `capbound`, and proves the facts a pruning rule needs about the bound itself:
# it is monotone in the candidate count, and it is at least `2n - 1`, so it
# dominates the depth bound of `lb_twice.bend`. The capacity sequence grows by
# at least one per level (`G j >= j`), which is why summing the first `n` levels
# is enough.
#
# The soundness statement, `cost(T, S) >= capbound(|S|, k)` for a valid tree
# with no duplicate candidates whose nodes have at most `k` children, needs the
# feedback classes of every node and the candidate count each level of the tree
# can hold. It is recorded as an open goal in `docs/proofs.md`.
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./classbound_nat.bend as CB

# Monotonicity of subtraction in the number it subtracts from.
def LB.sub_le_l(a: Nat, a2: Nat, c: Nat,
    e: {Nat.is_le(a, a2) == True{} : Bool}) ->
  {Nat.is_le(Nat.sub(a, c), Nat.sub(a2, c)) == True{} : Bool}:
  match a a2:
    case 0n _:
      NatProof.Nat.is_le_zero_l(Nat.sub(a2, c))
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(Nat.sub(1n+ap, c), Nat.sub(0n, c)) == True{} : Bool},
                   Logic.Proof.false_ne_true(e))
    case 1n+ap 1n+a2p:
      match c:
        case 0n:
          e
        case 1n+cp:
          LB.sub_le_l(ap, a2p, cp, e)

# The number of candidates the first `j` levels of a `k`-branching tree can
# hold: `1 + k + ... + k^(j-1)`.
def LB.G(+k: Nat, j: Nat) -> Nat:
  match j:
    case 0n:
      0n
    case 1n+p:
      Nat.add(1n, Nat.mul(k, LB.G(k, p)))

# `G` grows by at least one per level, so `G j >= j`.
def LB.G_ge(+k: Nat, j: Nat,
    k1: {Nat.is_le(1n, k) == True{} : Bool}) ->
  {Nat.is_le(j, LB.G(k, j)) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({Nat.is_le(j, LB.G(0n, j)) == True{} : Bool},
                   Logic.Proof.false_ne_true(k1))
    case 1n+ck:
      match j:
        case 0n:
          NatProof.Nat.is_le_refl(0n)
        case 1n++p:
          +ihp : {Nat.is_le(p, LB.G(1n+ck, p)) == True{} : Bool} =
            LB.G_ge(1n+ck, p, k1)
          +kg : {Nat.is_le(LB.G(1n+ck, p),
                           Nat.mul(1n+ck, LB.G(1n+ck, p))) == True{} : Bool} =
            CB.CB.is_le_add_self_r(LB.G(1n+ck, p), Nat.mul(ck, LB.G(1n+ck, p)))
          +h : {Nat.is_le(p, Nat.mul(1n+ck, LB.G(1n+ck, p))) == True{} : Bool} =
            NatProof.Nat.is_le_trans(p, LB.G(1n+ck, p),
              Nat.mul(1n+ck, LB.G(1n+ck, p)), ihp, kg)
          NatProof.Nat.is_le_succ(p, Nat.mul(1n+ck, LB.G(1n+ck, p)), h)

# The truncated sum of `n - G_j` over the levels `j, j+1, ... j+fuel-1`.
def LB.capSum(+n: Nat, +k: Nat, +fuel: Nat, +j: Nat) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+pf:
      Nat.add(Nat.sub(n, LB.G(k, j)),
              LB.capSum(n, k, pf, Nat.add(1n, j)))

# The capacity bound: `n` plus the candidates that no level can hold.
def LB.capbound(+n: Nat, +k: Nat) -> Nat:
  Nat.add(n, LB.capSum(n, k, n, 1n))

# Raising the candidate count raises every term of the sum.
def LB.capSum_mono(+n: Nat, +n2: Nat, +k: Nat, +fuel: Nat, +j: Nat,
    +le: {Nat.is_le(n, n2) == True{} : Bool}) ->
  {Nat.is_le(LB.capSum(n, k, fuel, j), LB.capSum(n2, k, fuel, j)) == True{} : Bool}:
  match fuel:
    case 0n:
      NatProof.Nat.is_le_refl(0n)
    case 1n+pf:
      +h1 : {Nat.is_le(Nat.sub(n, LB.G(k, j)), Nat.sub(n2, LB.G(k, j))) == True{} : Bool} =
        LB.sub_le_l(n, n2, LB.G(k, j), le)
      +h2 : {Nat.is_le(LB.capSum(n, k, pf, Nat.add(1n, j)),
                       LB.capSum(n2, k, pf, Nat.add(1n, j))) == True{} : Bool} =
        LB.capSum_mono(n, n2, k, pf, Nat.add(1n, j), le)
      CB.CB.is_le_add(Nat.sub(n, LB.G(k, j)), Nat.sub(n2, LB.G(k, j)),
        LB.capSum(n, k, pf, Nat.add(1n, j)), LB.capSum(n2, k, pf, Nat.add(1n, j)),
        h1, h2)

# More levels add nonnegative terms, so they only raise the sum.
def LB.capSum_le_fuel(+n: Nat, +k: Nat, +fuel: Nat, +j: Nat) ->
  {Nat.is_le(LB.capSum(n, k, fuel, j),
             LB.capSum(n, k, Nat.add(1n, fuel), j)) == True{} : Bool}:
  match fuel:
    case 0n:
      NatProof.Nat.is_le_zero_l(
        LB.capSum(n, k, Nat.add(1n, 0n), j))
    case 1n+pf:
      +ih : {Nat.is_le(LB.capSum(n, k, pf, Nat.add(1n, j)),
                       LB.capSum(n, k, Nat.add(1n, pf), Nat.add(1n, j))) == True{} : Bool} =
        LB.capSum_le_fuel(n, k, pf, Nat.add(1n, j))
      CB.CB.is_le_add(Nat.sub(n, LB.G(k, j)), Nat.sub(n, LB.G(k, j)),
        LB.capSum(n, k, pf, Nat.add(1n, j)),
        LB.capSum(n, k, Nat.add(1n, pf), Nat.add(1n, j)),
        NatProof.Nat.is_le_refl(Nat.sub(n, LB.G(k, j))), ih)

# Monotonicity of the bound in the candidate count.
def LB.capbound_mono(+n: Nat, +k: Nat) ->
  {Nat.is_le(LB.capbound(n, k), LB.capbound(Nat.add(1n, n), k)) == True{} : Bool}:
  +h1 : {Nat.is_le(Nat.add(n, LB.capSum(n, k, n, 1n)),
                   Nat.add(Nat.add(1n, n), LB.capSum(n, k, n, 1n))) == True{} : Bool} =
    CB.CB.is_le_add(n, Nat.add(1n, n), LB.capSum(n, k, n, 1n),
      LB.capSum(n, k, n, 1n),
      NatProof.Nat.is_le_of_lt(n, Nat.add(1n, n), NatProof.Nat.is_lt_succ_self(n)),
      NatProof.Nat.is_le_refl(LB.capSum(n, k, n, 1n)))
  +h2 : {Nat.is_le(Nat.add(Nat.add(1n, n), LB.capSum(n, k, n, 1n)),
                   Nat.add(Nat.add(1n, n), LB.capSum(Nat.add(1n, n), k, n, 1n))) == True{} : Bool} =
    NatProof.Nat.is_le_add_l(LB.capSum(n, k, n, 1n),
      LB.capSum(Nat.add(1n, n), k, n, 1n), Nat.add(1n, n),
      LB.capSum_mono(n, Nat.add(1n, n), k, n, 1n,
        NatProof.Nat.is_le_of_lt(n, Nat.add(1n, n), NatProof.Nat.is_lt_succ_self(n))))
  +h3 : {Nat.is_le(Nat.add(Nat.add(1n, n), LB.capSum(Nat.add(1n, n), k, n, 1n)),
                   Nat.add(Nat.add(1n, n),
                     LB.capSum(Nat.add(1n, n), k, Nat.add(1n, n), 1n))) == True{} : Bool} =
    NatProof.Nat.is_le_add_l(LB.capSum(Nat.add(1n, n), k, n, 1n),
      LB.capSum(Nat.add(1n, n), k, Nat.add(1n, n), 1n), Nat.add(1n, n),
      LB.capSum_le_fuel(Nat.add(1n, n), k, n, 1n))
  NatProof.Nat.is_le_trans(Nat.add(n, LB.capSum(n, k, n, 1n)),
    Nat.add(Nat.add(1n, n), LB.capSum(n, k, n, 1n)),
    Nat.add(Nat.add(1n, n), LB.capSum(Nat.add(1n, n), k, Nat.add(1n, n), 1n)),
    h1,
    NatProof.Nat.is_le_trans(Nat.add(Nat.add(1n, n), LB.capSum(n, k, n, 1n)),
      Nat.add(Nat.add(1n, n), LB.capSum(Nat.add(1n, n), k, n, 1n)),
      Nat.add(Nat.add(1n, n), LB.capSum(Nat.add(1n, n), k, Nat.add(1n, n), 1n)),
      h2, h3))

# The sum of the levels starts with `n - 1`.
def LB.capSum_first(+n: Nat, +k: Nat, nn: {Nat.is_le(1n, n) == True{} : Bool}) ->
  {Nat.is_le(Nat.sub(n, 1n), LB.capSum(n, k, n, 1n)) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(Nat.sub(0n, 1n), LB.capSum(0n, k, 0n, 1n)) == True{} : Bool},
                   Logic.Proof.false_ne_true(nn))
    case 1n+p:
      +rest : {Nat.is_le(0n, LB.capSum(1n+p, k, p, Nat.add(1n, 1n))) == True{} : Bool} =
        NatProof.Nat.is_le_zero_l(LB.capSum(1n+p, k, p, Nat.add(1n, 1n)))
      +eqz : {Nat.sub(p, Nat.mul(k, 0n)) == Nat.sub(p, 0n) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.sub(p, x), Nat.mul(k, 0n), 0n, CB.CB.mul_zero(k))
      +head : {Nat.is_le(Nat.sub(1n+p, 1n), Nat.sub(1n+p, LB.G(k, 1n))) == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(Nat.sub(p, 0n), Nat.sub(p, 0n), Nat.sub(p, Nat.mul(k, 0n)),
          Equal.sym(Nat, Nat.sub(p, Nat.mul(k, 0n)), Nat.sub(p, 0n), eqz),
          NatProof.Nat.is_le_refl(Nat.sub(p, 0n)))
      +sum : {Nat.is_le(Nat.add(Nat.sub(1n+p, 1n), 0n),
                       Nat.add(Nat.sub(1n+p, LB.G(k, 1n)),
                               LB.capSum(1n+p, k, p, Nat.add(1n, 1n)))) == True{} : Bool} =
        CB.CB.is_le_add(Nat.sub(1n+p, 1n), Nat.sub(1n+p, LB.G(k, 1n)),
          0n, LB.capSum(1n+p, k, p, Nat.add(1n, 1n)), head, rest)
      +ez : {Nat.add(Nat.sub(1n+p, 1n), 0n) == Nat.sub(1n+p, 1n) : Nat} =
        NatProof.NatPrf.add_zero(Nat.sub(1n+p, 1n))
      NatProof.Nat.is_le_eq_l(
        Nat.add(Nat.sub(1n+p, LB.G(k, 1n)), LB.capSum(1n+p, k, p, Nat.add(1n, 1n))),
        Nat.add(Nat.sub(1n+p, 1n), 0n), Nat.sub(1n+p, 1n), ez, sum)

# The capacity bound is at least the depth bound `2n - 1` of `lb_twice.bend`,
# stated as `n + (n - 1) <= capbound(n, k)`.
def LB.capbound_ge_depth(+n: Nat, +k: Nat,
    nn: {Nat.is_le(1n, n) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(n, Nat.sub(n, 1n)), LB.capbound(n, k)) == True{} : Bool}:
  +first : {Nat.is_le(Nat.sub(n, 1n), LB.capSum(n, k, n, 1n)) == True{} : Bool} =
    LB.capSum_first(n, k, nn)
  NatProof.Nat.is_le_add_l(Nat.sub(n, 1n), LB.capSum(n, k, n, 1n), n, first)
