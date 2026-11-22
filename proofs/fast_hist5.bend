# Correctness of the flat 1024-entry 5-letter histogram and bucketing path
# (`SolveFast.hist5_go`, `SolveFast.fill5_go`, `SolveFast.drain5_go`, and
# `SolveFast.guess_items_buf`).
#
# Proves unconditionally for every input `(nodup, g, S, best)` and every valid
# reusable node buffer `buf` (`FH.BufOk(buf)`):
# 1. `FH.gres_items(guess_items_buf(nodup, g, S, |S|, best, buf))
#     == SolveFast.guess_items(nodup, g, S, |S|, best)`
# 2. `FH.BufOk(FH.gres_buf(guess_items_buf(nodup, g, S, |S|, best, buf)))`
#
# Structure:
# - Pure `FGroup` algebraic identities: `fgroups_lb_nodup(fg, n) == n + 2*m - k`
#   and `fgroups_smaller(n, fg) == (m < n) || (2 <= k)` for `n >= 1`, plus exact
#   evolution of `total`, `count`, `has_code`, `lookup_code`, and reversed class
#   code lists under `fgroup_add_fast`.
# - Symbolic depth-indexed `Data` tree predicates `FH.SeenTree` and `FH.BktTree`
#   avoiding any 1024-way unrolling while remaining freely copyable (`Data`).
# - Exact single-pass specifications for `hist5_go`, `fill5_go`, and `drain5_go`.
import Base
import ../src/feedback.bend as Feedback
import ../src/groups.bend as Groups
import ../src/solve_ref.bend as SolveRef
import ../src/solve_fast.bend as SolveFast
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./fast_groups.bend as FG
import ./array.bend as Arr
import ./fast_fb5.bend as FF5

# ---------------------------------------------------------------------------
# Small Nat and Bool helpers
# ---------------------------------------------------------------------------

def FH.bool_and_intro(a: Bool, b: Bool,
    +ea: {a == True{} : Bool}, +eb: {b == True{} : Bool}) ->
  {Bool.and(a, b) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(a, b), Bool.and(True{}, b), True{},
    Equal.cong(Bool, Bool, x => Bool.and(x, b), a, True{}, ea), eb)

def FH.nat_sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def FH.nat_sub_add_cancel(+x: Nat, +k: Nat) ->
  {Nat.sub(Nat.add(x, k), k) == x : Nat}:
  match k:
    case 0n:
      Equal.trans(Nat, Nat.sub(Nat.add(x, 0n), 0n), Nat.sub(x, 0n), x,
        Equal.cong(Nat, Nat, y => Nat.sub(y, 0n), Nat.add(x, 0n), x,
          NatProof.NatPrf.add_zero(x)),
        FH.nat_sub_zero(x))
    case 1n++kp:
      Equal.trans(Nat,
        Nat.sub(Nat.add(x, 1n+kp), 1n+kp),
        Nat.sub(Nat.add(1n, Nat.add(x, kp)), 1n+kp),
        x,
        Equal.cong(Nat, Nat, y => Nat.sub(y, 1n+kp),
          Nat.add(x, 1n+kp), Nat.add(1n, Nat.add(x, kp)),
          NatProof.NatPrf.add_succ(x, kp)),
        FH.nat_sub_add_cancel(x, kp))

def FH.nat_add_comm_r(+a: Nat, +b: Nat, +c: Nat) ->
  {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}:
  Equal.trans(Nat,
    Nat.add(Nat.add(a, b), c),
    Nat.add(a, Nat.add(b, c)),
    Nat.add(Nat.add(a, c), b),
    NatProof.NatPrf.add_assoc(a, b, c),
    Equal.trans(Nat,
      Nat.add(a, Nat.add(b, c)),
      Nat.add(a, Nat.add(c, b)),
      Nat.add(Nat.add(a, c), b),
      Equal.cong(Nat, Nat, x => Nat.add(a, x), Nat.add(b, c), Nat.add(c, b),
        NatProof.NatPrf.add_comm(b, c)),
      Equal.sym(Nat, Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)),
        NatProof.NatPrf.add_assoc(a, c, b))))

def FH.nat_add_2_step(+a: Nat, +b: Nat) ->
  {Nat.add(Nat.add(a, b), Nat.add(a, b))
   == Nat.add(Nat.add(a, a), Nat.add(b, b)) : Nat}:
  Equal.trans(Nat,
    Nat.add(Nat.add(a, b), Nat.add(a, b)),
    Nat.add(Nat.add(Nat.add(a, b), a), b),
    Nat.add(Nat.add(a, a), Nat.add(b, b)),
    Equal.sym(Nat, Nat.add(Nat.add(Nat.add(a, b), a), b),
      Nat.add(Nat.add(a, b), Nat.add(a, b)),
      NatProof.NatPrf.add_assoc(Nat.add(a, b), a, b)),
    Equal.trans(Nat,
      Nat.add(Nat.add(Nat.add(a, b), a), b),
      Nat.add(Nat.add(Nat.add(a, a), b), b),
      Nat.add(Nat.add(a, a), Nat.add(b, b)),
      Equal.cong(Nat, Nat, x => Nat.add(x, b),
        Nat.add(Nat.add(a, b), a), Nat.add(Nat.add(a, a), b),
        FH.nat_add_comm_r(a, b, a)),
      NatProof.NatPrf.add_assoc(Nat.add(a, a), b, b)))

def FH.nat_sub1_plus1(+a: Nat, +h: {Nat.is_le(1n, a) == True{} : Bool}) ->
  {Nat.add(Nat.sub(a, 1n), 1n) == a : Nat}:
  match a:
    case 0n:
      Empty.absurd({1n == 0n : Nat}, Logic.Proof.false_ne_true(h))
    case 1n++p:
      Equal.trans(Nat,
        Nat.add(Nat.sub(p, 0n), 1n),
        Nat.add(p, 1n),
        1n+p,
        Equal.cong(Nat, Nat, x => Nat.add(x, 1n), Nat.sub(p, 0n), p,
          FH.nat_sub_zero(p)),
        Equal.trans(Nat, Nat.add(p, 1n), Nat.add(1n, p), 1n+p,
          NatProof.NatPrf.add_comm(p, 1n), {==}))

def FH.nat_le_add_l(+a: Nat, +b: Nat) ->
  {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      NatProof.Nat.is_le_zero_l(b)
    case 1n++ap:
      FH.nat_le_add_l(ap, b)

def FH.nat_le_add_r(+a: Nat, +b: Nat) ->
  {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  NatProof.Nat.is_le_eq_r(b, Nat.add(b, a), Nat.add(a, b),
    NatProof.NatPrf.add_comm(b, a), FH.nat_le_add_l(b, a))

def FH.nat_le_1_add(+a: Nat, +b: Nat, +ha: {Nat.is_le(1n, a) == True{} : Bool}) ->
  {Nat.is_le(1n, Nat.add(a, b)) == True{} : Bool}:
  NatProof.Nat.is_le_trans(1n, a, Nat.add(a, b), ha, FH.nat_le_add_l(a, b))

def FH.nat_is_lt_add_pos(+a: Nat, +b: Nat,
    +hb: {Nat.is_le(1n, b) == True{} : Bool}) ->
  {Nat.is_lt(a, Nat.add(a, b)) == True{} : Bool}:
  match b:
    case 0n:
      Empty.absurd({Nat.is_lt(a, Nat.add(a, 0n)) == True{} : Bool},
        Logic.Proof.false_ne_true(hb))
    case 1n++bp:
      +hlt : {Nat.is_lt(a, Nat.add(1n, Nat.add(a, bp))) == True{} : Bool} =
        NatProof.Nat.is_lt_succ_of_le(a, Nat.add(a, bp), FH.nat_le_add_l(a, bp))
      Equal.trans(Bool,
        Nat.is_lt(a, Nat.add(a, 1n+bp)),
        Nat.is_lt(a, Nat.add(1n, Nat.add(a, bp))),
        True{},
        Equal.cong(Nat, Bool, x => Nat.is_lt(a, x),
          Nat.add(a, 1n+bp), Nat.add(1n, Nat.add(a, bp)),
          NatProof.NatPrf.add_succ(a, bp)),
        hlt)

def FH.nat_is_lt_of_le_false_go(+a: Nat, +b: Nat, c: Cmp,
    +ec: {c == Nat.cmp(a, b) : Cmp},
    +hle: {Nat.is_le(a, b) == True{} : Bool},
    +hnlt: {Nat.is_lt(a, b) == False{} : Bool}) -> {a == b : Nat}:
  match c:
    case LT{}:
      +et : {Nat.is_lt(a, b) == True{} : Bool} =
        Equal.cong(Cmp, Bool, Cmp.is_lt, Nat.cmp(a, b), LT{},
          Equal.sym(Cmp, LT{}, Nat.cmp(a, b), ec))
      Empty.absurd({a == b : Nat},
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, Nat.is_lt(a, b), False{},
            Equal.sym(Bool, Nat.is_lt(a, b), True{}, et), hnlt)))
    case EQ{}:
      NatProof.NatPrf.is_eq_true(a, b,
        Equal.cong(Cmp, Bool, Cmp.is_eq, Nat.cmp(a, b), EQ{},
          Equal.sym(Cmp, EQ{}, Nat.cmp(a, b), ec)))
    case GT{}:
      +ef : {Nat.is_le(a, b) == False{} : Bool} =
        Equal.cong(Cmp, Bool, Cmp.is_le, Nat.cmp(a, b), GT{},
          Equal.sym(Cmp, GT{}, Nat.cmp(a, b), ec))
      Empty.absurd({a == b : Nat},
        Logic.Proof.false_ne_true(
          Equal.trans(Bool, False{}, Nat.is_le(a, b), True{},
            Equal.sym(Bool, Nat.is_le(a, b), False{}, ef), hle)))

def FH.nat_eq_of_le_and_not_lt(+a: Nat, +b: Nat,
    +hle: {Nat.is_le(a, b) == True{} : Bool},
    +hnlt: {Nat.is_lt(a, b) == False{} : Bool}) -> {a == b : Nat}:
  FH.nat_is_lt_of_le_false_go(a, b, Nat.cmp(a, b), {==}, hle, hnlt)

def FH.nat_is_lt_irrefl(a: Nat) -> {Nat.is_lt(a, a) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      FH.nat_is_lt_irrefl(p)

def FH.nat_is_lt_of_lt_le(+a: Nat, +b: Nat, +c: Nat,
    +hab: {Nat.is_lt(a, b) == True{} : Bool},
    +hbc: {Nat.is_le(b, c) == True{} : Bool}) ->
  {Nat.is_lt(a, c) == True{} : Bool}:
  NatProof.Nat.is_lt_le_trans(a, b, c, hab, hbc)

# ---------------------------------------------------------------------------
# Pure `FGroup` specs and algebraic identities
# ---------------------------------------------------------------------------

def FH.fgroups_total(+fg: +List<SolveFast.FGroup>) -> Nat:
  match fg:
    case Nil{}:
      0n
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{f, len, rws}:
          Nat.add(len, FH.fgroups_total(rest))

def FH.fgroups_count(+fg: +List<SolveFast.FGroup>) -> Nat:
  match fg:
    case Nil{}:
      0n
    case Con{gp, rest}:
      Nat.add(1n, FH.fgroups_count(rest))

def FH.fgroups_pos(+fg: +List<SolveFast.FGroup>) -> Bool:
  match fg:
    case Nil{}:
      True{}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{f, len, rws}:
          Bool.and(Nat.is_le(1n, len), FH.fgroups_pos(rest))

def FH.has_code(+c: U32, +fg: +List<SolveFast.FGroup>) -> Bool:
  match fg:
    case Nil{}:
      False{}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{f, len, rws}:
          Bool.or(U32.is_eq(c, FF5.FF5.encode_fb5_list(f)),
            FH.has_code(c, rest))

def FH.lookup_code(+c: U32, +fg: +List<SolveFast.FGroup>) -> +List<+List<Nat>>:
  match fg:
    case Nil{}:
      Nil{}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{f, len, rws}:
          Feedback.Bool.case(+List<+List<Nat>>,
            U32.is_eq(c, FF5.FF5.encode_fb5_list(f)),
            rws, FH.lookup_code(c, rest))

def FH.fgroups_wf(+fg: +List<SolveFast.FGroup>) -> Bool:
  match fg:
    case Nil{}:
      True{}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{f, len, rws}:
          Bool.and(FF5.FF5.is_fb5(f),
            Bool.and(Nat.is_le(1n, len),
              Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                Bool.and(Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), rest)),
                  FH.fgroups_wf(rest)))))

def FH.fgroups_pos_of_wf(+fg: +List<SolveFast.FGroup>,
    +hw: {FH.fgroups_wf(fg) == True{} : Bool}) ->
  {FH.fgroups_pos(fg) == True{} : Bool}:
  match fg:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          +h1 = Logic.Proof.and_true_r(FF5.FF5.is_fb5(f),
                  Bool.and(Nat.is_le(1n, len),
                    Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                      Bool.and(
                        Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), rest)),
                        FH.fgroups_wf(rest)))), hw)
          +hp = Logic.Proof.and_true_l(Nat.is_le(1n, len),
                  Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                    Bool.and(
                      Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), rest)),
                      FH.fgroups_wf(rest))), h1)
          +h2 = Logic.Proof.and_true_r(Nat.is_le(1n, len),
                  Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                    Bool.and(
                      Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), rest)),
                      FH.fgroups_wf(rest))), h1)
          +h3 = Logic.Proof.and_true_r(Nat.is_eq(len, Groups.len_words(rws)),
                  Bool.and(
                    Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), rest)),
                    FH.fgroups_wf(rest)), h2)
          +hr = Logic.Proof.and_true_r(
                  Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), rest)),
                  FH.fgroups_wf(rest), h3)
          FH.bool_and_intro(Nat.is_le(1n, len), FH.fgroups_pos(rest),
            hp, FH.fgroups_pos_of_wf(rest, hr))

# Theorem 1: `fgroups_lb_nodup(fg, acc) + count(fg) == acc + 2 * total(fg)`.
def FH.fgroups_lb_nodup_sum(+fg: +List<SolveFast.FGroup>, +acc: Nat,
    +hpos: {FH.fgroups_pos(fg) == True{} : Bool}) ->
  {Nat.add(SolveFast.fgroups_lb_nodup(fg, acc), FH.fgroups_count(fg))
   == Nat.add(acc, Nat.add(FH.fgroups_total(fg), FH.fgroups_total(fg))) : Nat}:
  match fg:
    case Nil{}:
      Equal.trans(Nat, Nat.add(acc, 0n), acc, Nat.add(acc, 0n),
        NatProof.NatPrf.add_zero(acc),
        Equal.sym(Nat, Nat.add(acc, 0n), acc, NatProof.NatPrf.add_zero(acc)))
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          +h1 : {Nat.is_le(1n, len) == True{} : Bool} =
            Logic.Proof.and_true_l(Nat.is_le(1n, len),
              FH.fgroups_pos(rest), hpos)
          +hr : {FH.fgroups_pos(rest) == True{} : Bool} =
            Logic.Proof.and_true_r(Nat.is_le(1n, len),
              FH.fgroups_pos(rest), hpos)
          +clb : Nat = Nat.sub(Nat.add(len, len), 1n)
          +lb_r : Nat = SolveFast.fgroups_lb_nodup(rest, Nat.add(acc, clb))
          +mr : Nat = FH.fgroups_total(rest)
          +kr : Nat = FH.fgroups_count(rest)
          +h2l : {Nat.is_le(1n, Nat.add(len, len)) == True{} : Bool} =
            FH.nat_le_1_add(len, len, h1)
          +eclb : {Nat.add(clb, 1n) == Nat.add(len, len) : Nat} =
            FH.nat_sub1_plus1(Nat.add(len, len), h2l)
          +ih : {Nat.add(lb_r, kr) == Nat.add(Nat.add(acc, clb), Nat.add(mr, mr))
                 : Nat} =
            FH.fgroups_lb_nodup_sum(rest, Nat.add(acc, clb), hr)
          +e1 : {Nat.add(lb_r, Nat.add(1n, kr))
                 == Nat.add(Nat.add(lb_r, kr), 1n) : Nat} =
            Equal.trans(Nat,
              Nat.add(lb_r, Nat.add(1n, kr)),
              Nat.add(lb_r, Nat.add(kr, 1n)),
              Nat.add(Nat.add(lb_r, kr), 1n),
              Equal.cong(Nat, Nat, x => Nat.add(lb_r, x),
                Nat.add(1n, kr), Nat.add(kr, 1n),
                NatProof.NatPrf.add_comm(1n, kr)),
              Equal.sym(Nat, Nat.add(Nat.add(lb_r, kr), 1n),
                Nat.add(lb_r, Nat.add(kr, 1n)),
                NatProof.NatPrf.add_assoc(lb_r, kr, 1n)))
          +e2 : {Nat.add(Nat.add(lb_r, kr), 1n)
                 == Nat.add(Nat.add(Nat.add(acc, clb), Nat.add(mr, mr)), 1n)
                 : Nat} =
            Equal.cong(Nat, Nat, x => Nat.add(x, 1n),
              Nat.add(lb_r, kr), Nat.add(Nat.add(acc, clb), Nat.add(mr, mr)),
              ih)
          +e3 : {Nat.add(Nat.add(Nat.add(acc, clb), Nat.add(mr, mr)), 1n)
                 == Nat.add(Nat.add(Nat.add(acc, clb), 1n), Nat.add(mr, mr))
                 : Nat} =
            FH.nat_add_comm_r(Nat.add(acc, clb), Nat.add(mr, mr), 1n)
          +e4 : {Nat.add(Nat.add(acc, clb), 1n)
                 == Nat.add(acc, Nat.add(len, len)) : Nat} =
            Equal.trans(Nat,
              Nat.add(Nat.add(acc, clb), 1n),
              Nat.add(acc, Nat.add(clb, 1n)),
              Nat.add(acc, Nat.add(len, len)),
              NatProof.NatPrf.add_assoc(acc, clb, 1n),
              Equal.cong(Nat, Nat, x => Nat.add(acc, x),
                Nat.add(clb, 1n), Nat.add(len, len), eclb))
          +e5 : {Nat.add(Nat.add(Nat.add(acc, clb), 1n), Nat.add(mr, mr))
                 == Nat.add(acc,
                      Nat.add(Nat.add(len, len), Nat.add(mr, mr))) : Nat} =
            Equal.trans(Nat,
              Nat.add(Nat.add(Nat.add(acc, clb), 1n), Nat.add(mr, mr)),
              Nat.add(Nat.add(acc, Nat.add(len, len)), Nat.add(mr, mr)),
              Nat.add(acc, Nat.add(Nat.add(len, len), Nat.add(mr, mr))),
              Equal.cong(Nat, Nat, x => Nat.add(x, Nat.add(mr, mr)),
                Nat.add(Nat.add(acc, clb), 1n),
                Nat.add(acc, Nat.add(len, len)), e4),
              NatProof.NatPrf.add_assoc(acc, Nat.add(len, len), Nat.add(mr, mr)))
          +e6 : {Nat.add(acc, Nat.add(Nat.add(len, len), Nat.add(mr, mr)))
                 == Nat.add(acc,
                      Nat.add(Nat.add(len, mr), Nat.add(len, mr))) : Nat} =
            Equal.cong(Nat, Nat, x => Nat.add(acc, x),
              Nat.add(Nat.add(len, len), Nat.add(mr, mr)),
              Nat.add(Nat.add(len, mr), Nat.add(len, mr)),
              Equal.sym(Nat,
                Nat.add(Nat.add(len, mr), Nat.add(len, mr)),
                Nat.add(Nat.add(len, len), Nat.add(mr, mr)),
                FH.nat_add_2_step(len, mr)))
          Equal.trans(Nat,
            Nat.add(lb_r, Nat.add(1n, kr)),
            Nat.add(Nat.add(Nat.add(acc, clb), 1n), Nat.add(mr, mr)),
            Nat.add(acc, Nat.add(Nat.add(len, mr), Nat.add(len, mr))),
            Equal.trans(Nat,
              Nat.add(lb_r, Nat.add(1n, kr)),
              Nat.add(Nat.add(lb_r, kr), 1n),
              Nat.add(Nat.add(Nat.add(acc, clb), 1n), Nat.add(mr, mr)),
              e1,
              Equal.trans(Nat,
                Nat.add(Nat.add(lb_r, kr), 1n),
                Nat.add(Nat.add(Nat.add(acc, clb), Nat.add(mr, mr)), 1n),
                Nat.add(Nat.add(Nat.add(acc, clb), 1n), Nat.add(mr, mr)),
                e2, e3)),
            Equal.trans(Nat,
              Nat.add(Nat.add(Nat.add(acc, clb), 1n), Nat.add(mr, mr)),
              Nat.add(acc, Nat.add(Nat.add(len, len), Nat.add(mr, mr))),
              Nat.add(acc, Nat.add(Nat.add(len, mr), Nat.add(len, mr))),
              e5, e6))

def FH.fgroups_lb_nodup_formula(+n: Nat, +fg: +List<SolveFast.FGroup>,
    +hpos: {FH.fgroups_pos(fg) == True{} : Bool}) ->
  {SolveFast.fgroups_lb_nodup(fg, n)
   == Nat.sub(
        Nat.add(n, Nat.add(FH.fgroups_total(fg), FH.fgroups_total(fg))),
        FH.fgroups_count(fg)) : Nat}:
  +lb = SolveFast.fgroups_lb_nodup(fg, n)
  +m = FH.fgroups_total(fg)
  +k = FH.fgroups_count(fg)
  Equal.trans(Nat,
    lb,
    Nat.sub(Nat.add(lb, k), k),
    Nat.sub(Nat.add(n, Nat.add(m, m)), k),
    Equal.sym(Nat, Nat.sub(Nat.add(lb, k), k), lb, FH.nat_sub_add_cancel(lb, k)),
    Equal.cong(Nat, Nat, x => Nat.sub(x, k),
      Nat.add(lb, k), Nat.add(n, Nat.add(m, m)),
      FH.fgroups_lb_nodup_sum(fg, n, hpos)))

# Theorem 2: `fgroups_smaller(n, fg) == (total(fg) < n) || (2 <= count(fg))`
# whenever `fgroups_pos(fg) == True{}`, `1 <= n`, and `total(fg) <= n`.
def FH.fgroups_smaller_go_of_lt(+n: Nat, +fg: +List<SolveFast.FGroup>,
    +hlt: {Nat.is_lt(FH.fgroups_total(fg), n) == True{} : Bool}) ->
  {SolveFast.fgroups_smaller(n, fg) == True{} : Bool}:
  match fg:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          +hhead : {Nat.is_lt(len, n) == True{} : Bool} =
            NatProof.Nat.is_le_lt_trans(len, Nat.add(len, FH.fgroups_total(rest)),
              n, FH.nat_le_add_l(len, FH.fgroups_total(rest)), hlt)
          +hrest : {Nat.is_lt(FH.fgroups_total(rest), n) == True{} : Bool} =
            NatProof.Nat.is_le_lt_trans(FH.fgroups_total(rest),
              Nat.add(len, FH.fgroups_total(rest)), n,
              FH.nat_le_add_r(len, FH.fgroups_total(rest)), hlt)
          Equal.trans(Bool,
            SolveFast.fgroups_smaller_go(n,
              SolveFast.FGroup{f, len, rws} <> rest, Nat.is_lt(len, n)),
            SolveFast.fgroups_smaller_go(n,
              SolveFast.FGroup{f, len, rws} <> rest, True{}),
            True{},
            Equal.cong(Bool, Bool,
              b => SolveFast.fgroups_smaller_go(n,
                     SolveFast.FGroup{f, len, rws} <> rest, b),
              Nat.is_lt(len, n), True{}, hhead),
            FH.fgroups_smaller_go_of_lt(n, rest, hrest))

def FH.fgroups_smaller_of_eq(+n: Nat, +fg: +List<SolveFast.FGroup>,
    +hpos: {FH.fgroups_pos(fg) == True{} : Bool},
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +heq: {FH.fgroups_total(fg) == n : Nat}) ->
  {SolveFast.fgroups_smaller(n, fg)
   == Bool.or(False{}, Nat.is_le(2n, FH.fgroups_count(fg))) : Bool}:
  match fg:
    case Nil{}:
      +h10 : {Nat.is_le(1n, 0n) == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(1n, n, 0n,
          Equal.sym(Nat, 0n, n, heq), hge1)
      Empty.absurd({True{} == False{} : Bool},
        Logic.Proof.false_ne_true(h10))
    case Con{gp1, rest1}:
      match gp1:
        case SolveFast.FGroup{+f1, +l1, +r1}:
          match rest1:
            case Nil{}:
              +el1 : {l1 == n : Nat} =
                Equal.trans(Nat, l1, Nat.add(l1, 0n), n,
                  Equal.sym(Nat, Nat.add(l1, 0n), l1,
                    NatProof.NatPrf.add_zero(l1)),
                  heq)
              +ef : {Nat.is_lt(l1, n) == False{} : Bool} =
                Equal.trans(Bool, Nat.is_lt(l1, n), Nat.is_lt(n, n), False{},
                  Equal.cong(Nat, Bool, x => Nat.is_lt(x, n), l1, n, el1),
                  FH.nat_is_lt_irrefl(n))
              Equal.cong(Bool, Bool,
                b => SolveFast.fgroups_smaller_go(n,
                       SolveFast.FGroup{f1, l1, r1} <> Nil{}, b),
                Nat.is_lt(l1, n), False{}, ef)
            case Con{gp2, rest2}:
              match gp2:
                case SolveFast.FGroup{+f2, +l2, +r2}:
                  +hl1 : {Nat.is_le(1n, l1) == True{} : Bool} =
                    Logic.Proof.and_true_l(Nat.is_le(1n, l1),
                      Bool.and(Nat.is_le(1n, l2), FH.fgroups_pos(rest2)),
                      hpos)
                  +hpr1 : {Bool.and(Nat.is_le(1n, l2), FH.fgroups_pos(rest2))
                           == True{} : Bool} =
                    Logic.Proof.and_true_r(Nat.is_le(1n, l1),
                      Bool.and(Nat.is_le(1n, l2), FH.fgroups_pos(rest2)),
                      hpos)
                  +hl2 : {Nat.is_le(1n, l2) == True{} : Bool} =
                    Logic.Proof.and_true_l(Nat.is_le(1n, l2),
                      FH.fgroups_pos(rest2), hpr1)
                  +mr1 : Nat = Nat.add(l2, FH.fgroups_total(rest2))
                  +hmr1_pos : {Nat.is_le(1n, mr1) == True{} : Bool} =
                    FH.nat_le_1_add(l2, FH.fgroups_total(rest2), hl2)
                  +hl1_lt : {Nat.is_lt(l1, n) == True{} : Bool} =
                    Equal.trans(Bool,
                      Nat.is_lt(l1, n),
                      Nat.is_lt(l1, Nat.add(l1, mr1)),
                      True{},
                      Equal.cong(Nat, Bool, x => Nat.is_lt(l1, x),
                        n, Nat.add(l1, mr1),
                        Equal.sym(Nat, Nat.add(l1, mr1), n, heq)),
                      FH.nat_is_lt_add_pos(l1, mr1, hmr1_pos))
                  +hmr1_lt : {Nat.is_lt(mr1, n) == True{} : Bool} =
                    Equal.trans(Bool,
                      Nat.is_lt(mr1, n),
                      Nat.is_lt(mr1, Nat.add(mr1, l1)),
                      True{},
                      Equal.cong(Nat, Bool, x => Nat.is_lt(mr1, x),
                        n, Nat.add(mr1, l1),
                        Equal.trans(Nat, n, Nat.add(l1, mr1),
                          Nat.add(mr1, l1),
                          Equal.sym(Nat, Nat.add(l1, mr1), n, heq),
                          NatProof.NatPrf.add_comm(l1, mr1))),
                      FH.nat_is_lt_add_pos(mr1, l1, hl1))
                  +rlist : +List<SolveFast.FGroup> =
                    SolveFast.FGroup{f2, l2, r2} <> rest2
                  Equal.trans(Bool,
                    SolveFast.fgroups_smaller_go(n,
                      SolveFast.FGroup{f1, l1, r1} <> rlist,
                      Nat.is_lt(l1, n)),
                    True{},
                    Nat.is_le(0n, FH.fgroups_count(rest2)),
                    Equal.trans(Bool,
                      SolveFast.fgroups_smaller_go(n,
                        SolveFast.FGroup{f1, l1, r1} <> rlist,
                        Nat.is_lt(l1, n)),
                      SolveFast.fgroups_smaller_go(n,
                        SolveFast.FGroup{f1, l1, r1} <> rlist, True{}),
                      True{},
                      Equal.cong(Bool, Bool,
                        b => SolveFast.fgroups_smaller_go(n,
                               SolveFast.FGroup{f1, l1, r1} <> rlist, b),
                        Nat.is_lt(l1, n), True{}, hl1_lt),
                      FH.fgroups_smaller_go_of_lt(n, rlist, hmr1_lt)),
                    Equal.sym(Bool,
                      Nat.is_le(0n, FH.fgroups_count(rest2)), True{},
                      NatProof.Nat.is_le_zero_l(FH.fgroups_count(rest2))))

def FH.fgroups_smaller_of_lt_bound(+n: Nat, +fg: +List<SolveFast.FGroup>,
    +hpos: {FH.fgroups_pos(fg) == True{} : Bool},
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +hle: {Nat.is_le(FH.fgroups_total(fg), n) == True{} : Bool},
    lt: Bool, +elt: {lt == Nat.is_lt(FH.fgroups_total(fg), n) : Bool}) ->
  {SolveFast.fgroups_smaller(n, fg)
   == Bool.or(lt, Nat.is_le(2n, FH.fgroups_count(fg))) : Bool}:
  match lt:
    case True{}:
      FH.fgroups_smaller_go_of_lt(n, fg,
        Equal.sym(Bool, True{}, Nat.is_lt(FH.fgroups_total(fg), n), elt))
    case False{}:
      FH.fgroups_smaller_of_eq(n, fg, hpos, hge1,
        FH.nat_eq_of_le_and_not_lt(FH.fgroups_total(fg), n, hle,
          Equal.sym(Bool, False{}, Nat.is_lt(FH.fgroups_total(fg), n), elt)))

def FH.fgroups_smaller_formula(+n: Nat, +fg: +List<SolveFast.FGroup>,
    +hpos: {FH.fgroups_pos(fg) == True{} : Bool},
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +hle: {Nat.is_le(FH.fgroups_total(fg), n) == True{} : Bool}) ->
  {SolveFast.fgroups_smaller(n, fg)
   == Bool.or(Nat.is_lt(FH.fgroups_total(fg), n),
              Nat.is_le(2n, FH.fgroups_count(fg))) : Bool}:
  FH.fgroups_smaller_of_lt_bound(n, fg, hpos, hge1, hle,
    Nat.is_lt(FH.fgroups_total(fg), n), {==})

# `rev_words_len` equals `(len + |xs|, rev_words(xs, acc))`.
def FH.rev_words_len_eq(+xs: +List<+List<Nat>>, +acc: +List<+List<Nat>>,
    +len: Nat) ->
  {SolveFast.rev_words_len(xs, acc, len)
   == SolveFast.RevLen{Nat.add(len, Groups.len_words(xs)),
                       SolveFast.rev_words(xs, acc)} : SolveFast.RevLen}:
  match xs:
    case Nil{}:
      Equal.cong(Nat, SolveFast.RevLen, l => SolveFast.RevLen{l, acc},
        len, Nat.add(len, 0n),
        Equal.sym(Nat, Nat.add(len, 0n), len, NatProof.NatPrf.add_zero(len)))
    case Con{+w, +t}:
      Equal.trans(SolveFast.RevLen,
        SolveFast.rev_words_len(t, w <> acc, Nat.add(1n, len)),
        SolveFast.RevLen{Nat.add(Nat.add(1n, len), Groups.len_words(t)),
                         SolveFast.rev_words(t, w <> acc)},
        SolveFast.RevLen{Nat.add(len, Nat.add(1n, Groups.len_words(t))),
                         SolveFast.rev_words(t, w <> acc)},
        FH.rev_words_len_eq(t, w <> acc, Nat.add(1n, len)),
        Equal.cong(Nat, SolveFast.RevLen,
          l => SolveFast.RevLen{l, SolveFast.rev_words(t, w <> acc)},
          Nat.add(Nat.add(1n, len), Groups.len_words(t)),
          Nat.add(len, Nat.add(1n, Groups.len_words(t))),
          Equal.sym(Nat,
            Nat.add(len, Nat.add(1n, Groups.len_words(t))),
            Nat.add(Nat.add(1n, len), Groups.len_words(t)),
            NatProof.NatPrf.add_succ(len, Groups.len_words(t)))))

# ---------------------------------------------------------------------------
# Bit-level index helpers for symbolic depth-indexed array invariants
# ---------------------------------------------------------------------------

def FH.word_bit_or_pow2_same(+k: Nat, +m: Nat, +w: Word(m),
    +lt: {Nat.is_lt(k, m) == True{} : Bool}) ->
  {Arr.Arr.word_bit(k, m, Word.or(m, w, Arr.Arr.pow2_word(k, m)))
   == True{} : Bool}:
  match k m:
    case _ 0n:
      Empty.absurd(
        {Arr.Arr.word_bit(k, 0n, Word.or(0n, w, Arr.Arr.pow2_word(k, 0n)))
         == True{} : Bool},
        Logic.Proof.false_ne_true(lt))
    case 0n 1n++mp:
      match w:
        case WCon{+b, +t}:
          match b:
            case True{}:
              {==}
            case False{}:
              {==}
    case 1n++kp 1n++mp:
      match w:
        case WCon{+b, +t}:
          FH.word_bit_or_pow2_same(kp, mp, t, lt)

def FH.word_bit_or_pow2_lt(+k: Nat, +j: Nat, +m: Nat, +w: Word(m),
    +hjk: {Nat.is_lt(j, k) == True{} : Bool}) ->
  {Arr.Arr.word_bit(k, m, Word.or(m, w, Arr.Arr.pow2_word(j, m)))
   == Arr.Arr.word_bit(k, m, w) : Bool}:
  match k j m:
    case _ _ 0n:
      {==}
    case 0n _ 1n++mp:
      Empty.absurd(
        {Arr.Arr.word_bit(0n, 1n+mp, Word.or(1n+mp, w, Arr.Arr.pow2_word(j, 1n+mp)))
         == Arr.Arr.word_bit(0n, 1n+mp, w) : Bool},
        NatProof.Nat.not_lt_zero(j, hjk))
    case 1n++kp 0n 1n++mp:
      match w:
        case WCon{+b, +t}:
          Equal.cong(Word(mp), Bool, x => Arr.Arr.word_bit(kp, mp, x),
            Word.or(mp, t, Word.zero(mp)), t, FF5.FF5.word_or_zero_r(mp, t))
    case 1n++kp 1n++jp 1n++mp:
      match w:
        case WCon{+b, +t}:
          FH.word_bit_or_pow2_lt(kp, jp, mp, t, hjk)

def FH.word_or_pow2_sub(+k: Nat, +m: Nat, +w: Word(m),
    +hb: {Arr.Arr.word_bit(k, m, w) == True{} : Bool}) ->
  {Word.or(m, Arr.Arr.pow2_word(k, m), Word.sub(m, w, Arr.Arr.pow2_word(k, m)))
   == w : Word(m)}:
  match k m:
    case _ 0n:
      match w:
        case WNil{}:
          {==}
    case 0n 1n++mp:
      match w:
        case WCon{+b, +t}:
          +eq1 : {Word.sub(1n+mp, WCon{b, t}, Arr.Arr.pow2_word(0n, 1n+mp))
                  == WCon{False{}, Word.adc(mp, t, Word.zero(mp), True{}, True{})}
                  : Word(1n+mp)} =
            Equal.cong(Bool, Word(1n+mp),
              x => Word.sub(1n+mp, WCon{x, t}, Arr.Arr.pow2_word(0n, 1n+mp)),
              b, True{}, hb)
          +eq2 : {WCon{False{}, Word.adc(mp, t, Word.zero(mp), True{}, True{})}
                  == WCon{False{}, t} : Word(1n+mp)} =
            Equal.cong(Word(mp), Word(1n+mp), x => WCon{False{}, x},
              Word.adc(mp, t, Word.zero(mp), True{}, True{}), t,
              Arr.Arr.word_adc_sub_zero_t(mp, t))
          +eq3 : {Word.or(1n+mp, Arr.Arr.pow2_word(0n, 1n+mp), WCon{False{}, t})
                  == WCon{True{}, t} : Word(1n+mp)} =
            Equal.cong(Word(mp), Word(1n+mp), x => WCon{True{}, x},
              Word.or(mp, Word.zero(mp), t), t, FF5.FF5.word_or_zero_l(mp, t))
          Equal.trans(Word(1n+mp),
            Word.or(1n+mp, Arr.Arr.pow2_word(0n, 1n+mp),
              Word.sub(1n+mp, WCon{b, t}, Arr.Arr.pow2_word(0n, 1n+mp))),
            WCon{True{}, t},
            WCon{b, t},
            Equal.trans(Word(1n+mp),
              Word.or(1n+mp, Arr.Arr.pow2_word(0n, 1n+mp),
                Word.sub(1n+mp, WCon{b, t}, Arr.Arr.pow2_word(0n, 1n+mp))),
              Word.or(1n+mp, Arr.Arr.pow2_word(0n, 1n+mp), WCon{False{}, t}),
              WCon{True{}, t},
              Equal.cong(Word(1n+mp), Word(1n+mp),
                x => Word.or(1n+mp, Arr.Arr.pow2_word(0n, 1n+mp), x),
                Word.sub(1n+mp, WCon{b, t}, Arr.Arr.pow2_word(0n, 1n+mp)),
                WCon{False{}, t},
                Equal.trans(Word(1n+mp),
                  Word.sub(1n+mp, WCon{b, t}, Arr.Arr.pow2_word(0n, 1n+mp)),
                  WCon{False{}, Word.adc(mp, t, Word.zero(mp), True{}, True{})},
                  WCon{False{}, t}, eq1, eq2)),
              eq3),
            Equal.cong(Bool, Word(1n+mp), x => WCon{x, t}, True{}, b,
              Equal.sym(Bool, b, True{}, hb)))
    case 1n++kp 1n++mp:
      match w:
        case WCon{+b, +t}:
          match b:
            case False{}:
              Equal.cong(Word(mp), Word(1n+mp), x => WCon{False{}, x},
                Word.or(mp, Arr.Arr.pow2_word(kp, mp),
                  Word.sub(mp, t, Arr.Arr.pow2_word(kp, mp))),
                t, FH.word_or_pow2_sub(kp, mp, t, hb))
            case True{}:
              Equal.cong(Word(mp), Word(1n+mp), x => WCon{True{}, x},
                Word.or(mp, Arr.Arr.pow2_word(kp, mp),
                  Word.sub(mp, t, Arr.Arr.pow2_word(kp, mp))),
                t, FH.word_or_pow2_sub(kp, mp, t, hb))

def FH.u32_bit(+k: Nat, +u: U32) -> Bool:
  match u:
    case U32{w}:
      Arr.Arr.word_bit(k, 32n, w)

def FH.u32_bit_or_pow2_same(+k: Nat, +u: U32,
    +lt: {Nat.is_lt(k, 32n) == True{} : Bool}) ->
  {FH.u32_bit(k, U32.or(u, Arr.Arr.pow2_u32(k))) == True{} : Bool}:
  match u:
    case U32{+w}:
      FH.word_bit_or_pow2_same(k, 32n, w, lt)

def FH.u32_bit_or_pow2_lt(+k: Nat, +j: Nat, +u: U32,
    +hjk: {Nat.is_lt(j, k) == True{} : Bool}) ->
  {FH.u32_bit(k, U32.or(u, Arr.Arr.pow2_u32(j))) == FH.u32_bit(k, u) : Bool}:
  match u:
    case U32{+w}:
      FH.word_bit_or_pow2_lt(k, j, 32n, w, hjk)

def FH.u32_or_base_sub(+p: Nat, +base: U32, +i: U32,
    +hz: {Arr.Arr.u32_zero_from(1n+p, i) == True{} : Bool},
    +lt: {Nat.is_lt(p, 32n) == True{} : Bool},
    +hge: {U32.is_lt(i, Arr.Arr.pow2_u32(p)) == False{} : Bool}) ->
  {U32.or(U32.or(base, Arr.Arr.pow2_u32(p)), U32.sub(i, Arr.Arr.pow2_u32(p)))
   == U32.or(base, i) : U32}:
  match i:
    case U32{+wi}:
      +hnb : {Bool.not(Arr.Arr.word_bit(p, 32n, wi)) == False{} : Bool} =
        Equal.trans(Bool,
          Bool.not(Arr.Arr.word_bit(p, 32n, wi)),
          Cmp.is_lt(Word.cmp(32n, wi, Arr.Arr.pow2_word(p, 32n))),
          False{},
          Equal.sym(Bool,
            Cmp.is_lt(Word.cmp(32n, wi, Arr.Arr.pow2_word(p, 32n))),
            Bool.not(Arr.Arr.word_bit(p, 32n, wi)),
            Arr.Arr.word_cmp_pow2_bit(p, 32n, wi, hz, lt)),
          hge)
      +hb : {Arr.Arr.word_bit(p, 32n, wi) == True{} : Bool} =
        Arr.Arr.bool_not_false(Arr.Arr.word_bit(p, 32n, wi), hnb)
      +eor : {U32.or(Arr.Arr.pow2_u32(p), U32.sub(U32{wi}, Arr.Arr.pow2_u32(p)))
              == U32{wi} : U32} =
        Equal.cong(Word(32n), U32, x => U32{x},
          Word.or(32n, Arr.Arr.pow2_word(p, 32n),
            Word.sub(32n, wi, Arr.Arr.pow2_word(p, 32n))),
          wi, FH.word_or_pow2_sub(p, 32n, wi, hb))
      Equal.trans(U32,
        U32.or(U32.or(base, Arr.Arr.pow2_u32(p)),
          U32.sub(U32{wi}, Arr.Arr.pow2_u32(p))),
        U32.or(base,
          U32.or(Arr.Arr.pow2_u32(p), U32.sub(U32{wi}, Arr.Arr.pow2_u32(p)))),
        U32.or(base, U32{wi}),
        FF5.FF5.u32_or_assoc(base, Arr.Arr.pow2_u32(p),
          U32.sub(U32{wi}, Arr.Arr.pow2_u32(p))),
        Equal.cong(U32, U32, x => U32.or(base, x),
          U32.or(Arr.Arr.pow2_u32(p), U32.sub(U32{wi}, Arr.Arr.pow2_u32(p))),
          U32{wi}, eor))

def FH.word_bit_or(+k: Nat, +m: Nat, +a: Word(m), +b: Word(m)) ->
  {Arr.Arr.word_bit(k, m, Word.or(m, a, b))
   == Bool.or(Arr.Arr.word_bit(k, m, a), Arr.Arr.word_bit(k, m, b)) : Bool}:
  match k m:
    case _ 0n:
      {==}
    case 0n 1n++mp:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          {==}
    case 1n++kp 1n++mp:
      match a b:
        case WCon{ab, at} WCon{bb, bt}:
          FH.word_bit_or(kp, mp, at, bt)

def FH.u32_bit_or(+k: Nat, +a: U32, +b: U32) ->
  {FH.u32_bit(k, U32.or(a, b))
   == Bool.or(FH.u32_bit(k, a), FH.u32_bit(k, b)) : Bool}:
  match a b:
    case U32{+wa} U32{+wb}:
      FH.word_bit_or(k, 32n, wa, wb)

def FH.word_bit_zero_of_zero_from(+d: Nat, +k: Nat, +m: Nat, +w: Word(m),
    +hz: {Arr.Arr.word_zero_from(d, m, w) == True{} : Bool},
    +hle: {Nat.is_le(d, k) == True{} : Bool}) ->
  {Arr.Arr.word_bit(k, m, w) == False{} : Bool}:
  match d k m:
    case _ _ 0n:
      {==}
    case 0n 0n 1n++mp:
      match w:
        case WCon{+b, +t}:
          Arr.Arr.bool_not_true(b,
            Logic.Proof.and_true_l(Bool.not(b),
              Arr.Arr.word_zero_from(0n, mp, t), hz))
    case 0n 1n++kp 1n++mp:
      match w:
        case WCon{+b, +t}:
          FH.word_bit_zero_of_zero_from(0n, kp, mp, t,
            Logic.Proof.and_true_r(Bool.not(b),
              Arr.Arr.word_zero_from(0n, mp, t), hz),
            NatProof.Nat.is_le_zero_l(kp))
    case 1n++dp 0n 1n++mp:
      Empty.absurd({Arr.Arr.word_bit(0n, 1n+mp, w) == False{} : Bool},
        Logic.Proof.false_ne_true(hle))
    case 1n++dp 1n++kp 1n++mp:
      match w:
        case WCon{+b, +t}:
          FH.word_bit_zero_of_zero_from(dp, kp, mp, t, hz, hle)

def FH.u32_bit_zero_of_zero_from(+d: Nat, +k: Nat, +u: U32,
    +hz: {Arr.Arr.u32_zero_from(d, u) == True{} : Bool},
    +hle: {Nat.is_le(d, k) == True{} : Bool}) ->
  {FH.u32_bit(k, u) == False{} : Bool}:
  match u:
    case U32{+w}:
      FH.word_bit_zero_of_zero_from(d, k, 32n, w, hz, hle)

def FH.u32_bit_of_lt(+p: Nat, +i: U32,
    +hz: {Arr.Arr.u32_zero_from(1n+p, i) == True{} : Bool},
    +lt: {Nat.is_lt(p, 32n) == True{} : Bool},
    +hlt: {U32.is_lt(i, Arr.Arr.pow2_u32(p)) == True{} : Bool}) ->
  {FH.u32_bit(p, i) == False{} : Bool}:
  match i:
    case U32{+wi}:
      +hnb : {Bool.not(Arr.Arr.word_bit(p, 32n, wi)) == True{} : Bool} =
        Equal.trans(Bool,
          Bool.not(Arr.Arr.word_bit(p, 32n, wi)),
          Cmp.is_lt(Word.cmp(32n, wi, Arr.Arr.pow2_word(p, 32n))),
          True{},
          Equal.sym(Bool,
            Cmp.is_lt(Word.cmp(32n, wi, Arr.Arr.pow2_word(p, 32n))),
            Bool.not(Arr.Arr.word_bit(p, 32n, wi)),
            Arr.Arr.word_cmp_pow2_bit(p, 32n, wi, hz, lt)),
          hlt)
      Arr.Arr.bool_not_true(Arr.Arr.word_bit(p, 32n, wi), hnb)

def FH.u32_bit_of_ge(+p: Nat, +i: U32,
    +hz: {Arr.Arr.u32_zero_from(1n+p, i) == True{} : Bool},
    +lt: {Nat.is_lt(p, 32n) == True{} : Bool},
    +hge: {U32.is_lt(i, Arr.Arr.pow2_u32(p)) == False{} : Bool}) ->
  {FH.u32_bit(p, i) == True{} : Bool}:
  match i:
    case U32{+wi}:
      +hnb : {Bool.not(Arr.Arr.word_bit(p, 32n, wi)) == False{} : Bool} =
        Equal.trans(Bool,
          Bool.not(Arr.Arr.word_bit(p, 32n, wi)),
          Cmp.is_lt(Word.cmp(32n, wi, Arr.Arr.pow2_word(p, 32n))),
          False{},
          Equal.sym(Bool,
            Cmp.is_lt(Word.cmp(32n, wi, Arr.Arr.pow2_word(p, 32n))),
            Bool.not(Arr.Arr.word_bit(p, 32n, wi)),
            Arr.Arr.word_cmp_pow2_bit(p, 32n, wi, hz, lt)),
          hge)
      Arr.Arr.bool_not_false(Arr.Arr.word_bit(p, 32n, wi), hnb)

def FH.u32_ne_of_bit_diff_go(+k: Nat, +a: U32, +b: U32,
    +ha: {FH.u32_bit(k, a) == True{} : Bool},
    +hb: {FH.u32_bit(k, b) == False{} : Bool},
    eq: Bool, +eeq: {eq == U32.is_eq(a, b) : Bool}) ->
  {U32.is_eq(a, b) == False{} : Bool}:
  match eq:
    case False{}:
      Equal.sym(Bool, False{}, U32.is_eq(a, b), eeq)
    case True{}:
      +eab : {a == b : U32} =
        Arr.Arr.u32_is_eq_true(a, b,
          Equal.sym(Bool, True{}, U32.is_eq(a, b), eeq))
      +etf : {True{} == False{} : Bool} =
        Equal.trans(Bool, True{}, FH.u32_bit(k, a), False{},
          Equal.sym(Bool, FH.u32_bit(k, a), True{}, ha),
          Equal.trans(Bool, FH.u32_bit(k, a), FH.u32_bit(k, b), False{},
            Equal.cong(U32, Bool, u => FH.u32_bit(k, u), a, b, eab), hb))
      Empty.absurd({U32.is_eq(a, b) == False{} : Bool},
        Logic.Proof.true_ne_false(etf))

def FH.u32_ne_of_bit_tf(+k: Nat, +a: U32, +b: U32,
    +ha: {FH.u32_bit(k, a) == True{} : Bool},
    +hb: {FH.u32_bit(k, b) == False{} : Bool}) ->
  {U32.is_eq(a, b) == False{} : Bool}:
  FH.u32_ne_of_bit_diff_go(k, a, b, ha, hb, U32.is_eq(a, b), {==})

def FH.u32_ne_sym_go(+a: U32, +b: U32,
    +hne: {U32.is_eq(a, b) == False{} : Bool},
    eq: Bool, +eeq: {eq == U32.is_eq(b, a) : Bool}) ->
  {U32.is_eq(b, a) == False{} : Bool}:
  match eq:
    case False{}:
      Equal.sym(Bool, False{}, U32.is_eq(b, a), eeq)
    case True{}:
      +eba : {b == a : U32} =
        Arr.Arr.u32_is_eq_true(b, a,
          Equal.sym(Bool, True{}, U32.is_eq(b, a), eeq))
      +et : {U32.is_eq(a, b) == True{} : Bool} =
        Equal.trans(Bool, U32.is_eq(a, b), U32.is_eq(a, a), True{},
          Equal.cong(U32, Bool, x => U32.is_eq(a, x), b, a, eba),
          Arr.Arr.u32_is_eq_refl(a))
      Empty.absurd({U32.is_eq(b, a) == False{} : Bool},
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, U32.is_eq(a, b), False{},
            Equal.sym(Bool, U32.is_eq(a, b), True{}, et), hne)))

def FH.u32_ne_sym(+a: U32, +b: U32,
    +hne: {U32.is_eq(a, b) == False{} : Bool}) ->
  {U32.is_eq(b, a) == False{} : Bool}:
  FH.u32_ne_sym_go(a, b, hne, U32.is_eq(b, a), {==})

def FH.u32_ne_of_bit_ft(+k: Nat, +a: U32, +b: U32,
    +ha: {FH.u32_bit(k, a) == False{} : Bool},
    +hb: {FH.u32_bit(k, b) == True{} : Bool}) ->
  {U32.is_eq(a, b) == False{} : Bool}:
  FH.u32_ne_sym(b, a, FH.u32_ne_of_bit_tf(k, b, a, hb, ha))

# ---------------------------------------------------------------------------
# Evolution of `FGroup` specs under `fgroup_add_fast` and `fgroups_build_fast`
# ---------------------------------------------------------------------------

def FH.rev_codes(+fg: +List<SolveFast.FGroup>,
                 +acc: +List<U32>) -> +List<U32>:
  match fg:
    case Nil{}:
      acc
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{f, len, rws}:
          FH.rev_codes(rest, FF5.FF5.encode_fb5_list(f) <> acc)

def FH.bool_or_false_l(b: Bool) -> {Bool.or(False{}, b) == b : Bool}:
  {==}

def FH.bool_or_true_l(b: Bool) -> {Bool.or(True{}, b) == True{} : Bool}:
  {==}

def FH.bool_not_true_of_false(b: Bool, +e: {b == False{} : Bool}) ->
  {Bool.not(b) == True{} : Bool}:
  Equal.cong(Bool, Bool, Bool.not, b, False{}, e)

def FH.bool_false_of_not_true(b: Bool, +e: {Bool.not(b) == True{} : Bool}) ->
  {b == False{} : Bool}:
  Arr.Arr.bool_not_true(b, e)

def FH.bool_or_false_l_inv(a: Bool, b: Bool,
    +e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Logic.Proof.true_ne_false(e))

def FH.bool_or_false_r_inv(a: Bool, b: Bool,
    +e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      Empty.absurd({b == False{} : Bool}, Logic.Proof.true_ne_false(e))

def FH.u32_eq_sym_bool_go(+a: U32, +b: U32,
    b1: Bool, +e1: {b1 == U32.is_eq(a, b) : Bool},
    b2: Bool, +e2: {b2 == U32.is_eq(b, a) : Bool}) ->
  {U32.is_eq(a, b) == U32.is_eq(b, a) : Bool}:
  match b1 b2:
    case True{} True{}:
      Equal.trans(Bool, U32.is_eq(a, b), True{}, U32.is_eq(b, a),
        Equal.sym(Bool, True{}, U32.is_eq(a, b), e1), e2)
    case False{} False{}:
      Equal.trans(Bool, U32.is_eq(a, b), False{}, U32.is_eq(b, a),
        Equal.sym(Bool, False{}, U32.is_eq(a, b), e1), e2)
    case True{} False{}:
      +ef : {U32.is_eq(a, b) == False{} : Bool} =
        FH.u32_ne_sym(b, a, Equal.sym(Bool, False{}, U32.is_eq(b, a), e2))
      Empty.absurd({U32.is_eq(a, b) == U32.is_eq(b, a) : Bool},
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, U32.is_eq(a, b), False{}, e1, ef)))
    case False{} True{}:
      +ef : {U32.is_eq(b, a) == False{} : Bool} =
        FH.u32_ne_sym(a, b, Equal.sym(Bool, False{}, U32.is_eq(a, b), e1))
      Empty.absurd({U32.is_eq(a, b) == U32.is_eq(b, a) : Bool},
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, U32.is_eq(b, a), False{}, e2, ef)))

def FH.u32_eq_sym_bool(+a: U32, +b: U32) ->
  {U32.is_eq(a, b) == U32.is_eq(b, a) : Bool}:
  FH.u32_eq_sym_bool_go(a, b, U32.is_eq(a, b), {==}, U32.is_eq(b, a), {==})

def FH.succ_bool_case(b: Bool, +x: Nat, +y: Nat) ->
  {Nat.add(1n, Feedback.Bool.case(Nat, b, x, y))
   == Feedback.Bool.case(Nat, b, Nat.add(1n, x), Nat.add(1n, y)) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# `fgroup_add_go` properties for a 5-letter feedback `fb` with code `c = encode(fb)`.
# We bundle the key `fgroup_add` invariants cleanly in `FH.AddFacts` (`is Data`).
type FH.AddFacts<+w: +List<Nat>, +fb: +List<Feedback.Color>,
                 +fg: +List<SolveFast.FGroup>, +fg2: +List<SolveFast.FGroup>> is Data:
  AddFacts{
    wf2: {FH.fgroups_wf(fg2) == True{} : Bool},
    tot2: {FH.fgroups_total(fg2) == Nat.add(1n, FH.fgroups_total(fg)) : Nat},
    cnt2: {FH.fgroups_count(fg2)
           == Feedback.Bool.case(Nat,
                FH.has_code(FF5.FF5.encode_fb5_list(fb), fg),
                FH.fgroups_count(fg),
                Nat.add(1n, FH.fgroups_count(fg))) : Nat},
    has_self: {FH.has_code(FF5.FF5.encode_fb5_list(fb), fg2) == True{} : Bool},
    lkp_self: {FH.lookup_code(FF5.FF5.encode_fb5_list(fb), fg2)
               == w <> FH.lookup_code(FF5.FF5.encode_fb5_list(fb), fg)
               : +List<+List<Nat>>}
  }

def FH.fgroup_add_has_other(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +fg: +List<SolveFast.FGroup>, hit: Bool, +j: U32,
    +eh: {hit == SolveFast.next_fgroup_hit(fb, fg) : Bool},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool},
    +hne: {U32.is_eq(j, FF5.FF5.encode_fb5_list(fb)) == False{} : Bool}) ->
  {FH.has_code(j, SolveFast.fgroup_add_go(w, fb, fg, hit))
   == FH.has_code(j, fg) : Bool}:
  match fg:
    case Nil{}:
      Equal.cong(Bool, Bool, b => Bool.or(b, False{}),
        U32.is_eq(j, FF5.FF5.encode_fb5_list(fb)), False{}, hne)
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          match hit:
            case True{}:
              {==}
            case False{}:
              +h1 = Logic.Proof.and_true_r(FF5.FF5.is_fb5(f),
                      Bool.and(Nat.is_le(1n, len),
                        Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                          Bool.and(
                            Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), rest)),
                            FH.fgroups_wf(rest)))), hwf)
              +h2 = Logic.Proof.and_true_r(Nat.is_le(1n, len),
                      Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                        Bool.and(
                          Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), rest)),
                          FH.fgroups_wf(rest))), h1)
              +h3 = Logic.Proof.and_true_r(Nat.is_eq(len, Groups.len_words(rws)),
                      Bool.and(
                        Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), rest)),
                        FH.fgroups_wf(rest)), h2)
              +hr = Logic.Proof.and_true_r(
                      Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), rest)),
                      FH.fgroups_wf(rest), h3)
              Equal.cong(Bool, Bool,
                b => Bool.or(U32.is_eq(j, FF5.FF5.encode_fb5_list(f)), b),
                FH.has_code(j, SolveFast.fgroup_add_go(w, fb, rest,
                  SolveFast.next_fgroup_hit(fb, rest))),
                FH.has_code(j, rest),
                FH.fgroup_add_has_other(w, fb, rest,
                  SolveFast.next_fgroup_hit(fb, rest), j, {==}, hfb, hr, hne))

def FH.fgroup_add_lookup_other(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +fg: +List<SolveFast.FGroup>, hit: Bool, +j: U32,
    +eh: {hit == SolveFast.next_fgroup_hit(fb, fg) : Bool},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool},
    +hne: {U32.is_eq(j, FF5.FF5.encode_fb5_list(fb)) == False{} : Bool}) ->
  {FH.lookup_code(j, SolveFast.fgroup_add_go(w, fb, fg, hit))
   == FH.lookup_code(j, fg) : +List<+List<Nat>>}:
  match fg:
    case Nil{}:
      Equal.cong(Bool, +List<+List<Nat>>,
        b => Feedback.Bool.case(+List<+List<Nat>>, b, w <> Nil{}, Nil{}),
        U32.is_eq(j, FF5.FF5.encode_fb5_list(fb)), False{}, hne)
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          match hit:
            case True{}:
              +hf5 : {FF5.FF5.is_fb5(f) == True{} : Bool} =
                Logic.Proof.and_true_l(FF5.FF5.is_fb5(f),
                  Bool.and(Nat.is_le(1n, len),
                    Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                      Bool.and(
                        Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), rest)),
                        FH.fgroups_wf(rest)))), hwf)
              +ec : {U32.is_eq(FF5.FF5.encode_fb5_list(fb),
                       FF5.FF5.encode_fb5_list(f)) == True{} : Bool} =
                Equal.trans(Bool,
                  U32.is_eq(FF5.FF5.encode_fb5_list(fb),
                    FF5.FF5.encode_fb5_list(f)),
                  Feedback.feedback_eq(fb, f),
                  True{},
                  FF5.FF5.code_eq_iff_fb_eq(fb, f, hfb, hf5),
                  Equal.trans(Bool, Feedback.feedback_eq(fb, f),
                    SolveFast.feedback_eq_fast(fb, f), True{},
                    Equal.sym(Bool, SolveFast.feedback_eq_fast(fb, f),
                      Feedback.feedback_eq(fb, f),
                      FG.FG.feedback_eq_fast_eq(fb, f)),
                    Equal.sym(Bool, True{}, SolveFast.feedback_eq_fast(fb, f),
                      eh)))
              +ef_eq : {FF5.FF5.encode_fb5_list(fb)
                        == FF5.FF5.encode_fb5_list(f) : U32} =
                Arr.Arr.u32_is_eq_true(FF5.FF5.encode_fb5_list(fb),
                  FF5.FF5.encode_fb5_list(f), ec)
              +hjf : {U32.is_eq(j, FF5.FF5.encode_fb5_list(f))
                      == False{} : Bool} =
                Equal.trans(Bool,
                  U32.is_eq(j, FF5.FF5.encode_fb5_list(f)),
                  U32.is_eq(j, FF5.FF5.encode_fb5_list(fb)),
                  False{},
                  Equal.cong(U32, Bool, x => U32.is_eq(j, x),
                    FF5.FF5.encode_fb5_list(f), FF5.FF5.encode_fb5_list(fb),
                    Equal.sym(U32, FF5.FF5.encode_fb5_list(fb),
                      FF5.FF5.encode_fb5_list(f), ef_eq)),
                  hne)
              Equal.trans(+List<+List<Nat>>,
                Feedback.Bool.case(+List<+List<Nat>>,
                  U32.is_eq(j, FF5.FF5.encode_fb5_list(f)),
                  w <> rws, FH.lookup_code(j, rest)),
                FH.lookup_code(j, rest),
                Feedback.Bool.case(+List<+List<Nat>>,
                  U32.is_eq(j, FF5.FF5.encode_fb5_list(f)),
                  rws, FH.lookup_code(j, rest)),
                Equal.cong(Bool, +List<+List<Nat>>,
                  b => Feedback.Bool.case(+List<+List<Nat>>, b,
                         w <> rws, FH.lookup_code(j, rest)),
                  U32.is_eq(j, FF5.FF5.encode_fb5_list(f)), False{}, hjf),
                Equal.sym(+List<+List<Nat>>,
                  Feedback.Bool.case(+List<+List<Nat>>,
                    U32.is_eq(j, FF5.FF5.encode_fb5_list(f)),
                    rws, FH.lookup_code(j, rest)),
                  FH.lookup_code(j, rest),
                  Equal.cong(Bool, +List<+List<Nat>>,
                    b => Feedback.Bool.case(+List<+List<Nat>>, b,
                           rws, FH.lookup_code(j, rest)),
                    U32.is_eq(j, FF5.FF5.encode_fb5_list(f)), False{}, hjf)))
            case False{}:
              +h1 = Logic.Proof.and_true_r(FF5.FF5.is_fb5(f),
                      Bool.and(Nat.is_le(1n, len),
                        Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                          Bool.and(
                            Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), rest)),
                            FH.fgroups_wf(rest)))), hwf)
              +h2 = Logic.Proof.and_true_r(Nat.is_le(1n, len),
                      Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                        Bool.and(
                          Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), rest)),
                          FH.fgroups_wf(rest))), h1)
              +h3 = Logic.Proof.and_true_r(Nat.is_eq(len, Groups.len_words(rws)),
                      Bool.and(
                        Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), rest)),
                        FH.fgroups_wf(rest)), h2)
              +hr = Logic.Proof.and_true_r(
                      Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), rest)),
                      FH.fgroups_wf(rest), h3)
              Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                x => Feedback.Bool.case(+List<+List<Nat>>,
                       U32.is_eq(j, FF5.FF5.encode_fb5_list(f)), rws, x),
                FH.lookup_code(j, SolveFast.fgroup_add_go(w, fb, rest,
                  SolveFast.next_fgroup_hit(fb, rest))),
                FH.lookup_code(j, rest),
                FH.fgroup_add_lookup_other(w, fb, rest,
                  SolveFast.next_fgroup_hit(fb, rest), j, {==}, hfb, hr, hne))

def FH.add_facts_false_step(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>,
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +hlen: {Nat.is_le(1n, len) == True{} : Bool},
    +heql: {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool},
    +hnf: {Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), rest))
           == True{} : Bool},
    +hr: {FH.fgroups_wf(rest) == True{} : Bool},
    +ec: {U32.is_eq(FF5.FF5.encode_fb5_list(fb), FF5.FF5.encode_fb5_list(f))
          == False{} : Bool},
    ih: FH.AddFacts<w, fb, rest,
          SolveFast.fgroup_add_go(w, fb, rest,
            SolveFast.next_fgroup_hit(fb, rest))>) ->
  FH.AddFacts<w, fb, SolveFast.FGroup{f, len, rws} <> rest,
    SolveFast.FGroup{f, len, rws}
    <> SolveFast.fgroup_add_go(w, fb, rest,
         SolveFast.next_fgroup_hit(fb, rest))>:
  match ih:
    case AddFacts{+wf_r, +tot_r, +cnt_r, +has_r, +lkp_r}:
      +c = FF5.FF5.encode_fb5_list(fb)
      +cf = FF5.FF5.encode_fb5_list(f)
      +ec_sym : {U32.is_eq(cf, c) == False{} : Bool} =
        FH.u32_ne_sym(c, cf, ec)
      +rest2 = SolveFast.fgroup_add_go(w, fb, rest,
                 SolveFast.next_fgroup_hit(fb, rest))
      +hnf2 : {Bool.not(FH.has_code(cf, rest2)) == True{} : Bool} =
        Equal.trans(Bool,
          Bool.not(FH.has_code(cf, rest2)),
          Bool.not(FH.has_code(cf, rest)),
          True{},
          Equal.cong(Bool, Bool, Bool.not,
            FH.has_code(cf, rest2), FH.has_code(cf, rest),
            FH.fgroup_add_has_other(w, fb, rest,
              SolveFast.next_fgroup_hit(fb, rest), cf, {==}, hfb, hr, ec_sym)),
          hnf)
      +wf2 : {FH.fgroups_wf(SolveFast.FGroup{f, len, rws} <> rest2)
              == True{} : Bool} =
        FH.bool_and_intro(FF5.FF5.is_fb5(f),
          Bool.and(Nat.is_le(1n, len),
            Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
              Bool.and(Bool.not(FH.has_code(cf, rest2)),
                FH.fgroups_wf(rest2)))),
          hf5,
          FH.bool_and_intro(Nat.is_le(1n, len),
            Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
              Bool.and(Bool.not(FH.has_code(cf, rest2)),
                FH.fgroups_wf(rest2))),
            hlen,
            FH.bool_and_intro(Nat.is_eq(len, Groups.len_words(rws)),
              Bool.and(Bool.not(FH.has_code(cf, rest2)),
                FH.fgroups_wf(rest2)),
              heql,
              FH.bool_and_intro(Bool.not(FH.has_code(cf, rest2)),
                FH.fgroups_wf(rest2), hnf2, wf_r))))
      +tot2 : {Nat.add(len, FH.fgroups_total(rest2))
               == Nat.add(1n, Nat.add(len, FH.fgroups_total(rest))) : Nat} =
        Equal.trans(Nat,
          Nat.add(len, FH.fgroups_total(rest2)),
          Nat.add(len, Nat.add(1n, FH.fgroups_total(rest))),
          Nat.add(1n, Nat.add(len, FH.fgroups_total(rest))),
          Equal.cong(Nat, Nat, x => Nat.add(len, x),
            FH.fgroups_total(rest2),
            Nat.add(1n, FH.fgroups_total(rest)), tot_r),
          NatProof.NatPrf.add_succ(len, FH.fgroups_total(rest)))
      +ehas : {Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest))
               == FH.has_code(c, rest) : Bool} =
        Equal.cong(Bool, Bool,
          b => Bool.or(b, FH.has_code(c, rest)),
          U32.is_eq(c, cf), False{}, ec)
      +cnt2 : {Nat.add(1n, FH.fgroups_count(rest2))
               == Feedback.Bool.case(Nat,
                    Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest)),
                    Nat.add(1n, FH.fgroups_count(rest)),
                    Nat.add(1n, Nat.add(1n, FH.fgroups_count(rest)))) : Nat} =
        Equal.trans(Nat,
          Nat.add(1n, FH.fgroups_count(rest2)),
          Nat.add(1n,
            Feedback.Bool.case(Nat, FH.has_code(c, rest),
              FH.fgroups_count(rest),
              Nat.add(1n, FH.fgroups_count(rest)))),
          Feedback.Bool.case(Nat,
            Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest)),
            Nat.add(1n, FH.fgroups_count(rest)),
            Nat.add(1n, Nat.add(1n, FH.fgroups_count(rest)))),
          Equal.cong(Nat, Nat, x => Nat.add(1n, x),
            FH.fgroups_count(rest2),
            Feedback.Bool.case(Nat, FH.has_code(c, rest),
              FH.fgroups_count(rest),
              Nat.add(1n, FH.fgroups_count(rest))), cnt_r),
          Equal.trans(Nat,
            Nat.add(1n,
              Feedback.Bool.case(Nat, FH.has_code(c, rest),
                FH.fgroups_count(rest),
                Nat.add(1n, FH.fgroups_count(rest)))),
            Feedback.Bool.case(Nat, FH.has_code(c, rest),
              Nat.add(1n, FH.fgroups_count(rest)),
              Nat.add(1n, Nat.add(1n, FH.fgroups_count(rest)))),
            Feedback.Bool.case(Nat,
              Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest)),
              Nat.add(1n, FH.fgroups_count(rest)),
              Nat.add(1n, Nat.add(1n, FH.fgroups_count(rest)))),
            FH.succ_bool_case(FH.has_code(c, rest),
              FH.fgroups_count(rest),
              Nat.add(1n, FH.fgroups_count(rest))),
            Equal.cong(Bool, Nat,
              b => Feedback.Bool.case(Nat, b,
                     Nat.add(1n, FH.fgroups_count(rest)),
                     Nat.add(1n, Nat.add(1n, FH.fgroups_count(rest)))),
              FH.has_code(c, rest),
              Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest)),
              Equal.sym(Bool,
                Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest)),
                FH.has_code(c, rest), ehas))))
      +has2 : {Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest2))
               == True{} : Bool} =
        Equal.trans(Bool,
          Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest2)),
          FH.has_code(c, rest2),
          True{},
          Equal.cong(Bool, Bool,
            b => Bool.or(b, FH.has_code(c, rest2)),
            U32.is_eq(c, cf), False{}, ec),
          has_r)
      +lkp2 : {Feedback.Bool.case(+List<+List<Nat>>, U32.is_eq(c, cf),
                 rws, FH.lookup_code(c, rest2))
               == w <> Feedback.Bool.case(+List<+List<Nat>>,
                         U32.is_eq(c, cf),
                         rws, FH.lookup_code(c, rest)) : +List<+List<Nat>>} =
        Equal.trans(+List<+List<Nat>>,
          Feedback.Bool.case(+List<+List<Nat>>, U32.is_eq(c, cf),
            rws, FH.lookup_code(c, rest2)),
          FH.lookup_code(c, rest2),
          w <> Feedback.Bool.case(+List<+List<Nat>>, U32.is_eq(c, cf),
                 rws, FH.lookup_code(c, rest)),
          Equal.cong(Bool, +List<+List<Nat>>,
            b => Feedback.Bool.case(+List<+List<Nat>>, b,
                   rws, FH.lookup_code(c, rest2)),
            U32.is_eq(c, cf), False{}, ec),
          Equal.trans(+List<+List<Nat>>,
            FH.lookup_code(c, rest2),
            w <> FH.lookup_code(c, rest),
            w <> Feedback.Bool.case(+List<+List<Nat>>, U32.is_eq(c, cf),
                   rws, FH.lookup_code(c, rest)),
            lkp_r,
            Equal.cong(Bool, +List<+List<Nat>>,
              b => w <> Feedback.Bool.case(+List<+List<Nat>>, b,
                          rws, FH.lookup_code(c, rest)),
              False{}, U32.is_eq(c, cf),
              Equal.sym(Bool, U32.is_eq(c, cf), False{}, ec))))
      AddFacts{wf2, tot2, cnt2, has2, lkp2}

def FH.fgroup_add_facts(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +fg: +List<SolveFast.FGroup>, hit: Bool,
    +eh: {hit == SolveFast.next_fgroup_hit(fb, fg) : Bool},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool}) ->
  FH.AddFacts<w, fb, fg, SolveFast.fgroup_add_go(w, fb, fg, hit)>:
  match fg:
    case Nil{}:
      +c = FF5.FF5.encode_fb5_list(fb)
      +erefl : {U32.is_eq(c, c) == True{} : Bool} = Arr.Arr.u32_is_eq_refl(c)
      AddFacts{
        FH.bool_and_intro(FF5.FF5.is_fb5(fb), True{}, hfb, {==}),
        {==},
        {==},
        Equal.cong(Bool, Bool, b => Bool.or(b, False{}),
          U32.is_eq(c, c), True{}, erefl),
        Equal.cong(Bool, +List<+List<Nat>>,
          b => Feedback.Bool.case(+List<+List<Nat>>, b, w <> Nil{}, Nil{}),
          U32.is_eq(c, c), True{}, erefl)}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          match hit:
            case True{}:
              +c = FF5.FF5.encode_fb5_list(fb)
              +cf = FF5.FF5.encode_fb5_list(f)
              +hf5 = Logic.Proof.and_true_l(FF5.FF5.is_fb5(f),
                       Bool.and(Nat.is_le(1n, len),
                         Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                           Bool.and(Bool.not(FH.has_code(cf, rest)),
                             FH.fgroups_wf(rest)))), hwf)
              +h1 = Logic.Proof.and_true_r(FF5.FF5.is_fb5(f),
                      Bool.and(Nat.is_le(1n, len),
                        Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                          Bool.and(Bool.not(FH.has_code(cf, rest)),
                            FH.fgroups_wf(rest)))), hwf)
              +h2 = Logic.Proof.and_true_r(Nat.is_le(1n, len),
                      Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                        Bool.and(Bool.not(FH.has_code(cf, rest)),
                          FH.fgroups_wf(rest))), h1)
              +heql = Logic.Proof.and_true_l(Nat.is_eq(len, Groups.len_words(rws)),
                        Bool.and(Bool.not(FH.has_code(cf, rest)),
                          FH.fgroups_wf(rest)), h2)
              +h3 = Logic.Proof.and_true_r(Nat.is_eq(len, Groups.len_words(rws)),
                      Bool.and(Bool.not(FH.has_code(cf, rest)),
                        FH.fgroups_wf(rest)), h2)
              +ec : {U32.is_eq(c, cf) == True{} : Bool} =
                Equal.trans(Bool, U32.is_eq(c, cf), Feedback.feedback_eq(fb, f),
                  True{}, FF5.FF5.code_eq_iff_fb_eq(fb, f, hfb, hf5),
                  Equal.trans(Bool, Feedback.feedback_eq(fb, f),
                    SolveFast.feedback_eq_fast(fb, f), True{},
                    Equal.sym(Bool, SolveFast.feedback_eq_fast(fb, f),
                      Feedback.feedback_eq(fb, f),
                      FG.FG.feedback_eq_fast_eq(fb, f)),
                    Equal.sym(Bool, True{}, SolveFast.feedback_eq_fast(fb, f),
                      eh)))
              +has_t : {Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest))
                        == True{} : Bool} =
                Equal.cong(Bool, Bool, b => Bool.or(b, FH.has_code(c, rest)),
                  U32.is_eq(c, cf), True{}, ec)
              +wf2 : {FH.fgroups_wf(
                        SolveFast.FGroup{f, Nat.add(1n, len), w <> rws} <> rest)
                      == True{} : Bool} =
                FH.bool_and_intro(FF5.FF5.is_fb5(f),
                  Bool.and(Nat.is_le(1n, Nat.add(1n, len)),
                    Bool.and(
                      Nat.is_eq(Nat.add(1n, len),
                        Nat.add(1n, Groups.len_words(rws))),
                      Bool.and(Bool.not(FH.has_code(cf, rest)),
                        FH.fgroups_wf(rest)))),
                  hf5,
                  FH.bool_and_intro(Nat.is_le(1n, Nat.add(1n, len)),
                    Bool.and(
                      Nat.is_eq(Nat.add(1n, len),
                        Nat.add(1n, Groups.len_words(rws))),
                      Bool.and(Bool.not(FH.has_code(cf, rest)),
                        FH.fgroups_wf(rest))),
                    NatProof.Nat.is_le_zero_l(len),
                    FH.bool_and_intro(
                      Nat.is_eq(Nat.add(1n, len),
                        Nat.add(1n, Groups.len_words(rws))),
                      Bool.and(Bool.not(FH.has_code(cf, rest)),
                        FH.fgroups_wf(rest)),
                      heql, h3)))
              AddFacts{
                wf2,
                {==},
                Equal.sym(Nat,
                  Feedback.Bool.case(Nat,
                    Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest)),
                    Nat.add(1n, FH.fgroups_count(rest)),
                    Nat.add(1n, Nat.add(1n, FH.fgroups_count(rest)))),
                  Nat.add(1n, FH.fgroups_count(rest)),
                  Equal.cong(Bool, Nat,
                    b => Feedback.Bool.case(Nat, b,
                           Nat.add(1n, FH.fgroups_count(rest)),
                           Nat.add(1n, Nat.add(1n, FH.fgroups_count(rest)))),
                    Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest)), True{},
                    has_t)),
                has_t,
                Equal.trans(+List<+List<Nat>>,
                  Feedback.Bool.case(+List<+List<Nat>>, U32.is_eq(c, cf),
                    w <> rws, FH.lookup_code(c, rest)),
                  w <> rws,
                  w <> Feedback.Bool.case(+List<+List<Nat>>, U32.is_eq(c, cf),
                         rws, FH.lookup_code(c, rest)),
                  Equal.cong(Bool, +List<+List<Nat>>,
                    b => Feedback.Bool.case(+List<+List<Nat>>, b,
                           w <> rws, FH.lookup_code(c, rest)),
                    U32.is_eq(c, cf), True{}, ec),
                  Equal.cong(Bool, +List<+List<Nat>>,
                    b => w <> Feedback.Bool.case(+List<+List<Nat>>, b,
                                rws, FH.lookup_code(c, rest)),
                    True{}, U32.is_eq(c, cf),
                    Equal.sym(Bool, U32.is_eq(c, cf), True{}, ec)))}
            case False{}:
              +c = FF5.FF5.encode_fb5_list(fb)
              +cf = FF5.FF5.encode_fb5_list(f)
              +hf5 = Logic.Proof.and_true_l(FF5.FF5.is_fb5(f),
                       Bool.and(Nat.is_le(1n, len),
                         Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                           Bool.and(Bool.not(FH.has_code(cf, rest)),
                             FH.fgroups_wf(rest)))), hwf)
              +h1 = Logic.Proof.and_true_r(FF5.FF5.is_fb5(f),
                      Bool.and(Nat.is_le(1n, len),
                        Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                          Bool.and(Bool.not(FH.has_code(cf, rest)),
                            FH.fgroups_wf(rest)))), hwf)
              +hlen = Logic.Proof.and_true_l(Nat.is_le(1n, len),
                        Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                          Bool.and(Bool.not(FH.has_code(cf, rest)),
                            FH.fgroups_wf(rest))), h1)
              +h2 = Logic.Proof.and_true_r(Nat.is_le(1n, len),
                      Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                        Bool.and(Bool.not(FH.has_code(cf, rest)),
                          FH.fgroups_wf(rest))), h1)
              +heql = Logic.Proof.and_true_l(Nat.is_eq(len, Groups.len_words(rws)),
                        Bool.and(Bool.not(FH.has_code(cf, rest)),
                          FH.fgroups_wf(rest)), h2)
              +h3 = Logic.Proof.and_true_r(Nat.is_eq(len, Groups.len_words(rws)),
                      Bool.and(Bool.not(FH.has_code(cf, rest)),
                        FH.fgroups_wf(rest)), h2)
              +hnf = Logic.Proof.and_true_l(Bool.not(FH.has_code(cf, rest)),
                       FH.fgroups_wf(rest), h3)
              +hr = Logic.Proof.and_true_r(Bool.not(FH.has_code(cf, rest)),
                      FH.fgroups_wf(rest), h3)
              +ec : {U32.is_eq(c, cf) == False{} : Bool} =
                Equal.trans(Bool, U32.is_eq(c, cf), Feedback.feedback_eq(fb, f),
                  False{}, FF5.FF5.code_eq_iff_fb_eq(fb, f, hfb, hf5),
                  Equal.trans(Bool, Feedback.feedback_eq(fb, f),
                    SolveFast.feedback_eq_fast(fb, f), False{},
                    Equal.sym(Bool, SolveFast.feedback_eq_fast(fb, f),
                      Feedback.feedback_eq(fb, f),
                      FG.FG.feedback_eq_fast_eq(fb, f)),
                    Equal.sym(Bool, False{}, SolveFast.feedback_eq_fast(fb, f),
                      eh)))
              FH.add_facts_false_step(w, fb, f, len, rws, rest,
                hfb, hf5, hlen, heql, hnf, hr, ec,
                FH.fgroup_add_facts(w, fb, rest,
                  SolveFast.next_fgroup_hit(fb, rest), {==}, hfb, hr))

# `rev_codes` evolution under `fgroup_add_go`, plus `all_len5` predicate.
def FH.fgroup_add_rev_codes(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +fg: +List<SolveFast.FGroup>, +acc: +List<U32>, hit: Bool,
    +eh: {hit == SolveFast.next_fgroup_hit(fb, fg) : Bool},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool}) ->
  {FH.rev_codes(SolveFast.fgroup_add_go(w, fb, fg, hit), acc)
   == Feedback.Bool.case(+List<U32>,
        FH.has_code(FF5.FF5.encode_fb5_list(fb), fg),
        FH.rev_codes(fg, acc),
        FF5.FF5.encode_fb5_list(fb) <> FH.rev_codes(fg, acc)) : +List<U32>}:
  match fg:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          match hit:
            case True{}:
              +c = FF5.FF5.encode_fb5_list(fb)
              +cf = FF5.FF5.encode_fb5_list(f)
              +hf5 = Logic.Proof.and_true_l(FF5.FF5.is_fb5(f),
                       Bool.and(Nat.is_le(1n, len),
                         Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                           Bool.and(Bool.not(FH.has_code(cf, rest)),
                             FH.fgroups_wf(rest)))), hwf)
              +ec : {U32.is_eq(c, cf) == True{} : Bool} =
                Equal.trans(Bool, U32.is_eq(c, cf), Feedback.feedback_eq(fb, f),
                  True{}, FF5.FF5.code_eq_iff_fb_eq(fb, f, hfb, hf5),
                  Equal.trans(Bool, Feedback.feedback_eq(fb, f),
                    SolveFast.feedback_eq_fast(fb, f), True{},
                    Equal.sym(Bool, SolveFast.feedback_eq_fast(fb, f),
                      Feedback.feedback_eq(fb, f),
                      FG.FG.feedback_eq_fast_eq(fb, f)),
                    Equal.sym(Bool, True{}, SolveFast.feedback_eq_fast(fb, f),
                      eh)))
              +has_t : {Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest))
                        == True{} : Bool} =
                Equal.cong(Bool, Bool, b => Bool.or(b, FH.has_code(c, rest)),
                  U32.is_eq(c, cf), True{}, ec)
              Equal.sym(+List<U32>,
                Feedback.Bool.case(+List<U32>,
                  Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest)),
                  FH.rev_codes(rest, cf <> acc),
                  c <> FH.rev_codes(rest, cf <> acc)),
                FH.rev_codes(rest, cf <> acc),
                Equal.cong(Bool, +List<U32>,
                  b => Feedback.Bool.case(+List<U32>, b,
                         FH.rev_codes(rest, cf <> acc),
                         c <> FH.rev_codes(rest, cf <> acc)),
                  Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest)), True{},
                  has_t))
            case False{}:
              +c = FF5.FF5.encode_fb5_list(fb)
              +cf = FF5.FF5.encode_fb5_list(f)
              +hf5 = Logic.Proof.and_true_l(FF5.FF5.is_fb5(f),
                       Bool.and(Nat.is_le(1n, len),
                         Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                           Bool.and(Bool.not(FH.has_code(cf, rest)),
                             FH.fgroups_wf(rest)))), hwf)
              +h1 = Logic.Proof.and_true_r(FF5.FF5.is_fb5(f),
                      Bool.and(Nat.is_le(1n, len),
                        Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                          Bool.and(Bool.not(FH.has_code(cf, rest)),
                            FH.fgroups_wf(rest)))), hwf)
              +h2 = Logic.Proof.and_true_r(Nat.is_le(1n, len),
                      Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                        Bool.and(Bool.not(FH.has_code(cf, rest)),
                          FH.fgroups_wf(rest))), h1)
              +h3 = Logic.Proof.and_true_r(Nat.is_eq(len, Groups.len_words(rws)),
                      Bool.and(Bool.not(FH.has_code(cf, rest)),
                        FH.fgroups_wf(rest)), h2)
              +hr = Logic.Proof.and_true_r(Bool.not(FH.has_code(cf, rest)),
                      FH.fgroups_wf(rest), h3)
              +ec : {U32.is_eq(c, cf) == False{} : Bool} =
                Equal.trans(Bool, U32.is_eq(c, cf), Feedback.feedback_eq(fb, f),
                  False{}, FF5.FF5.code_eq_iff_fb_eq(fb, f, hfb, hf5),
                  Equal.trans(Bool, Feedback.feedback_eq(fb, f),
                    SolveFast.feedback_eq_fast(fb, f), False{},
                    Equal.sym(Bool, SolveFast.feedback_eq_fast(fb, f),
                      Feedback.feedback_eq(fb, f),
                      FG.FG.feedback_eq_fast_eq(fb, f)),
                    Equal.sym(Bool, False{}, SolveFast.feedback_eq_fast(fb, f),
                      eh)))
              +ehas : {Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest))
                       == FH.has_code(c, rest) : Bool} =
                Equal.cong(Bool, Bool,
                  b => Bool.or(b, FH.has_code(c, rest)),
                  U32.is_eq(c, cf), False{}, ec)
              Equal.trans(+List<U32>,
                FH.rev_codes(
                  SolveFast.fgroup_add_go(w, fb, rest,
                    SolveFast.next_fgroup_hit(fb, rest)), cf <> acc),
                Feedback.Bool.case(+List<U32>, FH.has_code(c, rest),
                  FH.rev_codes(rest, cf <> acc),
                  c <> FH.rev_codes(rest, cf <> acc)),
                Feedback.Bool.case(+List<U32>,
                  Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest)),
                  FH.rev_codes(rest, cf <> acc),
                  c <> FH.rev_codes(rest, cf <> acc)),
                FH.fgroup_add_rev_codes(w, fb, rest, cf <> acc,
                  SolveFast.next_fgroup_hit(fb, rest), {==}, hfb, hr),
                Equal.cong(Bool, +List<U32>,
                  b => Feedback.Bool.case(+List<U32>, b,
                         FH.rev_codes(rest, cf <> acc),
                         c <> FH.rev_codes(rest, cf <> acc)),
                  FH.has_code(c, rest),
                  Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest)),
                  Equal.sym(Bool,
                    Bool.or(U32.is_eq(c, cf), FH.has_code(c, rest)),
                    FH.has_code(c, rest), ehas)))

def FH.is_word5(+w: +List<Nat>) -> Bool:
  match w:
    case Nil{}:
      False{}
    case Con{a0, t1}:
      match t1:
        case Nil{}:
          False{}
        case Con{a1, t2}:
          match t2:
            case Nil{}:
              False{}
            case Con{a2, t3}:
              match t3:
                case Nil{}:
                  False{}
                case Con{a3, t4}:
                  match t4:
                    case Nil{}:
                      False{}
                    case Con{a4, t5}:
                      match t5:
                        case Nil{}:
                          True{}
                        case Con{a5, t6}:
                          False{}

def FH.all_len5(+S: +List<+List<Nat>>) -> Bool:
  match S:
    case Nil{}:
      True{}
    case Con{w, rest}:
      Bool.and(FH.is_word5(w), FH.all_len5(rest))

# ---------------------------------------------------------------------------
# Low-bit-zero predicate `u32_zero_below` for base indices in tree invariants
# ---------------------------------------------------------------------------

def FH.word_zero_below(d: Nat, m: Nat, +w: Word(m)) -> Bool:
  match d:
    case 0n:
      True{}
    case 1n++dp:
      match m:
        case 0n:
          True{}
        case 1n++mp:
          match w:
            case WCon{b, t}:
              Bool.and(Bool.not(b), FH.word_zero_below(dp, mp, t))

def FH.u32_zero_below(+d: Nat, +u: U32) -> Bool:
  match u:
    case U32{w}:
      FH.word_zero_below(d, 32n, w)

def FH.word_zero_below_pred(+p: Nat, +m: Nat, +w: Word(m),
    +hz: {FH.word_zero_below(1n+p, m, w) == True{} : Bool}) ->
  {FH.word_zero_below(p, m, w) == True{} : Bool}:
  match p m:
    case 0n _:
      {==}
    case _ 0n:
      {==}
    case 1n++pp 1n++mp:
      match w:
        case WCon{+b, +t}:
          FH.bool_and_intro(Bool.not(b), FH.word_zero_below(pp, mp, t),
            Logic.Proof.and_true_l(Bool.not(b),
              FH.word_zero_below(1n+pp, mp, t), hz),
            FH.word_zero_below_pred(pp, mp, t,
              Logic.Proof.and_true_r(Bool.not(b),
                FH.word_zero_below(1n+pp, mp, t), hz)))

def FH.u32_zero_below_pred(+p: Nat, +u: U32,
    +hz: {FH.u32_zero_below(1n+p, u) == True{} : Bool}) ->
  {FH.u32_zero_below(p, u) == True{} : Bool}:
  match u:
    case U32{+w}:
      FH.word_zero_below_pred(p, 32n, w, hz)

def FH.word_bit_of_zero_below(+p: Nat, +m: Nat, +w: Word(m),
    +hz: {FH.word_zero_below(1n+p, m, w) == True{} : Bool}) ->
  {Arr.Arr.word_bit(p, m, w) == False{} : Bool}:
  match p m:
    case _ 0n:
      {==}
    case 0n 1n++mp:
      match w:
        case WCon{+b, +t}:
          Arr.Arr.bool_not_true(b,
            Logic.Proof.and_true_l(Bool.not(b),
              FH.word_zero_below(0n, mp, t), hz))
    case 1n++pp 1n++mp:
      match w:
        case WCon{+b, +t}:
          FH.word_bit_of_zero_below(pp, mp, t,
            Logic.Proof.and_true_r(Bool.not(b),
              FH.word_zero_below(1n+pp, mp, t), hz))

def FH.u32_bit_of_zero_below(+p: Nat, +u: U32,
    +hz: {FH.u32_zero_below(1n+p, u) == True{} : Bool}) ->
  {FH.u32_bit(p, u) == False{} : Bool}:
  match u:
    case U32{+w}:
      FH.word_bit_of_zero_below(p, 32n, w, hz)

def FH.word_zero_below_or_pow2(+p: Nat, +m: Nat, +w: Word(m),
    +hz: {FH.word_zero_below(p, m, w) == True{} : Bool}) ->
  {FH.word_zero_below(p, m, Word.or(m, w, Arr.Arr.pow2_word(p, m)))
   == True{} : Bool}:
  match p m:
    case 0n _:
      {==}
    case _ 0n:
      {==}
    case 1n++pp 1n++mp:
      match w:
        case WCon{+b, +t}:
          +hb : {Bool.not(b) == True{} : Bool} =
            Logic.Proof.and_true_l(Bool.not(b),
              FH.word_zero_below(pp, mp, t), hz)
          +ht : {FH.word_zero_below(pp, mp, t) == True{} : Bool} =
            Logic.Proof.and_true_r(Bool.not(b),
              FH.word_zero_below(pp, mp, t), hz)
          +hb2 : {Bool.not(Bool.or(b, False{})) == True{} : Bool} =
            Equal.trans(Bool, Bool.not(Bool.or(b, False{})), Bool.not(b),
              True{},
              Equal.cong(Bool, Bool, Bool.not, Bool.or(b, False{}), b,
                FF5.FF5.bool_or_false_r(b)), hb)
          FH.bool_and_intro(Bool.not(Bool.or(b, False{})),
            FH.word_zero_below(pp, mp, Word.or(mp, t, Arr.Arr.pow2_word(pp, mp))),
            hb2, FH.word_zero_below_or_pow2(pp, mp, t, ht))

def FH.u32_zero_below_or_pow2(+p: Nat, +u: U32,
    +hz: {FH.u32_zero_below(p, u) == True{} : Bool}) ->
  {FH.u32_zero_below(p, U32.or(u, Arr.Arr.pow2_u32(p))) == True{} : Bool}:
  match u:
    case U32{+w}:
      FH.word_zero_below_or_pow2(p, 32n, w, hz)

# ---------------------------------------------------------------------------
# Symbolic depth-indexed invariant `FH.SeenTree` for `seen: Array<Nat>`
# ---------------------------------------------------------------------------

def FH.seen_ok(+fg: +List<SolveFast.FGroup>, +gen: Nat, +c: U32,
               +v: Nat) -> Bool:
  Feedback.Bool.case(Bool, FH.has_code(c, fg),
    Nat.is_eq(v, gen),
    Nat.is_lt(v, gen))

def FH.SeenTree(+d: Nat, +base: U32, a: Array<Nat>, +gen: Nat,
                +fg: +List<SolveFast.FGroup>) -> Data:
  match d:
    case 0n:
      match a:
        case ALeaf{v}:
          {FH.seen_ok(fg, gen, base, v) == True{} : Bool}
        case ANode{xs, ys}:
          Empty
    case 1n++p:
      match a:
        case ALeaf{v}:
          Empty
        case ANode{xs, ys}:
          Arr.Arr.DPair<
            FH.SeenTree(p, base, xs, gen, fg),
            FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, gen, fg)>

def FH.seen_tree_transport(+d: Nat, +base: U32, -a1: Array<Nat>, -a2: Array<Nat>,
    +gen: Nat, +fg: +List<SolveFast.FGroup>, +ea: {a1 == a2 : Array<Nat>},
    +hs: FH.SeenTree(d, base, a1, gen, fg)) ->
  FH.SeenTree(d, base, a2, gen, fg):
  %ea : FH.SeenTree(d, base, _, gen, fg)
  hs

def FH.seen_tree_transport_fg(+d: Nat, +base: U32, -a: Array<Nat>, +gen: Nat,
    +fg1: +List<SolveFast.FGroup>, +fg2: +List<SolveFast.FGroup>,
    +efg: {fg1 == fg2 : +List<SolveFast.FGroup>},
    +hs: FH.SeenTree(d, base, a, gen, fg1)) ->
  FH.SeenTree(d, base, a, gen, fg2):
  %efg : FH.SeenTree(d, base, a, gen, _)
  hs

def FH.seen_tree_depth(+d: Nat, +base: U32, a: Array<Nat>, +gen: Nat,
    +fg: +List<SolveFast.FGroup>, +hs: FH.SeenTree(d, base, a, gen, fg)) ->
  Arr.Arr.Depth(Nat, d, a):
  match d:
    case 0n:
      match a:
        case ALeaf{v}:
          Unit{}
        case ANode{xs, ys}:
          hs
    case 1n++p:
      match a:
        case ALeaf{v}:
          hs
        case ANode{xs, ys}:
          +hxs = Arr.Arr.dpair_l(
                   FH.SeenTree(p, base, xs, gen, fg),
                   FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, gen, fg),
                   hs)
          +hys = Arr.Arr.dpair_r(
                   FH.SeenTree(p, base, xs, gen, fg),
                   FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, gen, fg),
                   hs)
          Arr.DPair{
            FH.seen_tree_depth(p, base, xs, gen, fg, hxs),
            FH.seen_tree_depth(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, gen,
              fg, hys)}

def FH.seen_tree_new(+d: Nat, +base: U32) ->
  FH.SeenTree(d, base, Array.new(Nat, d, 0n), 1n, Nil{}):
  match d:
    case 0n:
      {==}
    case 1n++p:
      Arr.DPair{
        FH.seen_tree_new(p, base),
        FH.seen_tree_new(p, U32.or(base, Arr.Arr.pow2_u32(p)))}

def FH.seen_ok_bump_go(+gen: Nat, +v: Nat, b: Bool,
    +h: {Feedback.Bool.case(Bool, b, Nat.is_eq(v, gen), Nat.is_lt(v, gen))
         == True{} : Bool}) ->
  {Nat.is_lt(v, Nat.add(1n, gen)) == True{} : Bool}:
  match b:
    case True{}:
      +ev : {v == gen : Nat} = NatProof.NatPrf.is_eq_true(v, gen, h)
      Equal.trans(Bool, Nat.is_lt(v, 1n+gen), Nat.is_lt(gen, 1n+gen), True{},
        Equal.cong(Nat, Bool, x => Nat.is_lt(x, 1n+gen), v, gen, ev),
        NatProof.Nat.is_lt_succ_self(gen))
    case False{}:
      NatProof.Nat.is_lt_le_trans(v, gen, 1n+gen, h,
        NatProof.Nat.is_le_of_lt(gen, 1n+gen, NatProof.Nat.is_lt_succ_self(gen)))

def FH.seen_tree_bump(+d: Nat, +base: U32, a: Array<Nat>, +gen: Nat,
    +fg: +List<SolveFast.FGroup>, +hs: FH.SeenTree(d, base, a, gen, fg)) ->
  FH.SeenTree(d, base, a, Nat.add(1n, gen), Nil{}):
  match d:
    case 0n:
      match a:
        case ALeaf{+v}:
          FH.seen_ok_bump_go(gen, v, FH.has_code(base, fg), hs)
        case ANode{xs, ys}:
          hs
    case 1n++p:
      match a:
        case ALeaf{v}:
          hs
        case ANode{xs, ys}:
          +hxs = Arr.Arr.dpair_l(
                   FH.SeenTree(p, base, xs, gen, fg),
                   FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, gen, fg),
                   hs)
          +hys = Arr.Arr.dpair_r(
                   FH.SeenTree(p, base, xs, gen, fg),
                   FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, gen, fg),
                   hs)
          Arr.DPair{
            FH.seen_tree_bump(p, base, xs, gen, fg, hxs),
            FH.seen_tree_bump(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, gen,
              fg, hys)}

# Reading `seen` at `code` gives `FH.seen_ok(fg, gen, code, old) == True{}`.
def FH.seen_get_lo(-ys: Array<Nat>, r: Array<Nat> & Nat,
    +fg: +List<SolveFast.FGroup>, +gen: Nat, +c: U32,
    +hr: {FH.seen_ok(fg, gen, c, Arr.Arr.snd(Array<Nat>, Nat, r))
          == True{} : Bool}) ->
  {FH.seen_ok(fg, gen, c,
     Arr.Arr.snd(Array<Nat>, Nat, Array.swap.lo(Nat, ys, r))) == True{} : Bool}:
  (a, +v) = r
  hr

def FH.seen_get_hi(-xs: Array<Nat>, r: Array<Nat> & Nat,
    +fg: +List<SolveFast.FGroup>, +gen: Nat, +c: U32,
    +hr: {FH.seen_ok(fg, gen, c, Arr.Arr.snd(Array<Nat>, Nat, r))
          == True{} : Bool}) ->
  {FH.seen_ok(fg, gen, c,
     Arr.Arr.snd(Array<Nat>, Nat, Array.swap.hi(Nat, xs, r))) == True{} : Bool}:
  (a, +v) = r
  hr

def FH.seen_tree_get_go_lo(+p: Nat, +base: U32, -xs: Array<Nat>,
    -ys: Array<Nat>, +gen: Nat, +fg: +List<SolveFast.FGroup>, +i: U32,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +hxs: FH.SeenTree(p, base, xs, gen, fg),
    d: &a1: Array<Nat> -> &a2: Array<Nat> ->
       {a1 == xs : Array<Nat>} & {a2 == a1 : Array<Nat>},
    ih: @xs2: Array<Nat> -> FH.SeenTree(p, base, xs2, gen, fg) ->
        {FH.seen_ok(fg, gen, U32.or(base, i),
           Arr.Arr.snd(Array<Nat>, Nat,
             Array.get.go(Nat, xs2, Arr.Arr.pow2_u32(p), i,
               U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))))) == True{} : Bool}) ->
  {FH.seen_ok(fg, gen, U32.or(base, i),
     Arr.Arr.snd(Array<Nat>, Nat,
       Array.get.go(Nat, ANode{xs, ys}, Arr.Arr.pow2_u32(1n+p), i, True{})))
   == True{} : Bool}:
  (xs1, d2) = d
  (xs2, pe) = d2
  (+ex1, +ex2) = pe
  +hxs2 = FH.seen_tree_transport(p, base, xs, xs2, gen, fg,
            Equal.sym(Array<Nat>, xs2, xs,
              Equal.trans(Array<Nat>, xs2, xs1, xs, ex2, ex1)), hxs)
  +h2 = ih(xs2, hxs2)
  +h1 : {FH.seen_ok(fg, gen, U32.or(base, i),
           Arr.Arr.snd(Array<Nat>, Nat,
             Array.get.go(Nat, xs1, Arr.Arr.pow2_u32(p), i,
               U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))))) == True{} : Bool} =
    Equal.trans(Bool,
      FH.seen_ok(fg, gen, U32.or(base, i),
        Arr.Arr.snd(Array<Nat>, Nat,
          Array.get.go(Nat, xs1, Arr.Arr.pow2_u32(p), i,
            U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))))),
      FH.seen_ok(fg, gen, U32.or(base, i),
        Arr.Arr.snd(Array<Nat>, Nat,
          Array.get.go(Nat, xs2, Arr.Arr.pow2_u32(p), i,
            U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))))),
      True{},
      Equal.cong(Array<Nat>, Bool,
        x => FH.seen_ok(fg, gen, U32.or(base, i),
               Arr.Arr.snd(Array<Nat>, Nat,
                 Array.get.go(Nat, x, Arr.Arr.pow2_u32(p), i,
                   U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))))),
        xs1, xs2, Equal.sym(Array<Nat>, xs2, xs1, ex2)),
      h2)
  %ex1 : {FH.seen_ok(fg, gen, U32.or(base, i),
            Arr.Arr.snd(Array<Nat>, Nat,
              Array.get.go(Nat, ANode{_, ys}, Arr.Arr.pow2_u32(1n+p), i, True{})))
          == True{} : Bool}
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    {FH.seen_ok(fg, gen, U32.or(base, i),
       Arr.Arr.snd(Array<Nat>, Nat,
         Array.swap.lo(Nat, ys,
           Array.get.go(Nat, xs1, _, i, U32.is_lt(i, U32.shr(_))))))
     == True{} : Bool}
  FH.seen_get_lo(ys,
    Array.get.go(Nat, xs1, Arr.Arr.pow2_u32(p), i,
      U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))),
    fg, gen, U32.or(base, i), h1)

def FH.seen_tree_get_go_hi(+p: Nat, +base: U32, -xs: Array<Nat>,
    -ys: Array<Nat>, +gen: Nat, +fg: +List<SolveFast.FGroup>, +i: U32,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +eb2: {U32.or(U32.or(base, Arr.Arr.pow2_u32(p)),
                  U32.sub(i, Arr.Arr.pow2_u32(p))) == U32.or(base, i) : U32},
    +hys: FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, gen, fg),
    d: &a1: Array<Nat> -> &a2: Array<Nat> ->
       {a1 == ys : Array<Nat>} & {a2 == a1 : Array<Nat>},
    ih: @ys2: Array<Nat> ->
        FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys2, gen, fg) ->
        {FH.seen_ok(fg, gen,
           U32.or(U32.or(base, Arr.Arr.pow2_u32(p)),
                  U32.sub(i, Arr.Arr.pow2_u32(p))),
           Arr.Arr.snd(Array<Nat>, Nat,
             Array.get.go(Nat, ys2, Arr.Arr.pow2_u32(p),
               U32.sub(i, Arr.Arr.pow2_u32(p)),
               U32.is_lt(U32.sub(i, Arr.Arr.pow2_u32(p)),
                 U32.shr(Arr.Arr.pow2_u32(p)))))) == True{} : Bool}) ->
  {FH.seen_ok(fg, gen, U32.or(base, i),
     Arr.Arr.snd(Array<Nat>, Nat,
       Array.get.go(Nat, ANode{xs, ys}, Arr.Arr.pow2_u32(1n+p), i, False{})))
   == True{} : Bool}:
  (ys1, d2) = d
  (ys2, pe) = d2
  (+ey1, +ey2) = pe
  +base2 = U32.or(base, Arr.Arr.pow2_u32(p))
  +ip = U32.sub(i, Arr.Arr.pow2_u32(p))
  +hys2 = FH.seen_tree_transport(p, base2, ys, ys2, gen, fg,
            Equal.sym(Array<Nat>, ys2, ys,
              Equal.trans(Array<Nat>, ys2, ys1, ys, ey2, ey1)), hys)
  +h2 = ih(ys2, hys2)
  +h1 : {FH.seen_ok(fg, gen, U32.or(base, i),
           Arr.Arr.snd(Array<Nat>, Nat,
             Array.get.go(Nat, ys1, Arr.Arr.pow2_u32(p), ip,
               U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))))) == True{} : Bool} =
    Equal.trans(Bool,
      FH.seen_ok(fg, gen, U32.or(base, i),
        Arr.Arr.snd(Array<Nat>, Nat,
          Array.get.go(Nat, ys1, Arr.Arr.pow2_u32(p), ip,
            U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))))),
      FH.seen_ok(fg, gen, U32.or(base2, ip),
        Arr.Arr.snd(Array<Nat>, Nat,
          Array.get.go(Nat, ys2, Arr.Arr.pow2_u32(p), ip,
            U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))))),
      True{},
      Equal.trans(Bool,
        FH.seen_ok(fg, gen, U32.or(base, i),
          Arr.Arr.snd(Array<Nat>, Nat,
            Array.get.go(Nat, ys1, Arr.Arr.pow2_u32(p), ip,
              U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))))),
        FH.seen_ok(fg, gen, U32.or(base2, ip),
          Arr.Arr.snd(Array<Nat>, Nat,
            Array.get.go(Nat, ys1, Arr.Arr.pow2_u32(p), ip,
              U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))))),
        FH.seen_ok(fg, gen, U32.or(base2, ip),
          Arr.Arr.snd(Array<Nat>, Nat,
            Array.get.go(Nat, ys2, Arr.Arr.pow2_u32(p), ip,
              U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))))),
        Equal.cong(U32, Bool,
          c => FH.seen_ok(fg, gen, c,
                 Arr.Arr.snd(Array<Nat>, Nat,
                   Array.get.go(Nat, ys1, Arr.Arr.pow2_u32(p), ip,
                     U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))))),
          U32.or(base, i), U32.or(base2, ip),
          Equal.sym(U32, U32.or(base2, ip), U32.or(base, i), eb2)),
        Equal.cong(Array<Nat>, Bool,
          y => FH.seen_ok(fg, gen, U32.or(base2, ip),
                 Arr.Arr.snd(Array<Nat>, Nat,
                   Array.get.go(Nat, y, Arr.Arr.pow2_u32(p), ip,
                     U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))))),
          ys1, ys2, Equal.sym(Array<Nat>, ys2, ys1, ey2))),
      h2)
  %ey1 : {FH.seen_ok(fg, gen, U32.or(base, i),
            Arr.Arr.snd(Array<Nat>, Nat,
              Array.get.go(Nat, ANode{xs, _}, Arr.Arr.pow2_u32(1n+p), i, False{})))
          == True{} : Bool}
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    {FH.seen_ok(fg, gen, U32.or(base, i),
       Arr.Arr.snd(Array<Nat>, Nat,
         Array.swap.hi(Nat, xs,
           Array.get.go(Nat, ys1, _, U32.sub(i, _),
             U32.is_lt(U32.sub(i, _), U32.shr(_)))))) == True{} : Bool}
  FH.seen_get_hi(xs,
    Array.get.go(Nat, ys1, Arr.Arr.pow2_u32(p), ip,
      U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))),
    fg, gen, U32.or(base, i), h1)

def FH.seen_tree_get_go(+d: Nat, +base: U32, a: Array<Nat>, +gen: Nat,
    +fg: +List<SolveFast.FGroup>, +i: U32, z: Bool,
    +ez: {z == U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(d))) : Bool},
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.Arr.u32_zero_from(d, i) == True{} : Bool},
    +hs: FH.SeenTree(d, base, a, gen, fg)) ->
  {FH.seen_ok(fg, gen, U32.or(base, i),
     Arr.Arr.snd(Array<Nat>, Nat,
       Array.get.go(Nat, a, Arr.Arr.pow2_u32(d), i, z))) == True{} : Bool}:
  match d:
    case 0n:
      match a:
        case ALeaf{+v}:
          +ei0 : {i == 0 : U32} = Arr.Arr.u32_eq_zero(i, zi)
          +eor : {U32.or(base, i) == base : U32} =
            Equal.trans(U32, U32.or(base, i), U32.or(base, 0), base,
              Equal.cong(U32, U32, x => U32.or(base, x), i, 0, ei0),
              FF5.FF5.u32_or_zero_r(base))
          Equal.trans(Bool,
            FH.seen_ok(fg, gen, U32.or(base, i), v),
            FH.seen_ok(fg, gen, base, v),
            True{},
            Equal.cong(U32, Bool, c => FH.seen_ok(fg, gen, c, v),
              U32.or(base, i), base, eor),
            hs)
        case ANode{xs, ys}:
          Empty.absurd(
            {FH.seen_ok(fg, gen, U32.or(base, i),
               Arr.Arr.snd(Array<Nat>, Nat,
                 Array.get.go(Nat, ANode{xs, ys}, Arr.Arr.pow2_u32(0n), i, z)))
             == True{} : Bool}, hs)
    case 1n++p:
      match a:
        case ALeaf{v}:
          Empty.absurd(
            {FH.seen_ok(fg, gen, U32.or(base, i),
               Arr.Arr.snd(Array<Nat>, Nat,
                 Array.get.go(Nat, ALeaf{v}, Arr.Arr.pow2_u32(1n+p), i, z)))
             == True{} : Bool}, hs)
        case ANode{xs, ys}:
          match z:
            case True{}:
              +hxs = Arr.Arr.dpair_l(
                       FH.SeenTree(p, base, xs, gen, fg),
                       FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys,
                         gen, fg), hs)
              +plt : {Nat.is_lt(p, 32n) == True{} : Bool} =
                NatProof.Nat.is_le_lt_trans(p, 1n+p, 32n,
                  NatProof.Nat.is_le_of_lt(p, 1n+p,
                    NatProof.Nat.is_lt_succ_self(p)), hlt)
              +eshr : {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p)
                       : U32} =
                Arr.Arr.u32_shr_pow2(p, hlt)
              +ilt : {U32.is_lt(i, Arr.Arr.pow2_u32(p)) == True{} : Bool} =
                Equal.trans(Bool,
                  U32.is_lt(i, Arr.Arr.pow2_u32(p)),
                  U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))),
                  True{},
                  Equal.cong(U32, Bool, x => U32.is_lt(i, x),
                    Arr.Arr.pow2_u32(p), U32.shr(Arr.Arr.pow2_u32(1n+p)),
                    Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)),
                      Arr.Arr.pow2_u32(p), eshr)),
                  Equal.sym(Bool, True{},
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))), ez))
              +zip : {Arr.Arr.u32_zero_from(p, i) == True{} : Bool} =
                Arr.Arr.u32_zero_from_lt(p, i, zi, plt, ilt)
              FH.seen_tree_get_go_lo(p, base, xs, ys, gen, fg, i, eshr, hxs,
                Arr.Arr.dup(Nat, xs),
                xs2 => hxs2 =>
                  FH.seen_tree_get_go(p, base, xs2, gen, fg, i,
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, hxs2))
            case False{}:
              +hys = Arr.Arr.dpair_r(
                       FH.SeenTree(p, base, xs, gen, fg),
                       FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys,
                         gen, fg), hs)
              +plt : {Nat.is_lt(p, 32n) == True{} : Bool} =
                NatProof.Nat.is_le_lt_trans(p, 1n+p, 32n,
                  NatProof.Nat.is_le_of_lt(p, 1n+p,
                    NatProof.Nat.is_lt_succ_self(p)), hlt)
              +eshr : {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p)
                       : U32} =
                Arr.Arr.u32_shr_pow2(p, hlt)
              +ige : {U32.is_lt(i, Arr.Arr.pow2_u32(p)) == False{} : Bool} =
                Equal.trans(Bool,
                  U32.is_lt(i, Arr.Arr.pow2_u32(p)),
                  U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))),
                  False{},
                  Equal.cong(U32, Bool, x => U32.is_lt(i, x),
                    Arr.Arr.pow2_u32(p), U32.shr(Arr.Arr.pow2_u32(1n+p)),
                    Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)),
                      Arr.Arr.pow2_u32(p), eshr)),
                  Equal.sym(Bool, False{},
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))), ez))
              +ip = U32.sub(i, Arr.Arr.pow2_u32(p))
              +zip : {Arr.Arr.u32_zero_from(p, ip) == True{} : Bool} =
                Arr.Arr.u32_zero_from_ge(p, i, zi, plt, ige)
              +eb2 : {U32.or(U32.or(base, Arr.Arr.pow2_u32(p)), ip)
                      == U32.or(base, i) : U32} =
                FH.u32_or_base_sub(p, base, i, zi, plt, ige)
              FH.seen_tree_get_go_hi(p, base, xs, ys, gen, fg, i, eshr, eb2,
                hys, Arr.Arr.dup(Nat, ys),
                ys2 => hys2 =>
                  FH.seen_tree_get_go(p, U32.or(base, Arr.Arr.pow2_u32(p)),
                    ys2, gen, fg, ip,
                    U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, hys2))

def FH.seen_tree_get_dup2(-seen: Array<Nat>, a1: Array<Nat>, +gen: Nat,
    +fg: +List<SolveFast.FGroup>, +code: U32,
    +ea1: {a1 == seen : Array<Nat>}, -a2: Array<Nat>,
    +ea2: {a2 == a1 : Array<Nat>},
    dp2: &b1: Array<Nat> -> &b2: Array<Nat> ->
         {b1 == a2 : Array<Nat>} & {b2 == b1 : Array<Nat>},
    +zc: {Arr.Arr.u32_zero_from(10n, code) == True{} : Bool},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg)) ->
  {FH.seen_ok(fg, gen, code,
     Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, seen, code)))
   == True{} : Bool}:
  (b1, dp3) = dp2
  (b2, pe2) = dp3
  (+eb1, +eb2) = pe2
  +ea_b1 : {b1 == a1 : Array<Nat>} = Equal.trans(Array<Nat>, b1, a2, a1, eb1, ea2)
  +ea_b2 : {b2 == a1 : Array<Nat>} = Equal.trans(Array<Nat>, b2, b1, a1, eb2, ea_b1)
  +hs1 = FH.seen_tree_transport(10n, 0, seen, a1, gen, fg,
           Equal.sym(Array<Nat>, a1, seen, ea1), hs)
  +hs_b1 = FH.seen_tree_transport(10n, 0, a1, b1, gen, fg,
             Equal.sym(Array<Nat>, b1, a1, ea_b1), hs1)
  +hd_b1 = FH.seen_tree_depth(10n, 0, b1, gen, fg, hs_b1)
  +hd_b2 = Arr.Arr.depth_transport(Nat, 10n, b1, b2,
             Equal.sym(Array<Nat>, b2, b1, eb2), hd_b1)
  +em : {U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)) == code : U32} =
    Arr.Arr.u32_and_mask(10n, code, zc)
  +eg : {Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, b2, code))
         == Arr.Arr.snd(Array<Nat>, Nat,
              Array.get.go(Nat, b2, Arr.Arr.pow2_u32(10n), code,
                U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))) : Nat} =
    Equal.trans(Nat,
      Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, b2, code)),
      Arr.Arr.snd(Array<Nat>, Nat,
        Array.get.go(Nat, b2, Arr.Arr.pow2_u32(10n),
          U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)),
          U32.is_lt(U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)),
            U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.snd(Array<Nat>, Nat,
        Array.get.go(Nat, b2, Arr.Arr.pow2_u32(10n), code,
          U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.get_depth(Nat, 10n, b2, code, hd_b2),
      Equal.cong(U32, Nat,
        j => Arr.Arr.snd(Array<Nat>, Nat,
               Array.get.go(Nat, b2, Arr.Arr.pow2_u32(10n), j,
                 U32.is_lt(j, U32.shr(Arr.Arr.pow2_u32(10n))))),
        U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)), code, em))
  +ea1_b2 : {a1 == b2 : Array<Nat>} = Equal.sym(Array<Nat>, b2, a1, ea_b2)
  +ego : {FH.seen_ok(fg, gen, U32.or(0, code),
            Arr.Arr.snd(Array<Nat>, Nat,
              Array.get.go(Nat, a1, Arr.Arr.pow2_u32(10n), code,
                U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))))
          == True{} : Bool} =
    FH.seen_tree_get_go(10n, 0, a1, gen, fg, code,
      U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))), {==}, {==}, zc, hs1)
  +e0c : {U32.or(0, code) == code : U32} = FF5.FF5.u32_or_zero_l(code)
  %ea1 : {FH.seen_ok(fg, gen, code,
            Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, _, code)))
          == True{} : Bool}
  %ea_b2 : {FH.seen_ok(fg, gen, code,
              Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, _, code)))
            == True{} : Bool}
  Equal.trans(Bool,
    FH.seen_ok(fg, gen, code,
      Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, b2, code))),
    FH.seen_ok(fg, gen, code,
      Arr.Arr.snd(Array<Nat>, Nat,
        Array.get.go(Nat, b2, Arr.Arr.pow2_u32(10n), code,
          U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))),
    True{},
    Equal.cong(Nat, Bool, v => FH.seen_ok(fg, gen, code, v),
      Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, b2, code)),
      Arr.Arr.snd(Array<Nat>, Nat,
        Array.get.go(Nat, b2, Arr.Arr.pow2_u32(10n), code,
          U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      eg),
    Equal.trans(Bool,
      FH.seen_ok(fg, gen, code,
        Arr.Arr.snd(Array<Nat>, Nat,
          Array.get.go(Nat, b2, Arr.Arr.pow2_u32(10n), code,
            U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))),
      FH.seen_ok(fg, gen, U32.or(0, code),
        Arr.Arr.snd(Array<Nat>, Nat,
          Array.get.go(Nat, a1, Arr.Arr.pow2_u32(10n), code,
            U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))),
      True{},
      Equal.trans(Bool,
        FH.seen_ok(fg, gen, code,
          Arr.Arr.snd(Array<Nat>, Nat,
            Array.get.go(Nat, b2, Arr.Arr.pow2_u32(10n), code,
              U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))),
        FH.seen_ok(fg, gen, code,
          Arr.Arr.snd(Array<Nat>, Nat,
            Array.get.go(Nat, a1, Arr.Arr.pow2_u32(10n), code,
              U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))),
        FH.seen_ok(fg, gen, U32.or(0, code),
          Arr.Arr.snd(Array<Nat>, Nat,
            Array.get.go(Nat, a1, Arr.Arr.pow2_u32(10n), code,
              U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))),
        Equal.cong(Array<Nat>, Bool,
          x => FH.seen_ok(fg, gen, code,
                 Arr.Arr.snd(Array<Nat>, Nat,
                   Array.get.go(Nat, x, Arr.Arr.pow2_u32(10n), code,
                     U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))),
          b2, a1, ea_b2),
        Equal.cong(U32, Bool,
          c => FH.seen_ok(fg, gen, c,
                 Arr.Arr.snd(Array<Nat>, Nat,
                   Array.get.go(Nat, a1, Arr.Arr.pow2_u32(10n), code,
                     U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))),
          code, U32.or(0, code), Equal.sym(U32, U32.or(0, code), code, e0c))),
      ego))

def FH.seen_tree_get_dup(-seen: Array<Nat>, +gen: Nat,
    +fg: +List<SolveFast.FGroup>, +code: U32,
    +zc: {Arr.Arr.u32_zero_from(10n, code) == True{} : Bool},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg),
    dp: &a1: Array<Nat> -> &a2: Array<Nat> ->
        {a1 == seen : Array<Nat>} & {a2 == a1 : Array<Nat>}) ->
  {FH.seen_ok(fg, gen, code,
     Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, seen, code)))
   == True{} : Bool}:
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  FH.seen_tree_get_dup2(seen, a1, gen, fg, code, ea1, a2, ea2,
    Arr.Arr.dup(Nat, a2), zc, hs)

def FH.seen_tree_get(seen: Array<Nat>, +gen: Nat,
    +fg: +List<SolveFast.FGroup>, +code: U32,
    +zc: {Arr.Arr.u32_zero_from(10n, code) == True{} : Bool},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg)) ->
  {FH.seen_ok(fg, gen, code,
     Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, seen, code)))
   == True{} : Bool}:
  FH.seen_tree_get_dup(seen, gen, fg, code, zc, hs, Arr.Arr.dup(Nat, seen))

def FH.u32_ne_of_bit_val(+k: Nat, +a: U32, +b: U32, bval: Bool,
    +ha: {FH.u32_bit(k, a) == bval : Bool},
    +hb: {FH.u32_bit(k, b) == Bool.not(bval) : Bool}) ->
  {U32.is_eq(a, b) == False{} : Bool}:
  match bval:
    case True{}:
      FH.u32_ne_of_bit_tf(k, a, b, ha, hb)
    case False{}:
      FH.u32_ne_of_bit_ft(k, a, b, ha, hb)

# Updating `SeenTree` on `Array.swap(Nat, seen, code, gen)`.
def FH.seen_tree_other(+d: Nat, +base: U32, a: Array<Nat>, +gen: Nat,
    +w: +List<Nat>, +fb: +List<Feedback.Color>, +fg: +List<SolveFast.FGroup>,
    +k: Nat, +bval: Bool,
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool},
    +hle: {Nat.is_le(d, k) == True{} : Bool},
    +hbb: {FH.u32_bit(k, base) == bval : Bool},
    +hbc: {FH.u32_bit(k, FF5.FF5.encode_fb5_list(fb)) == Bool.not(bval) : Bool},
    +hs: FH.SeenTree(d, base, a, gen, fg)) ->
  FH.SeenTree(d, base, a, gen, SolveFast.fgroup_add_fast(w, fb, fg)):
  match d:
    case 0n:
      match a:
        case ALeaf{+v}:
          +c = FF5.FF5.encode_fb5_list(fb)
          +hne : {U32.is_eq(base, c) == False{} : Bool} =
            FH.u32_ne_of_bit_val(k, base, c, bval, hbb, hbc)
          +ehas : {FH.has_code(base, SolveFast.fgroup_add_fast(w, fb, fg))
                   == FH.has_code(base, fg) : Bool} =
            FH.fgroup_add_has_other(w, fb, fg,
              SolveFast.next_fgroup_hit(fb, fg), base, {==}, hfb, hwf, hne)
          Equal.trans(Bool,
            FH.seen_ok(SolveFast.fgroup_add_fast(w, fb, fg), gen, base, v),
            FH.seen_ok(fg, gen, base, v),
            True{},
            Equal.cong(Bool, Bool,
              b => Feedback.Bool.case(Bool, b, Nat.is_eq(v, gen),
                     Nat.is_lt(v, gen)),
              FH.has_code(base, SolveFast.fgroup_add_fast(w, fb, fg)),
              FH.has_code(base, fg), ehas),
            hs)
        case ANode{xs, ys}:
          hs
    case 1n++p:
      match a:
        case ALeaf{v}:
          hs
        case ANode{xs, ys}:
          +hxs = Arr.Arr.dpair_l(
                   FH.SeenTree(p, base, xs, gen, fg),
                   FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys,
                     gen, fg), hs)
          +hys = Arr.Arr.dpair_r(
                   FH.SeenTree(p, base, xs, gen, fg),
                   FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys,
                     gen, fg), hs)
          +hpk : {Nat.is_lt(p, k) == True{} : Bool} =
            NatProof.Nat.is_lt_le_trans(p, 1n+p, k,
              NatProof.Nat.is_lt_succ_self(p), hle)
          +hple : {Nat.is_le(p, k) == True{} : Bool} =
            NatProof.Nat.is_le_of_lt(p, k, hpk)
          +hbb2 : {FH.u32_bit(k, U32.or(base, Arr.Arr.pow2_u32(p)))
                   == bval : Bool} =
            Equal.trans(Bool,
              FH.u32_bit(k, U32.or(base, Arr.Arr.pow2_u32(p))),
              FH.u32_bit(k, base), bval,
              FH.u32_bit_or_pow2_lt(k, p, base, hpk), hbb)
          Arr.DPair{
            FH.seen_tree_other(p, base, xs, gen, w, fb, fg, k, bval,
              hfb, hwf, hple, hbb, hbc, hxs),
            FH.seen_tree_other(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, gen,
              w, fb, fg, k, bval, hfb, hwf, hple, hbb2, hbc, hys)}

def FH.seen_swap_lo(+p: Nat, +base: U32, -ys: Array<Nat>, r: Array<Nat> & Nat,
    +gen: Nat, +fg2: +List<SolveFast.FGroup>,
    +hr: FH.SeenTree(p, base, Arr.Arr.fst(Array<Nat>, Nat, r), gen, fg2),
    +hy: FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, gen, fg2)) ->
  FH.SeenTree(1n+p, base,
    Arr.Arr.fst(Array<Nat>, Nat, Array.swap.lo(Nat, ys, r)), gen, fg2):
  (a2, res) = r
  Arr.DPair{hr, hy}

def FH.seen_swap_hi(+p: Nat, +base: U32, -xs: Array<Nat>, r: Array<Nat> & Nat,
    +gen: Nat, +fg2: +List<SolveFast.FGroup>,
    +hx: FH.SeenTree(p, base, xs, gen, fg2),
    +hr: FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)),
           Arr.Arr.fst(Array<Nat>, Nat, r), gen, fg2)) ->
  FH.SeenTree(1n+p, base,
    Arr.Arr.fst(Array<Nat>, Nat, Array.swap.hi(Nat, xs, r)), gen, fg2):
  (a2, res) = r
  Arr.DPair{hx, hr}

def FH.seen_tree_swap_go_lo(+p: Nat, +base: U32, -xs: Array<Nat>,
    -ys: Array<Nat>, +gen: Nat, +fg: +List<SolveFast.FGroup>,
    +fg2: +List<SolveFast.FGroup>, +i: U32,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +hxs: FH.SeenTree(p, base, xs, gen, fg),
    +hys2: FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, gen, fg2),
    d: &a1: Array<Nat> -> &a2: Array<Nat> ->
       {a1 == xs : Array<Nat>} & {a2 == a1 : Array<Nat>},
    ih: @xs2: Array<Nat> -> FH.SeenTree(p, base, xs2, gen, fg) ->
        FH.SeenTree(p, base,
          Arr.Arr.fst(Array<Nat>, Nat,
            Array.swap.go(Nat, xs2, Arr.Arr.pow2_u32(p), i, gen,
              U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))), gen, fg2)) ->
  FH.SeenTree(1n+p, base,
    Arr.Arr.fst(Array<Nat>, Nat,
      Array.swap.go(Nat, ANode{xs, ys}, Arr.Arr.pow2_u32(1n+p), i, gen,
        True{})), gen, fg2):
  (xs1, d2) = d
  (xs2, pe) = d2
  (+ex1, +ex2) = pe
  +hxs2 = FH.seen_tree_transport(p, base, xs, xs2, gen, fg,
            Equal.sym(Array<Nat>, xs2, xs,
              Equal.trans(Array<Nat>, xs2, xs1, xs, ex2, ex1)), hxs)
  +h2 = ih(xs2, hxs2)
  +h1 : FH.SeenTree(p, base,
          Arr.Arr.fst(Array<Nat>, Nat,
            Array.swap.go(Nat, xs1, Arr.Arr.pow2_u32(p), i, gen,
              U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))), gen, fg2) =
    FH.seen_tree_transport(p, base,
      Arr.Arr.fst(Array<Nat>, Nat,
        Array.swap.go(Nat, xs2, Arr.Arr.pow2_u32(p), i, gen,
          U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
      Arr.Arr.fst(Array<Nat>, Nat,
        Array.swap.go(Nat, xs1, Arr.Arr.pow2_u32(p), i, gen,
          U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
      gen, fg2,
      Equal.cong(Array<Nat>, Array<Nat>,
        x => Arr.Arr.fst(Array<Nat>, Nat,
               Array.swap.go(Nat, x, Arr.Arr.pow2_u32(p), i, gen,
                 U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
        xs2, xs1, ex2),
      h2)
  %ex1 : FH.SeenTree(1n+p, base,
           Arr.Arr.fst(Array<Nat>, Nat,
             Array.swap.go(Nat, ANode{_, ys}, Arr.Arr.pow2_u32(1n+p), i, gen,
               True{})), gen, fg2)
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    FH.SeenTree(1n+p, base,
      Arr.Arr.fst(Array<Nat>, Nat,
        Array.swap.lo(Nat, ys,
          Array.swap.go(Nat, xs1, _, i, gen, U32.is_lt(i, U32.shr(_))))),
      gen, fg2)
  FH.seen_swap_lo(p, base, ys,
    Array.swap.go(Nat, xs1, Arr.Arr.pow2_u32(p), i, gen,
      U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))),
    gen, fg2, h1, hys2)

def FH.seen_tree_swap_go_hi(+p: Nat, +base: U32, -xs: Array<Nat>,
    -ys: Array<Nat>, +gen: Nat, +fg: +List<SolveFast.FGroup>,
    +fg2: +List<SolveFast.FGroup>, +i: U32,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +hxs2: FH.SeenTree(p, base, xs, gen, fg2),
    +hys: FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, gen, fg),
    d: &a1: Array<Nat> -> &a2: Array<Nat> ->
       {a1 == ys : Array<Nat>} & {a2 == a1 : Array<Nat>},
    ih: @ys2: Array<Nat> ->
        FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys2, gen, fg) ->
        FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)),
          Arr.Arr.fst(Array<Nat>, Nat,
            Array.swap.go(Nat, ys2, Arr.Arr.pow2_u32(p),
              U32.sub(i, Arr.Arr.pow2_u32(p)), gen,
              U32.is_lt(U32.sub(i, Arr.Arr.pow2_u32(p)),
                U32.shr(Arr.Arr.pow2_u32(p))))), gen, fg2)) ->
  FH.SeenTree(1n+p, base,
    Arr.Arr.fst(Array<Nat>, Nat,
      Array.swap.go(Nat, ANode{xs, ys}, Arr.Arr.pow2_u32(1n+p), i, gen,
        False{})), gen, fg2):
  (ys1, d2) = d
  (ys2, pe) = d2
  (+ey1, +ey2) = pe
  +base2 = U32.or(base, Arr.Arr.pow2_u32(p))
  +ip = U32.sub(i, Arr.Arr.pow2_u32(p))
  +hys2 = FH.seen_tree_transport(p, base2, ys, ys2, gen, fg,
            Equal.sym(Array<Nat>, ys2, ys,
              Equal.trans(Array<Nat>, ys2, ys1, ys, ey2, ey1)), hys)
  +h2 = ih(ys2, hys2)
  +h1 : FH.SeenTree(p, base2,
          Arr.Arr.fst(Array<Nat>, Nat,
            Array.swap.go(Nat, ys1, Arr.Arr.pow2_u32(p), ip, gen,
              U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))), gen, fg2) =
    FH.seen_tree_transport(p, base2,
      Arr.Arr.fst(Array<Nat>, Nat,
        Array.swap.go(Nat, ys2, Arr.Arr.pow2_u32(p), ip, gen,
          U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
      Arr.Arr.fst(Array<Nat>, Nat,
        Array.swap.go(Nat, ys1, Arr.Arr.pow2_u32(p), ip, gen,
          U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
      gen, fg2,
      Equal.cong(Array<Nat>, Array<Nat>,
        y => Arr.Arr.fst(Array<Nat>, Nat,
               Array.swap.go(Nat, y, Arr.Arr.pow2_u32(p), ip, gen,
                 U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
        ys2, ys1, ey2),
      h2)
  %ey1 : FH.SeenTree(1n+p, base,
           Arr.Arr.fst(Array<Nat>, Nat,
             Array.swap.go(Nat, ANode{xs, _}, Arr.Arr.pow2_u32(1n+p), i, gen,
               False{})), gen, fg2)
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    FH.SeenTree(1n+p, base,
      Arr.Arr.fst(Array<Nat>, Nat,
        Array.swap.hi(Nat, xs,
          Array.swap.go(Nat, ys1, _, U32.sub(i, _), gen,
            U32.is_lt(U32.sub(i, _), U32.shr(_))))),
      gen, fg2)
  FH.seen_swap_hi(p, base, xs,
    Array.swap.go(Nat, ys1, Arr.Arr.pow2_u32(p), ip, gen,
      U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))),
    gen, fg2, hxs2, h1)

def FH.seen_tree_swap_go(+d: Nat, +base: U32, a: Array<Nat>, +gen: Nat,
    +w: +List<Nat>, +fb: +List<Feedback.Color>, +fg: +List<SolveFast.FGroup>,
    +i: U32, z: Bool,
    +ez: {z == U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(d))) : Bool},
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.Arr.u32_zero_from(d, i) == True{} : Bool},
    +hbz: {FH.u32_zero_below(d, base) == True{} : Bool},
    +etgt: {U32.or(base, i) == FF5.FF5.encode_fb5_list(fb) : U32},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool},
    +hself: {FH.has_code(FF5.FF5.encode_fb5_list(fb),
               SolveFast.fgroup_add_fast(w, fb, fg)) == True{} : Bool},
    +hs: FH.SeenTree(d, base, a, gen, fg)) ->
  FH.SeenTree(d, base,
    Arr.Arr.fst(Array<Nat>, Nat,
      Array.swap.go(Nat, a, Arr.Arr.pow2_u32(d), i, gen, z)),
    gen, SolveFast.fgroup_add_fast(w, fb, fg)):
  match d:
    case 0n:
      match a:
        case ALeaf{v}:
          +ei0 : {i == 0 : U32} = Arr.Arr.u32_eq_zero(i, zi)
          +ebase : {base == FF5.FF5.encode_fb5_list(fb) : U32} =
            Equal.trans(U32, base, U32.or(base, 0),
              FF5.FF5.encode_fb5_list(fb),
              Equal.sym(U32, U32.or(base, 0), base, FF5.FF5.u32_or_zero_r(base)),
              Equal.trans(U32, U32.or(base, 0), U32.or(base, i),
                FF5.FF5.encode_fb5_list(fb),
                Equal.cong(U32, U32, x => U32.or(base, x), 0, i,
                  Equal.sym(U32, i, 0, ei0)),
                etgt))
          +hhas : {FH.has_code(base, SolveFast.fgroup_add_fast(w, fb, fg))
                   == True{} : Bool} =
            Equal.trans(Bool,
              FH.has_code(base, SolveFast.fgroup_add_fast(w, fb, fg)),
              FH.has_code(FF5.FF5.encode_fb5_list(fb),
                SolveFast.fgroup_add_fast(w, fb, fg)),
              True{},
              Equal.cong(U32, Bool,
                c => FH.has_code(c, SolveFast.fgroup_add_fast(w, fb, fg)),
                base, FF5.FF5.encode_fb5_list(fb), ebase),
              hself)
          Equal.trans(Bool,
            FH.seen_ok(SolveFast.fgroup_add_fast(w, fb, fg), gen, base, gen),
            Nat.is_eq(gen, gen),
            True{},
            Equal.cong(Bool, Bool,
              b => Feedback.Bool.case(Bool, b, Nat.is_eq(gen, gen),
                     Nat.is_lt(gen, gen)),
              FH.has_code(base, SolveFast.fgroup_add_fast(w, fb, fg)), True{},
              hhas),
            NatProof.NatPrf.is_eq_refl(gen))
        case ANode{xs, ys}:
          Empty.absurd(
            FH.SeenTree(0n, base,
              Arr.Arr.fst(Array<Nat>, Nat,
                Array.swap.go(Nat, ANode{xs, ys}, Arr.Arr.pow2_u32(0n), i, gen,
                  z)), gen, SolveFast.fgroup_add_fast(w, fb, fg)), hs)
    case 1n++p:
      match a:
        case ALeaf{v}:
          Empty.absurd(
            FH.SeenTree(1n+p, base,
              Arr.Arr.fst(Array<Nat>, Nat,
                Array.swap.go(Nat, ALeaf{v}, Arr.Arr.pow2_u32(1n+p), i, gen, z)),
              gen, SolveFast.fgroup_add_fast(w, fb, fg)), hs)
        case ANode{xs, ys}:
          match z:
            case True{}:
              +hxs = Arr.Arr.dpair_l(
                       FH.SeenTree(p, base, xs, gen, fg),
                       FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys,
                         gen, fg), hs)
              +hys = Arr.Arr.dpair_r(
                       FH.SeenTree(p, base, xs, gen, fg),
                       FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys,
                         gen, fg), hs)
              +plt : {Nat.is_lt(p, 32n) == True{} : Bool} =
                NatProof.Nat.is_le_lt_trans(p, 1n+p, 32n,
                  NatProof.Nat.is_le_of_lt(p, 1n+p,
                    NatProof.Nat.is_lt_succ_self(p)), hlt)
              +eshr : {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p)
                       : U32} =
                Arr.Arr.u32_shr_pow2(p, hlt)
              +ilt : {U32.is_lt(i, Arr.Arr.pow2_u32(p)) == True{} : Bool} =
                Equal.trans(Bool,
                  U32.is_lt(i, Arr.Arr.pow2_u32(p)),
                  U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))),
                  True{},
                  Equal.cong(U32, Bool, x => U32.is_lt(i, x),
                    Arr.Arr.pow2_u32(p), U32.shr(Arr.Arr.pow2_u32(1n+p)),
                    Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)),
                      Arr.Arr.pow2_u32(p), eshr)),
                  Equal.sym(Bool, True{},
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))), ez))
              +zip : {Arr.Arr.u32_zero_from(p, i) == True{} : Bool} =
                Arr.Arr.u32_zero_from_lt(p, i, zi, plt, ilt)
              +hbzp : {FH.u32_zero_below(p, base) == True{} : Bool} =
                FH.u32_zero_below_pred(p, base, hbz)
              +hbp_base : {FH.u32_bit(p, base) == False{} : Bool} =
                FH.u32_bit_of_zero_below(p, base, hbz)
              +hbp_i : {FH.u32_bit(p, i) == False{} : Bool} =
                FH.u32_bit_of_lt(p, i, zi, plt, ilt)
              +hbp_tgt : {FH.u32_bit(p, FF5.FF5.encode_fb5_list(fb))
                          == False{} : Bool} =
                Equal.trans(Bool,
                  FH.u32_bit(p, FF5.FF5.encode_fb5_list(fb)),
                  FH.u32_bit(p, U32.or(base, i)),
                  False{},
                  Equal.cong(U32, Bool, u => FH.u32_bit(p, u),
                    FF5.FF5.encode_fb5_list(fb), U32.or(base, i),
                    Equal.sym(U32, U32.or(base, i),
                      FF5.FF5.encode_fb5_list(fb), etgt)),
                  Equal.trans(Bool,
                    FH.u32_bit(p, U32.or(base, i)),
                    Bool.or(FH.u32_bit(p, base), FH.u32_bit(p, i)),
                    False{},
                    FH.u32_bit_or(p, base, i),
                    Equal.trans(Bool,
                      Bool.or(FH.u32_bit(p, base), FH.u32_bit(p, i)),
                      Bool.or(False{}, FH.u32_bit(p, i)),
                      False{},
                      Equal.cong(Bool, Bool, b => Bool.or(b, FH.u32_bit(p, i)),
                        FH.u32_bit(p, base), False{}, hbp_base),
                      hbp_i)))
              +base2 = U32.or(base, Arr.Arr.pow2_u32(p))
              +hys2 = FH.seen_tree_other(p, base2, ys, gen, w, fb, fg, p, True{},
                        hfb, hwf, NatProof.Nat.is_le_refl(p),
                        FH.u32_bit_or_pow2_same(p, base, plt), hbp_tgt, hys)
              FH.seen_tree_swap_go_lo(p, base, xs, ys, gen, fg,
                SolveFast.fgroup_add_fast(w, fb, fg), i, eshr, hxs, hys2,
                Arr.Arr.dup(Nat, xs),
                xs2 => hxs2 =>
                  FH.seen_tree_swap_go(p, base, xs2, gen, w, fb, fg, i,
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, hbzp, etgt, hfb, hwf, hself, hxs2))
            case False{}:
              +hxs = Arr.Arr.dpair_l(
                       FH.SeenTree(p, base, xs, gen, fg),
                       FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys,
                         gen, fg), hs)
              +hys = Arr.Arr.dpair_r(
                       FH.SeenTree(p, base, xs, gen, fg),
                       FH.SeenTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys,
                         gen, fg), hs)
              +plt : {Nat.is_lt(p, 32n) == True{} : Bool} =
                NatProof.Nat.is_le_lt_trans(p, 1n+p, 32n,
                  NatProof.Nat.is_le_of_lt(p, 1n+p,
                    NatProof.Nat.is_lt_succ_self(p)), hlt)
              +eshr : {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p)
                       : U32} =
                Arr.Arr.u32_shr_pow2(p, hlt)
              +ige : {U32.is_lt(i, Arr.Arr.pow2_u32(p)) == False{} : Bool} =
                Equal.trans(Bool,
                  U32.is_lt(i, Arr.Arr.pow2_u32(p)),
                  U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))),
                  False{},
                  Equal.cong(U32, Bool, x => U32.is_lt(i, x),
                    Arr.Arr.pow2_u32(p), U32.shr(Arr.Arr.pow2_u32(1n+p)),
                    Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)),
                      Arr.Arr.pow2_u32(p), eshr)),
                  Equal.sym(Bool, False{},
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))), ez))
              +ip = U32.sub(i, Arr.Arr.pow2_u32(p))
              +zip : {Arr.Arr.u32_zero_from(p, ip) == True{} : Bool} =
                Arr.Arr.u32_zero_from_ge(p, i, zi, plt, ige)
              +base2 = U32.or(base, Arr.Arr.pow2_u32(p))
              +hbzp : {FH.u32_zero_below(p, base) == True{} : Bool} =
                FH.u32_zero_below_pred(p, base, hbz)
              +hbz2 : {FH.u32_zero_below(p, base2) == True{} : Bool} =
                FH.u32_zero_below_or_pow2(p, base, hbzp)
              +hbp_base : {FH.u32_bit(p, base) == False{} : Bool} =
                FH.u32_bit_of_zero_below(p, base, hbz)
              +hbp_i : {FH.u32_bit(p, i) == True{} : Bool} =
                FH.u32_bit_of_ge(p, i, zi, plt, ige)
              +hbp_tgt : {FH.u32_bit(p, FF5.FF5.encode_fb5_list(fb))
                          == True{} : Bool} =
                Equal.trans(Bool,
                  FH.u32_bit(p, FF5.FF5.encode_fb5_list(fb)),
                  FH.u32_bit(p, U32.or(base, i)),
                  True{},
                  Equal.cong(U32, Bool, u => FH.u32_bit(p, u),
                    FF5.FF5.encode_fb5_list(fb), U32.or(base, i),
                    Equal.sym(U32, U32.or(base, i),
                      FF5.FF5.encode_fb5_list(fb), etgt)),
                  Equal.trans(Bool,
                    FH.u32_bit(p, U32.or(base, i)),
                    Bool.or(FH.u32_bit(p, base), FH.u32_bit(p, i)),
                    True{},
                    FH.u32_bit_or(p, base, i),
                    Equal.trans(Bool,
                      Bool.or(FH.u32_bit(p, base), FH.u32_bit(p, i)),
                      Bool.or(False{}, FH.u32_bit(p, i)),
                      True{},
                      Equal.cong(Bool, Bool, b => Bool.or(b, FH.u32_bit(p, i)),
                        FH.u32_bit(p, base), False{}, hbp_base),
                      hbp_i)))
              +etgt2 : {U32.or(base2, ip) == FF5.FF5.encode_fb5_list(fb) : U32} =
                Equal.trans(U32, U32.or(base2, ip), U32.or(base, i),
                  FF5.FF5.encode_fb5_list(fb),
                  FH.u32_or_base_sub(p, base, i, zi, plt, ige), etgt)
              +hxs2 = FH.seen_tree_other(p, base, xs, gen, w, fb, fg, p, False{},
                        hfb, hwf, NatProof.Nat.is_le_refl(p), hbp_base, hbp_tgt,
                        hxs)
              FH.seen_tree_swap_go_hi(p, base, xs, ys, gen, fg,
                SolveFast.fgroup_add_fast(w, fb, fg), i, eshr, hxs2, hys,
                Arr.Arr.dup(Nat, ys),
                ys2 => hys2 =>
                  FH.seen_tree_swap_go(p, base2, ys2, gen, w, fb, fg, ip,
                    U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, hbz2, etgt2, hfb, hwf, hself, hys2))

def FH.seen_tree_swap_dup2(-seen: Array<Nat>, a1: Array<Nat>, +gen: Nat,
    +w: +List<Nat>, +fb: +List<Feedback.Color>, +fg: +List<SolveFast.FGroup>,
    +ea1: {a1 == seen : Array<Nat>}, -a2: Array<Nat>,
    +ea2: {a2 == a1 : Array<Nat>},
    dp2: &b1: Array<Nat> -> &b2: Array<Nat> ->
         {b1 == a2 : Array<Nat>} & {b2 == b1 : Array<Nat>},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool},
    +hself: {FH.has_code(FF5.FF5.encode_fb5_list(fb),
               SolveFast.fgroup_add_fast(w, fb, fg)) == True{} : Bool},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg)) ->
  FH.SeenTree(10n, 0,
    Arr.Arr.fst(Array<Nat>, Nat,
      Array.swap(Nat, seen, FF5.FF5.encode_fb5_list(fb), gen)),
    gen, SolveFast.fgroup_add_fast(w, fb, fg)):
  (b1, dp3) = dp2
  (b2, pe2) = dp3
  (+eb1, +eb2) = pe2
  +code = FF5.FF5.encode_fb5_list(fb)
  +zc : {Arr.Arr.u32_zero_from(10n, code) == True{} : Bool} =
    FF5.FF5.encode_fb5_list_zero_from(fb, hfb)
  +ea_b1 : {b1 == a1 : Array<Nat>} = Equal.trans(Array<Nat>, b1, a2, a1, eb1, ea2)
  +ea_b2 : {b2 == a1 : Array<Nat>} = Equal.trans(Array<Nat>, b2, b1, a1, eb2, ea_b1)
  +hs1 = FH.seen_tree_transport(10n, 0, seen, a1, gen, fg,
           Equal.sym(Array<Nat>, a1, seen, ea1), hs)
  +hs_b1 = FH.seen_tree_transport(10n, 0, a1, b1, gen, fg,
             Equal.sym(Array<Nat>, b1, a1, ea_b1), hs1)
  +hd_b1 = FH.seen_tree_depth(10n, 0, b1, gen, fg, hs_b1)
  +hd_b2 = Arr.Arr.depth_transport(Nat, 10n, b1, b2,
             Equal.sym(Array<Nat>, b2, b1, eb2), hd_b1)
  +em : {U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)) == code : U32} =
    Arr.Arr.u32_and_mask(10n, code, zc)
  +esw : {Arr.Arr.fst(Array<Nat>, Nat, Array.swap(Nat, b2, code, gen))
          == Arr.Arr.fst(Array<Nat>, Nat,
               Array.swap.go(Nat, b2, Arr.Arr.pow2_u32(10n), code, gen,
                 U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))
          : Array<Nat>} =
    Equal.trans(Array<Nat>,
      Arr.Arr.fst(Array<Nat>, Nat, Array.swap(Nat, b2, code, gen)),
      Arr.Arr.fst(Array<Nat>, Nat,
        Array.swap.go(Nat, b2, Arr.Arr.pow2_u32(10n),
          U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)), gen,
          U32.is_lt(U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)),
            U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.fst(Array<Nat>, Nat,
        Array.swap.go(Nat, b2, Arr.Arr.pow2_u32(10n), code, gen,
          U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.swap_depth(Nat, 10n, b2, code, gen, hd_b2),
      Equal.cong(U32, Array<Nat>,
        j => Arr.Arr.fst(Array<Nat>, Nat,
               Array.swap.go(Nat, b2, Arr.Arr.pow2_u32(10n), j, gen,
                 U32.is_lt(j, U32.shr(Arr.Arr.pow2_u32(10n))))),
        U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)), code, em))
  +ea1_b2 : {a1 == b2 : Array<Nat>} = Equal.sym(Array<Nat>, b2, a1, ea_b2)
  +hgo = FH.seen_tree_swap_go(10n, 0, a1, gen, w, fb, fg, code,
           U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))), {==}, {==}, zc,
           {==}, FF5.FF5.u32_or_zero_l(code), hfb, hwf, hself, hs1)
  +eq_a : {Arr.Arr.fst(Array<Nat>, Nat,
             Array.swap.go(Nat, a1, Arr.Arr.pow2_u32(10n), code, gen,
               U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))
           == Arr.Arr.fst(Array<Nat>, Nat, Array.swap(Nat, b2, code, gen))
           : Array<Nat>} =
    Equal.trans(Array<Nat>,
      Arr.Arr.fst(Array<Nat>, Nat,
        Array.swap.go(Nat, a1, Arr.Arr.pow2_u32(10n), code, gen,
          U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.fst(Array<Nat>, Nat,
        Array.swap.go(Nat, b2, Arr.Arr.pow2_u32(10n), code, gen,
          U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.fst(Array<Nat>, Nat, Array.swap(Nat, b2, code, gen)),
      Equal.cong(Array<Nat>, Array<Nat>,
        x => Arr.Arr.fst(Array<Nat>, Nat,
               Array.swap.go(Nat, x, Arr.Arr.pow2_u32(10n), code, gen,
                 U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
        a1, b2, ea1_b2),
      Equal.sym(Array<Nat>,
        Arr.Arr.fst(Array<Nat>, Nat, Array.swap(Nat, b2, code, gen)),
        Arr.Arr.fst(Array<Nat>, Nat,
          Array.swap.go(Nat, b2, Arr.Arr.pow2_u32(10n), code, gen,
            U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
        esw))
  %ea1 : FH.SeenTree(10n, 0,
           Arr.Arr.fst(Array<Nat>, Nat, Array.swap(Nat, _, code, gen)),
           gen, SolveFast.fgroup_add_fast(w, fb, fg))
  %ea_b2 : FH.SeenTree(10n, 0,
             Arr.Arr.fst(Array<Nat>, Nat, Array.swap(Nat, _, code, gen)),
             gen, SolveFast.fgroup_add_fast(w, fb, fg))
  FH.seen_tree_transport(10n, 0,
    Arr.Arr.fst(Array<Nat>, Nat,
      Array.swap.go(Nat, a1, Arr.Arr.pow2_u32(10n), code, gen,
        U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
    Arr.Arr.fst(Array<Nat>, Nat, Array.swap(Nat, b2, code, gen)),
    gen, SolveFast.fgroup_add_fast(w, fb, fg), eq_a, hgo)

def FH.seen_tree_swap_dup(-seen: Array<Nat>, +gen: Nat,
    +w: +List<Nat>, +fb: +List<Feedback.Color>, +fg: +List<SolveFast.FGroup>,
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool},
    +hself: {FH.has_code(FF5.FF5.encode_fb5_list(fb),
               SolveFast.fgroup_add_fast(w, fb, fg)) == True{} : Bool},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg),
    dp: &a1: Array<Nat> -> &a2: Array<Nat> ->
        {a1 == seen : Array<Nat>} & {a2 == a1 : Array<Nat>}) ->
  FH.SeenTree(10n, 0,
    Arr.Arr.fst(Array<Nat>, Nat,
      Array.swap(Nat, seen, FF5.FF5.encode_fb5_list(fb), gen)),
    gen, SolveFast.fgroup_add_fast(w, fb, fg)):
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  FH.seen_tree_swap_dup2(seen, a1, gen, w, fb, fg, ea1, a2, ea2,
    Arr.Arr.dup(Nat, a2), hfb, hwf, hself, hs)

def FH.seen_tree_swap(seen: Array<Nat>, +gen: Nat,
    +w: +List<Nat>, +fb: +List<Feedback.Color>, +fg: +List<SolveFast.FGroup>,
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool},
    +hself: {FH.has_code(FF5.FF5.encode_fb5_list(fb),
               SolveFast.fgroup_add_fast(w, fb, fg)) == True{} : Bool},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg)) ->
  FH.SeenTree(10n, 0,
    Arr.Arr.fst(Array<Nat>, Nat,
      Array.swap(Nat, seen, FF5.FF5.encode_fb5_list(fb), gen)),
    gen, SolveFast.fgroup_add_fast(w, fb, fg)):
  FH.seen_tree_swap_dup(seen, gen, w, fb, fg, hfb, hwf, hself, hs,
    Arr.Arr.dup(Nat, seen))

# ---------------------------------------------------------------------------
# Pass 1 specification: `SolveFast.hist5_go`
# ---------------------------------------------------------------------------

def FH.nat_ne_of_lt(+a: Nat, +b: Nat,
    +hlt: {Nat.is_lt(a, b) == True{} : Bool},
    eq: Bool, +eeq: {eq == Nat.is_eq(a, b) : Bool}) ->
  {Nat.is_eq(a, b) == False{} : Bool}:
  match eq:
    case False{}:
      Equal.sym(Bool, False{}, Nat.is_eq(a, b), eeq)
    case True{}:
      +eab : {a == b : Nat} =
        NatProof.NatPrf.is_eq_true(a, b,
          Equal.sym(Bool, True{}, Nat.is_eq(a, b), eeq))
      +hself : {Nat.is_lt(b, b) == True{} : Bool} =
        Equal.trans(Bool, Nat.is_lt(b, b), Nat.is_lt(a, b), True{},
          Equal.cong(Nat, Bool, x => Nat.is_lt(x, b), b, a,
            Equal.sym(Nat, a, b, eab)), hlt)
      Empty.absurd({Nat.is_eq(a, b) == False{} : Bool},
        NatProof.Nat.not_lt_self(b, hself))

def FH.seen_ok_eq_gen_iff(+fg: +List<SolveFast.FGroup>, +gen: Nat, +c: U32,
    +v: Nat, b: Bool, +eb: {b == FH.has_code(c, fg) : Bool},
    +hok: {FH.seen_ok(fg, gen, c, v) == True{} : Bool}) ->
  {Nat.is_eq(v, gen) == FH.has_code(c, fg) : Bool}:
  match b:
    case True{}:
      +heq : {Nat.is_eq(v, gen) == True{} : Bool} =
        Equal.trans(Bool, Nat.is_eq(v, gen), FH.seen_ok(fg, gen, c, v), True{},
          Equal.cong(Bool, Bool,
            x => Feedback.Bool.case(Bool, x, Nat.is_eq(v, gen),
                   Nat.is_lt(v, gen)),
            True{}, FH.has_code(c, fg), eb),
          hok)
      Equal.trans(Bool, Nat.is_eq(v, gen), True{}, FH.has_code(c, fg),
        heq, eb)
    case False{}:
      +hlt : {Nat.is_lt(v, gen) == True{} : Bool} =
        Equal.trans(Bool, Nat.is_lt(v, gen), FH.seen_ok(fg, gen, c, v), True{},
          Equal.cong(Bool, Bool,
            x => Feedback.Bool.case(Bool, x, Nat.is_eq(v, gen),
                   Nat.is_lt(v, gen)),
            False{}, FH.has_code(c, fg), eb),
          hok)
      +hne : {Nat.is_eq(v, gen) == False{} : Bool} =
        FH.nat_ne_of_lt(v, gen, hlt, Nat.is_eq(v, gen), {==})
      Equal.trans(Bool, Nat.is_eq(v, gen), False{}, FH.has_code(c, fg),
        hne, eb)

# Result predicate for `hist5_go` (`-> Data` so freely copyable!).
def FH.HistSpec(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +fg0: +List<SolveFast.FGroup>, +gen: Nat, res: SolveFast.Hist5Res) -> Data:
  match res:
    case SolveFast.Hist5Fallback{seen2}:
      FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{})
    case SolveFast.Hist5Ok{seen2, m, k}:
      +fg1 : +List<SolveFast.FGroup> = SolveFast.fgroups_build_fast(g, S, fg0)
      Arr.Arr.DPair<
        FH.SeenTree(10n, 0, seen2, gen, fg1),
        Arr.Arr.DPair<
          {FH.all_len5(S) == True{} : Bool},
          Arr.Arr.DPair<
            {FH.fgroups_wf(fg1) == True{} : Bool},
            Arr.Arr.DPair<
              {m == FH.fgroups_total(fg1) : Nat},
              Arr.Arr.DPair<
                {k == FH.fgroups_count(fg1) : Nat},
                {Nat.is_le(m, Nat.add(Groups.len_words(S),
                                      FH.fgroups_total(fg0))) == True{} : Bool}>>>>>

def FH.hist_spec_transport(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +fg0: +List<SolveFast.FGroup>, +gen: Nat,
    -r1: SolveFast.Hist5Res, -r2: SolveFast.Hist5Res,
    +er: {r1 == r2 : SolveFast.Hist5Res},
    +h: FH.HistSpec(g, S, fg0, gen, r1)) ->
  FH.HistSpec(g, S, fg0, gen, r2):
  %er : FH.HistSpec(g, S, fg0, gen, _)
  h

def FH.HistOneSpec(+g: +List<Nat>, +w: +List<Nat>,
    +fg0: +List<SolveFast.FGroup>, +gen: Nat, res: SolveFast.Hist5Res) -> Data:
  match res:
    case SolveFast.Hist5Fallback{seen2}:
      FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{})
    case SolveFast.Hist5Ok{seen2, m, k}:
      +fg1 : +List<SolveFast.FGroup> =
        SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w))
      Arr.Arr.DPair<
        FH.SeenTree(10n, 0, seen2, gen, fg1),
        Arr.Arr.DPair<
          {FH.is_word5(w) == True{} : Bool},
          Arr.Arr.DPair<
            {FH.fgroups_wf(fg1) == True{} : Bool},
            Arr.Arr.DPair<
              {m == FH.fgroups_total(fg1) : Nat},
              Arr.Arr.DPair<
                {k == FH.fgroups_count(fg1) : Nat},
                {Nat.is_le(m, Nat.add(1n, FH.fgroups_total(fg0)))
                 == True{} : Bool}>>>>>

def FH.hist_one_transport(+g: +List<Nat>, +w: +List<Nat>,
    +fg0: +List<SolveFast.FGroup>, +gen: Nat,
    -r1: SolveFast.Hist5Res, -r2: SolveFast.Hist5Res,
    +er: {r1 == r2 : SolveFast.Hist5Res},
    +h: FH.HistOneSpec(g, w, fg0, gen, r1)) ->
  FH.HistOneSpec(g, w, fg0, gen, r2):
  %er : FH.HistOneSpec(g, w, fg0, gen, _)
  h

def FH.hist5_hit_branch(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>,
    -seen2: Array<Nat>, +gen: Nat, +m: Nat, +k: Nat,
    seen_before: Bool,
    +esb: {seen_before == FH.has_code(FF5.FF5.encode_fb5_list(fb), fg0) : Bool},
    +h5w: {FH.is_word5(w) == True{} : Bool},
    +efg1: {SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w))
            == SolveFast.fgroup_add_fast(w, fb, fg0) : +List<SolveFast.FGroup>},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs_next: FH.SeenTree(10n, 0, seen2, gen,
                SolveFast.fgroups_next_acc(g, w, fg0,
                  SolveFast.word_eq_fast(g, w))),
    +wf_next: {FH.fgroups_wf(
                 SolveFast.fgroups_next_acc(g, w, fg0,
                   SolveFast.word_eq_fast(g, w))) == True{} : Bool},
    +em1: {Nat.add(1n, m)
           == FH.fgroups_total(
                SolveFast.fgroups_next_acc(g, w, fg0,
                  SolveFast.word_eq_fast(g, w))) : Nat},
    +hle1: {Nat.is_le(Nat.add(1n, m), Nat.add(1n, FH.fgroups_total(fg0)))
            == True{} : Bool},
    +cnt2: {FH.fgroups_count(SolveFast.fgroup_add_fast(w, fb, fg0))
            == Feedback.Bool.case(Nat,
                 FH.has_code(FF5.FF5.encode_fb5_list(fb), fg0),
                 FH.fgroups_count(fg0),
                 Nat.add(1n, FH.fgroups_count(fg0))) : Nat}) ->
  FH.HistOneSpec(g, w, fg0, gen,
    SolveFast.hist5_hit(seen2, m, k, seen_before)):
  match seen_before:
    case True{}:
      +fg1 = SolveFast.fgroup_add_fast(w, fb, fg0)
      +fg_next = SolveFast.fgroups_next_acc(g, w, fg0,
                   SolveFast.word_eq_fast(g, w))
      +ec : {FH.fgroups_count(fg1) == FH.fgroups_count(fg0) : Nat} =
        Equal.trans(Nat,
          FH.fgroups_count(fg1),
          Feedback.Bool.case(Nat,
            FH.has_code(FF5.FF5.encode_fb5_list(fb), fg0),
            FH.fgroups_count(fg0), Nat.add(1n, FH.fgroups_count(fg0))),
          FH.fgroups_count(fg0),
          cnt2,
          Equal.cong(Bool, Nat,
            b => Feedback.Bool.case(Nat, b,
                   FH.fgroups_count(fg0), Nat.add(1n, FH.fgroups_count(fg0))),
            FH.has_code(FF5.FF5.encode_fb5_list(fb), fg0), True{},
            Equal.sym(Bool, True{},
              FH.has_code(FF5.FF5.encode_fb5_list(fb), fg0), esb)))
      +ek1 : {k == FH.fgroups_count(fg_next) : Nat} =
        Equal.trans(Nat, k, FH.fgroups_count(fg0), FH.fgroups_count(fg_next),
          hk,
          Equal.trans(Nat, FH.fgroups_count(fg0), FH.fgroups_count(fg1),
            FH.fgroups_count(fg_next),
            Equal.sym(Nat, FH.fgroups_count(fg1), FH.fgroups_count(fg0), ec),
            Equal.cong(+List<SolveFast.FGroup>, Nat, x => FH.fgroups_count(x),
              fg1, fg_next,
              Equal.sym(+List<SolveFast.FGroup>, fg_next, fg1, efg1))))
      Arr.DPair{hs_next, Arr.DPair{h5w, Arr.DPair{wf_next,
        Arr.DPair{em1, Arr.DPair{ek1, hle1}}}}}
    case False{}:
      +fg1 = SolveFast.fgroup_add_fast(w, fb, fg0)
      +fg_next = SolveFast.fgroups_next_acc(g, w, fg0,
                   SolveFast.word_eq_fast(g, w))
      +ec : {FH.fgroups_count(fg1) == Nat.add(1n, FH.fgroups_count(fg0)) : Nat} =
        Equal.trans(Nat,
          FH.fgroups_count(fg1),
          Feedback.Bool.case(Nat,
            FH.has_code(FF5.FF5.encode_fb5_list(fb), fg0),
            FH.fgroups_count(fg0), Nat.add(1n, FH.fgroups_count(fg0))),
          Nat.add(1n, FH.fgroups_count(fg0)),
          cnt2,
          Equal.cong(Bool, Nat,
            b => Feedback.Bool.case(Nat, b,
                   FH.fgroups_count(fg0), Nat.add(1n, FH.fgroups_count(fg0))),
            FH.has_code(FF5.FF5.encode_fb5_list(fb), fg0), False{},
            Equal.sym(Bool, False{},
              FH.has_code(FF5.FF5.encode_fb5_list(fb), fg0), esb)))
      +ek1 : {Nat.add(1n, k) == FH.fgroups_count(fg_next) : Nat} =
        Equal.trans(Nat, Nat.add(1n, k), Nat.add(1n, FH.fgroups_count(fg0)),
          FH.fgroups_count(fg_next),
          Equal.cong(Nat, Nat, x => Nat.add(1n, x), k, FH.fgroups_count(fg0),
            hk),
          Equal.trans(Nat, Nat.add(1n, FH.fgroups_count(fg0)),
            FH.fgroups_count(fg1), FH.fgroups_count(fg_next),
            Equal.sym(Nat, FH.fgroups_count(fg1),
              Nat.add(1n, FH.fgroups_count(fg0)), ec),
            Equal.cong(+List<SolveFast.FGroup>, Nat, x => FH.fgroups_count(x),
              fg1, fg_next,
              Equal.sym(+List<SolveFast.FGroup>, fg_next, fg1, efg1))))
      Arr.DPair{hs_next, Arr.DPair{h5w, Arr.DPair{wf_next,
        Arr.DPair{em1, Arr.DPair{ek1, hle1}}}}}

def FH.hist5_hit_spec(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>,
    -seen2: Array<Nat>, +gen: Nat, +m: Nat, +k: Nat,
    seen_before: Bool,
    +esb: {seen_before == FH.has_code(FF5.FF5.encode_fb5_list(fb), fg0) : Bool},
    +h5w: {FH.is_word5(w) == True{} : Bool},
    +efg1: {SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w))
            == SolveFast.fgroup_add_fast(w, fb, fg0) : +List<SolveFast.FGroup>},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs_new: FH.SeenTree(10n, 0, seen2, gen,
               SolveFast.fgroup_add_fast(w, fb, fg0)),
    facts: FH.AddFacts<w, fb, fg0, SolveFast.fgroup_add_fast(w, fb, fg0)>) ->
  FH.HistOneSpec(g, w, fg0, gen,
    SolveFast.hist5_hit(seen2, m, k, seen_before)):
  match facts:
    case AddFacts{+wf2, +tot2, +cnt2, +has2, +lkp2}:
      +fg1 = SolveFast.fgroup_add_fast(w, fb, fg0)
      +fg_next = SolveFast.fgroups_next_acc(g, w, fg0,
                   SolveFast.word_eq_fast(g, w))
      +efg_sym : {fg1 == fg_next : +List<SolveFast.FGroup>} =
        Equal.sym(+List<SolveFast.FGroup>, fg_next, fg1, efg1)
      +hs_next = FH.seen_tree_transport_fg(10n, 0, seen2, gen, fg1, fg_next,
                   efg_sym, hs_new)
      +wf_next : {FH.fgroups_wf(fg_next) == True{} : Bool} =
        Equal.trans(Bool, FH.fgroups_wf(fg_next), FH.fgroups_wf(fg1), True{},
          Equal.cong(+List<SolveFast.FGroup>, Bool, x => FH.fgroups_wf(x),
            fg_next, fg1, efg1), wf2)
      +em1 : {Nat.add(1n, m) == FH.fgroups_total(fg_next) : Nat} =
        Equal.trans(Nat, Nat.add(1n, m), Nat.add(1n, FH.fgroups_total(fg0)),
          FH.fgroups_total(fg_next),
          Equal.cong(Nat, Nat, x => Nat.add(1n, x), m, FH.fgroups_total(fg0),
            hm),
          Equal.trans(Nat, Nat.add(1n, FH.fgroups_total(fg0)),
            FH.fgroups_total(fg1), FH.fgroups_total(fg_next),
            Equal.sym(Nat, FH.fgroups_total(fg1),
              Nat.add(1n, FH.fgroups_total(fg0)), tot2),
            Equal.cong(+List<SolveFast.FGroup>, Nat, x => FH.fgroups_total(x),
              fg1, fg_next, efg_sym)))
      +hle1 : {Nat.is_le(Nat.add(1n, m), Nat.add(1n, FH.fgroups_total(fg0)))
               == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(Nat.add(1n, FH.fgroups_total(fg0)),
          Nat.add(1n, FH.fgroups_total(fg0)), Nat.add(1n, m),
          Equal.cong(Nat, Nat, x => Nat.add(1n, x), FH.fgroups_total(fg0), m,
            Equal.sym(Nat, m, FH.fgroups_total(fg0), hm)),
          NatProof.Nat.is_le_refl(Nat.add(1n, FH.fgroups_total(fg0))))
      FH.hist5_hit_branch(g, w, fb, fg0, seen2, gen, m, k, seen_before, esb,
        h5w, efg1, hk, hs_next, wf_next, em1, hle1, cnt2)

def FH.hist5_swap_spec_go(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>, +gen: Nat,
    +m: Nat, +k: Nat, r: Array<Nat> & Nat,
    +h5w: {FH.is_word5(w) == True{} : Bool},
    +ewf: {SolveFast.word_eq_fast(g, w) == False{} : Bool},
    +efbeq: {SolveFast.feedback_fast(g, w) == fb : +List<Feedback.Color>},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs_new: FH.SeenTree(10n, 0, Arr.Arr.fst(Array<Nat>, Nat, r), gen,
               SolveFast.fgroup_add_fast(w, fb, fg0)),
    +hok: {FH.seen_ok(fg0, gen, FF5.FF5.encode_fb5_list(fb),
             Arr.Arr.snd(Array<Nat>, Nat, r)) == True{} : Bool}) ->
  FH.HistOneSpec(g, w, fg0, gen, SolveFast.hist5_swap(gen, m, k, r)):
  (seen2, +old) = r
  +c = FF5.FF5.encode_fb5_list(fb)
  +hold : {Nat.is_eq(old, gen) == FH.has_code(c, fg0) : Bool} =
    FH.seen_ok_eq_gen_iff(fg0, gen, c, old, FH.has_code(c, fg0), {==}, hok)
  +fg1 = SolveFast.fgroup_add_fast(w, fb, fg0)
  +efg1 : {SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w))
           == fg1 : +List<SolveFast.FGroup>} =
    Equal.trans(+List<SolveFast.FGroup>,
      SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)),
      SolveFast.fgroup_add_fast(w, SolveFast.feedback_fast(g, w), fg0),
      fg1,
      Equal.cong(Bool, +List<SolveFast.FGroup>,
        b => SolveFast.fgroups_next_acc(g, w, fg0, b),
        SolveFast.word_eq_fast(g, w), False{}, ewf),
      Equal.cong(+List<Feedback.Color>, +List<SolveFast.FGroup>,
        f => SolveFast.fgroup_add_fast(w, f, fg0),
        SolveFast.feedback_fast(g, w), fb, efbeq))
  +facts = FH.fgroup_add_facts(w, fb, fg0,
             SolveFast.next_fgroup_hit(fb, fg0), {==}, hfb, hwf)
  FH.hist5_hit_spec(g, w, fb, fg0, seen2, gen, m, k,
    Nat.is_eq(old, gen), hold, h5w, efg1, hm, hk, hs_new, facts)

def FH.hist5_step_swap_dup4(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>,
    -seen: Array<Nat>, s1: Array<Nat>, +ea1: {s1 == seen : Array<Nat>},
    b1: Array<Nat>, +ea_b1: {b1 == s1 : Array<Nat>},
    b2: Array<Nat>, +ea_b2: {b2 == s1 : Array<Nat>},
    -b3: Array<Nat>, +ea_b3: {b3 == s1 : Array<Nat>},
    dp4: &c1: Array<Nat> -> &c2: Array<Nat> ->
         {c1 == b3 : Array<Nat>} & {c2 == c1 : Array<Nat>},
    +gen: Nat, +m: Nat, +k: Nat, +code: U32,
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +h5w: {FH.is_word5(w) == True{} : Bool},
    +ewf: {SolveFast.word_eq_fast(g, w) == False{} : Bool},
    +efbeq: {SolveFast.feedback_fast(g, w) == fb : +List<Feedback.Color>},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg0),
    +hself: {FH.has_code(FF5.FF5.encode_fb5_list(fb),
               SolveFast.fgroup_add_fast(w, fb, fg0)) == True{} : Bool}) ->
  FH.HistOneSpec(g, w, fg0, gen,
    SolveFast.hist5_swap(gen, m, k, Array.swap(Nat, seen, code, gen))):
  (c1, dp5) = dp4
  (c2, pe4) = dp5
  (+ec1, +ec2) = pe4
  +ea_c1 : {c1 == s1 : Array<Nat>} = Equal.trans(Array<Nat>, c1, b3, s1, ec1, ea_b3)
  +ea_c2 : {c2 == s1 : Array<Nat>} = Equal.trans(Array<Nat>, c2, c1, s1, ec2, ea_c1)
  +es_b1 : {b1 == seen : Array<Nat>} = Equal.trans(Array<Nat>, b1, s1, seen, ea_b1, ea1)
  +es_b2 : {b2 == seen : Array<Nat>} = Equal.trans(Array<Nat>, b2, s1, seen, ea_b2, ea1)
  +es_c1 : {c1 == seen : Array<Nat>} = Equal.trans(Array<Nat>, c1, s1, seen, ea_c1, ea1)
  +c = FF5.FF5.encode_fb5_list(fb)
  +zc : {Arr.Arr.u32_zero_from(10n, c) == True{} : Bool} =
    FF5.FF5.encode_fb5_list_zero_from(fb, hfb)
  +hs_b1 = FH.seen_tree_transport(10n, 0, seen, b1, gen, fg0,
             Equal.sym(Array<Nat>, b1, seen, es_b1), hs)
  +hs_b2 = FH.seen_tree_transport(10n, 0, seen, b2, gen, fg0,
             Equal.sym(Array<Nat>, b2, seen, es_b2), hs)
  +hs_c1 = FH.seen_tree_transport(10n, 0, seen, c1, gen, fg0,
             Equal.sym(Array<Nat>, c1, seen, es_c1), hs)
  +hd_c1 = FH.seen_tree_depth(10n, 0, c1, gen, fg0, hs_c1)
  +hd_c2 = Arr.Arr.depth_transport(Nat, 10n, c1, c2,
             Equal.sym(Array<Nat>, c2, c1, ec2), hd_c1)
  +hs_new_b1 : FH.SeenTree(10n, 0,
                 Arr.Arr.fst(Array<Nat>, Nat, Array.swap(Nat, b1, c, gen)),
                 gen, SolveFast.fgroup_add_fast(w, fb, fg0)) =
    FH.seen_tree_swap(b1, gen, w, fb, fg0, hfb, hwf, hself, hs_b1)
  +hs_new_s1 : FH.SeenTree(10n, 0,
                 Arr.Arr.fst(Array<Nat>, Nat, Array.swap(Nat, s1, c, gen)),
                 gen, SolveFast.fgroup_add_fast(w, fb, fg0)) =
    FH.seen_tree_transport(10n, 0,
      Arr.Arr.fst(Array<Nat>, Nat, Array.swap(Nat, b1, c, gen)),
      Arr.Arr.fst(Array<Nat>, Nat, Array.swap(Nat, s1, c, gen)),
      gen, SolveFast.fgroup_add_fast(w, fb, fg0),
      Equal.cong(Array<Nat>, Array<Nat>,
        x => Arr.Arr.fst(Array<Nat>, Nat, Array.swap(Nat, x, c, gen)),
        b1, s1, ea_b1),
      hs_new_b1)
  +hok_b2 : {FH.seen_ok(fg0, gen, c,
               Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, b2, c)))
             == True{} : Bool} =
    FH.seen_tree_get(b2, gen, fg0, c, zc, hs_b2)
  +esw_old_c2 : {Arr.Arr.snd(Array<Nat>, Nat, Array.swap(Nat, c2, c, gen))
                 == Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, c2, c)) : Nat} =
    Arr.Arr.swap_old(Nat, 10n, c2, c, gen, hd_c2)
  +hok_s1 : {FH.seen_ok(fg0, gen, c,
               Arr.Arr.snd(Array<Nat>, Nat, Array.swap(Nat, s1, c, gen)))
             == True{} : Bool} =
    Equal.trans(Bool,
      FH.seen_ok(fg0, gen, c,
        Arr.Arr.snd(Array<Nat>, Nat, Array.swap(Nat, s1, c, gen))),
      FH.seen_ok(fg0, gen, c,
        Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, b2, c))),
      True{},
      Equal.trans(Bool,
        FH.seen_ok(fg0, gen, c,
          Arr.Arr.snd(Array<Nat>, Nat, Array.swap(Nat, s1, c, gen))),
        FH.seen_ok(fg0, gen, c,
          Arr.Arr.snd(Array<Nat>, Nat, Array.swap(Nat, c2, c, gen))),
        FH.seen_ok(fg0, gen, c,
          Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, b2, c))),
        Equal.cong(Array<Nat>, Bool,
          x => FH.seen_ok(fg0, gen, c,
                 Arr.Arr.snd(Array<Nat>, Nat, Array.swap(Nat, x, c, gen))),
          s1, c2, Equal.sym(Array<Nat>, c2, s1, ea_c2)),
        Equal.trans(Bool,
          FH.seen_ok(fg0, gen, c,
            Arr.Arr.snd(Array<Nat>, Nat, Array.swap(Nat, c2, c, gen))),
          FH.seen_ok(fg0, gen, c,
            Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, c2, c))),
          FH.seen_ok(fg0, gen, c,
            Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, b2, c))),
          Equal.cong(Nat, Bool, v => FH.seen_ok(fg0, gen, c, v),
            Arr.Arr.snd(Array<Nat>, Nat, Array.swap(Nat, c2, c, gen)),
            Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, c2, c)), esw_old_c2),
          Equal.cong(Array<Nat>, Bool,
            x => FH.seen_ok(fg0, gen, c,
                   Arr.Arr.snd(Array<Nat>, Nat, Array.get(Nat, x, c))),
            c2, b2,
            Equal.trans(Array<Nat>, c2, s1, b2, ea_c2,
              Equal.sym(Array<Nat>, b2, s1, ea_b2))))),
      hok_b2)
  %ea1 : FH.HistOneSpec(g, w, fg0, gen,
           SolveFast.hist5_swap(gen, m, k, Array.swap(Nat, _, code, gen)))
  %Equal.sym(U32, code, c, ecode) :
    FH.HistOneSpec(g, w, fg0, gen,
      SolveFast.hist5_swap(gen, m, k, Array.swap(Nat, s1, _, gen)))
  FH.hist5_swap_spec_go(g, w, fb, fg0, gen, m, k, Array.swap(Nat, s1, c, gen),
    h5w, ewf, efbeq, hfb, hwf, hm, hk, hs_new_s1, hok_s1)

def FH.hist5_step_swap_dup3(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>,
    -seen: Array<Nat>, s1: Array<Nat>, +ea1: {s1 == seen : Array<Nat>},
    b1: Array<Nat>, +ea_b1: {b1 == s1 : Array<Nat>},
    -b2: Array<Nat>, +ea_b2: {b2 == s1 : Array<Nat>},
    dp3: &x1: Array<Nat> -> &x2: Array<Nat> ->
         {x1 == b2 : Array<Nat>} & {x2 == x1 : Array<Nat>},
    +gen: Nat, +m: Nat, +k: Nat, +code: U32,
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +h5w: {FH.is_word5(w) == True{} : Bool},
    +ewf: {SolveFast.word_eq_fast(g, w) == False{} : Bool},
    +efbeq: {SolveFast.feedback_fast(g, w) == fb : +List<Feedback.Color>},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg0),
    +hself: {FH.has_code(FF5.FF5.encode_fb5_list(fb),
               SolveFast.fgroup_add_fast(w, fb, fg0)) == True{} : Bool}) ->
  FH.HistOneSpec(g, w, fg0, gen,
    SolveFast.hist5_swap(gen, m, k, Array.swap(Nat, seen, code, gen))):
  (x1, dpx) = dp3
  (x2, pex) = dpx
  (+ex1, +ex2) = pex
  +ea_x1 : {x1 == s1 : Array<Nat>} = Equal.trans(Array<Nat>, x1, b2, s1, ex1, ea_b2)
  +ea_x2 : {x2 == s1 : Array<Nat>} = Equal.trans(Array<Nat>, x2, x1, s1, ex2, ea_x1)
  FH.hist5_step_swap_dup4(g, w, fb, fg0, seen, s1, ea1, b1, ea_b1, x1, ea_x1,
    x2, ea_x2, Arr.Arr.dup(Nat, x2), gen, m, k, code, ecode, h5w, ewf, efbeq,
    hfb, hwf, hm, hk, hs, hself)

def FH.hist5_step_swap_dup2(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>,
    -seen: Array<Nat>, s1: Array<Nat>, +ea1: {s1 == seen : Array<Nat>},
    -s2: Array<Nat>, +ea2: {s2 == s1 : Array<Nat>},
    dp2: &b1: Array<Nat> -> &b2: Array<Nat> ->
         {b1 == s2 : Array<Nat>} & {b2 == b1 : Array<Nat>},
    +gen: Nat, +m: Nat, +k: Nat, +code: U32,
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +h5w: {FH.is_word5(w) == True{} : Bool},
    +ewf: {SolveFast.word_eq_fast(g, w) == False{} : Bool},
    +efbeq: {SolveFast.feedback_fast(g, w) == fb : +List<Feedback.Color>},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg0),
    +hself: {FH.has_code(FF5.FF5.encode_fb5_list(fb),
               SolveFast.fgroup_add_fast(w, fb, fg0)) == True{} : Bool}) ->
  FH.HistOneSpec(g, w, fg0, gen,
    SolveFast.hist5_swap(gen, m, k, Array.swap(Nat, seen, code, gen))):
  (b1, dp3) = dp2
  (b2, pe2) = dp3
  (+eb1, +eb2) = pe2
  +ea_b1 : {b1 == s1 : Array<Nat>} = Equal.trans(Array<Nat>, b1, s2, s1, eb1, ea2)
  +ea_b2 : {b2 == s1 : Array<Nat>} = Equal.trans(Array<Nat>, b2, b1, s1, eb2, ea_b1)
  FH.hist5_step_swap_dup3(g, w, fb, fg0, seen, s1, ea1, b1, ea_b1, b2, ea_b2,
    Arr.Arr.dup(Nat, b2), gen, m, k, code, ecode, h5w, ewf, efbeq, hfb, hwf,
    hm, hk, hs, hself)

def FH.hist5_step_swap_dup(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>,
    -seen: Array<Nat>, +gen: Nat, +m: Nat, +k: Nat, +code: U32,
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +h5w: {FH.is_word5(w) == True{} : Bool},
    +ewf: {SolveFast.word_eq_fast(g, w) == False{} : Bool},
    +efbeq: {SolveFast.feedback_fast(g, w) == fb : +List<Feedback.Color>},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg0),
    +hself: {FH.has_code(FF5.FF5.encode_fb5_list(fb),
               SolveFast.fgroup_add_fast(w, fb, fg0)) == True{} : Bool},
    dp: &s1: Array<Nat> -> &s2: Array<Nat> ->
        {s1 == seen : Array<Nat>} & {s2 == s1 : Array<Nat>}) ->
  FH.HistOneSpec(g, w, fg0, gen,
    SolveFast.hist5_swap(gen, m, k, Array.swap(Nat, seen, code, gen))):
  (s1, dp2) = dp
  (s2, pe) = dp2
  (+ea1, +ea2) = pe
  FH.hist5_step_swap_dup2(g, w, fb, fg0, seen, s1, ea1, s2, ea2,
    Arr.Arr.dup(Nat, s2), gen, m, k, code, ecode, h5w, ewf, efbeq,
    hfb, hwf, hm, hk, hs, hself)

def FH.add_facts_has_self(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +fg0: +List<SolveFast.FGroup>, +fg1: +List<SolveFast.FGroup>,
    f: FH.AddFacts<w, fb, fg0, fg1>) ->
  {FH.has_code(FF5.FF5.encode_fb5_list(fb), fg1) == True{} : Bool}:
  match f:
    case AddFacts{wf2, tot2, cnt2, has_self, lkp_self}:
      has_self

def FH.hist5_step_spec(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>,
    seen: Array<Nat>, +gen: Nat, +m: Nat, +k: Nat, +code: U32,
    same: Bool,
    +esame: {same == SolveFast.word_eq_fast(g, w) : Bool},
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +h5w: {FH.is_word5(w) == True{} : Bool},
    +efbeq: {SolveFast.feedback_fast(g, w) == fb : +List<Feedback.Color>},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg0)) ->
  FH.HistOneSpec(g, w, fg0, gen,
    SolveFast.hist5_step(seen, gen, m, k, code, same)):
  match same:
    case True{}:
      +ewt : {SolveFast.word_eq_fast(g, w) == True{} : Bool} =
        Equal.sym(Bool, True{}, SolveFast.word_eq_fast(g, w), esame)
      +efg : {fg0 == SolveFast.fgroups_next_acc(g, w, fg0,
                       SolveFast.word_eq_fast(g, w)) : +List<SolveFast.FGroup>} =
        Equal.sym(+List<SolveFast.FGroup>,
          SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)),
          fg0,
          Equal.cong(Bool, +List<SolveFast.FGroup>,
            b => SolveFast.fgroups_next_acc(g, w, fg0, b),
            SolveFast.word_eq_fast(g, w), True{}, ewt))
      +fg_next = SolveFast.fgroups_next_acc(g, w, fg0,
                   SolveFast.word_eq_fast(g, w))
      +hs2 = FH.seen_tree_transport_fg(10n, 0, seen, gen, fg0, fg_next, efg, hs)
      +wf2 : {FH.fgroups_wf(fg_next) == True{} : Bool} =
        Equal.trans(Bool, FH.fgroups_wf(fg_next), FH.fgroups_wf(fg0), True{},
          Equal.cong(+List<SolveFast.FGroup>, Bool, x => FH.fgroups_wf(x),
            fg_next, fg0, Equal.sym(+List<SolveFast.FGroup>, fg0, fg_next, efg)),
          hwf)
      +hm2 : {m == FH.fgroups_total(fg_next) : Nat} =
        Equal.trans(Nat, m, FH.fgroups_total(fg0), FH.fgroups_total(fg_next),
          hm, Equal.cong(+List<SolveFast.FGroup>, Nat, x => FH.fgroups_total(x),
                fg0, fg_next, efg))
      +hk2 : {k == FH.fgroups_count(fg_next) : Nat} =
        Equal.trans(Nat, k, FH.fgroups_count(fg0), FH.fgroups_count(fg_next),
          hk, Equal.cong(+List<SolveFast.FGroup>, Nat, x => FH.fgroups_count(x),
                fg0, fg_next, efg))
      +hle : {Nat.is_le(m, Nat.add(1n, FH.fgroups_total(fg0))) == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(Nat.add(1n, FH.fgroups_total(fg0)),
          FH.fgroups_total(fg0), m,
          Equal.sym(Nat, m, FH.fgroups_total(fg0), hm),
          NatProof.Nat.is_le_of_lt(FH.fgroups_total(fg0),
            Nat.add(1n, FH.fgroups_total(fg0)),
            NatProof.Nat.is_lt_succ_self(FH.fgroups_total(fg0))))
      Arr.DPair{hs2, Arr.DPair{h5w, Arr.DPair{wf2,
        Arr.DPair{hm2, Arr.DPair{hk2, hle}}}}}
    case False{}:
      +ewf : {SolveFast.word_eq_fast(g, w) == False{} : Bool} =
        Equal.sym(Bool, False{}, SolveFast.word_eq_fast(g, w), esame)
      +hself = FH.add_facts_has_self(w, fb, fg0,
                 SolveFast.fgroup_add_fast(w, fb, fg0),
                 FH.fgroup_add_facts(w, fb, fg0,
                   SolveFast.next_fgroup_hit(fb, fg0), {==}, hfb, hwf))
      FH.hist5_step_swap_dup(g, w, fb, fg0, seen, gen, m, k, code, ecode,
        h5w, ewf, efbeq, hfb, hwf, hm, hk, hs, hself, Arr.Arr.dup(Nat, seen))

def FH.hist5_one_spec(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +w: +List<Nat>, +fg0: +List<SolveFast.FGroup>, seen: Array<Nat>, +gen: Nat,
    +m: Nat, +k: Nat,
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg0)) ->
  FH.HistOneSpec(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0, gen,
    SolveFast.hist5_one(g0, g1, g2, g3, g4, w, seen, gen, m, k)):
  match w:
    case Nil{}:
      FH.seen_tree_bump(10n, 0, seen, gen, fg0, hs)
    case Con{+a0, +t1}:
      match t1:
        case Nil{}:
          FH.seen_tree_bump(10n, 0, seen, gen, fg0, hs)
        case Con{+a1, +t2}:
          match t2:
            case Nil{}:
              FH.seen_tree_bump(10n, 0, seen, gen, fg0, hs)
            case Con{+a2, +t3}:
              match t3:
                case Nil{}:
                  FH.seen_tree_bump(10n, 0, seen, gen, fg0, hs)
                case Con{+a3, +t4}:
                  match t4:
                    case Nil{}:
                      FH.seen_tree_bump(10n, 0, seen, gen, fg0, hs)
                    case Con{+a4, +t5}:
                      match t5:
                        case Nil{}:
                          +gw : +List<Nat> =
                            g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
                          +aw : +List<Nat> =
                            a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))
                          +code = SolveFast.feedback_code5(g0, g1, g2, g3, g4,
                                    a0, a1, a2, a3, a4)
                          +fb = Feedback.feedback(gw, aw)
                          +esame : {U32.is_eq(code, 682)
                                    == SolveFast.word_eq_fast(gw, aw) : Bool} =
                            Equal.trans(Bool, U32.is_eq(code, 682),
                              Feedback.word_eq(gw, aw),
                              SolveFast.word_eq_fast(gw, aw),
                              FF5.FF5.code5_is_682_eq(g0, g1, g2, g3, g4,
                                a0, a1, a2, a3, a4),
                              Equal.sym(Bool, SolveFast.word_eq_fast(gw, aw),
                                Feedback.word_eq(gw, aw),
                                FG.FG.word_eq_fast_eq(gw, aw)))
                          FH.hist5_step_spec(gw, aw, fb, fg0, seen, gen, m, k,
                            code, U32.is_eq(code, 682), esame,
                            FF5.FF5.feedback_code5_eq(g0, g1, g2, g3, g4,
                              a0, a1, a2, a3, a4),
                            {==}, FG.FG.feedback_eq(gw, aw),
                            FF5.FF5.feedback_len5(g0, g1, g2, g3, g4,
                              a0, a1, a2, a3, a4),
                            hwf, hm, hk, hs)
                        case Con{+a5, +t6}:
                          FH.seen_tree_bump(10n, 0, seen, gen, fg0, hs)

def FH.hist5_fallback_rest(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +w: +List<Nat>, +rest: +List<+List<Nat>>, +fg0: +List<SolveFast.FGroup>,
    +gen: Nat, -seen2: Array<Nat>,
    +h1: FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{})) ->
  FH.HistSpec(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w <> rest, fg0, gen,
    SolveFast.hist5_go(g0, g1, g2, g3, g4, rest, gen,
      SolveFast.Hist5Fallback{seen2})):
  match rest:
    case Nil{}:
      h1
    case Con{w2, rest2}:
      h1

def FH.hist5_go_lift(+gw: +List<Nat>, +w: +List<Nat>, +rest: +List<+List<Nat>>,
    +fg0: +List<SolveFast.FGroup>, +gen: Nat, res: SolveFast.Hist5Res,
    +h5w: {FH.is_word5(w) == True{} : Bool},
    +hle_fg1: {Nat.is_le(
                 FH.fgroups_total(
                   SolveFast.fgroups_next_acc(gw, w, fg0,
                     SolveFast.word_eq_fast(gw, w))),
                 Nat.add(1n, FH.fgroups_total(fg0))) == True{} : Bool},
    +hrec: FH.HistSpec(gw, rest,
             SolveFast.fgroups_next_acc(gw, w, fg0,
               SolveFast.word_eq_fast(gw, w)), gen, res)) ->
  FH.HistSpec(gw, w <> rest, fg0, gen, res):
  match res:
    case SolveFast.Hist5Fallback{seen3}:
      hrec
    case SolveFast.Hist5Ok{seen3, +m3, +k3}:
      +fg1 = SolveFast.fgroups_next_acc(gw, w, fg0,
               SolveFast.word_eq_fast(gw, w))
      +fg2 = SolveFast.fgroups_build_fast(gw, rest, fg1)
      +hs3 = Arr.Arr.dpair_l(
               FH.SeenTree(10n, 0, seen3, gen, fg2),
               Arr.Arr.DPair<{FH.all_len5(rest) == True{} : Bool},
                 Arr.Arr.DPair<{FH.fgroups_wf(fg2) == True{} : Bool},
                   Arr.Arr.DPair<{m3 == FH.fgroups_total(fg2) : Nat},
                     Arr.Arr.DPair<{k3 == FH.fgroups_count(fg2) : Nat},
                       {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                              FH.fgroups_total(fg1)))
                        == True{} : Bool}>>>>, hrec)
      +r1 = Arr.Arr.dpair_r(
              FH.SeenTree(10n, 0, seen3, gen, fg2),
              Arr.Arr.DPair<{FH.all_len5(rest) == True{} : Bool},
                Arr.Arr.DPair<{FH.fgroups_wf(fg2) == True{} : Bool},
                  Arr.Arr.DPair<{m3 == FH.fgroups_total(fg2) : Nat},
                    Arr.Arr.DPair<{k3 == FH.fgroups_count(fg2) : Nat},
                      {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                             FH.fgroups_total(fg1)))
                       == True{} : Bool}>>>>, hrec)
      +h5r = Arr.Arr.dpair_l({FH.all_len5(rest) == True{} : Bool},
               Arr.Arr.DPair<{FH.fgroups_wf(fg2) == True{} : Bool},
                 Arr.Arr.DPair<{m3 == FH.fgroups_total(fg2) : Nat},
                   Arr.Arr.DPair<{k3 == FH.fgroups_count(fg2) : Nat},
                     {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                            FH.fgroups_total(fg1)))
                      == True{} : Bool}>>>, r1)
      +r2 = Arr.Arr.dpair_r({FH.all_len5(rest) == True{} : Bool},
              Arr.Arr.DPair<{FH.fgroups_wf(fg2) == True{} : Bool},
                Arr.Arr.DPair<{m3 == FH.fgroups_total(fg2) : Nat},
                  Arr.Arr.DPair<{k3 == FH.fgroups_count(fg2) : Nat},
                    {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                           FH.fgroups_total(fg1)))
                     == True{} : Bool}>>>, r1)
      +hwf2 = Arr.Arr.dpair_l({FH.fgroups_wf(fg2) == True{} : Bool},
                Arr.Arr.DPair<{m3 == FH.fgroups_total(fg2) : Nat},
                  Arr.Arr.DPair<{k3 == FH.fgroups_count(fg2) : Nat},
                    {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                           FH.fgroups_total(fg1)))
                     == True{} : Bool}>>, r2)
      +r3 = Arr.Arr.dpair_r({FH.fgroups_wf(fg2) == True{} : Bool},
              Arr.Arr.DPair<{m3 == FH.fgroups_total(fg2) : Nat},
                Arr.Arr.DPair<{k3 == FH.fgroups_count(fg2) : Nat},
                  {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                         FH.fgroups_total(fg1)))
                   == True{} : Bool}>>, r2)
      +hm3 = Arr.Arr.dpair_l({m3 == FH.fgroups_total(fg2) : Nat},
               Arr.Arr.DPair<{k3 == FH.fgroups_count(fg2) : Nat},
                 {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                        FH.fgroups_total(fg1)))
                  == True{} : Bool}>, r3)
      +r4 = Arr.Arr.dpair_r({m3 == FH.fgroups_total(fg2) : Nat},
              Arr.Arr.DPair<{k3 == FH.fgroups_count(fg2) : Nat},
                {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                       FH.fgroups_total(fg1)))
                 == True{} : Bool}>, r3)
      +hk3 = Arr.Arr.dpair_l({k3 == FH.fgroups_count(fg2) : Nat},
               {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                      FH.fgroups_total(fg1)))
                == True{} : Bool}, r4)
      +hle3 = Arr.Arr.dpair_r({k3 == FH.fgroups_count(fg2) : Nat},
                {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                       FH.fgroups_total(fg1)))
                 == True{} : Bool}, r4)
      +hle_step : {Nat.is_le(
                     Nat.add(Groups.len_words(rest), FH.fgroups_total(fg1)),
                     Nat.add(Groups.len_words(rest),
                       Nat.add(1n, FH.fgroups_total(fg0)))) == True{} : Bool} =
        NatProof.Nat.is_le_add_l(FH.fgroups_total(fg1),
          Nat.add(1n, FH.fgroups_total(fg0)), Groups.len_words(rest), hle_fg1)
      +hle_bound : {Nat.is_le(m3,
                      Nat.add(Nat.add(1n, Groups.len_words(rest)),
                        FH.fgroups_total(fg0))) == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(m3,
          Nat.add(Groups.len_words(rest), Nat.add(1n, FH.fgroups_total(fg0))),
          Nat.add(Nat.add(1n, Groups.len_words(rest)), FH.fgroups_total(fg0)),
          NatProof.NatPrf.add_succ(Groups.len_words(rest),
            FH.fgroups_total(fg0)),
          NatProof.Nat.is_le_trans(m3,
            Nat.add(Groups.len_words(rest), FH.fgroups_total(fg1)),
            Nat.add(Groups.len_words(rest), Nat.add(1n, FH.fgroups_total(fg0))),
            hle3, hle_step))
      Arr.DPair{hs3, Arr.DPair{
        FH.bool_and_intro(FH.is_word5(w), FH.all_len5(rest), h5w, h5r),
        Arr.DPair{hwf2, Arr.DPair{hm3, Arr.DPair{hk3, hle_bound}}}}}

def FH.hist5_go_ok_dup(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +w: +List<Nat>, +rest: +List<+List<Nat>>, +fg0: +List<SolveFast.FGroup>,
    +gen: Nat, -seen2: Array<Nat>, +m2: Nat, +k2: Nat,
    +h1: FH.HistOneSpec(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
           w, fg0, gen, SolveFast.Hist5Ok{seen2, m2, k2}),
    dp: &s2a: Array<Nat> -> &s2b: Array<Nat> ->
        {s2a == seen2 : Array<Nat>} & {s2b == s2a : Array<Nat>},
    rec: @s2: Array<Nat> -> @+m2r: Nat -> @+k2r: Nat ->
         {FH.fgroups_wf(
            SolveFast.fgroups_next_acc(
              g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
              SolveFast.word_eq_fast(
                g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w)))
          == True{} : Bool} ->
         {m2r == FH.fgroups_total(
                   SolveFast.fgroups_next_acc(
                     g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
                     SolveFast.word_eq_fast(
                       g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w))) : Nat} ->
         {k2r == FH.fgroups_count(
                   SolveFast.fgroups_next_acc(
                     g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
                     SolveFast.word_eq_fast(
                       g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w))) : Nat} ->
         FH.SeenTree(10n, 0, s2, gen,
           SolveFast.fgroups_next_acc(
             g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
             SolveFast.word_eq_fast(
               g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w))) ->
         FH.HistSpec(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), rest,
           SolveFast.fgroups_next_acc(
             g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
             SolveFast.word_eq_fast(
               g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w)),
           gen,
           SolveFast.hist5_go(g0, g1, g2, g3, g4, rest, gen,
             SolveFast.Hist5Ok{s2, m2r, k2r}))) ->
  FH.HistSpec(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w <> rest, fg0, gen,
    SolveFast.hist5_go(g0, g1, g2, g3, g4, rest, gen,
      SolveFast.Hist5Ok{seen2, m2, k2})):
  (s2a, dp2) = dp
  (s2b, pe) = dp2
  (+es2a, +es2b) = pe
  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
  +fg1 = SolveFast.fgroups_next_acc(gw, w, fg0,
           SolveFast.word_eq_fast(gw, w))
  +hs2 = Arr.Arr.dpair_l(
           FH.SeenTree(10n, 0, seen2, gen, fg1),
           Arr.Arr.DPair<{FH.is_word5(w) == True{} : Bool},
             Arr.Arr.DPair<{FH.fgroups_wf(fg1) == True{} : Bool},
               Arr.Arr.DPair<{m2 == FH.fgroups_total(fg1) : Nat},
                 Arr.Arr.DPair<{k2 == FH.fgroups_count(fg1) : Nat},
                   {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
                    == True{} : Bool}>>>>, h1)
  +r1 = Arr.Arr.dpair_r(
          FH.SeenTree(10n, 0, seen2, gen, fg1),
          Arr.Arr.DPair<{FH.is_word5(w) == True{} : Bool},
            Arr.Arr.DPair<{FH.fgroups_wf(fg1) == True{} : Bool},
              Arr.Arr.DPair<{m2 == FH.fgroups_total(fg1) : Nat},
                Arr.Arr.DPair<{k2 == FH.fgroups_count(fg1) : Nat},
                  {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
                   == True{} : Bool}>>>>, h1)
  +h5w = Arr.Arr.dpair_l({FH.is_word5(w) == True{} : Bool},
           Arr.Arr.DPair<{FH.fgroups_wf(fg1) == True{} : Bool},
             Arr.Arr.DPair<{m2 == FH.fgroups_total(fg1) : Nat},
               Arr.Arr.DPair<{k2 == FH.fgroups_count(fg1) : Nat},
                 {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
                  == True{} : Bool}>>>, r1)
  +r2 = Arr.Arr.dpair_r({FH.is_word5(w) == True{} : Bool},
          Arr.Arr.DPair<{FH.fgroups_wf(fg1) == True{} : Bool},
            Arr.Arr.DPair<{m2 == FH.fgroups_total(fg1) : Nat},
              Arr.Arr.DPair<{k2 == FH.fgroups_count(fg1) : Nat},
                {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
                 == True{} : Bool}>>>, r1)
  +hwf1 = Arr.Arr.dpair_l({FH.fgroups_wf(fg1) == True{} : Bool},
            Arr.Arr.DPair<{m2 == FH.fgroups_total(fg1) : Nat},
              Arr.Arr.DPair<{k2 == FH.fgroups_count(fg1) : Nat},
                {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
                 == True{} : Bool}>>, r2)
  +r3 = Arr.Arr.dpair_r({FH.fgroups_wf(fg1) == True{} : Bool},
          Arr.Arr.DPair<{m2 == FH.fgroups_total(fg1) : Nat},
            Arr.Arr.DPair<{k2 == FH.fgroups_count(fg1) : Nat},
              {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
               == True{} : Bool}>>, r2)
  +hm2 = Arr.Arr.dpair_l({m2 == FH.fgroups_total(fg1) : Nat},
           Arr.Arr.DPair<{k2 == FH.fgroups_count(fg1) : Nat},
             {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
              == True{} : Bool}>, r3)
  +r4 = Arr.Arr.dpair_r({m2 == FH.fgroups_total(fg1) : Nat},
          Arr.Arr.DPair<{k2 == FH.fgroups_count(fg1) : Nat},
            {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
             == True{} : Bool}>, r3)
  +hk2 = Arr.Arr.dpair_l({k2 == FH.fgroups_count(fg1) : Nat},
           {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
            == True{} : Bool}, r4)
  +hle2 = Arr.Arr.dpair_r({k2 == FH.fgroups_count(fg1) : Nat},
            {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
             == True{} : Bool}, r4)
  +es2b_s : {s2b == seen2 : Array<Nat>} =
    Equal.trans(Array<Nat>, s2b, s2a, seen2, es2b, es2a)
  +hs2b = FH.seen_tree_transport(10n, 0, seen2, s2b, gen, fg1,
            Equal.sym(Array<Nat>, s2b, seen2, es2b_s), hs2)
  +hrec_b = rec(s2b, m2, k2, hwf1, hm2, hk2, hs2b)
  +hrec_a = FH.hist_spec_transport(gw, rest, fg1, gen,
              SolveFast.hist5_go(g0, g1, g2, g3, g4, rest, gen,
                SolveFast.Hist5Ok{s2b, m2, k2}),
              SolveFast.hist5_go(g0, g1, g2, g3, g4, rest, gen,
                SolveFast.Hist5Ok{s2a, m2, k2}),
              Equal.cong(Array<Nat>, SolveFast.Hist5Res,
                x => SolveFast.hist5_go(g0, g1, g2, g3, g4, rest, gen,
                       SolveFast.Hist5Ok{x, m2, k2}),
                s2b, s2a, es2b),
              hrec_b)
  %es2a : FH.HistSpec(gw, w <> rest, fg0, gen,
            SolveFast.hist5_go(g0, g1, g2, g3, g4, rest, gen,
              SolveFast.Hist5Ok{_, m2, k2}))
  FH.hist5_go_lift(gw, w, rest, fg0, gen,
    SolveFast.hist5_go(g0, g1, g2, g3, g4, rest, gen,
      SolveFast.Hist5Ok{s2a, m2, k2}),
    h5w,
    NatProof.Nat.is_le_eq_l(Nat.add(1n, FH.fgroups_total(fg0)),
      m2, FH.fgroups_total(fg1), hm2, hle2),
    hrec_a)

def FH.hist5_go_step_dup(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +w: +List<Nat>, +rest: +List<+List<Nat>>, +fg0: +List<SolveFast.FGroup>,
    +gen: Nat, st1: SolveFast.Hist5Res,
    +h1: FH.HistOneSpec(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
           w, fg0, gen, st1),
    rec: @s2: Array<Nat> -> @+m2: Nat -> @+k2: Nat ->
         {FH.fgroups_wf(
            SolveFast.fgroups_next_acc(
              g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
              SolveFast.word_eq_fast(
                g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w)))
          == True{} : Bool} ->
         {m2 == FH.fgroups_total(
                  SolveFast.fgroups_next_acc(
                    g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
                    SolveFast.word_eq_fast(
                      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w))) : Nat} ->
         {k2 == FH.fgroups_count(
                  SolveFast.fgroups_next_acc(
                    g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
                    SolveFast.word_eq_fast(
                      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w))) : Nat} ->
         FH.SeenTree(10n, 0, s2, gen,
           SolveFast.fgroups_next_acc(
             g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
             SolveFast.word_eq_fast(
               g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w))) ->
         FH.HistSpec(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), rest,
           SolveFast.fgroups_next_acc(
             g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
             SolveFast.word_eq_fast(
               g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w)),
           gen,
           SolveFast.hist5_go(g0, g1, g2, g3, g4, rest, gen,
             SolveFast.Hist5Ok{s2, m2, k2}))) ->
  FH.HistSpec(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w <> rest, fg0, gen,
    SolveFast.hist5_go(g0, g1, g2, g3, g4, rest, gen, st1)):
  match st1:
    case SolveFast.Hist5Fallback{seen2}:
      FH.hist5_fallback_rest(g0, g1, g2, g3, g4, w, rest, fg0, gen, seen2, h1)
    case SolveFast.Hist5Ok{seen2, +m2, +k2}:
      FH.hist5_go_ok_dup(g0, g1, g2, g3, g4, w, rest, fg0, gen, seen2, m2, k2,
        h1, Arr.Arr.dup(Nat, seen2), rec)

def FH.hist5_go_cons_dup(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +w: +List<Nat>, +rest: +List<+List<Nat>>, +fg0: +List<SolveFast.FGroup>,
    -seen: Array<Nat>, +gen: Nat, +m: Nat, +k: Nat,
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg0),
    dp: &s1: Array<Nat> -> &s2: Array<Nat> ->
        {s1 == seen : Array<Nat>} & {s2 == s1 : Array<Nat>},
    rec: @s2: Array<Nat> -> @+m2: Nat -> @+k2: Nat ->
         {FH.fgroups_wf(
            SolveFast.fgroups_next_acc(
              g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
              SolveFast.word_eq_fast(
                g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w)))
          == True{} : Bool} ->
         {m2 == FH.fgroups_total(
                  SolveFast.fgroups_next_acc(
                    g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
                    SolveFast.word_eq_fast(
                      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w))) : Nat} ->
         {k2 == FH.fgroups_count(
                  SolveFast.fgroups_next_acc(
                    g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
                    SolveFast.word_eq_fast(
                      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w))) : Nat} ->
         FH.SeenTree(10n, 0, s2, gen,
           SolveFast.fgroups_next_acc(
             g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
             SolveFast.word_eq_fast(
               g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w))) ->
         FH.HistSpec(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), rest,
           SolveFast.fgroups_next_acc(
             g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
             SolveFast.word_eq_fast(
               g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w)),
           gen,
           SolveFast.hist5_go(g0, g1, g2, g3, g4, rest, gen,
             SolveFast.Hist5Ok{s2, m2, k2}))) ->
  FH.HistSpec(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w <> rest, fg0, gen,
    SolveFast.hist5_go(g0, g1, g2, g3, g4, rest, gen,
      SolveFast.hist5_one(g0, g1, g2, g3, g4, w, seen, gen, m, k))):
  (s1, dp2) = dp
  (s2, pe) = dp2
  (+es1, +es2) = pe
  +es2_s : {s2 == seen : Array<Nat>} = Equal.trans(Array<Nat>, s2, s1, seen, es2, es1)
  +hs2 = FH.seen_tree_transport(10n, 0, seen, s2, gen, fg0,
           Equal.sym(Array<Nat>, s2, seen, es2_s), hs)
  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
  +h1_s2 = FH.hist5_one_spec(g0, g1, g2, g3, g4, w, fg0, s2, gen, m, k,
             hwf, hm, hk, hs2)
  +es1_eq : {SolveFast.hist5_one(g0, g1, g2, g3, g4, w, s2, gen, m, k)
             == SolveFast.hist5_one(g0, g1, g2, g3, g4, w, s1, gen, m, k)
             : SolveFast.Hist5Res} =
    Equal.cong(Array<Nat>, SolveFast.Hist5Res,
      x => SolveFast.hist5_one(g0, g1, g2, g3, g4, w, x, gen, m, k),
      s2, s1, es2)
  %es1 : FH.HistSpec(gw, w <> rest, fg0, gen,
           SolveFast.hist5_go(g0, g1, g2, g3, g4, rest, gen,
             SolveFast.hist5_one(g0, g1, g2, g3, g4, w, _, gen, m, k)))
  %Equal.sym(SolveFast.Hist5Res,
     SolveFast.hist5_one(g0, g1, g2, g3, g4, w, s2, gen, m, k),
     SolveFast.hist5_one(g0, g1, g2, g3, g4, w, s1, gen, m, k), es1_eq) :
    FH.HistSpec(gw, w <> rest, fg0, gen,
      SolveFast.hist5_go(g0, g1, g2, g3, g4, rest, gen,
        SolveFast.hist5_one(g0, g1, g2, g3, g4, w, s1, gen, m, k)))
  FH.hist5_go_step_dup(g0, g1, g2, g3, g4, w, rest, fg0, gen,
    SolveFast.hist5_one(g0, g1, g2, g3, g4, w, s1, gen, m, k),
    FH.hist_one_transport(gw, w, fg0, gen,
      SolveFast.hist5_one(g0, g1, g2, g3, g4, w, s2, gen, m, k),
      SolveFast.hist5_one(g0, g1, g2, g3, g4, w, s1, gen, m, k),
      es1_eq, h1_s2),
    rec)

def FH.hist5_go_spec(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +S: +List<+List<Nat>>, +fg0: +List<SolveFast.FGroup>,
    seen: Array<Nat>, +gen: Nat, +m: Nat, +k: Nat,
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg0)) ->
  FH.HistSpec(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), S, fg0, gen,
    SolveFast.hist5_go(g0, g1, g2, g3, g4, S, gen,
      SolveFast.Hist5Ok{seen, m, k})):
  match S:
    case Nil{}:
      +hle : {Nat.is_le(m, FH.fgroups_total(fg0)) == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(FH.fgroups_total(fg0), FH.fgroups_total(fg0),
          m, Equal.sym(Nat, m, FH.fgroups_total(fg0), hm),
          NatProof.Nat.is_le_refl(FH.fgroups_total(fg0)))
      Arr.DPair{hs, Arr.DPair{{==}, Arr.DPair{hwf,
        Arr.DPair{hm, Arr.DPair{hk, hle}}}}}
    case Con{+w, +rest}:
      +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
      +fg1 = SolveFast.fgroups_next_acc(gw, w, fg0,
               SolveFast.word_eq_fast(gw, w))
      FH.hist5_go_cons_dup(g0, g1, g2, g3, g4, w, rest, fg0, seen, gen, m, k,
        hwf, hm, hk, hs, Arr.Arr.dup(Nat, seen),
        s2 => m2 => k2 => hwf1 => hm2 => hk2 => hs2 =>
          FH.hist5_go_spec(g0, g1, g2, g3, g4, rest, fg1, s2, gen, m2, k2,
            hwf1, hm2, hk2, hs2))


# ---------------------------------------------------------------------------
# Symbolic depth-indexed invariant `FH.BktTree` for `buckets`
# ---------------------------------------------------------------------------

def FH.BktTree(+d: Nat, +base: U32, a: Array<+List<+List<Nat>>>,
               +fg: +List<SolveFast.FGroup>) -> Data:
  match d:
    case 0n:
      match a:
        case ALeaf{v}:
          {v == FH.lookup_code(base, fg) : +List<+List<Nat>>}
        case ANode{xs, ys}:
          Empty
    case 1n++p:
      match a:
        case ALeaf{v}:
          Empty
        case ANode{xs, ys}:
          Arr.Arr.DPair<
            FH.BktTree(p, base, xs, fg),
            FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg)>

def FH.bkt_tree_transport(+d: Nat, +base: U32,
    -a1: Array<+List<+List<Nat>>>, -a2: Array<+List<+List<Nat>>>,
    +fg: +List<SolveFast.FGroup>,
    +ea: {a1 == a2 : Array<+List<+List<Nat>>>},
    +hb: FH.BktTree(d, base, a1, fg)) ->
  FH.BktTree(d, base, a2, fg):
  %ea : FH.BktTree(d, base, _, fg)
  hb

def FH.bkt_tree_transport_fg(+d: Nat, +base: U32,
    -a: Array<+List<+List<Nat>>>,
    +fg1: +List<SolveFast.FGroup>, +fg2: +List<SolveFast.FGroup>,
    +efg: {fg1 == fg2 : +List<SolveFast.FGroup>},
    +hb: FH.BktTree(d, base, a, fg1)) ->
  FH.BktTree(d, base, a, fg2):
  %efg : FH.BktTree(d, base, a, _)
  hb

def FH.bkt_tree_depth(+d: Nat, +base: U32, a: Array<+List<+List<Nat>>>,
    +fg: +List<SolveFast.FGroup>, +hb: FH.BktTree(d, base, a, fg)) ->
  Arr.Arr.Depth(+List<+List<Nat>>, d, a):
  match d:
    case 0n:
      match a:
        case ALeaf{v}:
          Unit{}
        case ANode{xs, ys}:
          hb
    case 1n++p:
      match a:
        case ALeaf{v}:
          hb
        case ANode{xs, ys}:
          +hxs = Arr.Arr.dpair_l(
                   FH.BktTree(p, base, xs, fg),
                   FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg), hb)
          +hys = Arr.Arr.dpair_r(
                   FH.BktTree(p, base, xs, fg),
                   FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg), hb)
          Arr.DPair{
            FH.bkt_tree_depth(p, base, xs, fg, hxs),
            FH.bkt_tree_depth(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg,
              hys)}

def FH.bkt_tree_new(+d: Nat, +base: U32) ->
  FH.BktTree(d, base, Array.new(+List<+List<Nat>>, d, Nil{}), Nil{}):
  match d:
    case 0n:
      {==}
    case 1n++p:
      Arr.DPair{
        FH.bkt_tree_new(p, base),
        FH.bkt_tree_new(p, U32.or(base, Arr.Arr.pow2_u32(p)))}

# Reading `buckets` at `code` returns `FH.lookup_code(code, fg)`.
def FH.bkt_get_lo(-ys: Array<+List<+List<Nat>>>,
    r: Array<+List<+List<Nat>>> & +List<+List<Nat>>,
    +fg: +List<SolveFast.FGroup>, +c: U32,
    +hr: {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>, r)
          == FH.lookup_code(c, fg) : +List<+List<Nat>>}) ->
  {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
     Array.swap.lo(+List<+List<Nat>>, ys, r))
   == FH.lookup_code(c, fg) : +List<+List<Nat>>}:
  (a, +v) = r
  hr

def FH.bkt_get_hi(-xs: Array<+List<+List<Nat>>>,
    r: Array<+List<+List<Nat>>> & +List<+List<Nat>>,
    +fg: +List<SolveFast.FGroup>, +c: U32,
    +hr: {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>, r)
          == FH.lookup_code(c, fg) : +List<+List<Nat>>}) ->
  {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
     Array.swap.hi(+List<+List<Nat>>, xs, r))
   == FH.lookup_code(c, fg) : +List<+List<Nat>>}:
  (a, +v) = r
  hr

def FH.bkt_tree_get_go_lo(+p: Nat, +base: U32,
    -xs: Array<+List<+List<Nat>>>, -ys: Array<+List<+List<Nat>>>,
    +fg: +List<SolveFast.FGroup>, +i: U32,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +hxs: FH.BktTree(p, base, xs, fg),
    d: &a1: Array<+List<+List<Nat>>> -> &a2: Array<+List<+List<Nat>>> ->
       {a1 == xs : Array<+List<+List<Nat>>>}
       & {a2 == a1 : Array<+List<+List<Nat>>>},
    ih: @xs2: Array<+List<+List<Nat>>> -> FH.BktTree(p, base, xs2, fg) ->
        {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
           Array.get.go(+List<+List<Nat>>, xs2, Arr.Arr.pow2_u32(p), i,
             U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))))
         == FH.lookup_code(U32.or(base, i), fg) : +List<+List<Nat>>}) ->
  {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
     Array.get.go(+List<+List<Nat>>, ANode{xs, ys}, Arr.Arr.pow2_u32(1n+p), i,
       True{}))
   == FH.lookup_code(U32.or(base, i), fg) : +List<+List<Nat>>}:
  (xs1, d2) = d
  (xs2, pe) = d2
  (+ex1, +ex2) = pe
  +hxs2 = FH.bkt_tree_transport(p, base, xs, xs2, fg,
            Equal.sym(Array<+List<+List<Nat>>>, xs2, xs,
              Equal.trans(Array<+List<+List<Nat>>>, xs2, xs1, xs, ex2, ex1)),
            hxs)
  +h2 = ih(xs2, hxs2)
  +h1 : {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
           Array.get.go(+List<+List<Nat>>, xs1, Arr.Arr.pow2_u32(p), i,
             U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))))
         == FH.lookup_code(U32.or(base, i), fg) : +List<+List<Nat>>} =
    Equal.trans(+List<+List<Nat>>,
      Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.get.go(+List<+List<Nat>>, xs1, Arr.Arr.pow2_u32(p), i,
          U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
      Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.get.go(+List<+List<Nat>>, xs2, Arr.Arr.pow2_u32(p), i,
          U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
      FH.lookup_code(U32.or(base, i), fg),
      Equal.cong(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        x => Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
               Array.get.go(+List<+List<Nat>>, x, Arr.Arr.pow2_u32(p), i,
                 U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
        xs1, xs2, Equal.sym(Array<+List<+List<Nat>>>, xs2, xs1, ex2)),
      h2)
  %ex1 : {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
            Array.get.go(+List<+List<Nat>>, ANode{_, ys},
              Arr.Arr.pow2_u32(1n+p), i, True{}))
          == FH.lookup_code(U32.or(base, i), fg) : +List<+List<Nat>>}
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
       Array.swap.lo(+List<+List<Nat>>, ys,
         Array.get.go(+List<+List<Nat>>, xs1, _, i,
           U32.is_lt(i, U32.shr(_)))))
     == FH.lookup_code(U32.or(base, i), fg) : +List<+List<Nat>>}
  FH.bkt_get_lo(ys,
    Array.get.go(+List<+List<Nat>>, xs1, Arr.Arr.pow2_u32(p), i,
      U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))),
    fg, U32.or(base, i), h1)

def FH.bkt_tree_get_go_hi(+p: Nat, +base: U32,
    -xs: Array<+List<+List<Nat>>>, -ys: Array<+List<+List<Nat>>>,
    +fg: +List<SolveFast.FGroup>, +i: U32,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +eb2: {U32.or(U32.or(base, Arr.Arr.pow2_u32(p)),
                  U32.sub(i, Arr.Arr.pow2_u32(p))) == U32.or(base, i) : U32},
    +hys: FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg),
    d: &a1: Array<+List<+List<Nat>>> -> &a2: Array<+List<+List<Nat>>> ->
       {a1 == ys : Array<+List<+List<Nat>>>}
       & {a2 == a1 : Array<+List<+List<Nat>>>},
    ih: @ys2: Array<+List<+List<Nat>>> ->
        FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys2, fg) ->
        {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
           Array.get.go(+List<+List<Nat>>, ys2, Arr.Arr.pow2_u32(p),
             U32.sub(i, Arr.Arr.pow2_u32(p)),
             U32.is_lt(U32.sub(i, Arr.Arr.pow2_u32(p)),
               U32.shr(Arr.Arr.pow2_u32(p)))))
         == FH.lookup_code(
              U32.or(U32.or(base, Arr.Arr.pow2_u32(p)),
                     U32.sub(i, Arr.Arr.pow2_u32(p))), fg)
         : +List<+List<Nat>>}) ->
  {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
     Array.get.go(+List<+List<Nat>>, ANode{xs, ys}, Arr.Arr.pow2_u32(1n+p), i,
       False{}))
   == FH.lookup_code(U32.or(base, i), fg) : +List<+List<Nat>>}:
  (ys1, d2) = d
  (ys2, pe) = d2
  (+ey1, +ey2) = pe
  +base2 = U32.or(base, Arr.Arr.pow2_u32(p))
  +ip = U32.sub(i, Arr.Arr.pow2_u32(p))
  +hys2 = FH.bkt_tree_transport(p, base2, ys, ys2, fg,
            Equal.sym(Array<+List<+List<Nat>>>, ys2, ys,
              Equal.trans(Array<+List<+List<Nat>>>, ys2, ys1, ys, ey2, ey1)),
            hys)
  +h2 = ih(ys2, hys2)
  +h1 : {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
           Array.get.go(+List<+List<Nat>>, ys1, Arr.Arr.pow2_u32(p), ip,
             U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))))
         == FH.lookup_code(U32.or(base, i), fg) : +List<+List<Nat>>} =
    Equal.trans(+List<+List<Nat>>,
      Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.get.go(+List<+List<Nat>>, ys1, Arr.Arr.pow2_u32(p), ip,
          U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
      FH.lookup_code(U32.or(base2, ip), fg),
      FH.lookup_code(U32.or(base, i), fg),
      Equal.trans(+List<+List<Nat>>,
        Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
          Array.get.go(+List<+List<Nat>>, ys1, Arr.Arr.pow2_u32(p), ip,
            U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
        Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
          Array.get.go(+List<+List<Nat>>, ys2, Arr.Arr.pow2_u32(p), ip,
            U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
        FH.lookup_code(U32.or(base2, ip), fg),
        Equal.cong(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
          y => Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                 Array.get.go(+List<+List<Nat>>, y, Arr.Arr.pow2_u32(p), ip,
                   U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
          ys1, ys2, Equal.sym(Array<+List<+List<Nat>>>, ys2, ys1, ey2)),
        h2),
      Equal.cong(U32, +List<+List<Nat>>, c => FH.lookup_code(c, fg),
        U32.or(base2, ip), U32.or(base, i), eb2))
  %ey1 : {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
            Array.get.go(+List<+List<Nat>>, ANode{xs, _},
              Arr.Arr.pow2_u32(1n+p), i, False{}))
          == FH.lookup_code(U32.or(base, i), fg) : +List<+List<Nat>>}
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
       Array.swap.hi(+List<+List<Nat>>, xs,
         Array.get.go(+List<+List<Nat>>, ys1, _, U32.sub(i, _),
           U32.is_lt(U32.sub(i, _), U32.shr(_)))))
     == FH.lookup_code(U32.or(base, i), fg) : +List<+List<Nat>>}
  FH.bkt_get_hi(xs,
    Array.get.go(+List<+List<Nat>>, ys1, Arr.Arr.pow2_u32(p), ip,
      U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))),
    fg, U32.or(base, i), h1)

def FH.bkt_tree_get_go(+d: Nat, +base: U32, a: Array<+List<+List<Nat>>>,
    +fg: +List<SolveFast.FGroup>, +i: U32, z: Bool,
    +ez: {z == U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(d))) : Bool},
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.Arr.u32_zero_from(d, i) == True{} : Bool},
    +hb: FH.BktTree(d, base, a, fg)) ->
  {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
     Array.get.go(+List<+List<Nat>>, a, Arr.Arr.pow2_u32(d), i, z))
   == FH.lookup_code(U32.or(base, i), fg) : +List<+List<Nat>>}:
  match d:
    case 0n:
      match a:
        case ALeaf{+v}:
          +ei0 : {i == 0 : U32} = Arr.Arr.u32_eq_zero(i, zi)
          +eor : {U32.or(base, i) == base : U32} =
            Equal.trans(U32, U32.or(base, i), U32.or(base, 0), base,
              Equal.cong(U32, U32, x => U32.or(base, x), i, 0, ei0),
              FF5.FF5.u32_or_zero_r(base))
          Equal.trans(+List<+List<Nat>>, v, FH.lookup_code(base, fg),
            FH.lookup_code(U32.or(base, i), fg), hb,
            Equal.cong(U32, +List<+List<Nat>>, c => FH.lookup_code(c, fg),
              base, U32.or(base, i),
              Equal.sym(U32, U32.or(base, i), base, eor)))
        case ANode{xs, ys}:
          Empty.absurd(
            {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
               Array.get.go(+List<+List<Nat>>, ANode{xs, ys},
                 Arr.Arr.pow2_u32(0n), i, z))
             == FH.lookup_code(U32.or(base, i), fg) : +List<+List<Nat>>}, hb)
    case 1n++p:
      match a:
        case ALeaf{v}:
          Empty.absurd(
            {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
               Array.get.go(+List<+List<Nat>>, ALeaf{v},
                 Arr.Arr.pow2_u32(1n+p), i, z))
             == FH.lookup_code(U32.or(base, i), fg) : +List<+List<Nat>>}, hb)
        case ANode{xs, ys}:
          match z:
            case True{}:
              +hxs = Arr.Arr.dpair_l(
                       FH.BktTree(p, base, xs, fg),
                       FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg),
                       hb)
              +plt : {Nat.is_lt(p, 32n) == True{} : Bool} =
                NatProof.Nat.is_le_lt_trans(p, 1n+p, 32n,
                  NatProof.Nat.is_le_of_lt(p, 1n+p,
                    NatProof.Nat.is_lt_succ_self(p)), hlt)
              +eshr : {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p)
                       : U32} =
                Arr.Arr.u32_shr_pow2(p, hlt)
              +ilt : {U32.is_lt(i, Arr.Arr.pow2_u32(p)) == True{} : Bool} =
                Equal.trans(Bool,
                  U32.is_lt(i, Arr.Arr.pow2_u32(p)),
                  U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))),
                  True{},
                  Equal.cong(U32, Bool, x => U32.is_lt(i, x),
                    Arr.Arr.pow2_u32(p), U32.shr(Arr.Arr.pow2_u32(1n+p)),
                    Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)),
                      Arr.Arr.pow2_u32(p), eshr)),
                  Equal.sym(Bool, True{},
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))), ez))
              +zip : {Arr.Arr.u32_zero_from(p, i) == True{} : Bool} =
                Arr.Arr.u32_zero_from_lt(p, i, zi, plt, ilt)
              FH.bkt_tree_get_go_lo(p, base, xs, ys, fg, i, eshr, hxs,
                Arr.Arr.dup(+List<+List<Nat>>, xs),
                xs2 => hxs2 =>
                  FH.bkt_tree_get_go(p, base, xs2, fg, i,
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, hxs2))
            case False{}:
              +hys = Arr.Arr.dpair_r(
                       FH.BktTree(p, base, xs, fg),
                       FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg),
                       hb)
              +plt : {Nat.is_lt(p, 32n) == True{} : Bool} =
                NatProof.Nat.is_le_lt_trans(p, 1n+p, 32n,
                  NatProof.Nat.is_le_of_lt(p, 1n+p,
                    NatProof.Nat.is_lt_succ_self(p)), hlt)
              +eshr : {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p)
                       : U32} =
                Arr.Arr.u32_shr_pow2(p, hlt)
              +ige : {U32.is_lt(i, Arr.Arr.pow2_u32(p)) == False{} : Bool} =
                Equal.trans(Bool,
                  U32.is_lt(i, Arr.Arr.pow2_u32(p)),
                  U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))),
                  False{},
                  Equal.cong(U32, Bool, x => U32.is_lt(i, x),
                    Arr.Arr.pow2_u32(p), U32.shr(Arr.Arr.pow2_u32(1n+p)),
                    Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)),
                      Arr.Arr.pow2_u32(p), eshr)),
                  Equal.sym(Bool, False{},
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))), ez))
              +ip = U32.sub(i, Arr.Arr.pow2_u32(p))
              +zip : {Arr.Arr.u32_zero_from(p, ip) == True{} : Bool} =
                Arr.Arr.u32_zero_from_ge(p, i, zi, plt, ige)
              +eb2 : {U32.or(U32.or(base, Arr.Arr.pow2_u32(p)), ip)
                      == U32.or(base, i) : U32} =
                FH.u32_or_base_sub(p, base, i, zi, plt, ige)
              FH.bkt_tree_get_go_hi(p, base, xs, ys, fg, i, eshr, eb2,
                hys, Arr.Arr.dup(+List<+List<Nat>>, ys),
                ys2 => hys2 =>
                  FH.bkt_tree_get_go(p, U32.or(base, Arr.Arr.pow2_u32(p)),
                    ys2, fg, ip,
                    U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, hys2))

def FH.bkt_tree_get_dup2(-bkts: Array<+List<+List<Nat>>>,
    a1: Array<+List<+List<Nat>>>, +fg: +List<SolveFast.FGroup>, +code: U32,
    +ea1: {a1 == bkts : Array<+List<+List<Nat>>>},
    -a2: Array<+List<+List<Nat>>>,
    +ea2: {a2 == a1 : Array<+List<+List<Nat>>>},
    dp2: &b1: Array<+List<+List<Nat>>> -> &b2: Array<+List<+List<Nat>>> ->
         {b1 == a2 : Array<+List<+List<Nat>>>}
         & {b2 == b1 : Array<+List<+List<Nat>>>},
    +zc: {Arr.Arr.u32_zero_from(10n, code) == True{} : Bool},
    +hb: FH.BktTree(10n, 0, bkts, fg)) ->
  {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
     Array.get(+List<+List<Nat>>, bkts, code))
   == FH.lookup_code(code, fg) : +List<+List<Nat>>}:
  (b1, dp3) = dp2
  (b2, pe2) = dp3
  (+eb1, +eb2) = pe2
  +ea_b1 : {b1 == a1 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, b1, a2, a1, eb1, ea2)
  +ea_b2 : {b2 == a1 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, b2, b1, a1, eb2, ea_b1)
  +hb1 = FH.bkt_tree_transport(10n, 0, bkts, a1, fg,
           Equal.sym(Array<+List<+List<Nat>>>, a1, bkts, ea1), hb)
  +hb_b1 = FH.bkt_tree_transport(10n, 0, a1, b1, fg,
             Equal.sym(Array<+List<+List<Nat>>>, b1, a1, ea_b1), hb1)
  +hd_b1 = FH.bkt_tree_depth(10n, 0, b1, fg, hb_b1)
  +hd_b2 = Arr.Arr.depth_transport(+List<+List<Nat>>, 10n, b1, b2,
             Equal.sym(Array<+List<+List<Nat>>>, b2, b1, eb2), hd_b1)
  +em : {U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)) == code : U32} =
    Arr.Arr.u32_and_mask(10n, code, zc)
  +eg : {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
           Array.get(+List<+List<Nat>>, b2, code))
         == Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
              Array.get.go(+List<+List<Nat>>, b2, Arr.Arr.pow2_u32(10n), code,
                U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))
         : +List<+List<Nat>>} =
    Equal.trans(+List<+List<Nat>>,
      Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.get(+List<+List<Nat>>, b2, code)),
      Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.get.go(+List<+List<Nat>>, b2, Arr.Arr.pow2_u32(10n),
          U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)),
          U32.is_lt(U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)),
            U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.get.go(+List<+List<Nat>>, b2, Arr.Arr.pow2_u32(10n), code,
          U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.get_depth(+List<+List<Nat>>, 10n, b2, code, hd_b2),
      Equal.cong(U32, +List<+List<Nat>>,
        j => Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
               Array.get.go(+List<+List<Nat>>, b2, Arr.Arr.pow2_u32(10n), j,
                 U32.is_lt(j, U32.shr(Arr.Arr.pow2_u32(10n))))),
        U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)), code, em))
  +ego = FH.bkt_tree_get_go(10n, 0, a1, fg, code,
           U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))), {==}, {==}, zc,
           hb1)
  +e0c : {U32.or(0, code) == code : U32} = FF5.FF5.u32_or_zero_l(code)
  %ea1 : {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
            Array.get(+List<+List<Nat>>, _, code))
          == FH.lookup_code(code, fg) : +List<+List<Nat>>}
  %ea_b2 : {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
              Array.get(+List<+List<Nat>>, _, code))
            == FH.lookup_code(code, fg) : +List<+List<Nat>>}
  Equal.trans(+List<+List<Nat>>,
    Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
      Array.get(+List<+List<Nat>>, b2, code)),
    Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
      Array.get.go(+List<+List<Nat>>, a1, Arr.Arr.pow2_u32(10n), code,
        U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
    FH.lookup_code(code, fg),
    Equal.trans(+List<+List<Nat>>,
      Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.get(+List<+List<Nat>>, b2, code)),
      Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.get.go(+List<+List<Nat>>, b2, Arr.Arr.pow2_u32(10n), code,
          U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.get.go(+List<+List<Nat>>, a1, Arr.Arr.pow2_u32(10n), code,
          U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      eg,
      Equal.cong(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        x => Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
               Array.get.go(+List<+List<Nat>>, x, Arr.Arr.pow2_u32(10n), code,
                 U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
        b2, a1, ea_b2)),
    Equal.trans(+List<+List<Nat>>,
      Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.get.go(+List<+List<Nat>>, a1, Arr.Arr.pow2_u32(10n), code,
          U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      FH.lookup_code(U32.or(0, code), fg),
      FH.lookup_code(code, fg),
      ego,
      Equal.cong(U32, +List<+List<Nat>>, c => FH.lookup_code(c, fg),
        U32.or(0, code), code, e0c)))

def FH.bkt_tree_get_dup(-bkts: Array<+List<+List<Nat>>>,
    +fg: +List<SolveFast.FGroup>, +code: U32,
    +zc: {Arr.Arr.u32_zero_from(10n, code) == True{} : Bool},
    +hb: FH.BktTree(10n, 0, bkts, fg),
    dp: &a1: Array<+List<+List<Nat>>> -> &a2: Array<+List<+List<Nat>>> ->
        {a1 == bkts : Array<+List<+List<Nat>>>}
        & {a2 == a1 : Array<+List<+List<Nat>>>}) ->
  {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
     Array.get(+List<+List<Nat>>, bkts, code))
   == FH.lookup_code(code, fg) : +List<+List<Nat>>}:
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  FH.bkt_tree_get_dup2(bkts, a1, fg, code, ea1, a2, ea2,
    Arr.Arr.dup(+List<+List<Nat>>, a2), zc, hb)

def FH.bkt_tree_get(bkts: Array<+List<+List<Nat>>>,
    +fg: +List<SolveFast.FGroup>, +code: U32,
    +zc: {Arr.Arr.u32_zero_from(10n, code) == True{} : Bool},
    +hb: FH.BktTree(10n, 0, bkts, fg)) ->
  {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
     Array.get(+List<+List<Nat>>, bkts, code))
   == FH.lookup_code(code, fg) : +List<+List<Nat>>}:
  FH.bkt_tree_get_dup(bkts, fg, code, zc, hb,
    Arr.Arr.dup(+List<+List<Nat>>, bkts))

# Unified bucket-update tag (`OpAdd` for `fill5`, `OpClear` for `drain5`) so
# the `BktTree` swap proof is written once and reused by both passes.
type FH.BktOp is Data:
  OpAdd{w: +List<Nat>, fb: +List<Feedback.Color>}
  OpClear{gp: SolveFast.FGroup}

def FH.bkt_op_code(op: FH.BktOp) -> U32:
  match op:
    case OpAdd{w, fb}:
      FF5.FF5.encode_fb5_list(fb)
    case OpClear{gp}:
      match gp:
        case SolveFast.FGroup{f, len, rws}:
          FF5.FF5.encode_fb5_list(f)

def FH.bkt_op_src(op: FH.BktOp, +fg: +List<SolveFast.FGroup>) ->
  +List<SolveFast.FGroup>:
  match op:
    case OpAdd{w, fb}:
      fg
    case OpClear{gp}:
      List.append(&2, SolveFast.FGroup, fg, gp <> Nil{})

def FH.bkt_op_dst(op: FH.BktOp, +fg: +List<SolveFast.FGroup>) ->
  +List<SolveFast.FGroup>:
  match op:
    case OpAdd{w, fb}:
      SolveFast.fgroup_add_fast(w, fb, fg)
    case OpClear{gp}:
      fg

def FH.bkt_op_val(op: FH.BktOp, +fg: +List<SolveFast.FGroup>) ->
  +List<+List<Nat>>:
  match op:
    case OpAdd{w, fb}:
      w <> FH.lookup_code(FF5.FF5.encode_fb5_list(fb), fg)
    case OpClear{gp}:
      Nil{}

def FH.bkt_op_ok(op: FH.BktOp, +fg: +List<SolveFast.FGroup>) -> Bool:
  match op:
    case OpAdd{w, fb}:
      Bool.and(FF5.FF5.is_fb5(fb), FH.fgroups_wf(fg))
    case OpClear{gp}:
      match gp:
        case SolveFast.FGroup{+f, len, rws}:
          Bool.and(FF5.FF5.is_fb5(f),
            Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), fg)))

def FH.lookup_append_other(+j: U32, +fg: +List<SolveFast.FGroup>,
    +gp: SolveFast.FGroup,
    +hne: {U32.is_eq(j, FH.bkt_op_code(OpClear{gp})) == False{} : Bool}) ->
  {FH.lookup_code(j, List.append(&2, SolveFast.FGroup, fg, gp <> Nil{}))
   == FH.lookup_code(j, fg) : +List<+List<Nat>>}:
  match fg:
    case Nil{}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          Equal.cong(Bool, +List<+List<Nat>>,
            b => Feedback.Bool.case(+List<+List<Nat>>, b, rws, Nil{}),
            U32.is_eq(j, FF5.FF5.encode_fb5_list(f)), False{}, hne)
    case Con{h, rest}:
      match h:
        case SolveFast.FGroup{+fh, +lh, +rh}:
          Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
            x => Feedback.Bool.case(+List<+List<Nat>>,
                   U32.is_eq(j, FF5.FF5.encode_fb5_list(fh)), rh, x),
            FH.lookup_code(j, List.append(&2, SolveFast.FGroup, rest,
              gp <> Nil{})),
            FH.lookup_code(j, rest),
            FH.lookup_append_other(j, rest, gp, hne))

def FH.lookup_nil_of_not_has(+c: U32, +fg: +List<SolveFast.FGroup>,
    +hnh: {FH.has_code(c, fg) == False{} : Bool}) ->
  {FH.lookup_code(c, fg) == Nil{} : +List<+List<Nat>>}:
  match fg:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          +h1 : {U32.is_eq(c, FF5.FF5.encode_fb5_list(f)) == False{} : Bool} =
            FH.bool_or_false_l_inv(U32.is_eq(c, FF5.FF5.encode_fb5_list(f)),
              FH.has_code(c, rest), hnh)
          +h2 : {FH.has_code(c, rest) == False{} : Bool} =
            FH.bool_or_false_r_inv(U32.is_eq(c, FF5.FF5.encode_fb5_list(f)),
              FH.has_code(c, rest), hnh)
          Equal.trans(+List<+List<Nat>>,
            Feedback.Bool.case(+List<+List<Nat>>,
              U32.is_eq(c, FF5.FF5.encode_fb5_list(f)),
              rws, FH.lookup_code(c, rest)),
            FH.lookup_code(c, rest),
            Nil{},
            Equal.cong(Bool, +List<+List<Nat>>,
              b => Feedback.Bool.case(+List<+List<Nat>>, b,
                     rws, FH.lookup_code(c, rest)),
              U32.is_eq(c, FF5.FF5.encode_fb5_list(f)), False{}, h1),
            FH.lookup_nil_of_not_has(c, rest, h2))

def FH.lookup_append_last(+fg: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), fg) == False{} : Bool}) ->
  {FH.lookup_code(FF5.FF5.encode_fb5_list(f),
     List.append(&2, SolveFast.FGroup, fg,
       SolveFast.FGroup{f, len, rws} <> Nil{}))
   == rws : +List<+List<Nat>>}:
  match fg:
    case Nil{}:
      Equal.cong(Bool, +List<+List<Nat>>,
        b => Feedback.Bool.case(+List<+List<Nat>>, b, rws, Nil{}),
        U32.is_eq(FF5.FF5.encode_fb5_list(f), FF5.FF5.encode_fb5_list(f)),
        True{}, Arr.Arr.u32_is_eq_refl(FF5.FF5.encode_fb5_list(f)))
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+fh, +lh, +rh}:
          +c = FF5.FF5.encode_fb5_list(f)
          +h1 : {U32.is_eq(c, FF5.FF5.encode_fb5_list(fh)) == False{} : Bool} =
            FH.bool_or_false_l_inv(U32.is_eq(c, FF5.FF5.encode_fb5_list(fh)),
              FH.has_code(c, rest), hnh)
          +h2 : {FH.has_code(c, rest) == False{} : Bool} =
            FH.bool_or_false_r_inv(U32.is_eq(c, FF5.FF5.encode_fb5_list(fh)),
              FH.has_code(c, rest), hnh)
          Equal.trans(+List<+List<Nat>>,
            Feedback.Bool.case(+List<+List<Nat>>,
              U32.is_eq(c, FF5.FF5.encode_fb5_list(fh)), rh,
              FH.lookup_code(c,
                List.append(&2, SolveFast.FGroup, rest,
                  SolveFast.FGroup{f, len, rws} <> Nil{}))),
            FH.lookup_code(c,
              List.append(&2, SolveFast.FGroup, rest,
                SolveFast.FGroup{f, len, rws} <> Nil{})),
            rws,
            Equal.cong(Bool, +List<+List<Nat>>,
              b => Feedback.Bool.case(+List<+List<Nat>>, b, rh,
                     FH.lookup_code(c,
                       List.append(&2, SolveFast.FGroup, rest,
                         SolveFast.FGroup{f, len, rws} <> Nil{}))),
              U32.is_eq(c, FF5.FF5.encode_fb5_list(fh)), False{}, h1),
            FH.lookup_append_last(rest, f, len, rws, h2))

def FH.bkt_op_other(+op: FH.BktOp, +fg: +List<SolveFast.FGroup>, +j: U32,
    +hok: {FH.bkt_op_ok(op, fg) == True{} : Bool},
    +hne: {U32.is_eq(j, FH.bkt_op_code(op)) == False{} : Bool}) ->
  {FH.lookup_code(j, FH.bkt_op_dst(op, fg))
   == FH.lookup_code(j, FH.bkt_op_src(op, fg)) : +List<+List<Nat>>}:
  match op:
    case OpAdd{+w, +fb}:
      +hfb = Logic.Proof.and_true_l(FF5.FF5.is_fb5(fb), FH.fgroups_wf(fg), hok)
      +hwf = Logic.Proof.and_true_r(FF5.FF5.is_fb5(fb), FH.fgroups_wf(fg), hok)
      FH.fgroup_add_lookup_other(w, fb, fg,
        SolveFast.next_fgroup_hit(fb, fg), j, {==}, hfb, hwf, hne)
    case OpClear{+gp}:
      Equal.sym(+List<+List<Nat>>,
        FH.lookup_code(j, List.append(&2, SolveFast.FGroup, fg, gp <> Nil{})),
        FH.lookup_code(j, fg),
        FH.lookup_append_other(j, fg, gp, hne))

def FH.add_facts_lkp_self(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +fg: +List<SolveFast.FGroup>, +fg2: +List<SolveFast.FGroup>,
    f: FH.AddFacts<w, fb, fg, fg2>) ->
  {FH.lookup_code(FF5.FF5.encode_fb5_list(fb), fg2)
   == w <> FH.lookup_code(FF5.FF5.encode_fb5_list(fb), fg)
   : +List<+List<Nat>>}:
  match f:
    case AddFacts{wf2, tot2, cnt2, has_self, lkp_self}:
      lkp_self

def FH.bkt_op_self(+op: FH.BktOp, +fg: +List<SolveFast.FGroup>,
    +hok: {FH.bkt_op_ok(op, fg) == True{} : Bool}) ->
  {FH.bkt_op_val(op, fg)
   == FH.lookup_code(FH.bkt_op_code(op), FH.bkt_op_dst(op, fg))
   : +List<+List<Nat>>}:
  match op:
    case OpAdd{+w, +fb}:
      +hfb = Logic.Proof.and_true_l(FF5.FF5.is_fb5(fb), FH.fgroups_wf(fg), hok)
      +hwf = Logic.Proof.and_true_r(FF5.FF5.is_fb5(fb), FH.fgroups_wf(fg), hok)
      Equal.sym(+List<+List<Nat>>,
        FH.lookup_code(FF5.FF5.encode_fb5_list(fb),
          SolveFast.fgroup_add_fast(w, fb, fg)),
        w <> FH.lookup_code(FF5.FF5.encode_fb5_list(fb), fg),
        FH.add_facts_lkp_self(w, fb, fg, SolveFast.fgroup_add_fast(w, fb, fg),
          FH.fgroup_add_facts(w, fb, fg, SolveFast.next_fgroup_hit(fb, fg),
            {==}, hfb, hwf)))
    case OpClear{+gp}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          +hnh : {FH.has_code(FF5.FF5.encode_fb5_list(f), fg)
                  == False{} : Bool} =
            Arr.Arr.bool_not_true(FH.has_code(FF5.FF5.encode_fb5_list(f), fg),
              Logic.Proof.and_true_r(FF5.FF5.is_fb5(f),
                Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), fg)), hok))
          Equal.sym(+List<+List<Nat>>,
            FH.lookup_code(FF5.FF5.encode_fb5_list(f), fg), Nil{},
            FH.lookup_nil_of_not_has(FF5.FF5.encode_fb5_list(f), fg, hnh))

def FH.bkt_op_zero_from(+op: FH.BktOp, +fg: +List<SolveFast.FGroup>,
    +hok: {FH.bkt_op_ok(op, fg) == True{} : Bool}) ->
  {Arr.Arr.u32_zero_from(10n, FH.bkt_op_code(op)) == True{} : Bool}:
  match op:
    case OpAdd{+w, +fb}:
      FF5.FF5.encode_fb5_list_zero_from(fb,
        Logic.Proof.and_true_l(FF5.FF5.is_fb5(fb), FH.fgroups_wf(fg), hok))
    case OpClear{+gp}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          FF5.FF5.encode_fb5_list_zero_from(f,
            Logic.Proof.and_true_l(FF5.FF5.is_fb5(f),
              Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), fg)), hok))

def FH.bkt_tree_other(+d: Nat, +base: U32, a: Array<+List<+List<Nat>>>,
    +op: FH.BktOp, +fg: +List<SolveFast.FGroup>, +k: Nat, +bval: Bool,
    +hok: {FH.bkt_op_ok(op, fg) == True{} : Bool},
    +hle: {Nat.is_le(d, k) == True{} : Bool},
    +hbb: {FH.u32_bit(k, base) == bval : Bool},
    +hbc: {FH.u32_bit(k, FH.bkt_op_code(op)) == Bool.not(bval) : Bool},
    +hb: FH.BktTree(d, base, a, FH.bkt_op_src(op, fg))) ->
  FH.BktTree(d, base, a, FH.bkt_op_dst(op, fg)):
  match d:
    case 0n:
      match a:
        case ALeaf{+v}:
          +hne : {U32.is_eq(base, FH.bkt_op_code(op)) == False{} : Bool} =
            FH.u32_ne_of_bit_val(k, base, FH.bkt_op_code(op), bval, hbb, hbc)
          Equal.trans(+List<+List<Nat>>, v,
            FH.lookup_code(base, FH.bkt_op_src(op, fg)),
            FH.lookup_code(base, FH.bkt_op_dst(op, fg)),
            hb,
            Equal.sym(+List<+List<Nat>>,
              FH.lookup_code(base, FH.bkt_op_dst(op, fg)),
              FH.lookup_code(base, FH.bkt_op_src(op, fg)),
              FH.bkt_op_other(op, fg, base, hok, hne)))
        case ANode{xs, ys}:
          hb
    case 1n++p:
      match a:
        case ALeaf{v}:
          hb
        case ANode{xs, ys}:
          +src = FH.bkt_op_src(op, fg)
          +hxs = Arr.Arr.dpair_l(
                   FH.BktTree(p, base, xs, src),
                   FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, src),
                   hb)
          +hys = Arr.Arr.dpair_r(
                   FH.BktTree(p, base, xs, src),
                   FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, src),
                   hb)
          +hpk : {Nat.is_lt(p, k) == True{} : Bool} =
            NatProof.Nat.is_lt_le_trans(p, 1n+p, k,
              NatProof.Nat.is_lt_succ_self(p), hle)
          +hple : {Nat.is_le(p, k) == True{} : Bool} =
            NatProof.Nat.is_le_of_lt(p, k, hpk)
          +hbb2 : {FH.u32_bit(k, U32.or(base, Arr.Arr.pow2_u32(p)))
                   == bval : Bool} =
            Equal.trans(Bool,
              FH.u32_bit(k, U32.or(base, Arr.Arr.pow2_u32(p))),
              FH.u32_bit(k, base), bval,
              FH.u32_bit_or_pow2_lt(k, p, base, hpk), hbb)
          Arr.DPair{
            FH.bkt_tree_other(p, base, xs, op, fg, k, bval,
              hok, hple, hbb, hbc, hxs),
            FH.bkt_tree_other(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, op, fg,
              k, bval, hok, hple, hbb2, hbc, hys)}

def FH.bkt_swap_lo(+p: Nat, +base: U32, -ys: Array<+List<+List<Nat>>>,
    r: Array<+List<+List<Nat>>> & +List<+List<Nat>>,
    +fg2: +List<SolveFast.FGroup>,
    +hr: FH.BktTree(p, base,
           Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>, r), fg2),
    +hy: FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg2)) ->
  FH.BktTree(1n+p, base,
    Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
      Array.swap.lo(+List<+List<Nat>>, ys, r)), fg2):
  (a2, res) = r
  Arr.DPair{hr, hy}

def FH.bkt_swap_hi(+p: Nat, +base: U32, -xs: Array<+List<+List<Nat>>>,
    r: Array<+List<+List<Nat>>> & +List<+List<Nat>>,
    +fg2: +List<SolveFast.FGroup>,
    +hx: FH.BktTree(p, base, xs, fg2),
    +hr: FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)),
           Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>, r), fg2)) ->
  FH.BktTree(1n+p, base,
    Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
      Array.swap.hi(+List<+List<Nat>>, xs, r)), fg2):
  (a2, res) = r
  Arr.DPair{hx, hr}

def FH.bkt_tree_swap_go_lo(+p: Nat, +base: U32,
    -xs: Array<+List<+List<Nat>>>, -ys: Array<+List<+List<Nat>>>,
    +fg1: +List<SolveFast.FGroup>, +fg2: +List<SolveFast.FGroup>,
    +i: U32, +v: +List<+List<Nat>>,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +hxs: FH.BktTree(p, base, xs, fg1),
    +hys2: FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg2),
    d: &a1: Array<+List<+List<Nat>>> -> &a2: Array<+List<+List<Nat>>> ->
       {a1 == xs : Array<+List<+List<Nat>>>}
       & {a2 == a1 : Array<+List<+List<Nat>>>},
    ih: @xs2: Array<+List<+List<Nat>>> -> FH.BktTree(p, base, xs2, fg1) ->
        FH.BktTree(p, base,
          Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
            Array.swap.go(+List<+List<Nat>>, xs2, Arr.Arr.pow2_u32(p), i, v,
              U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))), fg2)) ->
  FH.BktTree(1n+p, base,
    Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
      Array.swap.go(+List<+List<Nat>>, ANode{xs, ys}, Arr.Arr.pow2_u32(1n+p),
        i, v, True{})), fg2):
  (xs1, d2) = d
  (xs2, pe) = d2
  (+ex1, +ex2) = pe
  +hxs2 = FH.bkt_tree_transport(p, base, xs, xs2, fg1,
            Equal.sym(Array<+List<+List<Nat>>>, xs2, xs,
              Equal.trans(Array<+List<+List<Nat>>>, xs2, xs1, xs, ex2, ex1)),
            hxs)
  +h2 = ih(xs2, hxs2)
  +h1 = FH.bkt_tree_transport(p, base,
          Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
            Array.swap.go(+List<+List<Nat>>, xs2, Arr.Arr.pow2_u32(p), i, v,
              U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
          Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
            Array.swap.go(+List<+List<Nat>>, xs1, Arr.Arr.pow2_u32(p), i, v,
              U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
          fg2,
          Equal.cong(Array<+List<+List<Nat>>>, Array<+List<+List<Nat>>>,
            x => Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                   Array.swap.go(+List<+List<Nat>>, x, Arr.Arr.pow2_u32(p), i, v,
                     U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
            xs2, xs1, ex2),
          h2)
  %ex1 : FH.BktTree(1n+p, base,
           Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
             Array.swap.go(+List<+List<Nat>>, ANode{_, ys},
               Arr.Arr.pow2_u32(1n+p), i, v, True{})), fg2)
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    FH.BktTree(1n+p, base,
      Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.swap.lo(+List<+List<Nat>>, ys,
          Array.swap.go(+List<+List<Nat>>, xs1, _, i, v,
            U32.is_lt(i, U32.shr(_))))), fg2)
  FH.bkt_swap_lo(p, base, ys,
    Array.swap.go(+List<+List<Nat>>, xs1, Arr.Arr.pow2_u32(p), i, v,
      U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))),
    fg2, h1, hys2)

def FH.bkt_tree_swap_go_hi(+p: Nat, +base: U32,
    -xs: Array<+List<+List<Nat>>>, -ys: Array<+List<+List<Nat>>>,
    +fg1: +List<SolveFast.FGroup>, +fg2: +List<SolveFast.FGroup>,
    +i: U32, +v: +List<+List<Nat>>,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +hxs2: FH.BktTree(p, base, xs, fg2),
    +hys: FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg1),
    d: &a1: Array<+List<+List<Nat>>> -> &a2: Array<+List<+List<Nat>>> ->
       {a1 == ys : Array<+List<+List<Nat>>>}
       & {a2 == a1 : Array<+List<+List<Nat>>>},
    ih: @ys2: Array<+List<+List<Nat>>> ->
        FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys2, fg1) ->
        FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)),
          Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
            Array.swap.go(+List<+List<Nat>>, ys2, Arr.Arr.pow2_u32(p),
              U32.sub(i, Arr.Arr.pow2_u32(p)), v,
              U32.is_lt(U32.sub(i, Arr.Arr.pow2_u32(p)),
                U32.shr(Arr.Arr.pow2_u32(p))))), fg2)) ->
  FH.BktTree(1n+p, base,
    Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
      Array.swap.go(+List<+List<Nat>>, ANode{xs, ys}, Arr.Arr.pow2_u32(1n+p),
        i, v, False{})), fg2):
  (ys1, d2) = d
  (ys2, pe) = d2
  (+ey1, +ey2) = pe
  +base2 = U32.or(base, Arr.Arr.pow2_u32(p))
  +ip = U32.sub(i, Arr.Arr.pow2_u32(p))
  +hys2 = FH.bkt_tree_transport(p, base2, ys, ys2, fg1,
            Equal.sym(Array<+List<+List<Nat>>>, ys2, ys,
              Equal.trans(Array<+List<+List<Nat>>>, ys2, ys1, ys, ey2, ey1)),
            hys)
  +h2 = ih(ys2, hys2)
  +h1 = FH.bkt_tree_transport(p, base2,
          Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
            Array.swap.go(+List<+List<Nat>>, ys2, Arr.Arr.pow2_u32(p), ip, v,
              U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
          Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
            Array.swap.go(+List<+List<Nat>>, ys1, Arr.Arr.pow2_u32(p), ip, v,
              U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
          fg2,
          Equal.cong(Array<+List<+List<Nat>>>, Array<+List<+List<Nat>>>,
            y => Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                   Array.swap.go(+List<+List<Nat>>, y, Arr.Arr.pow2_u32(p), ip,
                     v, U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
            ys2, ys1, ey2),
          h2)
  %ey1 : FH.BktTree(1n+p, base,
           Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
             Array.swap.go(+List<+List<Nat>>, ANode{xs, _},
               Arr.Arr.pow2_u32(1n+p), i, v, False{})), fg2)
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    FH.BktTree(1n+p, base,
      Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.swap.hi(+List<+List<Nat>>, xs,
          Array.swap.go(+List<+List<Nat>>, ys1, _, U32.sub(i, _), v,
            U32.is_lt(U32.sub(i, _), U32.shr(_))))), fg2)
  FH.bkt_swap_hi(p, base, xs,
    Array.swap.go(+List<+List<Nat>>, ys1, Arr.Arr.pow2_u32(p), ip, v,
      U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))),
    fg2, hxs2, h1)

def FH.bkt_tree_swap_go(+d: Nat, +base: U32, a: Array<+List<+List<Nat>>>,
    +op: FH.BktOp, +fg: +List<SolveFast.FGroup>, +i: U32, z: Bool,
    +ez: {z == U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(d))) : Bool},
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.Arr.u32_zero_from(d, i) == True{} : Bool},
    +hbz: {FH.u32_zero_below(d, base) == True{} : Bool},
    +etgt: {U32.or(base, i) == FH.bkt_op_code(op) : U32},
    +hok: {FH.bkt_op_ok(op, fg) == True{} : Bool},
    +hb: FH.BktTree(d, base, a, FH.bkt_op_src(op, fg))) ->
  FH.BktTree(d, base,
    Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
      Array.swap.go(+List<+List<Nat>>, a, Arr.Arr.pow2_u32(d), i,
        FH.bkt_op_val(op, fg), z)),
    FH.bkt_op_dst(op, fg)):
  match d:
    case 0n:
      match a:
        case ALeaf{old}:
          +ei0 : {i == 0 : U32} = Arr.Arr.u32_eq_zero(i, zi)
          +ebase : {base == FH.bkt_op_code(op) : U32} =
            Equal.trans(U32, base, U32.or(base, 0), FH.bkt_op_code(op),
              Equal.sym(U32, U32.or(base, 0), base, FF5.FF5.u32_or_zero_r(base)),
              Equal.trans(U32, U32.or(base, 0), U32.or(base, i),
                FH.bkt_op_code(op),
                Equal.cong(U32, U32, x => U32.or(base, x), 0, i,
                  Equal.sym(U32, i, 0, ei0)),
                etgt))
          Equal.trans(+List<+List<Nat>>,
            FH.bkt_op_val(op, fg),
            FH.lookup_code(FH.bkt_op_code(op), FH.bkt_op_dst(op, fg)),
            FH.lookup_code(base, FH.bkt_op_dst(op, fg)),
            FH.bkt_op_self(op, fg, hok),
            Equal.cong(U32, +List<+List<Nat>>,
              c => FH.lookup_code(c, FH.bkt_op_dst(op, fg)),
              FH.bkt_op_code(op), base,
              Equal.sym(U32, base, FH.bkt_op_code(op), ebase)))
        case ANode{xs, ys}:
          Empty.absurd(
            FH.BktTree(0n, base,
              Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                Array.swap.go(+List<+List<Nat>>, ANode{xs, ys},
                  Arr.Arr.pow2_u32(0n), i, FH.bkt_op_val(op, fg), z)),
              FH.bkt_op_dst(op, fg)), hb)
    case 1n++p:
      match a:
        case ALeaf{old}:
          Empty.absurd(
            FH.BktTree(1n+p, base,
              Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                Array.swap.go(+List<+List<Nat>>, ALeaf{old},
                  Arr.Arr.pow2_u32(1n+p), i, FH.bkt_op_val(op, fg), z)),
              FH.bkt_op_dst(op, fg)), hb)
        case ANode{xs, ys}:
          match z:
            case True{}:
              +src = FH.bkt_op_src(op, fg)
              +hxs = Arr.Arr.dpair_l(
                       FH.BktTree(p, base, xs, src),
                       FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, src),
                       hb)
              +hys = Arr.Arr.dpair_r(
                       FH.BktTree(p, base, xs, src),
                       FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, src),
                       hb)
              +plt : {Nat.is_lt(p, 32n) == True{} : Bool} =
                NatProof.Nat.is_le_lt_trans(p, 1n+p, 32n,
                  NatProof.Nat.is_le_of_lt(p, 1n+p,
                    NatProof.Nat.is_lt_succ_self(p)), hlt)
              +eshr : {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p)
                       : U32} =
                Arr.Arr.u32_shr_pow2(p, hlt)
              +ilt : {U32.is_lt(i, Arr.Arr.pow2_u32(p)) == True{} : Bool} =
                Equal.trans(Bool,
                  U32.is_lt(i, Arr.Arr.pow2_u32(p)),
                  U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))),
                  True{},
                  Equal.cong(U32, Bool, x => U32.is_lt(i, x),
                    Arr.Arr.pow2_u32(p), U32.shr(Arr.Arr.pow2_u32(1n+p)),
                    Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)),
                      Arr.Arr.pow2_u32(p), eshr)),
                  Equal.sym(Bool, True{},
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))), ez))
              +zip : {Arr.Arr.u32_zero_from(p, i) == True{} : Bool} =
                Arr.Arr.u32_zero_from_lt(p, i, zi, plt, ilt)
              +hbzp : {FH.u32_zero_below(p, base) == True{} : Bool} =
                FH.u32_zero_below_pred(p, base, hbz)
              +hbp_base : {FH.u32_bit(p, base) == False{} : Bool} =
                FH.u32_bit_of_zero_below(p, base, hbz)
              +hbp_i : {FH.u32_bit(p, i) == False{} : Bool} =
                FH.u32_bit_of_lt(p, i, zi, plt, ilt)
              +hbp_tgt : {FH.u32_bit(p, FH.bkt_op_code(op)) == False{} : Bool} =
                Equal.trans(Bool,
                  FH.u32_bit(p, FH.bkt_op_code(op)),
                  FH.u32_bit(p, U32.or(base, i)),
                  False{},
                  Equal.cong(U32, Bool, u => FH.u32_bit(p, u),
                    FH.bkt_op_code(op), U32.or(base, i),
                    Equal.sym(U32, U32.or(base, i), FH.bkt_op_code(op), etgt)),
                  Equal.trans(Bool,
                    FH.u32_bit(p, U32.or(base, i)),
                    Bool.or(FH.u32_bit(p, base), FH.u32_bit(p, i)),
                    False{},
                    FH.u32_bit_or(p, base, i),
                    Equal.trans(Bool,
                      Bool.or(FH.u32_bit(p, base), FH.u32_bit(p, i)),
                      Bool.or(False{}, FH.u32_bit(p, i)),
                      False{},
                      Equal.cong(Bool, Bool, b => Bool.or(b, FH.u32_bit(p, i)),
                        FH.u32_bit(p, base), False{}, hbp_base),
                      hbp_i)))
              +base2 = U32.or(base, Arr.Arr.pow2_u32(p))
              +hys2 = FH.bkt_tree_other(p, base2, ys, op, fg, p, True{},
                        hok, NatProof.Nat.is_le_refl(p),
                        FH.u32_bit_or_pow2_same(p, base, plt), hbp_tgt, hys)
              FH.bkt_tree_swap_go_lo(p, base, xs, ys, src,
                FH.bkt_op_dst(op, fg), i, FH.bkt_op_val(op, fg), eshr,
                hxs, hys2, Arr.Arr.dup(+List<+List<Nat>>, xs),
                xs2 => hxs2 =>
                  FH.bkt_tree_swap_go(p, base, xs2, op, fg, i,
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, hbzp, etgt, hok, hxs2))
            case False{}:
              +src = FH.bkt_op_src(op, fg)
              +hxs = Arr.Arr.dpair_l(
                       FH.BktTree(p, base, xs, src),
                       FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, src),
                       hb)
              +hys = Arr.Arr.dpair_r(
                       FH.BktTree(p, base, xs, src),
                       FH.BktTree(p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, src),
                       hb)
              +plt : {Nat.is_lt(p, 32n) == True{} : Bool} =
                NatProof.Nat.is_le_lt_trans(p, 1n+p, 32n,
                  NatProof.Nat.is_le_of_lt(p, 1n+p,
                    NatProof.Nat.is_lt_succ_self(p)), hlt)
              +eshr : {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p)
                       : U32} =
                Arr.Arr.u32_shr_pow2(p, hlt)
              +ige : {U32.is_lt(i, Arr.Arr.pow2_u32(p)) == False{} : Bool} =
                Equal.trans(Bool,
                  U32.is_lt(i, Arr.Arr.pow2_u32(p)),
                  U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))),
                  False{},
                  Equal.cong(U32, Bool, x => U32.is_lt(i, x),
                    Arr.Arr.pow2_u32(p), U32.shr(Arr.Arr.pow2_u32(1n+p)),
                    Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)),
                      Arr.Arr.pow2_u32(p), eshr)),
                  Equal.sym(Bool, False{},
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))), ez))
              +ip = U32.sub(i, Arr.Arr.pow2_u32(p))
              +zip : {Arr.Arr.u32_zero_from(p, ip) == True{} : Bool} =
                Arr.Arr.u32_zero_from_ge(p, i, zi, plt, ige)
              +base2 = U32.or(base, Arr.Arr.pow2_u32(p))
              +hbzp : {FH.u32_zero_below(p, base) == True{} : Bool} =
                FH.u32_zero_below_pred(p, base, hbz)
              +hbz2 : {FH.u32_zero_below(p, base2) == True{} : Bool} =
                FH.u32_zero_below_or_pow2(p, base, hbzp)
              +hbp_base : {FH.u32_bit(p, base) == False{} : Bool} =
                FH.u32_bit_of_zero_below(p, base, hbz)
              +hbp_i : {FH.u32_bit(p, i) == True{} : Bool} =
                FH.u32_bit_of_ge(p, i, zi, plt, ige)
              +hbp_tgt : {FH.u32_bit(p, FH.bkt_op_code(op)) == True{} : Bool} =
                Equal.trans(Bool,
                  FH.u32_bit(p, FH.bkt_op_code(op)),
                  FH.u32_bit(p, U32.or(base, i)),
                  True{},
                  Equal.cong(U32, Bool, u => FH.u32_bit(p, u),
                    FH.bkt_op_code(op), U32.or(base, i),
                    Equal.sym(U32, U32.or(base, i), FH.bkt_op_code(op), etgt)),
                  Equal.trans(Bool,
                    FH.u32_bit(p, U32.or(base, i)),
                    Bool.or(FH.u32_bit(p, base), FH.u32_bit(p, i)),
                    True{},
                    FH.u32_bit_or(p, base, i),
                    Equal.trans(Bool,
                      Bool.or(FH.u32_bit(p, base), FH.u32_bit(p, i)),
                      Bool.or(False{}, FH.u32_bit(p, i)),
                      True{},
                      Equal.cong(Bool, Bool, b => Bool.or(b, FH.u32_bit(p, i)),
                        FH.u32_bit(p, base), False{}, hbp_base),
                      hbp_i)))
              +etgt2 : {U32.or(base2, ip) == FH.bkt_op_code(op) : U32} =
                Equal.trans(U32, U32.or(base2, ip), U32.or(base, i),
                  FH.bkt_op_code(op),
                  FH.u32_or_base_sub(p, base, i, zi, plt, ige), etgt)
              +hxs2 = FH.bkt_tree_other(p, base, xs, op, fg, p, False{},
                        hok, NatProof.Nat.is_le_refl(p), hbp_base, hbp_tgt, hxs)
              FH.bkt_tree_swap_go_hi(p, base, xs, ys, src,
                FH.bkt_op_dst(op, fg), i, FH.bkt_op_val(op, fg), eshr,
                hxs2, hys, Arr.Arr.dup(+List<+List<Nat>>, ys),
                ys2 => hys2 =>
                  FH.bkt_tree_swap_go(p, base2, ys2, op, fg, ip,
                    U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, hbz2, etgt2, hok, hys2))

def FH.bkt_tree_swap_dup2(-bkts: Array<+List<+List<Nat>>>,
    a1: Array<+List<+List<Nat>>>, +op: FH.BktOp, +fg: +List<SolveFast.FGroup>,
    +ea1: {a1 == bkts : Array<+List<+List<Nat>>>},
    -a2: Array<+List<+List<Nat>>>,
    +ea2: {a2 == a1 : Array<+List<+List<Nat>>>},
    dp2: &b1: Array<+List<+List<Nat>>> -> &b2: Array<+List<+List<Nat>>> ->
         {b1 == a2 : Array<+List<+List<Nat>>>}
         & {b2 == b1 : Array<+List<+List<Nat>>>},
    +hok: {FH.bkt_op_ok(op, fg) == True{} : Bool},
    +hb: FH.BktTree(10n, 0, bkts, FH.bkt_op_src(op, fg))) ->
  FH.BktTree(10n, 0,
    Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
      Array.swap(+List<+List<Nat>>, bkts, FH.bkt_op_code(op),
        FH.bkt_op_val(op, fg))),
    FH.bkt_op_dst(op, fg)):
  (b1, dp3) = dp2
  (b2, pe2) = dp3
  (+eb1, +eb2) = pe2
  +code = FH.bkt_op_code(op)
  +val = FH.bkt_op_val(op, fg)
  +src = FH.bkt_op_src(op, fg)
  +dst = FH.bkt_op_dst(op, fg)
  +zc = FH.bkt_op_zero_from(op, fg, hok)
  +ea_b1 : {b1 == a1 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, b1, a2, a1, eb1, ea2)
  +ea_b2 : {b2 == a1 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, b2, b1, a1, eb2, ea_b1)
  +hb1 = FH.bkt_tree_transport(10n, 0, bkts, a1, src,
           Equal.sym(Array<+List<+List<Nat>>>, a1, bkts, ea1), hb)
  +hb_b1 = FH.bkt_tree_transport(10n, 0, a1, b1, src,
             Equal.sym(Array<+List<+List<Nat>>>, b1, a1, ea_b1), hb1)
  +hd_b1 = FH.bkt_tree_depth(10n, 0, b1, src, hb_b1)
  +hd_b2 = Arr.Arr.depth_transport(+List<+List<Nat>>, 10n, b1, b2,
             Equal.sym(Array<+List<+List<Nat>>>, b2, b1, eb2), hd_b1)
  +em = Arr.Arr.u32_and_mask(10n, code, zc)
  +esw : {Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
            Array.swap(+List<+List<Nat>>, b2, code, val))
          == Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
               Array.swap.go(+List<+List<Nat>>, b2, Arr.Arr.pow2_u32(10n),
                 code, val, U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))
          : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>,
      Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.swap(+List<+List<Nat>>, b2, code, val)),
      Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.swap.go(+List<+List<Nat>>, b2, Arr.Arr.pow2_u32(10n),
          U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)), val,
          U32.is_lt(U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)),
            U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.swap.go(+List<+List<Nat>>, b2, Arr.Arr.pow2_u32(10n), code, val,
          U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.swap_depth(+List<+List<Nat>>, 10n, b2, code, val, hd_b2),
      Equal.cong(U32, Array<+List<+List<Nat>>>,
        j => Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
               Array.swap.go(+List<+List<Nat>>, b2, Arr.Arr.pow2_u32(10n), j,
                 val, U32.is_lt(j, U32.shr(Arr.Arr.pow2_u32(10n))))),
        U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)), code, em))
  +ea1_b2 : {a1 == b2 : Array<+List<+List<Nat>>>} =
    Equal.sym(Array<+List<+List<Nat>>>, b2, a1, ea_b2)
  +hgo = FH.bkt_tree_swap_go(10n, 0, a1, op, fg, code,
           U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))), {==}, {==}, zc,
           {==}, FF5.FF5.u32_or_zero_l(code), hok, hb1)
  +eq_a : {Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
             Array.swap.go(+List<+List<Nat>>, a1, Arr.Arr.pow2_u32(10n), code,
               val, U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))
           == Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                Array.swap(+List<+List<Nat>>, b2, code, val))
           : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>,
      Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.swap.go(+List<+List<Nat>>, a1, Arr.Arr.pow2_u32(10n), code, val,
          U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.swap.go(+List<+List<Nat>>, b2, Arr.Arr.pow2_u32(10n), code, val,
          U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.swap(+List<+List<Nat>>, b2, code, val)),
      Equal.cong(Array<+List<+List<Nat>>>, Array<+List<+List<Nat>>>,
        x => Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
               Array.swap.go(+List<+List<Nat>>, x, Arr.Arr.pow2_u32(10n), code,
                 val, U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
        a1, b2, ea1_b2),
      Equal.sym(Array<+List<+List<Nat>>>,
        Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
          Array.swap(+List<+List<Nat>>, b2, code, val)),
        Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
          Array.swap.go(+List<+List<Nat>>, b2, Arr.Arr.pow2_u32(10n), code, val,
            U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
        esw))
  %ea1 : FH.BktTree(10n, 0,
           Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
             Array.swap(+List<+List<Nat>>, _, code, val)), dst)
  %ea_b2 : FH.BktTree(10n, 0,
             Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
               Array.swap(+List<+List<Nat>>, _, code, val)), dst)
  FH.bkt_tree_transport(10n, 0,
    Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
      Array.swap.go(+List<+List<Nat>>, a1, Arr.Arr.pow2_u32(10n), code, val,
        U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
    Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
      Array.swap(+List<+List<Nat>>, b2, code, val)),
    dst, eq_a, hgo)

def FH.bkt_tree_swap_dup(-bkts: Array<+List<+List<Nat>>>,
    +op: FH.BktOp, +fg: +List<SolveFast.FGroup>,
    +hok: {FH.bkt_op_ok(op, fg) == True{} : Bool},
    +hb: FH.BktTree(10n, 0, bkts, FH.bkt_op_src(op, fg)),
    dp: &a1: Array<+List<+List<Nat>>> -> &a2: Array<+List<+List<Nat>>> ->
        {a1 == bkts : Array<+List<+List<Nat>>>}
        & {a2 == a1 : Array<+List<+List<Nat>>>}) ->
  FH.BktTree(10n, 0,
    Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
      Array.swap(+List<+List<Nat>>, bkts, FH.bkt_op_code(op),
        FH.bkt_op_val(op, fg))),
    FH.bkt_op_dst(op, fg)):
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  FH.bkt_tree_swap_dup2(bkts, a1, op, fg, ea1, a2, ea2,
    Arr.Arr.dup(+List<+List<Nat>>, a2), hok, hb)

def FH.bkt_tree_swap(bkts: Array<+List<+List<Nat>>>,
    +op: FH.BktOp, +fg: +List<SolveFast.FGroup>,
    +hok: {FH.bkt_op_ok(op, fg) == True{} : Bool},
    +hb: FH.BktTree(10n, 0, bkts, FH.bkt_op_src(op, fg))) ->
  FH.BktTree(10n, 0,
    Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
      Array.swap(+List<+List<Nat>>, bkts, FH.bkt_op_code(op),
        FH.bkt_op_val(op, fg))),
    FH.bkt_op_dst(op, fg)):
  FH.bkt_tree_swap_dup(bkts, op, fg, hok, hb,
    Arr.Arr.dup(+List<+List<Nat>>, bkts))

def FH.bkt_tree_set_add_dup(-bkts: Array<+List<+List<Nat>>>,
    +w: +List<Nat>, +fb: +List<Feedback.Color>, +fg: +List<SolveFast.FGroup>,
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool},
    +hb: FH.BktTree(10n, 0, bkts, fg),
    dp: &a1: Array<+List<+List<Nat>>> -> &a2: Array<+List<+List<Nat>>> ->
        {a1 == bkts : Array<+List<+List<Nat>>>}
        & {a2 == a1 : Array<+List<+List<Nat>>>}) ->
  FH.BktTree(10n, 0,
    Array.set(+List<+List<Nat>>, bkts, FF5.FF5.encode_fb5_list(fb),
      w <> FH.lookup_code(FF5.FF5.encode_fb5_list(fb), fg)),
    SolveFast.fgroup_add_fast(w, fb, fg)):
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  +c = FF5.FF5.encode_fb5_list(fb)
  +val : +List<+List<Nat>> = w <> FH.lookup_code(c, fg)
  +fg2 = SolveFast.fgroup_add_fast(w, fb, fg)
  +ea2_b : {a2 == bkts : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, a2, a1, bkts, ea2, ea1)
  +hb2 = FH.bkt_tree_transport(10n, 0, bkts, a2, fg,
           Equal.sym(Array<+List<+List<Nat>>>, a2, bkts, ea2_b), hb)
  +hsw = FH.bkt_tree_swap(a2, OpAdd{w, fb}, fg,
           FH.bool_and_intro(FF5.FF5.is_fb5(fb), FH.fgroups_wf(fg), hfb, hwf),
           hb2)
  +eset : {Array.set(+List<+List<Nat>>, a1, c, val)
           == Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                Array.swap(+List<+List<Nat>>, a1, c, val))
           : Array<+List<+List<Nat>>>} =
    Arr.Arr.set_eq(+List<+List<Nat>>, a1, c, val)
  %ea1 : FH.BktTree(10n, 0, Array.set(+List<+List<Nat>>, _, c, val), fg2)
  FH.bkt_tree_transport(10n, 0,
    Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
      Array.swap(+List<+List<Nat>>, a2, c, val)),
    Array.set(+List<+List<Nat>>, a1, c, val),
    fg2,
    Equal.trans(Array<+List<+List<Nat>>>,
      Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.swap(+List<+List<Nat>>, a2, c, val)),
      Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.swap(+List<+List<Nat>>, a1, c, val)),
      Array.set(+List<+List<Nat>>, a1, c, val),
      Equal.cong(Array<+List<+List<Nat>>>, Array<+List<+List<Nat>>>,
        x => Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
               Array.swap(+List<+List<Nat>>, x, c, val)),
        a2, a1, ea2),
      Equal.sym(Array<+List<+List<Nat>>>,
        Array.set(+List<+List<Nat>>, a1, c, val),
        Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
          Array.swap(+List<+List<Nat>>, a1, c, val)),
        eset)),
    hsw)

def FH.bkt_tree_set_add(bkts: Array<+List<+List<Nat>>>,
    +w: +List<Nat>, +fb: +List<Feedback.Color>, +fg: +List<SolveFast.FGroup>,
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool},
    +hb: FH.BktTree(10n, 0, bkts, fg)) ->
  FH.BktTree(10n, 0,
    Array.set(+List<+List<Nat>>, bkts, FF5.FF5.encode_fb5_list(fb),
      w <> FH.lookup_code(FF5.FF5.encode_fb5_list(fb), fg)),
    SolveFast.fgroup_add_fast(w, fb, fg)):
  FH.bkt_tree_set_add_dup(bkts, w, fb, fg, hfb, hwf, hb,
    Arr.Arr.dup(+List<+List<Nat>>, bkts))


# ---------------------------------------------------------------------------
# Pass 2a: `fill5_go` populates `buckets` and records `FH.rev_codes(fg, acc)`
# ---------------------------------------------------------------------------

def FH.add_facts_wf(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +fg: +List<SolveFast.FGroup>, +fg2: +List<SolveFast.FGroup>,
    f: FH.AddFacts<w, fb, fg, fg2>) ->
  {FH.fgroups_wf(fg2) == True{} : Bool}:
  match f:
    case AddFacts{wf2, tot2, cnt2, has_self, lkp_self}:
      wf2

def FH.list_nil_disc(-T: Data, xs: +List<T>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{h, t}:
      Empty

def FH.list_nil_ne_con(-T: Data, +h: T, +t: +List<T>,
    +e: {Nil{} == h <> t : +List<T>}) -> Empty:
  %e : FH.list_nil_disc(T, _)
  Unit{}

def FH.has_code_false_of_lookup_nil_step(+c: U32,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, eq: Bool,
    +eeq: {eq == U32.is_eq(c, FF5.FF5.encode_fb5_list(f)) : Bool},
    +hlen: {Nat.is_le(1n, len) == True{} : Bool},
    +heql: {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool},
    +hnil: {Feedback.Bool.case(+List<+List<Nat>>, eq, rws, FH.lookup_code(c, rest))
            == Nil{} : +List<+List<Nat>>},
    ih: {FH.lookup_code(c, rest) == Nil{} : +List<+List<Nat>>} ->
        {FH.has_code(c, rest) == False{} : Bool}) ->
  {Bool.or(eq, FH.has_code(c, rest)) == False{} : Bool}:
  match eq:
    case True{}:
      +elen0 : {len == 0n : Nat} =
        Equal.trans(Nat, len, Groups.len_words(rws), 0n,
          NatProof.NatPrf.is_eq_true(len, Groups.len_words(rws), heql),
          Equal.cong(+List<+List<Nat>>, Nat, xs => Groups.len_words(xs),
            rws, Nil{}, hnil))
      +h10 : {Nat.is_le(1n, 0n) == True{} : Bool} =
        Equal.trans(Bool, Nat.is_le(1n, 0n), Nat.is_le(1n, len), True{},
          Equal.cong(Nat, Bool, x => Nat.is_le(1n, x), 0n, len,
            Equal.sym(Nat, len, 0n, elen0)),
          hlen)
      Empty.absurd(
        {Bool.or(True{}, FH.has_code(c, rest)) == False{} : Bool},
        Logic.Proof.false_ne_true(h10))
    case False{}:
      ih(hnil)

def FH.has_code_false_of_lookup_nil(+c: U32, +fg: +List<SolveFast.FGroup>,
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool},
    +hnil: {FH.lookup_code(c, fg) == Nil{} : +List<+List<Nat>>}) ->
  {FH.has_code(c, fg) == False{} : Bool}:
  match fg:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          +cf = FF5.FF5.encode_fb5_list(f)
          +h1 = Logic.Proof.and_true_r(FF5.FF5.is_fb5(f),
                  Bool.and(Nat.is_le(1n, len),
                    Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                      Bool.and(Bool.not(FH.has_code(cf, rest)),
                        FH.fgroups_wf(rest)))), hwf)
          +hlen = Logic.Proof.and_true_l(Nat.is_le(1n, len),
                    Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                      Bool.and(Bool.not(FH.has_code(cf, rest)),
                        FH.fgroups_wf(rest))), h1)
          +h2 = Logic.Proof.and_true_r(Nat.is_le(1n, len),
                  Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                    Bool.and(Bool.not(FH.has_code(cf, rest)),
                      FH.fgroups_wf(rest))), h1)
          +heql = Logic.Proof.and_true_l(Nat.is_eq(len, Groups.len_words(rws)),
                    Bool.and(Bool.not(FH.has_code(cf, rest)),
                      FH.fgroups_wf(rest)), h2)
          +h3 = Logic.Proof.and_true_r(Nat.is_eq(len, Groups.len_words(rws)),
                  Bool.and(Bool.not(FH.has_code(cf, rest)),
                    FH.fgroups_wf(rest)), h2)
          +hr = Logic.Proof.and_true_r(Bool.not(FH.has_code(cf, rest)),
                  FH.fgroups_wf(rest), h3)
          FH.has_code_false_of_lookup_nil_step(c, f, len, rws, rest,
            U32.is_eq(c, cf), {==}, hlen, heql, hnil,
            h => FH.has_code_false_of_lookup_nil(c, rest, hr, h))

def FH.has_code_true_of_lookup_con_step(+c: U32,
    +h: +List<Nat>, +t: +List<+List<Nat>>,
    +rws: +List<+List<Nat>>, +rest: +List<SolveFast.FGroup>, eq: Bool,
    +econ: {Feedback.Bool.case(+List<+List<Nat>>, eq, rws, FH.lookup_code(c, rest))
            == h <> t : +List<+List<Nat>>},
    ih: {FH.lookup_code(c, rest) == h <> t : +List<+List<Nat>>} ->
        {FH.has_code(c, rest) == True{} : Bool}) ->
  {Bool.or(eq, FH.has_code(c, rest)) == True{} : Bool}:
  match eq:
    case True{}:
      {==}
    case False{}:
      ih(econ)

def FH.has_code_true_of_lookup_con(+c: U32, +fg: +List<SolveFast.FGroup>,
    +h: +List<Nat>, +t: +List<+List<Nat>>,
    +econ: {FH.lookup_code(c, fg) == h <> t : +List<+List<Nat>>}) ->
  {FH.has_code(c, fg) == True{} : Bool}:
  match fg:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool},
        FH.list_nil_ne_con(+List<Nat>, h, t, econ))
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          FH.has_code_true_of_lookup_con_step(c, h, t, rws, rest,
            U32.is_eq(c, FF5.FF5.encode_fb5_list(f)), econ,
            hc => FH.has_code_true_of_lookup_con(c, rest, h, t, hc))

def FH.FillSpec(+fg: +List<SolveFast.FGroup>, +acc_touched: +List<U32>,
    fs: SolveFast.Fill5State) -> Data:
  match fs:
    case SolveFast.Fill5State{bkts, touched}:
      Arr.Arr.DPair<
        FH.BktTree(10n, 0, bkts, fg),
        Arr.Arr.DPair<
          {touched == FH.rev_codes(fg, acc_touched) : +List<U32>},
          {FH.fgroups_wf(fg) == True{} : Bool}>>

def FH.fill_spec_transport(+fg: +List<SolveFast.FGroup>,
    +acc_touched: +List<U32>,
    -fs1: SolveFast.Fill5State, -fs2: SolveFast.Fill5State,
    +ef: {fs1 == fs2 : SolveFast.Fill5State},
    +h: FH.FillSpec(fg, acc_touched, fs1)) ->
  FH.FillSpec(fg, acc_touched, fs2):
  %ef : FH.FillSpec(fg, acc_touched, _)
  h

def FH.fill_spec_transport_fg(+fg1: +List<SolveFast.FGroup>,
    +fg2: +List<SolveFast.FGroup>, +acc_touched: +List<U32>,
    -fs: SolveFast.Fill5State,
    +efg: {fg1 == fg2 : +List<SolveFast.FGroup>},
    +h: FH.FillSpec(fg1, acc_touched, fs)) ->
  FH.FillSpec(fg2, acc_touched, fs):
  %efg : FH.FillSpec(_, acc_touched, fs)
  h

def FH.fill5_get_done_old(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +code: U32, +fg0: +List<SolveFast.FGroup>, +touched: +List<U32>,
    +acc_touched: +List<U32>,
    b2: Array<+List<+List<Nat>>>, +old: +List<+List<Nat>>,
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb2: FH.BktTree(10n, 0, b2, fg0),
    +eold: {old == FH.lookup_code(FF5.FF5.encode_fb5_list(fb), fg0)
            : +List<+List<Nat>>}) ->
  FH.FillSpec(SolveFast.fgroup_add_fast(w, fb, fg0), acc_touched,
    SolveFast.fill5_get_done(w, code, touched, (b2, old))):
  match old:
    case Nil{}:
      +c = FF5.FF5.encode_fb5_list(fb)
      +fg1 = SolveFast.fgroup_add_fast(w, fb, fg0)
      +hwf1 = FH.add_facts_wf(w, fb, fg0, fg1,
                FH.fgroup_add_facts(w, fb, fg0,
                  SolveFast.next_fgroup_hit(fb, fg0), {==}, hfb, hwf))
      +hhas : {FH.has_code(c, fg0) == False{} : Bool} =
        FH.has_code_false_of_lookup_nil(c, fg0, hwf,
          Equal.sym(+List<+List<Nat>>, Nil{}, FH.lookup_code(c, fg0), eold))
      +et1 : {code <> touched == FH.rev_codes(fg1, acc_touched) : +List<U32>} =
        Equal.trans(+List<U32>,
          code <> touched,
          c <> FH.rev_codes(fg0, acc_touched),
          FH.rev_codes(fg1, acc_touched),
          Equal.trans(+List<U32>,
            code <> touched,
            c <> touched,
            c <> FH.rev_codes(fg0, acc_touched),
            Equal.cong(U32, +List<U32>, j => j <> touched, code, c, ecode),
            Equal.cong(+List<U32>, +List<U32>, ts => c <> ts,
              touched, FH.rev_codes(fg0, acc_touched), etouched)),
          Equal.sym(+List<U32>,
            FH.rev_codes(fg1, acc_touched),
            c <> FH.rev_codes(fg0, acc_touched),
            Equal.trans(+List<U32>,
              FH.rev_codes(fg1, acc_touched),
              Feedback.Bool.case(+List<U32>, FH.has_code(c, fg0),
                FH.rev_codes(fg0, acc_touched),
                c <> FH.rev_codes(fg0, acc_touched)),
              c <> FH.rev_codes(fg0, acc_touched),
              FH.fgroup_add_rev_codes(w, fb, fg0, acc_touched,
                SolveFast.next_fgroup_hit(fb, fg0), {==}, hfb, hwf),
              Equal.cong(Bool, +List<U32>,
                b => Feedback.Bool.case(+List<U32>, b,
                       FH.rev_codes(fg0, acc_touched),
                       c <> FH.rev_codes(fg0, acc_touched)),
                FH.has_code(c, fg0), False{}, hhas))))
      %Equal.sym(U32, code, c, ecode) :
        Arr.Arr.DPair<
          FH.BktTree(10n, 0,
            Array.set(+List<+List<Nat>>, b2, _, w <> Nil{}), fg1),
          Arr.Arr.DPair<
            {code <> touched == FH.rev_codes(fg1, acc_touched) : +List<U32>},
            {FH.fgroups_wf(fg1) == True{} : Bool}>>
      %Equal.sym(+List<+List<Nat>>, Nil{}, FH.lookup_code(c, fg0), eold) :
        Arr.Arr.DPair<
          FH.BktTree(10n, 0,
            Array.set(+List<+List<Nat>>, b2, c, w <> _), fg1),
          Arr.Arr.DPair<
            {code <> touched == FH.rev_codes(fg1, acc_touched) : +List<U32>},
            {FH.fgroups_wf(fg1) == True{} : Bool}>>
      Arr.DPair{FH.bkt_tree_set_add(b2, w, fb, fg0, hfb, hwf, hb2),
        Arr.DPair{et1, hwf1}}
    case Con{+h, +t}:
      +c = FF5.FF5.encode_fb5_list(fb)
      +fg1 = SolveFast.fgroup_add_fast(w, fb, fg0)
      +hwf1 = FH.add_facts_wf(w, fb, fg0, fg1,
                FH.fgroup_add_facts(w, fb, fg0,
                  SolveFast.next_fgroup_hit(fb, fg0), {==}, hfb, hwf))
      +hhas : {FH.has_code(c, fg0) == True{} : Bool} =
        FH.has_code_true_of_lookup_con(c, fg0, h, t,
          Equal.sym(+List<+List<Nat>>, h <> t, FH.lookup_code(c, fg0), eold))
      +et1 : {touched == FH.rev_codes(fg1, acc_touched) : +List<U32>} =
        Equal.trans(+List<U32>,
          touched,
          FH.rev_codes(fg0, acc_touched),
          FH.rev_codes(fg1, acc_touched),
          etouched,
          Equal.sym(+List<U32>,
            FH.rev_codes(fg1, acc_touched),
            FH.rev_codes(fg0, acc_touched),
            Equal.trans(+List<U32>,
              FH.rev_codes(fg1, acc_touched),
              Feedback.Bool.case(+List<U32>, FH.has_code(c, fg0),
                FH.rev_codes(fg0, acc_touched),
                c <> FH.rev_codes(fg0, acc_touched)),
              FH.rev_codes(fg0, acc_touched),
              FH.fgroup_add_rev_codes(w, fb, fg0, acc_touched,
                SolveFast.next_fgroup_hit(fb, fg0), {==}, hfb, hwf),
              Equal.cong(Bool, +List<U32>,
                b => Feedback.Bool.case(+List<U32>, b,
                       FH.rev_codes(fg0, acc_touched),
                       c <> FH.rev_codes(fg0, acc_touched)),
                FH.has_code(c, fg0), True{}, hhas))))
      %Equal.sym(U32, code, c, ecode) :
        Arr.Arr.DPair<
          FH.BktTree(10n, 0,
            Array.set(+List<+List<Nat>>, b2, _, w <> (h <> t)), fg1),
          Arr.Arr.DPair<
            {touched == FH.rev_codes(fg1, acc_touched) : +List<U32>},
            {FH.fgroups_wf(fg1) == True{} : Bool}>>
      %Equal.sym(+List<+List<Nat>>, h <> t, FH.lookup_code(c, fg0), eold) :
        Arr.Arr.DPair<
          FH.BktTree(10n, 0,
            Array.set(+List<+List<Nat>>, b2, c, w <> _), fg1),
          Arr.Arr.DPair<
            {touched == FH.rev_codes(fg1, acc_touched) : +List<U32>},
            {FH.fgroups_wf(fg1) == True{} : Bool}>>
      Arr.DPair{FH.bkt_tree_set_add(b2, w, fb, fg0, hfb, hwf, hb2),
        Arr.DPair{et1, hwf1}}

def FH.fill5_get_done_pair(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +code: U32, +fg0: +List<SolveFast.FGroup>, +touched: +List<U32>,
    +acc_touched: +List<U32>,
    r: Array<+List<+List<Nat>>> & +List<+List<Nat>>,
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb2: FH.BktTree(10n, 0,
            Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>, r), fg0),
    +eold: {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>, r)
            == FH.lookup_code(FF5.FF5.encode_fb5_list(fb), fg0)
            : +List<+List<Nat>>}) ->
  FH.FillSpec(SolveFast.fgroup_add_fast(w, fb, fg0), acc_touched,
    SolveFast.fill5_get_done(w, code, touched, r)):
  (b2, +old) = r
  FH.fill5_get_done_old(w, fb, code, fg0, touched, acc_touched, b2, old,
    ecode, hfb, hwf, etouched, hb2, eold)

def FH.fill5_step_false_dup3(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +code: U32, +fg0: +List<SolveFast.FGroup>, +touched: +List<U32>,
    +acc_touched: +List<U32>,
    -bkts: Array<+List<+List<Nat>>>,
    a1: Array<+List<+List<Nat>>>,
    +ea1: {a1 == bkts : Array<+List<+List<Nat>>>},
    b1: Array<+List<+List<Nat>>>,
    +eb1: {b1 == a1 : Array<+List<+List<Nat>>>},
    c1: Array<+List<+List<Nat>>>,
    +ec1: {c1 == b1 : Array<+List<+List<Nat>>>},
    c2: Array<+List<+List<Nat>>>,
    +ec2: {c2 == c1 : Array<+List<+List<Nat>>>},
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb: FH.BktTree(10n, 0, bkts, fg0)) ->
  FH.FillSpec(SolveFast.fgroup_add_fast(w, fb, fg0), acc_touched,
    SolveFast.fill5_get_done(w, code, touched,
      Array.get(+List<+List<Nat>>, bkts, code))):
  +c = FF5.FF5.encode_fb5_list(fb)
  +eb1_b : {b1 == bkts : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, b1, a1, bkts, eb1, ea1)
  +ec1_a : {c1 == a1 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, c1, b1, a1, ec1, eb1)
  +ec1_b : {c1 == bkts : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, c1, b1, bkts, ec1, eb1_b)
  +ec2_a : {c2 == a1 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, c2, c1, a1, ec2, ec1_a)
  +ec2_b : {c2 == bkts : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, c2, c1, bkts, ec2, ec1_b)
  +hb_a1 = FH.bkt_tree_transport(10n, 0, bkts, a1, fg0,
             Equal.sym(Array<+List<+List<Nat>>>, a1, bkts, ea1), hb)
  +hb_c1 = FH.bkt_tree_transport(10n, 0, bkts, c1, fg0,
             Equal.sym(Array<+List<+List<Nat>>>, c1, bkts, ec1_b), hb)
  +hb_c2 = FH.bkt_tree_transport(10n, 0, bkts, c2, fg0,
             Equal.sym(Array<+List<+List<Nat>>>, c2, bkts, ec2_b), hb)
  +hd_b1 = FH.bkt_tree_depth(10n, 0, b1, fg0,
             FH.bkt_tree_transport(10n, 0, bkts, b1, fg0,
               Equal.sym(Array<+List<+List<Nat>>>, b1, bkts, eb1_b), hb))
  +hd_c1 = Arr.Arr.depth_transport(+List<+List<Nat>>, 10n, b1, c1,
             Equal.sym(Array<+List<+List<Nat>>>, c1, b1, ec1), hd_b1)
  +efst_c1 : {Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                Array.get(+List<+List<Nat>>, c1, code))
              == c1 : Array<+List<+List<Nat>>>} =
    Arr.Arr.get_fst(+List<+List<Nat>>, 10n, c1, code, hd_c1)
  +efst_a1 : {Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                Array.get(+List<+List<Nat>>, a1, code))
              == a1 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>,
      Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.get(+List<+List<Nat>>, a1, code)),
      c1, a1,
      Equal.trans(Array<+List<+List<Nat>>>,
        Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
          Array.get(+List<+List<Nat>>, a1, code)),
        Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
          Array.get(+List<+List<Nat>>, c1, code)),
        c1,
        Equal.cong(Array<+List<+List<Nat>>>, Array<+List<+List<Nat>>>,
          x => Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                 Array.get(+List<+List<Nat>>, x, code)),
          a1, c1, Equal.sym(Array<+List<+List<Nat>>>, c1, a1, ec1_a)),
        efst_c1),
      ec1_a)
  +hb_fst = FH.bkt_tree_transport(10n, 0, a1,
              Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                Array.get(+List<+List<Nat>>, a1, code)),
              fg0,
              Equal.sym(Array<+List<+List<Nat>>>,
                Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                  Array.get(+List<+List<Nat>>, a1, code)),
                a1, efst_a1),
              hb_a1)
  +zc : {Arr.Arr.u32_zero_from(10n, code) == True{} : Bool} =
    Equal.trans(Bool,
      Arr.Arr.u32_zero_from(10n, code),
      Arr.Arr.u32_zero_from(10n, c), True{},
      Equal.cong(U32, Bool, j => Arr.Arr.u32_zero_from(10n, j), code, c, ecode),
      FF5.FF5.encode_fb5_list_zero_from(fb, hfb))
  +eold_c2 : {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                Array.get(+List<+List<Nat>>, c2, code))
              == FH.lookup_code(code, fg0) : +List<+List<Nat>>} =
    FH.bkt_tree_get(c2, fg0, code, zc, hb_c2)
  +eold_a1 : {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                Array.get(+List<+List<Nat>>, a1, code))
              == FH.lookup_code(c, fg0) : +List<+List<Nat>>} =
    Equal.trans(+List<+List<Nat>>,
      Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.get(+List<+List<Nat>>, a1, code)),
      FH.lookup_code(code, fg0),
      FH.lookup_code(c, fg0),
      Equal.trans(+List<+List<Nat>>,
        Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
          Array.get(+List<+List<Nat>>, a1, code)),
        Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
          Array.get(+List<+List<Nat>>, c2, code)),
        FH.lookup_code(code, fg0),
        Equal.cong(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
          x => Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                 Array.get(+List<+List<Nat>>, x, code)),
          a1, c2, Equal.sym(Array<+List<+List<Nat>>>, c2, a1, ec2_a)),
        eold_c2),
      Equal.cong(U32, +List<+List<Nat>>, j => FH.lookup_code(j, fg0),
        code, c, ecode))
  %ea1 : FH.FillSpec(SolveFast.fgroup_add_fast(w, fb, fg0), acc_touched,
           SolveFast.fill5_get_done(w, code, touched,
             Array.get(+List<+List<Nat>>, _, code)))
  FH.fill5_get_done_pair(w, fb, code, fg0, touched, acc_touched,
    Array.get(+List<+List<Nat>>, a1, code),
    ecode, hfb, hwf, etouched, hb_fst, eold_a1)

def FH.fill5_step_false_dup2b(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +code: U32, +fg0: +List<SolveFast.FGroup>, +touched: +List<U32>,
    +acc_touched: +List<U32>,
    -bkts: Array<+List<+List<Nat>>>,
    a1: Array<+List<+List<Nat>>>,
    +ea1: {a1 == bkts : Array<+List<+List<Nat>>>},
    b1: Array<+List<+List<Nat>>>,
    +eb1: {b1 == a1 : Array<+List<+List<Nat>>>},
    -b2: Array<+List<+List<Nat>>>,
    +eb2: {b2 == b1 : Array<+List<+List<Nat>>>},
    dp3: &c1: Array<+List<+List<Nat>>> -> &c2: Array<+List<+List<Nat>>> ->
         {c1 == b2 : Array<+List<+List<Nat>>>}
         & {c2 == c1 : Array<+List<+List<Nat>>>},
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb: FH.BktTree(10n, 0, bkts, fg0)) ->
  FH.FillSpec(SolveFast.fgroup_add_fast(w, fb, fg0), acc_touched,
    SolveFast.fill5_get_done(w, code, touched,
      Array.get(+List<+List<Nat>>, bkts, code))):
  (c1, dp4) = dp3
  (c2, pe3) = dp4
  (+ec1, +ec2) = pe3
  FH.fill5_step_false_dup3(w, fb, code, fg0, touched, acc_touched, bkts,
    a1, ea1, b1, eb1,
    c1, Equal.trans(Array<+List<+List<Nat>>>, c1, b2, b1, ec1, eb2),
    c2, ec2, ecode, hfb, hwf, etouched, hb)

def FH.fill5_step_false_dup2(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +code: U32, +fg0: +List<SolveFast.FGroup>, +touched: +List<U32>,
    +acc_touched: +List<U32>,
    -bkts: Array<+List<+List<Nat>>>,
    a1: Array<+List<+List<Nat>>>,
    +ea1: {a1 == bkts : Array<+List<+List<Nat>>>},
    -a2: Array<+List<+List<Nat>>>,
    +ea2: {a2 == a1 : Array<+List<+List<Nat>>>},
    dp2: &b1: Array<+List<+List<Nat>>> -> &b2: Array<+List<+List<Nat>>> ->
         {b1 == a2 : Array<+List<+List<Nat>>>}
         & {b2 == b1 : Array<+List<+List<Nat>>>},
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb: FH.BktTree(10n, 0, bkts, fg0)) ->
  FH.FillSpec(SolveFast.fgroup_add_fast(w, fb, fg0), acc_touched,
    SolveFast.fill5_get_done(w, code, touched,
      Array.get(+List<+List<Nat>>, bkts, code))):
  (b1, dp3) = dp2
  (b2, pe2) = dp3
  (+eb1, +eb2) = pe2
  FH.fill5_step_false_dup2b(w, fb, code, fg0, touched, acc_touched, bkts,
    a1, ea1,
    b1, Equal.trans(Array<+List<+List<Nat>>>, b1, a2, a1, eb1, ea2),
    b2, eb2, Arr.Arr.dup(+List<+List<Nat>>, b2),
    ecode, hfb, hwf, etouched, hb)

def FH.fill5_step_false_dup(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +code: U32, +fg0: +List<SolveFast.FGroup>, +touched: +List<U32>,
    +acc_touched: +List<U32>,
    -bkts: Array<+List<+List<Nat>>>,
    dp: &a1: Array<+List<+List<Nat>>> -> &a2: Array<+List<+List<Nat>>> ->
        {a1 == bkts : Array<+List<+List<Nat>>>}
        & {a2 == a1 : Array<+List<+List<Nat>>>},
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb: FH.BktTree(10n, 0, bkts, fg0)) ->
  FH.FillSpec(SolveFast.fgroup_add_fast(w, fb, fg0), acc_touched,
    SolveFast.fill5_get_done(w, code, touched,
      Array.get(+List<+List<Nat>>, bkts, code))):
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  FH.fill5_step_false_dup2(w, fb, code, fg0, touched, acc_touched, bkts,
    a1, ea1, a2, ea2, Arr.Arr.dup(+List<+List<Nat>>, a2),
    ecode, hfb, hwf, etouched, hb)

def FH.fill5_step_spec(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>,
    bkts: Array<+List<+List<Nat>>>, +touched: +List<U32>,
    +acc_touched: +List<U32>, +code: U32, same: Bool,
    +esame: {same == SolveFast.word_eq_fast(g, w) : Bool},
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +efb: {SolveFast.feedback_fast(g, w) == fb : +List<Feedback.Color>},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb: FH.BktTree(10n, 0, bkts, fg0)) ->
  FH.FillSpec(SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)),
    acc_touched, SolveFast.fill5_step(w, code, same, bkts, touched)):
  match same:
    case True{}:
      %esame : FH.FillSpec(SolveFast.fgroups_next_acc(g, w, fg0, _),
                 acc_touched, SolveFast.Fill5State{bkts, touched})
      Arr.DPair{hb, Arr.DPair{etouched, hwf}}
    case False{}:
      %esame : FH.FillSpec(SolveFast.fgroups_next_acc(g, w, fg0, _),
                 acc_touched,
                 SolveFast.fill5_get_done(w, code, touched,
                   Array.get(+List<+List<Nat>>, bkts, code)))
      %Equal.sym(+List<Feedback.Color>, SolveFast.feedback_fast(g, w), fb, efb) :
        FH.FillSpec(SolveFast.fgroup_add_fast(w, _, fg0), acc_touched,
          SolveFast.fill5_get_done(w, code, touched,
            Array.get(+List<+List<Nat>>, bkts, code)))
      FH.fill5_step_false_dup(w, fb, code, fg0, touched, acc_touched, bkts,
        Arr.Arr.dup(+List<+List<Nat>>, bkts), ecode, hfb, hwf, etouched, hb)

def FH.fill5_one_spec(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +w: +List<Nat>, +fg0: +List<SolveFast.FGroup>,
    bkts: Array<+List<+List<Nat>>>, +touched: +List<U32>,
    +acc_touched: +List<U32>,
    +h5w: {FH.is_word5(w) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb: FH.BktTree(10n, 0, bkts, fg0)) ->
  FH.FillSpec(
    SolveFast.fgroups_next_acc(
      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
      SolveFast.word_eq_fast(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w)),
    acc_touched,
    SolveFast.fill5_one(g0, g1, g2, g3, g4, w, bkts, touched)):
  match w:
    case Nil{}:
      Empty.absurd(
        FH.FillSpec(
          SolveFast.fgroups_next_acc(
            g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), Nil{}, fg0,
            SolveFast.word_eq_fast(
              g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), Nil{})),
          acc_touched, SolveFast.Fill5State{bkts, touched}),
        Logic.Proof.false_ne_true(h5w))
    case Con{+a0, +t1}:
      match t1:
        case Nil{}:
          Empty.absurd(
            FH.FillSpec(
              SolveFast.fgroups_next_acc(
                g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), a0 <> Nil{}, fg0,
                SolveFast.word_eq_fast(
                  g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), a0 <> Nil{})),
              acc_touched, SolveFast.Fill5State{bkts, touched}),
            Logic.Proof.false_ne_true(h5w))
        case Con{+a1, +t2}:
          match t2:
            case Nil{}:
              +aw : +List<Nat> = a0 <> (a1 <> Nil{})
              Empty.absurd(
                FH.FillSpec(
                  SolveFast.fgroups_next_acc(
                    g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), aw, fg0,
                    SolveFast.word_eq_fast(
                      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), aw)),
                  acc_touched, SolveFast.Fill5State{bkts, touched}),
                Logic.Proof.false_ne_true(h5w))
            case Con{+a2, +t3}:
              match t3:
                case Nil{}:
                  +aw : +List<Nat> = a0 <> (a1 <> (a2 <> Nil{}))
                  Empty.absurd(
                    FH.FillSpec(
                      SolveFast.fgroups_next_acc(
                        g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), aw, fg0,
                        SolveFast.word_eq_fast(
                          g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), aw)),
                      acc_touched, SolveFast.Fill5State{bkts, touched}),
                    Logic.Proof.false_ne_true(h5w))
                case Con{+a3, +t4}:
                  match t4:
                    case Nil{}:
                      +aw : +List<Nat> = a0 <> (a1 <> (a2 <> (a3 <> Nil{})))
                      Empty.absurd(
                        FH.FillSpec(
                          SolveFast.fgroups_next_acc(
                            g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), aw, fg0,
                            SolveFast.word_eq_fast(
                              g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), aw)),
                          acc_touched, SolveFast.Fill5State{bkts, touched}),
                        Logic.Proof.false_ne_true(h5w))
                    case Con{+a4, +t5}:
                      match t5:
                        case Nil{}:
                          +gw : +List<Nat> =
                            g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
                          +aw : +List<Nat> =
                            a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))
                          +code = SolveFast.feedback_code5(g0, g1, g2, g3, g4,
                                    a0, a1, a2, a3, a4)
                          +fb = Feedback.feedback(gw, aw)
                          +esame : {U32.is_eq(code, 682)
                                    == SolveFast.word_eq_fast(gw, aw) : Bool} =
                            Equal.trans(Bool, U32.is_eq(code, 682),
                              Feedback.word_eq(gw, aw),
                              SolveFast.word_eq_fast(gw, aw),
                              FF5.FF5.code5_is_682_eq(g0, g1, g2, g3, g4,
                                a0, a1, a2, a3, a4),
                              Equal.sym(Bool, SolveFast.word_eq_fast(gw, aw),
                                Feedback.word_eq(gw, aw),
                                FG.FG.word_eq_fast_eq(gw, aw)))
                          FH.fill5_step_spec(gw, aw, fb, fg0, bkts, touched,
                            acc_touched, code, U32.is_eq(code, 682), esame,
                            FF5.FF5.feedback_code5_eq(g0, g1, g2, g3, g4,
                              a0, a1, a2, a3, a4),
                            FG.FG.feedback_eq(gw, aw),
                            FF5.FF5.feedback_len5(g0, g1, g2, g3, g4,
                              a0, a1, a2, a3, a4),
                            hwf, etouched, hb)
                        case Con{+a5, +t6}:
                          +aw : +List<Nat> =
                            a0 <> (a1 <> (a2 <> (a3 <> (a4 <> (a5 <> t6)))))
                          Empty.absurd(
                            FH.FillSpec(
                              SolveFast.fgroups_next_acc(
                                g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
                                aw, fg0,
                                SolveFast.word_eq_fast(
                                  g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
                                  aw)),
                              acc_touched, SolveFast.Fill5State{bkts, touched}),
                            Logic.Proof.false_ne_true(h5w))

def FH.fill5_go_step_dup(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +w: +List<Nat>, +rest: +List<+List<Nat>>, +fg0: +List<SolveFast.FGroup>,
    +acc_touched: +List<U32>,
    -bkts2: Array<+List<+List<Nat>>>, +touched2: +List<U32>,
    +h1: FH.FillSpec(
           SolveFast.fgroups_next_acc(
             g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
             SolveFast.word_eq_fast(
               g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w)),
           acc_touched, SolveFast.Fill5State{bkts2, touched2}),
    dp: &b1: Array<+List<+List<Nat>>> -> &b2: Array<+List<+List<Nat>>> ->
        {b1 == bkts2 : Array<+List<+List<Nat>>>}
        & {b2 == b1 : Array<+List<+List<Nat>>>},
    rec: @b2: Array<+List<+List<Nat>>> -> @+t2: +List<U32> ->
         {FH.fgroups_wf(
            SolveFast.fgroups_next_acc(
              g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
              SolveFast.word_eq_fast(
                g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w)))
          == True{} : Bool} ->
         {t2 == FH.rev_codes(
                  SolveFast.fgroups_next_acc(
                    g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
                    SolveFast.word_eq_fast(
                      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w)),
                  acc_touched) : +List<U32>} ->
         FH.BktTree(10n, 0, b2,
           SolveFast.fgroups_next_acc(
             g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
             SolveFast.word_eq_fast(
               g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w))) ->
         FH.FillSpec(
           SolveFast.fgroups_build_fast(
             g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w <> rest, fg0),
           acc_touched,
           SolveFast.fill5_go(g0, g1, g2, g3, g4, rest,
             SolveFast.Fill5State{b2, t2}))) ->
  FH.FillSpec(
    SolveFast.fgroups_build_fast(
      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w <> rest, fg0),
    acc_touched,
    SolveFast.fill5_go(g0, g1, g2, g3, g4, rest,
      SolveFast.Fill5State{bkts2, touched2})):
  (b1, dp2) = dp
  (b2, pe) = dp2
  (+eb1, +eb2) = pe
  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
  +fg1 = SolveFast.fgroups_next_acc(gw, w, fg0, SolveFast.word_eq_fast(gw, w))
  +fg_end = SolveFast.fgroups_build_fast(gw, w <> rest, fg0)
  +hb2 = Arr.Arr.dpair_l(
           FH.BktTree(10n, 0, bkts2, fg1),
           Arr.Arr.DPair<
             {touched2 == FH.rev_codes(fg1, acc_touched) : +List<U32>},
             {FH.fgroups_wf(fg1) == True{} : Bool}>, h1)
  +hr = Arr.Arr.dpair_r(
          FH.BktTree(10n, 0, bkts2, fg1),
          Arr.Arr.DPair<
            {touched2 == FH.rev_codes(fg1, acc_touched) : +List<U32>},
            {FH.fgroups_wf(fg1) == True{} : Bool}>, h1)
  +et2 = Arr.Arr.dpair_l(
           {touched2 == FH.rev_codes(fg1, acc_touched) : +List<U32>},
           {FH.fgroups_wf(fg1) == True{} : Bool}, hr)
  +hwf1 = Arr.Arr.dpair_r(
            {touched2 == FH.rev_codes(fg1, acc_touched) : +List<U32>},
            {FH.fgroups_wf(fg1) == True{} : Bool}, hr)
  +eb2_bk : {b2 == bkts2 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, b2, b1, bkts2, eb2, eb1)
  +hb_b2 = FH.bkt_tree_transport(10n, 0, bkts2, b2, fg1,
             Equal.sym(Array<+List<+List<Nat>>>, b2, bkts2, eb2_bk), hb2)
  +hrec_b2 = rec(b2, touched2, hwf1, et2, hb_b2)
  +hrec_b1 = FH.fill_spec_transport(fg_end, acc_touched,
               SolveFast.fill5_go(g0, g1, g2, g3, g4, rest,
                 SolveFast.Fill5State{b2, touched2}),
               SolveFast.fill5_go(g0, g1, g2, g3, g4, rest,
                 SolveFast.Fill5State{b1, touched2}),
               Equal.cong(Array<+List<+List<Nat>>>, SolveFast.Fill5State,
                 x => SolveFast.fill5_go(g0, g1, g2, g3, g4, rest,
                        SolveFast.Fill5State{x, touched2}),
                 b2, b1, eb2),
               hrec_b2)
  %eb1 : FH.FillSpec(fg_end, acc_touched,
           SolveFast.fill5_go(g0, g1, g2, g3, g4, rest,
             SolveFast.Fill5State{_, touched2}))
  hrec_b1

def FH.fill5_go_step(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +w: +List<Nat>, +rest: +List<+List<Nat>>, +fg0: +List<SolveFast.FGroup>,
    +acc_touched: +List<U32>, st1: SolveFast.Fill5State,
    +h1: FH.FillSpec(
           SolveFast.fgroups_next_acc(
             g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
             SolveFast.word_eq_fast(
               g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w)),
           acc_touched, st1),
    rec: @b2: Array<+List<+List<Nat>>> -> @+t2: +List<U32> ->
         {FH.fgroups_wf(
            SolveFast.fgroups_next_acc(
              g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
              SolveFast.word_eq_fast(
                g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w)))
          == True{} : Bool} ->
         {t2 == FH.rev_codes(
                  SolveFast.fgroups_next_acc(
                    g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
                    SolveFast.word_eq_fast(
                      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w)),
                  acc_touched) : +List<U32>} ->
         FH.BktTree(10n, 0, b2,
           SolveFast.fgroups_next_acc(
             g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
             SolveFast.word_eq_fast(
               g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w))) ->
         FH.FillSpec(
           SolveFast.fgroups_build_fast(
             g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w <> rest, fg0),
           acc_touched,
           SolveFast.fill5_go(g0, g1, g2, g3, g4, rest,
             SolveFast.Fill5State{b2, t2}))) ->
  FH.FillSpec(
    SolveFast.fgroups_build_fast(
      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w <> rest, fg0),
    acc_touched,
    SolveFast.fill5_go(g0, g1, g2, g3, g4, rest, st1)):
  match st1:
    case SolveFast.Fill5State{bkts2, +touched2}:
      FH.fill5_go_step_dup(g0, g1, g2, g3, g4, w, rest, fg0, acc_touched,
        bkts2, touched2, h1, Arr.Arr.dup(+List<+List<Nat>>, bkts2), rec)

def FH.fill5_go_cons_dup(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +w: +List<Nat>, +rest: +List<+List<Nat>>, +fg0: +List<SolveFast.FGroup>,
    -bkts: Array<+List<+List<Nat>>>, +touched: +List<U32>,
    +acc_touched: +List<U32>,
    +h5w: {FH.is_word5(w) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb: FH.BktTree(10n, 0, bkts, fg0),
    dp: &b1: Array<+List<+List<Nat>>> -> &b2: Array<+List<+List<Nat>>> ->
        {b1 == bkts : Array<+List<+List<Nat>>>}
        & {b2 == b1 : Array<+List<+List<Nat>>>},
    rec: @b2: Array<+List<+List<Nat>>> -> @+t2: +List<U32> ->
         {FH.fgroups_wf(
            SolveFast.fgroups_next_acc(
              g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
              SolveFast.word_eq_fast(
                g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w)))
          == True{} : Bool} ->
         {t2 == FH.rev_codes(
                  SolveFast.fgroups_next_acc(
                    g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
                    SolveFast.word_eq_fast(
                      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w)),
                  acc_touched) : +List<U32>} ->
         FH.BktTree(10n, 0, b2,
           SolveFast.fgroups_next_acc(
             g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w, fg0,
             SolveFast.word_eq_fast(
               g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w))) ->
         FH.FillSpec(
           SolveFast.fgroups_build_fast(
             g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w <> rest, fg0),
           acc_touched,
           SolveFast.fill5_go(g0, g1, g2, g3, g4, rest,
             SolveFast.Fill5State{b2, t2}))) ->
  FH.FillSpec(
    SolveFast.fgroups_build_fast(
      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), w <> rest, fg0),
    acc_touched,
    SolveFast.fill5_go(g0, g1, g2, g3, g4, rest,
      SolveFast.fill5_one(g0, g1, g2, g3, g4, w, bkts, touched))):
  (b1, dp2) = dp
  (b2, pe) = dp2
  (+eb1, +eb2) = pe
  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
  +fg1 = SolveFast.fgroups_next_acc(gw, w, fg0, SolveFast.word_eq_fast(gw, w))
  +fg_end = SolveFast.fgroups_build_fast(gw, w <> rest, fg0)
  +eb2_bk : {b2 == bkts : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, b2, b1, bkts, eb2, eb1)
  +hb2 = FH.bkt_tree_transport(10n, 0, bkts, b2, fg0,
           Equal.sym(Array<+List<+List<Nat>>>, b2, bkts, eb2_bk), hb)
  +h1_b2 = FH.fill5_one_spec(g0, g1, g2, g3, g4, w, fg0, b2, touched,
             acc_touched, h5w, hwf, etouched, hb2)
  +e1_eq : {SolveFast.fill5_one(g0, g1, g2, g3, g4, w, b2, touched)
            == SolveFast.fill5_one(g0, g1, g2, g3, g4, w, b1, touched)
            : SolveFast.Fill5State} =
    Equal.cong(Array<+List<+List<Nat>>>, SolveFast.Fill5State,
      x => SolveFast.fill5_one(g0, g1, g2, g3, g4, w, x, touched),
      b2, b1, eb2)
  %eb1 : FH.FillSpec(fg_end, acc_touched,
           SolveFast.fill5_go(g0, g1, g2, g3, g4, rest,
             SolveFast.fill5_one(g0, g1, g2, g3, g4, w, _, touched)))
  FH.fill5_go_step(g0, g1, g2, g3, g4, w, rest, fg0, acc_touched,
    SolveFast.fill5_one(g0, g1, g2, g3, g4, w, b1, touched),
    FH.fill_spec_transport(fg1, acc_touched,
      SolveFast.fill5_one(g0, g1, g2, g3, g4, w, b2, touched),
      SolveFast.fill5_one(g0, g1, g2, g3, g4, w, b1, touched),
      e1_eq, h1_b2),
    rec)

def FH.fill5_go_spec(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +S: +List<+List<Nat>>, +fg0: +List<SolveFast.FGroup>,
    bkts: Array<+List<+List<Nat>>>, +touched: +List<U32>,
    +acc_touched: +List<U32>,
    +hall5: {FH.all_len5(S) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb: FH.BktTree(10n, 0, bkts, fg0)) ->
  FH.FillSpec(
    SolveFast.fgroups_build_fast(
      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), S, fg0),
    acc_touched,
    SolveFast.fill5_go(g0, g1, g2, g3, g4, S,
      SolveFast.Fill5State{bkts, touched})):
  match S:
    case Nil{}:
      Arr.DPair{hb, Arr.DPair{etouched, hwf}}
    case Con{+w, +rest}:
      +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
      +fg1 = SolveFast.fgroups_next_acc(gw, w, fg0,
               SolveFast.word_eq_fast(gw, w))
      +h5w = Logic.Proof.and_true_l(FH.is_word5(w), FH.all_len5(rest), hall5)
      +h5r = Logic.Proof.and_true_r(FH.is_word5(w), FH.all_len5(rest), hall5)
      FH.fill5_go_cons_dup(g0, g1, g2, g3, g4, w, rest, fg0, bkts, touched,
        acc_touched, h5w, hwf, etouched, hb,
        Arr.Arr.dup(+List<+List<Nat>>, bkts),
        b2 => t2 => hwf1 => et2 => hb2 =>
          FH.fill5_go_spec(g0, g1, g2, g3, g4, rest, fg1, b2, t2, acc_touched,
            h5r, hwf1, et2, hb2))


# ---------------------------------------------------------------------------
# Pass 2b: `drain5_go` empties `buckets` back to `Nil{}` and emits exact items
# ---------------------------------------------------------------------------

def FH.list_append_nil(-T: Data, +xs: +List<T>) ->
  {List.append(&2, T, xs, Nil{}) == xs : +List<T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(+List<T>, +List<T>, r => h <> r,
        List.append(&2, T, t, Nil{}), t, FH.list_append_nil(T, t))

def FH.list_append_assoc(-T: Data, +xs: +List<T>, +ys: +List<T>,
    +zs: +List<T>) ->
  {List.append(&2, T, List.append(&2, T, xs, ys), zs)
   == List.append(&2, T, xs, List.append(&2, T, ys, zs)) : +List<T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(+List<T>, +List<T>, r => h <> r,
        List.append(&2, T, List.append(&2, T, t, ys), zs),
        List.append(&2, T, t, List.append(&2, T, ys, zs)),
        FH.list_append_assoc(T, t, ys, zs))

def FH.rev_codes_append(+fg: +List<SolveFast.FGroup>, +acc: +List<U32>) ->
  {FH.rev_codes(fg, acc)
   == List.append(&2, U32, FH.rev_codes(fg, Nil{}), acc) : +List<U32>}:
  match fg:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          +c = FF5.FF5.encode_fb5_list(f)
          Equal.trans(+List<U32>,
            FH.rev_codes(rest, c <> acc),
            List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> acc),
            List.append(&2, U32, FH.rev_codes(rest, c <> Nil{}), acc),
            FH.rev_codes_append(rest, c <> acc),
            Equal.trans(+List<U32>,
              List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> acc),
              List.append(&2, U32,
                List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
                acc),
              List.append(&2, U32, FH.rev_codes(rest, c <> Nil{}), acc),
              Equal.sym(+List<U32>,
                List.append(&2, U32,
                  List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
                  acc),
                List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> acc),
                FH.list_append_assoc(U32, FH.rev_codes(rest, Nil{}),
                  c <> Nil{}, acc)),
              Equal.cong(+List<U32>, +List<U32>,
                ts => List.append(&2, U32, ts, acc),
                List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
                FH.rev_codes(rest, c <> Nil{}),
                Equal.sym(+List<U32>,
                  FH.rev_codes(rest, c <> Nil{}),
                  List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
                  FH.rev_codes_append(rest, c <> Nil{})))))

def FH.drain5_go_append(+ts1: +List<U32>, +ts2: +List<U32>,
    st: SolveFast.Drain5State) ->
  {SolveFast.drain5_go(List.append(&2, U32, ts1, ts2), st)
   == SolveFast.drain5_go(ts2, SolveFast.drain5_go(ts1, st))
   : SolveFast.Drain5State}:
  match ts1:
    case Nil{}:
      {==}
    case Con{+code, +rest}:
      match st:
        case SolveFast.Drain5State{bkts, +rem_lb, +items}:
          FH.drain5_go_append(rest, ts2,
            SolveFast.drain5_swap(code, rem_lb, items,
              Array.swap(+List<+List<Nat>>, bkts, code, Nil{})))

def FH.disjoint_codes(+pre: +List<SolveFast.FGroup>,
    +fg: +List<SolveFast.FGroup>) -> Bool:
  match fg:
    case Nil{}:
      True{}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{f, len, rws}:
          Bool.and(Bool.not(FH.has_code(FF5.FF5.encode_fb5_list(f), pre)),
            FH.disjoint_codes(pre, rest))

def FH.disjoint_codes_nil(+fg: +List<SolveFast.FGroup>) ->
  {FH.disjoint_codes(Nil{}, fg) == True{} : Bool}:
  match fg:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{f, len, rws}:
          FH.disjoint_codes_nil(rest)

def FH.has_code_append_snoc_false(+c: U32, +pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +hpre: {FH.has_code(c, pre) == False{} : Bool},
    +hne: {U32.is_eq(c, FF5.FF5.encode_fb5_list(f)) == False{} : Bool}) ->
  {FH.has_code(c,
     List.append(&2, SolveFast.FGroup, pre,
       SolveFast.FGroup{f, len, rws} <> Nil{})) == False{} : Bool}:
  match pre:
    case Nil{}:
      Equal.trans(Bool,
        Bool.or(U32.is_eq(c, FF5.FF5.encode_fb5_list(f)), False{}),
        Bool.or(False{}, False{}), False{},
        Equal.cong(Bool, Bool, b => Bool.or(b, False{}),
          U32.is_eq(c, FF5.FF5.encode_fb5_list(f)), False{}, hne),
        {==})
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+fh, +lh, +rh}:
          +h1 = FH.bool_or_false_l_inv(
                  U32.is_eq(c, FF5.FF5.encode_fb5_list(fh)),
                  FH.has_code(c, rest), hpre)
          +h2 = FH.bool_or_false_r_inv(
                  U32.is_eq(c, FF5.FF5.encode_fb5_list(fh)),
                  FH.has_code(c, rest), hpre)
          Equal.trans(Bool,
            Bool.or(U32.is_eq(c, FF5.FF5.encode_fb5_list(fh)),
              FH.has_code(c,
                List.append(&2, SolveFast.FGroup, rest,
                  SolveFast.FGroup{f, len, rws} <> Nil{}))),
            Bool.or(False{},
              FH.has_code(c,
                List.append(&2, SolveFast.FGroup, rest,
                  SolveFast.FGroup{f, len, rws} <> Nil{}))),
            False{},
            Equal.cong(Bool, Bool,
              b => Bool.or(b,
                     FH.has_code(c,
                       List.append(&2, SolveFast.FGroup, rest,
                         SolveFast.FGroup{f, len, rws} <> Nil{}))),
              U32.is_eq(c, FF5.FF5.encode_fb5_list(fh)), False{}, h1),
            FH.has_code_append_snoc_false(c, rest, f, len, rws, h2, hne))

def FH.disjoint_codes_snoc(+pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>,
    +hdisj: {FH.disjoint_codes(pre, rest) == True{} : Bool},
    +hnot: {FH.has_code(FF5.FF5.encode_fb5_list(f), rest) == False{} : Bool}) ->
  {FH.disjoint_codes(
     List.append(&2, SolveFast.FGroup, pre,
       SolveFast.FGroup{f, len, rws} <> Nil{}),
     rest) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case Con{gp2, rest2}:
      match gp2:
        case SolveFast.FGroup{+f2, +len2, +rws2}:
          +c = FF5.FF5.encode_fb5_list(f)
          +c2 = FF5.FF5.encode_fb5_list(f2)
          +hd1 = Logic.Proof.and_true_l(Bool.not(FH.has_code(c2, pre)),
                   FH.disjoint_codes(pre, rest2), hdisj)
          +hd2 = Logic.Proof.and_true_r(Bool.not(FH.has_code(c2, pre)),
                   FH.disjoint_codes(pre, rest2), hdisj)
          +hpre_f : {FH.has_code(c2, pre) == False{} : Bool} =
            FH.bool_false_of_not_true(FH.has_code(c2, pre), hd1)
          +hne_cc2 : {U32.is_eq(c, c2) == False{} : Bool} =
            FH.bool_or_false_l_inv(U32.is_eq(c, c2),
              FH.has_code(c, rest2), hnot)
          +hnot2 : {FH.has_code(c, rest2) == False{} : Bool} =
            FH.bool_or_false_r_inv(U32.is_eq(c, c2),
              FH.has_code(c, rest2), hnot)
          +hne_c2c : {U32.is_eq(c2, c) == False{} : Bool} =
            Equal.trans(Bool, U32.is_eq(c2, c), U32.is_eq(c, c2), False{},
              FH.u32_eq_sym_bool(c2, c), hne_cc2)
          +pre2 = List.append(&2, SolveFast.FGroup, pre,
                    SolveFast.FGroup{f, len, rws} <> Nil{})
          FH.bool_and_intro(
            Bool.not(FH.has_code(c2, pre2)),
            FH.disjoint_codes(pre2, rest2),
            FH.bool_not_true_of_false(FH.has_code(c2, pre2),
              FH.has_code_append_snoc_false(c2, pre, f, len, rws,
                hpre_f, hne_c2c)),
            FH.disjoint_codes_snoc(pre, f, len, rws, rest2, hd2, hnot2))

def FH.DrainSpec(+pre: +List<SolveFast.FGroup>, +fg: +List<SolveFast.FGroup>,
    +rem_lb: Nat, +items: +List<SolveFast.Item>,
    dr: SolveFast.Drain5State) -> Data:
  match dr:
    case SolveFast.Drain5State{bkts2, lb2, items2}:
      Arr.Arr.DPair<
        FH.BktTree(10n, 0, bkts2, pre),
        {SolveFast.ItemsBound{lb2, items2}
         == SolveFast.fgroup_items_build(True{}, rem_lb, fg, items)
         : SolveFast.ItemsBound}>

def FH.drain_spec_transport(+pre: +List<SolveFast.FGroup>,
    +fg: +List<SolveFast.FGroup>, +rem_lb: Nat, +items: +List<SolveFast.Item>,
    -dr1: SolveFast.Drain5State, -dr2: SolveFast.Drain5State,
    +ed: {dr1 == dr2 : SolveFast.Drain5State},
    +h: FH.DrainSpec(pre, fg, rem_lb, items, dr1)) ->
  FH.DrainSpec(pre, fg, rem_lb, items, dr2):
  %ed : FH.DrainSpec(pre, fg, rem_lb, items, _)
  h

def FH.drain5_add_spec(+pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +rem_lb: Nat, +items: +List<SolveFast.Item>,
    -bkts3: Array<+List<+List<Nat>>>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +heql: {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool},
    +hb3: FH.BktTree(10n, 0, bkts3, pre),
    +eib2: {SolveFast.ItemsBound{lb2, items2}
            == SolveFast.fgroup_items_build(True{}, rem_lb, rest, items)
            : SolveFast.ItemsBound}) ->
  FH.DrainSpec(pre, SolveFast.FGroup{f, len, rws} <> rest, rem_lb, items,
    SolveFast.drain5_add(FF5.FF5.encode_fb5_list(f), lb2, items2, bkts3, rws)):
  match rws:
    case Nil{}:
      +c = FF5.FF5.encode_fb5_list(f)
      +edec : {SolveFast.decode_fb5(c) == f : +List<Feedback.Color>} =
        FF5.FF5.decode_encode_list(f, hf5)
      Arr.DPair{hb3,
        Equal.trans(SolveFast.ItemsBound,
          SolveFast.ItemsBound{lb2,
            SolveFast.ClassItem{SolveFast.decode_fb5(c), Nil{}, 0n, lb2}
              <> (SolveFast.Add{SolveFast.decode_fb5(c), lb2} <> items2)},
          SolveFast.group_items_step(f, Nil{}, 0n, 0n,
            SolveFast.ItemsBound{lb2, items2}),
          SolveFast.group_items_step(f, Nil{}, 0n, 0n,
            SolveFast.fgroup_items_build(True{}, rem_lb, rest, items)),
          Equal.cong(+List<Feedback.Color>, SolveFast.ItemsBound,
            fb => SolveFast.ItemsBound{lb2,
                    SolveFast.ClassItem{fb, Nil{}, 0n, lb2}
                      <> (SolveFast.Add{fb, lb2} <> items2)},
            SolveFast.decode_fb5(c), f, edec),
          Equal.cong(SolveFast.ItemsBound, SolveFast.ItemsBound,
            ib => SolveFast.group_items_step(f, Nil{}, 0n, 0n, ib),
            SolveFast.ItemsBound{lb2, items2},
            SolveFast.fgroup_items_build(True{}, rem_lb, rest, items),
            eib2))}
    case Con{+w, +wt}:
      match wt:
        case Nil{}:
          +c = FF5.FF5.encode_fb5_list(f)
          +edec : {SolveFast.decode_fb5(c) == f : +List<Feedback.Color>} =
            FF5.FF5.decode_encode_list(f, hf5)
          Arr.DPair{hb3,
            Equal.trans(SolveFast.ItemsBound,
              SolveFast.ItemsBound{Nat.add(1n, lb2),
                SolveFast.OneItem{SolveFast.decode_fb5(c), w} <> items2},
              SolveFast.group_items_one_step(f, w,
                SolveFast.ItemsBound{lb2, items2}),
              SolveFast.group_items_one_step(f, w,
                SolveFast.fgroup_items_build(True{}, rem_lb, rest, items)),
              Equal.cong(+List<Feedback.Color>, SolveFast.ItemsBound,
                fb => SolveFast.ItemsBound{Nat.add(1n, lb2),
                        SolveFast.OneItem{fb, w} <> items2},
                SolveFast.decode_fb5(c), f, edec),
              Equal.cong(SolveFast.ItemsBound, SolveFast.ItemsBound,
                ib => SolveFast.group_items_one_step(f, w, ib),
                SolveFast.ItemsBound{lb2, items2},
                SolveFast.fgroup_items_build(True{}, rem_lb, rest, items),
                eib2))}
        case Con{+w2, +wt2}:
          +c = FF5.FF5.encode_fb5_list(f)
          +edec : {SolveFast.decode_fb5(c) == f : +List<Feedback.Color>} =
            FF5.FF5.decode_encode_list(f, hf5)
          +acc2 : +List<+List<Nat>> = w2 <> (w <> Nil{})
          +ws : +List<+List<Nat>> = SolveFast.rev_words(wt2, acc2)
          +len2 : Nat = Nat.add(2n, Groups.len_words(wt2))
          +elen : {len2 == len : Nat} =
            Equal.sym(Nat, len, len2,
              NatProof.NatPrf.is_eq_true(len, len2, heql))
          +erl : {SolveFast.rev_words_len(wt2, acc2, 2n)
                  == SolveFast.RevLen{len2, ws} : SolveFast.RevLen} =
            FH.rev_words_len_eq(wt2, acc2, 2n)
          %Equal.sym(SolveFast.RevLen,
             SolveFast.rev_words_len(wt2, acc2, 2n),
             SolveFast.RevLen{len2, ws}, erl) :
            FH.DrainSpec(pre,
              SolveFast.FGroup{f, len, w <> (w2 <> wt2)} <> rest,
              rem_lb, items,
              SolveFast.drain5_add_ge2(SolveFast.decode_fb5(c), lb2, items2,
                bkts3, _))
          +clb2 = Nat.sub(Nat.add(len2, len2), 1n)
          +clb = Nat.sub(Nat.add(len, len), 1n)
          Arr.DPair{hb3,
            Equal.trans(SolveFast.ItemsBound,
              SolveFast.ItemsBound{Nat.add(clb2, lb2),
                SolveFast.ClassItem{SolveFast.decode_fb5(c), ws, len2, lb2}
                  <> (SolveFast.Add{SolveFast.decode_fb5(c), lb2} <> items2)},
              SolveFast.group_items_step(f, ws, len, clb,
                SolveFast.ItemsBound{lb2, items2}),
              SolveFast.group_items_step(f, ws, len, clb,
                SolveFast.fgroup_items_build(True{}, rem_lb, rest, items)),
              Equal.trans(SolveFast.ItemsBound,
                SolveFast.ItemsBound{Nat.add(clb2, lb2),
                  SolveFast.ClassItem{SolveFast.decode_fb5(c), ws, len2, lb2}
                    <> (SolveFast.Add{SolveFast.decode_fb5(c), lb2} <> items2)},
                SolveFast.ItemsBound{Nat.add(clb2, lb2),
                  SolveFast.ClassItem{f, ws, len2, lb2}
                    <> (SolveFast.Add{f, lb2} <> items2)},
                SolveFast.ItemsBound{Nat.add(clb, lb2),
                  SolveFast.ClassItem{f, ws, len, lb2}
                    <> (SolveFast.Add{f, lb2} <> items2)},
                Equal.cong(+List<Feedback.Color>, SolveFast.ItemsBound,
                  fb => SolveFast.ItemsBound{Nat.add(clb2, lb2),
                          SolveFast.ClassItem{fb, ws, len2, lb2}
                            <> (SolveFast.Add{fb, lb2} <> items2)},
                  SolveFast.decode_fb5(c), f, edec),
                Equal.cong(Nat, SolveFast.ItemsBound,
                  l => SolveFast.ItemsBound{
                         Nat.add(Nat.sub(Nat.add(l, l), 1n), lb2),
                         SolveFast.ClassItem{f, ws, l, lb2}
                           <> (SolveFast.Add{f, lb2} <> items2)},
                  len2, len, elen)),
              Equal.cong(SolveFast.ItemsBound, SolveFast.ItemsBound,
                ib => SolveFast.group_items_step(f, ws, len, clb, ib),
                SolveFast.ItemsBound{lb2, items2},
                SolveFast.fgroup_items_build(True{}, rem_lb, rest, items),
                eib2))}

def FH.drain5_swap_pair(+pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +rem_lb: Nat, +items: +List<SolveFast.Item>,
    +lb2: Nat, +items2: +List<SolveFast.Item>,
    r: Array<+List<+List<Nat>>> & +List<+List<Nat>>,
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +heql: {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool},
    +hb3: FH.BktTree(10n, 0,
            Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>, r), pre),
    +erws: {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>, r)
            == rws : +List<+List<Nat>>},
    +eib2: {SolveFast.ItemsBound{lb2, items2}
            == SolveFast.fgroup_items_build(True{}, rem_lb, rest, items)
            : SolveFast.ItemsBound}) ->
  FH.DrainSpec(pre, SolveFast.FGroup{f, len, rws} <> rest, rem_lb, items,
    SolveFast.drain5_swap(FF5.FF5.encode_fb5_list(f), lb2, items2, r)):
  (bkts3, +rws_got) = r
  %Equal.sym(+List<+List<Nat>>, rws_got, rws, erws) :
    FH.DrainSpec(pre, SolveFast.FGroup{f, len, rws} <> rest, rem_lb, items,
      SolveFast.drain5_add(FF5.FF5.encode_fb5_list(f), lb2, items2, bkts3, _))
  FH.drain5_add_spec(pre, f, len, rws, rest, rem_lb, items, bkts3, lb2, items2,
    hf5, heql, hb3, eib2)

def FH.drain5_one_dup4(+pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +rem_lb: Nat, +items: +List<SolveFast.Item>,
    -bkts2: Array<+List<+List<Nat>>>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    a1: Array<+List<+List<Nat>>>,
    +ea1: {a1 == bkts2 : Array<+List<+List<Nat>>>},
    b1: Array<+List<+List<Nat>>>,
    +eb1: {b1 == a1 : Array<+List<+List<Nat>>>},
    c1: Array<+List<+List<Nat>>>,
    +ec1: {c1 == b1 : Array<+List<+List<Nat>>>},
    d1: Array<+List<+List<Nat>>>,
    +ed1: {d1 == c1 : Array<+List<+List<Nat>>>},
    d2: Array<+List<+List<Nat>>>,
    +ed2: {d2 == d1 : Array<+List<+List<Nat>>>},
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +heql: {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hb2: FH.BktTree(10n, 0, bkts2,
            List.append(&2, SolveFast.FGroup, pre,
              SolveFast.FGroup{f, len, rws} <> Nil{})),
    +eib2: {SolveFast.ItemsBound{lb2, items2}
            == SolveFast.fgroup_items_build(True{}, rem_lb, rest, items)
            : SolveFast.ItemsBound}) ->
  FH.DrainSpec(pre, SolveFast.FGroup{f, len, rws} <> rest, rem_lb, items,
    SolveFast.drain5_swap(FF5.FF5.encode_fb5_list(f), lb2, items2,
      Array.swap(+List<+List<Nat>>, bkts2, FF5.FF5.encode_fb5_list(f), Nil{}))):
  +c = FF5.FF5.encode_fb5_list(f)
  +gp : SolveFast.FGroup = SolveFast.FGroup{f, len, rws}
  +pre2 = List.append(&2, SolveFast.FGroup, pre, gp <> Nil{})
  +eb1_b : {b1 == bkts2 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, b1, a1, bkts2, eb1, ea1)
  +ec1_a : {c1 == a1 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, c1, b1, a1, ec1, eb1)
  +ec1_b : {c1 == bkts2 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, c1, b1, bkts2, ec1, eb1_b)
  +ed1_a : {d1 == a1 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, d1, c1, a1, ed1, ec1_a)
  +ed1_b : {d1 == bkts2 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, d1, c1, bkts2, ed1, ec1_b)
  +ed2_a : {d2 == a1 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, d2, d1, a1, ed2, ed1_a)
  +ed2_b : {d2 == bkts2 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, d2, d1, bkts2, ed2, ed1_b)
  +hb_b1 = FH.bkt_tree_transport(10n, 0, bkts2, b1, pre2,
             Equal.sym(Array<+List<+List<Nat>>>, b1, bkts2, eb1_b), hb2)
  +hb_c1 = FH.bkt_tree_transport(10n, 0, bkts2, c1, pre2,
             Equal.sym(Array<+List<+List<Nat>>>, c1, bkts2, ec1_b), hb2)
  +hb_d2 = FH.bkt_tree_transport(10n, 0, bkts2, d2, pre2,
             Equal.sym(Array<+List<+List<Nat>>>, d2, bkts2, ed2_b), hb2)
  +hok : {FH.bkt_op_ok(OpClear{gp}, pre) == True{} : Bool} =
    FH.bool_and_intro(FF5.FF5.is_fb5(f), Bool.not(FH.has_code(c, pre)),
      hf5, FH.bool_not_true_of_false(FH.has_code(c, pre), hnh))
  +hb3_b1 = FH.bkt_tree_swap(b1, OpClear{gp}, pre, hok, hb_b1)
  +hb3_a1 = FH.bkt_tree_transport(10n, 0,
              Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                Array.swap(+List<+List<Nat>>, b1, c, Nil{})),
              Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                Array.swap(+List<+List<Nat>>, a1, c, Nil{})),
              pre,
              Equal.cong(Array<+List<+List<Nat>>>, Array<+List<+List<Nat>>>,
                x => Arr.Arr.fst(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                       Array.swap(+List<+List<Nat>>, x, c, Nil{})),
                b1, a1, eb1),
              hb3_b1)
  +hd_c1 = FH.bkt_tree_depth(10n, 0, c1, pre2, hb_c1)
  +hd_d1 = Arr.Arr.depth_transport(+List<+List<Nat>>, 10n, c1, d1,
             Equal.sym(Array<+List<+List<Nat>>>, d1, c1, ed1), hd_c1)
  +eold_d1 : {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                Array.swap(+List<+List<Nat>>, d1, c, Nil{}))
              == Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                   Array.get(+List<+List<Nat>>, d1, c))
              : +List<+List<Nat>>} =
    Arr.Arr.swap_old(+List<+List<Nat>>, 10n, d1, c, Nil{}, hd_d1)
  +eget_d2 : {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                Array.get(+List<+List<Nat>>, d2, c))
              == FH.lookup_code(c, pre2) : +List<+List<Nat>>} =
    FH.bkt_tree_get(d2, pre2, c, FF5.FF5.encode_fb5_list_zero_from(f, hf5),
      hb_d2)
  +erws_a1 : {Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                Array.swap(+List<+List<Nat>>, a1, c, Nil{}))
              == rws : +List<+List<Nat>>} =
    Equal.trans(+List<+List<Nat>>,
      Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
        Array.swap(+List<+List<Nat>>, a1, c, Nil{})),
      FH.lookup_code(c, pre2),
      rws,
      Equal.trans(+List<+List<Nat>>,
        Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
          Array.swap(+List<+List<Nat>>, a1, c, Nil{})),
        Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
          Array.get(+List<+List<Nat>>, d2, c)),
        FH.lookup_code(c, pre2),
        Equal.trans(+List<+List<Nat>>,
          Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
            Array.swap(+List<+List<Nat>>, a1, c, Nil{})),
          Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
            Array.swap(+List<+List<Nat>>, d1, c, Nil{})),
          Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
            Array.get(+List<+List<Nat>>, d2, c)),
          Equal.cong(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
            x => Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                   Array.swap(+List<+List<Nat>>, x, c, Nil{})),
            a1, d1, Equal.sym(Array<+List<+List<Nat>>>, d1, a1, ed1_a)),
          Equal.trans(+List<+List<Nat>>,
            Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
              Array.swap(+List<+List<Nat>>, d1, c, Nil{})),
            Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
              Array.get(+List<+List<Nat>>, d1, c)),
            Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
              Array.get(+List<+List<Nat>>, d2, c)),
            eold_d1,
            Equal.cong(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
              x => Arr.Arr.snd(Array<+List<+List<Nat>>>, +List<+List<Nat>>,
                     Array.get(+List<+List<Nat>>, x, c)),
              d1, d2, Equal.sym(Array<+List<+List<Nat>>>, d2, d1, ed2)))),
        eget_d2),
      FH.lookup_append_last(pre, f, len, rws, hnh))
  %ea1 : FH.DrainSpec(pre, gp <> rest, rem_lb, items,
           SolveFast.drain5_swap(c, lb2, items2,
             Array.swap(+List<+List<Nat>>, _, c, Nil{})))
  FH.drain5_swap_pair(pre, f, len, rws, rest, rem_lb, items, lb2, items2,
    Array.swap(+List<+List<Nat>>, a1, c, Nil{}),
    hf5, heql, hb3_a1, erws_a1, eib2)

def FH.drain5_one_dup3(+pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +rem_lb: Nat, +items: +List<SolveFast.Item>,
    -bkts2: Array<+List<+List<Nat>>>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    a1: Array<+List<+List<Nat>>>,
    +ea1: {a1 == bkts2 : Array<+List<+List<Nat>>>},
    b1: Array<+List<+List<Nat>>>,
    +eb1: {b1 == a1 : Array<+List<+List<Nat>>>},
    c1: Array<+List<+List<Nat>>>,
    +ec1: {c1 == b1 : Array<+List<+List<Nat>>>},
    -c2: Array<+List<+List<Nat>>>,
    +ec2: {c2 == c1 : Array<+List<+List<Nat>>>},
    dp4: &d1: Array<+List<+List<Nat>>> -> &d2: Array<+List<+List<Nat>>> ->
         {d1 == c2 : Array<+List<+List<Nat>>>}
         & {d2 == d1 : Array<+List<+List<Nat>>>},
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +heql: {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hb2: FH.BktTree(10n, 0, bkts2,
            List.append(&2, SolveFast.FGroup, pre,
              SolveFast.FGroup{f, len, rws} <> Nil{})),
    +eib2: {SolveFast.ItemsBound{lb2, items2}
            == SolveFast.fgroup_items_build(True{}, rem_lb, rest, items)
            : SolveFast.ItemsBound}) ->
  FH.DrainSpec(pre, SolveFast.FGroup{f, len, rws} <> rest, rem_lb, items,
    SolveFast.drain5_swap(FF5.FF5.encode_fb5_list(f), lb2, items2,
      Array.swap(+List<+List<Nat>>, bkts2, FF5.FF5.encode_fb5_list(f), Nil{}))):
  (d1, dp5) = dp4
  (d2, pe4) = dp5
  (+ed1, +ed2) = pe4
  FH.drain5_one_dup4(pre, f, len, rws, rest, rem_lb, items, bkts2, lb2, items2,
    a1, ea1, b1, eb1, c1, ec1,
    d1, Equal.trans(Array<+List<+List<Nat>>>, d1, c2, c1, ed1, ec2),
    d2, ed2, hf5, heql, hnh, hb2, eib2)

def FH.drain5_one_dup2(+pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +rem_lb: Nat, +items: +List<SolveFast.Item>,
    -bkts2: Array<+List<+List<Nat>>>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    a1: Array<+List<+List<Nat>>>,
    +ea1: {a1 == bkts2 : Array<+List<+List<Nat>>>},
    b1: Array<+List<+List<Nat>>>,
    +eb1: {b1 == a1 : Array<+List<+List<Nat>>>},
    -b2: Array<+List<+List<Nat>>>,
    +eb2: {b2 == b1 : Array<+List<+List<Nat>>>},
    dp3: &c1: Array<+List<+List<Nat>>> -> &c2: Array<+List<+List<Nat>>> ->
         {c1 == b2 : Array<+List<+List<Nat>>>}
         & {c2 == c1 : Array<+List<+List<Nat>>>},
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +heql: {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hb2: FH.BktTree(10n, 0, bkts2,
            List.append(&2, SolveFast.FGroup, pre,
              SolveFast.FGroup{f, len, rws} <> Nil{})),
    +eib2: {SolveFast.ItemsBound{lb2, items2}
            == SolveFast.fgroup_items_build(True{}, rem_lb, rest, items)
            : SolveFast.ItemsBound}) ->
  FH.DrainSpec(pre, SolveFast.FGroup{f, len, rws} <> rest, rem_lb, items,
    SolveFast.drain5_swap(FF5.FF5.encode_fb5_list(f), lb2, items2,
      Array.swap(+List<+List<Nat>>, bkts2, FF5.FF5.encode_fb5_list(f), Nil{}))):
  (c1, dp4) = dp3
  (c2, pe3) = dp4
  (+ec1, +ec2) = pe3
  FH.drain5_one_dup3(pre, f, len, rws, rest, rem_lb, items, bkts2, lb2, items2,
    a1, ea1, b1, eb1,
    c1, Equal.trans(Array<+List<+List<Nat>>>, c1, b2, b1, ec1, eb2),
    c2, ec2, Arr.Arr.dup(+List<+List<Nat>>, c2),
    hf5, heql, hnh, hb2, eib2)

def FH.drain5_one_dup1(+pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +rem_lb: Nat, +items: +List<SolveFast.Item>,
    -bkts2: Array<+List<+List<Nat>>>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    a1: Array<+List<+List<Nat>>>,
    +ea1: {a1 == bkts2 : Array<+List<+List<Nat>>>},
    -a2: Array<+List<+List<Nat>>>,
    +ea2: {a2 == a1 : Array<+List<+List<Nat>>>},
    dp2: &b1: Array<+List<+List<Nat>>> -> &b2: Array<+List<+List<Nat>>> ->
         {b1 == a2 : Array<+List<+List<Nat>>>}
         & {b2 == b1 : Array<+List<+List<Nat>>>},
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +heql: {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hb2: FH.BktTree(10n, 0, bkts2,
            List.append(&2, SolveFast.FGroup, pre,
              SolveFast.FGroup{f, len, rws} <> Nil{})),
    +eib2: {SolveFast.ItemsBound{lb2, items2}
            == SolveFast.fgroup_items_build(True{}, rem_lb, rest, items)
            : SolveFast.ItemsBound}) ->
  FH.DrainSpec(pre, SolveFast.FGroup{f, len, rws} <> rest, rem_lb, items,
    SolveFast.drain5_swap(FF5.FF5.encode_fb5_list(f), lb2, items2,
      Array.swap(+List<+List<Nat>>, bkts2, FF5.FF5.encode_fb5_list(f), Nil{}))):
  (b1, dp3) = dp2
  (b2, pe2) = dp3
  (+eb1, +eb2) = pe2
  FH.drain5_one_dup2(pre, f, len, rws, rest, rem_lb, items, bkts2, lb2, items2,
    a1, ea1,
    b1, Equal.trans(Array<+List<+List<Nat>>>, b1, a2, a1, eb1, ea2),
    b2, eb2, Arr.Arr.dup(+List<+List<Nat>>, b2),
    hf5, heql, hnh, hb2, eib2)

def FH.drain5_one_dup0(+pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +rem_lb: Nat, +items: +List<SolveFast.Item>,
    -bkts2: Array<+List<+List<Nat>>>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    dp1: &a1: Array<+List<+List<Nat>>> -> &a2: Array<+List<+List<Nat>>> ->
         {a1 == bkts2 : Array<+List<+List<Nat>>>}
         & {a2 == a1 : Array<+List<+List<Nat>>>},
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +heql: {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hb2: FH.BktTree(10n, 0, bkts2,
            List.append(&2, SolveFast.FGroup, pre,
              SolveFast.FGroup{f, len, rws} <> Nil{})),
    +eib2: {SolveFast.ItemsBound{lb2, items2}
            == SolveFast.fgroup_items_build(True{}, rem_lb, rest, items)
            : SolveFast.ItemsBound}) ->
  FH.DrainSpec(pre, SolveFast.FGroup{f, len, rws} <> rest, rem_lb, items,
    SolveFast.drain5_swap(FF5.FF5.encode_fb5_list(f), lb2, items2,
      Array.swap(+List<+List<Nat>>, bkts2, FF5.FF5.encode_fb5_list(f), Nil{}))):
  (a1, dp2) = dp1
  (a2, pe1) = dp2
  (+ea1, +ea2) = pe1
  FH.drain5_one_dup1(pre, f, len, rws, rest, rem_lb, items, bkts2, lb2, items2,
    a1, ea1, a2, ea2, Arr.Arr.dup(+List<+List<Nat>>, a2),
    hf5, heql, hnh, hb2, eib2)

def FH.drain5_one_dup(+pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +rem_lb: Nat, +items: +List<SolveFast.Item>,
    bkts2: Array<+List<+List<Nat>>>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +heql: {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hb2: FH.BktTree(10n, 0, bkts2,
            List.append(&2, SolveFast.FGroup, pre,
              SolveFast.FGroup{f, len, rws} <> Nil{})),
    +eib2: {SolveFast.ItemsBound{lb2, items2}
            == SolveFast.fgroup_items_build(True{}, rem_lb, rest, items)
            : SolveFast.ItemsBound}) ->
  FH.DrainSpec(pre, SolveFast.FGroup{f, len, rws} <> rest, rem_lb, items,
    SolveFast.drain5_swap(FF5.FF5.encode_fb5_list(f), lb2, items2,
      Array.swap(+List<+List<Nat>>, bkts2, FF5.FF5.encode_fb5_list(f), Nil{}))):
  FH.drain5_one_dup0(pre, f, len, rws, rest, rem_lb, items, bkts2, lb2, items2,
    Arr.Arr.dup(+List<+List<Nat>>, bkts2), hf5, heql, hnh, hb2, eib2)

def FH.drain5_cons_step(+pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +rem_lb: Nat, +items: +List<SolveFast.Item>,
    dr1: SolveFast.Drain5State,
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +heql: {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hdr1: FH.DrainSpec(
             List.append(&2, SolveFast.FGroup, pre,
               SolveFast.FGroup{f, len, rws} <> Nil{}),
             rest, rem_lb, items, dr1)) ->
  FH.DrainSpec(pre, SolveFast.FGroup{f, len, rws} <> rest, rem_lb, items,
    SolveFast.drain5_go(FF5.FF5.encode_fb5_list(f) <> Nil{}, dr1)):
  match dr1:
    case SolveFast.Drain5State{bkts2, +lb2, +items2}:
      +gp : SolveFast.FGroup = SolveFast.FGroup{f, len, rws}
      +pre2 = List.append(&2, SolveFast.FGroup, pre, gp <> Nil{})
      +hb2 = Arr.Arr.dpair_l(
               FH.BktTree(10n, 0, bkts2, pre2),
               {SolveFast.ItemsBound{lb2, items2}
                == SolveFast.fgroup_items_build(True{}, rem_lb, rest, items)
                : SolveFast.ItemsBound}, hdr1)
      +eib2 = Arr.Arr.dpair_r(
                FH.BktTree(10n, 0, bkts2, pre2),
                {SolveFast.ItemsBound{lb2, items2}
                 == SolveFast.fgroup_items_build(True{}, rem_lb, rest, items)
                 : SolveFast.ItemsBound}, hdr1)
      FH.drain5_one_dup(pre, f, len, rws, rest, rem_lb, items, bkts2, lb2,
        items2, hf5, heql, hnh, hb2, eib2)

def FH.drain5_go_cons_dup2(+pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +rem_lb: Nat, +items: +List<SolveFast.Item>,
    -bkts: Array<+List<+List<Nat>>>,
    b1: Array<+List<+List<Nat>>>,
    +eb1: {b1 == bkts : Array<+List<+List<Nat>>>},
    -b2: Array<+List<+List<Nat>>>,
    +eb2: {b2 == b1 : Array<+List<+List<Nat>>>},
    dp2: &b3: Array<+List<+List<Nat>>> -> &b4: Array<+List<+List<Nat>>> ->
         {b3 == b2 : Array<+List<+List<Nat>>>}
         & {b4 == b3 : Array<+List<+List<Nat>>>},
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +heql: {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hb: FH.BktTree(10n, 0, bkts,
           List.append(&2, SolveFast.FGroup,
             List.append(&2, SolveFast.FGroup, pre,
               SolveFast.FGroup{f, len, rws} <> Nil{}),
             rest)),
    ih: @b2: Array<+List<+List<Nat>>> ->
        FH.BktTree(10n, 0, b2,
          List.append(&2, SolveFast.FGroup,
            List.append(&2, SolveFast.FGroup, pre,
              SolveFast.FGroup{f, len, rws} <> Nil{}),
            rest)) ->
        FH.DrainSpec(
          List.append(&2, SolveFast.FGroup, pre,
            SolveFast.FGroup{f, len, rws} <> Nil{}),
          rest, rem_lb, items,
          SolveFast.drain5_go(FH.rev_codes(rest, Nil{}),
            SolveFast.Drain5State{b2, rem_lb, items}))) ->
  FH.DrainSpec(pre, SolveFast.FGroup{f, len, rws} <> rest, rem_lb, items,
    SolveFast.drain5_go(
      FH.rev_codes(SolveFast.FGroup{f, len, rws} <> rest, Nil{}),
      SolveFast.Drain5State{bkts, rem_lb, items})):
  (b3, dp3) = dp2
  (b4, pe2) = dp3
  (+eb3, +eb4) = pe2
  +c = FF5.FF5.encode_fb5_list(f)
  +gp : SolveFast.FGroup = SolveFast.FGroup{f, len, rws}
  +pre2 = List.append(&2, SolveFast.FGroup, pre, gp <> Nil{})
  +eb3_b1 : {b3 == b1 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, b3, b2, b1, eb3, eb2)
  +eb4_b1 : {b4 == b1 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, b4, b3, b1, eb4, eb3_b1)
  +eb4_bk : {b4 == bkts : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, b4, b1, bkts, eb4_b1, eb1)
  +hb4 = FH.bkt_tree_transport(10n, 0, bkts, b4,
           List.append(&2, SolveFast.FGroup, pre2, rest),
           Equal.sym(Array<+List<+List<Nat>>>, b4, bkts, eb4_bk), hb)
  +hdr4 = ih(b4, hb4)
  +hdr1 = FH.drain_spec_transport(pre2, rest, rem_lb, items,
            SolveFast.drain5_go(FH.rev_codes(rest, Nil{}),
              SolveFast.Drain5State{b4, rem_lb, items}),
            SolveFast.drain5_go(FH.rev_codes(rest, Nil{}),
              SolveFast.Drain5State{b1, rem_lb, items}),
            Equal.cong(Array<+List<+List<Nat>>>, SolveFast.Drain5State,
              x => SolveFast.drain5_go(FH.rev_codes(rest, Nil{}),
                     SolveFast.Drain5State{x, rem_lb, items}),
              b4, b1, eb4_b1),
            hdr4)
  +eapp : {SolveFast.drain5_go(
             List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
             SolveFast.Drain5State{b3, rem_lb, items})
           == SolveFast.drain5_go(c <> Nil{},
                SolveFast.drain5_go(FH.rev_codes(rest, Nil{}),
                  SolveFast.Drain5State{b3, rem_lb, items}))
           : SolveFast.Drain5State} =
    FH.drain5_go_append(FH.rev_codes(rest, Nil{}), c <> Nil{},
      SolveFast.Drain5State{b3, rem_lb, items})
  +eapp_b1 : {SolveFast.drain5_go(
                List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
                SolveFast.Drain5State{b1, rem_lb, items})
              == SolveFast.drain5_go(c <> Nil{},
                   SolveFast.drain5_go(FH.rev_codes(rest, Nil{}),
                     SolveFast.Drain5State{b1, rem_lb, items}))
              : SolveFast.Drain5State} =
    Equal.trans(SolveFast.Drain5State,
      SolveFast.drain5_go(
        List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
        SolveFast.Drain5State{b1, rem_lb, items}),
      SolveFast.drain5_go(c <> Nil{},
        SolveFast.drain5_go(FH.rev_codes(rest, Nil{}),
          SolveFast.Drain5State{b3, rem_lb, items})),
      SolveFast.drain5_go(c <> Nil{},
        SolveFast.drain5_go(FH.rev_codes(rest, Nil{}),
          SolveFast.Drain5State{b1, rem_lb, items})),
      Equal.trans(SolveFast.Drain5State,
        SolveFast.drain5_go(
          List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
          SolveFast.Drain5State{b1, rem_lb, items}),
        SolveFast.drain5_go(
          List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
          SolveFast.Drain5State{b3, rem_lb, items}),
        SolveFast.drain5_go(c <> Nil{},
          SolveFast.drain5_go(FH.rev_codes(rest, Nil{}),
            SolveFast.Drain5State{b3, rem_lb, items})),
        Equal.cong(Array<+List<+List<Nat>>>, SolveFast.Drain5State,
          x => SolveFast.drain5_go(
                 List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
                 SolveFast.Drain5State{x, rem_lb, items}),
          b1, b3, Equal.sym(Array<+List<+List<Nat>>>, b3, b1, eb3_b1)),
        eapp),
      Equal.cong(Array<+List<+List<Nat>>>, SolveFast.Drain5State,
        x => SolveFast.drain5_go(c <> Nil{},
               SolveFast.drain5_go(FH.rev_codes(rest, Nil{}),
                 SolveFast.Drain5State{x, rem_lb, items})),
        b3, b1, eb3_b1))
  %eb1 : FH.DrainSpec(pre, gp <> rest, rem_lb, items,
           SolveFast.drain5_go(FH.rev_codes(rest, c <> Nil{}),
             SolveFast.Drain5State{_, rem_lb, items}))
  %Equal.sym(+List<U32>,
     FH.rev_codes(rest, c <> Nil{}),
     List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
     FH.rev_codes_append(rest, c <> Nil{})) :
    FH.DrainSpec(pre, gp <> rest, rem_lb, items,
      SolveFast.drain5_go(_, SolveFast.Drain5State{b1, rem_lb, items}))
  %Equal.sym(SolveFast.Drain5State,
     SolveFast.drain5_go(
       List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
       SolveFast.Drain5State{b1, rem_lb, items}),
     SolveFast.drain5_go(c <> Nil{},
       SolveFast.drain5_go(FH.rev_codes(rest, Nil{}),
         SolveFast.Drain5State{b1, rem_lb, items})),
     eapp_b1) :
    FH.DrainSpec(pre, gp <> rest, rem_lb, items, _)
  FH.drain5_cons_step(pre, f, len, rws, rest, rem_lb, items,
    SolveFast.drain5_go(FH.rev_codes(rest, Nil{}),
      SolveFast.Drain5State{b1, rem_lb, items}),
    hf5, heql, hnh, hdr1)

def FH.drain5_go_cons_dup(+pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +rem_lb: Nat, +items: +List<SolveFast.Item>,
    -bkts: Array<+List<+List<Nat>>>,
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +heql: {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hb: FH.BktTree(10n, 0, bkts,
           List.append(&2, SolveFast.FGroup,
             List.append(&2, SolveFast.FGroup, pre,
               SolveFast.FGroup{f, len, rws} <> Nil{}),
             rest)),
    dp: &b1: Array<+List<+List<Nat>>> -> &b2: Array<+List<+List<Nat>>> ->
        {b1 == bkts : Array<+List<+List<Nat>>>}
        & {b2 == b1 : Array<+List<+List<Nat>>>},
    ih: @b2: Array<+List<+List<Nat>>> ->
        FH.BktTree(10n, 0, b2,
          List.append(&2, SolveFast.FGroup,
            List.append(&2, SolveFast.FGroup, pre,
              SolveFast.FGroup{f, len, rws} <> Nil{}),
            rest)) ->
        FH.DrainSpec(
          List.append(&2, SolveFast.FGroup, pre,
            SolveFast.FGroup{f, len, rws} <> Nil{}),
          rest, rem_lb, items,
          SolveFast.drain5_go(FH.rev_codes(rest, Nil{}),
            SolveFast.Drain5State{b2, rem_lb, items}))) ->
  FH.DrainSpec(pre, SolveFast.FGroup{f, len, rws} <> rest, rem_lb, items,
    SolveFast.drain5_go(
      FH.rev_codes(SolveFast.FGroup{f, len, rws} <> rest, Nil{}),
      SolveFast.Drain5State{bkts, rem_lb, items})):
  (b1, dp2) = dp
  (b2, pe) = dp2
  (+eb1, +eb2) = pe
  FH.drain5_go_cons_dup2(pre, f, len, rws, rest, rem_lb, items, bkts,
    b1, eb1, b2, eb2, Arr.Arr.dup(+List<+List<Nat>>, b2),
    hf5, heql, hnh, hb, ih)

def FH.drain5_go_spec(+fg: +List<SolveFast.FGroup>,
    +pre: +List<SolveFast.FGroup>, bkts: Array<+List<+List<Nat>>>,
    +rem_lb: Nat, +items: +List<SolveFast.Item>,
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool},
    +hdisj: {FH.disjoint_codes(pre, fg) == True{} : Bool},
    +hb: FH.BktTree(10n, 0, bkts, List.append(&2, SolveFast.FGroup, pre, fg))) ->
  FH.DrainSpec(pre, fg, rem_lb, items,
    SolveFast.drain5_go(FH.rev_codes(fg, Nil{}),
      SolveFast.Drain5State{bkts, rem_lb, items})):
  match fg:
    case Nil{}:
      Arr.DPair{
        FH.bkt_tree_transport_fg(10n, 0, bkts,
          List.append(&2, SolveFast.FGroup, pre, Nil{}), pre,
          FH.list_append_nil(SolveFast.FGroup, pre), hb),
        {==}}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          +c = FF5.FF5.encode_fb5_list(f)
          +gp1 : SolveFast.FGroup = SolveFast.FGroup{f, len, rws}
          +pre2 = List.append(&2, SolveFast.FGroup, pre, gp1 <> Nil{})
          +hf5 = Logic.Proof.and_true_l(FF5.FF5.is_fb5(f),
                   Bool.and(Nat.is_le(1n, len),
                     Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                       Bool.and(Bool.not(FH.has_code(c, rest)),
                         FH.fgroups_wf(rest)))), hwf)
          +h1 = Logic.Proof.and_true_r(FF5.FF5.is_fb5(f),
                  Bool.and(Nat.is_le(1n, len),
                    Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                      Bool.and(Bool.not(FH.has_code(c, rest)),
                        FH.fgroups_wf(rest)))), hwf)
          +h2 = Logic.Proof.and_true_r(Nat.is_le(1n, len),
                  Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
                    Bool.and(Bool.not(FH.has_code(c, rest)),
                      FH.fgroups_wf(rest))), h1)
          +heql = Logic.Proof.and_true_l(Nat.is_eq(len, Groups.len_words(rws)),
                    Bool.and(Bool.not(FH.has_code(c, rest)),
                      FH.fgroups_wf(rest)), h2)
          +h3 = Logic.Proof.and_true_r(Nat.is_eq(len, Groups.len_words(rws)),
                  Bool.and(Bool.not(FH.has_code(c, rest)),
                    FH.fgroups_wf(rest)), h2)
          +hnot_r = FH.bool_false_of_not_true(FH.has_code(c, rest),
                      Logic.Proof.and_true_l(Bool.not(FH.has_code(c, rest)),
                        FH.fgroups_wf(rest), h3))
          +hr = Logic.Proof.and_true_r(Bool.not(FH.has_code(c, rest)),
                  FH.fgroups_wf(rest), h3)
          +hnh_pre = FH.bool_false_of_not_true(FH.has_code(c, pre),
                       Logic.Proof.and_true_l(Bool.not(FH.has_code(c, pre)),
                         FH.disjoint_codes(pre, rest), hdisj))
          +hd_rest = Logic.Proof.and_true_r(Bool.not(FH.has_code(c, pre)),
                       FH.disjoint_codes(pre, rest), hdisj)
          +hd_pre2 = FH.disjoint_codes_snoc(pre, f, len, rws, rest,
                       hd_rest, hnot_r)
          +eapp : {List.append(&2, SolveFast.FGroup, pre, gp1 <> rest)
                   == List.append(&2, SolveFast.FGroup, pre2, rest)
                   : +List<SolveFast.FGroup>} =
            Equal.sym(+List<SolveFast.FGroup>,
              List.append(&2, SolveFast.FGroup, pre2, rest),
              List.append(&2, SolveFast.FGroup, pre, gp1 <> rest),
              FH.list_append_assoc(SolveFast.FGroup, pre, gp1 <> Nil{}, rest))
          +hb_pre2 = FH.bkt_tree_transport_fg(10n, 0, bkts,
                       List.append(&2, SolveFast.FGroup, pre, gp1 <> rest),
                       List.append(&2, SolveFast.FGroup, pre2, rest),
                       eapp, hb)
          FH.drain5_go_cons_dup(pre, f, len, rws, rest, rem_lb, items, bkts,
            hf5, heql, hnh_pre, hb_pre2,
            Arr.Arr.dup(+List<+List<Nat>>, bkts),
            b2 => hb2 =>
              FH.drain5_go_spec(rest, pre2, b2, rem_lb, items, hr, hd_pre2, hb2))


# ---------------------------------------------------------------------------
# Top-level buffer invariant `FH.BufOk` and `FH.guess_items_buf_spec`
# ---------------------------------------------------------------------------

def FH.BufOk(buf: SolveFast.Buf5) -> Data:
  match buf:
    case SolveFast.NoBuf{}:
      Unit
    case SolveFast.Buf5{seen, buckets, gen}:
      Arr.Arr.DPair<
        FH.SeenTree(10n, 0, seen, gen, Nil{}),
        FH.BktTree(10n, 0, buckets, Nil{})>

def FH.buf_ok_transport(-b1: SolveFast.Buf5, -b2: SolveFast.Buf5,
    +eb: {b1 == b2 : SolveFast.Buf5}, +h: FH.BufOk(b1)) -> FH.BufOk(b2):
  %eb : FH.BufOk(_)
  h

def FH.mk_buf_go_ok(use: Bool) -> FH.BufOk(SolveFast.mk_buf_go(use)):
  match use:
    case True{}:
      Arr.DPair{FH.seen_tree_new(10n, 0), FH.bkt_tree_new(10n, 0)}
    case False{}:
      Unit{}

def FH.mk_buf_ok(+nodup: Bool, +n: Nat, +b0: SolveRef.Best) ->
  FH.BufOk(SolveFast.mk_buf(nodup, n, b0)):
  match nodup:
    case True{}:
      FH.mk_buf_go_ok(
        Bool.or(Nat.is_le(8n, n),
          Bool.and(Nat.is_le(2n, n),
            Bool.not(SolveFast.skippable(b0, Nat.add(n, n))))))
    case False{}:
      Unit{}

def FH.buf_dup_go(-seen: Array<Nat>, -bkts: Array<+List<+List<Nat>>>, +gen: Nat,
    ds: &s1: Array<Nat> -> &s2: Array<Nat> ->
        {s1 == seen : Array<Nat>} & {s2 == s1 : Array<Nat>},
    db: &k1: Array<+List<+List<Nat>>> -> &k2: Array<+List<+List<Nat>>> ->
        {k1 == bkts : Array<+List<+List<Nat>>>}
        & {k2 == k1 : Array<+List<+List<Nat>>>}) ->
  &b1: SolveFast.Buf5 -> &b2: SolveFast.Buf5 ->
  {b1 == SolveFast.Buf5{seen, bkts, gen} : SolveFast.Buf5}
  & {b2 == b1 : SolveFast.Buf5}:
  (s1, ds2) = ds
  (s2, ps) = ds2
  (+es1, +es2) = ps
  (k1, db2) = db
  (k2, pk) = db2
  (+ek1, +ek2) = pk
  +e1 : {SolveFast.Buf5{s1, k1, gen} == SolveFast.Buf5{seen, bkts, gen}
         : SolveFast.Buf5} =
    Equal.trans(SolveFast.Buf5,
      SolveFast.Buf5{s1, k1, gen},
      SolveFast.Buf5{seen, k1, gen},
      SolveFast.Buf5{seen, bkts, gen},
      Equal.cong(Array<Nat>, SolveFast.Buf5,
        s => SolveFast.Buf5{s, k1, gen}, s1, seen, es1),
      Equal.cong(Array<+List<+List<Nat>>>, SolveFast.Buf5,
        k => SolveFast.Buf5{seen, k, gen}, k1, bkts, ek1))
  +e2 : {SolveFast.Buf5{s2, k2, gen} == SolveFast.Buf5{s1, k1, gen}
         : SolveFast.Buf5} =
    Equal.trans(SolveFast.Buf5,
      SolveFast.Buf5{s2, k2, gen},
      SolveFast.Buf5{s1, k2, gen},
      SolveFast.Buf5{s1, k1, gen},
      Equal.cong(Array<Nat>, SolveFast.Buf5,
        s => SolveFast.Buf5{s, k2, gen}, s2, s1, es2),
      Equal.cong(Array<+List<+List<Nat>>>, SolveFast.Buf5,
        k => SolveFast.Buf5{s1, k, gen}, k2, k1, ek2))
  (SolveFast.Buf5{s1, k1, gen}, (SolveFast.Buf5{s2, k2, gen}, (e1, e2)))

def FH.buf_dup(buf: SolveFast.Buf5) ->
  &b1: SolveFast.Buf5 -> &b2: SolveFast.Buf5 ->
  {b1 == buf : SolveFast.Buf5} & {b2 == b1 : SolveFast.Buf5}:
  match buf:
    case SolveFast.NoBuf{}:
      (SolveFast.NoBuf{}, (SolveFast.NoBuf{}, ({==}, {==})))
    case SolveFast.Buf5{seen, bkts, +gen}:
      FH.buf_dup_go(seen, bkts, gen,
        Arr.Arr.dup(Nat, seen), Arr.Arr.dup(+List<+List<Nat>>, bkts))

def FH.GuessResSpec(+items_spec: +List<SolveFast.Item>,
    gr: SolveFast.GuessRes) -> Data:
  match gr:
    case SolveFast.GuessRes{items, buf}:
      Arr.Arr.DPair<{items == items_spec : +List<SolveFast.Item>}, FH.BufOk(buf)>

def FH.finish_drain5_spec(+g: +List<Nat>, +fg: +List<SolveFast.FGroup>, +n: Nat,
    -seen: Array<Nat>, +gen2: Nat, dr: SolveFast.Drain5State,
    +hs: FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +hdr: FH.DrainSpec(Nil{}, fg, n, SolveFast.End{} <> Nil{}, dr)) ->
  FH.GuessResSpec(
    SolveFast.schedule_guess_ib(g,
      SolveFast.fgroup_items_build(True{}, n, fg, SolveFast.End{} <> Nil{})),
    SolveFast.finish_drain5(g, seen, gen2, dr)):
  match dr:
    case SolveFast.Drain5State{bkts3, +rem_lb3, +items3}:
      +hb3 = Arr.Arr.dpair_l(
               FH.BktTree(10n, 0, bkts3, Nil{}),
               {SolveFast.ItemsBound{rem_lb3, items3}
                == SolveFast.fgroup_items_build(True{}, n, fg,
                     SolveFast.End{} <> Nil{}) : SolveFast.ItemsBound}, hdr)
      +eib = Arr.Arr.dpair_r(
               FH.BktTree(10n, 0, bkts3, Nil{}),
               {SolveFast.ItemsBound{rem_lb3, items3}
                == SolveFast.fgroup_items_build(True{}, n, fg,
                     SolveFast.End{} <> Nil{}) : SolveFast.ItemsBound}, hdr)
      Arr.DPair{
        Equal.cong(SolveFast.ItemsBound, +List<SolveFast.Item>,
          ib => SolveFast.schedule_guess_ib(g, ib),
          SolveFast.ItemsBound{rem_lb3, items3},
          SolveFast.fgroup_items_build(True{}, n, fg, SolveFast.End{} <> Nil{}),
          eib),
        Arr.DPair{hs, hb3}}

def FH.run_drain5_spec_dup(+g: +List<Nat>, +fg: +List<SolveFast.FGroup>, +n: Nat,
    -seen: Array<Nat>, +gen2: Nat,
    -bkts2: Array<+List<+List<Nat>>>, +touched: +List<U32>,
    +hs: FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +hb2: FH.BktTree(10n, 0, bkts2, fg),
    +etouched: {touched == FH.rev_codes(fg, Nil{}) : +List<U32>},
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool},
    dp: &b1: Array<+List<+List<Nat>>> -> &b2: Array<+List<+List<Nat>>> ->
        {b1 == bkts2 : Array<+List<+List<Nat>>>}
        & {b2 == b1 : Array<+List<+List<Nat>>>}) ->
  FH.GuessResSpec(
    SolveFast.schedule_guess_ib(g,
      SolveFast.fgroup_items_build(True{}, n, fg, SolveFast.End{} <> Nil{})),
    SolveFast.finish_drain5(g, seen, gen2,
      SolveFast.drain5_go(touched,
        SolveFast.Drain5State{bkts2, n, SolveFast.End{} <> Nil{}}))):
  (b1, dp2) = dp
  (b2, pe) = dp2
  (+eb1, +eb2) = pe
  +eb2_bk : {b2 == bkts2 : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, b2, b1, bkts2, eb2, eb1)
  +hb_b2 = FH.bkt_tree_transport(10n, 0, bkts2, b2, fg,
             Equal.sym(Array<+List<+List<Nat>>>, b2, bkts2, eb2_bk), hb2)
  +hdr2 = FH.drain5_go_spec(fg, Nil{}, b2, n, SolveFast.End{} <> Nil{},
            hwf, FH.disjoint_codes_nil(fg), hb_b2)
  +hdr1 = FH.drain_spec_transport(Nil{}, fg, n, SolveFast.End{} <> Nil{},
            SolveFast.drain5_go(FH.rev_codes(fg, Nil{}),
              SolveFast.Drain5State{b2, n, SolveFast.End{} <> Nil{}}),
            SolveFast.drain5_go(FH.rev_codes(fg, Nil{}),
              SolveFast.Drain5State{b1, n, SolveFast.End{} <> Nil{}}),
            Equal.cong(Array<+List<+List<Nat>>>, SolveFast.Drain5State,
              x => SolveFast.drain5_go(FH.rev_codes(fg, Nil{}),
                     SolveFast.Drain5State{x, n, SolveFast.End{} <> Nil{}}),
              b2, b1, eb2),
            hdr2)
  %eb1 : FH.GuessResSpec(
           SolveFast.schedule_guess_ib(g,
             SolveFast.fgroup_items_build(True{}, n, fg,
               SolveFast.End{} <> Nil{})),
           SolveFast.finish_drain5(g, seen, gen2,
             SolveFast.drain5_go(touched,
               SolveFast.Drain5State{_, n, SolveFast.End{} <> Nil{}})))
  %Equal.sym(+List<U32>, touched, FH.rev_codes(fg, Nil{}), etouched) :
    FH.GuessResSpec(
      SolveFast.schedule_guess_ib(g,
        SolveFast.fgroup_items_build(True{}, n, fg,
          SolveFast.End{} <> Nil{})),
      SolveFast.finish_drain5(g, seen, gen2,
        SolveFast.drain5_go(_,
          SolveFast.Drain5State{b1, n, SolveFast.End{} <> Nil{}})))
  FH.finish_drain5_spec(g, fg, n, seen, gen2,
    SolveFast.drain5_go(FH.rev_codes(fg, Nil{}),
      SolveFast.Drain5State{b1, n, SolveFast.End{} <> Nil{}}),
    hs, hdr1)

def FH.run_drain5_spec(+g: +List<Nat>, +fg: +List<SolveFast.FGroup>, +n: Nat,
    -seen: Array<Nat>, +gen2: Nat, fs: SolveFast.Fill5State,
    +hs: FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +hfs: FH.FillSpec(fg, Nil{}, fs)) ->
  FH.GuessResSpec(
    SolveFast.schedule_guess_ib(g,
      SolveFast.fgroup_items_build(True{}, n, fg, SolveFast.End{} <> Nil{})),
    SolveFast.run_drain5(g, n, seen, gen2, fs)):
  match fs:
    case SolveFast.Fill5State{bkts2, +touched}:
      +hb2 = Arr.Arr.dpair_l(
               FH.BktTree(10n, 0, bkts2, fg),
               Arr.Arr.DPair<
                 {touched == FH.rev_codes(fg, Nil{}) : +List<U32>},
                 {FH.fgroups_wf(fg) == True{} : Bool}>, hfs)
      +hr = Arr.Arr.dpair_r(
              FH.BktTree(10n, 0, bkts2, fg),
              Arr.Arr.DPair<
                {touched == FH.rev_codes(fg, Nil{}) : +List<U32>},
                {FH.fgroups_wf(fg) == True{} : Bool}>, hfs)
      +et = Arr.Arr.dpair_l(
              {touched == FH.rev_codes(fg, Nil{}) : +List<U32>},
              {FH.fgroups_wf(fg) == True{} : Bool}, hr)
      +hwf = Arr.Arr.dpair_r(
               {touched == FH.rev_codes(fg, Nil{}) : +List<U32>},
               {FH.fgroups_wf(fg) == True{} : Bool}, hr)
      FH.run_drain5_spec_dup(g, fg, n, seen, gen2, bkts2, touched, hs, hb2, et,
        hwf, Arr.Arr.dup(+List<+List<Nat>>, bkts2))

def FH.schedule5_lb_false_dup(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +S: +List<+List<Nat>>, +n: Nat, -seen: Array<Nat>,
    -bkts: Array<+List<+List<Nat>>>, +gen2: Nat,
    +hall5: {FH.all_len5(S) == True{} : Bool},
    +hs: FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +hb: FH.BktTree(10n, 0, bkts, Nil{}),
    dp: &b1: Array<+List<+List<Nat>>> -> &b2: Array<+List<+List<Nat>>> ->
        {b1 == bkts : Array<+List<+List<Nat>>>}
        & {b2 == b1 : Array<+List<+List<Nat>>>}) ->
  FH.GuessResSpec(
    SolveFast.schedule_guess_ib(
      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
      SolveFast.fgroup_items_build(True{}, n,
        SolveFast.fgroups_build_fast(
          g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), S, Nil{}),
        SolveFast.End{} <> Nil{})),
    SolveFast.run_drain5(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), n,
      seen, gen2,
      SolveFast.fill5_go(g0, g1, g2, g3, g4, S,
        SolveFast.Fill5State{bkts, Nil{}}))):
  (b1, dp2) = dp
  (b2, pe) = dp2
  (+eb1, +eb2) = pe
  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
  +fg = SolveFast.fgroups_build_fast(gw, S, Nil{})
  +eb2_bk : {b2 == bkts : Array<+List<+List<Nat>>>} =
    Equal.trans(Array<+List<+List<Nat>>>, b2, b1, bkts, eb2, eb1)
  +hb2 = FH.bkt_tree_transport(10n, 0, bkts, b2, Nil{},
           Equal.sym(Array<+List<+List<Nat>>>, b2, bkts, eb2_bk), hb)
  +hfs2 = FH.fill5_go_spec(g0, g1, g2, g3, g4, S, Nil{}, b2, Nil{}, Nil{},
            hall5, {==}, {==}, hb2)
  +hfs1 = FH.fill_spec_transport(fg, Nil{},
            SolveFast.fill5_go(g0, g1, g2, g3, g4, S,
              SolveFast.Fill5State{b2, Nil{}}),
            SolveFast.fill5_go(g0, g1, g2, g3, g4, S,
              SolveFast.Fill5State{b1, Nil{}}),
            Equal.cong(Array<+List<+List<Nat>>>, SolveFast.Fill5State,
              x => SolveFast.fill5_go(g0, g1, g2, g3, g4, S,
                     SolveFast.Fill5State{x, Nil{}}),
              b2, b1, eb2),
            hfs2)
  %eb1 : FH.GuessResSpec(
           SolveFast.schedule_guess_ib(gw,
             SolveFast.fgroup_items_build(True{}, n, fg,
               SolveFast.End{} <> Nil{})),
           SolveFast.run_drain5(gw, n, seen, gen2,
             SolveFast.fill5_go(g0, g1, g2, g3, g4, S,
               SolveFast.Fill5State{_, Nil{}})))
  FH.run_drain5_spec(gw, fg, n, seen, gen2,
    SolveFast.fill5_go(g0, g1, g2, g3, g4, S, SolveFast.Fill5State{b1, Nil{}}),
    hs, hfs1)

def FH.schedule5_lb_spec(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +S: +List<+List<Nat>>, +n: Nat, -seen: Array<Nat>,
    bkts: Array<+List<+List<Nat>>>, +gen2: Nat, skip: Bool,
    +hall5: {FH.all_len5(S) == True{} : Bool},
    +hs: FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +hb: FH.BktTree(10n, 0, bkts, Nil{})) ->
  FH.GuessResSpec(
    SolveFast.schedule_fguess_lb(True{},
      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
      SolveFast.fgroups_build_fast(
        g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), S, Nil{}),
      n, skip),
    SolveFast.schedule5_lb(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
      g0, g1, g2, g3, g4, S, n, seen, bkts, gen2, skip)):
  match skip:
    case True{}:
      Arr.DPair{{==}, Arr.DPair{hs, hb}}
    case False{}:
      FH.schedule5_lb_false_dup(g0, g1, g2, g3, g4, S, n, seen, bkts, gen2,
        hall5, hs, hb, Arr.Arr.dup(+List<+List<Nat>>, bkts))

def FH.schedule5_usable_spec(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +S: +List<+List<Nat>>, +n: Nat, +best: SolveRef.Best,
    -seen: Array<Nat>, bkts: Array<+List<+List<Nat>>>, +gen2: Nat,
    +m: Nat, +k: Nat, usable: Bool,
    +hall5: {FH.all_len5(S) == True{} : Bool},
    +hwf: {FH.fgroups_wf(
             SolveFast.fgroups_build_fast(
               g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), S, Nil{}))
           == True{} : Bool},
    +hm: {m == FH.fgroups_total(
                 SolveFast.fgroups_build_fast(
                   g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), S, Nil{}))
          : Nat},
    +hk: {k == FH.fgroups_count(
                 SolveFast.fgroups_build_fast(
                   g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), S, Nil{}))
          : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +hb: FH.BktTree(10n, 0, bkts, Nil{})) ->
  FH.GuessResSpec(
    SolveFast.schedule_fguess(True{},
      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
      SolveFast.fgroups_build_fast(
        g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), S, Nil{}),
      n, best, usable),
    SolveFast.schedule5_usable(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
      g0, g1, g2, g3, g4, S, n, best, seen, bkts, gen2, m, k, usable)):
  match usable:
    case False{}:
      Arr.DPair{{==}, Arr.DPair{hs, hb}}
    case True{}:
      +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
      +fg = SolveFast.fgroups_build_fast(gw, S, Nil{})
      +hpos = FH.fgroups_pos_of_wf(fg, hwf)
      +elb : {SolveFast.fgroups_lb_nodup(fg, n)
              == Nat.sub(Nat.add(n, Nat.add(m, m)), k) : Nat} =
        Equal.trans(Nat,
          SolveFast.fgroups_lb_nodup(fg, n),
          Nat.sub(
            Nat.add(n, Nat.add(FH.fgroups_total(fg), FH.fgroups_total(fg))),
            FH.fgroups_count(fg)),
          Nat.sub(Nat.add(n, Nat.add(m, m)), k),
          FH.fgroups_lb_nodup_formula(n, fg, hpos),
          Equal.trans(Nat,
            Nat.sub(
              Nat.add(n, Nat.add(FH.fgroups_total(fg), FH.fgroups_total(fg))),
              FH.fgroups_count(fg)),
            Nat.sub(Nat.add(n, Nat.add(m, m)), FH.fgroups_count(fg)),
            Nat.sub(Nat.add(n, Nat.add(m, m)), k),
            Equal.cong(Nat, Nat,
              x => Nat.sub(Nat.add(n, Nat.add(x, x)), FH.fgroups_count(fg)),
              FH.fgroups_total(fg), m, Equal.sym(Nat, m, FH.fgroups_total(fg), hm)),
            Equal.cong(Nat, Nat,
              y => Nat.sub(Nat.add(n, Nat.add(m, m)), y),
              FH.fgroups_count(fg), k, Equal.sym(Nat, k, FH.fgroups_count(fg), hk))))
      +lb = Nat.sub(Nat.add(n, Nat.add(m, m)), k)
      %Equal.sym(Nat, SolveFast.fgroups_lb_nodup(fg, n), lb, elb) :
        FH.GuessResSpec(
          SolveFast.schedule_fguess_lb(True{}, gw, fg, n,
            SolveFast.skippable(best, _)),
          SolveFast.schedule5_lb(gw, g0, g1, g2, g3, g4, S, n, seen, bkts,
            gen2, SolveFast.skippable(best, lb)))
      FH.schedule5_lb_spec(g0, g1, g2, g3, g4, S, n, seen, bkts, gen2,
        SolveFast.skippable(best, lb), hall5, hs, hb)

def FH.schedule5_hist_ok_dup(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +S: +List<+List<Nat>>, +n: Nat, +best: SolveRef.Best,
    -seen2: Array<Nat>, bkts: Array<+List<+List<Nat>>>, +gen: Nat,
    +m: Nat, +k: Nat,
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(S) : Nat},
    +hb: FH.BktTree(10n, 0, bkts, Nil{}),
    +hhr: FH.HistSpec(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), S, Nil{},
            gen, SolveFast.Hist5Ok{seen2, m, k}),
    dp: &s1: Array<Nat> -> &s2: Array<Nat> ->
        {s1 == seen2 : Array<Nat>} & {s2 == s1 : Array<Nat>}) ->
  FH.GuessResSpec(
    SolveFast.schedule_fguess(True{},
      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
      SolveFast.fgroups_build_fast(
        g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), S, Nil{}),
      n, best,
      SolveFast.fgroups_smaller(n,
        SolveFast.fgroups_build_fast(
          g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), S, Nil{}))),
    SolveFast.schedule5_usable(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
      g0, g1, g2, g3, g4, S, n, best, seen2, bkts, Nat.add(1n, gen), m, k,
      Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)))):
  (s1, dp2) = dp
  (s2, pe) = dp2
  (+es1, +es2) = pe
  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
  +fg = SolveFast.fgroups_build_fast(gw, S, Nil{})
  +hs2 = Arr.Arr.dpair_l(
           FH.SeenTree(10n, 0, seen2, gen, fg),
           Arr.Arr.DPair<{FH.all_len5(S) == True{} : Bool},
             Arr.Arr.DPair<{FH.fgroups_wf(fg) == True{} : Bool},
               Arr.Arr.DPair<{m == FH.fgroups_total(fg) : Nat},
                 Arr.Arr.DPair<{k == FH.fgroups_count(fg) : Nat},
                   {Nat.is_le(m, Nat.add(Groups.len_words(S), 0n))
                    == True{} : Bool}>>>>, hhr)
  +r1 = Arr.Arr.dpair_r(
          FH.SeenTree(10n, 0, seen2, gen, fg),
          Arr.Arr.DPair<{FH.all_len5(S) == True{} : Bool},
            Arr.Arr.DPair<{FH.fgroups_wf(fg) == True{} : Bool},
              Arr.Arr.DPair<{m == FH.fgroups_total(fg) : Nat},
                Arr.Arr.DPair<{k == FH.fgroups_count(fg) : Nat},
                  {Nat.is_le(m, Nat.add(Groups.len_words(S), 0n))
                   == True{} : Bool}>>>>, hhr)
  +hall5 = Arr.Arr.dpair_l({FH.all_len5(S) == True{} : Bool},
             Arr.Arr.DPair<{FH.fgroups_wf(fg) == True{} : Bool},
               Arr.Arr.DPair<{m == FH.fgroups_total(fg) : Nat},
                 Arr.Arr.DPair<{k == FH.fgroups_count(fg) : Nat},
                   {Nat.is_le(m, Nat.add(Groups.len_words(S), 0n))
                    == True{} : Bool}>>>, r1)
  +r2 = Arr.Arr.dpair_r({FH.all_len5(S) == True{} : Bool},
          Arr.Arr.DPair<{FH.fgroups_wf(fg) == True{} : Bool},
            Arr.Arr.DPair<{m == FH.fgroups_total(fg) : Nat},
              Arr.Arr.DPair<{k == FH.fgroups_count(fg) : Nat},
                {Nat.is_le(m, Nat.add(Groups.len_words(S), 0n))
                 == True{} : Bool}>>>, r1)
  +hwf = Arr.Arr.dpair_l({FH.fgroups_wf(fg) == True{} : Bool},
           Arr.Arr.DPair<{m == FH.fgroups_total(fg) : Nat},
             Arr.Arr.DPair<{k == FH.fgroups_count(fg) : Nat},
               {Nat.is_le(m, Nat.add(Groups.len_words(S), 0n))
                == True{} : Bool}>>, r2)
  +r3 = Arr.Arr.dpair_r({FH.fgroups_wf(fg) == True{} : Bool},
          Arr.Arr.DPair<{m == FH.fgroups_total(fg) : Nat},
            Arr.Arr.DPair<{k == FH.fgroups_count(fg) : Nat},
              {Nat.is_le(m, Nat.add(Groups.len_words(S), 0n))
               == True{} : Bool}>>, r2)
  +hm = Arr.Arr.dpair_l({m == FH.fgroups_total(fg) : Nat},
          Arr.Arr.DPair<{k == FH.fgroups_count(fg) : Nat},
            {Nat.is_le(m, Nat.add(Groups.len_words(S), 0n))
             == True{} : Bool}>, r3)
  +r4 = Arr.Arr.dpair_r({m == FH.fgroups_total(fg) : Nat},
          Arr.Arr.DPair<{k == FH.fgroups_count(fg) : Nat},
            {Nat.is_le(m, Nat.add(Groups.len_words(S), 0n))
             == True{} : Bool}>, r3)
  +hk = Arr.Arr.dpair_l({k == FH.fgroups_count(fg) : Nat},
          {Nat.is_le(m, Nat.add(Groups.len_words(S), 0n)) == True{} : Bool}, r4)
  +hle0 = Arr.Arr.dpair_r({k == FH.fgroups_count(fg) : Nat},
            {Nat.is_le(m, Nat.add(Groups.len_words(S), 0n)) == True{} : Bool}, r4)
  +es2_seen : {s2 == seen2 : Array<Nat>} =
    Equal.trans(Array<Nat>, s2, s1, seen2, es2, es1)
  +hs_s2 = FH.seen_tree_transport(10n, 0, seen2, s2, gen, fg,
             Equal.sym(Array<Nat>, s2, seen2, es2_seen), hs2)
  +hbump_s2 = FH.seen_tree_bump(10n, 0, s2, gen, fg, hs_s2)
  +hbump = FH.seen_tree_transport(10n, 0, s2, seen2, Nat.add(1n, gen), Nil{},
             es2_seen, hbump_s2)
  +hle_n : {Nat.is_le(FH.fgroups_total(fg), n) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(FH.fgroups_total(fg),
      Nat.add(Groups.len_words(S), 0n), n,
      Equal.trans(Nat, Nat.add(Groups.len_words(S), 0n), Groups.len_words(S), n,
        NatProof.NatPrf.add_zero(Groups.len_words(S)),
        Equal.sym(Nat, n, Groups.len_words(S), en)),
      NatProof.Nat.is_le_eq_l(Nat.add(Groups.len_words(S), 0n), m,
        FH.fgroups_total(fg), hm, hle0))
  +eus : {SolveFast.fgroups_smaller(n, fg)
          == Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)) : Bool} =
    Equal.trans(Bool,
      SolveFast.fgroups_smaller(n, fg),
      Bool.or(Nat.is_lt(FH.fgroups_total(fg), n),
        Nat.is_le(2n, FH.fgroups_count(fg))),
      Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)),
      FH.fgroups_smaller_formula(n, fg, FH.fgroups_pos_of_wf(fg, hwf),
        hge1, hle_n),
      Equal.trans(Bool,
        Bool.or(Nat.is_lt(FH.fgroups_total(fg), n),
          Nat.is_le(2n, FH.fgroups_count(fg))),
        Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, FH.fgroups_count(fg))),
        Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)),
        Equal.cong(Nat, Bool,
          x => Bool.or(Nat.is_lt(x, n), Nat.is_le(2n, FH.fgroups_count(fg))),
          FH.fgroups_total(fg), m, Equal.sym(Nat, m, FH.fgroups_total(fg), hm)),
        Equal.cong(Nat, Bool,
          y => Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, y)),
          FH.fgroups_count(fg), k, Equal.sym(Nat, k, FH.fgroups_count(fg), hk))))
  %Equal.sym(Bool, SolveFast.fgroups_smaller(n, fg),
     Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)), eus) :
    FH.GuessResSpec(SolveFast.schedule_fguess(True{}, gw, fg, n, best, _),
      SolveFast.schedule5_usable(gw, g0, g1, g2, g3, g4, S, n, best, seen2,
        bkts, Nat.add(1n, gen), m, k,
        Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k))))
  FH.schedule5_usable_spec(g0, g1, g2, g3, g4, S, n, best, seen2, bkts,
    Nat.add(1n, gen), m, k, Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)),
    hall5, hwf, hm, hk, hbump, hb)

def FH.schedule5_hist_spec(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +S: +List<+List<Nat>>, +n: Nat, +best: SolveRef.Best,
    bkts: Array<+List<+List<Nat>>>, +gen: Nat, hr: SolveFast.Hist5Res,
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(S) : Nat},
    +hb: FH.BktTree(10n, 0, bkts, Nil{}),
    +hhr: FH.HistSpec(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), S, Nil{},
            gen, hr)) ->
  FH.GuessResSpec(
    SolveFast.schedule_fguess(True{},
      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
      SolveFast.fgroups_build_fast(
        g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), S, Nil{}),
      n, best,
      SolveFast.fgroups_smaller(n,
        SolveFast.fgroups_build_fast(
          g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), S, Nil{}))),
    SolveFast.schedule5_hist(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
      g0, g1, g2, g3, g4, S, n, best, bkts, gen, hr)):
  match hr:
    case SolveFast.Hist5Fallback{seen2}:
      Arr.DPair{{==}, Arr.DPair{hhr, hb}}
    case SolveFast.Hist5Ok{seen2, +m, +k}:
      FH.schedule5_hist_ok_dup(g0, g1, g2, g3, g4, S, n, best, seen2, bkts,
        gen, m, k, hge1, en, hb, hhr, Arr.Arr.dup(Nat, seen2))

def FH.guess_body_buf5_len5_dup(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +S: +List<+List<Nat>>, +n: Nat, +best: SolveRef.Best,
    -seen: Array<Nat>, bkts: Array<+List<+List<Nat>>>, +gen: Nat,
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(S) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +hb: FH.BktTree(10n, 0, bkts, Nil{}),
    dp: &s1: Array<Nat> -> &s2: Array<Nat> ->
        {s1 == seen : Array<Nat>} & {s2 == s1 : Array<Nat>}) ->
  FH.GuessResSpec(
    SolveFast.schedule_fguess(True{},
      g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
      SolveFast.fgroups_build_fast(
        g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), S, Nil{}),
      n, best,
      SolveFast.fgroups_smaller(n,
        SolveFast.fgroups_build_fast(
          g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), S, Nil{}))),
    SolveFast.schedule5_hist(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
      g0, g1, g2, g3, g4, S, n, best, bkts, gen,
      SolveFast.hist5_go(g0, g1, g2, g3, g4, S, gen,
        SolveFast.Hist5Ok{seen, 0n, 0n}))):
  (s1, dp2) = dp
  (s2, pe) = dp2
  (+es1, +es2) = pe
  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
  +fg = SolveFast.fgroups_build_fast(gw, S, Nil{})
  +es2_s : {s2 == seen : Array<Nat>} =
    Equal.trans(Array<Nat>, s2, s1, seen, es2, es1)
  +hs2 = FH.seen_tree_transport(10n, 0, seen, s2, gen, Nil{},
           Equal.sym(Array<Nat>, s2, seen, es2_s), hs)
  +hhr2 = FH.hist5_go_spec(g0, g1, g2, g3, g4, S, Nil{}, s2, gen, 0n, 0n,
            {==}, {==}, {==}, hs2)
  +hhr1 = FH.hist_spec_transport(gw, S, Nil{}, gen,
            SolveFast.hist5_go(g0, g1, g2, g3, g4, S, gen,
              SolveFast.Hist5Ok{s2, 0n, 0n}),
            SolveFast.hist5_go(g0, g1, g2, g3, g4, S, gen,
              SolveFast.Hist5Ok{s1, 0n, 0n}),
            Equal.cong(Array<Nat>, SolveFast.Hist5Res,
              x => SolveFast.hist5_go(g0, g1, g2, g3, g4, S, gen,
                     SolveFast.Hist5Ok{x, 0n, 0n}),
              s2, s1, es2),
            hhr2)
  %es1 : FH.GuessResSpec(
           SolveFast.schedule_fguess(True{}, gw, fg, n, best,
             SolveFast.fgroups_smaller(n, fg)),
           SolveFast.schedule5_hist(gw, g0, g1, g2, g3, g4, S, n, best, bkts,
             gen,
             SolveFast.hist5_go(g0, g1, g2, g3, g4, S, gen,
               SolveFast.Hist5Ok{_, 0n, 0n})))
  FH.schedule5_hist_spec(g0, g1, g2, g3, g4, S, n, best, bkts, gen,
    SolveFast.hist5_go(g0, g1, g2, g3, g4, S, gen,
      SolveFast.Hist5Ok{s1, 0n, 0n}),
    hge1, en, hb, hhr1)

def FH.guess_body_buf5_spec(+g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
    +best: SolveRef.Best, seen: Array<Nat>, bkts: Array<+List<+List<Nat>>>,
    +gen: Nat,
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(S) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +hb: FH.BktTree(10n, 0, bkts, Nil{})) ->
  FH.GuessResSpec(
    SolveFast.schedule_fguess(True{}, g, SolveFast.fgroups_build_fast(g, S, Nil{}),
      n, best,
      SolveFast.fgroups_smaller(n, SolveFast.fgroups_build_fast(g, S, Nil{}))),
    SolveFast.guess_body_buf5(g, S, n, best, seen, bkts, gen)):
  match g:
    case Nil{}:
      Arr.DPair{{==}, Arr.DPair{hs, hb}}
    case Con{+g0, +t1}:
      match t1:
        case Nil{}:
          Arr.DPair{{==}, Arr.DPair{hs, hb}}
        case Con{+g1, +t2}:
          match t2:
            case Nil{}:
              Arr.DPair{{==}, Arr.DPair{hs, hb}}
            case Con{+g2, +t3}:
              match t3:
                case Nil{}:
                  Arr.DPair{{==}, Arr.DPair{hs, hb}}
                case Con{+g3, +t4}:
                  match t4:
                    case Nil{}:
                      Arr.DPair{{==}, Arr.DPair{hs, hb}}
                    case Con{+g4, +t5}:
                      match t5:
                        case Nil{}:
                          FH.guess_body_buf5_len5_dup(g0, g1, g2, g3, g4, S, n,
                            best, seen, bkts, gen, hge1, en, hs, hb,
                            Arr.Arr.dup(Nat, seen))
                        case Con{+g5, +t6}:
                          Arr.DPair{{==}, Arr.DPair{hs, hb}}

def FH.guess_body_buf_ge2_spec(+g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
    +best: SolveRef.Best, buf: SolveFast.Buf5,
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(S) : Nat},
    +hbuf: FH.BufOk(buf)) ->
  FH.GuessResSpec(
    SolveFast.schedule_fguess(True{}, g, SolveFast.fgroups_build_fast(g, S, Nil{}),
      n, best,
      SolveFast.fgroups_smaller(n, SolveFast.fgroups_build_fast(g, S, Nil{}))),
    SolveFast.guess_body_buf_ge2(g, S, n, best, buf)):
  match buf:
    case SolveFast.NoBuf{}:
      Arr.DPair{{==}, Unit{}}
    case SolveFast.Buf5{seen, bkts, +gen}:
      +hs = Arr.Arr.dpair_l(
              FH.SeenTree(10n, 0, seen, gen, Nil{}),
              FH.BktTree(10n, 0, bkts, Nil{}), hbuf)
      +hb = Arr.Arr.dpair_r(
              FH.SeenTree(10n, 0, seen, gen, Nil{}),
              FH.BktTree(10n, 0, bkts, Nil{}), hbuf)
      FH.guess_body_buf5_spec(g, S, n, best, seen, bkts, gen, hge1, en, hs, hb)

def FH.guess_body_buf_spec(+g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
    +best: SolveRef.Best, buf: SolveFast.Buf5,
    +en: {n == Groups.len_words(S) : Nat},
    +hbuf: FH.BufOk(buf)) ->
  FH.GuessResSpec(SolveFast.guess_body(True{}, g, S, n, best),
    SolveFast.guess_body_buf(g, S, n, best, buf)):
  match S:
    case Nil{}:
      Arr.DPair{{==}, hbuf}
    case Con{+w, +t}:
      match t:
        case Nil{}:
          Arr.DPair{{==}, hbuf}
        case Con{+w2, +t2}:
          +hge1 : {Nat.is_le(1n, n) == True{} : Bool} =
            Equal.cong(Nat, Bool, x => Nat.is_le(1n, x),
              n, Groups.len_words(w <> (w2 <> t2)), en)
          FH.guess_body_buf_ge2_spec(g, w <> (w2 <> t2), n, best, buf,
            hge1, en, hbuf)

def FH.guess_items_mem_buf_spec(+g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
    +best: SolveRef.Best, buf: SolveFast.Buf5, in_s: Bool,
    +en: {n == Groups.len_words(S) : Nat},
    +hbuf: FH.BufOk(buf)) ->
  FH.GuessResSpec(SolveFast.guess_items_mem(g, S, n, best, in_s),
    SolveFast.guess_items_mem_buf(g, S, n, best, buf, in_s)):
  match in_s:
    case True{}:
      FH.guess_body_buf_spec(g, S, n, best, buf, en, hbuf)
    case False{}:
      Arr.DPair{{==}, hbuf}

def FH.guess_items_nodup_buf_spec(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +n: Nat, +best: SolveRef.Best, buf: SolveFast.Buf5, le_2n: Bool,
    +en: {n == Groups.len_words(S) : Nat},
    +hbuf: FH.BufOk(buf)) ->
  FH.GuessResSpec(SolveFast.guess_items_nodup(g, S, n, best, le_2n),
    SolveFast.guess_items_nodup_buf(g, S, n, best, buf, le_2n)):
  match le_2n:
    case False{}:
      FH.guess_body_buf_spec(g, S, n, best, buf, en, hbuf)
    case True{}:
      FH.guess_items_mem_buf_spec(g, S, n, best, buf,
        SolveFast.member_word_fast(g, S), en, hbuf)

# Main theorem: `guess_items_buf` always emits the exact same schedule items
# as `guess_items` and preserves `FH.BufOk`.
def FH.guess_items_buf_spec(+nodup: Bool, +g: +List<Nat>,
    +S: +List<+List<Nat>>, +n: Nat, +best: SolveRef.Best, buf: SolveFast.Buf5,
    +en: {n == Groups.len_words(S) : Nat},
    +hbuf: FH.BufOk(buf)) ->
  FH.GuessResSpec(SolveFast.guess_items(nodup, g, S, n, best),
    SolveFast.guess_items_buf(nodup, g, S, n, best, buf)):
  match nodup:
    case True{}:
      FH.guess_items_nodup_buf_spec(g, S, n, best, buf,
        SolveFast.skippable(best, Nat.add(n, n)), en, hbuf)
    case False{}:
      Arr.DPair{{==}, hbuf}
