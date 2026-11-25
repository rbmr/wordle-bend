# Correctness of the table-backed 5-letter histogram, LCF bucketing, O(1)
# three-word solver, and threaded node buffer (`SolveFast.hist5_go`,
# `SolveFast.fill5_go`, `SolveFast.drain5_go`, `SolveFast.mk_buf_tbl`, and
# `SolveFast.guess_items_buf`).
#
# Proves for every input `(nodup, row, g, cwS, n, floor, best)` and valid
# threaded buffer `buf` (`FH.BufOk(G, C, n_root, has_buf, nodup, buf)`):
# 1. `FH.GuessSpec` classifies the emitted items as one of:
#    - `GCSkipSelf`: stage-2 candidate guess skipped (`floor == 2*n`, `g in S`),
#    - `GCSkipUnusable`: guess does not split `S` (`groups_smaller == False{}`),
#    - `GCSkipPre`: `best_cost(best) <= pre_lb(n, g, S)`,
#    - `GCSkipLb`: `best_cost(best) <= lower_bound(n, groups_build(g, S, Nil{}))`,
#    - `GCLive{ord, body, perm}`: `groups_smaller == True{}`, `ord` is a
#      permutation (`FP.PermOk`) of `groups_build(g, S, Nil{})`, and `body`
#      matches `ord` item-for-item (`FH.BodyMatch`), including `DoneItem`
#      three-word subtrees (`FT3.done_three_ok_b`) and valid `CWord`s.
# 2. The returned buffer preserves `FH.BufOk(G, C, n_root, has_buf, nodup, buf2)`.
import Base
import ../src/feedback.bend as Feedback
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/solve_ref.bend as SolveRef
import ../src/solve_fast.bend as SolveFast
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./eval.bend as Eval
import ./mainvalid.bend as MV
import ./cover_groups.bend as CoverGroups
import ./fast_groups.bend as FG
import ./fast_lb.bend as FLB
import ./fast_one.bend as FO
import ./fast_nodup.bend as FN
import ./array.bend as Arr
import ./fast_fb5.bend as FF5
import ./fast_perm.bend as FP
import ./fast_tbl.bend as FT
import ./fast_three.bend as FT3
import ./lb_capacity.bend as CapProof

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

# ---------------------------------------------------------------------------
# Collision-budget pruning helpers (`Hist5Pruned`)
# ---------------------------------------------------------------------------

def FH.is_le_add_r(+a: Nat, +b: Nat, +c: Nat,
    +h: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  NatProof.Nat.is_le_eq_l(Nat.add(b, c), Nat.add(c, a), Nat.add(a, c),
    NatProof.NatPrf.add_comm(c, a),
    NatProof.Nat.is_le_eq_r(Nat.add(c, a), Nat.add(c, b), Nat.add(b, c),
      NatProof.NatPrf.add_comm(c, b),
      NatProof.Nat.is_le_add_l(a, b, c, h)))

def FH.le_add_sub(+b: Nat, +a: Nat) ->
  {Nat.is_le(b, Nat.add(a, Nat.sub(b, a))) == True{} : Bool}:
  match b a:
    case 0n _:
      NatProof.Nat.is_le_zero_l(Nat.add(a, Nat.sub(0n, a)))
    case 1n++bp 0n:
      NatProof.Nat.is_le_refl(1n+bp)
    case 1n++bp 1n++ap:
      FH.le_add_sub(bp, ap)

def FH.le_sub_of_add_le(+z: Nat, +y: Nat, +x: Nat,
    +h: {Nat.is_le(Nat.add(x, z), y) == True{} : Bool}) ->
  {Nat.is_le(x, Nat.sub(y, z)) == True{} : Bool}:
  match z y:
    case 0n _:
      NatProof.Nat.is_le_eq_r(x, y, Nat.sub(y, 0n),
        Equal.sym(Nat, Nat.sub(y, 0n), y, FH.nat_sub_zero(y)),
        NatProof.Nat.is_le_eq_l(y, Nat.add(x, 0n), x,
          NatProof.NatPrf.add_zero(x), h))
    case 1n++zp 0n:
      +h1 : {Nat.is_le(Nat.add(1n, Nat.add(x, zp)), 0n) == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(0n, Nat.add(x, 1n+zp),
          Nat.add(1n, Nat.add(x, zp)), NatProof.NatPrf.add_succ(x, zp), h)
      Empty.absurd({Nat.is_le(x, 0n) == True{} : Bool},
        Logic.Proof.false_ne_true(h1))
    case 1n++zp 1n++yp:
      +h1 : {Nat.is_le(Nat.add(1n, Nat.add(x, zp)), 1n+yp) == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(1n+yp, Nat.add(x, 1n+zp),
          Nat.add(1n, Nat.add(x, zp)), NatProof.NatPrf.add_succ(x, zp), h)
      FH.le_sub_of_add_le(zp, yp, x, h1)

def FH.fgroup_add_total(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +fg: +List<SolveFast.FGroup>, hit: Bool) ->
  {FH.fgroups_total(SolveFast.fgroup_add_go(w, fb, fg, hit))
   == Nat.add(1n, FH.fgroups_total(fg)) : Nat}:
  match fg:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          match hit:
            case True{}:
              {==}
            case False{}:
              Equal.trans(Nat,
                Nat.add(len,
                  FH.fgroups_total(
                    SolveFast.fgroup_add_go(w, fb, rest,
                      SolveFast.next_fgroup_hit(fb, rest)))),
                Nat.add(len, Nat.add(1n, FH.fgroups_total(rest))),
                Nat.add(1n, Nat.add(len, FH.fgroups_total(rest))),
                Equal.cong(Nat, Nat, x => Nat.add(len, x),
                  FH.fgroups_total(
                    SolveFast.fgroup_add_go(w, fb, rest,
                      SolveFast.next_fgroup_hit(fb, rest))),
                  Nat.add(1n, FH.fgroups_total(rest)),
                  FH.fgroup_add_total(w, fb, rest,
                    SolveFast.next_fgroup_hit(fb, rest))),
                NatProof.NatPrf.add_succ(len, FH.fgroups_total(rest)))

def FH.fgroup_add_count_le(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +fg: +List<SolveFast.FGroup>, hit: Bool) ->
  {Nat.is_le(FH.fgroups_count(SolveFast.fgroup_add_go(w, fb, fg, hit)),
             Nat.add(1n, FH.fgroups_count(fg))) == True{} : Bool}:
  match fg:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          match hit:
            case True{}:
              NatProof.Nat.is_le_of_lt(FH.fgroups_count(rest),
                Nat.add(1n, FH.fgroups_count(rest)),
                NatProof.Nat.is_lt_succ_self(FH.fgroups_count(rest)))
            case False{}:
              FH.fgroup_add_count_le(w, fb, rest,
                SolveFast.next_fgroup_hit(fb, rest))

def FH.fgroup_add_pos(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +fg: +List<SolveFast.FGroup>, hit: Bool,
    +hp: {FH.fgroups_pos(fg) == True{} : Bool}) ->
  {FH.fgroups_pos(SolveFast.fgroup_add_go(w, fb, fg, hit)) == True{} : Bool}:
  match fg:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          match hit:
            case True{}:
              +hr = Logic.Proof.and_true_r(Nat.is_le(1n, len),
                      FH.fgroups_pos(rest), hp)
              FH.bool_and_intro(Nat.is_le(1n, Nat.add(1n, len)),
                FH.fgroups_pos(rest), NatProof.Nat.is_le_zero_l(len), hr)
            case False{}:
              +hl = Logic.Proof.and_true_l(Nat.is_le(1n, len),
                      FH.fgroups_pos(rest), hp)
              +hr = Logic.Proof.and_true_r(Nat.is_le(1n, len),
                      FH.fgroups_pos(rest), hp)
              FH.bool_and_intro(Nat.is_le(1n, len),
                FH.fgroups_pos(SolveFast.fgroup_add_go(w, fb, rest,
                  SolveFast.next_fgroup_hit(fb, rest))),
                hl,
                FH.fgroup_add_pos(w, fb, rest,
                  SolveFast.next_fgroup_hit(fb, rest), hr))

def FH.fgroups_next_pos(+g: +List<Nat>, +w: +List<Nat>,
    +acc: +List<SolveFast.FGroup>, same: Bool,
    +hp: {FH.fgroups_pos(acc) == True{} : Bool}) ->
  {FH.fgroups_pos(SolveFast.fgroups_next_acc(g, w, acc, same))
   == True{} : Bool}:
  match same:
    case True{}:
      hp
    case False{}:
      FH.fgroup_add_pos(w, SolveFast.feedback_fast(g, w), acc,
        SolveFast.next_fgroup_hit(SolveFast.feedback_fast(g, w), acc), hp)

def FH.fgroups_build_pos(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +acc: +List<SolveFast.FGroup>,
    +hp: {FH.fgroups_pos(acc) == True{} : Bool}) ->
  {FH.fgroups_pos(SolveFast.fgroups_build_fast(g, S, acc)) == True{} : Bool}:
  match S:
    case Nil{}:
      hp
    case Con{+w, +rest}:
      FH.fgroups_build_pos(g, rest,
        SolveFast.fgroups_next_acc(g, w, acc, SolveFast.word_eq_fast(g, w)),
        FH.fgroups_next_pos(g, w, acc, SolveFast.word_eq_fast(g, w), hp))

def FH.fgroups_build_total_step(+g: +List<Nat>, +w: +List<Nat>,
    +rest: +List<+List<Nat>>, +acc: +List<SolveFast.FGroup>, same: Bool,
    +ih: {FH.fgroups_total(
            SolveFast.fgroups_build_fast(g, rest,
              SolveFast.fgroups_next_acc(g, w, acc, same)))
          == Nat.add(SolveFast.keep_fast(g, rest),
               FH.fgroups_total(SolveFast.fgroups_next_acc(g, w, acc, same)))
          : Nat}) ->
  {FH.fgroups_total(
     SolveFast.fgroups_build_fast(g, rest,
       SolveFast.fgroups_next_acc(g, w, acc, same)))
   == Nat.add(SolveFast.keep_step(SolveFast.keep_fast(g, rest), same),
        FH.fgroups_total(acc)) : Nat}:
  match same:
    case True{}:
      ih
    case False{}:
      +et : {FH.fgroups_total(
               SolveFast.fgroup_add_fast(w, SolveFast.feedback_fast(g, w), acc))
             == Nat.add(1n, FH.fgroups_total(acc)) : Nat} =
        FH.fgroup_add_total(w, SolveFast.feedback_fast(g, w), acc,
          SolveFast.next_fgroup_hit(SolveFast.feedback_fast(g, w), acc))
      Equal.trans(Nat,
        FH.fgroups_total(
          SolveFast.fgroups_build_fast(g, rest,
            SolveFast.fgroup_add_fast(w, SolveFast.feedback_fast(g, w), acc))),
        Nat.add(SolveFast.keep_fast(g, rest), Nat.add(1n, FH.fgroups_total(acc))),
        Nat.add(Nat.add(1n, SolveFast.keep_fast(g, rest)), FH.fgroups_total(acc)),
        Equal.trans(Nat,
          FH.fgroups_total(
            SolveFast.fgroups_build_fast(g, rest,
              SolveFast.fgroup_add_fast(w, SolveFast.feedback_fast(g, w), acc))),
          Nat.add(SolveFast.keep_fast(g, rest),
            FH.fgroups_total(
              SolveFast.fgroup_add_fast(w, SolveFast.feedback_fast(g, w), acc))),
          Nat.add(SolveFast.keep_fast(g, rest),
            Nat.add(1n, FH.fgroups_total(acc))),
          ih,
          Equal.cong(Nat, Nat, x => Nat.add(SolveFast.keep_fast(g, rest), x),
            FH.fgroups_total(
              SolveFast.fgroup_add_fast(w, SolveFast.feedback_fast(g, w), acc)),
            Nat.add(1n, FH.fgroups_total(acc)), et)),
        NatProof.NatPrf.add_succ(SolveFast.keep_fast(g, rest),
          FH.fgroups_total(acc)))

def FH.fgroups_build_total_eq_keep(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +acc: +List<SolveFast.FGroup>) ->
  {FH.fgroups_total(SolveFast.fgroups_build_fast(g, S, acc))
   == Nat.add(SolveFast.keep_fast(g, S), FH.fgroups_total(acc)) : Nat}:
  match S:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      FH.fgroups_build_total_step(g, w, rest, acc, SolveFast.word_eq_fast(g, w),
        FH.fgroups_build_total_eq_keep(g, rest,
          SolveFast.fgroups_next_acc(g, w, acc, SolveFast.word_eq_fast(g, w))))

def FH.pruned_step_mono(+g: +List<Nat>, +w: +List<Nat>,
    +fg: +List<SolveFast.FGroup>, +budget0: Nat, same: Bool,
    +h: {Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg))),
                   FH.fgroups_total(fg)) == True{} : Bool}) ->
  {Nat.is_le(
     Nat.add(1n, Nat.add(budget0,
       FH.fgroups_count(SolveFast.fgroups_next_acc(g, w, fg, same)))),
     FH.fgroups_total(SolveFast.fgroups_next_acc(g, w, fg, same)))
   == True{} : Bool}:
  match same:
    case True{}:
      h
    case False{}:
      +fg1 = SolveFast.fgroup_add_fast(w, SolveFast.feedback_fast(g, w), fg)
      +et : {FH.fgroups_total(fg1) == Nat.add(1n, FH.fgroups_total(fg)) : Nat} =
        FH.fgroup_add_total(w, SolveFast.feedback_fast(g, w), fg,
          SolveFast.next_fgroup_hit(SolveFast.feedback_fast(g, w), fg))
      +hc : {Nat.is_le(FH.fgroups_count(fg1), Nat.add(1n, FH.fgroups_count(fg)))
             == True{} : Bool} =
        FH.fgroup_add_count_le(w, SolveFast.feedback_fast(g, w), fg,
          SolveFast.next_fgroup_hit(SolveFast.feedback_fast(g, w), fg))
      +h1 : {Nat.is_le(
               Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg1))),
               Nat.add(1n, Nat.add(budget0, Nat.add(1n, FH.fgroups_count(fg)))))
             == True{} : Bool} =
        NatProof.Nat.is_le_add_l(FH.fgroups_count(fg1),
          Nat.add(1n, FH.fgroups_count(fg)), budget0, hc)
      +e1 : {Nat.add(1n, Nat.add(budget0, Nat.add(1n, FH.fgroups_count(fg))))
             == Nat.add(1n, Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg))))
             : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(1n, x),
          Nat.add(budget0, Nat.add(1n, FH.fgroups_count(fg))),
          Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg))),
          NatProof.NatPrf.add_succ(budget0, FH.fgroups_count(fg)))
      +h2 : {Nat.is_le(
               Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg1))),
               Nat.add(1n, FH.fgroups_total(fg))) == True{} : Bool} =
        NatProof.Nat.is_le_trans(
          Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg1))),
          Nat.add(1n, Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg)))),
          Nat.add(1n, FH.fgroups_total(fg)),
          NatProof.Nat.is_le_eq_r(
            Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg1))),
            Nat.add(1n, Nat.add(budget0, Nat.add(1n, FH.fgroups_count(fg)))),
            Nat.add(1n, Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg)))),
            e1, h1),
          h)
      NatProof.Nat.is_le_eq_r(
        Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg1))),
        Nat.add(1n, FH.fgroups_total(fg)),
        FH.fgroups_total(fg1),
        Equal.sym(Nat, FH.fgroups_total(fg1), Nat.add(1n, FH.fgroups_total(fg)),
          et),
        h2)

def FH.pruned_build_mono(+g: +List<Nat>, +rest: +List<+List<Nat>>,
    +fg: +List<SolveFast.FGroup>, +budget0: Nat,
    +h: {Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg))),
                   FH.fgroups_total(fg)) == True{} : Bool}) ->
  {Nat.is_le(
     Nat.add(1n, Nat.add(budget0,
       FH.fgroups_count(SolveFast.fgroups_build_fast(g, rest, fg)))),
     FH.fgroups_total(SolveFast.fgroups_build_fast(g, rest, fg)))
   == True{} : Bool}:
  match rest:
    case Nil{}:
      h
    case Con{+w, +t}:
      FH.pruned_build_mono(g, t,
        SolveFast.fgroups_next_acc(g, w, fg, SolveFast.word_eq_fast(g, w)),
        budget0,
        FH.pruned_step_mono(g, w, fg, budget0, SolveFast.word_eq_fast(g, w), h))

def FH.seen_tree_bump_erased(-seen2: Array<Nat>, +gen: Nat,
    +fg: +List<SolveFast.FGroup>,
    +hs: FH.SeenTree(10n, 0, seen2, gen, fg),
    dp: &s1: Array<Nat> -> &s2: Array<Nat> ->
        {s1 == seen2 : Array<Nat>} & {s2 == s1 : Array<Nat>}) ->
  FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{}):
  (s1, dp2) = dp
  (s2, pe) = dp2
  (+es1, +es2) = pe
  +es2_s : {s2 == seen2 : Array<Nat>} =
    Equal.trans(Array<Nat>, s2, s1, seen2, es2, es1)
  +hs2 = FH.seen_tree_transport(10n, 0, seen2, s2, gen, fg,
           Equal.sym(Array<Nat>, s2, seen2, es2_s), hs)
  FH.seen_tree_transport(10n, 0, s2, seen2, Nat.add(1n, gen), Nil{}, es2_s,
    FH.seen_tree_bump(10n, 0, s2, gen, fg, hs2))
# ---------------------------------------------------------------------------
# Schedule body specification (`FH.BodyMatch`) and `CWord`/`RowWord` helpers
# ---------------------------------------------------------------------------

def FH.cwords_ok_if(has_buf: Bool, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n_root: Nat,
    +cs: +List<SolveFast.CWord>) -> Bool:
  match has_buf:
    case False{}:
      True{}
    case True{}:
      FT.FT.cwords_ok_b(G, C, n_root, cs)

def FH.rws_ok_if(has_buf: Bool, +G: +List<+List<Nat>>, +n_root: Nat,
    +rws: +List<FT.FT.RowWord>) -> Bool:
  match has_buf:
    case False{}:
      True{}
    case True{}:
      FT.FT.rws_ok_b(G, n_root, rws)

def FH.gentry_ok_if(has_buf: Bool, +G: +List<+List<Nat>>, +n_root: Nat,
    +row: U32, +g: +List<Nat>) -> Bool:
  match has_buf:
    case False{}:
      True{}
    case True{}:
      FT.FT.gentry_ok_b(G, n_root, row, g)

def FH.cwords_words_cons(cw: SolveFast.CWord,
    +rest: +List<SolveFast.CWord>) ->
  {SolveFast.cwords_words(cw <> rest)
   == SolveFast.cword_w(cw) <> SolveFast.cwords_words(rest)
   : +List<+List<Nat>>}:
  match cw:
    case SolveFast.CWord{ci, grow, w}:
      {==}

def FH.cwords_dummy_words(+ws: +List<+List<Nat>>) ->
  {SolveFast.cwords_words(SolveFast.dummy_cwords(ws)) == ws
   : +List<+List<Nat>>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>, l => w <> l,
        SolveFast.cwords_words(SolveFast.dummy_cwords(t)), t,
        FH.cwords_dummy_words(t))

def FH.body_lb(+nodup: Bool, +n: Nat, +body: +List<SolveFast.Item>) -> Nat:
  match body:
    case Nil{}:
      0n
    case Con{it, rest}:
      match it:
        case SolveFast.Begin{g}:
          0n
        case SolveFast.ClassItem{fb, cws, wlen, tlb}:
          Nat.add(
            SolveFast.class_lb_fast(nodup, wlen, SolveFast.cwords_words(cws)),
            FH.body_lb(nodup, n, rest))
        case SolveFast.OneItem{fb, w}:
          Nat.add(1n, FH.body_lb(nodup, n, rest))
        case SolveFast.TwoItem{fb, w1, w2}:
          Nat.add(3n, FH.body_lb(nodup, n, rest))
        case SolveFast.DoneItem{fb, tree, cost}:
          Nat.add(cost, FH.body_lb(nodup, n, rest))
        case SolveFast.Add{fb, tlb}:
          FH.body_lb(nodup, n, rest)
        case SolveFast.End{}:
          n

# The number of feedback groups of `g` on the class `ws`. It is the same count
# the class scan produces (`CK.count` in `proofs/class_k.bend`).
def FH.cap_count(+g: +List<Nat>, +ws: +List<+List<Nat>>) -> Nat:
  FH.fgroups_count(SolveFast.fgroups_build_fast(g, ws, Nil{}))

# The largest count over the first `i` guesses of the guess list.
def FH.prefmax(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>, +i: Nat) -> Nat:
  match i:
    case 0n:
      0n
    case 1n+p:
      Nat.max(FH.cap_count(FT.FT.nth_word(G, p), ws), FH.prefmax(G, ws, p))

# The capacity lower bound of one class: the depth bound, or the capacity bound
# at the class's branching factor over the whole guess list, whichever is
# larger.
def FH.cap_class(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>) -> Nat:
  Nat.max(SolveFast.class_lb_fast(True{}, Groups.len_words(ws), ws),
    CapProof.LB.capbound(Groups.len_words(ws),
      FH.prefmax(G, ws, Groups.len_words(G))))

# The class bounds of a class list, added up.
def FH.cap_fold(+G: +List<+List<Nat>>, +groups: +List<Groups.Group>) -> Nat:
  match groups:
    case Nil{}:
      0n
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          Nat.add(FH.cap_class(G, ws), FH.cap_fold(G, rest))

# The capacity lower bound of a guess: one per candidate plus one class bound
# per feedback class.
def FH.cap_lb(+G: +List<+List<Nat>>, +n: Nat,
              +groups: +List<Groups.Group>) -> Nat:
  Nat.add(n, FH.cap_fold(G, groups))

def FH.done_ws_ok_b(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +tree: Tree.Tree, +cost: Nat) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{w1, t1}:
      match t1:
        case Nil{}:
          False{}
        case Con{w2, t2}:
          match t2:
            case Nil{}:
              False{}
            case Con{w3, t3}:
              match t3:
                case Nil{}:
                  FT3.FT3.done_three_ok_b(G, w1, w2, w3, tree, cost)
                case Con{_, _}:
                  False{}

def FH.BodyMatch(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +nodup: Bool, +n: Nat, +groups: +List<Groups.Group>,
    +body: +List<SolveFast.Item>) -> Data:
  match groups:
    case Nil{}:
      {body == SolveFast.End{} <> Nil{} : +List<SolveFast.Item>}
    case Con{gp, restg}:
      match gp:
        case Groups.Group{+fb, +ws}:
          match body:
            case Nil{}:
              Empty
            case Con{it, restb}:
              match it:
                case SolveFast.Begin{g}:
                  Empty
                case SolveFast.OneItem{+f, +w}:
                  Arr.Arr.DPair<
                    {f == fb : +List<Feedback.Color>},
                    Arr.Arr.DPair<
                      {ws == w <> Nil{} : +List<+List<Nat>>},
                      FH.BodyMatch(G, C, n_root, has_buf, nodup, n, restg,
                        restb)>>
                case SolveFast.TwoItem{+f, +w1, +w2}:
                  Arr.Arr.DPair<
                    {nodup == True{} : Bool},
                    Arr.Arr.DPair<
                      {f == fb : +List<Feedback.Color>},
                      Arr.Arr.DPair<
                        {ws == w1 <> (w2 <> Nil{}) : +List<+List<Nat>>},
                        FH.BodyMatch(G, C, n_root, has_buf, nodup, n, restg,
                          restb)>>>
                case SolveFast.DoneItem{+f, +tree, +cost}:
                  Arr.Arr.DPair<
                    {nodup == True{} : Bool},
                    Arr.Arr.DPair<
                      {f == fb : +List<Feedback.Color>},
                      Arr.Arr.DPair<
                        {FH.done_ws_ok_b(G, ws, tree, cost) == True{} : Bool},
                        FH.BodyMatch(G, C, n_root, has_buf, nodup, n, restg,
                          restb)>>>
                case SolveFast.ClassItem{+f, +cws, +wlen, +tlb}:
                  match restb:
                    case Nil{}:
                      Empty
                    case Con{it2, restb2}:
                      match it2:
                        case SolveFast.Add{+f2, +tlb2}:
                          Arr.Arr.DPair<
                            {f == fb : +List<Feedback.Color>},
                            Arr.Arr.DPair<
                              {f2 == fb : +List<Feedback.Color>},
                              Arr.Arr.DPair<
                                {SolveFast.cwords_words(cws) == ws
                                 : +List<+List<Nat>>},
                                Arr.Arr.DPair<
                                  {wlen == Groups.len_words(ws) : Nat},
                                  Arr.Arr.DPair<
                                    {FH.cwords_ok_if(has_buf, G, C, n_root, cws)
                                     == True{} : Bool},
                                    Arr.Arr.DPair<
                                      {tlb == FH.body_lb(nodup, n, restb2)
                                       : Nat},
                                      Arr.Arr.DPair<
                                        {tlb2 == tlb : Nat},
                                        FH.BodyMatch(G, C, n_root, has_buf,
                                          nodup, n, restg, restb2)>>>>>>>
                        case SolveFast.Begin{_}:
                          Empty
                        case SolveFast.ClassItem{_, _, _, _}:
                          Empty
                        case SolveFast.OneItem{_, _}:
                          Empty
                        case SolveFast.TwoItem{_, _, _}:
                          Empty
                        case SolveFast.DoneItem{_, _, _}:
                          Empty
                        case SolveFast.End{}:
                          Empty
                case SolveFast.Add{_, _}:
                  Empty
                case SolveFast.End{}:
                  Empty

def FH.class_lb_fast_nil(nodup: Bool) ->
  {SolveFast.class_lb_fast(nodup, 0n, Nil{}) == 0n : Nat}:
  match nodup:
    case True{}:
      {==}
    case False{}:
      {==}

def FH.group_items_two_body_lb(nodup: Bool, +n: Nat,
    +fb: +List<Feedback.Color>, +w: +List<Nat>, +w2: +List<Nat>,
    +rest: +List<Groups.Group>,
    +ndh: {FN.FN.nodup_ok(nodup, w <> (w2 <> Nil{})) == True{} : Bool},
    +ih: {FH.body_lb(nodup, n,
            List.append(&2, SolveFast.Item,
              SolveFast.group_items(nodup, n, rest),
              SolveFast.End{} <> Nil{}))
          == SolveFast.lower_bound(n, rest) : Nat}) ->
  {FH.body_lb(nodup, n,
     List.append(&2, SolveFast.Item,
       SolveFast.group_items_two(nodup, n, fb, w, w2, rest,
         SolveFast.group_items(nodup, n, rest)),
       SolveFast.End{} <> Nil{}))
   == Nat.add(SolveFast.class_lb(w <> (w2 <> Nil{})),
        SolveFast.lower_bound(n, rest)) : Nat}:
  match nodup:
    case True{}:
      +ws2 : +List<+List<Nat>> = w <> (w2 <> Nil{})
      Equal.trans(Nat,
        Nat.add(3n,
          FH.body_lb(True{}, n,
            List.append(&2, SolveFast.Item,
              SolveFast.group_items(True{}, n, rest),
              SolveFast.End{} <> Nil{}))),
        Nat.add(SolveFast.class_lb(ws2),
          FH.body_lb(True{}, n,
            List.append(&2, SolveFast.Item,
              SolveFast.group_items(True{}, n, rest),
              SolveFast.End{} <> Nil{}))),
        Nat.add(SolveFast.class_lb(ws2), SolveFast.lower_bound(n, rest)),
        Equal.cong(Nat, Nat,
          x => Nat.add(x,
                 FH.body_lb(True{}, n,
                   List.append(&2, SolveFast.Item,
                     SolveFast.group_items(True{}, n, rest),
                     SolveFast.End{} <> Nil{}))),
          3n, SolveFast.class_lb(ws2), FN.FN.class_lb_nodup_eq(ws2, ndh)),
        Equal.cong(Nat, Nat, x => Nat.add(SolveFast.class_lb(ws2), x),
          FH.body_lb(True{}, n,
            List.append(&2, SolveFast.Item,
              SolveFast.group_items(True{}, n, rest),
              SolveFast.End{} <> Nil{})),
          SolveFast.lower_bound(n, rest), ih))
    case False{}:
      +ws2 : +List<+List<Nat>> = w <> (w2 <> Nil{})
      Equal.cong(Nat, Nat, x => Nat.add(SolveFast.class_lb(ws2), x),
        FH.body_lb(False{}, n,
          List.append(&2, SolveFast.Item,
            SolveFast.group_items(False{}, n, rest),
            SolveFast.End{} <> Nil{})),
        SolveFast.lower_bound(n, rest), ih)

def FH.group_items_body_lb_ws(+nodup: Bool, +n: Nat, +fb: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +rest: +List<Groups.Group>,
    +ndh: {FN.FN.nodup_ok(nodup, ws) == True{} : Bool},
    +ih: {FH.body_lb(nodup, n,
            List.append(&2, SolveFast.Item, SolveFast.group_items(nodup, n, rest),
              SolveFast.End{} <> Nil{}))
          == SolveFast.lower_bound(n, rest) : Nat}) ->
  {FH.body_lb(nodup, n,
     List.append(&2, SolveFast.Item,
       SolveFast.group_items(nodup, n, Groups.Group{fb, ws} <> rest),
       SolveFast.End{} <> Nil{}))
   == SolveFast.lower_bound(n, Groups.Group{fb, ws} <> rest) : Nat}:
  match ws:
    case Nil{}:
      Equal.trans(Nat,
        Nat.add(SolveFast.class_lb_fast(nodup, 0n, Nil{}),
          FH.body_lb(nodup, n,
            List.append(&2, SolveFast.Item,
              SolveFast.group_items(nodup, n, rest),
              SolveFast.End{} <> Nil{}))),
        FH.body_lb(nodup, n,
          List.append(&2, SolveFast.Item,
            SolveFast.group_items(nodup, n, rest),
            SolveFast.End{} <> Nil{})),
        SolveFast.lower_bound(n, rest),
        Equal.cong(Nat, Nat,
          x => Nat.add(x,
                 FH.body_lb(nodup, n,
                   List.append(&2, SolveFast.Item,
                     SolveFast.group_items(nodup, n, rest),
                     SolveFast.End{} <> Nil{}))),
          SolveFast.class_lb_fast(nodup, 0n, Nil{}), 0n,
          FH.class_lb_fast_nil(nodup)),
        ih)
    case Con{+w, +wt}:
      match wt:
        case Nil{}:
          +ws1 : +List<+List<Nat>> = w <> Nil{}
          Equal.trans(Nat,
            Nat.add(1n,
              FH.body_lb(nodup, n,
                List.append(&2, SolveFast.Item,
                  SolveFast.group_items(nodup, n, rest),
                  SolveFast.End{} <> Nil{}))),
            Nat.add(SolveFast.class_lb(ws1),
              FH.body_lb(nodup, n,
                List.append(&2, SolveFast.Item,
                  SolveFast.group_items(nodup, n, rest),
                  SolveFast.End{} <> Nil{}))),
            Nat.add(SolveFast.class_lb(ws1),
              SolveFast.lower_bound(n, rest)),
            Equal.cong(Nat, Nat,
              x => Nat.add(x,
                     FH.body_lb(nodup, n,
                       List.append(&2, SolveFast.Item,
                         SolveFast.group_items(nodup, n, rest),
                         SolveFast.End{} <> Nil{}))),
              1n, SolveFast.class_lb(ws1),
              FN.FN.class_lb_nodup_eq(ws1, {==})),
            Equal.cong(Nat, Nat, x => Nat.add(SolveFast.class_lb(ws1), x),
              FH.body_lb(nodup, n,
                List.append(&2, SolveFast.Item,
                  SolveFast.group_items(nodup, n, rest),
                  SolveFast.End{} <> Nil{})),
              SolveFast.lower_bound(n, rest), ih))
        case Con{+w2, +wt2}:
          match wt2:
            case Nil{}:
              FH.group_items_two_body_lb(nodup, n, fb, w, w2, rest, ndh, ih)
            case Con{+w3, +wt3}:
              +ws3 : +List<+List<Nat>> = w <> (w2 <> (w3 <> wt3))
              +edw : {SolveFast.cwords_words(SolveFast.dummy_cwords(ws3))
                      == ws3 : +List<+List<Nat>>} =
                FH.cwords_dummy_words(ws3)
              +eclb : {SolveFast.class_lb_fast(nodup,
                         Groups.len_words(ws3),
                         SolveFast.cwords_words(SolveFast.dummy_cwords(ws3)))
                       == SolveFast.class_lb(ws3) : Nat} =
                Equal.trans(Nat,
                  SolveFast.class_lb_fast(nodup, Groups.len_words(ws3),
                    SolveFast.cwords_words(SolveFast.dummy_cwords(ws3))),
                  SolveFast.class_lb_fast(nodup, Groups.len_words(ws3), ws3),
                  SolveFast.class_lb(ws3),
                  Equal.cong(+List<+List<Nat>>, Nat,
                    l => SolveFast.class_lb_fast(nodup,
                           Groups.len_words(ws3), l),
                    SolveFast.cwords_words(SolveFast.dummy_cwords(ws3)),
                    ws3, edw),
                  FN.FN.class_lb_fast_eq(nodup, Groups.len_words(ws3),
                    ws3, {==}, ndh))
              Equal.trans(Nat,
                Nat.add(
                  SolveFast.class_lb_fast(nodup, Groups.len_words(ws3),
                    SolveFast.cwords_words(SolveFast.dummy_cwords(ws3))),
                  FH.body_lb(nodup, n,
                    List.append(&2, SolveFast.Item,
                      SolveFast.group_items(nodup, n, rest),
                      SolveFast.End{} <> Nil{}))),
                Nat.add(SolveFast.class_lb(ws3),
                  FH.body_lb(nodup, n,
                    List.append(&2, SolveFast.Item,
                      SolveFast.group_items(nodup, n, rest),
                      SolveFast.End{} <> Nil{}))),
                Nat.add(SolveFast.class_lb(ws3),
                  SolveFast.lower_bound(n, rest)),
                Equal.cong(Nat, Nat,
                  x => Nat.add(x,
                         FH.body_lb(nodup, n,
                           List.append(&2, SolveFast.Item,
                             SolveFast.group_items(nodup, n, rest),
                             SolveFast.End{} <> Nil{}))),
                  SolveFast.class_lb_fast(nodup, Groups.len_words(ws3),
                    SolveFast.cwords_words(SolveFast.dummy_cwords(ws3))),
                  SolveFast.class_lb(ws3), eclb),
                Equal.cong(Nat, Nat, x => Nat.add(SolveFast.class_lb(ws3), x),
                  FH.body_lb(nodup, n,
                    List.append(&2, SolveFast.Item,
                      SolveFast.group_items(nodup, n, rest),
                      SolveFast.End{} <> Nil{})),
                  SolveFast.lower_bound(n, rest), ih))

def FH.group_items_body_lb(+nodup: Bool, +n: Nat,
    +groups: +List<Groups.Group>,
    +ng: {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(groups))
          == True{} : Bool}) ->
  {FH.body_lb(nodup, n,
     List.append(&2, SolveFast.Item, SolveFast.group_items(nodup, n, groups),
       SolveFast.End{} <> Nil{}))
   == SolveFast.lower_bound(n, groups) : Nat}:
  match groups:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+fb, +ws}:
          +ndh = Logic.Proof.and_true_l(FN.FN.nodup_ok(nodup, ws),
                   FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(rest)), ng)
          +ngt = Logic.Proof.and_true_r(FN.FN.nodup_ok(nodup, ws),
                   FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(rest)), ng)
          +ih = FH.group_items_body_lb(nodup, n, rest, ngt)
          FH.group_items_body_lb_ws(nodup, n, fb, ws, rest, ndh, ih)

def FH.group_items_two_body_match(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, nodup: Bool, +n: Nat, +fb: +List<Feedback.Color>,
    +w: +List<Nat>, +w2: +List<Nat>, +rest: +List<Groups.Group>,
    +elbr: {SolveFast.lower_bound(n, rest)
            == FH.body_lb(nodup, n,
                 List.append(&2, SolveFast.Item,
                   SolveFast.group_items(nodup, n, rest),
                   SolveFast.End{} <> Nil{})) : Nat},
    +hrest: FH.BodyMatch(G, C, n_root, False{}, nodup, n, rest,
              List.append(&2, SolveFast.Item,
                SolveFast.group_items(nodup, n, rest),
                SolveFast.End{} <> Nil{}))) ->
  FH.BodyMatch(G, C, n_root, False{}, nodup, n,
    Groups.Group{fb, w <> (w2 <> Nil{})} <> rest,
    List.append(&2, SolveFast.Item,
      SolveFast.group_items_two(nodup, n, fb, w, w2, rest,
        SolveFast.group_items(nodup, n, rest)),
      SolveFast.End{} <> Nil{})):
  match nodup:
    case True{}:
      Arr.DPair{{==}, Arr.DPair{{==}, Arr.DPair{{==}, hrest}}}
    case False{}:
      Arr.DPair{{==}, Arr.DPair{{==}, Arr.DPair{{==}, Arr.DPair{{==},
        Arr.DPair{{==}, Arr.DPair{elbr, Arr.DPair{{==}, hrest}}}}}}}

def FH.group_items_body_match_ws(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +nodup: Bool, +n: Nat, +fb: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +rest: +List<Groups.Group>,
    +elbr: {SolveFast.lower_bound(n, rest)
            == FH.body_lb(nodup, n,
                 List.append(&2, SolveFast.Item,
                   SolveFast.group_items(nodup, n, rest),
                   SolveFast.End{} <> Nil{})) : Nat},
    +hrest: FH.BodyMatch(G, C, n_root, False{}, nodup, n, rest,
              List.append(&2, SolveFast.Item,
                SolveFast.group_items(nodup, n, rest),
                SolveFast.End{} <> Nil{}))) ->
  FH.BodyMatch(G, C, n_root, False{}, nodup, n,
    Groups.Group{fb, ws} <> rest,
    List.append(&2, SolveFast.Item,
      SolveFast.group_items(nodup, n, Groups.Group{fb, ws} <> rest),
      SolveFast.End{} <> Nil{})):
  match ws:
    case Nil{}:
      Arr.DPair{{==}, Arr.DPair{{==}, Arr.DPair{{==}, Arr.DPair{{==},
        Arr.DPair{{==}, Arr.DPair{elbr, Arr.DPair{{==}, hrest}}}}}}}
    case Con{+w, +wt}:
      match wt:
        case Nil{}:
          Arr.DPair{{==}, Arr.DPair{{==}, hrest}}
        case Con{+w2, +wt2}:
          match wt2:
            case Nil{}:
              FH.group_items_two_body_match(G, C, n_root, nodup, n,
                fb, w, w2, rest, elbr, hrest)
            case Con{+w3, +wt3}:
              +ws3 : +List<+List<Nat>> = w <> (w2 <> (w3 <> wt3))
              Arr.DPair{{==}, Arr.DPair{{==},
                Arr.DPair{FH.cwords_dummy_words(ws3),
                  Arr.DPair{{==}, Arr.DPair{{==},
                    Arr.DPair{elbr, Arr.DPair{{==}, hrest}}}}}}}

def FH.group_items_body_match(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +nodup: Bool, +n: Nat, +groups: +List<Groups.Group>,
    +ng: {FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(groups))
          == True{} : Bool}) ->
  FH.BodyMatch(G, C, n_root, False{}, nodup, n, groups,
    List.append(&2, SolveFast.Item, SolveFast.group_items(nodup, n, groups),
      SolveFast.End{} <> Nil{})):
  match groups:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+fb, +ws}:
          +ngt = Logic.Proof.and_true_r(FN.FN.nodup_ok(nodup, ws),
                   FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(rest)), ng)
          +hrest = FH.group_items_body_match(G, C, n_root, nodup, n, rest, ngt)
          +elbr : {SolveFast.lower_bound(n, rest)
                   == FH.body_lb(nodup, n,
                        List.append(&2, SolveFast.Item,
                          SolveFast.group_items(nodup, n, rest),
                          SolveFast.End{} <> Nil{})) : Nat} =
            Equal.sym(Nat,
              FH.body_lb(nodup, n,
                List.append(&2, SolveFast.Item,
                  SolveFast.group_items(nodup, n, rest),
                  SolveFast.End{} <> Nil{})),
              SolveFast.lower_bound(n, rest),
              FH.group_items_body_lb(nodup, n, rest, ngt))
          FH.group_items_body_match_ws(G, C, n_root, nodup, n, fb, ws, rest,
            elbr, hrest)

# ---------------------------------------------------------------------------
# Pass 1: table-backed `hist5_go` with `skip_self` and early abort
# ---------------------------------------------------------------------------

def FH.bool_or_l(a: Bool, b: Bool, +ha: {a == True{} : Bool}) ->
  {Bool.or(a, b) == True{} : Bool}:
  Equal.cong(Bool, Bool, x => Bool.or(x, b), a, True{}, ha)

def FH.bool_or_r(a: Bool, b: Bool, +hb: {b == True{} : Bool}) ->
  {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def FH.pruned_reason(+g: +List<Nat>, +ws: +List<+List<Nat>>,
    +fg0: +List<SolveFast.FGroup>, +budget0: Nat, +skip_self: Bool) -> Bool:
  +fg1 = SolveFast.fgroups_build_fast(g, ws, fg0)
  Bool.or(
    Bool.and(skip_self, Tree.member_word(g, ws)),
    Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg1))),
              FH.fgroups_total(fg1)))

def FH.HistSpec(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +fg0: +List<SolveFast.FGroup>, +gen: Nat, +budget0: Nat, +skip_self: Bool,
    -tbl0: Array<U32>, res: SolveFast.Hist5Res) -> Data:
  match res:
    case SolveFast.Hist5Pruned{seen2, tbl2}:
      Arr.Arr.DPair<
        FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{}),
        Arr.Arr.DPair<
          {tbl2 == tbl0 : Array<U32>},
          {FH.pruned_reason(g, S, fg0, budget0, skip_self) == True{} : Bool}>>
    case SolveFast.Hist5Ok{seen2, tbl2, m, k, budget}:
      +fg1 : +List<SolveFast.FGroup> = SolveFast.fgroups_build_fast(g, S, fg0)
      Arr.Arr.DPair<
        FH.SeenTree(10n, 0, seen2, gen, fg1),
        Arr.Arr.DPair<
          {tbl2 == tbl0 : Array<U32>},
          Arr.Arr.DPair<
            {FH.fgroups_wf(fg1) == True{} : Bool},
            Arr.Arr.DPair<
              {m == FH.fgroups_total(fg1) : Nat},
              Arr.Arr.DPair<
                {k == FH.fgroups_count(fg1) : Nat},
                Arr.Arr.DPair<
                  {Nat.add(budget, m) == Nat.add(budget0, k) : Nat},
                  {Nat.is_le(m, Nat.add(Groups.len_words(S),
                                        FH.fgroups_total(fg0)))
                   == True{} : Bool}>>>>>>

def FH.hist_spec_transport(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +fg0: +List<SolveFast.FGroup>, +gen: Nat, +budget0: Nat, +skip_self: Bool,
    -tbl0: Array<U32>, -r1: SolveFast.Hist5Res, -r2: SolveFast.Hist5Res,
    +er: {r1 == r2 : SolveFast.Hist5Res},
    +h: FH.HistSpec(g, S, fg0, gen, budget0, skip_self, tbl0, r1)) ->
  FH.HistSpec(g, S, fg0, gen, budget0, skip_self, tbl0, r2):
  %er : FH.HistSpec(g, S, fg0, gen, budget0, skip_self, tbl0, _)
  h

def FH.hist_spec_transport_tbl(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +fg0: +List<SolveFast.FGroup>, +gen: Nat, +budget0: Nat, +skip_self: Bool,
    -t1: Array<U32>, -t2: Array<U32>, -r: SolveFast.Hist5Res,
    +et: {t1 == t2 : Array<U32>},
    +h: FH.HistSpec(g, S, fg0, gen, budget0, skip_self, t1, r)) ->
  FH.HistSpec(g, S, fg0, gen, budget0, skip_self, t2, r):
  %et : FH.HistSpec(g, S, fg0, gen, budget0, skip_self, _, r)
  h

def FH.HistOneSpec(+g: +List<Nat>, +w: +List<Nat>,
    +fg0: +List<SolveFast.FGroup>, +gen: Nat, +budget0: Nat, +skip_self: Bool,
    -tbl0: Array<U32>, res: SolveFast.Hist5Res) -> Data:
  match res:
    case SolveFast.Hist5Pruned{seen2, tbl2}:
      Arr.Arr.DPair<
        FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{}),
        Arr.Arr.DPair<
          {tbl2 == tbl0 : Array<U32>},
          {FH.pruned_reason(g, w <> Nil{}, fg0, budget0, skip_self)
           == True{} : Bool}>>
    case SolveFast.Hist5Ok{seen2, tbl2, m, k, budget}:
      +fg1 : +List<SolveFast.FGroup> =
        SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w))
      Arr.Arr.DPair<
        FH.SeenTree(10n, 0, seen2, gen, fg1),
        Arr.Arr.DPair<
          {tbl2 == tbl0 : Array<U32>},
          Arr.Arr.DPair<
            {FH.fgroups_wf(fg1) == True{} : Bool},
            Arr.Arr.DPair<
              {m == FH.fgroups_total(fg1) : Nat},
              Arr.Arr.DPair<
                {k == FH.fgroups_count(fg1) : Nat},
                Arr.Arr.DPair<
                  {Nat.add(budget, m) == Nat.add(budget0, k) : Nat},
                  {Nat.is_le(m, Nat.add(1n, FH.fgroups_total(fg0)))
                   == True{} : Bool}>>>>>>

def FH.hist_one_transport(+g: +List<Nat>, +w: +List<Nat>,
    +fg0: +List<SolveFast.FGroup>, +gen: Nat, +budget0: Nat, +skip_self: Bool,
    -tbl0: Array<U32>, -r1: SolveFast.Hist5Res, -r2: SolveFast.Hist5Res,
    +er: {r1 == r2 : SolveFast.Hist5Res},
    +h: FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl0, r1)) ->
  FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl0, r2):
  %er : FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl0, _)
  h

def FH.hist_one_transport_tbl(+g: +List<Nat>, +w: +List<Nat>,
    +fg0: +List<SolveFast.FGroup>, +gen: Nat, +budget0: Nat, +skip_self: Bool,
    -t1: Array<U32>, -t2: Array<U32>, -r: SolveFast.Hist5Res,
    +et: {t1 == t2 : Array<U32>},
    +h: FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, t1, r)) ->
  FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, t2, r):
  %et : FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, _, r)
  h

def FH.hist5_hit_branch(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>,
    -seen2: Array<Nat>, -tbl: Array<U32>, +gen: Nat, +m: Nat, +k: Nat,
    +budget0: Nat, +skip_self: Bool, seen_before: Bool, budget: Nat,
    +esb: {seen_before == FH.has_code(FF5.FF5.encode_fb5_list(fb), fg0) : Bool},
    +hbgt: {Nat.add(budget, m) == Nat.add(budget0, k) : Nat},
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
                 Nat.add(1n, FH.fgroups_count(fg0))) : Nat},
    dp: &s1: Array<Nat> -> &s2: Array<Nat> ->
        {s1 == seen2 : Array<Nat>} & {s2 == s1 : Array<Nat>}) ->
  FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl,
    SolveFast.hist5_hit(seen2, tbl, m, k, seen_before, budget)):
  match seen_before:
    case True{}:
      match budget:
        case 0n:
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
          +eeq : {Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg_next)))
                  == FH.fgroups_total(fg_next) : Nat} =
            Equal.trans(Nat,
              Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg_next))),
              Nat.add(1n, m),
              FH.fgroups_total(fg_next),
              Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                Nat.add(budget0, FH.fgroups_count(fg_next)), m,
                Equal.trans(Nat,
                  Nat.add(budget0, FH.fgroups_count(fg_next)),
                  Nat.add(budget0, k), m,
                  Equal.cong(Nat, Nat, x => Nat.add(budget0, x),
                    FH.fgroups_count(fg_next), k,
                    Equal.sym(Nat, k, FH.fgroups_count(fg_next), ek1)),
                  Equal.sym(Nat, m, Nat.add(budget0, k), hbgt))),
              em1)
          +hpr : {Nat.is_le(
                    Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg_next))),
                    FH.fgroups_total(fg_next)) == True{} : Bool} =
            NatProof.Nat.is_le_eq_r(
              Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg_next))),
              Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg_next))),
              FH.fgroups_total(fg_next), eeq,
              NatProof.Nat.is_le_refl(
                Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg_next)))))
          Arr.DPair{
            FH.seen_tree_bump_erased(seen2, gen, fg_next, hs_next, dp),
            Arr.DPair{{==},
              FH.bool_or_r(Bool.and(skip_self, Tree.member_word(g, w <> Nil{})),
                Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg_next))),
                  FH.fgroups_total(fg_next)), hpr)}}
        case 1n++bp:
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
          +hbgt1 : {Nat.add(bp, Nat.add(1n, m)) == Nat.add(budget0, k) : Nat} =
            Equal.trans(Nat,
              Nat.add(bp, Nat.add(1n, m)),
              Nat.add(1n, Nat.add(bp, m)),
              Nat.add(budget0, k),
              NatProof.NatPrf.add_succ(bp, m), hbgt)
          Arr.DPair{hs_next, Arr.DPair{{==}, Arr.DPair{wf_next,
            Arr.DPair{em1, Arr.DPair{ek1, Arr.DPair{hbgt1, hle1}}}}}}
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
      +hbgt1 : {Nat.add(budget, Nat.add(1n, m))
                == Nat.add(budget0, Nat.add(1n, k)) : Nat} =
        Equal.trans(Nat,
          Nat.add(budget, Nat.add(1n, m)),
          Nat.add(1n, Nat.add(budget, m)),
          Nat.add(budget0, Nat.add(1n, k)),
          NatProof.NatPrf.add_succ(budget, m),
          Equal.trans(Nat,
            Nat.add(1n, Nat.add(budget, m)),
            Nat.add(1n, Nat.add(budget0, k)),
            Nat.add(budget0, Nat.add(1n, k)),
            Equal.cong(Nat, Nat, x => Nat.add(1n, x),
              Nat.add(budget, m), Nat.add(budget0, k), hbgt),
            Equal.sym(Nat, Nat.add(budget0, Nat.add(1n, k)),
              Nat.add(1n, Nat.add(budget0, k)),
              NatProof.NatPrf.add_succ(budget0, k))))
      Arr.DPair{hs_next, Arr.DPair{{==}, Arr.DPair{wf_next,
        Arr.DPair{em1, Arr.DPair{ek1, Arr.DPair{hbgt1, hle1}}}}}}

def FH.hist5_hit_spec(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>,
    -seen2: Array<Nat>, -tbl: Array<U32>, +gen: Nat, +m: Nat, +k: Nat,
    +budget0: Nat, +skip_self: Bool, seen_before: Bool, +budget: Nat,
    +esb: {seen_before == FH.has_code(FF5.FF5.encode_fb5_list(fb), fg0) : Bool},
    +hbgt: {Nat.add(budget, m) == Nat.add(budget0, k) : Nat},
    +efg1: {SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w))
            == SolveFast.fgroup_add_fast(w, fb, fg0) : +List<SolveFast.FGroup>},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs_new: FH.SeenTree(10n, 0, seen2, gen,
               SolveFast.fgroup_add_fast(w, fb, fg0)),
    facts: FH.AddFacts<w, fb, fg0, SolveFast.fgroup_add_fast(w, fb, fg0)>,
    dp: &s1: Array<Nat> -> &s2: Array<Nat> ->
        {s1 == seen2 : Array<Nat>} & {s2 == s1 : Array<Nat>}) ->
  FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl,
    SolveFast.hist5_hit(seen2, tbl, m, k, seen_before, budget)):
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
      FH.hist5_hit_branch(g, w, fb, fg0, seen2, tbl, gen, m, k, budget0,
        skip_self, seen_before, budget, esb, hbgt, efg1, hk, hs_next, wf_next,
        em1, hle1, cnt2, dp)

def FH.hist5_swap_spec_go(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>,
    -tbl: Array<U32>, +gen: Nat, +m: Nat, +k: Nat, +budget0: Nat, +budget: Nat,
    +skip_self: Bool, r: Array<Nat> & Nat,
    +hbgt: {Nat.add(budget, m) == Nat.add(budget0, k) : Nat},
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
  FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl,
    SolveFast.hist5_swap(tbl, gen, m, k, budget, r)):
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
  FH.hist5_hit_spec(g, w, fb, fg0, seen2, tbl, gen, m, k, budget0, skip_self,
    Nat.is_eq(old, gen), budget, hold, hbgt, efg1, hm, hk, hs_new, facts,
    Arr.Arr.dup(Nat, seen2))

def FH.hist5_step_swap_dup4(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>,
    -seen: Array<Nat>, -tbl: Array<U32>,
    s1: Array<Nat>, +ea1: {s1 == seen : Array<Nat>},
    b1: Array<Nat>, +ea_b1: {b1 == s1 : Array<Nat>},
    b2: Array<Nat>, +ea_b2: {b2 == s1 : Array<Nat>},
    -b3: Array<Nat>, +ea_b3: {b3 == s1 : Array<Nat>},
    dp4: &c1: Array<Nat> -> &c2: Array<Nat> ->
         {c1 == b3 : Array<Nat>} & {c2 == c1 : Array<Nat>},
    +gen: Nat, +m: Nat, +k: Nat, +budget0: Nat, +budget: Nat,
    +skip_self: Bool, +code: U32,
    +hbgt: {Nat.add(budget, m) == Nat.add(budget0, k) : Nat},
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +ewf: {SolveFast.word_eq_fast(g, w) == False{} : Bool},
    +efbeq: {SolveFast.feedback_fast(g, w) == fb : +List<Feedback.Color>},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg0),
    +hself: {FH.has_code(FF5.FF5.encode_fb5_list(fb),
               SolveFast.fgroup_add_fast(w, fb, fg0)) == True{} : Bool}) ->
  FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl,
    SolveFast.hist5_swap(tbl, gen, m, k, budget,
      Array.swap(Nat, seen, code, gen))):
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
  %ea1 : FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl,
           SolveFast.hist5_swap(tbl, gen, m, k, budget,
             Array.swap(Nat, _, code, gen)))
  %Equal.sym(U32, code, c, ecode) :
    FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl,
      SolveFast.hist5_swap(tbl, gen, m, k, budget,
        Array.swap(Nat, s1, _, gen)))
  FH.hist5_swap_spec_go(g, w, fb, fg0, tbl, gen, m, k, budget0, budget,
    skip_self, Array.swap(Nat, s1, c, gen), hbgt, ewf, efbeq, hfb, hwf, hm, hk,
    hs_new_s1, hok_s1)

def FH.hist5_step_swap_dup3(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>,
    -seen: Array<Nat>, -tbl: Array<U32>,
    s1: Array<Nat>, +ea1: {s1 == seen : Array<Nat>},
    b1: Array<Nat>, +ea_b1: {b1 == s1 : Array<Nat>},
    -b2: Array<Nat>, +ea_b2: {b2 == s1 : Array<Nat>},
    dp3: &x1: Array<Nat> -> &x2: Array<Nat> ->
         {x1 == b2 : Array<Nat>} & {x2 == x1 : Array<Nat>},
    +gen: Nat, +m: Nat, +k: Nat, +budget0: Nat, +budget: Nat,
    +skip_self: Bool, +code: U32,
    +hbgt: {Nat.add(budget, m) == Nat.add(budget0, k) : Nat},
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +ewf: {SolveFast.word_eq_fast(g, w) == False{} : Bool},
    +efbeq: {SolveFast.feedback_fast(g, w) == fb : +List<Feedback.Color>},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg0),
    +hself: {FH.has_code(FF5.FF5.encode_fb5_list(fb),
               SolveFast.fgroup_add_fast(w, fb, fg0)) == True{} : Bool}) ->
  FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl,
    SolveFast.hist5_swap(tbl, gen, m, k, budget,
      Array.swap(Nat, seen, code, gen))):
  (x1, dpx) = dp3
  (x2, pex) = dpx
  (+ex1, +ex2) = pex
  +ea_x1 : {x1 == s1 : Array<Nat>} = Equal.trans(Array<Nat>, x1, b2, s1, ex1, ea_b2)
  +ea_x2 : {x2 == s1 : Array<Nat>} = Equal.trans(Array<Nat>, x2, x1, s1, ex2, ea_x1)
  FH.hist5_step_swap_dup4(g, w, fb, fg0, seen, tbl, s1, ea1, b1, ea_b1,
    x1, ea_x1, x2, ea_x2, Arr.Arr.dup(Nat, x2), gen, m, k, budget0, budget,
    skip_self, code, hbgt, ecode, ewf, efbeq, hfb, hwf, hm, hk, hs, hself)

def FH.hist5_step_swap_dup2(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>,
    -seen: Array<Nat>, -tbl: Array<U32>,
    s1: Array<Nat>, +ea1: {s1 == seen : Array<Nat>},
    -s2: Array<Nat>, +ea2: {s2 == s1 : Array<Nat>},
    dp2: &b1: Array<Nat> -> &b2: Array<Nat> ->
         {b1 == s2 : Array<Nat>} & {b2 == b1 : Array<Nat>},
    +gen: Nat, +m: Nat, +k: Nat, +budget0: Nat, +budget: Nat,
    +skip_self: Bool, +code: U32,
    +hbgt: {Nat.add(budget, m) == Nat.add(budget0, k) : Nat},
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +ewf: {SolveFast.word_eq_fast(g, w) == False{} : Bool},
    +efbeq: {SolveFast.feedback_fast(g, w) == fb : +List<Feedback.Color>},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg0),
    +hself: {FH.has_code(FF5.FF5.encode_fb5_list(fb),
               SolveFast.fgroup_add_fast(w, fb, fg0)) == True{} : Bool}) ->
  FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl,
    SolveFast.hist5_swap(tbl, gen, m, k, budget,
      Array.swap(Nat, seen, code, gen))):
  (b1, dp3) = dp2
  (b2, pe2) = dp3
  (+eb1, +eb2) = pe2
  +ea_b1 : {b1 == s1 : Array<Nat>} = Equal.trans(Array<Nat>, b1, s2, s1, eb1, ea2)
  +ea_b2 : {b2 == s1 : Array<Nat>} = Equal.trans(Array<Nat>, b2, b1, s1, eb2, ea_b1)
  FH.hist5_step_swap_dup3(g, w, fb, fg0, seen, tbl, s1, ea1, b1, ea_b1,
    b2, ea_b2, Arr.Arr.dup(Nat, b2), gen, m, k, budget0, budget, skip_self,
    code, hbgt, ecode, ewf, efbeq, hfb, hwf, hm, hk, hs, hself)

def FH.hist5_step_swap_dup(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>,
    -seen: Array<Nat>, -tbl: Array<U32>,
    +gen: Nat, +m: Nat, +k: Nat, +budget0: Nat, +budget: Nat,
    +skip_self: Bool, +code: U32,
    +hbgt: {Nat.add(budget, m) == Nat.add(budget0, k) : Nat},
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
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
  FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl,
    SolveFast.hist5_swap(tbl, gen, m, k, budget,
      Array.swap(Nat, seen, code, gen))):
  (s1, dp2) = dp
  (s2, pe) = dp2
  (+ea1, +ea2) = pe
  FH.hist5_step_swap_dup2(g, w, fb, fg0, seen, tbl, s1, ea1, s2, ea2,
    Arr.Arr.dup(Nat, s2), gen, m, k, budget0, budget, skip_self, code, hbgt,
    ecode, ewf, efbeq, hfb, hwf, hm, hk, hs, hself)

def FH.add_facts_has_self(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +fg0: +List<SolveFast.FGroup>, +fg1: +List<SolveFast.FGroup>,
    f: FH.AddFacts<w, fb, fg0, fg1>) ->
  {FH.has_code(FF5.FF5.encode_fb5_list(fb), fg1) == True{} : Bool}:
  match f:
    case AddFacts{wf2, tot2, cnt2, has_self, lkp_self}:
      has_self

def FH.hist5_same_spec(+g: +List<Nat>, +w: +List<Nat>,
    +fg0: +List<SolveFast.FGroup>, seen: Array<Nat>, -tbl: Array<U32>,
    +gen: Nat, +m: Nat, +k: Nat, +budget0: Nat, +budget: Nat, skip_self: Bool,
    +hbgt: {Nat.add(budget, m) == Nat.add(budget0, k) : Nat},
    +ewt: {SolveFast.word_eq_fast(g, w) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg0)) ->
  FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl,
    SolveFast.hist5_same(seen, tbl, m, k, budget, skip_self)):
  match skip_self:
    case True{}:
      +heq : {Feedback.word_eq(g, w) == True{} : Bool} =
        Equal.trans(Bool, Feedback.word_eq(g, w), SolveFast.word_eq_fast(g, w),
          True{},
          Equal.sym(Bool, SolveFast.word_eq_fast(g, w), Feedback.word_eq(g, w),
            FG.FG.word_eq_fast_eq(g, w)),
          ewt)
      +hmem : {Tree.member_word(g, w <> Nil{}) == True{} : Bool} =
        Equal.cong(Bool, Bool,
          b => Feedback.Bool.case(Bool, b, True{}, False{}),
          Feedback.word_eq(g, w), True{}, heq)
      +fg1 = SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w))
      Arr.DPair{
        FH.seen_tree_bump(10n, 0, seen, gen, fg0, hs),
        Arr.DPair{{==},
          FH.bool_or_l(Tree.member_word(g, w <> Nil{}),
            Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg1))),
              FH.fgroups_total(fg1)), hmem)}}
    case False{}:
      +fg_next = SolveFast.fgroups_next_acc(g, w, fg0,
                   SolveFast.word_eq_fast(g, w))
      +efg : {fg0 == fg_next : +List<SolveFast.FGroup>} =
        Equal.sym(+List<SolveFast.FGroup>, fg_next, fg0,
          Equal.cong(Bool, +List<SolveFast.FGroup>,
            b => SolveFast.fgroups_next_acc(g, w, fg0, b),
            SolveFast.word_eq_fast(g, w), True{}, ewt))
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
      Arr.DPair{hs2, Arr.DPair{{==}, Arr.DPair{wf2,
        Arr.DPair{hm2, Arr.DPair{hk2, Arr.DPair{hbgt, hle}}}}}}

def FH.hist5_step_spec(+g: +List<Nat>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +fg0: +List<SolveFast.FGroup>,
    seen: Array<Nat>, -tbl: Array<U32>, +gen: Nat, +m: Nat, +k: Nat,
    +budget0: Nat, +budget: Nat, +skip_self: Bool, +code: U32, same: Bool,
    +hbgt: {Nat.add(budget, m) == Nat.add(budget0, k) : Nat},
    +esame: {same == SolveFast.word_eq_fast(g, w) : Bool},
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +efbeq: {SolveFast.feedback_fast(g, w) == fb : +List<Feedback.Color>},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg0)) ->
  FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl,
    SolveFast.hist5_step(seen, tbl, gen, m, k, budget, skip_self, code, same)):
  match same:
    case True{}:
      FH.hist5_same_spec(g, w, fg0, seen, tbl, gen, m, k, budget0, budget,
        skip_self, hbgt,
        Equal.sym(Bool, True{}, SolveFast.word_eq_fast(g, w), esame),
        hwf, hm, hk, hs)
    case False{}:
      +ewf : {SolveFast.word_eq_fast(g, w) == False{} : Bool} =
        Equal.sym(Bool, False{}, SolveFast.word_eq_fast(g, w), esame)
      +hself = FH.add_facts_has_self(w, fb, fg0,
                 SolveFast.fgroup_add_fast(w, fb, fg0),
                 FH.fgroup_add_facts(w, fb, fg0,
                   SolveFast.next_fgroup_hit(fb, fg0), {==}, hfb, hwf))
      FH.hist5_step_swap_dup(g, w, fb, fg0, seen, tbl, gen, m, k, budget0,
        budget, skip_self, code, hbgt, ecode, ewf, efbeq, hfb, hwf, hm, hk,
        hs, hself, Arr.Arr.dup(Nat, seen))

def FH.hist5_one_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +row: U32, +g: +List<Nat>, +cw: SolveFast.CWord,
    +fg0: +List<SolveFast.FGroup>, seen: Array<Nat>, tbl: Array<U32>,
    +gen: Nat, +m: Nat, +k: Nat, +budget0: Nat, +budget: Nat, +skip_self: Bool,
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hcw: {FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
    +hbgt: {Nat.add(budget, m) == Nat.add(budget0, k) : Nat},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg0)) ->
  FH.HistOneSpec(g, SolveFast.cword_w(cw), fg0, gen, budget0, skip_self, tbl,
    SolveFast.hist5_one(row, cw, seen, tbl, gen, m, k, budget, skip_self)):
  match cw:
    case SolveFast.CWord{+ci, +grow, +w}:
      +hcol = Logic.Proof.and_true_l(FT.FT.has_col_go(Groups.len_words(G), C, ci, w, 0n),
                FT.FT.gentry_ok_b(G, n_root, grow, w), hcw)
      FT.FT.tbl_get_use(
        r => FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl,
               SolveFast.hist5_tbl_done(seen, gen, m, k, budget, skip_self, r)),
        G, C, n_root, row, g, ci, w, tbl, htbl, hrow, hcol,
        tbl2 => +code => +etbl2 => +htbl2 => +ecode => +hg5 => +hw5 =>
          +fb = Feedback.feedback(g, w)
          +hfb : {FF5.FF5.is_fb5(fb) == True{} : Bool} =
            FT.FT.is_fb5_of_len5(g, w, hg5, hw5)
          +esame : {U32.is_eq(code, 682) == SolveFast.word_eq_fast(g, w) : Bool} =
            Equal.trans(Bool, U32.is_eq(code, 682), Feedback.word_eq(g, w),
              SolveFast.word_eq_fast(g, w),
              Equal.trans(Bool, U32.is_eq(code, 682),
                U32.is_eq(FT.FT.fb_code_words(g, w), 682),
                Feedback.word_eq(g, w),
                Equal.cong(U32, Bool, u => U32.is_eq(u, 682),
                  code, FT.FT.fb_code_words(g, w), ecode),
                FT.FT.fb_code_is_682(g, w, hg5, hw5)),
              Equal.sym(Bool, SolveFast.word_eq_fast(g, w),
                Feedback.word_eq(g, w), FG.FG.word_eq_fast_eq(g, w)))
          FH.hist_one_transport_tbl(g, w, fg0, gen, budget0, skip_self,
            tbl2, tbl,
            SolveFast.hist5_step(seen, tbl2, gen, m, k, budget, skip_self,
              code, U32.is_eq(code, 682)),
            etbl2,
            FH.hist5_step_spec(g, w, fb, fg0, seen, tbl2, gen, m, k, budget0,
              budget, skip_self, code, U32.is_eq(code, 682), hbgt, esame,
              ecode, FG.FG.feedback_eq(g, w), hfb, hwf, hm, hk, hs)))

def FH.word_eq_true_of_mem_one(b: Bool,
    +e: {Feedback.Bool.case(Bool, b, True{}, False{}) == True{} : Bool}) ->
  {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def FH.pruned_reason_one_ext(+g: +List<Nat>, +w: +List<Nat>,
    +rest: +List<+List<Nat>>, +fg0: +List<SolveFast.FGroup>, +budget0: Nat,
    +skip_self: Bool, b: Bool,
    +eb: {b == Bool.and(skip_self, Tree.member_word(g, w <> Nil{})) : Bool},
    +h1: {FH.pruned_reason(g, w <> Nil{}, fg0, budget0, skip_self)
          == True{} : Bool}) ->
  {FH.pruned_reason(g, w <> rest, fg0, budget0, skip_self) == True{} : Bool}:
  match b:
    case True{}:
      +hand : {Bool.and(skip_self, Tree.member_word(g, w <> Nil{}))
               == True{} : Bool} =
        Equal.sym(Bool, True{},
          Bool.and(skip_self, Tree.member_word(g, w <> Nil{})), eb)
      +hsk = Logic.Proof.and_true_l(skip_self, Tree.member_word(g, w <> Nil{}),
               hand)
      +hm1 = Logic.Proof.and_true_r(skip_self, Tree.member_word(g, w <> Nil{}),
               hand)
      +heq : {Feedback.word_eq(g, w) == True{} : Bool} =
        FH.word_eq_true_of_mem_one(Feedback.word_eq(g, w), hm1)
      +hm2 : {Tree.member_word(g, w <> rest) == True{} : Bool} =
        Equal.cong(Bool, Bool,
          x => Feedback.Bool.case(Bool, x, True{}, Tree.member_word(g, rest)),
          Feedback.word_eq(g, w), True{}, heq)
      +fg2 = SolveFast.fgroups_build_fast(g, w <> rest, fg0)
      FH.bool_or_l(Bool.and(skip_self, Tree.member_word(g, w <> rest)),
        Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg2))),
          FH.fgroups_total(fg2)),
        FH.bool_and_intro(skip_self, Tree.member_word(g, w <> rest), hsk, hm2))
    case False{}:
      +fg1 = SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w))
      +fg2 = SolveFast.fgroups_build_fast(g, rest, fg1)
      +hpr1 : {Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg1))),
                 FH.fgroups_total(fg1)) == True{} : Bool} =
        Equal.trans(Bool,
          Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg1))),
            FH.fgroups_total(fg1)),
          Bool.or(Bool.and(skip_self, Tree.member_word(g, w <> Nil{})),
            Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg1))),
              FH.fgroups_total(fg1))),
          True{},
          Equal.cong(Bool, Bool,
            x => Bool.or(x,
                   Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg1))),
                     FH.fgroups_total(fg1))),
            False{}, Bool.and(skip_self, Tree.member_word(g, w <> Nil{})), eb),
          h1)
      FH.bool_or_r(Bool.and(skip_self, Tree.member_word(g, w <> rest)),
        Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg2))),
          FH.fgroups_total(fg2)),
        FH.pruned_build_mono(g, rest, fg1, budget0, hpr1))

def FH.pruned_reason_cons_lift(+g: +List<Nat>, +w: +List<Nat>,
    +rest: +List<+List<Nat>>, +fg0: +List<SolveFast.FGroup>, +budget0: Nat,
    +skip_self: Bool, b: Bool,
    +eb: {b == Bool.and(skip_self, Tree.member_word(g, rest)) : Bool},
    +hrec: {FH.pruned_reason(g, rest,
              SolveFast.fgroups_next_acc(g, w, fg0,
                SolveFast.word_eq_fast(g, w)), budget0, skip_self)
            == True{} : Bool}) ->
  {FH.pruned_reason(g, w <> rest, fg0, budget0, skip_self) == True{} : Bool}:
  match b:
    case True{}:
      +hand : {Bool.and(skip_self, Tree.member_word(g, rest)) == True{} : Bool} =
        Equal.sym(Bool, True{},
          Bool.and(skip_self, Tree.member_word(g, rest)), eb)
      +hsk = Logic.Proof.and_true_l(skip_self, Tree.member_word(g, rest), hand)
      +hmr = Logic.Proof.and_true_r(skip_self, Tree.member_word(g, rest), hand)
      +hm2 : {Tree.member_word(g, w <> rest) == True{} : Bool} =
        FN.FN.member_cons_r(g, w, rest, hmr)
      +fg2 = SolveFast.fgroups_build_fast(g, w <> rest, fg0)
      FH.bool_or_l(Bool.and(skip_self, Tree.member_word(g, w <> rest)),
        Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg2))),
          FH.fgroups_total(fg2)),
        FH.bool_and_intro(skip_self, Tree.member_word(g, w <> rest), hsk, hm2))
    case False{}:
      +fg2 = SolveFast.fgroups_build_fast(g, w <> rest, fg0)
      +hpr2 : {Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg2))),
                 FH.fgroups_total(fg2)) == True{} : Bool} =
        Equal.trans(Bool,
          Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg2))),
            FH.fgroups_total(fg2)),
          Bool.or(Bool.and(skip_self, Tree.member_word(g, rest)),
            Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg2))),
              FH.fgroups_total(fg2))),
          True{},
          Equal.cong(Bool, Bool,
            x => Bool.or(x,
                   Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg2))),
                     FH.fgroups_total(fg2))),
            False{}, Bool.and(skip_self, Tree.member_word(g, rest)), eb),
          hrec)
      FH.bool_or_r(Bool.and(skip_self, Tree.member_word(g, w <> rest)),
        Nat.is_le(Nat.add(1n, Nat.add(budget0, FH.fgroups_count(fg2))),
          FH.fgroups_total(fg2)), hpr2)

def FH.hist5_pruned_rest(+row: U32, +g: +List<Nat>, +w: +List<Nat>,
    +rest: +List<SolveFast.CWord>, +fg0: +List<SolveFast.FGroup>,
    +gen: Nat, +budget0: Nat, +skip_self: Bool,
    -seen2: Array<Nat>, -tbl0: Array<U32>, -tbl2: Array<U32>,
    +h1: Arr.Arr.DPair<
           FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{}),
           Arr.Arr.DPair<
             {tbl2 == tbl0 : Array<U32>},
             {FH.pruned_reason(g, w <> Nil{}, fg0, budget0, skip_self)
              == True{} : Bool}>>) ->
  FH.HistSpec(g, w <> SolveFast.cwords_words(rest), fg0, gen, budget0,
    skip_self, tbl0,
    SolveFast.hist5_go(row, rest, gen, skip_self,
      SolveFast.Hist5Pruned{seen2, tbl2})):
  match rest:
    case Nil{}:
      h1
    case Con{+cw2, +rest2}:
      +rw : +List<+List<Nat>> = SolveFast.cwords_words(cw2 <> rest2)
      +hs2 = Arr.Arr.dpair_l(
               FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{}),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 {FH.pruned_reason(g, w <> Nil{}, fg0, budget0, skip_self)
                  == True{} : Bool}>, h1)
      +hr = Arr.Arr.dpair_r(
              FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{}),
              Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                {FH.pruned_reason(g, w <> Nil{}, fg0, budget0, skip_self)
                 == True{} : Bool}>, h1)
      +et = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
              {FH.pruned_reason(g, w <> Nil{}, fg0, budget0, skip_self)
               == True{} : Bool}, hr)
      +hpr = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
               {FH.pruned_reason(g, w <> Nil{}, fg0, budget0, skip_self)
                == True{} : Bool}, hr)
      Arr.DPair{hs2, Arr.DPair{et,
        FH.pruned_reason_one_ext(g, w, rw, fg0, budget0, skip_self,
          Bool.and(skip_self, Tree.member_word(g, w <> Nil{})), {==}, hpr)}}

def FH.hist5_go_lift(+g: +List<Nat>, +w: +List<Nat>, +rest: +List<+List<Nat>>,
    +fg0: +List<SolveFast.FGroup>, +gen: Nat, +budget0: Nat, +skip_self: Bool,
    -tbl0: Array<U32>, res: SolveFast.Hist5Res,
    +hle_fg1: {Nat.is_le(
                 FH.fgroups_total(
                   SolveFast.fgroups_next_acc(g, w, fg0,
                     SolveFast.word_eq_fast(g, w))),
                 Nat.add(1n, FH.fgroups_total(fg0))) == True{} : Bool},
    +hrec: FH.HistSpec(g, rest,
             SolveFast.fgroups_next_acc(g, w, fg0,
               SolveFast.word_eq_fast(g, w)), gen, budget0, skip_self, tbl0,
             res)) ->
  FH.HistSpec(g, w <> rest, fg0, gen, budget0, skip_self, tbl0, res):
  match res:
    case SolveFast.Hist5Pruned{seen3, tbl3}:
      +fg1 = SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w))
      +hs3 = Arr.Arr.dpair_l(
               FH.SeenTree(10n, 0, seen3, Nat.add(1n, gen), Nil{}),
               Arr.Arr.DPair<{tbl3 == tbl0 : Array<U32>},
                 {FH.pruned_reason(g, rest, fg1, budget0, skip_self)
                  == True{} : Bool}>, hrec)
      +hr = Arr.Arr.dpair_r(
              FH.SeenTree(10n, 0, seen3, Nat.add(1n, gen), Nil{}),
              Arr.Arr.DPair<{tbl3 == tbl0 : Array<U32>},
                {FH.pruned_reason(g, rest, fg1, budget0, skip_self)
                 == True{} : Bool}>, hrec)
      +et3 = Arr.Arr.dpair_l({tbl3 == tbl0 : Array<U32>},
               {FH.pruned_reason(g, rest, fg1, budget0, skip_self)
                == True{} : Bool}, hr)
      +hpr = Arr.Arr.dpair_r({tbl3 == tbl0 : Array<U32>},
               {FH.pruned_reason(g, rest, fg1, budget0, skip_self)
                == True{} : Bool}, hr)
      Arr.DPair{hs3, Arr.DPair{et3,
        FH.pruned_reason_cons_lift(g, w, rest, fg0, budget0, skip_self,
          Bool.and(skip_self, Tree.member_word(g, rest)), {==}, hpr)}}
    case SolveFast.Hist5Ok{seen3, tbl3, +m3, +k3, +b3}:
      +fg1 = SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w))
      +fg2 = SolveFast.fgroups_build_fast(g, rest, fg1)
      +hs3 = Arr.Arr.dpair_l(
               FH.SeenTree(10n, 0, seen3, gen, fg2),
               Arr.Arr.DPair<{tbl3 == tbl0 : Array<U32>},
                 Arr.Arr.DPair<{FH.fgroups_wf(fg2) == True{} : Bool},
                   Arr.Arr.DPair<{m3 == FH.fgroups_total(fg2) : Nat},
                     Arr.Arr.DPair<{k3 == FH.fgroups_count(fg2) : Nat},
                       Arr.Arr.DPair<
                         {Nat.add(b3, m3) == Nat.add(budget0, k3) : Nat},
                         {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                                FH.fgroups_total(fg1)))
                          == True{} : Bool}>>>>>, hrec)
      +r1 = Arr.Arr.dpair_r(
              FH.SeenTree(10n, 0, seen3, gen, fg2),
              Arr.Arr.DPair<{tbl3 == tbl0 : Array<U32>},
                Arr.Arr.DPair<{FH.fgroups_wf(fg2) == True{} : Bool},
                  Arr.Arr.DPair<{m3 == FH.fgroups_total(fg2) : Nat},
                    Arr.Arr.DPair<{k3 == FH.fgroups_count(fg2) : Nat},
                      Arr.Arr.DPair<
                        {Nat.add(b3, m3) == Nat.add(budget0, k3) : Nat},
                        {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                               FH.fgroups_total(fg1)))
                         == True{} : Bool}>>>>>, hrec)
      +et3 = Arr.Arr.dpair_l({tbl3 == tbl0 : Array<U32>},
               Arr.Arr.DPair<{FH.fgroups_wf(fg2) == True{} : Bool},
                 Arr.Arr.DPair<{m3 == FH.fgroups_total(fg2) : Nat},
                   Arr.Arr.DPair<{k3 == FH.fgroups_count(fg2) : Nat},
                     Arr.Arr.DPair<
                       {Nat.add(b3, m3) == Nat.add(budget0, k3) : Nat},
                       {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                              FH.fgroups_total(fg1)))
                        == True{} : Bool}>>>>, r1)
      +r2 = Arr.Arr.dpair_r({tbl3 == tbl0 : Array<U32>},
              Arr.Arr.DPair<{FH.fgroups_wf(fg2) == True{} : Bool},
                Arr.Arr.DPair<{m3 == FH.fgroups_total(fg2) : Nat},
                  Arr.Arr.DPair<{k3 == FH.fgroups_count(fg2) : Nat},
                    Arr.Arr.DPair<
                      {Nat.add(b3, m3) == Nat.add(budget0, k3) : Nat},
                      {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                             FH.fgroups_total(fg1)))
                       == True{} : Bool}>>>>, r1)
      +hwf2 = Arr.Arr.dpair_l({FH.fgroups_wf(fg2) == True{} : Bool},
                Arr.Arr.DPair<{m3 == FH.fgroups_total(fg2) : Nat},
                  Arr.Arr.DPair<{k3 == FH.fgroups_count(fg2) : Nat},
                    Arr.Arr.DPair<
                      {Nat.add(b3, m3) == Nat.add(budget0, k3) : Nat},
                      {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                             FH.fgroups_total(fg1)))
                       == True{} : Bool}>>>, r2)
      +r3 = Arr.Arr.dpair_r({FH.fgroups_wf(fg2) == True{} : Bool},
              Arr.Arr.DPair<{m3 == FH.fgroups_total(fg2) : Nat},
                Arr.Arr.DPair<{k3 == FH.fgroups_count(fg2) : Nat},
                  Arr.Arr.DPair<
                    {Nat.add(b3, m3) == Nat.add(budget0, k3) : Nat},
                    {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                           FH.fgroups_total(fg1)))
                     == True{} : Bool}>>>, r2)
      +hm3 = Arr.Arr.dpair_l({m3 == FH.fgroups_total(fg2) : Nat},
               Arr.Arr.DPair<{k3 == FH.fgroups_count(fg2) : Nat},
                 Arr.Arr.DPair<
                   {Nat.add(b3, m3) == Nat.add(budget0, k3) : Nat},
                   {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                          FH.fgroups_total(fg1)))
                    == True{} : Bool}>>, r3)
      +r4 = Arr.Arr.dpair_r({m3 == FH.fgroups_total(fg2) : Nat},
              Arr.Arr.DPair<{k3 == FH.fgroups_count(fg2) : Nat},
                Arr.Arr.DPair<
                  {Nat.add(b3, m3) == Nat.add(budget0, k3) : Nat},
                  {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                         FH.fgroups_total(fg1)))
                   == True{} : Bool}>>, r3)
      +hk3 = Arr.Arr.dpair_l({k3 == FH.fgroups_count(fg2) : Nat},
               Arr.Arr.DPair<
                 {Nat.add(b3, m3) == Nat.add(budget0, k3) : Nat},
                 {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                        FH.fgroups_total(fg1)))
                  == True{} : Bool}>, r4)
      +r5 = Arr.Arr.dpair_r({k3 == FH.fgroups_count(fg2) : Nat},
              Arr.Arr.DPair<
                {Nat.add(b3, m3) == Nat.add(budget0, k3) : Nat},
                {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                       FH.fgroups_total(fg1)))
                 == True{} : Bool}>, r4)
      +hbgt3 = Arr.Arr.dpair_l(
                 {Nat.add(b3, m3) == Nat.add(budget0, k3) : Nat},
                 {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                        FH.fgroups_total(fg1)))
                  == True{} : Bool}, r5)
      +hle3 = Arr.Arr.dpair_r(
                {Nat.add(b3, m3) == Nat.add(budget0, k3) : Nat},
                {Nat.is_le(m3, Nat.add(Groups.len_words(rest),
                                       FH.fgroups_total(fg1)))
                 == True{} : Bool}, r5)
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
      Arr.DPair{hs3, Arr.DPair{et3, Arr.DPair{hwf2, Arr.DPair{hm3,
        Arr.DPair{hk3, Arr.DPair{hbgt3, hle_bound}}}}}}

def FH.hist5_go_ok_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +row: U32, +g: +List<Nat>, +w: +List<Nat>,
    +rest: +List<SolveFast.CWord>, +fg0: +List<SolveFast.FGroup>,
    +gen: Nat, +budget0: Nat, +skip_self: Bool,
    -seen2: Array<Nat>, -tbl0: Array<U32>, -tbl2: Array<U32>,
    +m2: Nat, +k2: Nat, +b2: Nat,
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    +h1: FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl0,
           SolveFast.Hist5Ok{seen2, tbl2, m2, k2, b2}),
    dps: &s2a: Array<Nat> -> &s2b: Array<Nat> ->
         {s2a == seen2 : Array<Nat>} & {s2b == s2a : Array<Nat>},
    dpt: &t2a: Array<U32> -> &t2b: Array<U32> ->
         {t2a == tbl2 : Array<U32>} & {t2b == t2a : Array<U32>},
    rec: @s2: Array<Nat> -> @t2: Array<U32> ->
         @+m2r: Nat -> @+k2r: Nat -> @+b2r: Nat ->
         FT.FT.TblOk(G, C, n_root, t2) ->
         {Nat.add(b2r, m2r) == Nat.add(budget0, k2r) : Nat} ->
         {FH.fgroups_wf(
            SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)))
          == True{} : Bool} ->
         {m2r == FH.fgroups_total(
                   SolveFast.fgroups_next_acc(g, w, fg0,
                     SolveFast.word_eq_fast(g, w))) : Nat} ->
         {k2r == FH.fgroups_count(
                   SolveFast.fgroups_next_acc(g, w, fg0,
                     SolveFast.word_eq_fast(g, w))) : Nat} ->
         FH.SeenTree(10n, 0, s2, gen,
           SolveFast.fgroups_next_acc(g, w, fg0,
             SolveFast.word_eq_fast(g, w))) ->
         FH.HistSpec(g, SolveFast.cwords_words(rest),
           SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)),
           gen, budget0, skip_self, t2,
           SolveFast.hist5_go(row, rest, gen, skip_self,
             SolveFast.Hist5Ok{s2, t2, m2r, k2r, b2r}))) ->
  FH.HistSpec(g, w <> SolveFast.cwords_words(rest), fg0, gen, budget0,
    skip_self, tbl0,
    SolveFast.hist5_go(row, rest, gen, skip_self,
      SolveFast.Hist5Ok{seen2, tbl2, m2, k2, b2})):
  (s2a, dps2) = dps
  (s2b, pes) = dps2
  (+es2a, +es2b) = pes
  (t2a, dpt2) = dpt
  (t2b, pet) = dpt2
  (+et2a, +et2b) = pet
  +fg1 = SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w))
  +hs2 = Arr.Arr.dpair_l(
           FH.SeenTree(10n, 0, seen2, gen, fg1),
           Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
             Arr.Arr.DPair<{FH.fgroups_wf(fg1) == True{} : Bool},
               Arr.Arr.DPair<{m2 == FH.fgroups_total(fg1) : Nat},
                 Arr.Arr.DPair<{k2 == FH.fgroups_count(fg1) : Nat},
                   Arr.Arr.DPair<
                     {Nat.add(b2, m2) == Nat.add(budget0, k2) : Nat},
                     {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
                      == True{} : Bool}>>>>>, h1)
  +r1 = Arr.Arr.dpair_r(
          FH.SeenTree(10n, 0, seen2, gen, fg1),
          Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
            Arr.Arr.DPair<{FH.fgroups_wf(fg1) == True{} : Bool},
              Arr.Arr.DPair<{m2 == FH.fgroups_total(fg1) : Nat},
                Arr.Arr.DPair<{k2 == FH.fgroups_count(fg1) : Nat},
                  Arr.Arr.DPair<
                    {Nat.add(b2, m2) == Nat.add(budget0, k2) : Nat},
                    {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
                     == True{} : Bool}>>>>>, h1)
  +etbl2 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
             Arr.Arr.DPair<{FH.fgroups_wf(fg1) == True{} : Bool},
               Arr.Arr.DPair<{m2 == FH.fgroups_total(fg1) : Nat},
                 Arr.Arr.DPair<{k2 == FH.fgroups_count(fg1) : Nat},
                   Arr.Arr.DPair<
                     {Nat.add(b2, m2) == Nat.add(budget0, k2) : Nat},
                     {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
                      == True{} : Bool}>>>>, r1)
  +r2 = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
          Arr.Arr.DPair<{FH.fgroups_wf(fg1) == True{} : Bool},
            Arr.Arr.DPair<{m2 == FH.fgroups_total(fg1) : Nat},
              Arr.Arr.DPair<{k2 == FH.fgroups_count(fg1) : Nat},
                Arr.Arr.DPair<
                  {Nat.add(b2, m2) == Nat.add(budget0, k2) : Nat},
                  {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
                   == True{} : Bool}>>>>, r1)
  +hwf1 = Arr.Arr.dpair_l({FH.fgroups_wf(fg1) == True{} : Bool},
            Arr.Arr.DPair<{m2 == FH.fgroups_total(fg1) : Nat},
              Arr.Arr.DPair<{k2 == FH.fgroups_count(fg1) : Nat},
                Arr.Arr.DPair<
                  {Nat.add(b2, m2) == Nat.add(budget0, k2) : Nat},
                  {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
                   == True{} : Bool}>>>, r2)
  +r3 = Arr.Arr.dpair_r({FH.fgroups_wf(fg1) == True{} : Bool},
          Arr.Arr.DPair<{m2 == FH.fgroups_total(fg1) : Nat},
            Arr.Arr.DPair<{k2 == FH.fgroups_count(fg1) : Nat},
              Arr.Arr.DPair<
                {Nat.add(b2, m2) == Nat.add(budget0, k2) : Nat},
                {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
                 == True{} : Bool}>>>, r2)
  +hm2 = Arr.Arr.dpair_l({m2 == FH.fgroups_total(fg1) : Nat},
           Arr.Arr.DPair<{k2 == FH.fgroups_count(fg1) : Nat},
             Arr.Arr.DPair<
               {Nat.add(b2, m2) == Nat.add(budget0, k2) : Nat},
               {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
                == True{} : Bool}>>, r3)
  +r4 = Arr.Arr.dpair_r({m2 == FH.fgroups_total(fg1) : Nat},
          Arr.Arr.DPair<{k2 == FH.fgroups_count(fg1) : Nat},
            Arr.Arr.DPair<
              {Nat.add(b2, m2) == Nat.add(budget0, k2) : Nat},
              {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
               == True{} : Bool}>>, r3)
  +hk2 = Arr.Arr.dpair_l({k2 == FH.fgroups_count(fg1) : Nat},
           Arr.Arr.DPair<
             {Nat.add(b2, m2) == Nat.add(budget0, k2) : Nat},
             {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
              == True{} : Bool}>, r4)
  +r5 = Arr.Arr.dpair_r({k2 == FH.fgroups_count(fg1) : Nat},
          Arr.Arr.DPair<
            {Nat.add(b2, m2) == Nat.add(budget0, k2) : Nat},
            {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
             == True{} : Bool}>, r4)
  +hbgt2 = Arr.Arr.dpair_l(
             {Nat.add(b2, m2) == Nat.add(budget0, k2) : Nat},
             {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
              == True{} : Bool}, r5)
  +hle2 = Arr.Arr.dpair_r(
            {Nat.add(b2, m2) == Nat.add(budget0, k2) : Nat},
            {Nat.is_le(m2, Nat.add(1n, FH.fgroups_total(fg0)))
             == True{} : Bool}, r5)
  +es2b_s : {s2b == seen2 : Array<Nat>} =
    Equal.trans(Array<Nat>, s2b, s2a, seen2, es2b, es2a)
  +et2b_2 : {t2b == tbl2 : Array<U32>} =
    Equal.trans(Array<U32>, t2b, t2a, tbl2, et2b, et2a)
  +et2b_0 : {t2b == tbl0 : Array<U32>} =
    Equal.trans(Array<U32>, t2b, tbl2, tbl0, et2b_2, etbl2)
  +hs2b = FH.seen_tree_transport(10n, 0, seen2, s2b, gen, fg1,
            Equal.sym(Array<Nat>, s2b, seen2, es2b_s), hs2)
  +ht2b = FT.FT.tbl_ok_transport(G, C, n_root, tbl0, t2b,
            Equal.sym(Array<U32>, t2b, tbl0, et2b_0), htbl0)
  +hrec_b = rec(s2b, t2b, m2, k2, b2, ht2b, hbgt2, hwf1, hm2, hk2, hs2b)
  +hrec_t0 = FH.hist_spec_transport_tbl(g, SolveFast.cwords_words(rest), fg1,
               gen, budget0, skip_self, t2b, tbl0,
               SolveFast.hist5_go(row, rest, gen, skip_self,
                 SolveFast.Hist5Ok{s2b, t2b, m2, k2, b2}),
               et2b_0, hrec_b)
  +eq_ab : {SolveFast.hist5_go(row, rest, gen, skip_self,
              SolveFast.Hist5Ok{s2b, t2b, m2, k2, b2})
            == SolveFast.hist5_go(row, rest, gen, skip_self,
                 SolveFast.Hist5Ok{s2a, t2a, m2, k2, b2})
            : SolveFast.Hist5Res} =
    Equal.trans(SolveFast.Hist5Res,
      SolveFast.hist5_go(row, rest, gen, skip_self,
        SolveFast.Hist5Ok{s2b, t2b, m2, k2, b2}),
      SolveFast.hist5_go(row, rest, gen, skip_self,
        SolveFast.Hist5Ok{s2a, t2b, m2, k2, b2}),
      SolveFast.hist5_go(row, rest, gen, skip_self,
        SolveFast.Hist5Ok{s2a, t2a, m2, k2, b2}),
      Equal.cong(Array<Nat>, SolveFast.Hist5Res,
        x => SolveFast.hist5_go(row, rest, gen, skip_self,
               SolveFast.Hist5Ok{x, t2b, m2, k2, b2}),
        s2b, s2a, es2b),
      Equal.cong(Array<U32>, SolveFast.Hist5Res,
        y => SolveFast.hist5_go(row, rest, gen, skip_self,
               SolveFast.Hist5Ok{s2a, y, m2, k2, b2}),
        t2b, t2a, et2b))
  +hrec_a = FH.hist_spec_transport(g, SolveFast.cwords_words(rest), fg1, gen,
              budget0, skip_self, tbl0,
              SolveFast.hist5_go(row, rest, gen, skip_self,
                SolveFast.Hist5Ok{s2b, t2b, m2, k2, b2}),
              SolveFast.hist5_go(row, rest, gen, skip_self,
                SolveFast.Hist5Ok{s2a, t2a, m2, k2, b2}),
              eq_ab, hrec_t0)
  %es2a : FH.HistSpec(g, w <> SolveFast.cwords_words(rest), fg0, gen, budget0,
            skip_self, tbl0,
            SolveFast.hist5_go(row, rest, gen, skip_self,
              SolveFast.Hist5Ok{_, tbl2, m2, k2, b2}))
  %et2a : FH.HistSpec(g, w <> SolveFast.cwords_words(rest), fg0, gen, budget0,
            skip_self, tbl0,
            SolveFast.hist5_go(row, rest, gen, skip_self,
              SolveFast.Hist5Ok{s2a, _, m2, k2, b2}))
  FH.hist5_go_lift(g, w, SolveFast.cwords_words(rest), fg0, gen, budget0,
    skip_self, tbl0,
    SolveFast.hist5_go(row, rest, gen, skip_self,
      SolveFast.Hist5Ok{s2a, t2a, m2, k2, b2}),
    NatProof.Nat.is_le_eq_l(Nat.add(1n, FH.fgroups_total(fg0)),
      m2, FH.fgroups_total(fg1), hm2, hle2),
    hrec_a)

def FH.hist5_go_step_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +row: U32, +g: +List<Nat>, +w: +List<Nat>,
    +rest: +List<SolveFast.CWord>, +fg0: +List<SolveFast.FGroup>,
    +gen: Nat, +budget0: Nat, +skip_self: Bool,
    -tbl0: Array<U32>, +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    st1: SolveFast.Hist5Res,
    +h1: FH.HistOneSpec(g, w, fg0, gen, budget0, skip_self, tbl0, st1),
    rec: @s2: Array<Nat> -> @t2: Array<U32> ->
         @+m2: Nat -> @+k2: Nat -> @+b2: Nat ->
         FT.FT.TblOk(G, C, n_root, t2) ->
         {Nat.add(b2, m2) == Nat.add(budget0, k2) : Nat} ->
         {FH.fgroups_wf(
            SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)))
          == True{} : Bool} ->
         {m2 == FH.fgroups_total(
                  SolveFast.fgroups_next_acc(g, w, fg0,
                    SolveFast.word_eq_fast(g, w))) : Nat} ->
         {k2 == FH.fgroups_count(
                  SolveFast.fgroups_next_acc(g, w, fg0,
                    SolveFast.word_eq_fast(g, w))) : Nat} ->
         FH.SeenTree(10n, 0, s2, gen,
           SolveFast.fgroups_next_acc(g, w, fg0,
             SolveFast.word_eq_fast(g, w))) ->
         FH.HistSpec(g, SolveFast.cwords_words(rest),
           SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)),
           gen, budget0, skip_self, t2,
           SolveFast.hist5_go(row, rest, gen, skip_self,
             SolveFast.Hist5Ok{s2, t2, m2, k2, b2}))) ->
  FH.HistSpec(g, w <> SolveFast.cwords_words(rest), fg0, gen, budget0,
    skip_self, tbl0, SolveFast.hist5_go(row, rest, gen, skip_self, st1)):
  match st1:
    case SolveFast.Hist5Pruned{seen2, tbl2}:
      FH.hist5_pruned_rest(row, g, w, rest, fg0, gen, budget0, skip_self,
        seen2, tbl0, tbl2, h1)
    case SolveFast.Hist5Ok{seen2, tbl2, +m2, +k2, +b2}:
      FH.hist5_go_ok_dup(G, C, n_root, row, g, w, rest, fg0, gen, budget0,
        skip_self, seen2, tbl0, tbl2, m2, k2, b2, htbl0, h1,
        Arr.Arr.dup(Nat, seen2), Arr.Arr.dup(U32, tbl2), rec)

def FH.hist5_go_cons_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +row: U32, +g: +List<Nat>,
    +ci: U32, +grow: U32, +w: +List<Nat>, +rest: +List<SolveFast.CWord>,
    +fg0: +List<SolveFast.FGroup>, -seen: Array<Nat>, -tbl: Array<U32>,
    +gen: Nat, +m: Nat, +k: Nat, +budget0: Nat, +budget: Nat, +skip_self: Bool,
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hcw: {FT.FT.cword_ok_b(G, C, n_root, SolveFast.CWord{ci, grow, w})
           == True{} : Bool},
    +hbgt: {Nat.add(budget, m) == Nat.add(budget0, k) : Nat},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg0),
    dps: &s1: Array<Nat> -> &s2: Array<Nat> ->
         {s1 == seen : Array<Nat>} & {s2 == s1 : Array<Nat>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>},
    rec: @s2: Array<Nat> -> @t2: Array<U32> ->
         @+m2: Nat -> @+k2: Nat -> @+b2: Nat ->
         FT.FT.TblOk(G, C, n_root, t2) ->
         {Nat.add(b2, m2) == Nat.add(budget0, k2) : Nat} ->
         {FH.fgroups_wf(
            SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)))
          == True{} : Bool} ->
         {m2 == FH.fgroups_total(
                  SolveFast.fgroups_next_acc(g, w, fg0,
                    SolveFast.word_eq_fast(g, w))) : Nat} ->
         {k2 == FH.fgroups_count(
                  SolveFast.fgroups_next_acc(g, w, fg0,
                    SolveFast.word_eq_fast(g, w))) : Nat} ->
         FH.SeenTree(10n, 0, s2, gen,
           SolveFast.fgroups_next_acc(g, w, fg0,
             SolveFast.word_eq_fast(g, w))) ->
         FH.HistSpec(g, SolveFast.cwords_words(rest),
           SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)),
           gen, budget0, skip_self, t2,
           SolveFast.hist5_go(row, rest, gen, skip_self,
             SolveFast.Hist5Ok{s2, t2, m2, k2, b2}))) ->
  FH.HistSpec(g, w <> SolveFast.cwords_words(rest), fg0, gen, budget0,
    skip_self, tbl,
    SolveFast.hist5_go(row, rest, gen, skip_self,
      SolveFast.hist5_one(row, SolveFast.CWord{ci, grow, w}, seen, tbl, gen, m,
        k, budget, skip_self))):
  (s1, dps2) = dps
  (s2, pes) = dps2
  (+es1, +es2) = pes
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2) = pet
  +cw : SolveFast.CWord = SolveFast.CWord{ci, grow, w}
  +es2_s : {s2 == seen : Array<Nat>} = Equal.trans(Array<Nat>, s2, s1, seen, es2, es1)
  +et2_t : {t2 == tbl : Array<U32>} = Equal.trans(Array<U32>, t2, t1, tbl, et2, et1)
  +hs2 = FH.seen_tree_transport(10n, 0, seen, s2, gen, fg0,
           Equal.sym(Array<Nat>, s2, seen, es2_s), hs)
  +ht2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl, t2,
           Equal.sym(Array<U32>, t2, tbl, et2_t), htbl)
  +h1_s2 = FH.hist5_one_spec(G, C, n_root, row, g, cw, fg0, s2, t2, gen, m, k,
             budget0, budget, skip_self, ht2, hrow, hcw, hbgt, hwf, hm, hk, hs2)
  +h1_t0 = FH.hist_one_transport_tbl(g, w, fg0, gen, budget0, skip_self,
             t2, tbl,
             SolveFast.hist5_one(row, cw, s2, t2, gen, m, k, budget, skip_self),
             et2_t, h1_s2)
  +eq_12 : {SolveFast.hist5_one(row, cw, s2, t2, gen, m, k, budget, skip_self)
            == SolveFast.hist5_one(row, cw, s1, t1, gen, m, k, budget, skip_self)
            : SolveFast.Hist5Res} =
    Equal.trans(SolveFast.Hist5Res,
      SolveFast.hist5_one(row, cw, s2, t2, gen, m, k, budget, skip_self),
      SolveFast.hist5_one(row, cw, s1, t2, gen, m, k, budget, skip_self),
      SolveFast.hist5_one(row, cw, s1, t1, gen, m, k, budget, skip_self),
      Equal.cong(Array<Nat>, SolveFast.Hist5Res,
        x => SolveFast.hist5_one(row, cw, x, t2, gen, m, k, budget, skip_self),
        s2, s1, es2),
      Equal.cong(Array<U32>, SolveFast.Hist5Res,
        y => SolveFast.hist5_one(row, cw, s1, y, gen, m, k, budget, skip_self),
        t2, t1, et2))
  +h1_s1 = FH.hist_one_transport(g, w, fg0, gen, budget0, skip_self, tbl,
             SolveFast.hist5_one(row, cw, s2, t2, gen, m, k, budget, skip_self),
             SolveFast.hist5_one(row, cw, s1, t1, gen, m, k, budget, skip_self),
             eq_12, h1_t0)
  %es1 : FH.HistSpec(g, w <> SolveFast.cwords_words(rest), fg0, gen, budget0,
           skip_self, tbl,
           SolveFast.hist5_go(row, rest, gen, skip_self,
             SolveFast.hist5_one(row, cw, _, tbl, gen, m, k, budget, skip_self)))
  %et1 : FH.HistSpec(g, w <> SolveFast.cwords_words(rest), fg0, gen, budget0,
           skip_self, tbl,
           SolveFast.hist5_go(row, rest, gen, skip_self,
             SolveFast.hist5_one(row, cw, s1, _, gen, m, k, budget, skip_self)))
  FH.hist5_go_step_dup(G, C, n_root, row, g, w, rest, fg0, gen, budget0,
    skip_self, tbl, htbl,
    SolveFast.hist5_one(row, cw, s1, t1, gen, m, k, budget, skip_self),
    h1_s1, rec)

def FH.hist5_go_spec(+S: +List<SolveFast.CWord>, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n_root: Nat, +row: U32, +g: +List<Nat>,
    +fg0: +List<SolveFast.FGroup>, seen: Array<Nat>, tbl: Array<U32>,
    +gen: Nat, +m: Nat, +k: Nat, +budget0: Nat, +budget: Nat, +skip_self: Bool,
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hS: {FT.FT.cwords_ok_b(G, C, n_root, S) == True{} : Bool},
    +hbgt: {Nat.add(budget, m) == Nat.add(budget0, k) : Nat},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hm: {m == FH.fgroups_total(fg0) : Nat},
    +hk: {k == FH.fgroups_count(fg0) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen, fg0)) ->
  FH.HistSpec(g, SolveFast.cwords_words(S), fg0, gen, budget0, skip_self, tbl,
    SolveFast.hist5_go(row, S, gen, skip_self,
      SolveFast.Hist5Ok{seen, tbl, m, k, budget})):
  match S:
    case Nil{}:
      +hle : {Nat.is_le(m, FH.fgroups_total(fg0)) == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(FH.fgroups_total(fg0), FH.fgroups_total(fg0),
          m, Equal.sym(Nat, m, FH.fgroups_total(fg0), hm),
          NatProof.Nat.is_le_refl(FH.fgroups_total(fg0)))
      Arr.DPair{hs, Arr.DPair{{==}, Arr.DPair{hwf,
        Arr.DPair{hm, Arr.DPair{hk, Arr.DPair{hbgt, hle}}}}}}
    case Con{cw, +rest}:
      match cw:
        case SolveFast.CWord{+ci, +grow, +w}:
          +hcw = Logic.Proof.and_true_l(
                   FT.FT.cword_ok_b(G, C, n_root, SolveFast.CWord{ci, grow, w}),
                   FT.FT.cwords_ok_b(G, C, n_root, rest), hS)
          +hrest = Logic.Proof.and_true_r(
                     FT.FT.cword_ok_b(G, C, n_root, SolveFast.CWord{ci, grow, w}),
                     FT.FT.cwords_ok_b(G, C, n_root, rest), hS)
          +fg1 = SolveFast.fgroups_next_acc(g, w, fg0,
                   SolveFast.word_eq_fast(g, w))
          FH.hist5_go_cons_dup(G, C, n_root, row, g, ci, grow, w, rest, fg0,
            seen, tbl, gen, m, k, budget0, budget, skip_self, htbl, hrow, hcw,
            hbgt, hwf, hm, hk, hs, Arr.Arr.dup(Nat, seen),
            Arr.Arr.dup(U32, tbl),
            s2 => t2 => +m2 => +k2 => +b2 => +ht2 => +hbgt2 => +hwf1 =>
            +hm2 => +hk2 => +hs2 =>
              FH.hist5_go_spec(rest, G, C, n_root, row, g, fg1, s2, t2, gen,
                m2, k2, budget0, b2, skip_self, ht2, hrow, hrest, hbgt2, hwf1,
                hm2, hk2, hs2))


# ---------------------------------------------------------------------------
# Symbolic depth-indexed invariant `FH.BktTree` over `+List<SolveFast.CWord>`
# ---------------------------------------------------------------------------

def FH.BktLeaf(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +base: U32, +fg: +List<SolveFast.FGroup>,
    +v: +List<SolveFast.CWord>) -> Data:
  Arr.Arr.DPair<
    {SolveFast.cwords_words(v) == FH.lookup_code(base, fg) : +List<+List<Nat>>},
    {FT.FT.cwords_ok_b(G, C, n_root, v) == True{} : Bool}>

def FH.bkt_leaf_transport_v(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +base: U32, +fg: +List<SolveFast.FGroup>,
    -v1: +List<SolveFast.CWord>, -v2: +List<SolveFast.CWord>,
    +ev: {v1 == v2 : +List<SolveFast.CWord>},
    +hl: FH.BktLeaf(G, C, n_root, base, fg, v1)) ->
  FH.BktLeaf(G, C, n_root, base, fg, v2):
  %ev : FH.BktLeaf(G, C, n_root, base, fg, _)
  hl

def FH.bkt_leaf_transport_c(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +c1: U32, +c2: U32, +fg: +List<SolveFast.FGroup>,
    -v: +List<SolveFast.CWord>, +ec: {c1 == c2 : U32},
    +hl: FH.BktLeaf(G, C, n_root, c1, fg, v)) ->
  FH.BktLeaf(G, C, n_root, c2, fg, v):
  %ec : FH.BktLeaf(G, C, n_root, _, fg, v)
  hl

def FH.BktTree(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +d: Nat, +base: U32, a: Array<+List<SolveFast.CWord>>,
    +fg: +List<SolveFast.FGroup>) -> Data:
  match d:
    case 0n:
      match a:
        case ALeaf{v}:
          FH.BktLeaf(G, C, n_root, base, fg, v)
        case ANode{xs, ys}:
          Empty
    case 1n++p:
      match a:
        case ALeaf{v}:
          Empty
        case ANode{xs, ys}:
          Arr.Arr.DPair<
            FH.BktTree(G, C, n_root, p, base, xs, fg),
            FH.BktTree(G, C, n_root, p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg)>

def FH.bkt_tree_transport(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +d: Nat, +base: U32,
    -a1: Array<+List<SolveFast.CWord>>, -a2: Array<+List<SolveFast.CWord>>,
    +fg: +List<SolveFast.FGroup>,
    +ea: {a1 == a2 : Array<+List<SolveFast.CWord>>},
    +hb: FH.BktTree(G, C, n_root, d, base, a1, fg)) ->
  FH.BktTree(G, C, n_root, d, base, a2, fg):
  %ea : FH.BktTree(G, C, n_root, d, base, _, fg)
  hb

def FH.bkt_tree_transport_fg(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +d: Nat, +base: U32,
    -a: Array<+List<SolveFast.CWord>>,
    +fg1: +List<SolveFast.FGroup>, +fg2: +List<SolveFast.FGroup>,
    +efg: {fg1 == fg2 : +List<SolveFast.FGroup>},
    +hb: FH.BktTree(G, C, n_root, d, base, a, fg1)) ->
  FH.BktTree(G, C, n_root, d, base, a, fg2):
  %efg : FH.BktTree(G, C, n_root, d, base, a, _)
  hb

def FH.bkt_tree_depth(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +d: Nat, +base: U32, a: Array<+List<SolveFast.CWord>>,
    +fg: +List<SolveFast.FGroup>,
    +hb: FH.BktTree(G, C, n_root, d, base, a, fg)) ->
  Arr.Arr.Depth(+List<SolveFast.CWord>, d, a):
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
                   FH.BktTree(G, C, n_root, p, base, xs, fg),
                   FH.BktTree(G, C, n_root, p,
                     U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg), hb)
          +hys = Arr.Arr.dpair_r(
                   FH.BktTree(G, C, n_root, p, base, xs, fg),
                   FH.BktTree(G, C, n_root, p,
                     U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg), hb)
          Arr.DPair{
            FH.bkt_tree_depth(G, C, n_root, p, base, xs, fg, hxs),
            FH.bkt_tree_depth(G, C, n_root, p,
              U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg, hys)}

def FH.bkt_tree_new(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +d: Nat, +base: U32) ->
  FH.BktTree(G, C, n_root, d, base,
    Array.new(+List<SolveFast.CWord>, d, Nil{}), Nil{}):
  match d:
    case 0n:
      Arr.DPair{{==}, {==}}
    case 1n++p:
      Arr.DPair{
        FH.bkt_tree_new(G, C, n_root, p, base),
        FH.bkt_tree_new(G, C, n_root, p, U32.or(base, Arr.Arr.pow2_u32(p)))}

def FH.bkt_get_lo(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    -ys: Array<+List<SolveFast.CWord>>,
    r: Array<+List<SolveFast.CWord>> & +List<SolveFast.CWord>,
    +fg: +List<SolveFast.FGroup>, +c: U32,
    +hr: FH.BktLeaf(G, C, n_root, c, fg,
           Arr.Arr.snd(Array<+List<SolveFast.CWord>>,
             +List<SolveFast.CWord>, r))) ->
  FH.BktLeaf(G, C, n_root, c, fg,
    Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.swap.lo(+List<SolveFast.CWord>, ys, r))):
  (a, +v) = r
  hr

def FH.bkt_get_hi(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    -xs: Array<+List<SolveFast.CWord>>,
    r: Array<+List<SolveFast.CWord>> & +List<SolveFast.CWord>,
    +fg: +List<SolveFast.FGroup>, +c: U32,
    +hr: FH.BktLeaf(G, C, n_root, c, fg,
           Arr.Arr.snd(Array<+List<SolveFast.CWord>>,
             +List<SolveFast.CWord>, r))) ->
  FH.BktLeaf(G, C, n_root, c, fg,
    Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.swap.hi(+List<SolveFast.CWord>, xs, r))):
  (a, +v) = r
  hr

def FH.bkt_tree_get_go_lo(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +p: Nat, +base: U32,
    -xs: Array<+List<SolveFast.CWord>>, -ys: Array<+List<SolveFast.CWord>>,
    +fg: +List<SolveFast.FGroup>, +i: U32,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +hxs: FH.BktTree(G, C, n_root, p, base, xs, fg),
    d: &a1: Array<+List<SolveFast.CWord>> -> &a2: Array<+List<SolveFast.CWord>> ->
       {a1 == xs : Array<+List<SolveFast.CWord>>}
       & {a2 == a1 : Array<+List<SolveFast.CWord>>},
    ih: @xs2: Array<+List<SolveFast.CWord>> ->
        FH.BktTree(G, C, n_root, p, base, xs2, fg) ->
        FH.BktLeaf(G, C, n_root, U32.or(base, i), fg,
          Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            Array.get.go(+List<SolveFast.CWord>, xs2, Arr.Arr.pow2_u32(p), i,
              U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))))) ->
  FH.BktLeaf(G, C, n_root, U32.or(base, i), fg,
    Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.get.go(+List<SolveFast.CWord>, ANode{xs, ys},
        Arr.Arr.pow2_u32(1n+p), i, True{}))):
  (xs1, d2) = d
  (xs2, pe) = d2
  (+ex1, +ex2) = pe
  +hxs2 = FH.bkt_tree_transport(G, C, n_root, p, base, xs, xs2, fg,
            Equal.sym(Array<+List<SolveFast.CWord>>, xs2, xs,
              Equal.trans(Array<+List<SolveFast.CWord>>, xs2, xs1, xs, ex2, ex1)),
            hxs)
  +h2 = ih(xs2, hxs2)
  +h1 = FH.bkt_leaf_transport_v(G, C, n_root, U32.or(base, i), fg,
          Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            Array.get.go(+List<SolveFast.CWord>, xs2, Arr.Arr.pow2_u32(p), i,
              U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
          Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            Array.get.go(+List<SolveFast.CWord>, xs1, Arr.Arr.pow2_u32(p), i,
              U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
          Equal.cong(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            x => Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                   Array.get.go(+List<SolveFast.CWord>, x, Arr.Arr.pow2_u32(p), i,
                     U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
            xs2, xs1, ex2), h2)
  %ex1 : FH.BktLeaf(G, C, n_root, U32.or(base, i), fg,
           Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
             Array.get.go(+List<SolveFast.CWord>, ANode{_, ys},
               Arr.Arr.pow2_u32(1n+p), i, True{})))
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    FH.BktLeaf(G, C, n_root, U32.or(base, i), fg,
      Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.swap.lo(+List<SolveFast.CWord>, ys,
          Array.get.go(+List<SolveFast.CWord>, xs1, _, i,
            U32.is_lt(i, U32.shr(_))))))
  FH.bkt_get_lo(G, C, n_root, ys,
    Array.get.go(+List<SolveFast.CWord>, xs1, Arr.Arr.pow2_u32(p), i,
      U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))),
    fg, U32.or(base, i), h1)

def FH.bkt_tree_get_go_hi(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +p: Nat, +base: U32,
    -xs: Array<+List<SolveFast.CWord>>, -ys: Array<+List<SolveFast.CWord>>,
    +fg: +List<SolveFast.FGroup>, +i: U32,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +eb2: {U32.or(U32.or(base, Arr.Arr.pow2_u32(p)),
                  U32.sub(i, Arr.Arr.pow2_u32(p))) == U32.or(base, i) : U32},
    +hys: FH.BktTree(G, C, n_root, p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg),
    d: &a1: Array<+List<SolveFast.CWord>> -> &a2: Array<+List<SolveFast.CWord>> ->
       {a1 == ys : Array<+List<SolveFast.CWord>>}
       & {a2 == a1 : Array<+List<SolveFast.CWord>>},
    ih: @ys2: Array<+List<SolveFast.CWord>> ->
        FH.BktTree(G, C, n_root, p, U32.or(base, Arr.Arr.pow2_u32(p)), ys2, fg) ->
        FH.BktLeaf(G, C, n_root,
          U32.or(U32.or(base, Arr.Arr.pow2_u32(p)),
                 U32.sub(i, Arr.Arr.pow2_u32(p))), fg,
          Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            Array.get.go(+List<SolveFast.CWord>, ys2, Arr.Arr.pow2_u32(p),
              U32.sub(i, Arr.Arr.pow2_u32(p)),
              U32.is_lt(U32.sub(i, Arr.Arr.pow2_u32(p)),
                U32.shr(Arr.Arr.pow2_u32(p))))))) ->
  FH.BktLeaf(G, C, n_root, U32.or(base, i), fg,
    Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.get.go(+List<SolveFast.CWord>, ANode{xs, ys},
        Arr.Arr.pow2_u32(1n+p), i, False{}))):
  (ys1, d2) = d
  (ys2, pe) = d2
  (+ey1, +ey2) = pe
  +base2 = U32.or(base, Arr.Arr.pow2_u32(p))
  +ip = U32.sub(i, Arr.Arr.pow2_u32(p))
  +hys2 = FH.bkt_tree_transport(G, C, n_root, p, base2, ys, ys2, fg,
            Equal.sym(Array<+List<SolveFast.CWord>>, ys2, ys,
              Equal.trans(Array<+List<SolveFast.CWord>>, ys2, ys1, ys, ey2, ey1)),
            hys)
  +h2 = ih(ys2, hys2)
  +h2c = FH.bkt_leaf_transport_c(G, C, n_root, U32.or(base2, ip),
           U32.or(base, i), fg,
           Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
             Array.get.go(+List<SolveFast.CWord>, ys2, Arr.Arr.pow2_u32(p), ip,
               U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))), eb2, h2)
  +h1 = FH.bkt_leaf_transport_v(G, C, n_root, U32.or(base, i), fg,
          Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            Array.get.go(+List<SolveFast.CWord>, ys2, Arr.Arr.pow2_u32(p), ip,
              U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
          Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            Array.get.go(+List<SolveFast.CWord>, ys1, Arr.Arr.pow2_u32(p), ip,
              U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
          Equal.cong(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            y => Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                   Array.get.go(+List<SolveFast.CWord>, y, Arr.Arr.pow2_u32(p),
                     ip, U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
            ys2, ys1, ey2), h2c)
  %ey1 : FH.BktLeaf(G, C, n_root, U32.or(base, i), fg,
           Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
             Array.get.go(+List<SolveFast.CWord>, ANode{xs, _},
               Arr.Arr.pow2_u32(1n+p), i, False{})))
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    FH.BktLeaf(G, C, n_root, U32.or(base, i), fg,
      Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.swap.hi(+List<SolveFast.CWord>, xs,
          Array.get.go(+List<SolveFast.CWord>, ys1, _, U32.sub(i, _),
            U32.is_lt(U32.sub(i, _), U32.shr(_))))))
  FH.bkt_get_hi(G, C, n_root, xs,
    Array.get.go(+List<SolveFast.CWord>, ys1, Arr.Arr.pow2_u32(p), ip,
      U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))),
    fg, U32.or(base, i), h1)

def FH.bkt_tree_get_go(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +d: Nat, +base: U32, a: Array<+List<SolveFast.CWord>>,
    +fg: +List<SolveFast.FGroup>, +i: U32, z: Bool,
    +ez: {z == U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(d))) : Bool},
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.Arr.u32_zero_from(d, i) == True{} : Bool},
    +hb: FH.BktTree(G, C, n_root, d, base, a, fg)) ->
  FH.BktLeaf(G, C, n_root, U32.or(base, i), fg,
    Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.get.go(+List<SolveFast.CWord>, a, Arr.Arr.pow2_u32(d), i, z))):
  match d:
    case 0n:
      match a:
        case ALeaf{+v}:
          +ei0 : {i == 0 : U32} = Arr.Arr.u32_eq_zero(i, zi)
          +eor : {U32.or(base, i) == base : U32} =
            Equal.trans(U32, U32.or(base, i), U32.or(base, 0), base,
              Equal.cong(U32, U32, x => U32.or(base, x), i, 0, ei0),
              FF5.FF5.u32_or_zero_r(base))
          FH.bkt_leaf_transport_c(G, C, n_root, base, U32.or(base, i), fg, v,
            Equal.sym(U32, U32.or(base, i), base, eor), hb)
        case ANode{xs, ys}:
          Empty.absurd(
            FH.BktLeaf(G, C, n_root, U32.or(base, i), fg,
              Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                Array.get.go(+List<SolveFast.CWord>, ANode{xs, ys},
                  Arr.Arr.pow2_u32(0n), i, z))), hb)
    case 1n++p:
      match a:
        case ALeaf{v}:
          Empty.absurd(
            FH.BktLeaf(G, C, n_root, U32.or(base, i), fg,
              Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                Array.get.go(+List<SolveFast.CWord>, ALeaf{v},
                  Arr.Arr.pow2_u32(1n+p), i, z))), hb)
        case ANode{xs, ys}:
          match z:
            case True{}:
              +hxs = Arr.Arr.dpair_l(
                       FH.BktTree(G, C, n_root, p, base, xs, fg),
                       FH.BktTree(G, C, n_root, p,
                         U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg), hb)
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
                  U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))), True{},
                  Equal.cong(U32, Bool, x => U32.is_lt(i, x),
                    Arr.Arr.pow2_u32(p), U32.shr(Arr.Arr.pow2_u32(1n+p)),
                    Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)),
                      Arr.Arr.pow2_u32(p), eshr)),
                  Equal.sym(Bool, True{},
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))), ez))
              +zip : {Arr.Arr.u32_zero_from(p, i) == True{} : Bool} =
                Arr.Arr.u32_zero_from_lt(p, i, zi, plt, ilt)
              FH.bkt_tree_get_go_lo(G, C, n_root, p, base, xs, ys, fg, i, eshr,
                hxs, Arr.Arr.dup(+List<SolveFast.CWord>, xs),
                xs2 => hxs2 =>
                  FH.bkt_tree_get_go(G, C, n_root, p, base, xs2, fg, i,
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, hxs2))
            case False{}:
              +hys = Arr.Arr.dpair_r(
                       FH.BktTree(G, C, n_root, p, base, xs, fg),
                       FH.BktTree(G, C, n_root, p,
                         U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg), hb)
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
                  U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))), False{},
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
              FH.bkt_tree_get_go_hi(G, C, n_root, p, base, xs, ys, fg, i, eshr,
                eb2, hys, Arr.Arr.dup(+List<SolveFast.CWord>, ys),
                ys2 => hys2 =>
                  FH.bkt_tree_get_go(G, C, n_root, p,
                    U32.or(base, Arr.Arr.pow2_u32(p)), ys2, fg, ip,
                    U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, hys2))

def FH.bkt_tree_get_dup2(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, -bkts: Array<+List<SolveFast.CWord>>,
    a1: Array<+List<SolveFast.CWord>>, +fg: +List<SolveFast.FGroup>, +code: U32,
    +ea1: {a1 == bkts : Array<+List<SolveFast.CWord>>},
    -a2: Array<+List<SolveFast.CWord>>,
    +ea2: {a2 == a1 : Array<+List<SolveFast.CWord>>},
    dp2: &b1: Array<+List<SolveFast.CWord>> -> &b2: Array<+List<SolveFast.CWord>> ->
         {b1 == a2 : Array<+List<SolveFast.CWord>>}
         & {b2 == b1 : Array<+List<SolveFast.CWord>>},
    +zc: {Arr.Arr.u32_zero_from(10n, code) == True{} : Bool},
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, fg)) ->
  FH.BktLeaf(G, C, n_root, code, fg,
    Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.get(+List<SolveFast.CWord>, bkts, code))):
  (b1, dp3) = dp2
  (b2, pe2) = dp3
  (+eb1, +eb2) = pe2
  +ea_b1 : {b1 == a1 : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, b1, a2, a1, eb1, ea2)
  +ea_b2 : {b2 == a1 : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, b2, b1, a1, eb2, ea_b1)
  +hb1 = FH.bkt_tree_transport(G, C, n_root, 10n, 0, bkts, a1, fg,
           Equal.sym(Array<+List<SolveFast.CWord>>, a1, bkts, ea1), hb)
  +hb_b1 = FH.bkt_tree_transport(G, C, n_root, 10n, 0, a1, b1, fg,
             Equal.sym(Array<+List<SolveFast.CWord>>, b1, a1, ea_b1), hb1)
  +hd_b1 = FH.bkt_tree_depth(G, C, n_root, 10n, 0, b1, fg, hb_b1)
  +hd_b2 = Arr.Arr.depth_transport(+List<SolveFast.CWord>, 10n, b1, b2,
             Equal.sym(Array<+List<SolveFast.CWord>>, b2, b1, eb2), hd_b1)
  +em : {U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)) == code : U32} =
    Arr.Arr.u32_and_mask(10n, code, zc)
  +eg : {Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
           Array.get(+List<SolveFast.CWord>, b2, code))
         == Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
              Array.get.go(+List<SolveFast.CWord>, b2, Arr.Arr.pow2_u32(10n),
                code, U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))
         : +List<SolveFast.CWord>} =
    Equal.trans(+List<SolveFast.CWord>,
      Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.get(+List<SolveFast.CWord>, b2, code)),
      Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.get.go(+List<SolveFast.CWord>, b2, Arr.Arr.pow2_u32(10n),
          U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)),
          U32.is_lt(U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)),
            U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.get.go(+List<SolveFast.CWord>, b2, Arr.Arr.pow2_u32(10n), code,
          U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.get_depth(+List<SolveFast.CWord>, 10n, b2, code, hd_b2),
      Equal.cong(U32, +List<SolveFast.CWord>,
        j => Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
               Array.get.go(+List<SolveFast.CWord>, b2, Arr.Arr.pow2_u32(10n), j,
                 U32.is_lt(j, U32.shr(Arr.Arr.pow2_u32(10n))))),
        U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)), code, em))
  +ego = FH.bkt_tree_get_go(G, C, n_root, 10n, 0, a1, fg, code,
           U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))), {==}, {==}, zc,
           hb1)
  +ego_c = FH.bkt_leaf_transport_c(G, C, n_root, U32.or(0, code), code, fg,
             Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
               Array.get.go(+List<SolveFast.CWord>, a1, Arr.Arr.pow2_u32(10n),
                 code, U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
             FF5.FF5.u32_or_zero_l(code), ego)
  +ev : {Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
           Array.get.go(+List<SolveFast.CWord>, a1, Arr.Arr.pow2_u32(10n),
             code, U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))
         == Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
              Array.get(+List<SolveFast.CWord>, b2, code))
         : +List<SolveFast.CWord>} =
    Equal.sym(+List<SolveFast.CWord>,
      Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.get(+List<SolveFast.CWord>, b2, code)),
      Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.get.go(+List<SolveFast.CWord>, a1, Arr.Arr.pow2_u32(10n), code,
          U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      Equal.trans(+List<SolveFast.CWord>,
        Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
          Array.get(+List<SolveFast.CWord>, b2, code)),
        Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
          Array.get.go(+List<SolveFast.CWord>, b2, Arr.Arr.pow2_u32(10n), code,
            U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
        Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
          Array.get.go(+List<SolveFast.CWord>, a1, Arr.Arr.pow2_u32(10n), code,
            U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
        eg,
        Equal.cong(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
          x => Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                 Array.get.go(+List<SolveFast.CWord>, x, Arr.Arr.pow2_u32(10n),
                   code, U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
          b2, a1, ea_b2)))
  %ea1 : FH.BktLeaf(G, C, n_root, code, fg,
           Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
             Array.get(+List<SolveFast.CWord>, _, code)))
  %ea_b2 : FH.BktLeaf(G, C, n_root, code, fg,
             Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
               Array.get(+List<SolveFast.CWord>, _, code)))
  FH.bkt_leaf_transport_v(G, C, n_root, code, fg,
    Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.get.go(+List<SolveFast.CWord>, a1, Arr.Arr.pow2_u32(10n), code,
        U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
    Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.get(+List<SolveFast.CWord>, b2, code)), ev, ego_c)

def FH.bkt_tree_get_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, -bkts: Array<+List<SolveFast.CWord>>,
    +fg: +List<SolveFast.FGroup>, +code: U32,
    +zc: {Arr.Arr.u32_zero_from(10n, code) == True{} : Bool},
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, fg),
    dp: &a1: Array<+List<SolveFast.CWord>> -> &a2: Array<+List<SolveFast.CWord>> ->
        {a1 == bkts : Array<+List<SolveFast.CWord>>}
        & {a2 == a1 : Array<+List<SolveFast.CWord>>}) ->
  FH.BktLeaf(G, C, n_root, code, fg,
    Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.get(+List<SolveFast.CWord>, bkts, code))):
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  FH.bkt_tree_get_dup2(G, C, n_root, bkts, a1, fg, code, ea1, a2, ea2,
    Arr.Arr.dup(+List<SolveFast.CWord>, a2), zc, hb)

def FH.bkt_tree_get(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    bkts: Array<+List<SolveFast.CWord>>, +fg: +List<SolveFast.FGroup>, +code: U32,
    +zc: {Arr.Arr.u32_zero_from(10n, code) == True{} : Bool},
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, fg)) ->
  FH.BktLeaf(G, C, n_root, code, fg,
    Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.get(+List<SolveFast.CWord>, bkts, code))):
  FH.bkt_tree_get_dup(G, C, n_root, bkts, fg, code, zc, hb,
    Arr.Arr.dup(+List<SolveFast.CWord>, bkts))

type FH.BktOp is Data:
  OpAdd{cw: SolveFast.CWord, fb: +List<Feedback.Color>,
        old: +List<SolveFast.CWord>}
  OpClear{gp: SolveFast.FGroup}

def FH.bkt_op_code(op: FH.BktOp) -> U32:
  match op:
    case OpAdd{cw, fb, old}:
      FF5.FF5.encode_fb5_list(fb)
    case OpClear{gp}:
      match gp:
        case SolveFast.FGroup{f, len, rws}:
          FF5.FF5.encode_fb5_list(f)

def FH.bkt_op_src(op: FH.BktOp, +fg: +List<SolveFast.FGroup>) ->
  +List<SolveFast.FGroup>:
  match op:
    case OpAdd{cw, fb, old}:
      fg
    case OpClear{gp}:
      List.append(&2, SolveFast.FGroup, fg, gp <> Nil{})

def FH.bkt_op_dst(op: FH.BktOp, +fg: +List<SolveFast.FGroup>) ->
  +List<SolveFast.FGroup>:
  match op:
    case OpAdd{cw, fb, old}:
      SolveFast.fgroup_add_fast(SolveFast.cword_w(cw), fb, fg)
    case OpClear{gp}:
      fg

def FH.bkt_op_val(op: FH.BktOp) -> +List<SolveFast.CWord>:
  match op:
    case OpAdd{cw, fb, old}:
      cw <> old
    case OpClear{gp}:
      Nil{}

def FH.BktOpOk(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    op: FH.BktOp, +fg: +List<SolveFast.FGroup>) -> Data:
  match op:
    case OpAdd{+cw, +fb, +old}:
      Arr.Arr.DPair<
        {FF5.FF5.is_fb5(fb) == True{} : Bool},
        Arr.Arr.DPair<
          {FH.fgroups_wf(fg) == True{} : Bool},
          Arr.Arr.DPair<
            {FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
            FH.BktLeaf(G, C, n_root, FF5.FF5.encode_fb5_list(fb), fg, old)>>>
    case OpClear{gp}:
      match gp:
        case SolveFast.FGroup{+f, len, rws}:
          Arr.Arr.DPair<
            {FF5.FF5.is_fb5(f) == True{} : Bool},
            {FH.has_code(FF5.FF5.encode_fb5_list(f), fg) == False{} : Bool}>

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
            FH.lookup_code(c, rest), Nil{},
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

def FH.add_facts_lkp_self(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +fg: +List<SolveFast.FGroup>, +fg2: +List<SolveFast.FGroup>,
    f: FH.AddFacts<w, fb, fg, fg2>) ->
  {FH.lookup_code(FF5.FF5.encode_fb5_list(fb), fg2)
   == w <> FH.lookup_code(FF5.FF5.encode_fb5_list(fb), fg)
   : +List<+List<Nat>>}:
  match f:
    case AddFacts{wf2, tot2, cnt2, has_self, lkp_self}:
      lkp_self

def FH.bkt_op_other(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +op: FH.BktOp, +fg: +List<SolveFast.FGroup>, +j: U32,
    +hok: FH.BktOpOk(G, C, n_root, op, fg),
    +hne: {U32.is_eq(j, FH.bkt_op_code(op)) == False{} : Bool}) ->
  {FH.lookup_code(j, FH.bkt_op_dst(op, fg))
   == FH.lookup_code(j, FH.bkt_op_src(op, fg)) : +List<+List<Nat>>}:
  match op:
    case OpAdd{+cw, +fb, +old}:
      +hfb = Arr.Arr.dpair_l({FF5.FF5.is_fb5(fb) == True{} : Bool},
               Arr.Arr.DPair<{FH.fgroups_wf(fg) == True{} : Bool},
                 Arr.Arr.DPair<{FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
                   FH.BktLeaf(G, C, n_root, FF5.FF5.encode_fb5_list(fb), fg, old)>>,
               hok)
      +r1 = Arr.Arr.dpair_r({FF5.FF5.is_fb5(fb) == True{} : Bool},
              Arr.Arr.DPair<{FH.fgroups_wf(fg) == True{} : Bool},
                Arr.Arr.DPair<{FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
                  FH.BktLeaf(G, C, n_root, FF5.FF5.encode_fb5_list(fb), fg, old)>>,
              hok)
      +hwf = Arr.Arr.dpair_l({FH.fgroups_wf(fg) == True{} : Bool},
               Arr.Arr.DPair<{FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
                 FH.BktLeaf(G, C, n_root, FF5.FF5.encode_fb5_list(fb), fg, old)>,
               r1)
      FH.fgroup_add_lookup_other(SolveFast.cword_w(cw), fb, fg,
        SolveFast.next_fgroup_hit(fb, fg), j, {==}, hfb, hwf, hne)
    case OpClear{+gp}:
      Equal.sym(+List<+List<Nat>>,
        FH.lookup_code(j, List.append(&2, SolveFast.FGroup, fg, gp <> Nil{})),
        FH.lookup_code(j, fg),
        FH.lookup_append_other(j, fg, gp, hne))

def FH.bkt_op_self(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +op: FH.BktOp, +fg: +List<SolveFast.FGroup>,
    +hok: FH.BktOpOk(G, C, n_root, op, fg)) ->
  FH.BktLeaf(G, C, n_root, FH.bkt_op_code(op), FH.bkt_op_dst(op, fg),
    FH.bkt_op_val(op)):
  match op:
    case OpAdd{+cw, +fb, +old}:
      +c = FF5.FF5.encode_fb5_list(fb)
      +hfb = Arr.Arr.dpair_l({FF5.FF5.is_fb5(fb) == True{} : Bool},
               Arr.Arr.DPair<{FH.fgroups_wf(fg) == True{} : Bool},
                 Arr.Arr.DPair<{FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
                   FH.BktLeaf(G, C, n_root, c, fg, old)>>, hok)
      +r1 = Arr.Arr.dpair_r({FF5.FF5.is_fb5(fb) == True{} : Bool},
              Arr.Arr.DPair<{FH.fgroups_wf(fg) == True{} : Bool},
                Arr.Arr.DPair<{FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
                  FH.BktLeaf(G, C, n_root, c, fg, old)>>, hok)
      +hwf = Arr.Arr.dpair_l({FH.fgroups_wf(fg) == True{} : Bool},
               Arr.Arr.DPair<{FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
                 FH.BktLeaf(G, C, n_root, c, fg, old)>, r1)
      +r2 = Arr.Arr.dpair_r({FH.fgroups_wf(fg) == True{} : Bool},
              Arr.Arr.DPair<{FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
                FH.BktLeaf(G, C, n_root, c, fg, old)>, r1)
      +hcw = Arr.Arr.dpair_l({FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
               FH.BktLeaf(G, C, n_root, c, fg, old), r2)
      +hold = Arr.Arr.dpair_r({FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
                FH.BktLeaf(G, C, n_root, c, fg, old), r2)
      +ewold = Arr.Arr.dpair_l(
                 {SolveFast.cwords_words(old) == FH.lookup_code(c, fg)
                  : +List<+List<Nat>>},
                 {FT.FT.cwords_ok_b(G, C, n_root, old) == True{} : Bool}, hold)
      +hok_old = Arr.Arr.dpair_r(
                   {SolveFast.cwords_words(old) == FH.lookup_code(c, fg)
                    : +List<+List<Nat>>},
                   {FT.FT.cwords_ok_b(G, C, n_root, old) == True{} : Bool}, hold)
      +w = SolveFast.cword_w(cw)
      +ew : {SolveFast.cwords_words(cw <> old)
             == FH.lookup_code(c, SolveFast.fgroup_add_fast(w, fb, fg))
             : +List<+List<Nat>>} =
        Equal.trans(+List<+List<Nat>>,
          SolveFast.cwords_words(cw <> old),
          w <> FH.lookup_code(c, fg),
          FH.lookup_code(c, SolveFast.fgroup_add_fast(w, fb, fg)),
          Equal.trans(+List<+List<Nat>>,
            SolveFast.cwords_words(cw <> old),
            w <> SolveFast.cwords_words(old),
            w <> FH.lookup_code(c, fg),
            FH.cwords_words_cons(cw, old),
            Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>, l => w <> l,
              SolveFast.cwords_words(old), FH.lookup_code(c, fg), ewold)),
          Equal.sym(+List<+List<Nat>>,
            FH.lookup_code(c, SolveFast.fgroup_add_fast(w, fb, fg)),
            w <> FH.lookup_code(c, fg),
            FH.add_facts_lkp_self(w, fb, fg,
              SolveFast.fgroup_add_fast(w, fb, fg),
              FH.fgroup_add_facts(w, fb, fg,
                SolveFast.next_fgroup_hit(fb, fg), {==}, hfb, hwf))))
      Arr.DPair{ew,
        FH.bool_and_intro(FT.FT.cword_ok_b(G, C, n_root, cw),
          FT.FT.cwords_ok_b(G, C, n_root, old), hcw, hok_old)}
    case OpClear{+gp}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          +c = FF5.FF5.encode_fb5_list(f)
          +hnh = Arr.Arr.dpair_r({FF5.FF5.is_fb5(f) == True{} : Bool},
                   {FH.has_code(c, fg) == False{} : Bool}, hok)
          Arr.DPair{
            Equal.sym(+List<+List<Nat>>, FH.lookup_code(c, fg), Nil{},
              FH.lookup_nil_of_not_has(c, fg, hnh)),
            {==}}

def FH.bkt_op_zero_from(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +op: FH.BktOp, +fg: +List<SolveFast.FGroup>,
    +hok: FH.BktOpOk(G, C, n_root, op, fg)) ->
  {Arr.Arr.u32_zero_from(10n, FH.bkt_op_code(op)) == True{} : Bool}:
  match op:
    case OpAdd{+cw, +fb, +old}:
      FF5.FF5.encode_fb5_list_zero_from(fb,
        Arr.Arr.dpair_l({FF5.FF5.is_fb5(fb) == True{} : Bool},
          Arr.Arr.DPair<{FH.fgroups_wf(fg) == True{} : Bool},
            Arr.Arr.DPair<{FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
              FH.BktLeaf(G, C, n_root, FF5.FF5.encode_fb5_list(fb), fg, old)>>,
          hok))
    case OpClear{+gp}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          FF5.FF5.encode_fb5_list_zero_from(f,
            Arr.Arr.dpair_l({FF5.FF5.is_fb5(f) == True{} : Bool},
              {FH.has_code(FF5.FF5.encode_fb5_list(f), fg) == False{} : Bool},
              hok))

def FH.bkt_tree_other(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +d: Nat, +base: U32, a: Array<+List<SolveFast.CWord>>,
    +op: FH.BktOp, +fg: +List<SolveFast.FGroup>, +k: Nat, +bval: Bool,
    +hok: FH.BktOpOk(G, C, n_root, op, fg),
    +hle: {Nat.is_le(d, k) == True{} : Bool},
    +hbb: {FH.u32_bit(k, base) == bval : Bool},
    +hbc: {FH.u32_bit(k, FH.bkt_op_code(op)) == Bool.not(bval) : Bool},
    +hb: FH.BktTree(G, C, n_root, d, base, a, FH.bkt_op_src(op, fg))) ->
  FH.BktTree(G, C, n_root, d, base, a, FH.bkt_op_dst(op, fg)):
  match d:
    case 0n:
      match a:
        case ALeaf{+v}:
          +hne : {U32.is_eq(base, FH.bkt_op_code(op)) == False{} : Bool} =
            FH.u32_ne_of_bit_val(k, base, FH.bkt_op_code(op), bval, hbb, hbc)
          +ew = Arr.Arr.dpair_l(
                  {SolveFast.cwords_words(v)
                   == FH.lookup_code(base, FH.bkt_op_src(op, fg))
                   : +List<+List<Nat>>},
                  {FT.FT.cwords_ok_b(G, C, n_root, v) == True{} : Bool}, hb)
          +hcw = Arr.Arr.dpair_r(
                   {SolveFast.cwords_words(v)
                    == FH.lookup_code(base, FH.bkt_op_src(op, fg))
                    : +List<+List<Nat>>},
                   {FT.FT.cwords_ok_b(G, C, n_root, v) == True{} : Bool}, hb)
          Arr.DPair{
            Equal.trans(+List<+List<Nat>>,
              SolveFast.cwords_words(v),
              FH.lookup_code(base, FH.bkt_op_src(op, fg)),
              FH.lookup_code(base, FH.bkt_op_dst(op, fg)), ew,
              Equal.sym(+List<+List<Nat>>,
                FH.lookup_code(base, FH.bkt_op_dst(op, fg)),
                FH.lookup_code(base, FH.bkt_op_src(op, fg)),
                FH.bkt_op_other(G, C, n_root, op, fg, base, hok, hne))),
            hcw}
        case ANode{xs, ys}:
          hb
    case 1n++p:
      match a:
        case ALeaf{v}:
          hb
        case ANode{xs, ys}:
          +src = FH.bkt_op_src(op, fg)
          +hxs = Arr.Arr.dpair_l(
                   FH.BktTree(G, C, n_root, p, base, xs, src),
                   FH.BktTree(G, C, n_root, p,
                     U32.or(base, Arr.Arr.pow2_u32(p)), ys, src), hb)
          +hys = Arr.Arr.dpair_r(
                   FH.BktTree(G, C, n_root, p, base, xs, src),
                   FH.BktTree(G, C, n_root, p,
                     U32.or(base, Arr.Arr.pow2_u32(p)), ys, src), hb)
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
            FH.bkt_tree_other(G, C, n_root, p, base, xs, op, fg, k, bval,
              hok, hple, hbb, hbc, hxs),
            FH.bkt_tree_other(G, C, n_root, p,
              U32.or(base, Arr.Arr.pow2_u32(p)), ys, op, fg, k, bval,
              hok, hple, hbb2, hbc, hys)}

def FH.bkt_swap_lo(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +p: Nat, +base: U32, -ys: Array<+List<SolveFast.CWord>>,
    r: Array<+List<SolveFast.CWord>> & +List<SolveFast.CWord>,
    +fg2: +List<SolveFast.FGroup>,
    +hr: FH.BktTree(G, C, n_root, p, base,
           Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>, r),
           fg2),
    +hy: FH.BktTree(G, C, n_root, p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg2)) ->
  FH.BktTree(G, C, n_root, 1n+p, base,
    Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.swap.lo(+List<SolveFast.CWord>, ys, r)), fg2):
  (a2, res) = r
  Arr.DPair{hr, hy}

def FH.bkt_swap_hi(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +p: Nat, +base: U32, -xs: Array<+List<SolveFast.CWord>>,
    r: Array<+List<SolveFast.CWord>> & +List<SolveFast.CWord>,
    +fg2: +List<SolveFast.FGroup>,
    +hx: FH.BktTree(G, C, n_root, p, base, xs, fg2),
    +hr: FH.BktTree(G, C, n_root, p, U32.or(base, Arr.Arr.pow2_u32(p)),
           Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>, r),
           fg2)) ->
  FH.BktTree(G, C, n_root, 1n+p, base,
    Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.swap.hi(+List<SolveFast.CWord>, xs, r)), fg2):
  (a2, res) = r
  Arr.DPair{hx, hr}

def FH.bkt_tree_swap_go_lo(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +p: Nat, +base: U32,
    -xs: Array<+List<SolveFast.CWord>>, -ys: Array<+List<SolveFast.CWord>>,
    +fg1: +List<SolveFast.FGroup>, +fg2: +List<SolveFast.FGroup>,
    +i: U32, +v: +List<SolveFast.CWord>,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +hxs: FH.BktTree(G, C, n_root, p, base, xs, fg1),
    +hys2: FH.BktTree(G, C, n_root, p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg2),
    d: &a1: Array<+List<SolveFast.CWord>> -> &a2: Array<+List<SolveFast.CWord>> ->
       {a1 == xs : Array<+List<SolveFast.CWord>>}
       & {a2 == a1 : Array<+List<SolveFast.CWord>>},
    ih: @xs2: Array<+List<SolveFast.CWord>> ->
        FH.BktTree(G, C, n_root, p, base, xs2, fg1) ->
        FH.BktTree(G, C, n_root, p, base,
          Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            Array.swap.go(+List<SolveFast.CWord>, xs2, Arr.Arr.pow2_u32(p), i,
              v, U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))), fg2)) ->
  FH.BktTree(G, C, n_root, 1n+p, base,
    Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.swap.go(+List<SolveFast.CWord>, ANode{xs, ys},
        Arr.Arr.pow2_u32(1n+p), i, v, True{})), fg2):
  (xs1, d2) = d
  (xs2, pe) = d2
  (+ex1, +ex2) = pe
  +hxs2 = FH.bkt_tree_transport(G, C, n_root, p, base, xs, xs2, fg1,
            Equal.sym(Array<+List<SolveFast.CWord>>, xs2, xs,
              Equal.trans(Array<+List<SolveFast.CWord>>, xs2, xs1, xs, ex2, ex1)),
            hxs)
  +h2 = ih(xs2, hxs2)
  +h1 = FH.bkt_tree_transport(G, C, n_root, p, base,
          Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            Array.swap.go(+List<SolveFast.CWord>, xs2, Arr.Arr.pow2_u32(p), i,
              v, U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
          Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            Array.swap.go(+List<SolveFast.CWord>, xs1, Arr.Arr.pow2_u32(p), i,
              v, U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
          fg2,
          Equal.cong(Array<+List<SolveFast.CWord>>, Array<+List<SolveFast.CWord>>,
            x => Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                   Array.swap.go(+List<SolveFast.CWord>, x, Arr.Arr.pow2_u32(p),
                     i, v, U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
            xs2, xs1, ex2), h2)
  %ex1 : FH.BktTree(G, C, n_root, 1n+p, base,
           Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
             Array.swap.go(+List<SolveFast.CWord>, ANode{_, ys},
               Arr.Arr.pow2_u32(1n+p), i, v, True{})), fg2)
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    FH.BktTree(G, C, n_root, 1n+p, base,
      Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.swap.lo(+List<SolveFast.CWord>, ys,
          Array.swap.go(+List<SolveFast.CWord>, xs1, _, i, v,
            U32.is_lt(i, U32.shr(_))))), fg2)
  FH.bkt_swap_lo(G, C, n_root, p, base, ys,
    Array.swap.go(+List<SolveFast.CWord>, xs1, Arr.Arr.pow2_u32(p), i, v,
      U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))),
    fg2, h1, hys2)

def FH.bkt_tree_swap_go_hi(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +p: Nat, +base: U32,
    -xs: Array<+List<SolveFast.CWord>>, -ys: Array<+List<SolveFast.CWord>>,
    +fg1: +List<SolveFast.FGroup>, +fg2: +List<SolveFast.FGroup>,
    +i: U32, +v: +List<SolveFast.CWord>,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +hxs2: FH.BktTree(G, C, n_root, p, base, xs, fg2),
    +hys: FH.BktTree(G, C, n_root, p, U32.or(base, Arr.Arr.pow2_u32(p)), ys, fg1),
    d: &a1: Array<+List<SolveFast.CWord>> -> &a2: Array<+List<SolveFast.CWord>> ->
       {a1 == ys : Array<+List<SolveFast.CWord>>}
       & {a2 == a1 : Array<+List<SolveFast.CWord>>},
    ih: @ys2: Array<+List<SolveFast.CWord>> ->
        FH.BktTree(G, C, n_root, p, U32.or(base, Arr.Arr.pow2_u32(p)), ys2, fg1) ->
        FH.BktTree(G, C, n_root, p, U32.or(base, Arr.Arr.pow2_u32(p)),
          Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            Array.swap.go(+List<SolveFast.CWord>, ys2, Arr.Arr.pow2_u32(p),
              U32.sub(i, Arr.Arr.pow2_u32(p)), v,
              U32.is_lt(U32.sub(i, Arr.Arr.pow2_u32(p)),
                U32.shr(Arr.Arr.pow2_u32(p))))), fg2)) ->
  FH.BktTree(G, C, n_root, 1n+p, base,
    Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.swap.go(+List<SolveFast.CWord>, ANode{xs, ys},
        Arr.Arr.pow2_u32(1n+p), i, v, False{})), fg2):
  (ys1, d2) = d
  (ys2, pe) = d2
  (+ey1, +ey2) = pe
  +base2 = U32.or(base, Arr.Arr.pow2_u32(p))
  +ip = U32.sub(i, Arr.Arr.pow2_u32(p))
  +hys2 = FH.bkt_tree_transport(G, C, n_root, p, base2, ys, ys2, fg1,
            Equal.sym(Array<+List<SolveFast.CWord>>, ys2, ys,
              Equal.trans(Array<+List<SolveFast.CWord>>, ys2, ys1, ys, ey2, ey1)),
            hys)
  +h2 = ih(ys2, hys2)
  +h1 = FH.bkt_tree_transport(G, C, n_root, p, base2,
          Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            Array.swap.go(+List<SolveFast.CWord>, ys2, Arr.Arr.pow2_u32(p), ip,
              v, U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
          Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            Array.swap.go(+List<SolveFast.CWord>, ys1, Arr.Arr.pow2_u32(p), ip,
              v, U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
          fg2,
          Equal.cong(Array<+List<SolveFast.CWord>>, Array<+List<SolveFast.CWord>>,
            y => Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                   Array.swap.go(+List<SolveFast.CWord>, y, Arr.Arr.pow2_u32(p),
                     ip, v, U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
            ys2, ys1, ey2), h2)
  %ey1 : FH.BktTree(G, C, n_root, 1n+p, base,
           Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
             Array.swap.go(+List<SolveFast.CWord>, ANode{xs, _},
               Arr.Arr.pow2_u32(1n+p), i, v, False{})), fg2)
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    FH.BktTree(G, C, n_root, 1n+p, base,
      Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.swap.hi(+List<SolveFast.CWord>, xs,
          Array.swap.go(+List<SolveFast.CWord>, ys1, _, U32.sub(i, _), v,
            U32.is_lt(U32.sub(i, _), U32.shr(_))))), fg2)
  FH.bkt_swap_hi(G, C, n_root, p, base, xs,
    Array.swap.go(+List<SolveFast.CWord>, ys1, Arr.Arr.pow2_u32(p), ip, v,
      U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))),
    fg2, hxs2, h1)

def FH.bkt_tree_swap_go(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +d: Nat, +base: U32, a: Array<+List<SolveFast.CWord>>,
    +op: FH.BktOp, +fg: +List<SolveFast.FGroup>, +i: U32, z: Bool,
    +ez: {z == U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(d))) : Bool},
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.Arr.u32_zero_from(d, i) == True{} : Bool},
    +hbz: {FH.u32_zero_below(d, base) == True{} : Bool},
    +etgt: {U32.or(base, i) == FH.bkt_op_code(op) : U32},
    +hok: FH.BktOpOk(G, C, n_root, op, fg),
    +hb: FH.BktTree(G, C, n_root, d, base, a, FH.bkt_op_src(op, fg))) ->
  FH.BktTree(G, C, n_root, d, base,
    Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.swap.go(+List<SolveFast.CWord>, a, Arr.Arr.pow2_u32(d), i,
        FH.bkt_op_val(op), z)),
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
                  Equal.sym(U32, i, 0, ei0)), etgt))
          FH.bkt_leaf_transport_c(G, C, n_root, FH.bkt_op_code(op), base,
            FH.bkt_op_dst(op, fg), FH.bkt_op_val(op),
            Equal.sym(U32, base, FH.bkt_op_code(op), ebase),
            FH.bkt_op_self(G, C, n_root, op, fg, hok))
        case ANode{xs, ys}:
          Empty.absurd(
            FH.BktTree(G, C, n_root, 0n, base,
              Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                Array.swap.go(+List<SolveFast.CWord>, ANode{xs, ys},
                  Arr.Arr.pow2_u32(0n), i, FH.bkt_op_val(op), z)),
              FH.bkt_op_dst(op, fg)), hb)
    case 1n++p:
      match a:
        case ALeaf{old}:
          Empty.absurd(
            FH.BktTree(G, C, n_root, 1n+p, base,
              Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                Array.swap.go(+List<SolveFast.CWord>, ALeaf{old},
                  Arr.Arr.pow2_u32(1n+p), i, FH.bkt_op_val(op), z)),
              FH.bkt_op_dst(op, fg)), hb)
        case ANode{xs, ys}:
          match z:
            case True{}:
              +src = FH.bkt_op_src(op, fg)
              +hxs = Arr.Arr.dpair_l(
                       FH.BktTree(G, C, n_root, p, base, xs, src),
                       FH.BktTree(G, C, n_root, p,
                         U32.or(base, Arr.Arr.pow2_u32(p)), ys, src), hb)
              +hys = Arr.Arr.dpair_r(
                       FH.BktTree(G, C, n_root, p, base, xs, src),
                       FH.BktTree(G, C, n_root, p,
                         U32.or(base, Arr.Arr.pow2_u32(p)), ys, src), hb)
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
                  U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))), True{},
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
                  FH.u32_bit(p, U32.or(base, i)), False{},
                  Equal.cong(U32, Bool, u => FH.u32_bit(p, u),
                    FH.bkt_op_code(op), U32.or(base, i),
                    Equal.sym(U32, U32.or(base, i), FH.bkt_op_code(op), etgt)),
                  Equal.trans(Bool,
                    FH.u32_bit(p, U32.or(base, i)),
                    Bool.or(FH.u32_bit(p, base), FH.u32_bit(p, i)), False{},
                    FH.u32_bit_or(p, base, i),
                    Equal.trans(Bool,
                      Bool.or(FH.u32_bit(p, base), FH.u32_bit(p, i)),
                      Bool.or(False{}, FH.u32_bit(p, i)), False{},
                      Equal.cong(Bool, Bool, b => Bool.or(b, FH.u32_bit(p, i)),
                        FH.u32_bit(p, base), False{}, hbp_base), hbp_i)))
              +base2 = U32.or(base, Arr.Arr.pow2_u32(p))
              +hys2 = FH.bkt_tree_other(G, C, n_root, p, base2, ys, op, fg, p,
                        True{}, hok, NatProof.Nat.is_le_refl(p),
                        FH.u32_bit_or_pow2_same(p, base, plt), hbp_tgt, hys)
              FH.bkt_tree_swap_go_lo(G, C, n_root, p, base, xs, ys, src,
                FH.bkt_op_dst(op, fg), i, FH.bkt_op_val(op), eshr,
                hxs, hys2, Arr.Arr.dup(+List<SolveFast.CWord>, xs),
                xs2 => hxs2 =>
                  FH.bkt_tree_swap_go(G, C, n_root, p, base, xs2, op, fg, i,
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, hbzp, etgt, hok, hxs2))
            case False{}:
              +src = FH.bkt_op_src(op, fg)
              +hxs = Arr.Arr.dpair_l(
                       FH.BktTree(G, C, n_root, p, base, xs, src),
                       FH.BktTree(G, C, n_root, p,
                         U32.or(base, Arr.Arr.pow2_u32(p)), ys, src), hb)
              +hys = Arr.Arr.dpair_r(
                       FH.BktTree(G, C, n_root, p, base, xs, src),
                       FH.BktTree(G, C, n_root, p,
                         U32.or(base, Arr.Arr.pow2_u32(p)), ys, src), hb)
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
                  U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))), False{},
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
                  FH.u32_bit(p, U32.or(base, i)), True{},
                  Equal.cong(U32, Bool, u => FH.u32_bit(p, u),
                    FH.bkt_op_code(op), U32.or(base, i),
                    Equal.sym(U32, U32.or(base, i), FH.bkt_op_code(op), etgt)),
                  Equal.trans(Bool,
                    FH.u32_bit(p, U32.or(base, i)),
                    Bool.or(FH.u32_bit(p, base), FH.u32_bit(p, i)), True{},
                    FH.u32_bit_or(p, base, i),
                    Equal.trans(Bool,
                      Bool.or(FH.u32_bit(p, base), FH.u32_bit(p, i)),
                      Bool.or(False{}, FH.u32_bit(p, i)), True{},
                      Equal.cong(Bool, Bool, b => Bool.or(b, FH.u32_bit(p, i)),
                        FH.u32_bit(p, base), False{}, hbp_base), hbp_i)))
              +etgt2 : {U32.or(base2, ip) == FH.bkt_op_code(op) : U32} =
                Equal.trans(U32, U32.or(base2, ip), U32.or(base, i),
                  FH.bkt_op_code(op),
                  FH.u32_or_base_sub(p, base, i, zi, plt, ige), etgt)
              +hxs2 = FH.bkt_tree_other(G, C, n_root, p, base, xs, op, fg, p,
                        False{}, hok, NatProof.Nat.is_le_refl(p), hbp_base,
                        hbp_tgt, hxs)
              FH.bkt_tree_swap_go_hi(G, C, n_root, p, base, xs, ys, src,
                FH.bkt_op_dst(op, fg), i, FH.bkt_op_val(op), eshr,
                hxs2, hys, Arr.Arr.dup(+List<SolveFast.CWord>, ys),
                ys2 => hys2 =>
                  FH.bkt_tree_swap_go(G, C, n_root, p, base2, ys2, op, fg, ip,
                    U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, hbz2, etgt2, hok, hys2))

def FH.bkt_tree_swap_dup2(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, -bkts: Array<+List<SolveFast.CWord>>,
    a1: Array<+List<SolveFast.CWord>>, +op: FH.BktOp,
    +fg: +List<SolveFast.FGroup>,
    +ea1: {a1 == bkts : Array<+List<SolveFast.CWord>>},
    -a2: Array<+List<SolveFast.CWord>>,
    +ea2: {a2 == a1 : Array<+List<SolveFast.CWord>>},
    dp2: &b1: Array<+List<SolveFast.CWord>> -> &b2: Array<+List<SolveFast.CWord>> ->
         {b1 == a2 : Array<+List<SolveFast.CWord>>}
         & {b2 == b1 : Array<+List<SolveFast.CWord>>},
    +hok: FH.BktOpOk(G, C, n_root, op, fg),
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, FH.bkt_op_src(op, fg))) ->
  FH.BktTree(G, C, n_root, 10n, 0,
    Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.swap(+List<SolveFast.CWord>, bkts, FH.bkt_op_code(op),
        FH.bkt_op_val(op))),
    FH.bkt_op_dst(op, fg)):
  (b1, dp3) = dp2
  (b2, pe2) = dp3
  (+eb1, +eb2) = pe2
  +code = FH.bkt_op_code(op)
  +val = FH.bkt_op_val(op)
  +src = FH.bkt_op_src(op, fg)
  +dst = FH.bkt_op_dst(op, fg)
  +zc = FH.bkt_op_zero_from(G, C, n_root, op, fg, hok)
  +ea_b1 : {b1 == a1 : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, b1, a2, a1, eb1, ea2)
  +ea_b2 : {b2 == a1 : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, b2, b1, a1, eb2, ea_b1)
  +hb1 = FH.bkt_tree_transport(G, C, n_root, 10n, 0, bkts, a1, src,
           Equal.sym(Array<+List<SolveFast.CWord>>, a1, bkts, ea1), hb)
  +hb_b1 = FH.bkt_tree_transport(G, C, n_root, 10n, 0, a1, b1, src,
             Equal.sym(Array<+List<SolveFast.CWord>>, b1, a1, ea_b1), hb1)
  +hd_b1 = FH.bkt_tree_depth(G, C, n_root, 10n, 0, b1, src, hb_b1)
  +hd_b2 = Arr.Arr.depth_transport(+List<SolveFast.CWord>, 10n, b1, b2,
             Equal.sym(Array<+List<SolveFast.CWord>>, b2, b1, eb2), hd_b1)
  +em = Arr.Arr.u32_and_mask(10n, code, zc)
  +esw : {Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            Array.swap(+List<SolveFast.CWord>, b2, code, val))
          == Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
               Array.swap.go(+List<SolveFast.CWord>, b2, Arr.Arr.pow2_u32(10n),
                 code, val, U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))
          : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>,
      Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.swap(+List<SolveFast.CWord>, b2, code, val)),
      Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.swap.go(+List<SolveFast.CWord>, b2, Arr.Arr.pow2_u32(10n),
          U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)), val,
          U32.is_lt(U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)),
            U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.swap.go(+List<SolveFast.CWord>, b2, Arr.Arr.pow2_u32(10n), code,
          val, U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.swap_depth(+List<SolveFast.CWord>, 10n, b2, code, val, hd_b2),
      Equal.cong(U32, Array<+List<SolveFast.CWord>>,
        j => Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
               Array.swap.go(+List<SolveFast.CWord>, b2, Arr.Arr.pow2_u32(10n),
                 j, val, U32.is_lt(j, U32.shr(Arr.Arr.pow2_u32(10n))))),
        U32.and(code, U32.sub(Arr.Arr.pow2_u32(10n), 1)), code, em))
  +ea1_b2 : {a1 == b2 : Array<+List<SolveFast.CWord>>} =
    Equal.sym(Array<+List<SolveFast.CWord>>, b2, a1, ea_b2)
  +hgo = FH.bkt_tree_swap_go(G, C, n_root, 10n, 0, a1, op, fg, code,
           U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))), {==}, {==}, zc,
           {==}, FF5.FF5.u32_or_zero_l(code), hok, hb1)
  +eq_a : {Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
             Array.swap.go(+List<SolveFast.CWord>, a1, Arr.Arr.pow2_u32(10n),
               code, val, U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n)))))
           == Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                Array.swap(+List<SolveFast.CWord>, b2, code, val))
           : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>,
      Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.swap.go(+List<SolveFast.CWord>, a1, Arr.Arr.pow2_u32(10n), code,
          val, U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.swap.go(+List<SolveFast.CWord>, b2, Arr.Arr.pow2_u32(10n), code,
          val, U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
      Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.swap(+List<SolveFast.CWord>, b2, code, val)),
      Equal.cong(Array<+List<SolveFast.CWord>>, Array<+List<SolveFast.CWord>>,
        x => Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
               Array.swap.go(+List<SolveFast.CWord>, x, Arr.Arr.pow2_u32(10n),
                 code, val, U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
        a1, b2, ea1_b2),
      Equal.sym(Array<+List<SolveFast.CWord>>,
        Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
          Array.swap(+List<SolveFast.CWord>, b2, code, val)),
        Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
          Array.swap.go(+List<SolveFast.CWord>, b2, Arr.Arr.pow2_u32(10n), code,
            val, U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))), esw))
  %ea1 : FH.BktTree(G, C, n_root, 10n, 0,
           Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
             Array.swap(+List<SolveFast.CWord>, _, code, val)), dst)
  %ea_b2 : FH.BktTree(G, C, n_root, 10n, 0,
             Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
               Array.swap(+List<SolveFast.CWord>, _, code, val)), dst)
  FH.bkt_tree_transport(G, C, n_root, 10n, 0,
    Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.swap.go(+List<SolveFast.CWord>, a1, Arr.Arr.pow2_u32(10n), code,
        val, U32.is_lt(code, U32.shr(Arr.Arr.pow2_u32(10n))))),
    Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.swap(+List<SolveFast.CWord>, b2, code, val)),
    dst, eq_a, hgo)

def FH.bkt_tree_swap_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, -bkts: Array<+List<SolveFast.CWord>>,
    +op: FH.BktOp, +fg: +List<SolveFast.FGroup>,
    +hok: FH.BktOpOk(G, C, n_root, op, fg),
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, FH.bkt_op_src(op, fg)),
    dp: &a1: Array<+List<SolveFast.CWord>> -> &a2: Array<+List<SolveFast.CWord>> ->
        {a1 == bkts : Array<+List<SolveFast.CWord>>}
        & {a2 == a1 : Array<+List<SolveFast.CWord>>}) ->
  FH.BktTree(G, C, n_root, 10n, 0,
    Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.swap(+List<SolveFast.CWord>, bkts, FH.bkt_op_code(op),
        FH.bkt_op_val(op))),
    FH.bkt_op_dst(op, fg)):
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  FH.bkt_tree_swap_dup2(G, C, n_root, bkts, a1, op, fg, ea1, a2, ea2,
    Arr.Arr.dup(+List<SolveFast.CWord>, a2), hok, hb)

def FH.bkt_tree_swap(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    bkts: Array<+List<SolveFast.CWord>>, +op: FH.BktOp,
    +fg: +List<SolveFast.FGroup>,
    +hok: FH.BktOpOk(G, C, n_root, op, fg),
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, FH.bkt_op_src(op, fg))) ->
  FH.BktTree(G, C, n_root, 10n, 0,
    Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.swap(+List<SolveFast.CWord>, bkts, FH.bkt_op_code(op),
        FH.bkt_op_val(op))),
    FH.bkt_op_dst(op, fg)):
  FH.bkt_tree_swap_dup(G, C, n_root, bkts, op, fg, hok, hb,
    Arr.Arr.dup(+List<SolveFast.CWord>, bkts))

def FH.bkt_tree_set_add_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, -bkts: Array<+List<SolveFast.CWord>>,
    +cw: SolveFast.CWord, +fb: +List<Feedback.Color>,
    +old: +List<SolveFast.CWord>, +fg: +List<SolveFast.FGroup>,
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool},
    +hcw: {FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
    +hold: FH.BktLeaf(G, C, n_root, FF5.FF5.encode_fb5_list(fb), fg, old),
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, fg),
    dp: &a1: Array<+List<SolveFast.CWord>> -> &a2: Array<+List<SolveFast.CWord>> ->
        {a1 == bkts : Array<+List<SolveFast.CWord>>}
        & {a2 == a1 : Array<+List<SolveFast.CWord>>}) ->
  FH.BktTree(G, C, n_root, 10n, 0,
    Array.set(+List<SolveFast.CWord>, bkts, FF5.FF5.encode_fb5_list(fb),
      cw <> old),
    SolveFast.fgroup_add_fast(SolveFast.cword_w(cw), fb, fg)):
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  +c = FF5.FF5.encode_fb5_list(fb)
  +val : +List<SolveFast.CWord> = cw <> old
  +fg2 = SolveFast.fgroup_add_fast(SolveFast.cword_w(cw), fb, fg)
  +ea2_b : {a2 == bkts : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, a2, a1, bkts, ea2, ea1)
  +hb2 = FH.bkt_tree_transport(G, C, n_root, 10n, 0, bkts, a2, fg,
           Equal.sym(Array<+List<SolveFast.CWord>>, a2, bkts, ea2_b), hb)
  +hsw = FH.bkt_tree_swap(G, C, n_root, a2, OpAdd{cw, fb, old}, fg,
           Arr.DPair{hfb, Arr.DPair{hwf, Arr.DPair{hcw, hold}}}, hb2)
  +eset : {Array.set(+List<SolveFast.CWord>, a1, c, val)
           == Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                Array.swap(+List<SolveFast.CWord>, a1, c, val))
           : Array<+List<SolveFast.CWord>>} =
    Arr.Arr.set_eq(+List<SolveFast.CWord>, a1, c, val)
  %ea1 : FH.BktTree(G, C, n_root, 10n, 0,
           Array.set(+List<SolveFast.CWord>, _, c, val), fg2)
  FH.bkt_tree_transport(G, C, n_root, 10n, 0,
    Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
      Array.swap(+List<SolveFast.CWord>, a2, c, val)),
    Array.set(+List<SolveFast.CWord>, a1, c, val), fg2,
    Equal.trans(Array<+List<SolveFast.CWord>>,
      Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.swap(+List<SolveFast.CWord>, a2, c, val)),
      Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.swap(+List<SolveFast.CWord>, a1, c, val)),
      Array.set(+List<SolveFast.CWord>, a1, c, val),
      Equal.cong(Array<+List<SolveFast.CWord>>, Array<+List<SolveFast.CWord>>,
        x => Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
               Array.swap(+List<SolveFast.CWord>, x, c, val)),
        a2, a1, ea2),
      Equal.sym(Array<+List<SolveFast.CWord>>,
        Array.set(+List<SolveFast.CWord>, a1, c, val),
        Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
          Array.swap(+List<SolveFast.CWord>, a1, c, val)), eset)),
    hsw)

def FH.bkt_tree_set_add(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, bkts: Array<+List<SolveFast.CWord>>,
    +cw: SolveFast.CWord, +fb: +List<Feedback.Color>,
    +old: +List<SolveFast.CWord>, +fg: +List<SolveFast.FGroup>,
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool},
    +hcw: {FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
    +hold: FH.BktLeaf(G, C, n_root, FF5.FF5.encode_fb5_list(fb), fg, old),
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, fg)) ->
  FH.BktTree(G, C, n_root, 10n, 0,
    Array.set(+List<SolveFast.CWord>, bkts, FF5.FF5.encode_fb5_list(fb),
      cw <> old),
    SolveFast.fgroup_add_fast(SolveFast.cword_w(cw), fb, fg)):
  FH.bkt_tree_set_add_dup(G, C, n_root, bkts, cw, fb, old, fg, hfb, hwf, hcw,
    hold, hb, Arr.Arr.dup(+List<SolveFast.CWord>, bkts))


# ---------------------------------------------------------------------------
# Pass 2a: table-backed `fill5_go`
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
            Equal.sym(Nat, len, 0n, elen0)), hlen)
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

def FH.FillSpec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +fg: +List<SolveFast.FGroup>, +acc_touched: +List<U32>,
    -tbl0: Array<U32>, fs: SolveFast.Fill5State) -> Data:
  match fs:
    case SolveFast.Fill5State{bkts, tbl, touched}:
      Arr.Arr.DPair<
        FH.BktTree(G, C, n_root, 10n, 0, bkts, fg),
        Arr.Arr.DPair<
          {tbl == tbl0 : Array<U32>},
          Arr.Arr.DPair<
            {touched == FH.rev_codes(fg, acc_touched) : +List<U32>},
            {FH.fgroups_wf(fg) == True{} : Bool}>>>

def FH.fill_spec_transport(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +fg: +List<SolveFast.FGroup>, +acc_touched: +List<U32>,
    -tbl0: Array<U32>,
    -fs1: SolveFast.Fill5State, -fs2: SolveFast.Fill5State,
    +ef: {fs1 == fs2 : SolveFast.Fill5State},
    +h: FH.FillSpec(G, C, n_root, fg, acc_touched, tbl0, fs1)) ->
  FH.FillSpec(G, C, n_root, fg, acc_touched, tbl0, fs2):
  %ef : FH.FillSpec(G, C, n_root, fg, acc_touched, tbl0, _)
  h

def FH.fill_spec_transport_fg(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +fg1: +List<SolveFast.FGroup>, +fg2: +List<SolveFast.FGroup>,
    +acc_touched: +List<U32>, -tbl0: Array<U32>, -fs: SolveFast.Fill5State,
    +efg: {fg1 == fg2 : +List<SolveFast.FGroup>},
    +h: FH.FillSpec(G, C, n_root, fg1, acc_touched, tbl0, fs)) ->
  FH.FillSpec(G, C, n_root, fg2, acc_touched, tbl0, fs):
  %efg : FH.FillSpec(G, C, n_root, _, acc_touched, tbl0, fs)
  h

def FH.fill_spec_transport_tbl(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +fg: +List<SolveFast.FGroup>, +acc_touched: +List<U32>,
    -t1: Array<U32>, -t2: Array<U32>, -fs: SolveFast.Fill5State,
    +et: {t1 == t2 : Array<U32>},
    +h: FH.FillSpec(G, C, n_root, fg, acc_touched, t1, fs)) ->
  FH.FillSpec(G, C, n_root, fg, acc_touched, t2, fs):
  %et : FH.FillSpec(G, C, n_root, fg, acc_touched, _, fs)
  h

def FH.fill5_get_done_old(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +cw: SolveFast.CWord, +fb: +List<Feedback.Color>,
    +code: U32, +fg0: +List<SolveFast.FGroup>, +touched: +List<U32>,
    +acc_touched: +List<U32>, b2: Array<+List<SolveFast.CWord>>,
    -tbl: Array<U32>, +old: +List<SolveFast.CWord>,
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hcw: {FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb2: FH.BktTree(G, C, n_root, 10n, 0, b2, fg0),
    +hold: FH.BktLeaf(G, C, n_root, FF5.FF5.encode_fb5_list(fb), fg0, old)) ->
  FH.FillSpec(G, C, n_root,
    SolveFast.fgroup_add_fast(SolveFast.cword_w(cw), fb, fg0), acc_touched, tbl,
    SolveFast.fill5_get_done(cw, code, tbl, touched, (b2, old))):
  match old:
    case Nil{}:
      +c = FF5.FF5.encode_fb5_list(fb)
      +w = SolveFast.cword_w(cw)
      +fg1 = SolveFast.fgroup_add_fast(w, fb, fg0)
      +hwf1 = FH.add_facts_wf(w, fb, fg0, fg1,
                FH.fgroup_add_facts(w, fb, fg0,
                  SolveFast.next_fgroup_hit(fb, fg0), {==}, hfb, hwf))
      +eold = Arr.Arr.dpair_l(
                {Nil{} == FH.lookup_code(c, fg0) : +List<+List<Nat>>},
                {True{} == True{} : Bool}, hold)
      +hhas : {FH.has_code(c, fg0) == False{} : Bool} =
        FH.has_code_false_of_lookup_nil(c, fg0, hwf,
          Equal.sym(+List<+List<Nat>>, Nil{}, FH.lookup_code(c, fg0), eold))
      +et1 : {code <> touched == FH.rev_codes(fg1, acc_touched) : +List<U32>} =
        Equal.trans(+List<U32>,
          code <> touched,
          c <> FH.rev_codes(fg0, acc_touched),
          FH.rev_codes(fg1, acc_touched),
          Equal.trans(+List<U32>,
            code <> touched, c <> touched, c <> FH.rev_codes(fg0, acc_touched),
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
          FH.BktTree(G, C, n_root, 10n, 0,
            Array.set(+List<SolveFast.CWord>, b2, _, cw <> Nil{}), fg1),
          Arr.Arr.DPair<{tbl == tbl : Array<U32>},
            Arr.Arr.DPair<
              {code <> touched == FH.rev_codes(fg1, acc_touched) : +List<U32>},
              {FH.fgroups_wf(fg1) == True{} : Bool}>>>
      Arr.DPair{
        FH.bkt_tree_set_add(G, C, n_root, b2, cw, fb, Nil{}, fg0, hfb, hwf,
          hcw, hold, hb2),
        Arr.DPair{{==}, Arr.DPair{et1, hwf1}}}
    case Con{+h, +t}:
      +c = FF5.FF5.encode_fb5_list(fb)
      +w = SolveFast.cword_w(cw)
      +fg1 = SolveFast.fgroup_add_fast(w, fb, fg0)
      +hwf1 = FH.add_facts_wf(w, fb, fg0, fg1,
                FH.fgroup_add_facts(w, fb, fg0,
                  SolveFast.next_fgroup_hit(fb, fg0), {==}, hfb, hwf))
      +eold = Arr.Arr.dpair_l(
                {SolveFast.cwords_words(h <> t) == FH.lookup_code(c, fg0)
                 : +List<+List<Nat>>},
                {FT.FT.cwords_ok_b(G, C, n_root, h <> t) == True{} : Bool}, hold)
      +econ : {FH.lookup_code(c, fg0)
               == SolveFast.cword_w(h) <> SolveFast.cwords_words(t)
               : +List<+List<Nat>>} =
        Equal.trans(+List<+List<Nat>>,
          FH.lookup_code(c, fg0),
          SolveFast.cwords_words(h <> t),
          SolveFast.cword_w(h) <> SolveFast.cwords_words(t),
          Equal.sym(+List<+List<Nat>>, SolveFast.cwords_words(h <> t),
            FH.lookup_code(c, fg0), eold),
          FH.cwords_words_cons(h, t))
      +hhas : {FH.has_code(c, fg0) == True{} : Bool} =
        FH.has_code_true_of_lookup_con(c, fg0, SolveFast.cword_w(h),
          SolveFast.cwords_words(t), econ)
      +et1 : {touched == FH.rev_codes(fg1, acc_touched) : +List<U32>} =
        Equal.trans(+List<U32>,
          touched, FH.rev_codes(fg0, acc_touched), FH.rev_codes(fg1, acc_touched),
          etouched,
          Equal.sym(+List<U32>,
            FH.rev_codes(fg1, acc_touched), FH.rev_codes(fg0, acc_touched),
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
          FH.BktTree(G, C, n_root, 10n, 0,
            Array.set(+List<SolveFast.CWord>, b2, _, cw <> (h <> t)), fg1),
          Arr.Arr.DPair<{tbl == tbl : Array<U32>},
            Arr.Arr.DPair<
              {touched == FH.rev_codes(fg1, acc_touched) : +List<U32>},
              {FH.fgroups_wf(fg1) == True{} : Bool}>>>
      Arr.DPair{
        FH.bkt_tree_set_add(G, C, n_root, b2, cw, fb, h <> t, fg0, hfb, hwf,
          hcw, hold, hb2),
        Arr.DPair{{==}, Arr.DPair{et1, hwf1}}}

def FH.fill5_get_done_pair(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +cw: SolveFast.CWord, +fb: +List<Feedback.Color>,
    +code: U32, +fg0: +List<SolveFast.FGroup>, +touched: +List<U32>,
    +acc_touched: +List<U32>, -tbl: Array<U32>,
    r: Array<+List<SolveFast.CWord>> & +List<SolveFast.CWord>,
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hcw: {FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb2: FH.BktTree(G, C, n_root, 10n, 0,
            Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>, r),
            fg0),
    +hold: FH.BktLeaf(G, C, n_root, FF5.FF5.encode_fb5_list(fb), fg0,
             Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>, r))) ->
  FH.FillSpec(G, C, n_root,
    SolveFast.fgroup_add_fast(SolveFast.cword_w(cw), fb, fg0), acc_touched, tbl,
    SolveFast.fill5_get_done(cw, code, tbl, touched, r)):
  (b2, +old) = r
  FH.fill5_get_done_old(G, C, n_root, cw, fb, code, fg0, touched, acc_touched,
    b2, tbl, old, ecode, hfb, hwf, hcw, etouched, hb2, hold)

def FH.fill5_step_get_dup3(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +cw: SolveFast.CWord, +fb: +List<Feedback.Color>,
    +code: U32, +fg0: +List<SolveFast.FGroup>, +touched: +List<U32>,
    +acc_touched: +List<U32>, -bkts: Array<+List<SolveFast.CWord>>,
    -tbl: Array<U32>,
    a1: Array<+List<SolveFast.CWord>>,
    +ea1: {a1 == bkts : Array<+List<SolveFast.CWord>>},
    b1: Array<+List<SolveFast.CWord>>,
    +eb1: {b1 == a1 : Array<+List<SolveFast.CWord>>},
    -b2: Array<+List<SolveFast.CWord>>,
    +eb2: {b2 == b1 : Array<+List<SolveFast.CWord>>},
    dp3: &c1: Array<+List<SolveFast.CWord>> -> &c2: Array<+List<SolveFast.CWord>> ->
         {c1 == b2 : Array<+List<SolveFast.CWord>>}
         & {c2 == c1 : Array<+List<SolveFast.CWord>>},
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hcw: {FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, fg0)) ->
  FH.FillSpec(G, C, n_root,
    SolveFast.fgroup_add_fast(SolveFast.cword_w(cw), fb, fg0), acc_touched, tbl,
    SolveFast.fill5_get_done(cw, code, tbl, touched,
      Array.get(+List<SolveFast.CWord>, bkts, code))):
  (c1, dp4) = dp3
  (c2, pe3) = dp4
  (+ec1, +ec2) = pe3
  +c = FF5.FF5.encode_fb5_list(fb)
  +ec1_a : {c1 == a1 : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, c1, b2, a1, ec1,
      Equal.trans(Array<+List<SolveFast.CWord>>, b2, b1, a1, eb2, eb1))
  +ec2_a : {c2 == a1 : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, c2, c1, a1, ec2, ec1_a)
  +eb1_bk : {b1 == bkts : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, b1, a1, bkts, eb1, ea1)
  +ec1_bk : {c1 == bkts : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, c1, a1, bkts, ec1_a, ea1)
  +hb_a1 = FH.bkt_tree_transport(G, C, n_root, 10n, 0, bkts, a1, fg0,
             Equal.sym(Array<+List<SolveFast.CWord>>, a1, bkts, ea1), hb)
  +hb_b1 = FH.bkt_tree_transport(G, C, n_root, 10n, 0, bkts, b1, fg0,
             Equal.sym(Array<+List<SolveFast.CWord>>, b1, bkts, eb1_bk), hb)
  +hb_c1 = FH.bkt_tree_transport(G, C, n_root, 10n, 0, bkts, c1, fg0,
             Equal.sym(Array<+List<SolveFast.CWord>>, c1, bkts, ec1_bk), hb)
  +hd_b1 = FH.bkt_tree_depth(G, C, n_root, 10n, 0, b1, fg0, hb_b1)
  +hd_c2 = Arr.Arr.depth_transport(+List<SolveFast.CWord>, 10n, b1, c2,
             Equal.trans(Array<+List<SolveFast.CWord>>, b1, a1, c2, eb1,
               Equal.sym(Array<+List<SolveFast.CWord>>, c2, a1, ec2_a)), hd_b1)
  +efst_c2 : {Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                Array.get(+List<SolveFast.CWord>, c2, code)) == c2
              : Array<+List<SolveFast.CWord>>} =
    Arr.Arr.get_fst(+List<SolveFast.CWord>, 10n, c2, code, hd_c2)
  +efst_a1 : {Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                Array.get(+List<SolveFast.CWord>, a1, code)) == a1
              : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>,
      Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.get(+List<SolveFast.CWord>, a1, code)),
      Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.get(+List<SolveFast.CWord>, c2, code)), a1,
      Equal.cong(Array<+List<SolveFast.CWord>>, Array<+List<SolveFast.CWord>>,
        x => Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
               Array.get(+List<SolveFast.CWord>, x, code)),
        a1, c2, Equal.sym(Array<+List<SolveFast.CWord>>, c2, a1, ec2_a)),
      Equal.trans(Array<+List<SolveFast.CWord>>,
        Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
          Array.get(+List<SolveFast.CWord>, c2, code)),
        c2, a1, efst_c2, ec2_a))
  +hb_fst = FH.bkt_tree_transport(G, C, n_root, 10n, 0, a1,
              Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                Array.get(+List<SolveFast.CWord>, a1, code)), fg0,
              Equal.sym(Array<+List<SolveFast.CWord>>,
                Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                  Array.get(+List<SolveFast.CWord>, a1, code)), a1, efst_a1),
              hb_a1)
  +hl_c1 = FH.bkt_tree_get(G, C, n_root, c1, fg0, c,
             FF5.FF5.encode_fb5_list_zero_from(fb, hfb), hb_c1)
  +esnd : {Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
             Array.get(+List<SolveFast.CWord>, c1, c))
           == Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                Array.get(+List<SolveFast.CWord>, a1, code))
           : +List<SolveFast.CWord>} =
    Equal.trans(+List<SolveFast.CWord>,
      Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.get(+List<SolveFast.CWord>, c1, c)),
      Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.get(+List<SolveFast.CWord>, a1, c)),
      Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.get(+List<SolveFast.CWord>, a1, code)),
      Equal.cong(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        x => Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
               Array.get(+List<SolveFast.CWord>, x, c)),
        c1, a1, ec1_a),
      Equal.cong(U32, +List<SolveFast.CWord>,
        j => Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
               Array.get(+List<SolveFast.CWord>, a1, j)),
        c, code, Equal.sym(U32, code, c, ecode)))
  +hl_a1 = FH.bkt_leaf_transport_v(G, C, n_root, c, fg0,
             Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
               Array.get(+List<SolveFast.CWord>, c1, c)),
             Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
               Array.get(+List<SolveFast.CWord>, a1, code)), esnd, hl_c1)
  %ea1 : FH.FillSpec(G, C, n_root,
           SolveFast.fgroup_add_fast(SolveFast.cword_w(cw), fb, fg0),
           acc_touched, tbl,
           SolveFast.fill5_get_done(cw, code, tbl, touched,
             Array.get(+List<SolveFast.CWord>, _, code)))
  FH.fill5_get_done_pair(G, C, n_root, cw, fb, code, fg0, touched, acc_touched,
    tbl, Array.get(+List<SolveFast.CWord>, a1, code), ecode, hfb, hwf, hcw,
    etouched, hb_fst, hl_a1)

def FH.fill5_step_get_dup2(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +cw: SolveFast.CWord, +fb: +List<Feedback.Color>,
    +code: U32, +fg0: +List<SolveFast.FGroup>, +touched: +List<U32>,
    +acc_touched: +List<U32>, -bkts: Array<+List<SolveFast.CWord>>,
    -tbl: Array<U32>,
    a1: Array<+List<SolveFast.CWord>>,
    +ea1: {a1 == bkts : Array<+List<SolveFast.CWord>>},
    -a2: Array<+List<SolveFast.CWord>>,
    +ea2: {a2 == a1 : Array<+List<SolveFast.CWord>>},
    dp2: &b1: Array<+List<SolveFast.CWord>> -> &b2: Array<+List<SolveFast.CWord>> ->
         {b1 == a2 : Array<+List<SolveFast.CWord>>}
         & {b2 == b1 : Array<+List<SolveFast.CWord>>},
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hcw: {FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, fg0)) ->
  FH.FillSpec(G, C, n_root,
    SolveFast.fgroup_add_fast(SolveFast.cword_w(cw), fb, fg0), acc_touched, tbl,
    SolveFast.fill5_get_done(cw, code, tbl, touched,
      Array.get(+List<SolveFast.CWord>, bkts, code))):
  (b1, dp3) = dp2
  (b2, pe2) = dp3
  (+eb1, +eb2) = pe2
  FH.fill5_step_get_dup3(G, C, n_root, cw, fb, code, fg0, touched, acc_touched,
    bkts, tbl, a1, ea1,
    b1, Equal.trans(Array<+List<SolveFast.CWord>>, b1, a2, a1, eb1, ea2),
    b2, eb2, Arr.Arr.dup(+List<SolveFast.CWord>, b2),
    ecode, hfb, hwf, hcw, etouched, hb)

def FH.fill5_step_get_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +cw: SolveFast.CWord, +fb: +List<Feedback.Color>,
    +code: U32, +fg0: +List<SolveFast.FGroup>, +touched: +List<U32>,
    +acc_touched: +List<U32>, -bkts: Array<+List<SolveFast.CWord>>,
    -tbl: Array<U32>,
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hcw: {FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, fg0),
    dp: &a1: Array<+List<SolveFast.CWord>> -> &a2: Array<+List<SolveFast.CWord>> ->
        {a1 == bkts : Array<+List<SolveFast.CWord>>}
        & {a2 == a1 : Array<+List<SolveFast.CWord>>}) ->
  FH.FillSpec(G, C, n_root,
    SolveFast.fgroup_add_fast(SolveFast.cword_w(cw), fb, fg0), acc_touched, tbl,
    SolveFast.fill5_get_done(cw, code, tbl, touched,
      Array.get(+List<SolveFast.CWord>, bkts, code))):
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  FH.fill5_step_get_dup2(G, C, n_root, cw, fb, code, fg0, touched, acc_touched,
    bkts, tbl, a1, ea1, a2, ea2, Arr.Arr.dup(+List<SolveFast.CWord>, a2),
    ecode, hfb, hwf, hcw, etouched, hb)

def FH.fill5_step_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +g: +List<Nat>, +cw: SolveFast.CWord,
    +fb: +List<Feedback.Color>, +code: U32, same: Bool,
    +fg0: +List<SolveFast.FGroup>, bkts: Array<+List<SolveFast.CWord>>,
    -tbl: Array<U32>, +touched: +List<U32>, +acc_touched: +List<U32>,
    +esame: {same == SolveFast.word_eq_fast(g, SolveFast.cword_w(cw)) : Bool},
    +ecode: {code == FF5.FF5.encode_fb5_list(fb) : U32},
    +efbeq: {SolveFast.feedback_fast(g, SolveFast.cword_w(cw)) == fb
             : +List<Feedback.Color>},
    +hfb: {FF5.FF5.is_fb5(fb) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +hcw: {FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, fg0)) ->
  FH.FillSpec(G, C, n_root,
    SolveFast.fgroups_next_acc(g, SolveFast.cword_w(cw), fg0,
      SolveFast.word_eq_fast(g, SolveFast.cword_w(cw))),
    acc_touched, tbl,
    SolveFast.fill5_step(cw, code, same, bkts, tbl, touched)):
  match same:
    case True{}:
      +w = SolveFast.cword_w(cw)
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
      FH.fill_spec_transport_fg(G, C, n_root, fg0,
        SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)),
        acc_touched, tbl, SolveFast.Fill5State{bkts, tbl, touched}, efg,
        Arr.DPair{hb, Arr.DPair{{==}, Arr.DPair{etouched, hwf}}})
    case False{}:
      +w = SolveFast.cword_w(cw)
      +ewf : {SolveFast.word_eq_fast(g, w) == False{} : Bool} =
        Equal.sym(Bool, False{}, SolveFast.word_eq_fast(g, w), esame)
      +efg : {SolveFast.fgroup_add_fast(w, fb, fg0)
              == SolveFast.fgroups_next_acc(g, w, fg0,
                   SolveFast.word_eq_fast(g, w)) : +List<SolveFast.FGroup>} =
        Equal.sym(+List<SolveFast.FGroup>,
          SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)),
          SolveFast.fgroup_add_fast(w, fb, fg0),
          Equal.trans(+List<SolveFast.FGroup>,
            SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)),
            SolveFast.fgroup_add_fast(w, SolveFast.feedback_fast(g, w), fg0),
            SolveFast.fgroup_add_fast(w, fb, fg0),
            Equal.cong(Bool, +List<SolveFast.FGroup>,
              b => SolveFast.fgroups_next_acc(g, w, fg0, b),
              SolveFast.word_eq_fast(g, w), False{}, ewf),
            Equal.cong(+List<Feedback.Color>, +List<SolveFast.FGroup>,
              f => SolveFast.fgroup_add_fast(w, f, fg0),
              SolveFast.feedback_fast(g, w), fb, efbeq)))
      FH.fill_spec_transport_fg(G, C, n_root,
        SolveFast.fgroup_add_fast(w, fb, fg0),
        SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)),
        acc_touched, tbl,
        SolveFast.fill5_get_done(cw, code, tbl, touched,
          Array.get(+List<SolveFast.CWord>, bkts, code)),
        efg,
        FH.fill5_step_get_dup(G, C, n_root, cw, fb, code, fg0, touched,
          acc_touched, bkts, tbl, ecode, hfb, hwf, hcw, etouched, hb,
          Arr.Arr.dup(+List<SolveFast.CWord>, bkts)))

def FH.fill5_one_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +row: U32, +g: +List<Nat>, +cw: SolveFast.CWord,
    +fg0: +List<SolveFast.FGroup>, bkts: Array<+List<SolveFast.CWord>>,
    tbl: Array<U32>, +touched: +List<U32>, +acc_touched: +List<U32>,
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hcw: {FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, fg0)) ->
  FH.FillSpec(G, C, n_root,
    SolveFast.fgroups_next_acc(g, SolveFast.cword_w(cw), fg0,
      SolveFast.word_eq_fast(g, SolveFast.cword_w(cw))),
    acc_touched, tbl,
    SolveFast.fill5_one(row, cw, bkts, tbl, touched)):
  match cw:
    case SolveFast.CWord{+ci, +grow, +w}:
      +cw1 : SolveFast.CWord = SolveFast.CWord{ci, grow, w}
      +hcol = Logic.Proof.and_true_l(FT.FT.has_col_go(Groups.len_words(G), C, ci, w, 0n),
                FT.FT.gentry_ok_b(G, n_root, grow, w), hcw)
      FT.FT.tbl_get_use(
        r => FH.FillSpec(G, C, n_root,
               SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)),
               acc_touched, tbl,
               SolveFast.fill5_tbl_done(cw1, bkts, touched, r)),
        G, C, n_root, row, g, ci, w, tbl, htbl, hrow, hcol,
        tbl2 => +code => +etbl2 => +htbl2 => +ecode => +hg5 => +hw5 =>
          +fb = Feedback.feedback(g, w)
          +hfb : {FF5.FF5.is_fb5(fb) == True{} : Bool} =
            FT.FT.is_fb5_of_len5(g, w, hg5, hw5)
          +esame : {U32.is_eq(code, 682) == SolveFast.word_eq_fast(g, w) : Bool} =
            Equal.trans(Bool, U32.is_eq(code, 682), Feedback.word_eq(g, w),
              SolveFast.word_eq_fast(g, w),
              Equal.trans(Bool, U32.is_eq(code, 682),
                U32.is_eq(FT.FT.fb_code_words(g, w), 682),
                Feedback.word_eq(g, w),
                Equal.cong(U32, Bool, u => U32.is_eq(u, 682),
                  code, FT.FT.fb_code_words(g, w), ecode),
                FT.FT.fb_code_is_682(g, w, hg5, hw5)),
              Equal.sym(Bool, SolveFast.word_eq_fast(g, w),
                Feedback.word_eq(g, w), FG.FG.word_eq_fast_eq(g, w)))
          FH.fill_spec_transport_tbl(G, C, n_root,
            SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)),
            acc_touched, tbl2, tbl,
            SolveFast.fill5_step(cw1, code, U32.is_eq(code, 682), bkts, tbl2,
              touched),
            etbl2,
            FH.fill5_step_spec(G, C, n_root, g, cw1, fb, code,
              U32.is_eq(code, 682), fg0, bkts, tbl2, touched, acc_touched,
              esame, ecode, FG.FG.feedback_eq(g, w), hfb, hwf, hcw, etouched,
              hb)))

def FH.fill5_go_step_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +row: U32, +g: +List<Nat>, +w: +List<Nat>,
    +rest: +List<SolveFast.CWord>, +fg0: +List<SolveFast.FGroup>,
    +acc_touched: +List<U32>, -tbl0: Array<U32>,
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    st1: SolveFast.Fill5State,
    +h1: FH.FillSpec(G, C, n_root,
           SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)),
           acc_touched, tbl0, st1),
    rec: @b2: Array<+List<SolveFast.CWord>> -> @t2: Array<U32> ->
         @+tr2: +List<U32> ->
         FT.FT.TblOk(G, C, n_root, t2) ->
         {FH.fgroups_wf(
            SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)))
          == True{} : Bool} ->
         {tr2 == FH.rev_codes(
                   SolveFast.fgroups_next_acc(g, w, fg0,
                     SolveFast.word_eq_fast(g, w)), acc_touched) : +List<U32>} ->
         FH.BktTree(G, C, n_root, 10n, 0, b2,
           SolveFast.fgroups_next_acc(g, w, fg0,
             SolveFast.word_eq_fast(g, w))) ->
         FH.FillSpec(G, C, n_root,
           SolveFast.fgroups_build_fast(g, SolveFast.cwords_words(rest),
             SolveFast.fgroups_next_acc(g, w, fg0,
               SolveFast.word_eq_fast(g, w))),
           acc_touched, t2,
           SolveFast.fill5_go(row, rest,
             SolveFast.Fill5State{b2, t2, tr2}))) ->
  FH.FillSpec(G, C, n_root,
    SolveFast.fgroups_build_fast(g, w <> SolveFast.cwords_words(rest), fg0),
    acc_touched, tbl0, SolveFast.fill5_go(row, rest, st1)):
  match st1:
    case SolveFast.Fill5State{bkts2, tbl2, +tr2}:
      +fg1 = SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w))
      +hb2 = Arr.Arr.dpair_l(
               FH.BktTree(G, C, n_root, 10n, 0, bkts2, fg1),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 Arr.Arr.DPair<{tr2 == FH.rev_codes(fg1, acc_touched) : +List<U32>},
                   {FH.fgroups_wf(fg1) == True{} : Bool}>>, h1)
      +r1 = Arr.Arr.dpair_r(
              FH.BktTree(G, C, n_root, 10n, 0, bkts2, fg1),
              Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                Arr.Arr.DPair<{tr2 == FH.rev_codes(fg1, acc_touched) : +List<U32>},
                  {FH.fgroups_wf(fg1) == True{} : Bool}>>, h1)
      +et2 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
               Arr.Arr.DPair<{tr2 == FH.rev_codes(fg1, acc_touched) : +List<U32>},
                 {FH.fgroups_wf(fg1) == True{} : Bool}>, r1)
      +r2 = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
              Arr.Arr.DPair<{tr2 == FH.rev_codes(fg1, acc_touched) : +List<U32>},
                {FH.fgroups_wf(fg1) == True{} : Bool}>, r1)
      +etr = Arr.Arr.dpair_l(
               {tr2 == FH.rev_codes(fg1, acc_touched) : +List<U32>},
               {FH.fgroups_wf(fg1) == True{} : Bool}, r2)
      +hwf1 = Arr.Arr.dpair_r(
                {tr2 == FH.rev_codes(fg1, acc_touched) : +List<U32>},
                {FH.fgroups_wf(fg1) == True{} : Bool}, r2)
      +ht2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl0, tbl2,
               Equal.sym(Array<U32>, tbl2, tbl0, et2), htbl0)
      FH.fill_spec_transport_tbl(G, C, n_root,
        SolveFast.fgroups_build_fast(g, SolveFast.cwords_words(rest), fg1),
        acc_touched, tbl2, tbl0,
        SolveFast.fill5_go(row, rest, SolveFast.Fill5State{bkts2, tbl2, tr2}),
        et2, rec(bkts2, tbl2, tr2, ht2, hwf1, etr, hb2))

def FH.fill5_go_cons_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +row: U32, +g: +List<Nat>,
    +ci: U32, +grow: U32, +w: +List<Nat>, +rest: +List<SolveFast.CWord>,
    +fg0: +List<SolveFast.FGroup>, -bkts: Array<+List<SolveFast.CWord>>,
    -tbl: Array<U32>, +touched: +List<U32>, +acc_touched: +List<U32>,
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hcw: {FT.FT.cword_ok_b(G, C, n_root, SolveFast.CWord{ci, grow, w})
           == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, fg0),
    dpb: &b1: Array<+List<SolveFast.CWord>> -> &b2: Array<+List<SolveFast.CWord>> ->
         {b1 == bkts : Array<+List<SolveFast.CWord>>}
         & {b2 == b1 : Array<+List<SolveFast.CWord>>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>},
    rec: @b2: Array<+List<SolveFast.CWord>> -> @t2: Array<U32> ->
         @+tr2: +List<U32> ->
         FT.FT.TblOk(G, C, n_root, t2) ->
         {FH.fgroups_wf(
            SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w)))
          == True{} : Bool} ->
         {tr2 == FH.rev_codes(
                   SolveFast.fgroups_next_acc(g, w, fg0,
                     SolveFast.word_eq_fast(g, w)), acc_touched) : +List<U32>} ->
         FH.BktTree(G, C, n_root, 10n, 0, b2,
           SolveFast.fgroups_next_acc(g, w, fg0,
             SolveFast.word_eq_fast(g, w))) ->
         FH.FillSpec(G, C, n_root,
           SolveFast.fgroups_build_fast(g, SolveFast.cwords_words(rest),
             SolveFast.fgroups_next_acc(g, w, fg0,
               SolveFast.word_eq_fast(g, w))),
           acc_touched, t2,
           SolveFast.fill5_go(row, rest,
             SolveFast.Fill5State{b2, t2, tr2}))) ->
  FH.FillSpec(G, C, n_root,
    SolveFast.fgroups_build_fast(g, w <> SolveFast.cwords_words(rest), fg0),
    acc_touched, tbl,
    SolveFast.fill5_go(row, rest,
      SolveFast.fill5_one(row, SolveFast.CWord{ci, grow, w}, bkts, tbl,
        touched))):
  (b1, dpb2) = dpb
  (b2, peb) = dpb2
  (+eb1, +eb2) = peb
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2) = pet
  +cw : SolveFast.CWord = SolveFast.CWord{ci, grow, w}
  +fg1 = SolveFast.fgroups_next_acc(g, w, fg0, SolveFast.word_eq_fast(g, w))
  +eb2_bk : {b2 == bkts : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, b2, b1, bkts, eb2, eb1)
  +et2_t : {t2 == tbl : Array<U32>} = Equal.trans(Array<U32>, t2, t1, tbl, et2, et1)
  +hb2 = FH.bkt_tree_transport(G, C, n_root, 10n, 0, bkts, b2, fg0,
           Equal.sym(Array<+List<SolveFast.CWord>>, b2, bkts, eb2_bk), hb)
  +ht2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl, t2,
           Equal.sym(Array<U32>, t2, tbl, et2_t), htbl)
  +h1_2 = FH.fill5_one_spec(G, C, n_root, row, g, cw, fg0, b2, t2, touched,
            acc_touched, ht2, hrow, hcw, hwf, etouched, hb2)
  +h1_t0 = FH.fill_spec_transport_tbl(G, C, n_root, fg1, acc_touched, t2, tbl,
             SolveFast.fill5_one(row, cw, b2, t2, touched), et2_t, h1_2)
  +eq_12 : {SolveFast.fill5_one(row, cw, b2, t2, touched)
            == SolveFast.fill5_one(row, cw, b1, t1, touched)
            : SolveFast.Fill5State} =
    Equal.trans(SolveFast.Fill5State,
      SolveFast.fill5_one(row, cw, b2, t2, touched),
      SolveFast.fill5_one(row, cw, b1, t2, touched),
      SolveFast.fill5_one(row, cw, b1, t1, touched),
      Equal.cong(Array<+List<SolveFast.CWord>>, SolveFast.Fill5State,
        x => SolveFast.fill5_one(row, cw, x, t2, touched), b2, b1, eb2),
      Equal.cong(Array<U32>, SolveFast.Fill5State,
        y => SolveFast.fill5_one(row, cw, b1, y, touched), t2, t1, et2))
  +h1_1 = FH.fill_spec_transport(G, C, n_root, fg1, acc_touched, tbl,
            SolveFast.fill5_one(row, cw, b2, t2, touched),
            SolveFast.fill5_one(row, cw, b1, t1, touched), eq_12, h1_t0)
  %eb1 : FH.FillSpec(G, C, n_root,
           SolveFast.fgroups_build_fast(g, w <> SolveFast.cwords_words(rest),
             fg0), acc_touched, tbl,
           SolveFast.fill5_go(row, rest,
             SolveFast.fill5_one(row, cw, _, tbl, touched)))
  %et1 : FH.FillSpec(G, C, n_root,
           SolveFast.fgroups_build_fast(g, w <> SolveFast.cwords_words(rest),
             fg0), acc_touched, tbl,
           SolveFast.fill5_go(row, rest,
             SolveFast.fill5_one(row, cw, b1, _, touched)))
  FH.fill5_go_step_dup(G, C, n_root, row, g, w, rest, fg0, acc_touched, tbl,
    htbl, SolveFast.fill5_one(row, cw, b1, t1, touched), h1_1, rec)

def FH.fill5_go_spec(+S: +List<SolveFast.CWord>, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n_root: Nat, +row: U32, +g: +List<Nat>,
    +fg0: +List<SolveFast.FGroup>, bkts: Array<+List<SolveFast.CWord>>,
    tbl: Array<U32>, +touched: +List<U32>, +acc_touched: +List<U32>,
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hS: {FT.FT.cwords_ok_b(G, C, n_root, S) == True{} : Bool},
    +hwf: {FH.fgroups_wf(fg0) == True{} : Bool},
    +etouched: {touched == FH.rev_codes(fg0, acc_touched) : +List<U32>},
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, fg0)) ->
  FH.FillSpec(G, C, n_root,
    SolveFast.fgroups_build_fast(g, SolveFast.cwords_words(S), fg0),
    acc_touched, tbl,
    SolveFast.fill5_go(row, S, SolveFast.Fill5State{bkts, tbl, touched})):
  match S:
    case Nil{}:
      Arr.DPair{hb, Arr.DPair{{==}, Arr.DPair{etouched, hwf}}}
    case Con{cw, +rest}:
      match cw:
        case SolveFast.CWord{+ci, +grow, +w}:
          +hcw = Logic.Proof.and_true_l(
                   FT.FT.cword_ok_b(G, C, n_root, SolveFast.CWord{ci, grow, w}),
                   FT.FT.cwords_ok_b(G, C, n_root, rest), hS)
          +hrest = Logic.Proof.and_true_r(
                     FT.FT.cword_ok_b(G, C, n_root, SolveFast.CWord{ci, grow, w}),
                     FT.FT.cwords_ok_b(G, C, n_root, rest), hS)
          +fg1 = SolveFast.fgroups_next_acc(g, w, fg0,
                   SolveFast.word_eq_fast(g, w))
          FH.fill5_go_cons_dup(G, C, n_root, row, g, ci, grow, w, rest, fg0,
            bkts, tbl, touched, acc_touched, htbl, hrow, hcw, hwf, etouched, hb,
            Arr.Arr.dup(+List<SolveFast.CWord>, bkts), Arr.Arr.dup(U32, tbl),
            b2 => t2 => +tr2 => +ht2 => +hwf1 => +etr2 => +hb2 =>
              FH.fill5_go_spec(rest, G, C, n_root, row, g, fg1, b2, t2, tr2,
                acc_touched, ht2, hrow, hrest, hwf1, etr2, hb2))


# ---------------------------------------------------------------------------
# Pass 2b: LCF `BigClass`, `insert_big`, `emit_bigs`, `drain5_go` + `DoneItem`
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

def FH.drain5_go_append(+gn: Nat, +ts1: +List<U32>, +ts2: +List<U32>,
    st: SolveFast.Drain5State) ->
  {SolveFast.drain5_go(gn, List.append(&2, U32, ts1, ts2), st)
   == SolveFast.drain5_go(gn, ts2, SolveFast.drain5_go(gn, ts1, st))
   : SolveFast.Drain5State}:
  match ts1:
    case Nil{}:
      {==}
    case Con{+code, +rest}:
      match st:
        case SolveFast.Drain5State{bkts, tbl, +rem_lb, +items, +bigs}:
          FH.drain5_go_append(gn, rest, ts2,
            SolveFast.drain5_swap(code, rem_lb, items, bigs, tbl,
              Array.swap(+List<SolveFast.CWord>, bkts, code, Nil{})))

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
          U32.is_eq(c, FF5.FF5.encode_fb5_list(f)), False{}, hne), {==})
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
                  SolveFast.FGroup{f, len, rws} <> Nil{}))), False{},
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

def FH.big_group(bc: SolveFast.BigClass) -> Groups.Group:
  match bc:
    case SolveFast.BigClass{fb, ws, len, _}:
      Groups.Group{fb, SolveFast.cwords_words(ws)}

def FH.bigs_groups(+bs: +List<SolveFast.BigClass>) -> +List<Groups.Group>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{bc, rest}:
      FH.big_group(bc) <> FH.bigs_groups(rest)

def FH.big_ok_b(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    bc: SolveFast.BigClass) -> Bool:
  match bc:
    case SolveFast.BigClass{fb, +ws, len, _}:
      Bool.and(FT.FT.cwords_ok_b(G, C, n_root, ws),
        Nat.is_eq(len, Groups.len_words(SolveFast.cwords_words(ws))))

def FH.bigs_ok_b(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +bs: +List<SolveFast.BigClass>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{bc, rest}:
      Bool.and(FH.big_ok_b(G, C, n_root, bc), FH.bigs_ok_b(G, C, n_root, rest))

def FH.insert_big_ok(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +bc: SolveFast.BigClass, +len: Nat, +bs: +List<SolveFast.BigClass>, le: Bool,
    +hbc: {FH.big_ok_b(G, C, n_root, bc) == True{} : Bool},
    +hbs: {FH.bigs_ok_b(G, C, n_root, bs) == True{} : Bool}) ->
  {FH.bigs_ok_b(G, C, n_root, SolveFast.insert_big(bc, len, bs, le))
   == True{} : Bool}:
  match bs:
    case Nil{}:
      FH.bool_and_intro(FH.big_ok_b(G, C, n_root, bc), True{}, hbc, {==})
    case Con{+h, +t}:
      match le:
        case True{}:
          FH.bool_and_intro(FH.big_ok_b(G, C, n_root, bc),
            FH.bigs_ok_b(G, C, n_root, h <> t), hbc, hbs)
        case False{}:
          +hh = Logic.Proof.and_true_l(FH.big_ok_b(G, C, n_root, h),
                  FH.bigs_ok_b(G, C, n_root, t), hbs)
          +ht = Logic.Proof.and_true_r(FH.big_ok_b(G, C, n_root, h),
                  FH.bigs_ok_b(G, C, n_root, t), hbs)
          FH.bool_and_intro(FH.big_ok_b(G, C, n_root, h),
            FH.bigs_ok_b(G, C, n_root,
              SolveFast.insert_big(bc, len, t, SolveFast.next_big_le(len, t))),
            hh,
            FH.insert_big_ok(G, C, n_root, bc, len, t,
              SolveFast.next_big_le(len, t), hbc, ht))

def FH.insert_big_perm(+bc: SolveFast.BigClass, +len: Nat,
    +bs: +List<SolveFast.BigClass>, le: Bool) -> FP.FP.Perm:
  match bs:
    case Nil{}:
      FP.PRefl{}
    case Con{h, t}:
      match le:
        case True{}:
          FP.PRefl{}
        case False{}:
          FP.PTrans{
            FH.big_group(h) <> (FH.big_group(bc) <> FH.bigs_groups(t)),
            FP.PSwap{},
            FP.PSkip{FH.insert_big_perm(bc, len, t,
              SolveFast.next_big_le(len, t))}}

def FH.insert_big_perm_ok(+bc: SolveFast.BigClass, +len: Nat,
    +bs: +List<SolveFast.BigClass>, le: Bool) ->
  FP.FP.PermOk(FH.insert_big_perm(bc, len, bs, le),
    FH.big_group(bc) <> FH.bigs_groups(bs),
    FH.bigs_groups(SolveFast.insert_big(bc, len, bs, le))):
  match bs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      match le:
        case True{}:
          {==}
        case False{}:
          Arr.DPair{
            Arr.DPair{{==}, Arr.DPair{{==}, {==}}},
            Arr.DPair{{==},
              FH.insert_big_perm_ok(bc, len, t, SolveFast.next_big_le(len, t))}}

def FH.perm_append_l(p: FP.FP.Perm, +zs: +List<Groups.Group>) -> FP.FP.Perm:
  match p:
    case FP.PRefl{}:
      FP.PRefl{}
    case FP.PSkip{pr}:
      FP.PSkip{FH.perm_append_l(pr, zs)}
    case FP.PSwap{}:
      FP.PSwap{}
    case FP.PTrans{mid, p1, p2}:
      FP.PTrans{List.append(&2, Groups.Group, mid, zs),
        FH.perm_append_l(p1, zs), FH.perm_append_l(p2, zs)}

def FH.perm_append_l_ok(p: FP.FP.Perm, +xs: +List<Groups.Group>,
    +ys: +List<Groups.Group>, +zs: +List<Groups.Group>,
    +ok: FP.FP.PermOk(p, xs, ys)) ->
  FP.FP.PermOk(FH.perm_append_l(p, zs),
    List.append(&2, Groups.Group, xs, zs),
    List.append(&2, Groups.Group, ys, zs)):
  match p:
    case FP.PRefl{}:
      Equal.cong(+List<Groups.Group>, +List<Groups.Group>,
        l => List.append(&2, Groups.Group, l, zs), xs, ys, ok)
    case FP.PSkip{pr}:
      match xs:
        case Nil{}:
          Empty.absurd(
            FP.FP.PermOk(FP.PSkip{FH.perm_append_l(pr, zs)}, zs,
              List.append(&2, Groups.Group, ys, zs)), ok)
        case Con{+hx, +tx}:
          match ys:
            case Nil{}:
              Empty.absurd(
                FP.FP.PermOk(FP.PSkip{FH.perm_append_l(pr, zs)},
                  hx <> List.append(&2, Groups.Group, tx, zs), zs), ok)
            case Con{+hy, +ty}:
              +eh = Arr.Arr.dpair_l({hx == hy : Groups.Group},
                      FP.FP.PermOk(pr, tx, ty), ok)
              +et = Arr.Arr.dpair_r({hx == hy : Groups.Group},
                      FP.FP.PermOk(pr, tx, ty), ok)
              Arr.DPair{eh, FH.perm_append_l_ok(pr, tx, ty, zs, et)}
    case FP.PSwap{}:
      match xs:
        case Nil{}:
          Empty.absurd(
            FP.FP.PermOk(FP.PSwap{}, zs,
              List.append(&2, Groups.Group, ys, zs)), ok)
        case Con{+a, +t1}:
          match t1:
            case Nil{}:
              Empty.absurd(
                FP.FP.PermOk(FP.PSwap{}, a <> zs,
                  List.append(&2, Groups.Group, ys, zs)), ok)
            case Con{+b, +tx}:
              match ys:
                case Nil{}:
                  Empty.absurd(
                    FP.FP.PermOk(FP.PSwap{},
                      a <> (b <> List.append(&2, Groups.Group, tx, zs)), zs), ok)
                case Con{+c, +t2}:
                  match t2:
                    case Nil{}:
                      Empty.absurd(
                        FP.FP.PermOk(FP.PSwap{},
                          a <> (b <> List.append(&2, Groups.Group, tx, zs)),
                          c <> zs), ok)
                    case Con{+d, +ty}:
                      +ead = Arr.Arr.dpair_l({a == d : Groups.Group},
                               Arr.Arr.DPair<{b == c : Groups.Group},
                                 {tx == ty : +List<Groups.Group>}>, ok)
                      +r1 = Arr.Arr.dpair_r({a == d : Groups.Group},
                              Arr.Arr.DPair<{b == c : Groups.Group},
                                {tx == ty : +List<Groups.Group>}>, ok)
                      +ebc = Arr.Arr.dpair_l({b == c : Groups.Group},
                               {tx == ty : +List<Groups.Group>}, r1)
                      +et = Arr.Arr.dpair_r({b == c : Groups.Group},
                              {tx == ty : +List<Groups.Group>}, r1)
                      Arr.DPair{ead, Arr.DPair{ebc,
                        Equal.cong(+List<Groups.Group>, +List<Groups.Group>,
                          l => List.append(&2, Groups.Group, l, zs), tx, ty, et)}}
    case FP.PTrans{+mid, p1, p2}:
      +ok1 = Arr.Arr.dpair_l(FP.FP.PermOk(p1, xs, mid),
               FP.FP.PermOk(p2, mid, ys), ok)
      +ok2 = Arr.Arr.dpair_r(FP.FP.PermOk(p1, xs, mid),
               FP.FP.PermOk(p2, mid, ys), ok)
      Arr.DPair{
        FH.perm_append_l_ok(p1, xs, mid, zs, ok1),
        FH.perm_append_l_ok(p2, mid, ys, zs, ok2)}

def FH.emit_bigs_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +n_orig: Nat, +bs: +List<SolveFast.BigClass>,
    +rem_lb: Nat, +items: +List<SolveFast.Item>, +ig: +List<Groups.Group>,
    +hbs: {FH.bigs_ok_b(G, C, n_root, bs) == True{} : Bool},
    +hbm: FH.BodyMatch(G, C, n_root, True{}, True{}, n_orig, ig, items),
    +elb: {rem_lb == FH.body_lb(True{}, n_orig, items) : Nat}) ->
  FH.BodyMatch(G, C, n_root, True{}, True{}, n_orig,
    FP.FP.rev_groups(FH.bigs_groups(bs), ig),
    SolveFast.emit_bigs(bs, rem_lb, items)):
  match bs:
    case Nil{}:
      hbm
    case Con{bc, +rest}:
      match bc:
        case SolveFast.BigClass{+fb, +ws, +len, _}:
          +bcv : SolveFast.BigClass =
            SolveFast.BigClass{fb, ws, len, Nat.sub(Nat.add(len, len), 1n)}
          +hbc = Logic.Proof.and_true_l(
                   FH.big_ok_b(G, C, n_root, bcv),
                   FH.bigs_ok_b(G, C, n_root, rest), hbs)
          +hrest = Logic.Proof.and_true_r(
                     FH.big_ok_b(G, C, n_root, bcv),
                     FH.bigs_ok_b(G, C, n_root, rest), hbs)
          +hcws = Logic.Proof.and_true_l(
                    FT.FT.cwords_ok_b(G, C, n_root, ws),
                    Nat.is_eq(len, Groups.len_words(SolveFast.cwords_words(ws))),
                    hbc)
          +elen = NatProof.NatPrf.is_eq_true(len,
                    Groups.len_words(SolveFast.cwords_words(ws)),
                    Logic.Proof.and_true_r(
                      FT.FT.cwords_ok_b(G, C, n_root, ws),
                      Nat.is_eq(len, Groups.len_words(SolveFast.cwords_words(ws))),
                      hbc))
          +clb = Nat.sub(Nat.add(len, len), 1n)
          +items2 : +List<SolveFast.Item> =
            SolveFast.ClassItem{fb, ws, len, rem_lb}
            <> (SolveFast.Add{fb, rem_lb} <> items)
          +ig2 : +List<Groups.Group> =
            Groups.Group{fb, SolveFast.cwords_words(ws)} <> ig
          +hbm2 : FH.BodyMatch(G, C, n_root, True{}, True{}, n_orig, ig2, items2) =
            Arr.DPair{{==}, Arr.DPair{{==}, Arr.DPair{{==}, Arr.DPair{elen,
              Arr.DPair{hcws, Arr.DPair{elb, Arr.DPair{{==}, hbm}}}}}}}
          +elb2 : {Nat.add(clb, rem_lb) == FH.body_lb(True{}, n_orig, items2)
                   : Nat} =
            Equal.cong(Nat, Nat, x => Nat.add(clb, x),
              rem_lb, FH.body_lb(True{}, n_orig, items), elb)
          FH.emit_bigs_spec(G, C, n_root, n_orig, rest, Nat.add(clb, rem_lb),
            items2, ig2, hrest, hbm2, elb2)

def FH.len_rev_words(+xs: +List<+List<Nat>>, +acc: +List<+List<Nat>>) ->
  {Groups.len_words(SolveFast.rev_words(xs, acc))
   == Nat.add(Groups.len_words(xs), Groups.len_words(acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      Equal.trans(Nat,
        Groups.len_words(SolveFast.rev_words(t, w <> acc)),
        Nat.add(Groups.len_words(t), 1n+Groups.len_words(acc)),
        1n+Nat.add(Groups.len_words(t), Groups.len_words(acc)),
        FH.len_rev_words(t, w <> acc),
        NatProof.NatPrf.add_succ(Groups.len_words(t), Groups.len_words(acc)))

type FH.DrainWit<+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +fg: +List<SolveFast.FGroup>, +n_orig: Nat,
    +ig0: +List<Groups.Group>, +bigs0: +List<SolveFast.BigClass>,
    +lb2: Nat, +items2: +List<SolveFast.Item>,
    +bigs2: +List<SolveFast.BigClass>> is Data:
  DWit{ig: +List<Groups.Group>,
       perm: FP.FP.Perm,
       hok_bigs: {FH.bigs_ok_b(G, C, n_root, bigs2) == True{} : Bool},
       hbm: FH.BodyMatch(G, C, n_root, True{}, True{}, n_orig, ig, items2),
       elb: {lb2 == FH.body_lb(True{}, n_orig, items2) : Nat},
       hperm: FP.FP.PermOk(perm,
                List.append(&2, Groups.Group, FN.FN.fgroups_to_groups(fg),
                  List.append(&2, Groups.Group, FH.bigs_groups(bigs0), ig0)),
                List.append(&2, Groups.Group, FH.bigs_groups(bigs2), ig))}

def FH.DrainSpec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +pre: +List<SolveFast.FGroup>, +fg: +List<SolveFast.FGroup>,
    +n_orig: Nat, +ig0: +List<Groups.Group>, +bigs0: +List<SolveFast.BigClass>,
    -tbl0: Array<U32>, dr: SolveFast.Drain5State) -> Data:
  match dr:
    case SolveFast.Drain5State{bkts, tbl, lb, items, bigs}:
      Arr.Arr.DPair<
        FH.BktTree(G, C, n_root, 10n, 0, bkts, pre),
        Arr.Arr.DPair<
          {tbl == tbl0 : Array<U32>},
          FH.DrainWit<G, C, n_root, fg, n_orig, ig0, bigs0, lb, items, bigs>>>

def FH.drain_spec_transport(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +pre: +List<SolveFast.FGroup>, +fg: +List<SolveFast.FGroup>,
    +n_orig: Nat, +ig0: +List<Groups.Group>, +bigs0: +List<SolveFast.BigClass>,
    -tbl0: Array<U32>,
    -d1: SolveFast.Drain5State, -d2: SolveFast.Drain5State,
    +ed: {d1 == d2 : SolveFast.Drain5State},
    +h: FH.DrainSpec(G, C, n_root, pre, fg, n_orig, ig0, bigs0, tbl0, d1)) ->
  FH.DrainSpec(G, C, n_root, pre, fg, n_orig, ig0, bigs0, tbl0, d2):
  %ed : FH.DrainSpec(G, C, n_root, pre, fg, n_orig, ig0, bigs0, tbl0, _)
  h

def FH.drain_spec_transport_tbl(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +pre: +List<SolveFast.FGroup>, +fg: +List<SolveFast.FGroup>,
    +n_orig: Nat, +ig0: +List<Groups.Group>, +bigs0: +List<SolveFast.BigClass>,
    -t1: Array<U32>, -t2: Array<U32>, -d: SolveFast.Drain5State,
    +et: {t1 == t2 : Array<U32>},
    +h: FH.DrainSpec(G, C, n_root, pre, fg, n_orig, ig0, bigs0, t1, d)) ->
  FH.DrainSpec(G, C, n_root, pre, fg, n_orig, ig0, bigs0, t2, d):
  %et : FH.DrainSpec(G, C, n_root, pre, fg, n_orig, ig0, bigs0, _, d)
  h

def FH.drain_perm_item(+gp: Groups.Group, +fg_rest: +List<Groups.Group>,
    +base: +List<Groups.Group>, +bs: +List<Groups.Group>,
    +ig: +List<Groups.Group>, +perm1: FP.FP.Perm,
    +hp1: FP.FP.PermOk(perm1, List.append(&2, Groups.Group, fg_rest, base),
            List.append(&2, Groups.Group, bs, ig))) ->
  FP.FP.PermOk(
    FP.PTrans{gp <> List.append(&2, Groups.Group, bs, ig),
      FP.PSkip{perm1}, FP.FP.perm_sym(FP.FP.perm_pull(gp, bs, ig))},
    gp <> List.append(&2, Groups.Group, fg_rest, base),
    List.append(&2, Groups.Group, bs, gp <> ig)):
  Arr.DPair{
    Arr.DPair{{==}, hp1},
    FP.FP.perm_sym_ok(FP.FP.perm_pull(gp, bs, ig),
      List.append(&2, Groups.Group, bs, gp <> ig),
      gp <> List.append(&2, Groups.Group, bs, ig),
      FP.FP.perm_pull_ok(gp, bs, ig))}

def FH.drain5_add_three_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +n_orig: Nat, +ig0: +List<Groups.Group>,
    +bigs0: +List<SolveFast.BigClass>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    +bigs2: +List<SolveFast.BigClass>, -bkts3: Array<+List<SolveFast.CWord>>,
    -tbl0: Array<U32>, -tbl2: Array<U32>,
    +w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    tr: SolveFast.ThreeRes,
    +edec: {SolveFast.decode_fb5(FF5.FF5.encode_fb5_list(f)) == f
            : +List<Feedback.Color>},
    +ews: {SolveFast.rev_words(rws, Nil{}) == w1 <> (w2 <> (w3 <> Nil{}))
           : +List<+List<Nat>>},
    +hb3: FH.BktTree(G, C, n_root, 10n, 0, bkts3, pre),
    +etbl2: {tbl2 == tbl0 : Array<U32>},
    +htr: FT3.FT3.ThreeSpec(G, w1, w2, w3, tbl2, tr),
    +dw1: FH.DrainWit<G, C, n_root, rest, n_orig, ig0, bigs0, lb2, items2, bigs2>) ->
  FH.DrainSpec(G, C, n_root, pre, SolveFast.FGroup{f, len, rws} <> rest,
    n_orig, ig0, bigs0, tbl0,
    SolveFast.drain5_add_three(SolveFast.decode_fb5(FF5.FF5.encode_fb5_list(f)),
      lb2, items2, bigs2, bkts3, tr)):
  match tr:
    case SolveFast.ThreeRes{+tree, +cost, tbl3}:
      match dw1:
        case DWit{+ig1, +perm1, +hok_bigs1, +hbm1, +elb1, +hperm1}:
          +et32 = Arr.Arr.dpair_l({tbl3 == tbl2 : Array<U32>},
                    {FT3.FT3.done_three_ok_b(G, w1, w2, w3, tree, cost) == True{} : Bool},
                    htr)
          +hd3 = Arr.Arr.dpair_r({tbl3 == tbl2 : Array<U32>},
                   {FT3.FT3.done_three_ok_b(G, w1, w2, w3, tree, cost) == True{} : Bool},
                   htr)
          +gp_g : Groups.Group = Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
          +base = List.append(&2, Groups.Group, FH.bigs_groups(bigs0), ig0)
          +bs_g = FH.bigs_groups(bigs2)
          +hdws : {FH.done_ws_ok_b(G, SolveFast.rev_words(rws, Nil{}), tree, cost)
                   == True{} : Bool} =
            Equal.trans(Bool,
              FH.done_ws_ok_b(G, SolveFast.rev_words(rws, Nil{}), tree, cost),
              FT3.FT3.done_three_ok_b(G, w1, w2, w3, tree, cost), True{},
              Equal.cong(+List<+List<Nat>>, Bool,
                ws => FH.done_ws_ok_b(G, ws, tree, cost),
                SolveFast.rev_words(rws, Nil{}), w1 <> (w2 <> (w3 <> Nil{})),
                ews),
              hd3)
          +hbm2 : FH.BodyMatch(G, C, n_root, True{}, True{}, n_orig,
                    gp_g <> ig1,
                    SolveFast.DoneItem{
                      SolveFast.decode_fb5(FF5.FF5.encode_fb5_list(f)),
                      tree, cost} <> items2) =
            Arr.DPair{{==}, Arr.DPair{edec, Arr.DPair{hdws, hbm1}}}
          +elb2 : {Nat.add(cost, lb2)
                   == FH.body_lb(True{}, n_orig,
                        SolveFast.DoneItem{
                          SolveFast.decode_fb5(FF5.FF5.encode_fb5_list(f)),
                          tree, cost} <> items2) : Nat} =
            Equal.cong(Nat, Nat, x => Nat.add(cost, x),
              lb2, FH.body_lb(True{}, n_orig, items2), elb1)
          Arr.DPair{hb3, Arr.DPair{
            Equal.trans(Array<U32>, tbl3, tbl2, tbl0, et32, etbl2),
            DWit{gp_g <> ig1,
              FP.PTrans{gp_g <> List.append(&2, Groups.Group, bs_g, ig1),
                FP.PSkip{perm1},
                FP.FP.perm_sym(FP.FP.perm_pull(gp_g, bs_g, ig1))},
              hok_bigs1, hbm2, elb2,
              FH.drain_perm_item(gp_g, FN.FN.fgroups_to_groups(rest), base,
                bs_g, ig1, perm1, hperm1)}}}

def FH.drain5_add_ge4_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +n_orig: Nat, +ig0: +List<Groups.Group>,
    +bigs0: +List<SolveFast.BigClass>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    +bigs2: +List<SolveFast.BigClass>, -bkts3: Array<+List<SolveFast.CWord>>,
    -tbl0: Array<U32>, -tbl2: Array<U32>,
    rl: SolveFast.RevCWordsLen,
    +edec: {SolveFast.decode_fb5(FF5.FF5.encode_fb5_list(f)) == f
            : +List<Feedback.Color>},
    +ews: {SolveFast.cwords_words(FT.FT.rev_cwords_ws(rl))
           == SolveFast.rev_words(rws, Nil{}) : +List<+List<Nat>>},
    +elen: {FT.FT.rev_cwords_len_val(rl)
            == Groups.len_words(SolveFast.cwords_words(FT.FT.rev_cwords_ws(rl)))
            : Nat},
    +hcws: {FT.FT.cwords_ok_b(G, C, n_root, FT.FT.rev_cwords_ws(rl))
            == True{} : Bool},
    +hb3: FH.BktTree(G, C, n_root, 10n, 0, bkts3, pre),
    +etbl2: {tbl2 == tbl0 : Array<U32>},
    +dw1: FH.DrainWit<G, C, n_root, rest, n_orig, ig0, bigs0, lb2, items2, bigs2>) ->
  FH.DrainSpec(G, C, n_root, pre, SolveFast.FGroup{f, len, rws} <> rest,
    n_orig, ig0, bigs0, tbl0,
    SolveFast.drain5_add_ge2(SolveFast.decode_fb5(FF5.FF5.encode_fb5_list(f)),
      lb2, items2, bigs2, bkts3, tbl2, rl)):
  match rl:
    case SolveFast.RevCWordsLen{+rlen, +ws}:
      match dw1:
        case DWit{+ig1, +perm1, +hok_bigs1, +hbm1, +elb1, +hperm1}:
          +fdec = SolveFast.decode_fb5(FF5.FF5.encode_fb5_list(f))
          +bc : SolveFast.BigClass =
            SolveFast.BigClass{fdec, ws, rlen,
              Nat.sub(Nat.add(rlen, rlen), 1n)}
          +le0 = SolveFast.next_big_le(rlen, bigs2)
          +bigs3 = SolveFast.insert_big(bc, rlen, bigs2, le0)
          +hbc : {FH.big_ok_b(G, C, n_root, bc) == True{} : Bool} =
            FH.bool_and_intro(FT.FT.cwords_ok_b(G, C, n_root, ws),
              Nat.is_eq(rlen, Groups.len_words(SolveFast.cwords_words(ws))),
              hcws,
              Equal.trans(Bool,
                Nat.is_eq(rlen, Groups.len_words(SolveFast.cwords_words(ws))),
                Nat.is_eq(Groups.len_words(SolveFast.cwords_words(ws)),
                  Groups.len_words(SolveFast.cwords_words(ws))),
                True{},
                Equal.cong(Nat, Bool, x => Nat.is_eq(x,
                  Groups.len_words(SolveFast.cwords_words(ws))),
                  rlen, Groups.len_words(SolveFast.cwords_words(ws)), elen),
                NatProof.NatPrf.is_eq_refl(
                  Groups.len_words(SolveFast.cwords_words(ws)))))
          +hok_bigs3 = FH.insert_big_ok(G, C, n_root, bc, rlen, bigs2, le0,
                         hbc, hok_bigs1)
          +gp_g : Groups.Group = Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
          +egp : {gp_g == FH.big_group(bc) : Groups.Group} =
            Equal.trans(Groups.Group,
              Groups.Group{f, SolveFast.rev_words(rws, Nil{})},
              Groups.Group{fdec, SolveFast.rev_words(rws, Nil{})},
              Groups.Group{fdec, SolveFast.cwords_words(ws)},
              Equal.cong(+List<Feedback.Color>, Groups.Group,
                x => Groups.Group{x, SolveFast.rev_words(rws, Nil{})},
                f, fdec,
                Equal.sym(+List<Feedback.Color>, fdec, f, edec)),
              Equal.cong(+List<+List<Nat>>, Groups.Group,
                y => Groups.Group{fdec, y},
                SolveFast.rev_words(rws, Nil{}), SolveFast.cwords_words(ws),
                Equal.sym(+List<+List<Nat>>, SolveFast.cwords_words(ws),
                  SolveFast.rev_words(rws, Nil{}), ews)))
          +base = List.append(&2, Groups.Group, FH.bigs_groups(bigs0), ig0)
          +pins = FH.insert_big_perm(bc, rlen, bigs2, le0)
          +hp_ins = FH.insert_big_perm_ok(bc, rlen, bigs2, le0)
          +hp_app = FH.perm_append_l_ok(pins,
                      FH.big_group(bc) <> FH.bigs_groups(bigs2),
                      FH.bigs_groups(bigs3), ig1, hp_ins)
          +mid : +List<Groups.Group> =
            FH.big_group(bc) <> List.append(&2, Groups.Group,
              FH.bigs_groups(bigs2), ig1)
          +hp_all : FP.FP.PermOk(
                      FP.PTrans{mid, FP.PSkip{perm1},
                        FH.perm_append_l(pins, ig1)},
                      gp_g <> List.append(&2, Groups.Group,
                        FN.FN.fgroups_to_groups(rest), base),
                      List.append(&2, Groups.Group, FH.bigs_groups(bigs3), ig1)) =
            Arr.DPair{Arr.DPair{egp, hperm1}, hp_app}
          Arr.DPair{hb3, Arr.DPair{etbl2,
            DWit{ig1,
              FP.PTrans{mid, FP.PSkip{perm1}, FH.perm_append_l(pins, ig1)},
              hok_bigs3, hbm1, elb1, hp_all}}}

def FH.drain5_add_three_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +n_orig: Nat, +ig0: +List<Groups.Group>,
    +bigs0: +List<SolveFast.BigClass>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    +bigs2: +List<SolveFast.BigClass>, -bkts3: Array<+List<SolveFast.CWord>>,
    -tbl0: Array<U32>, -tbl2: Array<U32>,
    +cw3: SolveFast.CWord, +cw2: SolveFast.CWord, +cw: SolveFast.CWord,
    +edec: {SolveFast.decode_fb5(FF5.FF5.encode_fb5_list(f)) == f
            : +List<Feedback.Color>},
    +ews: {SolveFast.rev_words(rws, Nil{})
           == SolveFast.cword_w(cw3)
              <> (SolveFast.cword_w(cw2) <> (SolveFast.cword_w(cw) <> Nil{}))
           : +List<+List<Nat>>},
    +hcw3: {FT.FT.cword_ok_b(G, C, n_root, cw3) == True{} : Bool},
    +hcw2: {FT.FT.cword_ok_b(G, C, n_root, cw2) == True{} : Bool},
    +hcw1: {FT.FT.cword_ok_b(G, C, n_root, cw) == True{} : Bool},
    +nd3: {FN.FN.no_dup_ref(SolveFast.cword_w(cw3)
             <> (SolveFast.cword_w(cw2) <> (SolveFast.cword_w(cw) <> Nil{})))
           == True{} : Bool},
    +hb3: FH.BktTree(G, C, n_root, 10n, 0, bkts3, pre),
    +htbl2: FT.FT.TblOk(G, C, n_root, tbl2),
    +etbl2: {tbl2 == tbl0 : Array<U32>},
    +dw1: FH.DrainWit<G, C, n_root, rest, n_orig, ig0, bigs0, lb2, items2, bigs2>,
    dt: &t1: Array<U32> -> &t2: Array<U32> ->
        {t1 == tbl2 : Array<U32>} & {t2 == t1 : Array<U32>}) ->
  FH.DrainSpec(G, C, n_root, pre, SolveFast.FGroup{f, len, rws} <> rest,
    n_orig, ig0, bigs0, tbl0,
    SolveFast.drain5_add_three(SolveFast.decode_fb5(FF5.FF5.encode_fb5_list(f)),
      lb2, items2, bigs2, bkts3,
      SolveFast.solve_three_tbl(cw3, cw2, cw, tbl2))):
  (t1, dt2) = dt
  (t2, pe) = dt2
  (+et1, +et2) = pe
  +et2_tbl2 : {t2 == tbl2 : Array<U32>} =
    Equal.trans(Array<U32>, t2, t1, tbl2, et2, et1)
  +ht2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl2, t2,
           Equal.sym(Array<U32>, t2, tbl2, et2_tbl2), htbl2)
  +htr2 = FT3.FT3.solve_three_tbl_ok(G, C, n_root, cw3, cw2, cw, t2,
            ht2, hcw3, hcw2, hcw1, nd3)
  +etr21 : {SolveFast.solve_three_tbl(cw3, cw2, cw, t2)
            == SolveFast.solve_three_tbl(cw3, cw2, cw, t1)
            : SolveFast.ThreeRes} =
    Equal.cong(Array<U32>, SolveFast.ThreeRes,
      t => SolveFast.solve_three_tbl(cw3, cw2, cw, t), t2, t1, et2)
  +htr1a : FT3.FT3.ThreeSpec(G, SolveFast.cword_w(cw3), SolveFast.cword_w(cw2),
             SolveFast.cword_w(cw), t2,
             SolveFast.solve_three_tbl(cw3, cw2, cw, t1)) =
    %etr21 : FT3.FT3.ThreeSpec(G, SolveFast.cword_w(cw3), SolveFast.cword_w(cw2),
               SolveFast.cword_w(cw), t2, _)
    htr2
  +htr1 = FT3.FT3.three_spec_transport_tbl(G, SolveFast.cword_w(cw3),
            SolveFast.cword_w(cw2), SolveFast.cword_w(cw), t2, t1,
            SolveFast.solve_three_tbl(cw3, cw2, cw, t1), et2, htr1a)
  +et1_0 : {t1 == tbl0 : Array<U32>} =
    Equal.trans(Array<U32>, t1, tbl2, tbl0, et1, etbl2)
  %et1 : FH.DrainSpec(G, C, n_root, pre, SolveFast.FGroup{f, len, rws} <> rest,
           n_orig, ig0, bigs0, tbl0,
           SolveFast.drain5_add_three(
             SolveFast.decode_fb5(FF5.FF5.encode_fb5_list(f)),
             lb2, items2, bigs2, bkts3,
             SolveFast.solve_three_tbl(cw3, cw2, cw, _)))
  FH.drain5_add_three_spec(G, C, n_root, pre, f, len, rws, rest, n_orig, ig0,
    bigs0, lb2, items2, bigs2, bkts3, tbl0, t1,
    SolveFast.cword_w(cw3), SolveFast.cword_w(cw2), SolveFast.cword_w(cw),
    SolveFast.solve_three_tbl(cw3, cw2, cw, t1),
    edec, ews, hb3, et1_0, htr1, dw1)

def FH.drain5_add_spec_go(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +n_orig: Nat, +ig0: +List<Groups.Group>,
    +bigs0: +List<SolveFast.BigClass>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    +bigs2: +List<SolveFast.BigClass>, -bkts3: Array<+List<SolveFast.CWord>>,
    -tbl0: Array<U32>, tbl2: Array<U32>, +rws_cw: +List<SolveFast.CWord>,
    +edec: {SolveFast.decode_fb5(FF5.FF5.encode_fb5_list(f)) == f
            : +List<Feedback.Color>},
    +hnd_gp: {FN.FN.no_dup_ref(SolveFast.rev_words(rws, Nil{})) == True{} : Bool},
    +erws: {SolveFast.cwords_words(rws_cw) == rws : +List<+List<Nat>>},
    +hcws: {FT.FT.cwords_ok_b(G, C, n_root, rws_cw) == True{} : Bool},
    +hb3: FH.BktTree(G, C, n_root, 10n, 0, bkts3, pre),
    +htbl2: FT.FT.TblOk(G, C, n_root, tbl2),
    +etbl2: {tbl2 == tbl0 : Array<U32>},
    +dw1: FH.DrainWit<G, C, n_root, rest, n_orig, ig0, bigs0, lb2, items2, bigs2>) ->
  FH.DrainSpec(G, C, n_root, pre, SolveFast.FGroup{f, len, rws} <> rest,
    n_orig, ig0, bigs0, tbl0,
    SolveFast.drain5_add(FF5.FF5.encode_fb5_list(f), lb2, items2, bigs2,
      bkts3, tbl2, rws_cw)):
  match rws_cw:
    case Nil{}:
      match dw1:
        case DWit{+ig1, +perm1, +hok_bigs1, +hbm1, +elb1, +hperm1}:
          +fdec = SolveFast.decode_fb5(FF5.FF5.encode_fb5_list(f))
          +gp_g : Groups.Group = Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
          +ews : {Nil{} == SolveFast.rev_words(rws, Nil{}) : +List<+List<Nat>>} =
            Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
              xs => SolveFast.rev_words(xs, Nil{}), Nil{}, rws, erws)
          +it_new : +List<SolveFast.Item> =
            SolveFast.ClassItem{fdec, Nil{}, 0n, lb2}
            <> (SolveFast.Add{fdec, lb2} <> items2)
          +hbm2 : FH.BodyMatch(G, C, n_root, True{}, True{}, n_orig,
                    gp_g <> ig1, it_new) =
            Arr.DPair{edec, Arr.DPair{edec, Arr.DPair{ews,
              Arr.DPair{
                Equal.cong(+List<+List<Nat>>, Nat, xs => Groups.len_words(xs),
                  Nil{}, SolveFast.rev_words(rws, Nil{}), ews),
                Arr.DPair{{==}, Arr.DPair{elb1, Arr.DPair{{==}, hbm1}}}}}}}
          +base = List.append(&2, Groups.Group, FH.bigs_groups(bigs0), ig0)
          +bs_g = FH.bigs_groups(bigs2)
          Arr.DPair{hb3, Arr.DPair{etbl2,
            DWit{gp_g <> ig1,
              FP.PTrans{gp_g <> List.append(&2, Groups.Group, bs_g, ig1),
                FP.PSkip{perm1},
                FP.FP.perm_sym(FP.FP.perm_pull(gp_g, bs_g, ig1))},
              hok_bigs1, hbm2, elb1,
              FH.drain_perm_item(gp_g, FN.FN.fgroups_to_groups(rest), base,
                bs_g, ig1, perm1, hperm1)}}}
    case Con{+cw, +wt}:
      match wt:
        case Nil{}:
          match dw1:
            case DWit{+ig1, +perm1, +hok_bigs1, +hbm1, +elb1, +hperm1}:
              +fdec = SolveFast.decode_fb5(FF5.FF5.encode_fb5_list(f))
              +w = SolveFast.cword_w(cw)
              +gp_g : Groups.Group = Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
              +erws1 : {w <> Nil{} == rws : +List<+List<Nat>>} =
                Equal.trans(+List<+List<Nat>>, w <> Nil{},
                  SolveFast.cwords_words(cw <> Nil{}), rws,
                  Equal.sym(+List<+List<Nat>>,
                    SolveFast.cwords_words(cw <> Nil{}), w <> Nil{},
                    FH.cwords_words_cons(cw, Nil{})), erws)
              +ews : {SolveFast.rev_words(rws, Nil{}) == w <> Nil{}
                      : +List<+List<Nat>>} =
                Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                  xs => SolveFast.rev_words(xs, Nil{}), rws, w <> Nil{},
                  Equal.sym(+List<+List<Nat>>, w <> Nil{}, rws, erws1))
              +it_new : +List<SolveFast.Item> =
                SolveFast.OneItem{fdec, w} <> items2
              +hbm2 : FH.BodyMatch(G, C, n_root, True{}, True{}, n_orig,
                        gp_g <> ig1, it_new) =
                Arr.DPair{edec, Arr.DPair{ews, hbm1}}
              +elb2 : {Nat.add(1n, lb2) == FH.body_lb(True{}, n_orig, it_new)
                       : Nat} =
                Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                  lb2, FH.body_lb(True{}, n_orig, items2), elb1)
              +base = List.append(&2, Groups.Group, FH.bigs_groups(bigs0), ig0)
              +bs_g = FH.bigs_groups(bigs2)
              Arr.DPair{hb3, Arr.DPair{etbl2,
                DWit{gp_g <> ig1,
                  FP.PTrans{gp_g <> List.append(&2, Groups.Group, bs_g, ig1),
                    FP.PSkip{perm1},
                    FP.FP.perm_sym(FP.FP.perm_pull(gp_g, bs_g, ig1))},
                  hok_bigs1, hbm2, elb2,
                  FH.drain_perm_item(gp_g, FN.FN.fgroups_to_groups(rest), base,
                    bs_g, ig1, perm1, hperm1)}}}
        case Con{+cw2, +wt2}:
          match wt2:
            case Nil{}:
              match dw1:
                case DWit{+ig1, +perm1, +hok_bigs1, +hbm1, +elb1, +hperm1}:
                  +fdec = SolveFast.decode_fb5(FF5.FF5.encode_fb5_list(f))
                  +w = SolveFast.cword_w(cw)
                  +w2 = SolveFast.cword_w(cw2)
                  +gp_g : Groups.Group = Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
                  +erws2 : {w <> (w2 <> Nil{}) == rws : +List<+List<Nat>>} =
                    Equal.trans(+List<+List<Nat>>, w <> (w2 <> Nil{}),
                      SolveFast.cwords_words(cw <> (cw2 <> Nil{})), rws,
                      Equal.sym(+List<+List<Nat>>,
                        SolveFast.cwords_words(cw <> (cw2 <> Nil{})),
                        w <> (w2 <> Nil{}),
                        Equal.trans(+List<+List<Nat>>,
                          SolveFast.cwords_words(cw <> (cw2 <> Nil{})),
                          w <> SolveFast.cwords_words(cw2 <> Nil{}),
                          w <> (w2 <> Nil{}),
                          FH.cwords_words_cons(cw, cw2 <> Nil{}),
                          Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                            l => w <> l, SolveFast.cwords_words(cw2 <> Nil{}),
                            w2 <> Nil{}, FH.cwords_words_cons(cw2, Nil{})))),
                      erws)
                  +ews : {SolveFast.rev_words(rws, Nil{}) == w2 <> (w <> Nil{})
                          : +List<+List<Nat>>} =
                    Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                      xs => SolveFast.rev_words(xs, Nil{}),
                      rws, w <> (w2 <> Nil{}),
                      Equal.sym(+List<+List<Nat>>, w <> (w2 <> Nil{}), rws, erws2))
                  +it_new : +List<SolveFast.Item> =
                    SolveFast.TwoItem{fdec, w2, w} <> items2
                  +hbm2 : FH.BodyMatch(G, C, n_root, True{}, True{}, n_orig,
                            gp_g <> ig1, it_new) =
                    Arr.DPair{{==}, Arr.DPair{edec, Arr.DPair{ews, hbm1}}}
                  +elb2 : {Nat.add(3n, lb2) == FH.body_lb(True{}, n_orig, it_new)
                           : Nat} =
                    Equal.cong(Nat, Nat, x => Nat.add(3n, x),
                      lb2, FH.body_lb(True{}, n_orig, items2), elb1)
                  +base = List.append(&2, Groups.Group, FH.bigs_groups(bigs0), ig0)
                  +bs_g = FH.bigs_groups(bigs2)
                  Arr.DPair{hb3, Arr.DPair{etbl2,
                    DWit{gp_g <> ig1,
                      FP.PTrans{gp_g <> List.append(&2, Groups.Group, bs_g, ig1),
                        FP.PSkip{perm1},
                        FP.FP.perm_sym(FP.FP.perm_pull(gp_g, bs_g, ig1))},
                      hok_bigs1, hbm2, elb2,
                      FH.drain_perm_item(gp_g, FN.FN.fgroups_to_groups(rest),
                        base, bs_g, ig1, perm1, hperm1)}}}
            case Con{+cw3, +wt3}:
              match wt3:
                case Nil{}:
                  +w = SolveFast.cword_w(cw)
                  +w2 = SolveFast.cword_w(cw2)
                  +w3 = SolveFast.cword_w(cw3)
                  +hcw1 = Logic.Proof.and_true_l(
                            FT.FT.cword_ok_b(G, C, n_root, cw),
                            FT.FT.cwords_ok_b(G, C, n_root, cw2 <> (cw3 <> Nil{})),
                            hcws)
                  +hr1 = Logic.Proof.and_true_r(
                           FT.FT.cword_ok_b(G, C, n_root, cw),
                           FT.FT.cwords_ok_b(G, C, n_root, cw2 <> (cw3 <> Nil{})),
                           hcws)
                  +hcw2 = Logic.Proof.and_true_l(
                            FT.FT.cword_ok_b(G, C, n_root, cw2),
                            FT.FT.cwords_ok_b(G, C, n_root, cw3 <> Nil{}), hr1)
                  +hr2 = Logic.Proof.and_true_r(
                           FT.FT.cword_ok_b(G, C, n_root, cw2),
                           FT.FT.cwords_ok_b(G, C, n_root, cw3 <> Nil{}), hr1)
                  +hcw3 = Logic.Proof.and_true_l(
                            FT.FT.cword_ok_b(G, C, n_root, cw3), True{}, hr2)
                  +erws3 : {w <> (w2 <> (w3 <> Nil{})) == rws : +List<+List<Nat>>} =
                    Equal.trans(+List<+List<Nat>>, w <> (w2 <> (w3 <> Nil{})),
                      SolveFast.cwords_words(cw <> (cw2 <> (cw3 <> Nil{}))), rws,
                      Equal.sym(+List<+List<Nat>>,
                        SolveFast.cwords_words(cw <> (cw2 <> (cw3 <> Nil{}))),
                        w <> (w2 <> (w3 <> Nil{})),
                        Equal.trans(+List<+List<Nat>>,
                          SolveFast.cwords_words(cw <> (cw2 <> (cw3 <> Nil{}))),
                          w <> SolveFast.cwords_words(cw2 <> (cw3 <> Nil{})),
                          w <> (w2 <> (w3 <> Nil{})),
                          FH.cwords_words_cons(cw, cw2 <> (cw3 <> Nil{})),
                          Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                            l => w <> l,
                            SolveFast.cwords_words(cw2 <> (cw3 <> Nil{})),
                            w2 <> (w3 <> Nil{}),
                            Equal.trans(+List<+List<Nat>>,
                              SolveFast.cwords_words(cw2 <> (cw3 <> Nil{})),
                              w2 <> SolveFast.cwords_words(cw3 <> Nil{}),
                              w2 <> (w3 <> Nil{}),
                              FH.cwords_words_cons(cw2, cw3 <> Nil{}),
                              Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                                l2 => w2 <> l2,
                                SolveFast.cwords_words(cw3 <> Nil{}), w3 <> Nil{},
                                FH.cwords_words_cons(cw3, Nil{})))))), erws)
                  +ews : {SolveFast.rev_words(rws, Nil{})
                          == w3 <> (w2 <> (w <> Nil{})) : +List<+List<Nat>>} =
                    Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                      xs => SolveFast.rev_words(xs, Nil{}),
                      rws, w <> (w2 <> (w3 <> Nil{})),
                      Equal.sym(+List<+List<Nat>>, w <> (w2 <> (w3 <> Nil{})),
                        rws, erws3))
                  +nd3 : {FN.FN.no_dup_ref(w3 <> (w2 <> (w <> Nil{})))
                          == True{} : Bool} =
                    Equal.trans(Bool,
                      FN.FN.no_dup_ref(w3 <> (w2 <> (w <> Nil{}))),
                      FN.FN.no_dup_ref(SolveFast.rev_words(rws, Nil{})), True{},
                      Equal.cong(+List<+List<Nat>>, Bool,
                        xs => FN.FN.no_dup_ref(xs),
                        w3 <> (w2 <> (w <> Nil{})),
                        SolveFast.rev_words(rws, Nil{}),
                        Equal.sym(+List<+List<Nat>>,
                          SolveFast.rev_words(rws, Nil{}),
                          w3 <> (w2 <> (w <> Nil{})), ews)), hnd_gp)
                  FH.drain5_add_three_dup(G, C, n_root, pre, f, len, rws, rest,
                    n_orig, ig0, bigs0, lb2, items2, bigs2, bkts3, tbl0, tbl2,
                    cw3, cw2, cw, edec, ews, hcw3, hcw2, hcw1, nd3, hb3, htbl2,
                    etbl2, dw1, Arr.Arr.dup(U32, tbl2))
                case Con{+cw4, +wt4}:
                  +hcw1 = Logic.Proof.and_true_l(
                            FT.FT.cword_ok_b(G, C, n_root, cw),
                            FT.FT.cwords_ok_b(G, C, n_root,
                              cw2 <> (cw3 <> (cw4 <> wt4))), hcws)
                  +hr1 = Logic.Proof.and_true_r(
                           FT.FT.cword_ok_b(G, C, n_root, cw),
                           FT.FT.cwords_ok_b(G, C, n_root,
                             cw2 <> (cw3 <> (cw4 <> wt4))), hcws)
                  +hcw2 = Logic.Proof.and_true_l(
                            FT.FT.cword_ok_b(G, C, n_root, cw2),
                            FT.FT.cwords_ok_b(G, C, n_root, cw3 <> (cw4 <> wt4)),
                            hr1)
                  +hr2 = Logic.Proof.and_true_r(
                           FT.FT.cword_ok_b(G, C, n_root, cw2),
                           FT.FT.cwords_ok_b(G, C, n_root, cw3 <> (cw4 <> wt4)),
                           hr1)
                  +hcw3 = Logic.Proof.and_true_l(
                            FT.FT.cword_ok_b(G, C, n_root, cw3),
                            FT.FT.cwords_ok_b(G, C, n_root, cw4 <> wt4), hr2)
                  +hr3 = Logic.Proof.and_true_r(
                           FT.FT.cword_ok_b(G, C, n_root, cw3),
                           FT.FT.cwords_ok_b(G, C, n_root, cw4 <> wt4), hr2)
                  +hcw4 = Logic.Proof.and_true_l(
                            FT.FT.cword_ok_b(G, C, n_root, cw4),
                            FT.FT.cwords_ok_b(G, C, n_root, wt4), hr3)
                  +hwt4 = Logic.Proof.and_true_r(
                            FT.FT.cword_ok_b(G, C, n_root, cw4),
                            FT.FT.cwords_ok_b(G, C, n_root, wt4), hr3)
                  +acc4 : +List<SolveFast.CWord> =
                    cw4 <> (cw3 <> (cw2 <> (cw <> Nil{})))
                  +hacc4 : {FT.FT.cwords_ok_b(G, C, n_root, acc4) == True{} : Bool} =
                    FH.bool_and_intro(FT.FT.cword_ok_b(G, C, n_root, cw4),
                      FT.FT.cwords_ok_b(G, C, n_root, cw3 <> (cw2 <> (cw <> Nil{}))),
                      hcw4,
                      FH.bool_and_intro(FT.FT.cword_ok_b(G, C, n_root, cw3),
                        FT.FT.cwords_ok_b(G, C, n_root, cw2 <> (cw <> Nil{})),
                        hcw3,
                        FH.bool_and_intro(FT.FT.cword_ok_b(G, C, n_root, cw2),
                          FT.FT.cwords_ok_b(G, C, n_root, cw <> Nil{}),
                          hcw2,
                          FH.bool_and_intro(FT.FT.cword_ok_b(G, C, n_root, cw),
                            True{}, hcw1, {==}))))
                  +rl : SolveFast.RevCWordsLen =
                    SolveFast.rev_cwords_len(wt4, acc4, 4n)
                  +hws_ok = FT.FT.rev_cwords_ok(G, C, n_root, wt4, acc4,
                              hwt4, hacc4, 4n)
                  +w = SolveFast.cword_w(cw)
                  +w2 = SolveFast.cword_w(cw2)
                  +w3 = SolveFast.cword_w(cw3)
                  +w4 = SolveFast.cword_w(cw4)
                  +eacc4 : {SolveFast.cwords_words(acc4)
                            == w4 <> (w3 <> (w2 <> (w <> Nil{})))
                            : +List<+List<Nat>>} =
                    Equal.trans(+List<+List<Nat>>,
                      SolveFast.cwords_words(acc4),
                      w4 <> SolveFast.cwords_words(cw3 <> (cw2 <> (cw <> Nil{}))),
                      w4 <> (w3 <> (w2 <> (w <> Nil{}))),
                      FH.cwords_words_cons(cw4, cw3 <> (cw2 <> (cw <> Nil{}))),
                      Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                        l1 => w4 <> l1,
                        SolveFast.cwords_words(cw3 <> (cw2 <> (cw <> Nil{}))),
                        w3 <> (w2 <> (w <> Nil{})),
                        Equal.trans(+List<+List<Nat>>,
                          SolveFast.cwords_words(cw3 <> (cw2 <> (cw <> Nil{}))),
                          w3 <> SolveFast.cwords_words(cw2 <> (cw <> Nil{})),
                          w3 <> (w2 <> (w <> Nil{})),
                          FH.cwords_words_cons(cw3, cw2 <> (cw <> Nil{})),
                          Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                            l2 => w3 <> l2,
                            SolveFast.cwords_words(cw2 <> (cw <> Nil{})),
                            w2 <> (w <> Nil{}),
                            Equal.trans(+List<+List<Nat>>,
                              SolveFast.cwords_words(cw2 <> (cw <> Nil{})),
                              w2 <> SolveFast.cwords_words(cw <> Nil{}),
                              w2 <> (w <> Nil{}),
                              FH.cwords_words_cons(cw2, cw <> Nil{}),
                              Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                                l3 => w2 <> l3,
                                SolveFast.cwords_words(cw <> Nil{}), w <> Nil{},
                                FH.cwords_words_cons(cw, Nil{})))))))
                  +erws4 : {w <> (w2 <> (w3 <> (w4 <> SolveFast.cwords_words(wt4))))
                            == rws : +List<+List<Nat>>} =
                    Equal.trans(+List<+List<Nat>>,
                      w <> (w2 <> (w3 <> (w4 <> SolveFast.cwords_words(wt4)))),
                      SolveFast.cwords_words(cw <> (cw2 <> (cw3 <> (cw4 <> wt4)))),
                      rws,
                      Equal.sym(+List<+List<Nat>>,
                        SolveFast.cwords_words(cw <> (cw2 <> (cw3 <> (cw4 <> wt4)))),
                        w <> (w2 <> (w3 <> (w4 <> SolveFast.cwords_words(wt4)))),
                        Equal.trans(+List<+List<Nat>>,
                          SolveFast.cwords_words(cw <> (cw2 <> (cw3 <> (cw4 <> wt4)))),
                          w <> SolveFast.cwords_words(cw2 <> (cw3 <> (cw4 <> wt4))),
                          w <> (w2 <> (w3 <> (w4 <> SolveFast.cwords_words(wt4)))),
                          FH.cwords_words_cons(cw, cw2 <> (cw3 <> (cw4 <> wt4))),
                          Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                            l1 => w <> l1,
                            SolveFast.cwords_words(cw2 <> (cw3 <> (cw4 <> wt4))),
                            w2 <> (w3 <> (w4 <> SolveFast.cwords_words(wt4))),
                            Equal.trans(+List<+List<Nat>>,
                              SolveFast.cwords_words(cw2 <> (cw3 <> (cw4 <> wt4))),
                              w2 <> SolveFast.cwords_words(cw3 <> (cw4 <> wt4)),
                              w2 <> (w3 <> (w4 <> SolveFast.cwords_words(wt4))),
                              FH.cwords_words_cons(cw2, cw3 <> (cw4 <> wt4)),
                              Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                                l2 => w2 <> l2,
                                SolveFast.cwords_words(cw3 <> (cw4 <> wt4)),
                                w3 <> (w4 <> SolveFast.cwords_words(wt4)),
                                Equal.trans(+List<+List<Nat>>,
                                  SolveFast.cwords_words(cw3 <> (cw4 <> wt4)),
                                  w3 <> SolveFast.cwords_words(cw4 <> wt4),
                                  w3 <> (w4 <> SolveFast.cwords_words(wt4)),
                                  FH.cwords_words_cons(cw3, cw4 <> wt4),
                                  Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                                    l3 => w3 <> l3,
                                    SolveFast.cwords_words(cw4 <> wt4),
                                    w4 <> SolveFast.cwords_words(wt4),
                                    FH.cwords_words_cons(cw4, wt4)))))))), erws)
                  +ews_rev : {SolveFast.cwords_words(FT.FT.rev_cwords_ws(rl))
                              == SolveFast.rev_words(rws, Nil{})
                              : +List<+List<Nat>>} =
                    Equal.trans(+List<+List<Nat>>,
                      SolveFast.cwords_words(FT.FT.rev_cwords_ws(rl)),
                      SolveFast.rev_words(SolveFast.cwords_words(wt4),
                        w4 <> (w3 <> (w2 <> (w <> Nil{})))),
                      SolveFast.rev_words(rws, Nil{}),
                      Equal.trans(+List<+List<Nat>>,
                        SolveFast.cwords_words(FT.FT.rev_cwords_ws(rl)),
                        SolveFast.rev_words(SolveFast.cwords_words(wt4),
                          SolveFast.cwords_words(acc4)),
                        SolveFast.rev_words(SolveFast.cwords_words(wt4),
                          w4 <> (w3 <> (w2 <> (w <> Nil{})))),
                        FT.FT.rev_cwords_len_words(wt4, acc4, 4n),
                        Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                          a => SolveFast.rev_words(SolveFast.cwords_words(wt4), a),
                          SolveFast.cwords_words(acc4),
                          w4 <> (w3 <> (w2 <> (w <> Nil{}))), eacc4)),
                      Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                        xs => SolveFast.rev_words(xs, Nil{}),
                        w <> (w2 <> (w3 <> (w4 <> SolveFast.cwords_words(wt4)))),
                        rws, erws4))
                  +elen_ws : {FT.FT.rev_cwords_len_val(rl)
                              == Groups.len_words(
                                   SolveFast.cwords_words(FT.FT.rev_cwords_ws(rl)))
                              : Nat} =
                    Equal.trans(Nat,
                      FT.FT.rev_cwords_len_val(rl),
                      Nat.add(Groups.len_words(SolveFast.cwords_words(wt4)), 4n),
                      Groups.len_words(SolveFast.cwords_words(FT.FT.rev_cwords_ws(rl))),
                      FT.FT.rev_cwords_len_eq(wt4, acc4, 4n),
                      Equal.sym(Nat,
                        Groups.len_words(SolveFast.cwords_words(FT.FT.rev_cwords_ws(rl))),
                        Nat.add(Groups.len_words(SolveFast.cwords_words(wt4)), 4n),
                        Equal.trans(Nat,
                          Groups.len_words(SolveFast.cwords_words(FT.FT.rev_cwords_ws(rl))),
                          Groups.len_words(
                            SolveFast.rev_words(SolveFast.cwords_words(wt4),
                              w4 <> (w3 <> (w2 <> (w <> Nil{}))))),
                          Nat.add(Groups.len_words(SolveFast.cwords_words(wt4)), 4n),
                          Equal.cong(+List<+List<Nat>>, Nat,
                            l => Groups.len_words(l),
                            SolveFast.cwords_words(FT.FT.rev_cwords_ws(rl)),
                            SolveFast.rev_words(SolveFast.cwords_words(wt4),
                              w4 <> (w3 <> (w2 <> (w <> Nil{})))),
                            Equal.trans(+List<+List<Nat>>,
                              SolveFast.cwords_words(FT.FT.rev_cwords_ws(rl)),
                              SolveFast.rev_words(SolveFast.cwords_words(wt4),
                                SolveFast.cwords_words(acc4)),
                              SolveFast.rev_words(SolveFast.cwords_words(wt4),
                                w4 <> (w3 <> (w2 <> (w <> Nil{})))),
                              FT.FT.rev_cwords_len_words(wt4, acc4, 4n),
                              Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
                                a => SolveFast.rev_words(SolveFast.cwords_words(wt4), a),
                                SolveFast.cwords_words(acc4),
                                w4 <> (w3 <> (w2 <> (w <> Nil{}))), eacc4))),
                          FH.len_rev_words(SolveFast.cwords_words(wt4),
                            w4 <> (w3 <> (w2 <> (w <> Nil{})))))))
                  FH.drain5_add_ge4_spec(G, C, n_root, pre, f, len, rws, rest,
                    n_orig, ig0, bigs0, lb2, items2, bigs2, bkts3, tbl0, tbl2,
                    rl, edec, ews_rev, elen_ws, hws_ok, hb3, etbl2, dw1)

def FH.drain5_add_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +n_orig: Nat, +ig0: +List<Groups.Group>,
    +bigs0: +List<SolveFast.BigClass>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    +bigs2: +List<SolveFast.BigClass>, -bkts3: Array<+List<SolveFast.CWord>>,
    -tbl0: Array<U32>, tbl2: Array<U32>, +rws_cw: +List<SolveFast.CWord>,
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +hnd_gp: {FN.FN.no_dup_ref(SolveFast.rev_words(rws, Nil{})) == True{} : Bool},
    +erws: {SolveFast.cwords_words(rws_cw) == rws : +List<+List<Nat>>},
    +hcws: {FT.FT.cwords_ok_b(G, C, n_root, rws_cw) == True{} : Bool},
    +hb3: FH.BktTree(G, C, n_root, 10n, 0, bkts3, pre),
    +htbl2: FT.FT.TblOk(G, C, n_root, tbl2),
    +etbl2: {tbl2 == tbl0 : Array<U32>},
    +dw1: FH.DrainWit<G, C, n_root, rest, n_orig, ig0, bigs0, lb2, items2, bigs2>) ->
  FH.DrainSpec(G, C, n_root, pre, SolveFast.FGroup{f, len, rws} <> rest,
    n_orig, ig0, bigs0, tbl0,
    SolveFast.drain5_add(FF5.FF5.encode_fb5_list(f), lb2, items2, bigs2,
      bkts3, tbl2, rws_cw)):
  FH.drain5_add_spec_go(G, C, n_root, pre, f, len, rws, rest, n_orig, ig0,
    bigs0, lb2, items2, bigs2, bkts3, tbl0, tbl2, rws_cw,
    FF5.FF5.decode_encode_list(f, hf5), hnd_gp, erws, hcws, hb3, htbl2, etbl2,
    dw1)

def FH.drain5_swap_pair(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +n_orig: Nat, +ig0: +List<Groups.Group>,
    +bigs0: +List<SolveFast.BigClass>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    +bigs2: +List<SolveFast.BigClass>, -tbl0: Array<U32>, tbl2: Array<U32>,
    r: Array<+List<SolveFast.CWord>> & +List<SolveFast.CWord>,
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +hnd_gp: {FN.FN.no_dup_ref(SolveFast.rev_words(rws, Nil{})) == True{} : Bool},
    +hb3: FH.BktTree(G, C, n_root, 10n, 0,
            Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>, r),
            pre),
    +hl_rws: FH.BktLeaf(G, C, n_root, FF5.FF5.encode_fb5_list(f),
               List.append(&2, SolveFast.FGroup, pre,
                 SolveFast.FGroup{f, len, rws} <> Nil{}),
               Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>, r)),
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +htbl2: FT.FT.TblOk(G, C, n_root, tbl2),
    +etbl2: {tbl2 == tbl0 : Array<U32>},
    +dw1: FH.DrainWit<G, C, n_root, rest, n_orig, ig0, bigs0, lb2, items2, bigs2>) ->
  FH.DrainSpec(G, C, n_root, pre, SolveFast.FGroup{f, len, rws} <> rest,
    n_orig, ig0, bigs0, tbl0,
    SolveFast.drain5_swap(FF5.FF5.encode_fb5_list(f), lb2, items2, bigs2, tbl2, r)):
  (b3, +rws_cw) = r
  +c = FF5.FF5.encode_fb5_list(f)
  +pre2 = List.append(&2, SolveFast.FGroup, pre,
            SolveFast.FGroup{f, len, rws} <> Nil{})
  +ew_lkp = Arr.Arr.dpair_l(
              {SolveFast.cwords_words(rws_cw) == FH.lookup_code(c, pre2)
               : +List<+List<Nat>>},
              {FT.FT.cwords_ok_b(G, C, n_root, rws_cw) == True{} : Bool}, hl_rws)
  +hcws = Arr.Arr.dpair_r(
            {SolveFast.cwords_words(rws_cw) == FH.lookup_code(c, pre2)
             : +List<+List<Nat>>},
            {FT.FT.cwords_ok_b(G, C, n_root, rws_cw) == True{} : Bool}, hl_rws)
  +erws : {SolveFast.cwords_words(rws_cw) == rws : +List<+List<Nat>>} =
    Equal.trans(+List<+List<Nat>>,
      SolveFast.cwords_words(rws_cw), FH.lookup_code(c, pre2), rws,
      ew_lkp, FH.lookup_append_last(pre, f, len, rws, hnh))
  FH.drain5_add_spec(G, C, n_root, pre, f, len, rws, rest, n_orig, ig0, bigs0,
    lb2, items2, bigs2, b3, tbl0, tbl2, rws_cw, hf5, hnd_gp, erws, hcws, hb3,
    htbl2, etbl2, dw1)

def FH.drain5_one_dup4(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +n_orig: Nat, +ig0: +List<Groups.Group>,
    +bigs0: +List<SolveFast.BigClass>, -bkts2: Array<+List<SolveFast.CWord>>,
    -tbl0: Array<U32>, tbl2: Array<U32>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    +bigs2: +List<SolveFast.BigClass>,
    a1: Array<+List<SolveFast.CWord>>,
    +ea1: {a1 == bkts2 : Array<+List<SolveFast.CWord>>},
    b1: Array<+List<SolveFast.CWord>>,
    +eb1: {b1 == a1 : Array<+List<SolveFast.CWord>>},
    c1: Array<+List<SolveFast.CWord>>,
    +ec1: {c1 == b1 : Array<+List<SolveFast.CWord>>},
    d1: Array<+List<SolveFast.CWord>>,
    +ed1: {d1 == c1 : Array<+List<SolveFast.CWord>>},
    d2: Array<+List<SolveFast.CWord>>,
    +ed2: {d2 == d1 : Array<+List<SolveFast.CWord>>},
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +hnd_gp: {FN.FN.no_dup_ref(SolveFast.rev_words(rws, Nil{})) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hb2: FH.BktTree(G, C, n_root, 10n, 0, bkts2,
            List.append(&2, SolveFast.FGroup, pre,
              SolveFast.FGroup{f, len, rws} <> Nil{})),
    +htbl2: FT.FT.TblOk(G, C, n_root, tbl2),
    +etbl2: {tbl2 == tbl0 : Array<U32>},
    +dw1: FH.DrainWit<G, C, n_root, rest, n_orig, ig0, bigs0, lb2, items2, bigs2>) ->
  FH.DrainSpec(G, C, n_root, pre, SolveFast.FGroup{f, len, rws} <> rest,
    n_orig, ig0, bigs0, tbl0,
    SolveFast.drain5_swap(FF5.FF5.encode_fb5_list(f), lb2, items2, bigs2, tbl2,
      Array.swap(+List<SolveFast.CWord>, bkts2, FF5.FF5.encode_fb5_list(f), Nil{}))):
  +c = FF5.FF5.encode_fb5_list(f)
  +gp : SolveFast.FGroup = SolveFast.FGroup{f, len, rws}
  +pre2 = List.append(&2, SolveFast.FGroup, pre, gp <> Nil{})
  +eb1_b : {b1 == bkts2 : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, b1, a1, bkts2, eb1, ea1)
  +ec1_a : {c1 == a1 : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, c1, b1, a1, ec1, eb1)
  +ec1_b : {c1 == bkts2 : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, c1, b1, bkts2, ec1, eb1_b)
  +ed1_a : {d1 == a1 : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, d1, c1, a1, ed1, ec1_a)
  +ed2_a : {d2 == a1 : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, d2, d1, a1, ed2, ed1_a)
  +ed2_b : {d2 == bkts2 : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, d2, d1, bkts2, ed2,
      Equal.trans(Array<+List<SolveFast.CWord>>, d1, c1, bkts2, ed1, ec1_b))
  +hb_b1 = FH.bkt_tree_transport(G, C, n_root, 10n, 0, bkts2, b1, pre2,
             Equal.sym(Array<+List<SolveFast.CWord>>, b1, bkts2, eb1_b), hb2)
  +hb_c1 = FH.bkt_tree_transport(G, C, n_root, 10n, 0, bkts2, c1, pre2,
             Equal.sym(Array<+List<SolveFast.CWord>>, c1, bkts2, ec1_b), hb2)
  +hb_d2 = FH.bkt_tree_transport(G, C, n_root, 10n, 0, bkts2, d2, pre2,
             Equal.sym(Array<+List<SolveFast.CWord>>, d2, bkts2, ed2_b), hb2)
  +hb3_b1 = FH.bkt_tree_swap(G, C, n_root, b1, OpClear{gp}, pre,
              Arr.DPair{hf5, hnh}, hb_b1)
  +hb3_a1 = FH.bkt_tree_transport(G, C, n_root, 10n, 0,
              Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                Array.swap(+List<SolveFast.CWord>, b1, c, Nil{})),
              Arr.Arr.fst(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                Array.swap(+List<SolveFast.CWord>, a1, c, Nil{})), pre,
              Equal.cong(Array<+List<SolveFast.CWord>>, Array<+List<SolveFast.CWord>>,
                x => Arr.Arr.fst(Array<+List<SolveFast.CWord>>,
                       +List<SolveFast.CWord>,
                       Array.swap(+List<SolveFast.CWord>, x, c, Nil{})),
                b1, a1, eb1), hb3_b1)
  +hd_c1 = FH.bkt_tree_depth(G, C, n_root, 10n, 0, c1, pre2, hb_c1)
  +hd_d1 = Arr.Arr.depth_transport(+List<SolveFast.CWord>, 10n, c1, d1,
             Equal.sym(Array<+List<SolveFast.CWord>>, d1, c1, ed1), hd_c1)
  +eold_d1 : {Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                Array.swap(+List<SolveFast.CWord>, d1, c, Nil{}))
              == Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                   Array.get(+List<SolveFast.CWord>, d1, c))
              : +List<SolveFast.CWord>} =
    Arr.Arr.swap_old(+List<SolveFast.CWord>, 10n, d1, c, Nil{}, hd_d1)
  +hl_d2 = FH.bkt_tree_get(G, C, n_root, d2, pre2, c,
             FF5.FF5.encode_fb5_list_zero_from(f, hf5), hb_d2)
  +esnd : {Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
             Array.get(+List<SolveFast.CWord>, d2, c))
           == Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                Array.swap(+List<SolveFast.CWord>, a1, c, Nil{}))
           : +List<SolveFast.CWord>} =
    Equal.sym(+List<SolveFast.CWord>,
      Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.swap(+List<SolveFast.CWord>, a1, c, Nil{})),
      Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
        Array.get(+List<SolveFast.CWord>, d2, c)),
      Equal.trans(+List<SolveFast.CWord>,
        Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
          Array.swap(+List<SolveFast.CWord>, a1, c, Nil{})),
        Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
          Array.swap(+List<SolveFast.CWord>, d1, c, Nil{})),
        Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
          Array.get(+List<SolveFast.CWord>, d2, c)),
        Equal.cong(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
          x => Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                 Array.swap(+List<SolveFast.CWord>, x, c, Nil{})),
          a1, d1, Equal.sym(Array<+List<SolveFast.CWord>>, d1, a1, ed1_a)),
        Equal.trans(+List<SolveFast.CWord>,
          Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            Array.swap(+List<SolveFast.CWord>, d1, c, Nil{})),
          Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            Array.get(+List<SolveFast.CWord>, d1, c)),
          Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            Array.get(+List<SolveFast.CWord>, d2, c)),
          eold_d1,
          Equal.cong(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
            x => Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
                   Array.get(+List<SolveFast.CWord>, x, c)),
            d1, d2, Equal.sym(Array<+List<SolveFast.CWord>>, d2, d1, ed2)))))
  +hl_a1 = FH.bkt_leaf_transport_v(G, C, n_root, c, pre2,
             Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
               Array.get(+List<SolveFast.CWord>, d2, c)),
             Arr.Arr.snd(Array<+List<SolveFast.CWord>>, +List<SolveFast.CWord>,
               Array.swap(+List<SolveFast.CWord>, a1, c, Nil{})), esnd, hl_d2)
  %ea1 : FH.DrainSpec(G, C, n_root, pre, gp <> rest, n_orig, ig0, bigs0, tbl0,
           SolveFast.drain5_swap(c, lb2, items2, bigs2, tbl2,
             Array.swap(+List<SolveFast.CWord>, _, c, Nil{})))
  FH.drain5_swap_pair(G, C, n_root, pre, f, len, rws, rest, n_orig, ig0, bigs0,
    lb2, items2, bigs2, tbl0, tbl2,
    Array.swap(+List<SolveFast.CWord>, a1, c, Nil{}),
    hf5, hnd_gp, hb3_a1, hl_a1, hnh, htbl2, etbl2, dw1)

def FH.drain5_one_dup3(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +n_orig: Nat, +ig0: +List<Groups.Group>,
    +bigs0: +List<SolveFast.BigClass>, -bkts2: Array<+List<SolveFast.CWord>>,
    -tbl0: Array<U32>, tbl2: Array<U32>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    +bigs2: +List<SolveFast.BigClass>,
    a1: Array<+List<SolveFast.CWord>>,
    +ea1: {a1 == bkts2 : Array<+List<SolveFast.CWord>>},
    b1: Array<+List<SolveFast.CWord>>,
    +eb1: {b1 == a1 : Array<+List<SolveFast.CWord>>},
    c1: Array<+List<SolveFast.CWord>>,
    +ec1: {c1 == b1 : Array<+List<SolveFast.CWord>>},
    -c2: Array<+List<SolveFast.CWord>>,
    +ec2: {c2 == c1 : Array<+List<SolveFast.CWord>>},
    dp4: &d1: Array<+List<SolveFast.CWord>> -> &d2: Array<+List<SolveFast.CWord>> ->
         {d1 == c2 : Array<+List<SolveFast.CWord>>}
         & {d2 == d1 : Array<+List<SolveFast.CWord>>},
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +hnd_gp: {FN.FN.no_dup_ref(SolveFast.rev_words(rws, Nil{})) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hb2: FH.BktTree(G, C, n_root, 10n, 0, bkts2,
            List.append(&2, SolveFast.FGroup, pre,
              SolveFast.FGroup{f, len, rws} <> Nil{})),
    +htbl2: FT.FT.TblOk(G, C, n_root, tbl2),
    +etbl2: {tbl2 == tbl0 : Array<U32>},
    +dw1: FH.DrainWit<G, C, n_root, rest, n_orig, ig0, bigs0, lb2, items2, bigs2>) ->
  FH.DrainSpec(G, C, n_root, pre, SolveFast.FGroup{f, len, rws} <> rest,
    n_orig, ig0, bigs0, tbl0,
    SolveFast.drain5_swap(FF5.FF5.encode_fb5_list(f), lb2, items2, bigs2, tbl2,
      Array.swap(+List<SolveFast.CWord>, bkts2, FF5.FF5.encode_fb5_list(f), Nil{}))):
  (d1, dp5) = dp4
  (d2, pe4) = dp5
  (+ed1, +ed2) = pe4
  FH.drain5_one_dup4(G, C, n_root, pre, f, len, rws, rest, n_orig, ig0, bigs0,
    bkts2, tbl0, tbl2, lb2, items2, bigs2, a1, ea1, b1, eb1, c1, ec1,
    d1, Equal.trans(Array<+List<SolveFast.CWord>>, d1, c2, c1, ed1, ec2),
    d2, ed2, hf5, hnd_gp, hnh, hb2, htbl2, etbl2, dw1)

def FH.drain5_one_dup2(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +n_orig: Nat, +ig0: +List<Groups.Group>,
    +bigs0: +List<SolveFast.BigClass>, -bkts2: Array<+List<SolveFast.CWord>>,
    -tbl0: Array<U32>, tbl2: Array<U32>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    +bigs2: +List<SolveFast.BigClass>,
    a1: Array<+List<SolveFast.CWord>>,
    +ea1: {a1 == bkts2 : Array<+List<SolveFast.CWord>>},
    b1: Array<+List<SolveFast.CWord>>,
    +eb1: {b1 == a1 : Array<+List<SolveFast.CWord>>},
    -b2: Array<+List<SolveFast.CWord>>,
    +eb2: {b2 == b1 : Array<+List<SolveFast.CWord>>},
    dp3: &c1: Array<+List<SolveFast.CWord>> -> &c2: Array<+List<SolveFast.CWord>> ->
         {c1 == b2 : Array<+List<SolveFast.CWord>>}
         & {c2 == c1 : Array<+List<SolveFast.CWord>>},
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +hnd_gp: {FN.FN.no_dup_ref(SolveFast.rev_words(rws, Nil{})) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hb2: FH.BktTree(G, C, n_root, 10n, 0, bkts2,
            List.append(&2, SolveFast.FGroup, pre,
              SolveFast.FGroup{f, len, rws} <> Nil{})),
    +htbl2: FT.FT.TblOk(G, C, n_root, tbl2),
    +etbl2: {tbl2 == tbl0 : Array<U32>},
    +dw1: FH.DrainWit<G, C, n_root, rest, n_orig, ig0, bigs0, lb2, items2, bigs2>) ->
  FH.DrainSpec(G, C, n_root, pre, SolveFast.FGroup{f, len, rws} <> rest,
    n_orig, ig0, bigs0, tbl0,
    SolveFast.drain5_swap(FF5.FF5.encode_fb5_list(f), lb2, items2, bigs2, tbl2,
      Array.swap(+List<SolveFast.CWord>, bkts2, FF5.FF5.encode_fb5_list(f), Nil{}))):
  (c1, dp4) = dp3
  (c2, pe3) = dp4
  (+ec1, +ec2) = pe3
  FH.drain5_one_dup3(G, C, n_root, pre, f, len, rws, rest, n_orig, ig0, bigs0,
    bkts2, tbl0, tbl2, lb2, items2, bigs2, a1, ea1, b1, eb1,
    c1, Equal.trans(Array<+List<SolveFast.CWord>>, c1, b2, b1, ec1, eb2),
    c2, ec2, Arr.Arr.dup(+List<SolveFast.CWord>, c2),
    hf5, hnd_gp, hnh, hb2, htbl2, etbl2, dw1)

def FH.drain5_one_dup1(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +n_orig: Nat, +ig0: +List<Groups.Group>,
    +bigs0: +List<SolveFast.BigClass>, -bkts2: Array<+List<SolveFast.CWord>>,
    -tbl0: Array<U32>, tbl2: Array<U32>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    +bigs2: +List<SolveFast.BigClass>,
    a1: Array<+List<SolveFast.CWord>>,
    +ea1: {a1 == bkts2 : Array<+List<SolveFast.CWord>>},
    -a2: Array<+List<SolveFast.CWord>>,
    +ea2: {a2 == a1 : Array<+List<SolveFast.CWord>>},
    dp2: &b1: Array<+List<SolveFast.CWord>> -> &b2: Array<+List<SolveFast.CWord>> ->
         {b1 == a2 : Array<+List<SolveFast.CWord>>}
         & {b2 == b1 : Array<+List<SolveFast.CWord>>},
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +hnd_gp: {FN.FN.no_dup_ref(SolveFast.rev_words(rws, Nil{})) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hb2: FH.BktTree(G, C, n_root, 10n, 0, bkts2,
            List.append(&2, SolveFast.FGroup, pre,
              SolveFast.FGroup{f, len, rws} <> Nil{})),
    +htbl2: FT.FT.TblOk(G, C, n_root, tbl2),
    +etbl2: {tbl2 == tbl0 : Array<U32>},
    +dw1: FH.DrainWit<G, C, n_root, rest, n_orig, ig0, bigs0, lb2, items2, bigs2>) ->
  FH.DrainSpec(G, C, n_root, pre, SolveFast.FGroup{f, len, rws} <> rest,
    n_orig, ig0, bigs0, tbl0,
    SolveFast.drain5_swap(FF5.FF5.encode_fb5_list(f), lb2, items2, bigs2, tbl2,
      Array.swap(+List<SolveFast.CWord>, bkts2, FF5.FF5.encode_fb5_list(f), Nil{}))):
  (b1, dp3) = dp2
  (b2, pe2) = dp3
  (+eb1, +eb2) = pe2
  FH.drain5_one_dup2(G, C, n_root, pre, f, len, rws, rest, n_orig, ig0, bigs0,
    bkts2, tbl0, tbl2, lb2, items2, bigs2, a1, ea1,
    b1, Equal.trans(Array<+List<SolveFast.CWord>>, b1, a2, a1, eb1, ea2),
    b2, eb2, Arr.Arr.dup(+List<SolveFast.CWord>, b2),
    hf5, hnd_gp, hnh, hb2, htbl2, etbl2, dw1)

def FH.drain5_one_dup0(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +n_orig: Nat, +ig0: +List<Groups.Group>,
    +bigs0: +List<SolveFast.BigClass>, -bkts2: Array<+List<SolveFast.CWord>>,
    -tbl0: Array<U32>, tbl2: Array<U32>, +lb2: Nat, +items2: +List<SolveFast.Item>,
    +bigs2: +List<SolveFast.BigClass>,
    dp1: &a1: Array<+List<SolveFast.CWord>> -> &a2: Array<+List<SolveFast.CWord>> ->
         {a1 == bkts2 : Array<+List<SolveFast.CWord>>}
         & {a2 == a1 : Array<+List<SolveFast.CWord>>},
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +hnd_gp: {FN.FN.no_dup_ref(SolveFast.rev_words(rws, Nil{})) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hb2: FH.BktTree(G, C, n_root, 10n, 0, bkts2,
            List.append(&2, SolveFast.FGroup, pre,
              SolveFast.FGroup{f, len, rws} <> Nil{})),
    +htbl2: FT.FT.TblOk(G, C, n_root, tbl2),
    +etbl2: {tbl2 == tbl0 : Array<U32>},
    +dw1: FH.DrainWit<G, C, n_root, rest, n_orig, ig0, bigs0, lb2, items2, bigs2>) ->
  FH.DrainSpec(G, C, n_root, pre, SolveFast.FGroup{f, len, rws} <> rest,
    n_orig, ig0, bigs0, tbl0,
    SolveFast.drain5_swap(FF5.FF5.encode_fb5_list(f), lb2, items2, bigs2, tbl2,
      Array.swap(+List<SolveFast.CWord>, bkts2, FF5.FF5.encode_fb5_list(f), Nil{}))):
  (a1, dp2) = dp1
  (a2, pe1) = dp2
  (+ea1, +ea2) = pe1
  FH.drain5_one_dup1(G, C, n_root, pre, f, len, rws, rest, n_orig, ig0, bigs0,
    bkts2, tbl0, tbl2, lb2, items2, bigs2, a1, ea1, a2, ea2,
    Arr.Arr.dup(+List<SolveFast.CWord>, a2), hf5, hnd_gp, hnh, hb2, htbl2,
    etbl2, dw1)

def FH.drain5_cons_step(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +gn: Nat, +n_root: Nat, +pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +n_orig: Nat, +ig0: +List<Groups.Group>,
    +bigs0: +List<SolveFast.BigClass>, -tbl0: Array<U32>,
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0), dr1: SolveFast.Drain5State,
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +hnd_gp: {FN.FN.no_dup_ref(SolveFast.rev_words(rws, Nil{})) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hdr1: FH.DrainSpec(G, C, n_root,
             List.append(&2, SolveFast.FGroup, pre,
               SolveFast.FGroup{f, len, rws} <> Nil{}),
             rest, n_orig, ig0, bigs0, tbl0, dr1)) ->
  FH.DrainSpec(G, C, n_root, pre, SolveFast.FGroup{f, len, rws} <> rest,
    n_orig, ig0, bigs0, tbl0,
    SolveFast.drain5_go(gn, FF5.FF5.encode_fb5_list(f) <> Nil{}, dr1)):
  match dr1:
    case SolveFast.Drain5State{bkts2, tbl2, +lb2, +items2, +bigs2}:
      +gp : SolveFast.FGroup = SolveFast.FGroup{f, len, rws}
      +pre2 = List.append(&2, SolveFast.FGroup, pre, gp <> Nil{})
      +hb2 = Arr.Arr.dpair_l(
               FH.BktTree(G, C, n_root, 10n, 0, bkts2, pre2),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 FH.DrainWit<G, C, n_root, rest, n_orig, ig0, bigs0, lb2,
                   items2, bigs2>>, hdr1)
      +hr1 = Arr.Arr.dpair_r(
               FH.BktTree(G, C, n_root, 10n, 0, bkts2, pre2),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 FH.DrainWit<G, C, n_root, rest, n_orig, ig0, bigs0, lb2,
                   items2, bigs2>>, hdr1)
      +et2 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
               FH.DrainWit<G, C, n_root, rest, n_orig, ig0, bigs0, lb2,
                 items2, bigs2>, hr1)
      +dw1 = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
               FH.DrainWit<G, C, n_root, rest, n_orig, ig0, bigs0, lb2,
                 items2, bigs2>, hr1)
      +htbl2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl0, tbl2,
                 Equal.sym(Array<U32>, tbl2, tbl0, et2), htbl0)
      FH.drain5_one_dup0(G, C, n_root, pre, f, len, rws, rest, n_orig, ig0,
        bigs0, bkts2, tbl0, tbl2, lb2, items2, bigs2,
        Arr.Arr.dup(+List<SolveFast.CWord>, bkts2), hf5, hnd_gp, hnh, hb2,
        htbl2, et2, dw1)

def FH.drain5_go_cons_dup2(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +gn: Nat, +n_root: Nat, +pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +n_orig: Nat, +ig0: +List<Groups.Group>,
    +bigs0: +List<SolveFast.BigClass>, +lb0: Nat, +items0: +List<SolveFast.Item>,
    -bkts: Array<+List<SolveFast.CWord>>, -tbl: Array<U32>,
    b1: Array<+List<SolveFast.CWord>>,
    +eb1: {b1 == bkts : Array<+List<SolveFast.CWord>>},
    -b2: Array<+List<SolveFast.CWord>>,
    +eb2: {b2 == b1 : Array<+List<SolveFast.CWord>>},
    dpb2: &b3: Array<+List<SolveFast.CWord>> -> &b4: Array<+List<SolveFast.CWord>> ->
          {b3 == b2 : Array<+List<SolveFast.CWord>>}
          & {b4 == b3 : Array<+List<SolveFast.CWord>>},
    t1: Array<U32>, +et1: {t1 == tbl : Array<U32>},
    -t2: Array<U32>, +et2: {t2 == t1 : Array<U32>},
    dpt2: &t3: Array<U32> -> &t4: Array<U32> ->
          {t3 == t2 : Array<U32>} & {t4 == t3 : Array<U32>},
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +hnd_gp: {FN.FN.no_dup_ref(SolveFast.rev_words(rws, Nil{})) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts,
           List.append(&2, SolveFast.FGroup,
             List.append(&2, SolveFast.FGroup, pre,
               SolveFast.FGroup{f, len, rws} <> Nil{}), rest)),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    ih: @b4: Array<+List<SolveFast.CWord>> -> @t4: Array<U32> ->
        FH.BktTree(G, C, n_root, 10n, 0, b4,
          List.append(&2, SolveFast.FGroup,
            List.append(&2, SolveFast.FGroup, pre,
              SolveFast.FGroup{f, len, rws} <> Nil{}), rest)) ->
        FT.FT.TblOk(G, C, n_root, t4) ->
        FH.DrainSpec(G, C, n_root,
          List.append(&2, SolveFast.FGroup, pre,
            SolveFast.FGroup{f, len, rws} <> Nil{}),
          rest, n_orig, ig0, bigs0, t4,
          SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
            SolveFast.Drain5State{b4, t4, lb0, items0, bigs0}))) ->
  FH.DrainSpec(G, C, n_root, pre, SolveFast.FGroup{f, len, rws} <> rest,
    n_orig, ig0, bigs0, tbl,
    SolveFast.drain5_go(gn, 
      FH.rev_codes(SolveFast.FGroup{f, len, rws} <> rest, Nil{}),
      SolveFast.Drain5State{bkts, tbl, lb0, items0, bigs0})):
  (b3, dpb3) = dpb2
  (b4, peb2) = dpb3
  (+eb3, +eb4) = peb2
  (t3, dpt3) = dpt2
  (t4, pet2) = dpt3
  (+et3, +et4) = pet2
  +c = FF5.FF5.encode_fb5_list(f)
  +gp : SolveFast.FGroup = SolveFast.FGroup{f, len, rws}
  +pre2 = List.append(&2, SolveFast.FGroup, pre, gp <> Nil{})
  +eb3_b1 : {b3 == b1 : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, b3, b2, b1, eb3, eb2)
  +eb4_b1 : {b4 == b1 : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, b4, b3, b1, eb4, eb3_b1)
  +eb4_bk : {b4 == bkts : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, b4, b1, bkts, eb4_b1, eb1)
  +et3_t1 : {t3 == t1 : Array<U32>} = Equal.trans(Array<U32>, t3, t2, t1, et3, et2)
  +et4_t1 : {t4 == t1 : Array<U32>} = Equal.trans(Array<U32>, t4, t3, t1, et4, et3_t1)
  +et4_tb : {t4 == tbl : Array<U32>} = Equal.trans(Array<U32>, t4, t1, tbl, et4_t1, et1)
  +hb4 = FH.bkt_tree_transport(G, C, n_root, 10n, 0, bkts, b4,
           List.append(&2, SolveFast.FGroup, pre2, rest),
           Equal.sym(Array<+List<SolveFast.CWord>>, b4, bkts, eb4_bk), hb)
  +ht4 = FT.FT.tbl_ok_transport(G, C, n_root, tbl, t4,
           Equal.sym(Array<U32>, t4, tbl, et4_tb), htbl)
  +hdr4 = ih(b4, t4, hb4, ht4)
  +hdr_tb = FH.drain_spec_transport_tbl(G, C, n_root, pre2, rest, n_orig, ig0,
              bigs0, t4, tbl,
              SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
                SolveFast.Drain5State{b4, t4, lb0, items0, bigs0}),
              et4_tb, hdr4)
  +eq_41 : {SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
              SolveFast.Drain5State{b4, t4, lb0, items0, bigs0})
            == SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
                 SolveFast.Drain5State{b1, t1, lb0, items0, bigs0})
            : SolveFast.Drain5State} =
    Equal.trans(SolveFast.Drain5State,
      SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
        SolveFast.Drain5State{b4, t4, lb0, items0, bigs0}),
      SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
        SolveFast.Drain5State{b1, t4, lb0, items0, bigs0}),
      SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
        SolveFast.Drain5State{b1, t1, lb0, items0, bigs0}),
      Equal.cong(Array<+List<SolveFast.CWord>>, SolveFast.Drain5State,
        x => SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
               SolveFast.Drain5State{x, t4, lb0, items0, bigs0}),
        b4, b1, eb4_b1),
      Equal.cong(Array<U32>, SolveFast.Drain5State,
        y => SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
               SolveFast.Drain5State{b1, y, lb0, items0, bigs0}),
        t4, t1, et4_t1))
  +hdr1 = FH.drain_spec_transport(G, C, n_root, pre2, rest, n_orig, ig0, bigs0,
            tbl,
            SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
              SolveFast.Drain5State{b4, t4, lb0, items0, bigs0}),
            SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
              SolveFast.Drain5State{b1, t1, lb0, items0, bigs0}),
            eq_41, hdr_tb)
  +eapp : {SolveFast.drain5_go(gn, 
             List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
             SolveFast.Drain5State{b3, t3, lb0, items0, bigs0})
           == SolveFast.drain5_go(gn, c <> Nil{},
                SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
                  SolveFast.Drain5State{b3, t3, lb0, items0, bigs0}))
           : SolveFast.Drain5State} =
    FH.drain5_go_append(gn, FH.rev_codes(rest, Nil{}), c <> Nil{},
      SolveFast.Drain5State{b3, t3, lb0, items0, bigs0})
  +eapp_1 : {SolveFast.drain5_go(gn, 
               List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
               SolveFast.Drain5State{b1, t1, lb0, items0, bigs0})
             == SolveFast.drain5_go(gn, c <> Nil{},
                  SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
                    SolveFast.Drain5State{b1, t1, lb0, items0, bigs0}))
             : SolveFast.Drain5State} =
    Equal.trans(SolveFast.Drain5State,
      SolveFast.drain5_go(gn, 
        List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
        SolveFast.Drain5State{b1, t1, lb0, items0, bigs0}),
      SolveFast.drain5_go(gn, c <> Nil{},
        SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
          SolveFast.Drain5State{b3, t3, lb0, items0, bigs0})),
      SolveFast.drain5_go(gn, c <> Nil{},
        SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
          SolveFast.Drain5State{b1, t1, lb0, items0, bigs0})),
      Equal.trans(SolveFast.Drain5State,
        SolveFast.drain5_go(gn, 
          List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
          SolveFast.Drain5State{b1, t1, lb0, items0, bigs0}),
        SolveFast.drain5_go(gn, 
          List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
          SolveFast.Drain5State{b3, t3, lb0, items0, bigs0}),
        SolveFast.drain5_go(gn, c <> Nil{},
          SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
            SolveFast.Drain5State{b3, t3, lb0, items0, bigs0})),
        Equal.trans(SolveFast.Drain5State,
          SolveFast.drain5_go(gn, 
            List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
            SolveFast.Drain5State{b1, t1, lb0, items0, bigs0}),
          SolveFast.drain5_go(gn, 
            List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
            SolveFast.Drain5State{b3, t1, lb0, items0, bigs0}),
          SolveFast.drain5_go(gn, 
            List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
            SolveFast.Drain5State{b3, t3, lb0, items0, bigs0}),
          Equal.cong(Array<+List<SolveFast.CWord>>, SolveFast.Drain5State,
            x => SolveFast.drain5_go(gn, 
                   List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
                   SolveFast.Drain5State{x, t1, lb0, items0, bigs0}),
            b1, b3, Equal.sym(Array<+List<SolveFast.CWord>>, b3, b1, eb3_b1)),
          Equal.cong(Array<U32>, SolveFast.Drain5State,
            y => SolveFast.drain5_go(gn, 
                   List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
                   SolveFast.Drain5State{b3, y, lb0, items0, bigs0}),
            t1, t3, Equal.sym(Array<U32>, t3, t1, et3_t1))),
        eapp),
      Equal.trans(SolveFast.Drain5State,
        SolveFast.drain5_go(gn, c <> Nil{},
          SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
            SolveFast.Drain5State{b3, t3, lb0, items0, bigs0})),
        SolveFast.drain5_go(gn, c <> Nil{},
          SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
            SolveFast.Drain5State{b1, t3, lb0, items0, bigs0})),
        SolveFast.drain5_go(gn, c <> Nil{},
          SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
            SolveFast.Drain5State{b1, t1, lb0, items0, bigs0})),
        Equal.cong(Array<+List<SolveFast.CWord>>, SolveFast.Drain5State,
          x => SolveFast.drain5_go(gn, c <> Nil{},
                 SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
                   SolveFast.Drain5State{x, t3, lb0, items0, bigs0})),
          b3, b1, eb3_b1),
        Equal.cong(Array<U32>, SolveFast.Drain5State,
          y => SolveFast.drain5_go(gn, c <> Nil{},
                 SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
                   SolveFast.Drain5State{b1, y, lb0, items0, bigs0})),
          t3, t1, et3_t1)))
  %eb1 : FH.DrainSpec(G, C, n_root, pre, gp <> rest, n_orig, ig0, bigs0, tbl,
           SolveFast.drain5_go(gn, FH.rev_codes(rest, c <> Nil{}),
             SolveFast.Drain5State{_, tbl, lb0, items0, bigs0}))
  %et1 : FH.DrainSpec(G, C, n_root, pre, gp <> rest, n_orig, ig0, bigs0, tbl,
           SolveFast.drain5_go(gn, FH.rev_codes(rest, c <> Nil{}),
             SolveFast.Drain5State{b1, _, lb0, items0, bigs0}))
  %Equal.sym(+List<U32>,
     FH.rev_codes(rest, c <> Nil{}),
     List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
     FH.rev_codes_append(rest, c <> Nil{})) :
    FH.DrainSpec(G, C, n_root, pre, gp <> rest, n_orig, ig0, bigs0, tbl,
      SolveFast.drain5_go(gn, _, SolveFast.Drain5State{b1, t1, lb0, items0, bigs0}))
  %Equal.sym(SolveFast.Drain5State,
     SolveFast.drain5_go(gn, 
       List.append(&2, U32, FH.rev_codes(rest, Nil{}), c <> Nil{}),
       SolveFast.Drain5State{b1, t1, lb0, items0, bigs0}),
     SolveFast.drain5_go(gn, c <> Nil{},
       SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
         SolveFast.Drain5State{b1, t1, lb0, items0, bigs0})),
     eapp_1) :
    FH.DrainSpec(G, C, n_root, pre, gp <> rest, n_orig, ig0, bigs0, tbl, _)
  FH.drain5_cons_step(G, C, gn, n_root, pre, f, len, rws, rest, n_orig, ig0,
    bigs0, tbl, htbl,
    SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
      SolveFast.Drain5State{b1, t1, lb0, items0, bigs0}),
    hf5, hnd_gp, hnh, hdr1)

def FH.drain5_go_cons_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +gn: Nat, +n_root: Nat, +pre: +List<SolveFast.FGroup>,
    +f: +List<Feedback.Color>, +len: Nat, +rws: +List<+List<Nat>>,
    +rest: +List<SolveFast.FGroup>, +n_orig: Nat, +ig0: +List<Groups.Group>,
    +bigs0: +List<SolveFast.BigClass>, +lb0: Nat, +items0: +List<SolveFast.Item>,
    -bkts: Array<+List<SolveFast.CWord>>, -tbl: Array<U32>,
    +hf5: {FF5.FF5.is_fb5(f) == True{} : Bool},
    +hnd_gp: {FN.FN.no_dup_ref(SolveFast.rev_words(rws, Nil{})) == True{} : Bool},
    +hnh: {FH.has_code(FF5.FF5.encode_fb5_list(f), pre) == False{} : Bool},
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts,
           List.append(&2, SolveFast.FGroup,
             List.append(&2, SolveFast.FGroup, pre,
               SolveFast.FGroup{f, len, rws} <> Nil{}), rest)),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    dpb: &b1: Array<+List<SolveFast.CWord>> -> &b2: Array<+List<SolveFast.CWord>> ->
         {b1 == bkts : Array<+List<SolveFast.CWord>>}
         & {b2 == b1 : Array<+List<SolveFast.CWord>>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>},
    ih: @b4: Array<+List<SolveFast.CWord>> -> @t4: Array<U32> ->
        FH.BktTree(G, C, n_root, 10n, 0, b4,
          List.append(&2, SolveFast.FGroup,
            List.append(&2, SolveFast.FGroup, pre,
              SolveFast.FGroup{f, len, rws} <> Nil{}), rest)) ->
        FT.FT.TblOk(G, C, n_root, t4) ->
        FH.DrainSpec(G, C, n_root,
          List.append(&2, SolveFast.FGroup, pre,
            SolveFast.FGroup{f, len, rws} <> Nil{}),
          rest, n_orig, ig0, bigs0, t4,
          SolveFast.drain5_go(gn, FH.rev_codes(rest, Nil{}),
            SolveFast.Drain5State{b4, t4, lb0, items0, bigs0}))) ->
  FH.DrainSpec(G, C, n_root, pre, SolveFast.FGroup{f, len, rws} <> rest,
    n_orig, ig0, bigs0, tbl,
    SolveFast.drain5_go(gn, 
      FH.rev_codes(SolveFast.FGroup{f, len, rws} <> rest, Nil{}),
      SolveFast.Drain5State{bkts, tbl, lb0, items0, bigs0})):
  (b1, dpb2) = dpb
  (b2, peb) = dpb2
  (+eb1, +eb2) = peb
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2) = pet
  FH.drain5_go_cons_dup2(G, C, gn, n_root, pre, f, len, rws, rest, n_orig, ig0,
    bigs0, lb0, items0, bkts, tbl, b1, eb1, b2, eb2,
    Arr.Arr.dup(+List<SolveFast.CWord>, b2), t1, et1, t2, et2,
    Arr.Arr.dup(U32, t2), hf5, hnd_gp, hnh, hb, htbl, ih)

def FH.drain5_go_spec(+fg: +List<SolveFast.FGroup>, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +gn: Nat, +n_root: Nat, +pre: +List<SolveFast.FGroup>,
    +n_orig: Nat, +ig0: +List<Groups.Group>, +bigs0: +List<SolveFast.BigClass>,
    +lb0: Nat, +items0: +List<SolveFast.Item>,
    bkts: Array<+List<SolveFast.CWord>>, tbl: Array<U32>,
    +hwf: {FH.fgroups_wf(fg) == True{} : Bool},
    +hdisj: {FH.disjoint_codes(pre, fg) == True{} : Bool},
    +hnd_fg: {FN.FN.nodup_ok_jobs(True{},
                MV.MV.next_groups(FN.FN.fgroups_to_groups(fg))) == True{} : Bool},
    +hok_bigs0: {FH.bigs_ok_b(G, C, n_root, bigs0) == True{} : Bool},
    +hbm0: FH.BodyMatch(G, C, n_root, True{}, True{}, n_orig, ig0, items0),
    +elb0: {lb0 == FH.body_lb(True{}, n_orig, items0) : Nat},
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts,
           List.append(&2, SolveFast.FGroup, pre, fg)),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl)) ->
  FH.DrainSpec(G, C, n_root, pre, fg, n_orig, ig0, bigs0, tbl,
    SolveFast.drain5_go(gn, FH.rev_codes(fg, Nil{}),
      SolveFast.Drain5State{bkts, tbl, lb0, items0, bigs0})):
  match fg:
    case Nil{}:
      Arr.DPair{
        FH.bkt_tree_transport_fg(G, C, n_root, 10n, 0, bkts,
          List.append(&2, SolveFast.FGroup, pre, Nil{}), pre,
          FH.list_append_nil(SolveFast.FGroup, pre), hb),
        Arr.DPair{{==},
          DWit{ig0, FP.PRefl{}, hok_bigs0, hbm0, elb0, {==}}}}
    case Con{gp, +rest}:
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
          +hnd_gp = Logic.Proof.and_true_l(
                      FN.FN.no_dup_ref(SolveFast.rev_words(rws, Nil{})),
                      FN.FN.nodup_ok_jobs(True{},
                        MV.MV.next_groups(FN.FN.fgroups_to_groups(rest))),
                      hnd_fg)
          +hnd_rest = Logic.Proof.and_true_r(
                        FN.FN.no_dup_ref(SolveFast.rev_words(rws, Nil{})),
                        FN.FN.nodup_ok_jobs(True{},
                          MV.MV.next_groups(FN.FN.fgroups_to_groups(rest))),
                        hnd_fg)
          +eapp : {List.append(&2, SolveFast.FGroup, pre, gp1 <> rest)
                   == List.append(&2, SolveFast.FGroup, pre2, rest)
                   : +List<SolveFast.FGroup>} =
            Equal.sym(+List<SolveFast.FGroup>,
              List.append(&2, SolveFast.FGroup, pre2, rest),
              List.append(&2, SolveFast.FGroup, pre, gp1 <> rest),
              FH.list_append_assoc(SolveFast.FGroup, pre, gp1 <> Nil{}, rest))
          +hb_pre2 = FH.bkt_tree_transport_fg(G, C, n_root, 10n, 0, bkts,
                       List.append(&2, SolveFast.FGroup, pre, gp1 <> rest),
                       List.append(&2, SolveFast.FGroup, pre2, rest), eapp, hb)
          FH.drain5_go_cons_dup(G, C, gn, n_root, pre, f, len, rws, rest, n_orig,
            ig0, bigs0, lb0, items0, bkts, tbl, hf5, hnd_gp, hnh_pre, hb_pre2,
            htbl, Arr.Arr.dup(+List<SolveFast.CWord>, bkts),
            Arr.Arr.dup(U32, tbl),
            b2 => t2 => hb2 => ht2 =>
              FH.drain5_go_spec(rest, G, C, gn, n_root, pre2, n_orig, ig0, bigs0,
                lb0, items0, b2, t2, hr, hd_pre2, hnd_rest, hok_bigs0, hbm0,
                elb0, hb2, ht2))


# ---------------------------------------------------------------------------
# Buffer invariant `FH.BufOk`, `mk_buf_tbl`, `buf_dup`, and `FH.GuessSpec`
# ---------------------------------------------------------------------------

def FH.BufOk(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +nodup: Bool, buf: SolveFast.Buf5) -> Data:
  match has_buf:
    case False{}:
      match buf:
        case SolveFast.NoBuf{}:
          Unit
        case SolveFast.Buf5{_, _, _, _, _}:
          Empty
    case True{}:
      match buf:
        case SolveFast.NoBuf{}:
          Empty
        case SolveFast.Buf5{seen, buckets, tbl, gen, gn}:
          Arr.Arr.DPair<
            {nodup == True{} : Bool},
            Arr.Arr.DPair<
              FH.SeenTree(10n, 0, seen, gen, Nil{}),
              Arr.Arr.DPair<
                FH.BktTree(G, C, n_root, 10n, 0, buckets, Nil{}),
                Arr.Arr.DPair<
                  FT.FT.TblOk(G, C, n_root, tbl),
                  {gn == Groups.len_words(G) : Nat}>>>>

def FH.buf_ok_transport(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +has_buf: Bool, +nodup: Bool,
    -b1: SolveFast.Buf5, -b2: SolveFast.Buf5,
    +eb: {b1 == b2 : SolveFast.Buf5},
    +h: FH.BufOk(G, C, n_root, has_buf, nodup, b1)) ->
  FH.BufOk(G, C, n_root, has_buf, nodup, b2):
  %eb : FH.BufOk(G, C, n_root, has_buf, nodup, _)
  h

def FH.mk_buf_has_depth(md: Maybe<Nat>) -> Bool:
  match md:
    case None{}:
      False{}
    case Some{d}:
      True{}

def FH.mk_buf_has_if(ok: Bool, +G: +List<+List<Nat>>, +n: Nat) -> Bool:
  match ok:
    case False{}:
      False{}
    case True{}:
      FH.mk_buf_has_depth(SolveFast.depth_for(Nat.mul(Groups.len_words(G), n)))

def FH.mk_buf_has(+nodup: Bool, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n: Nat) -> Bool:
  match nodup:
    case False{}:
      False{}
    case True{}:
      FH.mk_buf_has_if(Bool.and(SolveFast.all_len5(G), SolveFast.all_len5(C)),
        G, n)

def FH.mk_buf_tbl_depth_ok(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n: Nat, md: Maybe<Nat>,
    +emd: {SolveFast.depth_for(Nat.mul(Groups.len_words(G), n)) == md
           : Maybe<Nat>},
    +hdsp: FT.FT.DepthSpec(Nat.mul(Groups.len_words(G), n), md),
    +en: {Groups.len_words(C) == n : Nat},
    +hg5: {SolveFast.all_len5(G) == True{} : Bool},
    +hc5: {SolveFast.all_len5(C) == True{} : Bool}) ->
  FH.BufOk(G, C, n, FH.mk_buf_has_depth(md), True{},
    SolveFast.mk_buf_tbl_depth(G, C, Groups.len_words(G),
      U32.from_nat(Groups.len_words(G)), md)):
  match md:
    case None{}:
      Unit{}
    case Some{+d}:
      +hd = Arr.Arr.dpair_l({Nat.is_lt(d, 32n) == True{} : Bool},
              {Nat.is_le(Nat.mul(Groups.len_words(G), n), FT.FT.pow2(d))
               == True{} : Bool}, hdsp)
      +hb = Arr.Arr.dpair_r({Nat.is_lt(d, 32n) == True{} : Bool},
              {Nat.is_le(Nat.mul(Groups.len_words(G), n), FT.FT.pow2(d))
               == True{} : Bool}, hdsp)
      Arr.DPair{{==}, Arr.DPair{
        FH.seen_tree_new(10n, 0),
        Arr.DPair{
          FH.bkt_tree_new(G, C, n, 10n, 0),
          Arr.DPair{
            FT.FT.mk_tbl_ok_go(G, C, n, d, emd, hd, hb, en, hg5, hc5),
            {==}}}}}

def FH.mk_buf_tbl_if_ok(ok: Bool, +G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n: Nat,
    +eok: {ok == Bool.and(SolveFast.all_len5(G), SolveFast.all_len5(C)) : Bool},
    +en: {Groups.len_words(C) == n : Nat}) ->
  FH.BufOk(G, C, n, FH.mk_buf_has_if(ok, G, n), True{},
    SolveFast.mk_buf_tbl_if(ok, G, C, n)):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      +hand : {Bool.and(SolveFast.all_len5(G), SolveFast.all_len5(C))
               == True{} : Bool} =
        Equal.sym(Bool, True{},
          Bool.and(SolveFast.all_len5(G), SolveFast.all_len5(C)), eok)
      +hg5 = Logic.Proof.and_true_l(SolveFast.all_len5(G),
               SolveFast.all_len5(C), hand)
      +hc5 = Logic.Proof.and_true_r(SolveFast.all_len5(G),
               SolveFast.all_len5(C), hand)
      +target = Nat.mul(Groups.len_words(G), n)
      FH.mk_buf_tbl_depth_ok(G, C, n, SolveFast.depth_for(target), {==},
        FT.FT.depth_for_spec(target), en, hg5, hc5)

def FH.mk_buf_tbl_ok(+nodup: Bool, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n: Nat,
    +en: {Groups.len_words(C) == n : Nat}) ->
  FH.BufOk(G, C, n, FH.mk_buf_has(nodup, G, C, n), nodup,
    SolveFast.mk_buf_tbl(nodup, G, C, n)):
  match nodup:
    case False{}:
      Unit{}
    case True{}:
      FH.mk_buf_tbl_if_ok(
        Bool.and(SolveFast.all_len5(G), SolveFast.all_len5(C)), G, C, n,
        {==}, en)

def FH.buf_dup_go(-seen: Array<Nat>, -bkts: Array<+List<SolveFast.CWord>>,
    -tbl: Array<U32>, +gen: Nat, +gn: Nat,
    ds: &s1: Array<Nat> -> &s2: Array<Nat> ->
        {s1 == seen : Array<Nat>} & {s2 == s1 : Array<Nat>},
    db: &k1: Array<+List<SolveFast.CWord>> -> &k2: Array<+List<SolveFast.CWord>> ->
        {k1 == bkts : Array<+List<SolveFast.CWord>>}
        & {k2 == k1 : Array<+List<SolveFast.CWord>>},
    dt: &t1: Array<U32> -> &t2: Array<U32> ->
        {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>}) ->
  &b1: SolveFast.Buf5 -> &b2: SolveFast.Buf5 ->
  {b1 == SolveFast.Buf5{seen, bkts, tbl, gen, gn} : SolveFast.Buf5}
  & {b2 == b1 : SolveFast.Buf5}:
  (s1, ds2) = ds
  (s2, ps) = ds2
  (+es1, +es2) = ps
  (k1, db2) = db
  (k2, pk) = db2
  (+ek1, +ek2) = pk
  (t1, dt2) = dt
  (t2, pt) = dt2
  (+et1, +et2) = pt
  +e1 : {SolveFast.Buf5{s1, k1, t1, gen, gn} == SolveFast.Buf5{seen, bkts, tbl, gen, gn}
         : SolveFast.Buf5} =
    Equal.trans(SolveFast.Buf5,
      SolveFast.Buf5{s1, k1, t1, gen, gn},
      SolveFast.Buf5{seen, k1, t1, gen, gn},
      SolveFast.Buf5{seen, bkts, tbl, gen, gn},
      Equal.cong(Array<Nat>, SolveFast.Buf5,
        s => SolveFast.Buf5{s, k1, t1, gen, gn}, s1, seen, es1),
      Equal.trans(SolveFast.Buf5,
        SolveFast.Buf5{seen, k1, t1, gen, gn},
        SolveFast.Buf5{seen, bkts, t1, gen, gn},
        SolveFast.Buf5{seen, bkts, tbl, gen, gn},
        Equal.cong(Array<+List<SolveFast.CWord>>, SolveFast.Buf5,
          k => SolveFast.Buf5{seen, k, t1, gen, gn}, k1, bkts, ek1),
        Equal.cong(Array<U32>, SolveFast.Buf5,
          t => SolveFast.Buf5{seen, bkts, t, gen, gn}, t1, tbl, et1)))
  +e2 : {SolveFast.Buf5{s2, k2, t2, gen, gn} == SolveFast.Buf5{s1, k1, t1, gen, gn}
         : SolveFast.Buf5} =
    Equal.trans(SolveFast.Buf5,
      SolveFast.Buf5{s2, k2, t2, gen, gn},
      SolveFast.Buf5{s1, k2, t2, gen, gn},
      SolveFast.Buf5{s1, k1, t1, gen, gn},
      Equal.cong(Array<Nat>, SolveFast.Buf5,
        s => SolveFast.Buf5{s, k2, t2, gen, gn}, s2, s1, es2),
      Equal.trans(SolveFast.Buf5,
        SolveFast.Buf5{s1, k2, t2, gen, gn},
        SolveFast.Buf5{s1, k1, t2, gen, gn},
        SolveFast.Buf5{s1, k1, t1, gen, gn},
        Equal.cong(Array<+List<SolveFast.CWord>>, SolveFast.Buf5,
          k => SolveFast.Buf5{s1, k, t2, gen, gn}, k2, k1, ek2),
        Equal.cong(Array<U32>, SolveFast.Buf5,
          t => SolveFast.Buf5{s1, k1, t, gen, gn}, t2, t1, et2)))
  (SolveFast.Buf5{s1, k1, t1, gen, gn}, (SolveFast.Buf5{s2, k2, t2, gen, gn}, (e1, e2)))

def FH.buf_dup(buf: SolveFast.Buf5) ->
  &b1: SolveFast.Buf5 -> &b2: SolveFast.Buf5 ->
  {b1 == buf : SolveFast.Buf5} & {b2 == b1 : SolveFast.Buf5}:
  match buf:
    case SolveFast.NoBuf{}:
      (SolveFast.NoBuf{}, (SolveFast.NoBuf{}, ({==}, {==})))
    case SolveFast.Buf5{seen, bkts, tbl, +gen, gn}:
      FH.buf_dup_go(seen, bkts, tbl, gen, gn,
        Arr.Arr.dup(Nat, seen),
        Arr.Arr.dup(+List<SolveFast.CWord>, bkts),
        Arr.Arr.dup(U32, tbl))

# Semantic 5-case classification for `guess_items_buf`.
type FH.GuessCase is Data:
  GCSkipSelf{}
  GCSkipUnusable{}
  GCSkipPre{}
  GCSkipLb{}
  GCSkipCap{}
  GCLive{ord: +List<Groups.Group>, body: +List<SolveFast.Item>, perm: FP.FP.Perm}

def FH.GuessCaseOk(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +nodup: Bool, +g: +List<Nat>, +S: +List<+List<Nat>>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, +items: +List<SolveFast.Item>,
    gc: FH.GuessCase) -> Data:
  match gc:
    case GCSkipSelf{}:
      Arr.Arr.DPair<
        {items == Nil{} : +List<SolveFast.Item>},
        Arr.Arr.DPair<
          {nodup == True{} : Bool},
          Arr.Arr.DPair<
            {floor == Nat.add(n, n) : Nat},
            {Tree.member_word(g, S) == True{} : Bool}>>>
    case GCSkipUnusable{}:
      Arr.Arr.DPair<
        {items == Nil{} : +List<SolveFast.Item>},
        {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
         == False{} : Bool}>
    case GCSkipPre{}:
      Arr.Arr.DPair<
        {items == Nil{} : +List<SolveFast.Item>},
        {Nat.is_le(Eval.Eval.cost_of(best), SolveFast.pre_lb(n, g, S))
         == True{} : Bool}>
    case GCSkipLb{}:
      Arr.Arr.DPair<
        {items == Nil{} : +List<SolveFast.Item>},
        {Nat.is_le(Eval.Eval.cost_of(best),
           SolveFast.lower_bound(n, Groups.groups_build(g, S, Nil{})))
         == True{} : Bool}>
    case GCSkipCap{}:
      Arr.Arr.DPair<
        {items == Nil{} : +List<SolveFast.Item>},
        Arr.Arr.DPair<
          {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
          Arr.Arr.DPair<
            {nodup == True{} : Bool},
            {Nat.is_le(Eval.Eval.cost_of(best),
               FH.cap_lb(G, Groups.len_words(S),
                 Groups.groups_build(g, S, Nil{})))
             == True{} : Bool}>>>
    case GCLive{ord, body, perm}:
      Arr.Arr.DPair<
        {items == SolveFast.Begin{g} <> body : +List<SolveFast.Item>},
        Arr.Arr.DPair<
          {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
          Arr.Arr.DPair<
            FP.FP.PermOk(perm, Groups.groups_build(g, S, Nil{}), ord),
            FH.BodyMatch(G, C, n_root, has_buf, nodup, n, ord, body)>>>

type FH.GuessWit<+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +nodup: Bool, +g: +List<Nat>, +S: +List<+List<Nat>>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best,
    +items: +List<SolveFast.Item>> is Data:
  GWit{gc: FH.GuessCase,
       ok: FH.GuessCaseOk(G, C, n_root, has_buf, nodup, g, S, n, floor, best,
             items, gc)}

def FH.GuessSpec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n_root: Nat,
    +has_buf: Bool, +nodup: Bool, +g: +List<Nat>, +S: +List<+List<Nat>>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best,
    gr: SolveFast.GuessRes) -> Data:
  match gr:
    case SolveFast.GuessRes{items, buf}:
      Arr.Arr.DPair<
        FH.GuessWit<G, C, n_root, has_buf, nodup, g, S, n, floor, best, items>,
        FH.BufOk(G, C, n_root, has_buf, nodup, buf)>

# What the capacity walk's result gives the model: a skip carries the bound,
# a completed walk carries the unchanged class list.
def FH.CapWalkWit(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +bs0: +List<SolveFast.BigClass>, +capv: Nat,
    +best: SolveRef.Best, r: SolveFast.CapRes) -> Data:
  match r:
    case SolveFast.CapSkip{tbl}:
      Arr.Arr.DPair<
        {Nat.is_le(SolveFast.best_cost(best), capv) == True{} : Bool},
        FT.FT.TblOk(G, C, n_root, tbl)>
    case SolveFast.CapOk{bigs, tbl}:
      Arr.Arr.DPair<{bigs == bs0 : List<&2, SolveFast.BigClass>},
        FT.FT.TblOk(G, C, n_root, tbl)>

# The hook that supplies the capacity walk's specification from above (the
# walk's proof lives in cap_walk.bend, which imports this module).
def FH.CapHookType(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>) -> Type:
  @+gn: Nat ->
  @+n_root: Nat ->
  @+bigs0: +List<SolveFast.BigClass> ->
  @+items0: +List<SolveFast.Item> ->
  @tbl0: Array<U32> ->
  @+best: SolveRef.Best ->
  @+n: Nat ->
  @+capv: Nat ->
  @+hgn: {gn == Groups.len_words(G) : Nat} ->
  @+hok: {FH.bigs_ok_b(G, C, n_root, bigs0) == True{} : Bool} ->
  @+htbl: FT.FT.TblOk(G, C, n_root, tbl0) ->
  @+hb: {Nat.is_le(Nat.add(
             Nat.add(Nat.add(SolveFast.bigs_depth(bigs0),
               SolveFast.cap_base(n, items0)), 0n),
             Nat.sub(FH.cap_fold(G, FH.bigs_groups(bigs0)),
               SolveFast.bigs_depth(bigs0))), capv) == True{} : Bool} ->
  FH.CapWalkWit(G, C, n_root, bigs0, capv, best,
    SolveFast.cap_walk(
      Nat.add(Nat.add(SolveFast.bigs_len(bigs0), SolveFast.bigs_len(bigs0)), 2n),
      bigs0, bigs0, 1n,
      Nat.is_le(SolveFast.best_cost(best),
        Nat.add(SolveFast.bigs_depth(bigs0), SolveFast.cap_base(n, items0))),
      Nil{}, 0n, Nat.add(SolveFast.bigs_depth(bigs0),
        SolveFast.cap_base(n, items0)), best, gn, SolveFast.ck_cheap(0n, tbl0)))

def FH.run_drain5_spec_dw(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +gn: Nat, +hgn: {gn == Groups.len_words(G) : Nat},
    hook: FH.CapHookType(G, C),
    +n_root: Nat, +g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat, +floor: Nat,
    +best: SolveRef.Best, -seen: Array<Nat>, +gen2: Nat,
    -bkts3: Array<+List<SolveFast.CWord>>, -tbl3: Array<U32>,
    +lb3: Nat, +items3: +List<SolveFast.Item>,
    +bigs3: +List<SolveFast.BigClass>,
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
    +hs: FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +hb3: FH.BktTree(G, C, n_root, 10n, 0, bkts3, Nil{}),
    +htbl3: FT.FT.TblOk(G, C, n_root, tbl3),
    +dw: FH.DrainWit<G, C, n_root, SolveFast.fgroups_build_fast(g, S, Nil{}),
           n, Nil{}, Nil{}, lb3, items3, bigs3>) ->
  FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
    SolveFast.GuessRes{
      SolveFast.Begin{g} <> SolveFast.emit_bigs(bigs3, lb3, items3),
      SolveFast.Buf5{seen, bkts3, tbl3, gen2, gn}}):
  match dw:
    case DWit{+ig, +perm1, +hok_bigs, +hbm, +elb, +hperm1}:
      +fg = SolveFast.fgroups_build_fast(g, S, Nil{})
      +bs_g = FH.bigs_groups(bigs3)
      +ord = FP.FP.rev_groups(bs_g, ig)
      +body = SolveFast.emit_bigs(bigs3, lb3, items3)
      +hbm_all = FH.emit_bigs_spec(G, C, n_root, n, bigs3, lb3, items3, ig,
                   hok_bigs, hbm, elb)
      +efg_app : {Groups.groups_build(g, S, Nil{})
                  == List.append(&2, Groups.Group,
                       FN.FN.fgroups_to_groups(fg), Nil{})
                  : +List<Groups.Group>} =
        Equal.sym(+List<Groups.Group>,
          List.append(&2, Groups.Group, FN.FN.fgroups_to_groups(fg), Nil{}),
          Groups.groups_build(g, S, Nil{}),
          Equal.trans(+List<Groups.Group>,
            List.append(&2, Groups.Group, FN.FN.fgroups_to_groups(fg), Nil{}),
            FN.FN.fgroups_to_groups(fg),
            Groups.groups_build(g, S, Nil{}),
            FH.list_append_nil(Groups.Group, FN.FN.fgroups_to_groups(fg)),
            FN.FN.fgroups_build_eq(g, S, Nil{})))
      +p_rev = FP.FP.perm_sym(FP.FP.perm_rev_append(bs_g, ig))
      +hp_rev = FP.FP.perm_sym_ok(FP.FP.perm_rev_append(bs_g, ig),
                  ord, List.append(&2, Groups.Group, bs_g, ig),
                  FP.FP.perm_rev_append_ok(bs_g, ig))
      +p_full : FP.FP.Perm = FP.PTrans{
                  List.append(&2, Groups.Group, FN.FN.fgroups_to_groups(fg), Nil{}),
                  FP.PRefl{},
                  FP.PTrans{List.append(&2, Groups.Group, bs_g, ig),
                    perm1, p_rev}}
      +hp_full : FP.FP.PermOk(p_full, Groups.groups_build(g, S, Nil{}), ord) =
        Arr.DPair{efg_app, Arr.DPair{hperm1, hp_rev}}
      Arr.DPair{
        GWit{GCLive{ord, body, p_full},
          Arr.DPair{{==}, Arr.DPair{hus, Arr.DPair{hp_full, hbm_all}}}},
        Arr.DPair{{==}, Arr.DPair{hs, Arr.DPair{hb3,
          Arr.DPair{htbl3, hgn}}}}}

def FH.finish_drain5_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +gn: Nat, +hgn: {gn == Groups.len_words(G) : Nat},
    hook: FH.CapHookType(G, C),
    +n_root: Nat, +g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat, +floor: Nat,
    +best: SolveRef.Best, -seen: Array<Nat>, -tbl0: Array<U32>, +gen2: Nat,
    dr: SolveFast.Drain5State,
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
    +hs: FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    +hdr: FH.DrainSpec(G, C, n_root, Nil{},
            SolveFast.fgroups_build_fast(g, S, Nil{}), n, Nil{}, Nil{}, tbl0,
            dr)) ->
  FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
    SolveFast.finish_drain5(g, seen, gen2, gn, best, n, dr)):
  match dr:
    case SolveFast.Drain5State{bkts3, tbl3, +lb3, +items3, +bigs3}:
      +fg = SolveFast.fgroups_build_fast(g, S, Nil{})
      +hb3 = Arr.Arr.dpair_l(
               FH.BktTree(G, C, n_root, 10n, 0, bkts3, Nil{}),
               Arr.Arr.DPair<{tbl3 == tbl0 : Array<U32>},
                 FH.DrainWit<G, C, n_root, fg, n, Nil{}, Nil{}, lb3, items3,
                   bigs3>>, hdr)
      +hr = Arr.Arr.dpair_r(
              FH.BktTree(G, C, n_root, 10n, 0, bkts3, Nil{}),
              Arr.Arr.DPair<{tbl3 == tbl0 : Array<U32>},
                FH.DrainWit<G, C, n_root, fg, n, Nil{}, Nil{}, lb3, items3,
                  bigs3>>, hdr)
      +et3 = Arr.Arr.dpair_l({tbl3 == tbl0 : Array<U32>},
               FH.DrainWit<G, C, n_root, fg, n, Nil{}, Nil{}, lb3, items3,
                 bigs3>, hr)
      +dw = Arr.Arr.dpair_r({tbl3 == tbl0 : Array<U32>},
              FH.DrainWit<G, C, n_root, fg, n, Nil{}, Nil{}, lb3, items3,
                bigs3>, hr)
      +htbl3 = FT.FT.tbl_ok_transport(G, C, n_root, tbl0, tbl3,
                 Equal.sym(Array<U32>, tbl3, tbl0, et3), htbl0)
      FH.run_drain5_spec_dw(G, C, gn, hgn, hook, n_root, g, S, n, floor, best, seen, gen2,
        bkts3, tbl3, lb3, items3, bigs3, hus, hs, hb3, htbl3, dw)

def FH.run_drain5_spec_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +gn: Nat, +hgn: {gn == Groups.len_words(G) : Nat},
    hook: FH.CapHookType(G, C),
    +n_root: Nat, +g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat, +floor: Nat,
    +best: SolveRef.Best, -seen: Array<Nat>, +gen2: Nat,
    -bkts2: Array<+List<SolveFast.CWord>>, -tbl0: Array<U32>, -tbl2: Array<U32>,
    +touched: +List<U32>,
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
    +hnd_s: {FN.FN.no_dup_ref(S) == True{} : Bool},
    +hs: FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    +et20: {tbl2 == tbl0 : Array<U32>},
    +hb2: FH.BktTree(G, C, n_root, 10n, 0, bkts2,
            SolveFast.fgroups_build_fast(g, S, Nil{})),
    +etouched: {touched == FH.rev_codes(SolveFast.fgroups_build_fast(g, S, Nil{}), Nil{})
                : +List<U32>},
    +hwf: {FH.fgroups_wf(SolveFast.fgroups_build_fast(g, S, Nil{}))
           == True{} : Bool},
    dpb: &b1: Array<+List<SolveFast.CWord>> -> &b2: Array<+List<SolveFast.CWord>> ->
         {b1 == bkts2 : Array<+List<SolveFast.CWord>>}
         & {b2 == b1 : Array<+List<SolveFast.CWord>>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl2 : Array<U32>} & {t2 == t1 : Array<U32>}) ->
  FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
    SolveFast.finish_drain5(g, seen, gen2, gn, best, n,
      SolveFast.drain5_go(gn, touched,
        SolveFast.Drain5State{bkts2, tbl2, n, SolveFast.End{} <> Nil{}, Nil{}}))):
  (b1, dpb2) = dpb
  (b2, peb) = dpb2
  (+eb1, +eb2) = peb
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2) = pet
  +fg = SolveFast.fgroups_build_fast(g, S, Nil{})
  +eb2_bk : {b2 == bkts2 : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, b2, b1, bkts2, eb2, eb1)
  +et2_t2 : {t2 == tbl2 : Array<U32>} = Equal.trans(Array<U32>, t2, t1, tbl2, et2, et1)
  +et2_t0 : {t2 == tbl0 : Array<U32>} = Equal.trans(Array<U32>, t2, tbl2, tbl0, et2_t2, et20)
  +hb_b2 = FH.bkt_tree_transport(G, C, n_root, 10n, 0, bkts2, b2, fg,
             Equal.sym(Array<+List<SolveFast.CWord>>, b2, bkts2, eb2_bk), hb2)
  +ht_t2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl0, t2,
             Equal.sym(Array<U32>, t2, tbl0, et2_t0), htbl0)
  +hnd_fg : {FN.FN.nodup_ok_jobs(True{},
               MV.MV.next_groups(FN.FN.fgroups_to_groups(fg))) == True{} : Bool} =
    Equal.trans(Bool,
      FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(FN.FN.fgroups_to_groups(fg))),
      FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(Groups.groups_build(g, S, Nil{}))),
      True{},
      Equal.cong(+List<Groups.Group>, Bool,
        gs => FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(gs)),
        FN.FN.fgroups_to_groups(fg), Groups.groups_build(g, S, Nil{}),
        FN.FN.fgroups_build_eq(g, S, Nil{})),
      FN.FN.nodup_ok_next_groups(True{}, Groups.groups_build(g, S, Nil{}), S,
        CoverGroups.Cover.all_subseq_nil(g, S), hnd_s))
  +hdr2 = FH.drain5_go_spec(fg, G, C, gn, n_root, Nil{}, n, Nil{}, Nil{}, n,
            SolveFast.End{} <> Nil{}, b2, t2, hwf, FH.disjoint_codes_nil(fg),
            hnd_fg, {==}, {==}, {==}, hb_b2, ht_t2)
  +hdr_t0 = FH.drain_spec_transport_tbl(G, C, n_root, Nil{}, fg, n, Nil{}, Nil{},
              t2, tbl0,
              SolveFast.drain5_go(gn, FH.rev_codes(fg, Nil{}),
                SolveFast.Drain5State{b2, t2, n, SolveFast.End{} <> Nil{}, Nil{}}),
              et2_t0, hdr2)
  +eq_12 : {SolveFast.drain5_go(gn, FH.rev_codes(fg, Nil{}),
              SolveFast.Drain5State{b2, t2, n, SolveFast.End{} <> Nil{}, Nil{}})
            == SolveFast.drain5_go(gn, FH.rev_codes(fg, Nil{}),
                 SolveFast.Drain5State{b1, t1, n, SolveFast.End{} <> Nil{}, Nil{}})
            : SolveFast.Drain5State} =
    Equal.trans(SolveFast.Drain5State,
      SolveFast.drain5_go(gn, FH.rev_codes(fg, Nil{}),
        SolveFast.Drain5State{b2, t2, n, SolveFast.End{} <> Nil{}, Nil{}}),
      SolveFast.drain5_go(gn, FH.rev_codes(fg, Nil{}),
        SolveFast.Drain5State{b1, t2, n, SolveFast.End{} <> Nil{}, Nil{}}),
      SolveFast.drain5_go(gn, FH.rev_codes(fg, Nil{}),
        SolveFast.Drain5State{b1, t1, n, SolveFast.End{} <> Nil{}, Nil{}}),
      Equal.cong(Array<+List<SolveFast.CWord>>, SolveFast.Drain5State,
        x => SolveFast.drain5_go(gn, FH.rev_codes(fg, Nil{}),
               SolveFast.Drain5State{x, t2, n, SolveFast.End{} <> Nil{}, Nil{}}),
        b2, b1, eb2),
      Equal.cong(Array<U32>, SolveFast.Drain5State,
        y => SolveFast.drain5_go(gn, FH.rev_codes(fg, Nil{}),
               SolveFast.Drain5State{b1, y, n, SolveFast.End{} <> Nil{}, Nil{}}),
        t2, t1, et2))
  +hdr1 = FH.drain_spec_transport(G, C, n_root, Nil{}, fg, n, Nil{}, Nil{},
            tbl0,
            SolveFast.drain5_go(gn, FH.rev_codes(fg, Nil{}),
              SolveFast.Drain5State{b2, t2, n, SolveFast.End{} <> Nil{}, Nil{}}),
            SolveFast.drain5_go(gn, FH.rev_codes(fg, Nil{}),
              SolveFast.Drain5State{b1, t1, n, SolveFast.End{} <> Nil{}, Nil{}}),
            eq_12, hdr_t0)
  %eb1 : FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
           SolveFast.finish_drain5(g, seen, gen2, gn, best, n,
             SolveFast.drain5_go(gn, touched,
               SolveFast.Drain5State{_, tbl2, n, SolveFast.End{} <> Nil{}, Nil{}})))
  %et1 : FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
           SolveFast.finish_drain5(g, seen, gen2, gn, best, n,
             SolveFast.drain5_go(gn, touched,
               SolveFast.Drain5State{b1, _, n, SolveFast.End{} <> Nil{}, Nil{}})))
  %Equal.sym(+List<U32>, touched, FH.rev_codes(fg, Nil{}), etouched) :
    FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
      SolveFast.finish_drain5(g, seen, gen2, gn, best, n,
        SolveFast.drain5_go(gn, _,
          SolveFast.Drain5State{b1, t1, n, SolveFast.End{} <> Nil{}, Nil{}})))
  FH.finish_drain5_spec(G, C, gn, hgn, hook, n_root, g, S, n, floor, best, seen, tbl0, gen2,
    SolveFast.drain5_go(gn, FH.rev_codes(fg, Nil{}),
      SolveFast.Drain5State{b1, t1, n, SolveFast.End{} <> Nil{}, Nil{}}),
    hus, hs, htbl0, hdr1)

def FH.run_drain5_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +gn: Nat, +hgn: {gn == Groups.len_words(G) : Nat},
    hook: FH.CapHookType(G, C),
    +n_root: Nat, +g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat, +floor: Nat,
    +best: SolveRef.Best, -seen: Array<Nat>, -tbl0: Array<U32>, +gen2: Nat,
    fs: SolveFast.Fill5State,
    +hus: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           == True{} : Bool},
    +hnd_s: {FN.FN.no_dup_ref(S) == True{} : Bool},
    +hs: FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    +hfs: FH.FillSpec(G, C, n_root, SolveFast.fgroups_build_fast(g, S, Nil{}),
            Nil{}, tbl0, fs)) ->
  FH.GuessSpec(G, C, n_root, True{}, True{}, g, S, n, floor, best,
    SolveFast.run_drain5(g, n, seen, gen2, gn, best, fs)):
  match fs:
    case SolveFast.Fill5State{bkts2, tbl2, +touched}:
      +fg = SolveFast.fgroups_build_fast(g, S, Nil{})
      +hb2 = Arr.Arr.dpair_l(
               FH.BktTree(G, C, n_root, 10n, 0, bkts2, fg),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 Arr.Arr.DPair<{touched == FH.rev_codes(fg, Nil{}) : +List<U32>},
                   {FH.fgroups_wf(fg) == True{} : Bool}>>, hfs)
      +r1 = Arr.Arr.dpair_r(
              FH.BktTree(G, C, n_root, 10n, 0, bkts2, fg),
              Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                Arr.Arr.DPair<{touched == FH.rev_codes(fg, Nil{}) : +List<U32>},
                  {FH.fgroups_wf(fg) == True{} : Bool}>>, hfs)
      +et20 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
                Arr.Arr.DPair<{touched == FH.rev_codes(fg, Nil{}) : +List<U32>},
                  {FH.fgroups_wf(fg) == True{} : Bool}>, r1)
      +r2 = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
              Arr.Arr.DPair<{touched == FH.rev_codes(fg, Nil{}) : +List<U32>},
                {FH.fgroups_wf(fg) == True{} : Bool}>, r1)
      +et = Arr.Arr.dpair_l({touched == FH.rev_codes(fg, Nil{}) : +List<U32>},
              {FH.fgroups_wf(fg) == True{} : Bool}, r2)
      +hwf = Arr.Arr.dpair_r({touched == FH.rev_codes(fg, Nil{}) : +List<U32>},
               {FH.fgroups_wf(fg) == True{} : Bool}, r2)
      FH.run_drain5_spec_dup(G, C, gn, hgn, hook, n_root, g, S, n, floor, best, seen, gen2,
        bkts2, tbl0, tbl2, touched, hus, hnd_s, hs, htbl0, et20, hb2, et, hwf,
        Arr.Arr.dup(+List<SolveFast.CWord>, bkts2), Arr.Arr.dup(U32, tbl2))

def FH.schedule5_lb_false_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +gn: Nat, +hgn: {gn == Groups.len_words(G) : Nat},
    hook: FH.CapHookType(G, C),
    +n_root: Nat, +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, -seen: Array<Nat>,
    -bkts: Array<+List<SolveFast.CWord>>, -tbl: Array<U32>, +gen2: Nat,
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hS: {FT.FT.cwords_ok_b(G, C, n_root, S) == True{} : Bool},
    +hus: {Groups.groups_smaller(SolveFast.cwords_words(S),
             Groups.groups_build(g, SolveFast.cwords_words(S), Nil{}))
           == True{} : Bool},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hs: FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    dpb: &b1: Array<+List<SolveFast.CWord>> -> &b2: Array<+List<SolveFast.CWord>> ->
         {b1 == bkts : Array<+List<SolveFast.CWord>>}
         & {b2 == b1 : Array<+List<SolveFast.CWord>>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>}) ->
  FH.GuessSpec(G, C, n_root, True{}, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.run_drain5(g, n, seen, gen2, gn, best,
      SolveFast.fill5_go(row, S, SolveFast.Fill5State{bkts, tbl, Nil{}}))):
  (b1, dpb2) = dpb
  (b2, peb) = dpb2
  (+eb1, +eb2) = peb
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2) = pet
  +ws = SolveFast.cwords_words(S)
  +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
  +eb2_bk : {b2 == bkts : Array<+List<SolveFast.CWord>>} =
    Equal.trans(Array<+List<SolveFast.CWord>>, b2, b1, bkts, eb2, eb1)
  +et2_t : {t2 == tbl : Array<U32>} = Equal.trans(Array<U32>, t2, t1, tbl, et2, et1)
  +hb2 = FH.bkt_tree_transport(G, C, n_root, 10n, 0, bkts, b2, Nil{},
           Equal.sym(Array<+List<SolveFast.CWord>>, b2, bkts, eb2_bk), hb)
  +ht2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl, t2,
           Equal.sym(Array<U32>, t2, tbl, et2_t), htbl)
  +hfs2 = FH.fill5_go_spec(S, G, C, n_root, row, g, Nil{}, b2, t2, Nil{}, Nil{},
            ht2, hrow, hS, {==}, {==}, hb2)
  +hfs_t0 = FH.fill_spec_transport_tbl(G, C, n_root, fg, Nil{}, t2, tbl,
              SolveFast.fill5_go(row, S, SolveFast.Fill5State{b2, t2, Nil{}}),
              et2_t, hfs2)
  +eq_12 : {SolveFast.fill5_go(row, S, SolveFast.Fill5State{b2, t2, Nil{}})
            == SolveFast.fill5_go(row, S, SolveFast.Fill5State{b1, t1, Nil{}})
            : SolveFast.Fill5State} =
    Equal.trans(SolveFast.Fill5State,
      SolveFast.fill5_go(row, S, SolveFast.Fill5State{b2, t2, Nil{}}),
      SolveFast.fill5_go(row, S, SolveFast.Fill5State{b1, t2, Nil{}}),
      SolveFast.fill5_go(row, S, SolveFast.Fill5State{b1, t1, Nil{}}),
      Equal.cong(Array<+List<SolveFast.CWord>>, SolveFast.Fill5State,
        x => SolveFast.fill5_go(row, S, SolveFast.Fill5State{x, t2, Nil{}}),
        b2, b1, eb2),
      Equal.cong(Array<U32>, SolveFast.Fill5State,
        y => SolveFast.fill5_go(row, S, SolveFast.Fill5State{b1, y, Nil{}}),
        t2, t1, et2))
  +hfs1 = FH.fill_spec_transport(G, C, n_root, fg, Nil{}, tbl,
            SolveFast.fill5_go(row, S, SolveFast.Fill5State{b2, t2, Nil{}}),
            SolveFast.fill5_go(row, S, SolveFast.Fill5State{b1, t1, Nil{}}),
            eq_12, hfs_t0)
  %eb1 : FH.GuessSpec(G, C, n_root, True{}, True{}, g, ws, n, floor, best,
           SolveFast.run_drain5(g, n, seen, gen2, gn, best,
             SolveFast.fill5_go(row, S, SolveFast.Fill5State{_, tbl, Nil{}})))
  %et1 : FH.GuessSpec(G, C, n_root, True{}, True{}, g, ws, n, floor, best,
           SolveFast.run_drain5(g, n, seen, gen2, gn, best,
             SolveFast.fill5_go(row, S, SolveFast.Fill5State{b1, _, Nil{}})))
  FH.run_drain5_spec(G, C, gn, hgn, hook, n_root, g, ws, n, floor, best, seen, tbl, gen2,
    SolveFast.fill5_go(row, S, SolveFast.Fill5State{b1, t1, Nil{}}),
    hus, hnd_s, hs, htbl, hfs1)

def FH.fgroups_lb_nodup_eq_lb(+g: +List<Nat>, +ws: +List<+List<Nat>>, +n: Nat,
    +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool}) ->
  {SolveFast.fgroups_lb_nodup(SolveFast.fgroups_build_fast(g, ws, Nil{}), n)
   == SolveFast.lower_bound(n, Groups.groups_build(g, ws, Nil{})) : Nat}:
  +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
  +egrp : {FN.FN.fgroups_to_groups(fg) == Groups.groups_build(g, ws, Nil{})
           : +List<Groups.Group>} =
    FN.FN.fgroups_build_eq(g, ws, Nil{})
  +hlok : {FN.FN.fgroups_lens_ok(fg) == True{} : Bool} =
    FN.FN.fgroups_build_lens_ok(g, ws, Nil{}, {==})
  +hng : {FN.FN.nodup_ok_jobs(True{},
            MV.MV.next_groups(FN.FN.fgroups_to_groups(fg))) == True{} : Bool} =
    Equal.trans(Bool,
      FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(FN.FN.fgroups_to_groups(fg))),
      FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(Groups.groups_build(g, ws, Nil{}))),
      True{},
      Equal.cong(+List<Groups.Group>, Bool,
        gs => FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(gs)),
        FN.FN.fgroups_to_groups(fg), Groups.groups_build(g, ws, Nil{}), egrp),
      FN.FN.nodup_ok_next_groups(True{}, Groups.groups_build(g, ws, Nil{}), ws,
        CoverGroups.Cover.all_subseq_nil(g, ws), hnd))
  Equal.trans(Nat,
    SolveFast.fgroups_lb_nodup(fg, n),
    SolveFast.lower_bound(n, FN.FN.fgroups_to_groups(fg)),
    SolveFast.lower_bound(n, Groups.groups_build(g, ws, Nil{})),
    FN.FN.fgroups_lb_eq(True{}, n, fg, hlok, hng),
    Equal.cong(+List<Groups.Group>, Nat, gs => SolveFast.lower_bound(n, gs),
      FN.FN.fgroups_to_groups(fg), Groups.groups_build(g, ws, Nil{}), egrp))

def FH.schedule5_lb_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +gn: Nat, +hgn: {gn == Groups.len_words(G) : Nat},
    hook: FH.CapHookType(G, C),
    +n_root: Nat, +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, -seen: Array<Nat>,
    bkts: Array<+List<SolveFast.CWord>>, tbl: Array<U32>, +gen2: Nat,
    +lb: Nat, skip: Bool,
    +esk: {skip == SolveFast.skippable(best, lb) : Bool},
    +elb: {lb == SolveFast.lower_bound(n,
                   Groups.groups_build(g, SolveFast.cwords_words(S), Nil{}))
           : Nat},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hS: {FT.FT.cwords_ok_b(G, C, n_root, S) == True{} : Bool},
    +hus: {Groups.groups_smaller(SolveFast.cwords_words(S),
             Groups.groups_build(g, SolveFast.cwords_words(S), Nil{}))
           == True{} : Bool},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hs: FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl)) ->
  FH.GuessSpec(G, C, n_root, True{}, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.schedule5_lb(row, g, S, n, seen, bkts, tbl, gen2, gn, best,
      skip)):
  match skip:
    case True{}:
      +ws = SolveFast.cwords_words(S)
      +hle_lb : {Nat.is_le(Eval.Eval.cost_of(best), lb) == True{} : Bool} =
        FLB.FS.skippable_to_le(best, lb,
          Equal.sym(Bool, True{}, SolveFast.skippable(best, lb), esk))
      +hle : {Nat.is_le(Eval.Eval.cost_of(best),
                SolveFast.lower_bound(n, Groups.groups_build(g, ws, Nil{})))
              == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best), lb,
          SolveFast.lower_bound(n, Groups.groups_build(g, ws, Nil{})),
          elb, hle_lb)
      Arr.DPair{
        GWit{GCSkipLb{}, Arr.DPair{{==}, hle}},
        Arr.DPair{{==}, Arr.DPair{hs, Arr.DPair{hb,
          Arr.DPair{htbl, hgn}}}}}
    case False{}:
      FH.schedule5_lb_false_dup(G, C, gn, hgn, hook, n_root, row, g, S, n, floor, best, seen,
        bkts, tbl, gen2, hrow, hS, hus, hnd_s, hs, hb, htbl,
        Arr.Arr.dup(+List<SolveFast.CWord>, bkts), Arr.Arr.dup(U32, tbl))

def FH.schedule5_usable_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +gn: Nat, +hgn: {gn == Groups.len_words(G) : Nat},
    hook: FH.CapHookType(G, C),
    +n_root: Nat, +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, -seen: Array<Nat>,
    bkts: Array<+List<SolveFast.CWord>>, tbl: Array<U32>, +gen2: Nat,
    +m: Nat, +k: Nat, usable: Bool,
    +eus: {usable == Groups.groups_smaller(SolveFast.cwords_words(S),
                       Groups.groups_build(g, SolveFast.cwords_words(S), Nil{}))
           : Bool},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hS: {FT.FT.cwords_ok_b(G, C, n_root, S) == True{} : Bool},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hwf: {FH.fgroups_wf(
             SolveFast.fgroups_build_fast(g, SolveFast.cwords_words(S), Nil{}))
           == True{} : Bool},
    +hm: {m == FH.fgroups_total(
                 SolveFast.fgroups_build_fast(g, SolveFast.cwords_words(S),
                   Nil{})) : Nat},
    +hk: {k == FH.fgroups_count(
                 SolveFast.fgroups_build_fast(g, SolveFast.cwords_words(S),
                   Nil{})) : Nat},
    +hs: FH.SeenTree(10n, 0, seen, gen2, Nil{}),
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl)) ->
  FH.GuessSpec(G, C, n_root, True{}, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.schedule5_usable(row, g, S, n, best, seen, bkts, tbl, gen2,
      gn, m, k, usable)):
  match usable:
    case False{}:
      +ws = SolveFast.cwords_words(S)
      Arr.DPair{
        GWit{GCSkipUnusable{},
          Arr.DPair{{==},
            Equal.sym(Bool, False{},
              Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})), eus)}},
        Arr.DPair{{==}, Arr.DPair{hs, Arr.DPair{hb,
          Arr.DPair{htbl, hgn}}}}}
    case True{}:
      +ws = SolveFast.cwords_words(S)
      +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
      +lb = Nat.sub(Nat.add(n, Nat.add(m, m)), k)
      +hpos = FH.fgroups_pos_of_wf(fg, hwf)
      +elb_fg : {SolveFast.fgroups_lb_nodup(fg, n) == lb : Nat} =
        Equal.trans(Nat,
          SolveFast.fgroups_lb_nodup(fg, n),
          Nat.sub(
            Nat.add(n, Nat.add(FH.fgroups_total(fg), FH.fgroups_total(fg))),
            FH.fgroups_count(fg)),
          lb,
          FH.fgroups_lb_nodup_formula(n, fg, hpos),
          Equal.trans(Nat,
            Nat.sub(
              Nat.add(n, Nat.add(FH.fgroups_total(fg), FH.fgroups_total(fg))),
              FH.fgroups_count(fg)),
            Nat.sub(Nat.add(n, Nat.add(m, m)), FH.fgroups_count(fg)), lb,
            Equal.cong(Nat, Nat,
              x => Nat.sub(Nat.add(n, Nat.add(x, x)), FH.fgroups_count(fg)),
              FH.fgroups_total(fg), m, Equal.sym(Nat, m, FH.fgroups_total(fg), hm)),
            Equal.cong(Nat, Nat,
              y => Nat.sub(Nat.add(n, Nat.add(m, m)), y),
              FH.fgroups_count(fg), k, Equal.sym(Nat, k, FH.fgroups_count(fg), hk))))
      +elb : {lb == SolveFast.lower_bound(n, Groups.groups_build(g, ws, Nil{}))
              : Nat} =
        Equal.trans(Nat, lb, SolveFast.fgroups_lb_nodup(fg, n),
          SolveFast.lower_bound(n, Groups.groups_build(g, ws, Nil{})),
          Equal.sym(Nat, SolveFast.fgroups_lb_nodup(fg, n), lb, elb_fg),
          FH.fgroups_lb_nodup_eq_lb(g, ws, n, hnd_s))
      +hus : {Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
              == True{} : Bool} =
        Equal.sym(Bool, True{},
          Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})), eus)
      FH.schedule5_lb_spec(G, C, gn, hgn, hook, n_root, row, g, S, n, floor, best, seen, bkts,
        tbl, gen2, lb, SolveFast.skippable(best, lb), {==}, elb, hrow, hS, hus,
        hnd_s, hs, hb, htbl)

def FH.pruned_skippable_true(+g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
    +best: SolveRef.Best,
    +en: {n == Groups.len_words(S) : Nat},
    +hnd: {FN.FN.no_dup_ref(S) == True{} : Bool},
    +hpr: {Nat.is_le(
             Nat.add(1n, Nat.add(
               Nat.sub(SolveFast.best_cost(best), Nat.add(n, n)),
               FH.fgroups_count(SolveFast.fgroups_build_fast(g, S, Nil{})))),
             FH.fgroups_total(SolveFast.fgroups_build_fast(g, S, Nil{})))
           == True{} : Bool}) ->
  {SolveFast.skippable(best,
     SolveFast.fgroups_lb_nodup(SolveFast.fgroups_build_fast(g, S, Nil{}), n))
   == True{} : Bool}:
  +fg = SolveFast.fgroups_build_fast(g, S, Nil{})
  +B = SolveFast.best_cost(best)
  +b0 = Nat.sub(B, Nat.add(n, n))
  +m = FH.fgroups_total(fg)
  +k = FH.fgroups_count(fg)
  +em : {m == SolveFast.keep_fast(g, S) : Nat} =
    Equal.trans(Nat, m, Nat.add(SolveFast.keep_fast(g, S), 0n),
      SolveFast.keep_fast(g, S),
      FH.fgroups_build_total_eq_keep(g, S, Nil{}),
      NatProof.NatPrf.add_zero(SolveFast.keep_fast(g, S)))
  +hn_le : {Nat.is_le(n, Nat.add(1n, m)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_l(Nat.add(1n, m), Groups.len_words(S), n,
      Equal.sym(Nat, n, Groups.len_words(S), en),
      NatProof.Nat.is_le_eq_r(Groups.len_words(S),
        Nat.add(1n, SolveFast.keep_fast(g, S)), Nat.add(1n, m),
        Equal.cong(Nat, Nat, x => Nat.add(1n, x),
          SolveFast.keep_fast(g, S), m,
          Equal.sym(Nat, m, SolveFast.keep_fast(g, S), em)),
        FN.FN.len_le_succ_keep(g, S, hnd)))
  +hb_le : {Nat.is_le(B, Nat.add(Nat.add(n, n), b0)) == True{} : Bool} =
    FH.le_add_sub(B, Nat.add(n, n))
  +hbk1 : {Nat.is_le(Nat.add(B, k),
             Nat.add(Nat.add(Nat.add(n, n), b0), k)) == True{} : Bool} =
    FH.is_le_add_r(B, Nat.add(Nat.add(n, n), b0), k, hb_le)
  +eassoc : {Nat.add(Nat.add(Nat.add(n, n), b0), k)
             == Nat.add(n, Nat.add(n, Nat.add(b0, k))) : Nat} =
    Equal.trans(Nat,
      Nat.add(Nat.add(Nat.add(n, n), b0), k),
      Nat.add(Nat.add(n, n), Nat.add(b0, k)),
      Nat.add(n, Nat.add(n, Nat.add(b0, k))),
      NatProof.NatPrf.add_assoc(Nat.add(n, n), b0, k),
      NatProof.NatPrf.add_assoc(n, n, Nat.add(b0, k)))
  +hbk2 : {Nat.is_le(Nat.add(B, k),
             Nat.add(n, Nat.add(n, Nat.add(b0, k)))) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(Nat.add(B, k),
      Nat.add(Nat.add(Nat.add(n, n), b0), k),
      Nat.add(n, Nat.add(n, Nat.add(b0, k))), eassoc, hbk1)
  +hinner1 : {Nat.is_le(Nat.add(n, Nat.add(b0, k)),
                Nat.add(Nat.add(1n, m), Nat.add(b0, k))) == True{} : Bool} =
    FH.is_le_add_r(n, Nat.add(1n, m), Nat.add(b0, k), hn_le)
  +einner : {Nat.add(Nat.add(1n, m), Nat.add(b0, k))
             == Nat.add(m, Nat.add(1n, Nat.add(b0, k))) : Nat} =
    Equal.sym(Nat,
      Nat.add(m, Nat.add(1n, Nat.add(b0, k))),
      Nat.add(1n, Nat.add(m, Nat.add(b0, k))),
      NatProof.NatPrf.add_succ(m, Nat.add(b0, k)))
  +hinner2 : {Nat.is_le(Nat.add(n, Nat.add(b0, k)), Nat.add(m, m))
              == True{} : Bool} =
    NatProof.Nat.is_le_trans(
      Nat.add(n, Nat.add(b0, k)),
      Nat.add(m, Nat.add(1n, Nat.add(b0, k))), Nat.add(m, m),
      NatProof.Nat.is_le_eq_r(Nat.add(n, Nat.add(b0, k)),
        Nat.add(Nat.add(1n, m), Nat.add(b0, k)),
        Nat.add(m, Nat.add(1n, Nat.add(b0, k))), einner, hinner1),
      NatProof.Nat.is_le_add_l(Nat.add(1n, Nat.add(b0, k)), m, m, hpr))
  +hbk3 : {Nat.is_le(Nat.add(B, k), Nat.add(n, Nat.add(m, m)))
           == True{} : Bool} =
    NatProof.Nat.is_le_trans(
      Nat.add(B, k), Nat.add(n, Nat.add(n, Nat.add(b0, k))),
      Nat.add(n, Nat.add(m, m)), hbk2,
      NatProof.Nat.is_le_add_l(Nat.add(n, Nat.add(b0, k)), Nat.add(m, m), n,
        hinner2))
  +hsub : {Nat.is_le(B, Nat.sub(Nat.add(n, Nat.add(m, m)), k))
           == True{} : Bool} =
    FH.le_sub_of_add_le(k, Nat.add(n, Nat.add(m, m)), B, hbk3)
  +elb : {SolveFast.fgroups_lb_nodup(fg, n)
          == Nat.sub(Nat.add(n, Nat.add(m, m)), k) : Nat} =
    FH.fgroups_lb_nodup_formula(n, fg, FH.fgroups_build_pos(g, S, Nil{}, {==}))
  NatProof.Nat.is_le_eq_r(B,
    Nat.sub(Nat.add(n, Nat.add(m, m)), k),
    SolveFast.fgroups_lb_nodup(fg, n),
    Equal.sym(Nat, SolveFast.fgroups_lb_nodup(fg, n),
      Nat.sub(Nat.add(n, Nat.add(m, m)), k), elb), hsub)

def FH.pruned_skippable_stage2(+g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
    +best: SolveRef.Best,
    +en: {n == Groups.len_words(S) : Nat},
    +hnm: {Tree.member_word(g, S) == False{} : Bool},
    +hpr: {Nat.is_le(
             Nat.add(1n, Nat.add(
               Nat.sub(Nat.sub(SolveFast.best_cost(best), Nat.add(n, n)), 1n),
               FH.fgroups_count(SolveFast.fgroups_build_fast(g, S, Nil{})))),
             FH.fgroups_total(SolveFast.fgroups_build_fast(g, S, Nil{})))
           == True{} : Bool}) ->
  {SolveFast.skippable(best,
     SolveFast.fgroups_lb_nodup(SolveFast.fgroups_build_fast(g, S, Nil{}), n))
   == True{} : Bool}:
  +fg = SolveFast.fgroups_build_fast(g, S, Nil{})
  +B = SolveFast.best_cost(best)
  +b1 = Nat.sub(B, Nat.add(n, n))
  +b0 = Nat.sub(b1, 1n)
  +m = FH.fgroups_total(fg)
  +k = FH.fgroups_count(fg)
  +em : {m == n : Nat} =
    Equal.trans(Nat, m, SolveFast.keep_fast(g, S), n,
      Equal.trans(Nat, m, Nat.add(SolveFast.keep_fast(g, S), 0n),
        SolveFast.keep_fast(g, S),
        FH.fgroups_build_total_eq_keep(g, S, Nil{}),
        NatProof.NatPrf.add_zero(SolveFast.keep_fast(g, S))),
      Equal.trans(Nat, SolveFast.keep_fast(g, S), Groups.len_words(S), n,
        FN.FN.keep_of_not_member(g, S, hnm),
        Equal.sym(Nat, n, Groups.len_words(S), en)))
  +hb_le1 : {Nat.is_le(B, Nat.add(Nat.add(n, n), b1)) == True{} : Bool} =
    FH.le_add_sub(B, Nat.add(n, n))
  +hb1_le : {Nat.is_le(b1, Nat.add(1n, b0)) == True{} : Bool} =
    FH.le_add_sub(b1, 1n)
  +hb_le : {Nat.is_le(B, Nat.add(Nat.add(n, n), Nat.add(1n, b0)))
            == True{} : Bool} =
    NatProof.Nat.is_le_trans(B, Nat.add(Nat.add(n, n), b1),
      Nat.add(Nat.add(n, n), Nat.add(1n, b0)), hb_le1,
      NatProof.Nat.is_le_add_l(b1, Nat.add(1n, b0), Nat.add(n, n), hb1_le))
  +hbk1 : {Nat.is_le(Nat.add(B, k),
             Nat.add(Nat.add(Nat.add(n, n), Nat.add(1n, b0)), k))
           == True{} : Bool} =
    FH.is_le_add_r(B, Nat.add(Nat.add(n, n), Nat.add(1n, b0)), k, hb_le)
  +eassoc : {Nat.add(Nat.add(Nat.add(n, n), Nat.add(1n, b0)), k)
             == Nat.add(Nat.add(n, n), Nat.add(1n, Nat.add(b0, k))) : Nat} =
    NatProof.NatPrf.add_assoc(Nat.add(n, n), Nat.add(1n, b0), k)
  +hbk2 : {Nat.is_le(Nat.add(B, k),
             Nat.add(Nat.add(n, n), Nat.add(1n, Nat.add(b0, k))))
           == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(Nat.add(B, k),
      Nat.add(Nat.add(Nat.add(n, n), Nat.add(1n, b0)), k),
      Nat.add(Nat.add(n, n), Nat.add(1n, Nat.add(b0, k))), eassoc, hbk1)
  +hbk3 : {Nat.is_le(Nat.add(B, k), Nat.add(Nat.add(n, n), m))
           == True{} : Bool} =
    NatProof.Nat.is_le_trans(Nat.add(B, k),
      Nat.add(Nat.add(n, n), Nat.add(1n, Nat.add(b0, k))),
      Nat.add(Nat.add(n, n), m), hbk2,
      NatProof.Nat.is_le_add_l(Nat.add(1n, Nat.add(b0, k)), m, Nat.add(n, n),
        hpr))
  +e_nnm : {Nat.add(Nat.add(n, n), m) == Nat.add(n, Nat.add(m, m)) : Nat} =
    Equal.trans(Nat,
      Nat.add(Nat.add(n, n), m),
      Nat.add(n, Nat.add(n, m)),
      Nat.add(n, Nat.add(m, m)),
      NatProof.NatPrf.add_assoc(n, n, m),
      Equal.cong(Nat, Nat, x => Nat.add(n, Nat.add(x, m)), n, m,
        Equal.sym(Nat, m, n, em)))
  +hbk4 : {Nat.is_le(Nat.add(B, k), Nat.add(n, Nat.add(m, m)))
           == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(Nat.add(B, k), Nat.add(Nat.add(n, n), m),
      Nat.add(n, Nat.add(m, m)), e_nnm, hbk3)
  +hsub : {Nat.is_le(B, Nat.sub(Nat.add(n, Nat.add(m, m)), k))
           == True{} : Bool} =
    FH.le_sub_of_add_le(k, Nat.add(n, Nat.add(m, m)), B, hbk4)
  +elb : {SolveFast.fgroups_lb_nodup(fg, n)
          == Nat.sub(Nat.add(n, Nat.add(m, m)), k) : Nat} =
    FH.fgroups_lb_nodup_formula(n, fg, FH.fgroups_build_pos(g, S, Nil{}, {==}))
  NatProof.Nat.is_le_eq_r(B,
    Nat.sub(Nat.add(n, Nat.add(m, m)), k),
    SolveFast.fgroups_lb_nodup(fg, n),
    Equal.sym(Nat, SolveFast.fgroups_lb_nodup(fg, n),
      Nat.sub(Nat.add(n, Nat.add(m, m)), k), elb), hsub)

def FH.schedule5_pruned_wit(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +g: +List<Nat>, +ws: +List<+List<Nat>>, +n: Nat, +floor: Nat,
    +best: SolveRef.Best, skip_self: Bool,
    +esk: {skip_self == Nat.is_eq(floor, Nat.add(n, n)) : Bool},
    +en: {n == Groups.len_words(ws) : Nat},
    +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool},
    mem: Bool, +emem: {mem == Tree.member_word(g, ws) : Bool},
    +hpr: {FH.pruned_reason(g, ws, Nil{},
             SolveFast.budget_for(n, best, skip_self), skip_self)
           == True{} : Bool}) ->
  FH.GuessWit<G, C, n_root, True{}, True{}, g, ws, n, floor, best, Nil{}>:
  match skip_self:
    case False{}:
      +hsk = FH.pruned_skippable_true(g, ws, n, best, en, hnd, hpr)
      +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
      +hle_fg = FLB.FS.skippable_to_le(best, SolveFast.fgroups_lb_nodup(fg, n),
                  hsk)
      +hle = NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best),
               SolveFast.fgroups_lb_nodup(fg, n),
               SolveFast.lower_bound(n, Groups.groups_build(g, ws, Nil{})),
               FH.fgroups_lb_nodup_eq_lb(g, ws, n, hnd), hle_fg)
      GWit{GCSkipLb{}, Arr.DPair{{==}, hle}}
    case True{}:
      match mem:
        case True{}:
          +efl : {floor == Nat.add(n, n) : Nat} =
            NatProof.NatPrf.is_eq_true(floor, Nat.add(n, n),
              Equal.sym(Bool, True{}, Nat.is_eq(floor, Nat.add(n, n)), esk))
          +hmem : {Tree.member_word(g, ws) == True{} : Bool} =
            Equal.sym(Bool, True{}, Tree.member_word(g, ws), emem)
          GWit{GCSkipSelf{},
            Arr.DPair{{==}, Arr.DPair{{==}, Arr.DPair{efl, hmem}}}}
        case False{}:
          +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
          +b0 = SolveFast.budget_for(n, best, True{})
          +hnm : {Tree.member_word(g, ws) == False{} : Bool} =
            Equal.sym(Bool, False{}, Tree.member_word(g, ws), emem)
          +hpr2 : {Nat.is_le(
                     Nat.add(1n, Nat.add(b0, FH.fgroups_count(fg))),
                     FH.fgroups_total(fg)) == True{} : Bool} =
            Equal.trans(Bool,
              Nat.is_le(Nat.add(1n, Nat.add(b0, FH.fgroups_count(fg))),
                FH.fgroups_total(fg)),
              Bool.or(Tree.member_word(g, ws),
                Nat.is_le(Nat.add(1n, Nat.add(b0, FH.fgroups_count(fg))),
                  FH.fgroups_total(fg))), True{},
              Equal.cong(Bool, Bool,
                x => Bool.or(x,
                       Nat.is_le(Nat.add(1n, Nat.add(b0, FH.fgroups_count(fg))),
                         FH.fgroups_total(fg))),
                False{}, Tree.member_word(g, ws), emem), hpr)
          +hsk = FH.pruned_skippable_stage2(g, ws, n, best, en, hnm, hpr2)
          +hle_fg = FLB.FS.skippable_to_le(best,
                      SolveFast.fgroups_lb_nodup(fg, n), hsk)
          +hle = NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best),
                   SolveFast.fgroups_lb_nodup(fg, n),
                   SolveFast.lower_bound(n, Groups.groups_build(g, ws, Nil{})),
                   FH.fgroups_lb_nodup_eq_lb(g, ws, n, hnd), hle_fg)
          GWit{GCSkipLb{}, Arr.DPair{{==}, hle}}

def FH.schedule5_hist_ok_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +gn: Nat, +hgn: {gn == Groups.len_words(G) : Nat},
    hook: FH.CapHookType(G, C),
    +n_root: Nat, +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, +skip_self: Bool,
    -seen2: Array<Nat>, bkts: Array<+List<SolveFast.CWord>>,
    -tbl0: Array<U32>, tbl2: Array<U32>, +gen: Nat, +m: Nat, +k: Nat, +b: Nat,
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hS: {FT.FT.cwords_ok_b(G, C, n_root, S) == True{} : Bool},
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    +hhr: FH.HistSpec(g, SolveFast.cwords_words(S), Nil{}, gen,
            SolveFast.budget_for(n, best, skip_self), skip_self, tbl0,
            SolveFast.Hist5Ok{seen2, tbl2, m, k, b}),
    dp: &s1: Array<Nat> -> &s2: Array<Nat> ->
        {s1 == seen2 : Array<Nat>} & {s2 == s1 : Array<Nat>}) ->
  FH.GuessSpec(G, C, n_root, True{}, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.schedule5_usable(row, g, S, n, best, seen2, bkts, tbl2,
      Nat.add(1n, gen), gn, m, k,
      Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)))):
  (s1, dp2) = dp
  (s2, pe) = dp2
  (+es1, +es2) = pe
  +ws = SolveFast.cwords_words(S)
  +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
  +budget0 = SolveFast.budget_for(n, best, skip_self)
  +hs2 = Arr.Arr.dpair_l(
           FH.SeenTree(10n, 0, seen2, gen, fg),
           Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
             Arr.Arr.DPair<{FH.fgroups_wf(fg) == True{} : Bool},
               Arr.Arr.DPair<{m == FH.fgroups_total(fg) : Nat},
                 Arr.Arr.DPair<{k == FH.fgroups_count(fg) : Nat},
                   Arr.Arr.DPair<
                     {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                     {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                      == True{} : Bool}>>>>>, hhr)
  +r1 = Arr.Arr.dpair_r(
          FH.SeenTree(10n, 0, seen2, gen, fg),
          Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
            Arr.Arr.DPair<{FH.fgroups_wf(fg) == True{} : Bool},
              Arr.Arr.DPair<{m == FH.fgroups_total(fg) : Nat},
                Arr.Arr.DPair<{k == FH.fgroups_count(fg) : Nat},
                  Arr.Arr.DPair<
                    {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                    {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                     == True{} : Bool}>>>>>, hhr)
  +et20 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
            Arr.Arr.DPair<{FH.fgroups_wf(fg) == True{} : Bool},
              Arr.Arr.DPair<{m == FH.fgroups_total(fg) : Nat},
                Arr.Arr.DPair<{k == FH.fgroups_count(fg) : Nat},
                  Arr.Arr.DPair<
                    {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                    {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                     == True{} : Bool}>>>>, r1)
  +r2 = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
          Arr.Arr.DPair<{FH.fgroups_wf(fg) == True{} : Bool},
            Arr.Arr.DPair<{m == FH.fgroups_total(fg) : Nat},
              Arr.Arr.DPair<{k == FH.fgroups_count(fg) : Nat},
                Arr.Arr.DPair<
                  {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                  {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                   == True{} : Bool}>>>>, r1)
  +hwf = Arr.Arr.dpair_l({FH.fgroups_wf(fg) == True{} : Bool},
           Arr.Arr.DPair<{m == FH.fgroups_total(fg) : Nat},
             Arr.Arr.DPair<{k == FH.fgroups_count(fg) : Nat},
               Arr.Arr.DPair<
                 {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                 {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                  == True{} : Bool}>>>, r2)
  +r3 = Arr.Arr.dpair_r({FH.fgroups_wf(fg) == True{} : Bool},
          Arr.Arr.DPair<{m == FH.fgroups_total(fg) : Nat},
            Arr.Arr.DPair<{k == FH.fgroups_count(fg) : Nat},
              Arr.Arr.DPair<
                {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
                {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
                 == True{} : Bool}>>>, r2)
  +hm = Arr.Arr.dpair_l({m == FH.fgroups_total(fg) : Nat},
          Arr.Arr.DPair<{k == FH.fgroups_count(fg) : Nat},
            Arr.Arr.DPair<
              {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
              {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
               == True{} : Bool}>>, r3)
  +r4 = Arr.Arr.dpair_r({m == FH.fgroups_total(fg) : Nat},
          Arr.Arr.DPair<{k == FH.fgroups_count(fg) : Nat},
            Arr.Arr.DPair<
              {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
              {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
               == True{} : Bool}>>, r3)
  +hk = Arr.Arr.dpair_l({k == FH.fgroups_count(fg) : Nat},
          Arr.Arr.DPair<
            {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
            {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
             == True{} : Bool}>, r4)
  +r5 = Arr.Arr.dpair_r({k == FH.fgroups_count(fg) : Nat},
          Arr.Arr.DPair<
            {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
            {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n))
             == True{} : Bool}>, r4)
  +hle0 = Arr.Arr.dpair_r(
            {Nat.add(b, m) == Nat.add(budget0, k) : Nat},
            {Nat.is_le(m, Nat.add(Groups.len_words(ws), 0n)) == True{} : Bool},
            r5)
  +es2_seen : {s2 == seen2 : Array<Nat>} =
    Equal.trans(Array<Nat>, s2, s1, seen2, es2, es1)
  +hs_s2 = FH.seen_tree_transport(10n, 0, seen2, s2, gen, fg,
             Equal.sym(Array<Nat>, s2, seen2, es2_seen), hs2)
  +hbump = FH.seen_tree_transport(10n, 0, s2, seen2, Nat.add(1n, gen), Nil{},
             es2_seen, FH.seen_tree_bump(10n, 0, s2, gen, fg, hs_s2))
  +htbl2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl0, tbl2,
             Equal.sym(Array<U32>, tbl2, tbl0, et20), htbl0)
  +hle_n : {Nat.is_le(FH.fgroups_total(fg), n) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(FH.fgroups_total(fg),
      Nat.add(Groups.len_words(ws), 0n), n,
      Equal.trans(Nat, Nat.add(Groups.len_words(ws), 0n), Groups.len_words(ws),
        n, NatProof.NatPrf.add_zero(Groups.len_words(ws)),
        Equal.sym(Nat, n, Groups.len_words(ws), en)),
      NatProof.Nat.is_le_eq_l(Nat.add(Groups.len_words(ws), 0n), m,
        FH.fgroups_total(fg), hm, hle0))
  +eus_fg : {SolveFast.fgroups_smaller(n, fg)
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
  +eus_g : {SolveFast.fgroups_smaller(n, fg)
            == Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
            : Bool} =
    Equal.trans(Bool,
      SolveFast.fgroups_smaller(n, fg),
      SolveFast.fgroups_smaller(Groups.len_words(ws), fg),
      Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})),
      Equal.cong(Nat, Bool, x => SolveFast.fgroups_smaller(x, fg),
        n, Groups.len_words(ws), en),
      Equal.trans(Bool,
        SolveFast.fgroups_smaller(Groups.len_words(ws), fg),
        Groups.groups_smaller(ws, FN.FN.fgroups_to_groups(fg)),
        Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})),
        FN.FN.fgroups_smaller_eq(ws, fg,
          FN.FN.fgroups_build_lens_ok(g, ws, Nil{}, {==})),
        Equal.cong(+List<Groups.Group>, Bool, gs => Groups.groups_smaller(ws, gs),
          FN.FN.fgroups_to_groups(fg), Groups.groups_build(g, ws, Nil{}),
          FN.FN.fgroups_build_eq(g, ws, Nil{}))))
  +eus : {Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k))
          == Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
          : Bool} =
    Equal.trans(Bool,
      Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)),
      SolveFast.fgroups_smaller(n, fg),
      Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})),
      Equal.sym(Bool, SolveFast.fgroups_smaller(n, fg),
        Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)), eus_fg), eus_g)
  FH.schedule5_usable_spec(G, C, gn, hgn, hook, n_root, row, g, S, n, floor, best, seen2,
    bkts, tbl2, Nat.add(1n, gen), m, k,
    Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)), eus, hrow, hS, hnd_s, hwf,
    hm, hk, hbump, hb, htbl2)

def FH.schedule5_hist_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +gn: Nat, +hgn: {gn == Groups.len_words(G) : Nat},
    hook: FH.CapHookType(G, C),
    +n_root: Nat, +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, +skip_self: Bool,
    bkts: Array<+List<SolveFast.CWord>>, -tbl0: Array<U32>, +gen: Nat,
    hr: SolveFast.Hist5Res,
    +esk: {skip_self == Nat.is_eq(floor, Nat.add(n, n)) : Bool},
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hS: {FT.FT.cwords_ok_b(G, C, n_root, S) == True{} : Bool},
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
    +htbl0: FT.FT.TblOk(G, C, n_root, tbl0),
    +hhr: FH.HistSpec(g, SolveFast.cwords_words(S), Nil{}, gen,
            SolveFast.budget_for(n, best, skip_self), skip_self, tbl0, hr)) ->
  FH.GuessSpec(G, C, n_root, True{}, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.schedule5_hist(row, g, S, n, best, bkts, gen, gn, hr)):
  match hr:
    case SolveFast.Hist5Pruned{seen2, tbl2}:
      +ws = SolveFast.cwords_words(S)
      +budget0 = SolveFast.budget_for(n, best, skip_self)
      +hs2 = Arr.Arr.dpair_l(
               FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{}),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 {FH.pruned_reason(g, ws, Nil{}, budget0, skip_self)
                  == True{} : Bool}>, hhr)
      +hr1 = Arr.Arr.dpair_r(
               FH.SeenTree(10n, 0, seen2, Nat.add(1n, gen), Nil{}),
               Arr.Arr.DPair<{tbl2 == tbl0 : Array<U32>},
                 {FH.pruned_reason(g, ws, Nil{}, budget0, skip_self)
                  == True{} : Bool}>, hhr)
      +et2 = Arr.Arr.dpair_l({tbl2 == tbl0 : Array<U32>},
               {FH.pruned_reason(g, ws, Nil{}, budget0, skip_self)
                == True{} : Bool}, hr1)
      +hpr = Arr.Arr.dpair_r({tbl2 == tbl0 : Array<U32>},
               {FH.pruned_reason(g, ws, Nil{}, budget0, skip_self)
                == True{} : Bool}, hr1)
      +htbl2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl0, tbl2,
                 Equal.sym(Array<U32>, tbl2, tbl0, et2), htbl0)
      Arr.DPair{
        FH.schedule5_pruned_wit(G, C, n_root, g, ws, n, floor, best, skip_self,
          esk, en, hnd_s, Tree.member_word(g, ws), {==}, hpr),
        Arr.DPair{{==}, Arr.DPair{hs2, Arr.DPair{hb,
          Arr.DPair{htbl2, hgn}}}}}
    case SolveFast.Hist5Ok{seen2, tbl2, +m, +k, +b}:
      FH.schedule5_hist_ok_dup(G, C, gn, hgn, hook, n_root, row, g, S, n, floor, best,
        skip_self, seen2, bkts, tbl0, tbl2, gen, m, k, b, hge1, en, hnd_s,
        hrow, hS, hb, htbl0, hhr, Arr.Arr.dup(Nat, seen2))

def FH.guess_body_buf5_dup(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +gn: Nat, +hgn: {gn == Groups.len_words(G) : Nat},
    hook: FH.CapHookType(G, C),
    +n_root: Nat, +row: U32, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, +skip_self: Bool,
    -seen: Array<Nat>, bkts: Array<+List<SolveFast.CWord>>, -tbl: Array<U32>,
    +gen: Nat,
    +esk: {skip_self == Nat.is_eq(floor, Nat.add(n, n)) : Bool},
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hrow: {FT.FT.gentry_ok_b(G, n_root, row, g) == True{} : Bool},
    +hS: {FT.FT.cwords_ok_b(G, C, n_root, S) == True{} : Bool},
    +hs: FH.SeenTree(10n, 0, seen, gen, Nil{}),
    +hb: FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
    +htbl: FT.FT.TblOk(G, C, n_root, tbl),
    dps: &s1: Array<Nat> -> &s2: Array<Nat> ->
         {s1 == seen : Array<Nat>} & {s2 == s1 : Array<Nat>},
    dpt: &t1: Array<U32> -> &t2: Array<U32> ->
         {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>}) ->
  FH.GuessSpec(G, C, n_root, True{}, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.schedule5_hist(row, g, S, n, best, bkts, gen, gn,
      SolveFast.hist5_go(row, S, gen, skip_self,
        SolveFast.Hist5Ok{seen, tbl, 0n, 0n,
          SolveFast.budget_for(n, best, skip_self)}))):
  (s1, dps2) = dps
  (s2, pes) = dps2
  (+es1, +es2) = pes
  (t1, dpt2) = dpt
  (t2, pet) = dpt2
  (+et1, +et2) = pet
  +ws = SolveFast.cwords_words(S)
  +budget0 = SolveFast.budget_for(n, best, skip_self)
  +es2_s : {s2 == seen : Array<Nat>} = Equal.trans(Array<Nat>, s2, s1, seen, es2, es1)
  +et2_t : {t2 == tbl : Array<U32>} = Equal.trans(Array<U32>, t2, t1, tbl, et2, et1)
  +hs2 = FH.seen_tree_transport(10n, 0, seen, s2, gen, Nil{},
           Equal.sym(Array<Nat>, s2, seen, es2_s), hs)
  +ht2 = FT.FT.tbl_ok_transport(G, C, n_root, tbl, t2,
           Equal.sym(Array<U32>, t2, tbl, et2_t), htbl)
  +hhr2 = FH.hist5_go_spec(S, G, C, n_root, row, g, Nil{}, s2, t2, gen, 0n, 0n,
            budget0, budget0, skip_self, ht2, hrow, hS, {==}, {==}, {==}, {==},
            hs2)
  +hhr_t0 = FH.hist_spec_transport_tbl(g, ws, Nil{}, gen, budget0, skip_self,
              t2, tbl,
              SolveFast.hist5_go(row, S, gen, skip_self,
                SolveFast.Hist5Ok{s2, t2, 0n, 0n, budget0}), et2_t, hhr2)
  +eq_12 : {SolveFast.hist5_go(row, S, gen, skip_self,
              SolveFast.Hist5Ok{s2, t2, 0n, 0n, budget0})
            == SolveFast.hist5_go(row, S, gen, skip_self,
                 SolveFast.Hist5Ok{s1, t1, 0n, 0n, budget0})
            : SolveFast.Hist5Res} =
    Equal.trans(SolveFast.Hist5Res,
      SolveFast.hist5_go(row, S, gen, skip_self,
        SolveFast.Hist5Ok{s2, t2, 0n, 0n, budget0}),
      SolveFast.hist5_go(row, S, gen, skip_self,
        SolveFast.Hist5Ok{s1, t2, 0n, 0n, budget0}),
      SolveFast.hist5_go(row, S, gen, skip_self,
        SolveFast.Hist5Ok{s1, t1, 0n, 0n, budget0}),
      Equal.cong(Array<Nat>, SolveFast.Hist5Res,
        x => SolveFast.hist5_go(row, S, gen, skip_self,
               SolveFast.Hist5Ok{x, t2, 0n, 0n, budget0}), s2, s1, es2),
      Equal.cong(Array<U32>, SolveFast.Hist5Res,
        y => SolveFast.hist5_go(row, S, gen, skip_self,
               SolveFast.Hist5Ok{s1, y, 0n, 0n, budget0}), t2, t1, et2))
  +hhr1 = FH.hist_spec_transport(g, ws, Nil{}, gen, budget0, skip_self, tbl,
            SolveFast.hist5_go(row, S, gen, skip_self,
              SolveFast.Hist5Ok{s2, t2, 0n, 0n, budget0}),
            SolveFast.hist5_go(row, S, gen, skip_self,
              SolveFast.Hist5Ok{s1, t1, 0n, 0n, budget0}), eq_12, hhr_t0)
  %es1 : FH.GuessSpec(G, C, n_root, True{}, True{}, g, ws, n, floor, best,
           SolveFast.schedule5_hist(row, g, S, n, best, bkts, gen, gn,
             SolveFast.hist5_go(row, S, gen, skip_self,
               SolveFast.Hist5Ok{_, tbl, 0n, 0n, budget0})))
  %et1 : FH.GuessSpec(G, C, n_root, True{}, True{}, g, ws, n, floor, best,
           SolveFast.schedule5_hist(row, g, S, n, best, bkts, gen, gn,
             SolveFast.hist5_go(row, S, gen, skip_self,
               SolveFast.Hist5Ok{s1, _, 0n, 0n, budget0})))
  FH.schedule5_hist_spec(G, C, gn, hgn, hook, n_root, row, g, S, n, floor, best, skip_self,
    bkts, tbl, gen,
    SolveFast.hist5_go(row, S, gen, skip_self,
      SolveFast.Hist5Ok{s1, t1, 0n, 0n, budget0}),
    esk, hge1, en, hnd_s, hrow, hS, hb, htbl, hhr1)

# Helper for the non-`Buf5` (`schedule_fguess`) path.
def FH.schedule_fguess_lb_wit(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +nodup: Bool, +g: +List<Nat>, +ws: +List<+List<Nat>>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, skip: Bool,
    +esk: {skip == SolveFast.skippable(best,
                     SolveFast.fgroups_lb(nodup, n,
                       SolveFast.fgroups_build_fast(g, ws, Nil{}))) : Bool},
    +hus: {Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
           == True{} : Bool},
    +hnd: {FN.FN.nodup_ok(nodup, ws) == True{} : Bool}) ->
  FH.GuessWit<G, C, n_root, False{}, nodup, g, ws, n, floor, best,
    SolveFast.schedule_fguess_lb(nodup, g,
      SolveFast.fgroups_build_fast(g, ws, Nil{}), n, skip)>:
  match skip:
    case True{}:
      +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
      +egrp : {FN.FN.fgroups_to_groups(fg) == Groups.groups_build(g, ws, Nil{})
               : +List<Groups.Group>} =
        FN.FN.fgroups_build_eq(g, ws, Nil{})
      +hlok : {FN.FN.fgroups_lens_ok(fg) == True{} : Bool} =
        FN.FN.fgroups_build_lens_ok(g, ws, Nil{}, {==})
      +hng_g : {FN.FN.nodup_ok_jobs(nodup,
                  MV.MV.next_groups(Groups.groups_build(g, ws, Nil{})))
                == True{} : Bool} =
        FN.FN.nodup_ok_next_groups(nodup, Groups.groups_build(g, ws, Nil{}), ws,
          CoverGroups.Cover.all_subseq_nil(g, ws), hnd)
      +hng : {FN.FN.nodup_ok_jobs(nodup,
                MV.MV.next_groups(FN.FN.fgroups_to_groups(fg))) == True{} : Bool} =
        Equal.trans(Bool,
          FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(FN.FN.fgroups_to_groups(fg))),
          FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(Groups.groups_build(g, ws, Nil{}))),
          True{},
          Equal.cong(+List<Groups.Group>, Bool,
            gs => FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(gs)),
            FN.FN.fgroups_to_groups(fg), Groups.groups_build(g, ws, Nil{}), egrp),
          hng_g)
      +elb : {SolveFast.fgroups_lb(nodup, n, fg)
              == SolveFast.lower_bound(n, Groups.groups_build(g, ws, Nil{}))
              : Nat} =
        Equal.trans(Nat,
          SolveFast.fgroups_lb(nodup, n, fg),
          SolveFast.lower_bound(n, FN.FN.fgroups_to_groups(fg)),
          SolveFast.lower_bound(n, Groups.groups_build(g, ws, Nil{})),
          FN.FN.fgroups_lb_eq(nodup, n, fg, hlok, hng),
          Equal.cong(+List<Groups.Group>, Nat, gs => SolveFast.lower_bound(n, gs),
            FN.FN.fgroups_to_groups(fg), Groups.groups_build(g, ws, Nil{}), egrp))
      +hle = NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best),
               SolveFast.fgroups_lb(nodup, n, fg),
               SolveFast.lower_bound(n, Groups.groups_build(g, ws, Nil{})), elb,
               FLB.FS.skippable_to_le(best, SolveFast.fgroups_lb(nodup, n, fg),
                 Equal.sym(Bool, True{},
                   SolveFast.skippable(best, SolveFast.fgroups_lb(nodup, n, fg)),
                   esk)))
      GWit{GCSkipLb{}, Arr.DPair{{==}, hle}}
    case False{}:
      +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
      +egrp : {FN.FN.fgroups_to_groups(fg) == Groups.groups_build(g, ws, Nil{})
               : +List<Groups.Group>} =
        FN.FN.fgroups_build_eq(g, ws, Nil{})
      +hlok : {FN.FN.fgroups_lens_ok(fg) == True{} : Bool} =
        FN.FN.fgroups_build_lens_ok(g, ws, Nil{}, {==})
      +hng_g : {FN.FN.nodup_ok_jobs(nodup,
                  MV.MV.next_groups(Groups.groups_build(g, ws, Nil{})))
                == True{} : Bool} =
        FN.FN.nodup_ok_next_groups(nodup, Groups.groups_build(g, ws, Nil{}), ws,
          CoverGroups.Cover.all_subseq_nil(g, ws), hnd)
      +hng : {FN.FN.nodup_ok_jobs(nodup,
                MV.MV.next_groups(FN.FN.fgroups_to_groups(fg))) == True{} : Bool} =
        Equal.trans(Bool,
          FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(FN.FN.fgroups_to_groups(fg))),
          FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(Groups.groups_build(g, ws, Nil{}))),
          True{},
          Equal.cong(+List<Groups.Group>, Bool,
            gs => FN.FN.nodup_ok_jobs(nodup, MV.MV.next_groups(gs)),
            FN.FN.fgroups_to_groups(fg), Groups.groups_build(g, ws, Nil{}), egrp),
          hng_g)
      +groups = Groups.groups_build(g, ws, Nil{})
      +body : +List<SolveFast.Item> =
        List.append(&2, SolveFast.Item, SolveFast.group_items(nodup, n, groups),
          SolveFast.End{} <> Nil{})
      +eib : {SolveFast.fgroup_items_build(nodup, n, fg, SolveFast.End{} <> Nil{})
              == SolveFast.ItemsBound{SolveFast.lower_bound(n, groups), body}
              : SolveFast.ItemsBound} =
        Equal.trans(SolveFast.ItemsBound,
          SolveFast.fgroup_items_build(nodup, n, fg, SolveFast.End{} <> Nil{}),
          SolveFast.ItemsBound{
            SolveFast.lower_bound(n, FN.FN.fgroups_to_groups(fg)),
            List.append(&2, SolveFast.Item,
              SolveFast.group_items(nodup, n, FN.FN.fgroups_to_groups(fg)),
              SolveFast.End{} <> Nil{})},
          SolveFast.ItemsBound{SolveFast.lower_bound(n, groups), body},
          FN.FN.fgroup_items_build_eq(nodup, n, fg, SolveFast.End{} <> Nil{},
            hlok, hng),
          Equal.cong(+List<Groups.Group>, SolveFast.ItemsBound,
            gs => SolveFast.ItemsBound{SolveFast.lower_bound(n, gs),
                    List.append(&2, SolveFast.Item,
                      SolveFast.group_items(nodup, n, gs),
                      SolveFast.End{} <> Nil{})},
            FN.FN.fgroups_to_groups(fg), groups, egrp))
      +eits : {SolveFast.schedule_guess_ib(g,
                 SolveFast.fgroup_items_build(nodup, n, fg,
                   SolveFast.End{} <> Nil{}))
               == SolveFast.Begin{g} <> body : +List<SolveFast.Item>} =
        Equal.cong(SolveFast.ItemsBound, +List<SolveFast.Item>,
          ib => SolveFast.schedule_guess_ib(g, ib),
          SolveFast.fgroup_items_build(nodup, n, fg, SolveFast.End{} <> Nil{}),
          SolveFast.ItemsBound{SolveFast.lower_bound(n, groups), body}, eib)
      GWit{GCLive{groups, body, FP.PRefl{}},
        Arr.DPair{eits, Arr.DPair{hus, Arr.DPair{{==},
          FH.group_items_body_match(G, C, n_root, nodup, n, groups, hng_g)}}}}

def FH.schedule_fguess_wit(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +nodup: Bool, +g: +List<Nat>, +ws: +List<+List<Nat>>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, usable: Bool,
    +eus: {usable == Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
           : Bool},
    +hnd: {FN.FN.nodup_ok(nodup, ws) == True{} : Bool}) ->
  FH.GuessWit<G, C, n_root, False{}, nodup, g, ws, n, floor, best,
    SolveFast.schedule_fguess(nodup, g,
      SolveFast.fgroups_build_fast(g, ws, Nil{}), n, best, usable)>:
  match usable:
    case False{}:
      GWit{GCSkipUnusable{},
        Arr.DPair{{==},
          Equal.sym(Bool, False{},
            Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})), eus)}}
    case True{}:
      +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
      FH.schedule_fguess_lb_wit(G, C, n_root, nodup, g, ws, n, floor, best,
        SolveFast.skippable(best, SolveFast.fgroups_lb(nodup, n, fg)), {==},
        Equal.sym(Bool, True{},
          Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})), eus),
        hnd)

def FH.schedule_fguess_fast_wit(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +nodup: Bool, +g: +List<Nat>, +ws: +List<+List<Nat>>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best,
    +en: {n == Groups.len_words(ws) : Nat},
    +hnd: {FN.FN.nodup_ok(nodup, ws) == True{} : Bool}) ->
  FH.GuessWit<G, C, n_root, False{}, nodup, g, ws, n, floor, best,
    SolveFast.schedule_fguess(nodup, g,
      SolveFast.fgroups_build_fast(g, ws, Nil{}), n, best,
      SolveFast.fgroups_smaller(n, SolveFast.fgroups_build_fast(g, ws, Nil{})))>:
  +fg = SolveFast.fgroups_build_fast(g, ws, Nil{})
  +eus : {SolveFast.fgroups_smaller(n, fg)
          == Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})) : Bool} =
    Equal.trans(Bool,
      SolveFast.fgroups_smaller(n, fg),
      SolveFast.fgroups_smaller(Groups.len_words(ws), fg),
      Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})),
      Equal.cong(Nat, Bool, x => SolveFast.fgroups_smaller(x, fg),
        n, Groups.len_words(ws), en),
      Equal.trans(Bool,
        SolveFast.fgroups_smaller(Groups.len_words(ws), fg),
        Groups.groups_smaller(ws, FN.FN.fgroups_to_groups(fg)),
        Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})),
        FN.FN.fgroups_smaller_eq(ws, fg,
          FN.FN.fgroups_build_lens_ok(g, ws, Nil{}, {==})),
        Equal.cong(+List<Groups.Group>, Bool, gs => Groups.groups_smaller(ws, gs),
          FN.FN.fgroups_to_groups(fg), Groups.groups_build(g, ws, Nil{}),
          FN.FN.fgroups_build_eq(g, ws, Nil{}))))
  FH.schedule_fguess_wit(G, C, n_root, nodup, g, ws, n, floor, best,
    SolveFast.fgroups_smaller(n, fg), eus, hnd)

# Helper for `ws == Nil{}` and `ws == [w]` (works for ANY `has_buf`!).
def FH.schedule_nil_wit(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +has_buf: Bool, +nodup: Bool, +g: +List<Nat>, +floor: Nat,
    +best: SolveRef.Best, skip: Bool,
    +esk: {skip == SolveFast.skippable(best, 0n) : Bool}) ->
  FH.GuessWit<G, C, n_root, has_buf, nodup, g, Nil{}, 0n, floor, best,
    SolveFast.schedule_fguess_lb(nodup, g, Nil{}, 0n, skip)>:
  match skip:
    case True{}:
      GWit{GCSkipLb{},
        Arr.DPair{{==},
          FLB.FS.skippable_to_le(best, 0n,
            Equal.sym(Bool, True{}, SolveFast.skippable(best, 0n), esk))}}
    case False{}:
      GWit{GCLive{Nil{}, SolveFast.End{} <> Nil{}, FP.PRefl{}},
        Arr.DPair{{==}, Arr.DPair{{==}, Arr.DPair{{==}, {==}}}}}

def FH.schedule_one_lb_wit(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +has_buf: Bool, +nodup: Bool, +g: +List<Nat>, +w: +List<Nat>,
    +floor: Nat, +best: SolveRef.Best, skip: Bool,
    +esk: {skip == SolveFast.skippable(best, 1n) : Bool},
    +heq: {Feedback.word_eq(g, w) == True{} : Bool}) ->
  FH.GuessWit<G, C, n_root, has_buf, nodup, g, w <> Nil{}, 1n, floor, best,
    SolveFast.schedule_one_lb(g, skip)>:
  match skip:
    case True{}:
      +egrp : {Groups.groups_build(g, w <> Nil{}, Nil{}) == Nil{}
               : +List<Groups.Group>} =
        Equal.cong(Bool, +List<Groups.Group>,
          b => Feedback.Bool.case(+List<Groups.Group>, b, Nil{},
                 Groups.group_add(w, Feedback.feedback(g, w), Nil{})),
          Feedback.word_eq(g, w), True{}, heq)
      +hle1 : {Nat.is_le(Eval.Eval.cost_of(best), 1n) == True{} : Bool} =
        FLB.FS.skippable_to_le(best, 1n,
          Equal.sym(Bool, True{}, SolveFast.skippable(best, 1n), esk))
      +hle : {Nat.is_le(Eval.Eval.cost_of(best),
                SolveFast.lower_bound(1n,
                  Groups.groups_build(g, w <> Nil{}, Nil{})))
              == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best), 1n,
          SolveFast.lower_bound(1n, Groups.groups_build(g, w <> Nil{}, Nil{})),
          Equal.cong(+List<Groups.Group>, Nat, gs => SolveFast.lower_bound(1n, gs),
            Nil{}, Groups.groups_build(g, w <> Nil{}, Nil{}),
            Equal.sym(+List<Groups.Group>,
              Groups.groups_build(g, w <> Nil{}, Nil{}), Nil{}, egrp)), hle1)
      GWit{GCSkipLb{}, Arr.DPair{{==}, hle}}
    case False{}:
      +egrp : {Groups.groups_build(g, w <> Nil{}, Nil{}) == Nil{}
               : +List<Groups.Group>} =
        Equal.cong(Bool, +List<Groups.Group>,
          b => Feedback.Bool.case(+List<Groups.Group>, b, Nil{},
                 Groups.group_add(w, Feedback.feedback(g, w), Nil{})),
          Feedback.word_eq(g, w), True{}, heq)
      +hus : {Groups.groups_smaller(w <> Nil{},
                Groups.groups_build(g, w <> Nil{}, Nil{})) == True{} : Bool} =
        Equal.cong(+List<Groups.Group>, Bool,
          gs => Groups.groups_smaller(w <> Nil{}, gs),
          Groups.groups_build(g, w <> Nil{}, Nil{}), Nil{}, egrp)
      GWit{GCLive{Nil{}, SolveFast.End{} <> Nil{}, FP.PRefl{}},
        Arr.DPair{{==}, Arr.DPair{hus, Arr.DPair{egrp, {==}}}}}

def FH.schedule_one_wit(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +has_buf: Bool, +nodup: Bool, +g: +List<Nat>, +w: +List<Nat>,
    +floor: Nat, +best: SolveRef.Best, same: Bool,
    +esame: {same == SolveFast.word_eq_fast(g, w) : Bool}) ->
  FH.GuessWit<G, C, n_root, has_buf, nodup, g, w <> Nil{}, 1n, floor, best,
    SolveFast.schedule_one_guess(g, best, same)>:
  match same:
    case True{}:
      +heq : {Feedback.word_eq(g, w) == True{} : Bool} =
        Equal.trans(Bool, Feedback.word_eq(g, w), SolveFast.word_eq_fast(g, w),
          True{},
          Equal.sym(Bool, SolveFast.word_eq_fast(g, w), Feedback.word_eq(g, w),
            FG.FG.word_eq_fast_eq(g, w)),
          Equal.sym(Bool, True{}, SolveFast.word_eq_fast(g, w), esame))
      FH.schedule_one_lb_wit(G, C, n_root, has_buf, nodup, g, w, floor, best,
        SolveFast.skippable(best, 1n), {==}, heq)
    case False{}:
      +hne : {Feedback.word_eq(g, w) == False{} : Bool} =
        Equal.trans(Bool, Feedback.word_eq(g, w), SolveFast.word_eq_fast(g, w),
          False{},
          Equal.sym(Bool, SolveFast.word_eq_fast(g, w), Feedback.word_eq(g, w),
            FG.FG.word_eq_fast_eq(g, w)),
          Equal.sym(Bool, False{}, SolveFast.word_eq_fast(g, w), esame))
      +egrp : {Groups.groups_build(g, w <> Nil{}, Nil{})
               == Groups.Group{Feedback.feedback(g, w), w <> Nil{}} <> Nil{}
               : +List<Groups.Group>} =
        Equal.cong(Bool, +List<Groups.Group>,
          b => Feedback.Bool.case(+List<Groups.Group>, b, Nil{},
                 Groups.Group{Feedback.feedback(g, w), w <> Nil{}} <> Nil{}),
          Feedback.word_eq(g, w), False{}, hne)
      +hnus : {Groups.groups_smaller(w <> Nil{},
                 Groups.groups_build(g, w <> Nil{}, Nil{})) == False{} : Bool} =
        Equal.cong(+List<Groups.Group>, Bool,
          gs => Groups.groups_smaller(w <> Nil{}, gs),
          Groups.groups_build(g, w <> Nil{}, Nil{}),
          Groups.Group{Feedback.feedback(g, w), w <> Nil{}} <> Nil{}, egrp)
      GWit{GCSkipUnusable{}, Arr.DPair{{==}, hnus}}

def FH.guess_body_buf_ge2_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    hook: FH.CapHookType(G, C),
    +n_root: Nat, has_buf: Bool, +row: U32, +g: +List<Nat>,
    +S: +List<SolveFast.CWord>, +n: Nat, +floor: Nat, +best: SolveRef.Best,
    +skip_self: Bool, buf: SolveFast.Buf5,
    +esk: {skip_self == Nat.is_eq(floor, Nat.add(n, n)) : Bool},
    +hge1: {Nat.is_le(1n, n) == True{} : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hrow: {FH.gentry_ok_if(has_buf, G, n_root, row, g) == True{} : Bool},
    +hS: {FH.cwords_ok_if(has_buf, G, C, n_root, S) == True{} : Bool},
    +hbuf: FH.BufOk(G, C, n_root, has_buf, True{}, buf)) ->
  FH.GuessSpec(G, C, n_root, has_buf, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.guess_body_buf_ge2(row, g, S, n, best, skip_self, buf)):
  match has_buf:
    case False{}:
      match buf:
        case SolveFast.NoBuf{}:
          Arr.DPair{
            FH.schedule_fguess_fast_wit(G, C, n_root, True{}, g,
              SolveFast.cwords_words(S), n, floor, best, en, hnd_s),
            Unit{}}
        case SolveFast.Buf5{s0, k0, t0, g0, gn0}:
          Empty.absurd(
            FH.GuessSpec(G, C, n_root, False{}, True{}, g,
              SolveFast.cwords_words(S), n, floor, best,
              SolveFast.guess_body_buf_ge2(row, g, S, n, best, skip_self,
                SolveFast.Buf5{s0, k0, t0, g0, gn0})), hbuf)
    case True{}:
      match buf:
        case SolveFast.NoBuf{}:
          Empty.absurd(
            FH.GuessSpec(G, C, n_root, True{}, True{}, g,
              SolveFast.cwords_words(S), n, floor, best,
              SolveFast.guess_body_buf_ge2(row, g, S, n, best, skip_self,
                SolveFast.NoBuf{})), hbuf)
        case SolveFast.Buf5{seen, bkts, tbl, +gen, +gn}:
          +r1 = Arr.Arr.dpair_r({True{} == True{} : Bool},
                  Arr.Arr.DPair<FH.SeenTree(10n, 0, seen, gen, Nil{}),
                    Arr.Arr.DPair<FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
                      Arr.Arr.DPair<FT.FT.TblOk(G, C, n_root, tbl),
                        {gn == Groups.len_words(G) : Nat}>>>, hbuf)
          +hs = Arr.Arr.dpair_l(FH.SeenTree(10n, 0, seen, gen, Nil{}),
                  Arr.Arr.DPair<FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
                    Arr.Arr.DPair<FT.FT.TblOk(G, C, n_root, tbl),
                      {gn == Groups.len_words(G) : Nat}>>, r1)
          +r2 = Arr.Arr.dpair_r(FH.SeenTree(10n, 0, seen, gen, Nil{}),
                  Arr.Arr.DPair<FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
                    Arr.Arr.DPair<FT.FT.TblOk(G, C, n_root, tbl),
                      {gn == Groups.len_words(G) : Nat}>>, r1)
          +r3 = Arr.Arr.dpair_r(FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
                  Arr.Arr.DPair<FT.FT.TblOk(G, C, n_root, tbl),
                    {gn == Groups.len_words(G) : Nat}>, r2)
          +hb = Arr.Arr.dpair_l(FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
                  Arr.Arr.DPair<FT.FT.TblOk(G, C, n_root, tbl),
                    {gn == Groups.len_words(G) : Nat}>, r2)
          +htbl = Arr.Arr.dpair_l(FT.FT.TblOk(G, C, n_root, tbl),
                    {gn == Groups.len_words(G) : Nat}, r3)
          +hgn : {gn == Groups.len_words(G) : Nat} =
            Arr.Arr.dpair_r(FT.FT.TblOk(G, C, n_root, tbl),
              {gn == Groups.len_words(G) : Nat}, r3)
          FH.guess_body_buf5_dup(G, C, gn, hgn, hook, n_root, row, g, S, n, floor, best,
            skip_self, seen, bkts, tbl, gen, esk, hge1, en, hnd_s, hrow, hS,
            hs, hb, htbl, Arr.Arr.dup(Nat, seen), Arr.Arr.dup(U32, tbl))

def FH.guess_body_buf_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    hook: FH.CapHookType(G, C),
    +n_root: Nat, +has_buf: Bool, +row: U32, +g: +List<Nat>,
    +S: +List<SolveFast.CWord>, +n: Nat, +floor: Nat, +best: SolveRef.Best,
    +skip_self: Bool, buf: SolveFast.Buf5,
    +esk: {skip_self == Nat.is_eq(floor, Nat.add(n, n)) : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hrow: {FH.gentry_ok_if(has_buf, G, n_root, row, g) == True{} : Bool},
    +hS: {FH.cwords_ok_if(has_buf, G, C, n_root, S) == True{} : Bool},
    +hbuf: FH.BufOk(G, C, n_root, has_buf, True{}, buf)) ->
  FH.GuessSpec(G, C, n_root, has_buf, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.guess_body_buf(row, g, S, n, best, skip_self, buf)):
  match S:
    case Nil{}:
      %Equal.sym(Nat, n, 0n, en) :
        FH.GuessSpec(G, C, n_root, has_buf, True{}, g, Nil{}, _, floor, best,
          SolveFast.GuessRes{
            SolveFast.schedule_fguess_lb(True{}, g, Nil{}, 0n,
              SolveFast.skippable(best, 0n)), buf})
      Arr.DPair{
        FH.schedule_nil_wit(G, C, n_root, has_buf, True{}, g, floor, best,
          SolveFast.skippable(best, 0n), {==}), hbuf}
    case Con{cw, +t}:
      match cw:
        case SolveFast.CWord{+ci, +grow, +w}:
          match t:
            case Nil{}:
              %Equal.sym(Nat, n, 1n, en) :
                FH.GuessSpec(G, C, n_root, has_buf, True{}, g, w <> Nil{}, _,
                  floor, best,
                  SolveFast.GuessRes{
                    SolveFast.schedule_one_guess(g, best,
                      SolveFast.word_eq_fast(g, w)), buf})
              Arr.DPair{
                FH.schedule_one_wit(G, C, n_root, has_buf, True{}, g, w, floor,
                  best, SolveFast.word_eq_fast(g, w), {==}), hbuf}
            case Con{cw2, +t2}:
              match cw2:
                case SolveFast.CWord{+ci2, +grow2, +w2}:
                  +cw1 : SolveFast.CWord = SolveFast.CWord{ci, grow, w}
                  +cw2a : SolveFast.CWord = SolveFast.CWord{ci2, grow2, w2}
                  +hge1 : {Nat.is_le(1n, n) == True{} : Bool} =
                    Equal.cong(Nat, Bool, x => Nat.is_le(1n, x),
                      n, 1n+(1n+Groups.len_words(SolveFast.cwords_words(t2))),
                      en)
                  FH.guess_body_buf_ge2_spec(G, C, hook, n_root, has_buf, row, g,
                    cw1 <> (cw2a <> t2), n, floor, best, skip_self, buf, esk,
                    hge1, en, hnd_s, hrow, hS, hbuf)

def FH.guess_items_mem_buf_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    hook: FH.CapHookType(G, C),
    +n_root: Nat, +has_buf: Bool, +row: U32, +g: +List<Nat>,
    +S: +List<SolveFast.CWord>, +n: Nat, +floor: Nat, +best: SolveRef.Best,
    +skip_self: Bool, buf: SolveFast.Buf5, in_s: Bool,
    +ein: {in_s == SolveFast.member_word_fast(g, SolveFast.cwords_words(S))
           : Bool},
    +ele2n: {SolveFast.skippable(best, Nat.add(n, n)) == True{} : Bool},
    +esk: {skip_self == Nat.is_eq(floor, Nat.add(n, n)) : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hrow: {FH.gentry_ok_if(has_buf, G, n_root, row, g) == True{} : Bool},
    +hS: {FH.cwords_ok_if(has_buf, G, C, n_root, S) == True{} : Bool},
    +hbuf: FH.BufOk(G, C, n_root, has_buf, True{}, buf)) ->
  FH.GuessSpec(G, C, n_root, has_buf, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.guess_items_mem_buf(row, g, S, n, best, skip_self, buf, in_s)):
  match in_s:
    case True{}:
      FH.guess_body_buf_spec(G, C, hook, n_root, has_buf, row, g, S, n, floor, best,
        skip_self, buf, esk, en, hnd_s, hrow, hS, hbuf)
    case False{}:
      +ws = SolveFast.cwords_words(S)
      +hnm : {Tree.member_word(g, ws) == False{} : Bool} =
        Equal.trans(Bool, Tree.member_word(g, ws),
          SolveFast.member_word_fast(g, ws), False{},
          Equal.sym(Bool, SolveFast.member_word_fast(g, ws),
            Tree.member_word(g, ws), FO.FO.member_word_fast_eq(g, ws)),
          Equal.sym(Bool, False{}, SolveFast.member_word_fast(g, ws), ein))
      +epre : {Nat.add(n, n) == SolveFast.pre_lb(n, g, ws) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(n, x),
          n, SolveFast.keep_fast(g, ws),
          Equal.trans(Nat, n, Groups.len_words(ws), SolveFast.keep_fast(g, ws),
            en,
            Equal.sym(Nat, SolveFast.keep_fast(g, ws), Groups.len_words(ws),
              FN.FN.keep_of_not_member(g, ws, hnm))))
      +hle : {Nat.is_le(Eval.Eval.cost_of(best), SolveFast.pre_lb(n, g, ws))
              == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best), Nat.add(n, n),
          SolveFast.pre_lb(n, g, ws), epre,
          FLB.FS.skippable_to_le(best, Nat.add(n, n), ele2n))
      Arr.DPair{GWit{GCSkipPre{}, Arr.DPair{{==}, hle}}, hbuf}

def FH.guess_items_nodup_buf_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    hook: FH.CapHookType(G, C),
    +n_root: Nat, +has_buf: Bool, +row: U32, +g: +List<Nat>,
    +S: +List<SolveFast.CWord>, +n: Nat, +floor: Nat, +best: SolveRef.Best,
    +skip_self: Bool, buf: SolveFast.Buf5, le_2n: Bool,
    +e2n: {le_2n == SolveFast.skippable(best, Nat.add(n, n)) : Bool},
    +esk: {skip_self == Nat.is_eq(floor, Nat.add(n, n)) : Bool},
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hnd_s: {FN.FN.no_dup_ref(SolveFast.cwords_words(S)) == True{} : Bool},
    +hrow: {FH.gentry_ok_if(has_buf, G, n_root, row, g) == True{} : Bool},
    +hS: {FH.cwords_ok_if(has_buf, G, C, n_root, S) == True{} : Bool},
    +hbuf: FH.BufOk(G, C, n_root, has_buf, True{}, buf)) ->
  FH.GuessSpec(G, C, n_root, has_buf, True{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.guess_items_nodup_buf(row, g, S, n, best, skip_self, buf, le_2n)):
  match le_2n:
    case False{}:
      FH.guess_body_buf_spec(G, C, hook, n_root, has_buf, row, g, S, n, floor, best,
        skip_self, buf, esk, en, hnd_s, hrow, hS, hbuf)
    case True{}:
      FH.guess_items_mem_buf_spec(G, C, hook, n_root, has_buf, row, g, S, n, floor,
        best, skip_self, buf,
        SolveFast.member_word_fast(g, SolveFast.cwords_words(S)), {==},
        Equal.sym(Bool, True{}, SolveFast.skippable(best, Nat.add(n, n)), e2n),
        esk, en, hnd_s, hrow, hS, hbuf)

def FH.guess_body_dup_wit(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +g: +List<Nat>, +ws: +List<+List<Nat>>, +n: Nat, +floor: Nat,
    +best: SolveRef.Best, +en: {n == Groups.len_words(ws) : Nat}) ->
  FH.GuessWit<G, C, n_root, False{}, False{}, g, ws, n, floor, best,
    SolveFast.guess_body(False{}, g, ws, n, best)>:
  match ws:
    case Nil{}:
      %Equal.sym(Nat, n, 0n, en) :
        FH.GuessWit<G, C, n_root, False{}, False{}, g, Nil{}, _, floor, best,
          SolveFast.schedule_fguess_lb(False{}, g, Nil{}, 0n,
            SolveFast.skippable(best, 0n))>
      FH.schedule_nil_wit(G, C, n_root, False{}, False{}, g, floor, best,
        SolveFast.skippable(best, 0n), {==})
    case Con{+w, +t}:
      match t:
        case Nil{}:
          %Equal.sym(Nat, n, 1n, en) :
            FH.GuessWit<G, C, n_root, False{}, False{}, g, w <> Nil{}, _, floor,
              best, SolveFast.schedule_one_guess(g, best,
                      SolveFast.word_eq_fast(g, w))>
          FH.schedule_one_wit(G, C, n_root, False{}, False{}, g, w, floor, best,
            SolveFast.word_eq_fast(g, w), {==})
        case Con{+w2, +t2}:
          FH.schedule_fguess_fast_wit(G, C, n_root, False{}, g,
            w <> (w2 <> t2), n, floor, best, en, {==})

def FH.guess_items_dup_wit(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, +g: +List<Nat>, +ws: +List<+List<Nat>>, +n: Nat, +floor: Nat,
    +best: SolveRef.Best, pre_skip: Bool,
    +ep: {pre_skip == SolveFast.skippable(best, SolveFast.pre_lb(n, g, ws))
          : Bool},
    +en: {n == Groups.len_words(ws) : Nat}) ->
  FH.GuessWit<G, C, n_root, False{}, False{}, g, ws, n, floor, best,
    SolveFast.guess_items_go(False{}, g, ws, n, best, pre_skip)>:
  match pre_skip:
    case True{}:
      GWit{GCSkipPre{},
        Arr.DPair{{==},
          FLB.FS.skippable_to_le(best, SolveFast.pre_lb(n, g, ws),
            Equal.sym(Bool, True{},
              SolveFast.skippable(best, SolveFast.pre_lb(n, g, ws)), ep))}}
    case False{}:
      FH.guess_body_dup_wit(G, C, n_root, g, ws, n, floor, best, en)

def FH.guess_items_buf_false_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n_root: Nat, has_buf: Bool, +g: +List<Nat>, +S: +List<SolveFast.CWord>,
    +n: Nat, +floor: Nat, +best: SolveRef.Best, buf: SolveFast.Buf5,
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hbuf: FH.BufOk(G, C, n_root, has_buf, False{}, buf)) ->
  FH.GuessSpec(G, C, n_root, has_buf, False{}, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.GuessRes{
      SolveFast.guess_items_go(False{}, g, SolveFast.cwords_words(S), n, best,
        SolveFast.skippable(best,
          SolveFast.pre_lb(n, g, SolveFast.cwords_words(S)))), buf}):
  match has_buf:
    case False{}:
      +ws = SolveFast.cwords_words(S)
      Arr.DPair{
        FH.guess_items_dup_wit(G, C, n_root, g, ws, n, floor, best,
          SolveFast.skippable(best, SolveFast.pre_lb(n, g, ws)), {==}, en),
        hbuf}
    case True{}:
      match buf:
        case SolveFast.NoBuf{}:
          Empty.absurd(
            FH.GuessSpec(G, C, n_root, True{}, False{}, g,
              SolveFast.cwords_words(S), n, floor, best,
              SolveFast.GuessRes{
                SolveFast.guess_items_go(False{}, g, SolveFast.cwords_words(S),
                  n, best,
                  SolveFast.skippable(best,
                    SolveFast.pre_lb(n, g, SolveFast.cwords_words(S)))),
                SolveFast.NoBuf{}}), hbuf)
        case SolveFast.Buf5{seen, bkts, tbl, gen, gn}:
          +hft = Arr.Arr.dpair_l({False{} == True{} : Bool},
                   Arr.Arr.DPair<FH.SeenTree(10n, 0, seen, gen, Nil{}),
                     Arr.Arr.DPair<FH.BktTree(G, C, n_root, 10n, 0, bkts, Nil{}),
                       Arr.Arr.DPair<FT.FT.TblOk(G, C, n_root, tbl),
                         {gn == Groups.len_words(G) : Nat}>>>, hbuf)
          Empty.absurd(
            FH.GuessSpec(G, C, n_root, True{}, False{}, g,
              SolveFast.cwords_words(S), n, floor, best,
              SolveFast.GuessRes{
                SolveFast.guess_items_go(False{}, g, SolveFast.cwords_words(S),
                  n, best,
                  SolveFast.skippable(best,
                    SolveFast.pre_lb(n, g, SolveFast.cwords_words(S)))),
                SolveFast.Buf5{seen, bkts, tbl, gen, gn}}),
            Logic.Proof.false_ne_true(hft))

# Main theorem: `guess_items_buf` satisfies the 5-case `FH.GuessSpec` and
# preserves `FH.BufOk`.
def FH.guess_items_buf_spec(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    hook: FH.CapHookType(G, C),
    +n_root: Nat, +has_buf: Bool, +nodup: Bool, +row: U32, +g: +List<Nat>,
    +S: +List<SolveFast.CWord>, +n: Nat, +floor: Nat, +best: SolveRef.Best,
    buf: SolveFast.Buf5,
    +en: {n == Groups.len_words(SolveFast.cwords_words(S)) : Nat},
    +hnd: {FN.FN.nodup_ok(nodup, SolveFast.cwords_words(S)) == True{} : Bool},
    +hrow: {FH.gentry_ok_if(has_buf, G, n_root, row, g) == True{} : Bool},
    +hS: {FH.cwords_ok_if(has_buf, G, C, n_root, S) == True{} : Bool},
    +hbuf: FH.BufOk(G, C, n_root, has_buf, nodup, buf)) ->
  FH.GuessSpec(G, C, n_root, has_buf, nodup, g, SolveFast.cwords_words(S), n,
    floor, best,
    SolveFast.guess_items_buf(nodup, row, g, S, n, floor, best, buf)):
  match nodup:
    case True{}:
      FH.guess_items_nodup_buf_spec(G, C, hook, n_root, has_buf, row, g, S, n, floor,
        best, Nat.is_eq(floor, Nat.add(n, n)), buf,
        SolveFast.skippable(best, Nat.add(n, n)), {==}, {==}, en, hnd, hrow,
        hS, hbuf)
    case False{}:
      FH.guess_items_buf_false_spec(G, C, n_root, has_buf, g, S, n, floor,
        best, buf, en, hbuf)
