# Precomputed feedback table (`Array<U32>`), `CWord` / `RowWord` indexing
# invariants, and O(1) table lookup specification for `src/solve_fast.bend`.
#
# Proves:
# - Exact `Word` / `U32` arithmetic for `U32.from_nat`, `U32.to_nat`, `U32.inc`,
#   `U32.add`, and `U32.sub` without reducing large powers of two.
# - `FT.depth_for_spec`: `SolveFast.depth_for(target) == Some{d}` implies
#   `d < 32` and `target <= 2^d`.
# - Symbolic depth-indexed `Data` invariant `FT.TblTree(d, base, tbl, G, C, n, upto)`
#   and `FT.TblOk(G, C, n, tbl)` preserved by `fill_tbl_go` and read by `Array.get`.
# - Pure boolean validity predicates `FT.gentry_ok_b`, `FT.cword_ok_b`,
#   `FT.cwords_ok_b`, and `FT.rws_ok_b` proved for `build_cwords` and
#   `glist_of_guesses` / `glist_of_cwords`.
# - `FT.tbl_lookup_eq`: looking up `U32.add(row, ci)` in a valid table `tbl`
#   preserves `tbl` (`Arr.get_fst`) and returns `FF5.encode_fb5_list(Feedback.feedback(g, w))`
#   with both `g` and `w` of length 5.
import Base
import ../src/feedback.bend as Feedback
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/solve_fast.bend as SolveFast
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./cover_list.bend as CoverList
import ./array.bend as Arr
import ./fast_groups.bend as FG
import ./fast_one.bend as FO
import ./fast_nodup.bend as FN
import ./fast_fb5.bend as FF5
import ./classbound_nat.bend as CBN
import ./feedback.bend as FbProof

# ---------------------------------------------------------------------------
# Section 1: Powers of two and elementary Nat arithmetic
# ---------------------------------------------------------------------------

def FT.pow2(d: Nat) -> Nat:
  match d:
    case 0n:
      1n
    case 1n++p:
      Nat.add(FT.pow2(p), FT.pow2(p))

def FT.pow2_pos(d: Nat) -> {Nat.is_le(1n, FT.pow2(d)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n++p:
      NatProof.Nat.is_le_trans(1n, FT.pow2(p), Nat.add(FT.pow2(p), FT.pow2(p)),
        FT.pow2_pos(p),
        NatProof.Nat.is_le_eq_l(Nat.add(FT.pow2(p), FT.pow2(p)),
          Nat.add(FT.pow2(p), 0n), FT.pow2(p),
          NatProof.NatPrf.add_zero(FT.pow2(p)),
          NatProof.Nat.is_le_add_l(0n, FT.pow2(p), FT.pow2(p),
            NatProof.Nat.is_le_zero_l(FT.pow2(p)))))

def FT.double_eq_add(n: Nat) -> {Nat.double(n) == Nat.add(n, n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat,
        2n+Nat.double(p),
        2n+Nat.add(p, p),
        1n+Nat.add(p, 1n+p),
        Equal.cong(Nat, Nat, x => 2n+x, Nat.double(p), Nat.add(p, p),
          FT.double_eq_add(p)),
        Equal.cong(Nat, Nat, x => 1n+x, 1n+Nat.add(p, p), Nat.add(p, 1n+p),
          Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p),
            NatProof.NatPrf.add_succ(p, p))))

def FT.nat_sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def FT.nat_sub_add_l(a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), a) == b : Nat}:
  match a:
    case 0n:
      FT.nat_sub_zero(b)
    case 1n+ap:
      FT.nat_sub_add_l(ap, b)

def FT.nat_sub_sub(a: Nat, +x: Nat, +b: Nat) ->
  {Nat.sub(Nat.sub(x, a), b) == Nat.sub(x, Nat.add(a, b)) : Nat}:
  match a x:
    case 0n _:
      Equal.cong(Nat, Nat, z => Nat.sub(z, b), Nat.sub(x, 0n), x,
        FT.nat_sub_zero(x))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+xp:
      FT.nat_sub_sub(ap, xp, b)

def FT.nat_le_succ_of_lt(+a: Nat, +b: Nat,
    +hlt: {Nat.is_lt(a, b) == True{} : Bool}) ->
  {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_le(1n+a, 0n) == True{} : Bool},
        Logic.Proof.false_ne_true(hlt))
    case 0n 1n+bp:
      NatProof.Nat.is_le_zero_l(bp)
    case 1n+ap 1n+bp:
      FT.nat_le_succ_of_lt(ap, bp, hlt)

def FT.nat_lt_zero_false(b: Nat) -> {Nat.is_lt(b, 0n) == False{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+bp:
      {==}

def FT.nat_lt_add_false(a: Nat, +b: Nat) ->
  {Nat.is_lt(Nat.add(a, b), a) == False{} : Bool}:
  match a:
    case 0n:
      FT.nat_lt_zero_false(b)
    case 1n+ap:
      FT.nat_lt_add_false(ap, b)

def FT.nat_lt_false_of_le(a: Nat, b: Nat,
    +hle: {Nat.is_le(b, a) == True{} : Bool}) ->
  {Nat.is_lt(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+ap 0n:
      {==}
    case 0n 1n++bp:
      Empty.absurd({Nat.is_lt(0n, 1n+bp) == False{} : Bool},
        Logic.Proof.false_ne_true(hle))
    case 1n+ap 1n+bp:
      FT.nat_lt_false_of_le(ap, bp, hle)

def FT.nat_le_of_lt_false(a: Nat, b: Nat,
    +hf: {Nat.is_lt(a, b) == False{} : Bool}) ->
  {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+ap 0n:
      {==}
    case 0n 1n++bp:
      Empty.absurd({Nat.is_le(1n+bp, 0n) == True{} : Bool},
        Logic.Proof.true_ne_false(hf))
    case 1n+ap 1n+bp:
      FT.nat_le_of_lt_false(ap, bp, hf)

def FT.nat_le_add_l(+a: Nat, +b: Nat) ->
  {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  NatProof.Nat.is_le_eq_l(Nat.add(a, b), Nat.add(a, 0n), a,
    NatProof.NatPrf.add_zero(a),
    NatProof.Nat.is_le_add_l(0n, b, a, NatProof.Nat.is_le_zero_l(b)))

def FT.nat_le_add_r(+a: Nat, +b: Nat) ->
  {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  NatProof.Nat.is_le_eq_r(b, Nat.add(b, a), Nat.add(a, b),
    NatProof.NatPrf.add_comm(b, a), FT.nat_le_add_l(b, a))

def FT.nat_add_le_add(+a1: Nat, +a2: Nat, +b1: Nat, +b2: Nat,
    +ha: {Nat.is_le(a1, a2) == True{} : Bool},
    +hb: {Nat.is_le(b1, b2) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(a1, b1), Nat.add(a2, b2)) == True{} : Bool}:
  NatProof.Nat.is_le_trans(Nat.add(a1, b1), Nat.add(a1, b2), Nat.add(a2, b2),
    NatProof.Nat.is_le_add_l(b1, b2, a1, hb),
    NatProof.Nat.is_le_eq_l(Nat.add(a2, b2), Nat.add(b2, a1), Nat.add(a1, b2),
      NatProof.NatPrf.add_comm(b2, a1),
      NatProof.Nat.is_le_eq_r(Nat.add(b2, a1), Nat.add(b2, a2), Nat.add(a2, b2),
        NatProof.NatPrf.add_comm(b2, a2),
        NatProof.Nat.is_le_add_l(a1, a2, b2, ha))))

def FT.nat_lt_add_l(+a: Nat, +b: Nat, +c: Nat,
    +h: {Nat.is_lt(a, b) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  match c:
    case 0n:
      h
    case 1n+cp:
      FT.nat_lt_add_l(a, b, cp, h)

def FT.nat_lt_add_r(+a: Nat, +b: Nat, +c: Nat,
    +h: {Nat.is_lt(a, b) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  Equal.trans(Bool,
    Nat.is_lt(Nat.add(a, c), Nat.add(b, c)),
    Nat.is_lt(Nat.add(c, a), Nat.add(c, b)),
    True{},
    Equal.trans(Bool,
      Nat.is_lt(Nat.add(a, c), Nat.add(b, c)),
      Nat.is_lt(Nat.add(c, a), Nat.add(b, c)),
      Nat.is_lt(Nat.add(c, a), Nat.add(c, b)),
      Equal.cong(Nat, Bool, x => Nat.is_lt(x, Nat.add(b, c)),
        Nat.add(a, c), Nat.add(c, a), NatProof.NatPrf.add_comm(a, c)),
      Equal.cong(Nat, Bool, y => Nat.is_lt(Nat.add(c, a), y),
        Nat.add(b, c), Nat.add(c, b), NatProof.NatPrf.add_comm(b, c))),
    FT.nat_lt_add_l(a, b, c, h))

def FT.nat_lt_half(a: Nat, b: Nat,
    +h: {Nat.is_lt(Nat.add(a, a), Nat.add(b, b)) == True{} : Bool}) ->
  {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      h
    case 0n 1n+bp:
      {==}
    case 1n++ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool},
        Logic.Proof.false_ne_true(h))
    case 1n++ap 1n++bp:
      +h1 : {Nat.is_lt(1n+Nat.add(ap, ap), 1n+Nat.add(bp, bp)) == True{} : Bool} =
        Equal.trans(Bool,
          Nat.is_lt(1n+Nat.add(ap, ap), 1n+Nat.add(bp, bp)),
          Nat.is_lt(Nat.add(ap, 1n+ap), Nat.add(bp, 1n+bp)),
          True{},
          Equal.trans(Bool,
            Nat.is_lt(1n+Nat.add(ap, ap), 1n+Nat.add(bp, bp)),
            Nat.is_lt(Nat.add(ap, 1n+ap), 1n+Nat.add(bp, bp)),
            Nat.is_lt(Nat.add(ap, 1n+ap), Nat.add(bp, 1n+bp)),
            Equal.cong(Nat, Bool, x => Nat.is_lt(x, 1n+Nat.add(bp, bp)),
              1n+Nat.add(ap, ap), Nat.add(ap, 1n+ap),
              Equal.sym(Nat, Nat.add(ap, 1n+ap), 1n+Nat.add(ap, ap),
                NatProof.NatPrf.add_succ(ap, ap))),
            Equal.cong(Nat, Bool, y => Nat.is_lt(Nat.add(ap, 1n+ap), y),
              1n+Nat.add(bp, bp), Nat.add(bp, 1n+bp),
              Equal.sym(Nat, Nat.add(bp, 1n+bp), 1n+Nat.add(bp, bp),
                NatProof.NatPrf.add_succ(bp, bp)))),
          h)
      FT.nat_lt_half(ap, bp, h1)

def FT.nat_double_lt_of_lt(+a: Nat, +b: Nat,
    +h: {Nat.is_lt(a, b) == True{} : Bool}) ->
  {Nat.is_lt(1n+Nat.add(a, a), Nat.add(b, b)) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_lt(1n+Nat.add(a, a), 0n) == True{} : Bool},
        Logic.Proof.false_ne_true(h))
    case 0n 1n++bp:
      Equal.cong(Nat, Bool, x => Nat.is_lt(0n, x),
        Nat.add(bp, 1n+bp), 1n+Nat.add(bp, bp),
        NatProof.NatPrf.add_succ(bp, bp))
    case 1n++ap 1n++bp:
      +ih : {Nat.is_lt(1n+Nat.add(ap, ap), Nat.add(bp, bp)) == True{} : Bool} =
        FT.nat_double_lt_of_lt(ap, bp, h)
      Equal.trans(Bool,
        Nat.is_lt(1n+Nat.add(ap, 1n+ap), Nat.add(bp, 1n+bp)),
        Nat.is_lt(1n+Nat.add(ap, ap), Nat.add(bp, bp)),
        True{},
        Equal.trans(Bool,
          Nat.is_lt(1n+Nat.add(ap, 1n+ap), Nat.add(bp, 1n+bp)),
          Nat.is_lt(2n+Nat.add(ap, ap), Nat.add(bp, 1n+bp)),
          Nat.is_lt(1n+Nat.add(ap, ap), Nat.add(bp, bp)),
          Equal.cong(Nat, Bool, x => Nat.is_lt(1n+x, Nat.add(bp, 1n+bp)),
            Nat.add(ap, 1n+ap), 1n+Nat.add(ap, ap),
            NatProof.NatPrf.add_succ(ap, ap)),
          Equal.cong(Nat, Bool, y => Nat.is_lt(2n+Nat.add(ap, ap), y),
            Nat.add(bp, 1n+bp), 1n+Nat.add(bp, bp),
            NatProof.NatPrf.add_succ(bp, bp))),
        ih)

def FT.nat_mul_succ(+a: Nat, +b: Nat) ->
  {Nat.mul(1n+a, b) == Nat.add(b, Nat.mul(a, b)) : Nat}:
  {==}

def FT.nat_add_comm_r(+a: Nat, +b: Nat, +c: Nat) ->
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

# ---------------------------------------------------------------------------
# Section 2: Word / U32 arithmetic (`to_nat`, `from_nat`, `inc`, `add`, `sub`)
# ---------------------------------------------------------------------------

def FT.word_to_nat_zero(m: Nat) ->
  {Word.to_nat(m, Word.zero(m)) == 0n : Nat}:
  match m:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, x => Nat.double(x), Word.to_nat(p, Word.zero(p)), 0n,
        FT.word_to_nat_zero(p))

def FT.word_to_nat_zero_from(+k: Nat, +m: Nat, +w: Word(m),
    +hz: {Arr.Arr.word_zero_from(k, m, w) == True{} : Bool}) ->
  {Nat.is_lt(Word.to_nat(m, w), FT.pow2(k)) == True{} : Bool}:
  match k m:
    case 0n _:
      +ew : {w == Word.zero(m) : Word(m)} = Arr.Arr.word_eq_zero(m, w, hz)
      +ez : {Word.to_nat(m, w) == 0n : Nat} =
        Equal.trans(Nat, Word.to_nat(m, w), Word.to_nat(m, Word.zero(m)), 0n,
          Equal.cong(Word(m), Nat, x => Word.to_nat(m, x), w, Word.zero(m), ew),
          FT.word_to_nat_zero(m))
      Equal.cong(Nat, Bool, x => Nat.is_lt(x, 1n), Word.to_nat(m, w), 0n, ez)
    case 1n++kp 0n:
      NatProof.Nat.is_lt_le_trans(0n, 1n, FT.pow2(1n+kp), {==},
        FT.pow2_pos(1n+kp))
    case 1n++kp 1n++mp:
      match w:
        case WCon{b, +t}:
          match b:
            case False{}:
              +ih : {Nat.is_lt(Word.to_nat(mp, t), FT.pow2(kp)) == True{} : Bool} =
                FT.word_to_nat_zero_from(kp, mp, t, hz)
              +ed : {Nat.double(Word.to_nat(mp, t))
                     == Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)) : Nat} =
                FT.double_eq_add(Word.to_nat(mp, t))
              +h1 : {Nat.is_lt(1n+Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)),
                       Nat.add(FT.pow2(kp), FT.pow2(kp))) == True{} : Bool} =
                FT.nat_double_lt_of_lt(Word.to_nat(mp, t), FT.pow2(kp), ih)
              +h0 : {Nat.is_lt(Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)),
                       Nat.add(FT.pow2(kp), FT.pow2(kp))) == True{} : Bool} =
                NatProof.Nat.is_le_lt_trans(
                  Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)),
                  1n+Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)),
                  Nat.add(FT.pow2(kp), FT.pow2(kp)),
                  NatProof.Nat.is_le_of_lt(
                    Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)),
                    1n+Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)),
                    NatProof.Nat.is_lt_succ_self(
                      Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)))),
                  h1)
              Equal.trans(Bool,
                Nat.is_lt(Nat.double(Word.to_nat(mp, t)),
                  Nat.add(FT.pow2(kp), FT.pow2(kp))),
                Nat.is_lt(Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)),
                  Nat.add(FT.pow2(kp), FT.pow2(kp))),
                True{},
                Equal.cong(Nat, Bool,
                  x => Nat.is_lt(x, Nat.add(FT.pow2(kp), FT.pow2(kp))),
                  Nat.double(Word.to_nat(mp, t)),
                  Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)), ed),
                h0)
            case True{}:
              +ih : {Nat.is_lt(Word.to_nat(mp, t), FT.pow2(kp)) == True{} : Bool} =
                FT.word_to_nat_zero_from(kp, mp, t, hz)
              +ed : {Nat.double(Word.to_nat(mp, t))
                     == Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)) : Nat} =
                FT.double_eq_add(Word.to_nat(mp, t))
              +h1 : {Nat.is_lt(1n+Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)),
                       Nat.add(FT.pow2(kp), FT.pow2(kp))) == True{} : Bool} =
                FT.nat_double_lt_of_lt(Word.to_nat(mp, t), FT.pow2(kp), ih)
              Equal.trans(Bool,
                Nat.is_lt(1n+Nat.double(Word.to_nat(mp, t)),
                  Nat.add(FT.pow2(kp), FT.pow2(kp))),
                Nat.is_lt(1n+Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)),
                  Nat.add(FT.pow2(kp), FT.pow2(kp))),
                True{},
                Equal.cong(Nat, Bool,
                  x => Nat.is_lt(1n+x, Nat.add(FT.pow2(kp), FT.pow2(kp))),
                  Nat.double(Word.to_nat(mp, t)),
                  Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)), ed),
                h1)

def FT.u32_to_nat_zero_from(+k: Nat, +u: U32,
    +hz: {Arr.Arr.u32_zero_from(k, u) == True{} : Bool}) ->
  {Nat.is_lt(U32.to_nat(u), FT.pow2(k)) == True{} : Bool}:
  match u:
    case U32{+w}:
      FT.word_to_nat_zero_from(k, 32n, w, hz)

def FT.word_zero_of_to_nat_zero(m: Nat, +w: Word(m),
    +hz: {Word.to_nat(m, w) == 0n : Nat}) ->
  {Arr.Arr.word_zero_from(0n, m, w) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n++p:
      match w:
        case WCon{b, +t}:
          match b:
            case True{}:
              Empty.absurd(
                {Arr.Arr.word_zero_from(0n, 1n+p, WCon{True{}, t})
                 == True{} : Bool},
                NatProof.NatPrf.zero_ne_succ(Nat.double(Word.to_nat(p, t)),
                  Equal.sym(Nat, 1n+Nat.double(Word.to_nat(p, t)), 0n, hz)))
            case False{}:
              +eadd : {Nat.add(Word.to_nat(p, t), Word.to_nat(p, t)) == 0n : Nat} =
                Equal.trans(Nat,
                  Nat.add(Word.to_nat(p, t), Word.to_nat(p, t)),
                  Nat.double(Word.to_nat(p, t)), 0n,
                  Equal.sym(Nat, Nat.double(Word.to_nat(p, t)),
                    Nat.add(Word.to_nat(p, t), Word.to_nat(p, t)),
                    FT.double_eq_add(Word.to_nat(p, t))),
                  hz)
              +hle : {Nat.is_le(Word.to_nat(p, t), 0n) == True{} : Bool} =
                NatProof.Nat.is_le_eq_r(Word.to_nat(p, t),
                  Nat.add(Word.to_nat(p, t), Word.to_nat(p, t)), 0n, eadd,
                  FT.nat_le_add_l(Word.to_nat(p, t), Word.to_nat(p, t)))
              FT.word_zero_of_to_nat_zero(p, t,
                NatProof.Nat.eq_zero_of_le_zero(Word.to_nat(p, t), hle))

def FT.word_zero_from_of_to_nat_lt(+k: Nat, +m: Nat, +w: Word(m),
    +hlt: {Nat.is_lt(Word.to_nat(m, w), FT.pow2(k)) == True{} : Bool}) ->
  {Arr.Arr.word_zero_from(k, m, w) == True{} : Bool}:
  match k m:
    case _ 0n:
      {==}
    case 0n 1n++mp:
      +hle : {Nat.is_le(Word.to_nat(1n+mp, w), 0n) == True{} : Bool} =
        NatProof.Nat.is_le_of_lt_succ(Word.to_nat(1n+mp, w), 0n, hlt)
      FT.word_zero_of_to_nat_zero(1n+mp, w,
        NatProof.Nat.eq_zero_of_le_zero(Word.to_nat(1n+mp, w), hle))
    case 1n++kp 1n++mp:
      match w:
        case WCon{b, +t}:
          match b:
            case False{}:
              +ed : {Nat.double(Word.to_nat(mp, t))
                     == Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)) : Nat} =
                FT.double_eq_add(Word.to_nat(mp, t))
              +h2 : {Nat.is_lt(Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)),
                       Nat.add(FT.pow2(kp), FT.pow2(kp))) == True{} : Bool} =
                Equal.trans(Bool,
                  Nat.is_lt(Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)),
                    Nat.add(FT.pow2(kp), FT.pow2(kp))),
                  Nat.is_lt(Nat.double(Word.to_nat(mp, t)),
                    Nat.add(FT.pow2(kp), FT.pow2(kp))),
                  True{},
                  Equal.cong(Nat, Bool,
                    x => Nat.is_lt(x, Nat.add(FT.pow2(kp), FT.pow2(kp))),
                    Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)),
                    Nat.double(Word.to_nat(mp, t)),
                    Equal.sym(Nat, Nat.double(Word.to_nat(mp, t)),
                      Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)), ed)),
                  hlt)
              FT.word_zero_from_of_to_nat_lt(kp, mp, t,
                FT.nat_lt_half(Word.to_nat(mp, t), FT.pow2(kp), h2))
            case True{}:
              +ed : {Nat.double(Word.to_nat(mp, t))
                     == Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)) : Nat} =
                FT.double_eq_add(Word.to_nat(mp, t))
              +h1 : {Nat.is_lt(Nat.double(Word.to_nat(mp, t)),
                       Nat.add(FT.pow2(kp), FT.pow2(kp))) == True{} : Bool} =
                NatProof.Nat.is_le_lt_trans(
                  Nat.double(Word.to_nat(mp, t)),
                  1n+Nat.double(Word.to_nat(mp, t)),
                  Nat.add(FT.pow2(kp), FT.pow2(kp)),
                  NatProof.Nat.is_le_of_lt(
                    Nat.double(Word.to_nat(mp, t)),
                    1n+Nat.double(Word.to_nat(mp, t)),
                    NatProof.Nat.is_lt_succ_self(Nat.double(Word.to_nat(mp, t)))),
                  hlt)
              +h2 : {Nat.is_lt(Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)),
                       Nat.add(FT.pow2(kp), FT.pow2(kp))) == True{} : Bool} =
                Equal.trans(Bool,
                  Nat.is_lt(Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)),
                    Nat.add(FT.pow2(kp), FT.pow2(kp))),
                  Nat.is_lt(Nat.double(Word.to_nat(mp, t)),
                    Nat.add(FT.pow2(kp), FT.pow2(kp))),
                  True{},
                  Equal.cong(Nat, Bool,
                    x => Nat.is_lt(x, Nat.add(FT.pow2(kp), FT.pow2(kp))),
                    Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)),
                    Nat.double(Word.to_nat(mp, t)),
                    Equal.sym(Nat, Nat.double(Word.to_nat(mp, t)),
                      Nat.add(Word.to_nat(mp, t), Word.to_nat(mp, t)), ed)),
                  h1)
              FT.word_zero_from_of_to_nat_lt(kp, mp, t,
                FT.nat_lt_half(Word.to_nat(mp, t), FT.pow2(kp), h2))

def FT.u32_zero_from_of_to_nat_lt(+k: Nat, +u: U32,
    +hlt: {Nat.is_lt(U32.to_nat(u), FT.pow2(k)) == True{} : Bool}) ->
  {Arr.Arr.u32_zero_from(k, u) == True{} : Bool}:
  match u:
    case U32{+w}:
      FT.word_zero_from_of_to_nat_lt(k, 32n, w, hlt)

def FT.word_has_zero(m: Nat, +w: Word(m)) -> Bool:
  match m:
    case 0n:
      False{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          Bool.or(Bool.not(b), FT.word_has_zero(p, t))

def FT.bool_or_r(+a: Bool, +b: Bool, +eb: {b == True{} : Bool}) ->
  {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      eb

def FT.word_has_zero_of_zero_from(+k: Nat, +m: Nat, +w: Word(m),
    +hkm: {Nat.is_lt(k, m) == True{} : Bool},
    +hz: {Arr.Arr.word_zero_from(k, m, w) == True{} : Bool}) ->
  {FT.word_has_zero(m, w) == True{} : Bool}:
  match k m:
    case _ 0n:
      Empty.absurd({False{} == True{} : Bool}, Logic.Proof.false_ne_true(hkm))
    case 0n 1n++mp:
      match w:
        case WCon{+b, +t}:
          +hnb : {Bool.not(b) == True{} : Bool} =
            Logic.Proof.and_true_l(Bool.not(b),
              Arr.Arr.word_zero_from(0n, mp, t), hz)
          Equal.cong(Bool, Bool, x => Bool.or(x, FT.word_has_zero(mp, t)),
            Bool.not(b), True{}, hnb)
    case 1n++kp 1n++mp:
      match w:
        case WCon{+b, +t}:
          FT.bool_or_r(Bool.not(b), FT.word_has_zero(mp, t),
            FT.word_has_zero_of_zero_from(kp, mp, t, hkm, hz))

def FT.word_inc_to_nat(+m: Nat, +w: Word(m),
    +hz: {FT.word_has_zero(m, w) == True{} : Bool}) ->
  {Word.to_nat(m, Word.inc(m, w)) == Nat.add(1n, Word.to_nat(m, w)) : Nat}:
  match m:
    case 0n:
      Empty.absurd({0n == 1n : Nat}, Logic.Proof.false_ne_true(hz))
    case 1n++p:
      match w:
        case WCon{b, +t}:
          match b:
            case False{}:
              {==}
            case True{}:
              Equal.cong(Nat, Nat, x => Nat.double(x),
                Word.to_nat(p, Word.inc(p, t)), 1n+Word.to_nat(p, t),
                FT.word_inc_to_nat(p, t, hz))

def FT.u32_inc_to_nat(+d: Nat, +u: U32,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hz: {Arr.Arr.u32_zero_from(d, u) == True{} : Bool}) ->
  {U32.to_nat(U32.inc(u)) == Nat.add(1n, U32.to_nat(u)) : Nat}:
  match u:
    case U32{+w}:
      FT.word_inc_to_nat(32n, w,
        FT.word_has_zero_of_zero_from(d, 32n, w, hd, hz))

def FT.u32_to_nat_from_nat(+d: Nat, +k: Nat,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hlt: {Nat.is_lt(k, FT.pow2(d)) == True{} : Bool}) ->
  {U32.to_nat(U32.from_nat(k)) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n++kp:
      +hkp : {Nat.is_lt(kp, FT.pow2(d)) == True{} : Bool} =
        NatProof.Nat.is_le_lt_trans(kp, 1n+kp, FT.pow2(d),
          NatProof.Nat.is_le_of_lt(kp, 1n+kp, NatProof.Nat.is_lt_succ_self(kp)),
          hlt)
      +ih : {U32.to_nat(U32.from_nat(kp)) == kp : Nat} =
        FT.u32_to_nat_from_nat(d, kp, hd, hkp)
      +hlt_u : {Nat.is_lt(U32.to_nat(U32.from_nat(kp)), FT.pow2(d))
                == True{} : Bool} =
        Equal.trans(Bool,
          Nat.is_lt(U32.to_nat(U32.from_nat(kp)), FT.pow2(d)),
          Nat.is_lt(kp, FT.pow2(d)), True{},
          Equal.cong(Nat, Bool, x => Nat.is_lt(x, FT.pow2(d)),
            U32.to_nat(U32.from_nat(kp)), kp, ih), hkp)
      +hz : {Arr.Arr.u32_zero_from(d, U32.from_nat(kp)) == True{} : Bool} =
        FT.u32_zero_from_of_to_nat_lt(d, U32.from_nat(kp), hlt_u)
      Equal.trans(Nat,
        U32.to_nat(U32.inc(U32.from_nat(kp))),
        Nat.add(1n, U32.to_nat(U32.from_nat(kp))),
        1n+kp,
        FT.u32_inc_to_nat(d, U32.from_nat(kp), hd, hz),
        Equal.cong(Nat, Nat, x => 1n+x, U32.to_nat(U32.from_nat(kp)), kp, ih))

def FT.u32_zero_from_from_nat(+d: Nat, +k: Nat,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hlt: {Nat.is_lt(k, FT.pow2(d)) == True{} : Bool}) ->
  {Arr.Arr.u32_zero_from(d, U32.from_nat(k)) == True{} : Bool}:
  FT.u32_zero_from_of_to_nat_lt(d, U32.from_nat(k),
    Equal.trans(Bool,
      Nat.is_lt(U32.to_nat(U32.from_nat(k)), FT.pow2(d)),
      Nat.is_lt(k, FT.pow2(d)), True{},
      Equal.cong(Nat, Bool, x => Nat.is_lt(x, FT.pow2(d)),
        U32.to_nat(U32.from_nat(k)), k,
        FT.u32_to_nat_from_nat(d, k, hd, hlt)),
      hlt))

def FT.double_add_eq(+p2: Nat, +s: Nat, +mt: Nat,
    +ih: {Nat.add(p2, s) == mt : Nat}) ->
  {Nat.add(Nat.add(p2, p2), Nat.double(s)) == Nat.double(mt) : Nat}:
  Equal.trans(Nat,
    Nat.add(Nat.add(p2, p2), Nat.double(s)),
    Nat.add(Nat.add(p2, s), Nat.add(p2, s)),
    Nat.double(mt),
    Equal.trans(Nat,
      Nat.add(Nat.add(p2, p2), Nat.double(s)),
      Nat.add(Nat.add(p2, p2), Nat.add(s, s)),
      Nat.add(Nat.add(p2, s), Nat.add(p2, s)),
      Equal.cong(Nat, Nat, x => Nat.add(Nat.add(p2, p2), x),
        Nat.double(s), Nat.add(s, s), FT.double_eq_add(s)),
      Equal.trans(Nat,
        Nat.add(Nat.add(p2, p2), Nat.add(s, s)),
        Nat.add(Nat.add(Nat.add(p2, p2), s), s),
        Nat.add(Nat.add(p2, s), Nat.add(p2, s)),
        Equal.sym(Nat,
          Nat.add(Nat.add(Nat.add(p2, p2), s), s),
          Nat.add(Nat.add(p2, p2), Nat.add(s, s)),
          NatProof.NatPrf.add_assoc(Nat.add(p2, p2), s, s)),
        Equal.trans(Nat,
          Nat.add(Nat.add(Nat.add(p2, p2), s), s),
          Nat.add(Nat.add(Nat.add(p2, s), p2), s),
          Nat.add(Nat.add(p2, s), Nat.add(p2, s)),
          Equal.cong(Nat, Nat, x => Nat.add(x, s),
            Nat.add(Nat.add(p2, p2), s),
            Nat.add(Nat.add(p2, s), p2),
            FT.nat_add_comm_r(p2, p2, s)),
          NatProof.NatPrf.add_assoc(Nat.add(p2, s), p2, s)))),
    Equal.trans(Nat,
      Nat.add(Nat.add(p2, s), Nat.add(p2, s)),
      Nat.add(mt, mt),
      Nat.double(mt),
      Equal.cong(Nat, Nat, x => Nat.add(x, x), Nat.add(p2, s), mt, ih),
      Equal.sym(Nat, Nat.double(mt), Nat.add(mt, mt), FT.double_eq_add(mt))))

def FT.word_to_nat_sub_pow2(+k: Nat, +m: Nat, +w: Word(m),
    +hz: {Arr.Arr.word_zero_from(1n+k, m, w) == True{} : Bool},
    +hb: {Arr.Arr.word_bit(k, m, w) == True{} : Bool},
    +lt: {Nat.is_lt(k, m) == True{} : Bool}) ->
  {Nat.add(FT.pow2(k), Word.to_nat(m, Word.sub(m, w, Arr.Arr.pow2_word(k, m))))
   == Word.to_nat(m, w) : Nat}:
  match k m:
    case _ 0n:
      Empty.absurd(
        {Nat.add(FT.pow2(k), Word.to_nat(0n, Word.sub(0n, w, Arr.Arr.pow2_word(k, 0n))))
         == Word.to_nat(0n, w) : Nat},
        Logic.Proof.false_ne_true(lt))
    case 0n 1n++mp:
      match w:
        case WCon{+b, +t}:
          +eb : {b == True{} : Bool} = hb
          +ew1 : {Word.sub(1n+mp, WCon{b, t}, Arr.Arr.pow2_word(0n, 1n+mp))
                  == WCon{False{}, Word.adc(mp, t, Word.zero(mp), True{}, True{})}
                  : Word(1n+mp)} =
            Equal.cong(Bool, Word(1n+mp),
              x => Word.sub(1n+mp, WCon{x, t}, Arr.Arr.pow2_word(0n, 1n+mp)),
              b, True{}, eb)
          +ew2 : {WCon{False{}, Word.adc(mp, t, Word.zero(mp), True{}, True{})}
                  == WCon{False{}, t} : Word(1n+mp)} =
            Equal.cong(Word(mp), Word(1n+mp), x => WCon{False{}, x},
              Word.adc(mp, t, Word.zero(mp), True{}, True{}), t,
              Arr.Arr.word_adc_sub_zero_t(mp, t))
          +ew : {Word.sub(1n+mp, WCon{b, t}, Arr.Arr.pow2_word(0n, 1n+mp))
                 == WCon{False{}, t} : Word(1n+mp)} =
            Equal.trans(Word(1n+mp),
              Word.sub(1n+mp, WCon{b, t}, Arr.Arr.pow2_word(0n, 1n+mp)),
              WCon{False{}, Word.adc(mp, t, Word.zero(mp), True{}, True{})},
              WCon{False{}, t}, ew1, ew2)
          Equal.trans(Nat,
            1n+Word.to_nat(1n+mp, Word.sub(1n+mp, WCon{b, t}, Arr.Arr.pow2_word(0n, 1n+mp))),
            1n+Nat.double(Word.to_nat(mp, t)),
            Word.to_nat(1n+mp, WCon{b, t}),
            Equal.cong(Word(1n+mp), Nat, x => 1n+Word.to_nat(1n+mp, x),
              Word.sub(1n+mp, WCon{b, t}, Arr.Arr.pow2_word(0n, 1n+mp)),
              WCon{False{}, t}, ew),
            Equal.cong(Bool, Nat, x => Word.to_nat(1n+mp, WCon{x, t}),
              True{}, b, Equal.sym(Bool, b, True{}, eb)))
    case 1n++kp 1n++mp:
      match w:
        case WCon{b, +t}:
          match b:
            case False{}:
              +ih = FT.word_to_nat_sub_pow2(kp, mp, t, hz, hb, lt)
              FT.double_add_eq(FT.pow2(kp),
                Word.to_nat(mp, Word.sub(mp, t, Arr.Arr.pow2_word(kp, mp))),
                Word.to_nat(mp, t), ih)
            case True{}:
              +ih = FT.word_to_nat_sub_pow2(kp, mp, t, hz, hb, lt)
              +s : Nat = Word.to_nat(mp, Word.sub(mp, t, Arr.Arr.pow2_word(kp, mp)))
              +p2 : Nat = FT.pow2(kp)
              +ed_sum = FT.double_add_eq(p2, s, Word.to_nat(mp, t), ih)
              Equal.trans(Nat,
                Nat.add(Nat.add(p2, p2), 1n+Nat.double(s)),
                1n+Nat.add(Nat.add(p2, p2), Nat.double(s)),
                1n+Nat.double(Word.to_nat(mp, t)),
                NatProof.NatPrf.add_succ(Nat.add(p2, p2), Nat.double(s)),
                Equal.cong(Nat, Nat, x => 1n+x,
                  Nat.add(Nat.add(p2, p2), Nat.double(s)),
                  Nat.double(Word.to_nat(mp, t)), ed_sum))

def FT.u32_to_nat_sub_pow2(+k: Nat, +u: U32,
    +hz: {Arr.Arr.u32_zero_from(1n+k, u) == True{} : Bool},
    +lt: {Nat.is_lt(k, 32n) == True{} : Bool},
    +hge: {U32.is_lt(u, Arr.Arr.pow2_u32(k)) == False{} : Bool}) ->
  {Nat.add(FT.pow2(k), U32.to_nat(U32.sub(u, Arr.Arr.pow2_u32(k))))
   == U32.to_nat(u) : Nat}:
  match u:
    case U32{+w}:
      +hnb : {Bool.not(Arr.Arr.word_bit(k, 32n, w)) == False{} : Bool} =
        Equal.trans(Bool,
          Bool.not(Arr.Arr.word_bit(k, 32n, w)),
          Cmp.is_lt(Word.cmp(32n, w, Arr.Arr.pow2_word(k, 32n))),
          False{},
          Equal.sym(Bool,
            Cmp.is_lt(Word.cmp(32n, w, Arr.Arr.pow2_word(k, 32n))),
            Bool.not(Arr.Arr.word_bit(k, 32n, w)),
            Arr.Arr.word_cmp_pow2_bit(k, 32n, w, hz, lt)),
          hge)
      FT.word_to_nat_sub_pow2(k, 32n, w, hz,
        Arr.Arr.bool_not_false(Arr.Arr.word_bit(k, 32n, w), hnb), lt)

def FT.word_adc_zero_l(m: Nat, +b: Word(m)) ->
  {Word.adc(m, Word.zero(m), b, False{}, False{}) == b : Word(m)}:
  match m:
    case 0n:
      match b:
        case WNil{}:
          {==}
    case 1n++p:
      match b:
        case WCon{bb, +bt}:
          match bb:
            case False{}:
              Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x},
                Word.adc(p, Word.zero(p), bt, False{}, False{}), bt,
                FT.word_adc_zero_l(p, bt))
            case True{}:
              Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x},
                Word.adc(p, Word.zero(p), bt, False{}, False{}), bt,
                FT.word_adc_zero_l(p, bt))

def FT.word_adc_carry_eq_inc_step(+p: Nat, ab: Bool, bb: Bool,
    +at: Word(p), +bt: Word(p),
    +ih: {Word.adc(p, at, bt, False{}, True{})
          == Word.inc(p, Word.adc(p, at, bt, False{}, False{})) : Word(p)}) ->
  {Word.adc(1n+p, WCon{ab, at}, WCon{bb, bt}, False{}, True{})
   == Word.inc(1n+p, Word.adc(1n+p, WCon{ab, at}, WCon{bb, bt}, False{}, False{}))
   : Word(1n+p)}:
  match ab bb:
    case False{} False{}:
      {==}
    case False{} True{}:
      Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x},
        Word.adc(p, at, bt, False{}, True{}),
        Word.inc(p, Word.adc(p, at, bt, False{}, False{})), ih)
    case True{} False{}:
      Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x},
        Word.adc(p, at, bt, False{}, True{}),
        Word.inc(p, Word.adc(p, at, bt, False{}, False{})), ih)
    case True{} True{}:
      {==}

def FT.word_adc_carry_eq_inc(m: Nat, +a: Word(m), +b: Word(m)) ->
  {Word.adc(m, a, b, False{}, True{})
   == Word.inc(m, Word.adc(m, a, b, False{}, False{})) : Word(m)}:
  match m:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          FT.word_adc_carry_eq_inc_step(p, ab, bb, at, bt,
            FT.word_adc_carry_eq_inc(p, at, bt))

def FT.word_adc_inc_l_step(+p: Nat, ab: Bool, bb: Bool,
    +at: Word(p), +bt: Word(p),
    +ih: {Word.adc(p, Word.inc(p, at), bt, False{}, False{})
          == Word.adc(p, at, bt, False{}, True{}) : Word(p)}) ->
  {Word.adc(1n+p, Word.inc(1n+p, WCon{ab, at}), WCon{bb, bt}, False{}, False{})
   == Word.adc(1n+p, WCon{ab, at}, WCon{bb, bt}, False{}, True{})
   : Word(1n+p)}:
  match ab bb:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      Equal.cong(Word(p), Word(1n+p), x => WCon{False{}, x},
        Word.adc(p, Word.inc(p, at), bt, False{}, False{}),
        Word.adc(p, at, bt, False{}, True{}), ih)
    case True{} True{}:
      Equal.cong(Word(p), Word(1n+p), x => WCon{True{}, x},
        Word.adc(p, Word.inc(p, at), bt, False{}, False{}),
        Word.adc(p, at, bt, False{}, True{}), ih)

def FT.word_adc_inc_l(m: Nat, +a: Word(m), +b: Word(m)) ->
  {Word.adc(m, Word.inc(m, a), b, False{}, False{})
   == Word.adc(m, a, b, False{}, True{}) : Word(m)}:
  match m:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match a b:
        case WCon{ab, +at} WCon{bb, +bt}:
          FT.word_adc_inc_l_step(p, ab, bb, at, bt,
            FT.word_adc_inc_l(p, at, bt))

def FT.word_add_inc_l(+m: Nat, +a: Word(m), +b: Word(m)) ->
  {Word.add(m, Word.inc(m, a), b) == Word.inc(m, Word.add(m, a, b)) : Word(m)}:
  Equal.trans(Word(m),
    Word.adc(m, Word.inc(m, a), b, False{}, False{}),
    Word.adc(m, a, b, False{}, True{}),
    Word.inc(m, Word.adc(m, a, b, False{}, False{})),
    FT.word_adc_inc_l(m, a, b),
    FT.word_adc_carry_eq_inc(m, a, b))

def FT.u32_add_zero_l(+b: U32) -> {U32.add(0, b) == b : U32}:
  match b:
    case U32{+w}:
      Equal.cong(Word(32n), U32, x => U32{x},
        Word.adc(32n, Word.zero(32n), w, False{}, False{}), w,
        FT.word_adc_zero_l(32n, w))

def FT.u32_add_inc_l(+a: U32, +b: U32) ->
  {U32.add(U32.inc(a), b) == U32.inc(U32.add(a, b)) : U32}:
  match a b:
    case U32{+wa} U32{+wb}:
      Equal.cong(Word(32n), U32, x => U32{x},
        Word.add(32n, Word.inc(32n, wa), wb),
        Word.inc(32n, Word.add(32n, wa, wb)),
        FT.word_add_inc_l(32n, wa, wb))

def FT.u32_add_from_nat(+a: Nat, +b: Nat) ->
  {U32.add(U32.from_nat(a), U32.from_nat(b)) == U32.from_nat(Nat.add(a, b)) : U32}:
  match a:
    case 0n:
      FT.u32_add_zero_l(U32.from_nat(b))
    case 1n++ap:
      Equal.trans(U32,
        U32.add(U32.inc(U32.from_nat(ap)), U32.from_nat(b)),
        U32.inc(U32.add(U32.from_nat(ap), U32.from_nat(b))),
        U32.inc(U32.from_nat(Nat.add(ap, b))),
        FT.u32_add_inc_l(U32.from_nat(ap), U32.from_nat(b)),
        Equal.cong(U32, U32, x => U32.inc(x),
          U32.add(U32.from_nat(ap), U32.from_nat(b)),
          U32.from_nat(Nat.add(ap, b)),
          FT.u32_add_from_nat(ap, b)))

# ---------------------------------------------------------------------------
# Section 3: `SolveFast.depth_for` specification
# ---------------------------------------------------------------------------

def FT.DepthSpec(+target: Nat, md: Maybe<Nat>) -> Data:
  match md:
    case None{}:
      Unit
    case Some{d}:
      Arr.Arr.DPair<{Nat.is_lt(d, 32n) == True{} : Bool},
                    {Nat.is_le(target, FT.pow2(d)) == True{} : Bool}>

def FT.depth_for_go_spec(+rem: Nat, +target: Nat, +pow: Nat, +d: Nat,
    ok: Bool,
    +eok: {ok == Nat.is_le(target, pow) : Bool},
    +epow: {pow == FT.pow2(d) : Nat},
    +hlt: {Nat.is_lt(Nat.add(rem, d), 32n) == True{} : Bool}) ->
  FT.DepthSpec(target, SolveFast.depth_for_go(rem, target, pow, d, ok)):
  match rem:
    case 0n:
      match ok:
        case False{}:
          Unit{}
        case True{}:
          +hle : {Nat.is_le(target, FT.pow2(d)) == True{} : Bool} =
            NatProof.Nat.is_le_eq_r(target, pow, FT.pow2(d), epow,
              Equal.sym(Bool, True{}, Nat.is_le(target, pow), eok))
          Arr.DPair{hlt, hle}
    case 1n++p:
      match ok:
        case True{}:
          +hd : {Nat.is_lt(d, 32n) == True{} : Bool} =
            NatProof.Nat.is_le_lt_trans(d, Nat.add(1n+p, d), 32n,
              FT.nat_le_add_r(1n+p, d), hlt)
          +hle : {Nat.is_le(target, FT.pow2(d)) == True{} : Bool} =
            NatProof.Nat.is_le_eq_r(target, pow, FT.pow2(d), epow,
              Equal.sym(Bool, True{}, Nat.is_le(target, pow), eok))
          Arr.DPair{hd, hle}
        case False{}:
          +epow2 : {Nat.add(pow, pow) == FT.pow2(1n+d) : Nat} =
            Equal.cong(Nat, Nat, x => Nat.add(x, x), pow, FT.pow2(d), epow)
          +hlt2 : {Nat.is_lt(Nat.add(p, 1n+d), 32n) == True{} : Bool} =
            Equal.trans(Bool,
              Nat.is_lt(Nat.add(p, 1n+d), 32n),
              Nat.is_lt(1n+Nat.add(p, d), 32n),
              True{},
              Equal.cong(Nat, Bool, x => Nat.is_lt(x, 32n),
                Nat.add(p, 1n+d), 1n+Nat.add(p, d),
                NatProof.NatPrf.add_succ(p, d)),
              hlt)
          FT.depth_for_go_spec(p, target, Nat.add(pow, pow), 1n+d,
            Nat.is_le(target, Nat.add(pow, pow)), {==}, epow2, hlt2)

def FT.depth_for_spec(+target: Nat) ->
  FT.DepthSpec(target, SolveFast.depth_for(target)):
  FT.depth_for_go_spec(25n, target, 1n, 0n, Nat.is_le(target, 1n),
    {==}, {==}, {==})

# ---------------------------------------------------------------------------
# Section 4: `FT.tbl_at`, `FT.TblTree`, `set`, `get`, and `fill_tbl_go`
# ---------------------------------------------------------------------------

def FT.nth_word(+ws: +List<+List<Nat>>, i: Nat) -> +List<Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, rest}:
      match i:
        case 0n:
          w
        case 1n+p:
          FT.nth_word(rest, p)

def FT.fb_code_words(+g: +List<Nat>, +a: +List<Nat>) -> U32:
  FF5.FF5.encode_fb5_list(Feedback.feedback(g, a))

def FT.tbl_at_step(+w: +List<Nat>, +G: +List<+List<Nat>>, +m: Nat, +idx: Nat,
    lt: Bool, rec: Nat -> U32) -> U32:
  match lt:
    case True{}:
      FT.fb_code_words(FT.nth_word(G, idx), w)
    case False{}:
      rec(Nat.sub(idx, m))

# The table is candidate-major: candidate `ci` owns the block `[ci*m, (ci+1)*m)`
# of slots, where `m = len(G)` is the number of guesses, and slot `ci*m + gi`
# holds the code of guess `gi` against candidate `ci`. `n` is `len(C)`, the
# number of blocks, and is only carried through the recursion.
def FT.tbl_at(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
              +idx: Nat) -> U32:
  match C:
    case Nil{}:
      0
    case Con{+w, +rest}:
      FT.tbl_at_step(w, G, Groups.len_words(G), idx,
        Nat.is_lt(idx, Groups.len_words(G)),
        idx2 => FT.tbl_at(G, rest, n, idx2))

def FT.tbl_at_head(+w: +List<Nat>, +rest: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, +n: Nat, +idx: Nat,
    +hlt: {Nat.is_lt(idx, Groups.len_words(G)) == True{} : Bool}) ->
  {FT.tbl_at(G, w <> rest, n, idx)
   == FT.fb_code_words(FT.nth_word(G, idx), w) : U32}:
  Equal.cong(Bool, U32,
    b => FT.tbl_at_step(w, G, Groups.len_words(G), idx, b,
           idx2 => FT.tbl_at(G, rest, n, idx2)),
    Nat.is_lt(idx, Groups.len_words(G)), True{}, hlt)

def FT.tbl_at_tail(+w: +List<Nat>, +rest: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, +n: Nat, +idx: Nat,
    +hf: {Nat.is_lt(idx, Groups.len_words(G)) == False{} : Bool}) ->
  {FT.tbl_at(G, w <> rest, n, idx)
   == FT.tbl_at(G, rest, n, Nat.sub(idx, Groups.len_words(G))) : U32}:
  Equal.cong(Bool, U32,
    b => FT.tbl_at_step(w, G, Groups.len_words(G), idx, b,
           idx2 => FT.tbl_at(G, rest, n, idx2)),
    Nat.is_lt(idx, Groups.len_words(G)), False{}, hf)

def FT.TblTree(+d: Nat, +base: Nat, a: Array<U32>,
               +G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
               +n: Nat, +upto: Nat) -> Data:
  match d:
    case 0n:
      match a:
        case ALeaf{v}:
          Feedback.Bool.case(Data, Nat.is_lt(base, upto),
            {v == FT.tbl_at(G, C, n, base) : U32}, Unit)
        case ANode{xs, ys}:
          Empty
    case 1n++p:
      match a:
        case ALeaf{v}:
          Empty
        case ANode{xs, ys}:
          Arr.Arr.DPair<
            FT.TblTree(p, base, xs, G, C, n, upto),
            FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto)>

def FT.tbl_tree_transport(+d: Nat, +base: Nat, -a1: Array<U32>, -a2: Array<U32>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat, +upto: Nat,
    +ea: {a1 == a2 : Array<U32>},
    +ht: FT.TblTree(d, base, a1, G, C, n, upto)) ->
  FT.TblTree(d, base, a2, G, C, n, upto):
  %ea : FT.TblTree(d, base, _, G, C, n, upto)
  ht

def FT.tbl_tree_transport_upto(+d: Nat, +base: Nat, -a: Array<U32>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    +u1: Nat, +u2: Nat, +eu: {u1 == u2 : Nat},
    +ht: FT.TblTree(d, base, a, G, C, n, u1)) ->
  FT.TblTree(d, base, a, G, C, n, u2):
  %eu : FT.TblTree(d, base, a, G, C, n, _)
  ht

def FT.tbl_tree_transport_gc(+d: Nat, -a1: Array<U32>, -a2: Array<U32>,
    +G1: +List<+List<Nat>>, +G2: +List<+List<Nat>>,
    +C1: +List<+List<Nat>>, +C2: +List<+List<Nat>>, +n: Nat,
    +u1: Nat, +u2: Nat,
    +ea: {a1 == a2 : Array<U32>},
    +eG: {G1 == G2 : +List<+List<Nat>>},
    +eC: {C1 == C2 : +List<+List<Nat>>},
    +eu: {u1 == u2 : Nat},
    +ht: FT.TblTree(d, 0n, a1, G1, C1, n, u1)) ->
  FT.TblTree(d, 0n, a2, G2, C2, n, u2):
  %ea : FT.TblTree(d, 0n, _, G2, C2, n, u2)
  %eG : FT.TblTree(d, 0n, a1, _, C2, n, u2)
  %eC : FT.TblTree(d, 0n, a1, G1, _, n, u2)
  %eu : FT.TblTree(d, 0n, a1, G1, C1, n, _)
  ht

def FT.tbl_tree_depth(+d: Nat, +base: Nat, a: Array<U32>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat, +upto: Nat,
    +ht: FT.TblTree(d, base, a, G, C, n, upto)) -> Arr.Arr.Depth(U32, d, a):
  match d:
    case 0n:
      match a:
        case ALeaf{v}:
          Unit{}
        case ANode{xs, ys}:
          ht
    case 1n++p:
      match a:
        case ALeaf{v}:
          ht
        case ANode{xs, ys}:
          +hxs = Arr.Arr.dpair_l(
                   FT.TblTree(p, base, xs, G, C, n, upto),
                   FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto),
                   ht)
          +hys = Arr.Arr.dpair_r(
                   FT.TblTree(p, base, xs, G, C, n, upto),
                   FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto),
                   ht)
          Arr.DPair{
            FT.tbl_tree_depth(p, base, xs, G, C, n, upto, hxs),
            FT.tbl_tree_depth(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto,
              hys)}

def FT.tbl_tree_new(+d: Nat, +base: Nat, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n: Nat) ->
  FT.TblTree(d, base, Array.new(U32, d, 0), G, C, n, 0n):
  match d:
    case 0n:
      %Equal.sym(Bool, Nat.is_lt(base, 0n), False{}, FT.nat_lt_zero_false(base)) :
        Feedback.Bool.case(Data, _, {0 == FT.tbl_at(G, C, n, base) : U32}, Unit)
      Unit{}
    case 1n++p:
      Arr.DPair{
        FT.tbl_tree_new(p, base, G, C, n),
        FT.tbl_tree_new(p, Nat.add(base, FT.pow2(p)), G, C, n)}

# Every leaf in a subtree starting at `base >= 1 + upto` trivially satisfies `TblTree(..., 1 + upto)`.
def FT.tbl_tree_ge_inc(+d: Nat, +base: Nat, a: Array<U32>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat, +upto: Nat,
    +hge: {Nat.is_le(1n+upto, base) == True{} : Bool},
    +ht: FT.TblTree(d, base, a, G, C, n, upto)) ->
  FT.TblTree(d, base, a, G, C, n, 1n+upto):
  match d:
    case 0n:
      match a:
        case ALeaf{v}:
          +hf : {Nat.is_lt(base, 1n+upto) == False{} : Bool} =
            FT.nat_lt_false_of_le(base, 1n+upto, hge)
          %Equal.sym(Bool, Nat.is_lt(base, 1n+upto), False{}, hf) :
            Feedback.Bool.case(Data, _, {v == FT.tbl_at(G, C, n, base) : U32}, Unit)
          Unit{}
        case ANode{xs, ys}:
          ht
    case 1n++p:
      match a:
        case ALeaf{v}:
          ht
        case ANode{xs, ys}:
          +hxs = Arr.Arr.dpair_l(
                   FT.TblTree(p, base, xs, G, C, n, upto),
                   FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto),
                   ht)
          +hys = Arr.Arr.dpair_r(
                   FT.TblTree(p, base, xs, G, C, n, upto),
                   FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto),
                   ht)
          +hge2 : {Nat.is_le(1n+upto, Nat.add(base, FT.pow2(p))) == True{} : Bool} =
            NatProof.Nat.is_le_trans(1n+upto, base, Nat.add(base, FT.pow2(p)),
              hge, FT.nat_le_add_l(base, FT.pow2(p)))
          Arr.DPair{
            FT.tbl_tree_ge_inc(p, base, xs, G, C, n, upto, hge, hxs),
            FT.tbl_tree_ge_inc(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto,
              hge2, hys)}

# Every leaf in a subtree with `base + 2^d <= upto` already satisfied `< upto`,
# so it also satisfies `< 1 + upto`.
def FT.tbl_tree_lt_inc(+d: Nat, +base: Nat, a: Array<U32>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat, +upto: Nat,
    +hle: {Nat.is_le(Nat.add(base, FT.pow2(d)), upto) == True{} : Bool},
    +ht: FT.TblTree(d, base, a, G, C, n, upto)) ->
  FT.TblTree(d, base, a, G, C, n, 1n+upto):
  match d:
    case 0n:
      match a:
        case ALeaf{v}:
          +hlt1 : {Nat.is_lt(base, upto) == True{} : Bool} =
            NatProof.Nat.is_lt_le_trans(base, Nat.add(base, 1n), upto,
              Equal.trans(Bool,
                Nat.is_lt(base, Nat.add(base, 1n)),
                Nat.is_lt(base, 1n+base), True{},
                Equal.cong(Nat, Bool, x => Nat.is_lt(base, x),
                  Nat.add(base, 1n), 1n+base, NatProof.NatPrf.add_comm(base, 1n)),
                NatProof.Nat.is_lt_succ_self(base)),
              hle)
          +hlt2 : {Nat.is_lt(base, 1n+upto) == True{} : Bool} =
            NatProof.Nat.is_lt_le_trans(base, upto, 1n+upto, hlt1,
              NatProof.Nat.is_le_of_lt(upto, 1n+upto,
                NatProof.Nat.is_lt_succ_self(upto)))
          +eqv : {v == FT.tbl_at(G, C, n, base) : U32} =
            %hlt1 : Feedback.Bool.case(Data, _, {v == FT.tbl_at(G, C, n, base) : U32}, Unit)
            ht
          %Equal.sym(Bool, Nat.is_lt(base, 1n+upto), True{}, hlt2) :
            Feedback.Bool.case(Data, _, {v == FT.tbl_at(G, C, n, base) : U32}, Unit)
          eqv
        case ANode{xs, ys}:
          ht
    case 1n++p:
      match a:
        case ALeaf{v}:
          ht
        case ANode{xs, ys}:
          +hxs = Arr.Arr.dpair_l(
                   FT.TblTree(p, base, xs, G, C, n, upto),
                   FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto),
                   ht)
          +hys = Arr.Arr.dpair_r(
                   FT.TblTree(p, base, xs, G, C, n, upto),
                   FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto),
                   ht)
          +hle_l : {Nat.is_le(Nat.add(base, FT.pow2(p)), upto) == True{} : Bool} =
            NatProof.Nat.is_le_trans(
              Nat.add(base, FT.pow2(p)),
              Nat.add(base, Nat.add(FT.pow2(p), FT.pow2(p))),
              upto,
              NatProof.Nat.is_le_add_l(FT.pow2(p),
                Nat.add(FT.pow2(p), FT.pow2(p)), base,
                FT.nat_le_add_l(FT.pow2(p), FT.pow2(p))),
              hle)
          +hle_r : {Nat.is_le(Nat.add(Nat.add(base, FT.pow2(p)), FT.pow2(p)), upto)
                    == True{} : Bool} =
            NatProof.Nat.is_le_eq_l(upto,
              Nat.add(base, Nat.add(FT.pow2(p), FT.pow2(p))),
              Nat.add(Nat.add(base, FT.pow2(p)), FT.pow2(p)),
              Equal.sym(Nat,
                Nat.add(Nat.add(base, FT.pow2(p)), FT.pow2(p)),
                Nat.add(base, Nat.add(FT.pow2(p), FT.pow2(p))),
                NatProof.NatPrf.add_assoc(base, FT.pow2(p), FT.pow2(p))),
              hle)
          Arr.DPair{
            FT.tbl_tree_lt_inc(p, base, xs, G, C, n, upto, hle_l, hxs),
            FT.tbl_tree_lt_inc(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto,
              hle_r, hys)}

# Setting the next slot `upto = base + U32.to_nat(i)` to `FT.tbl_at(G, C, n, upto)`.
def FT.tbl_swap_lo(+p: Nat, +base: Nat, -ys: Array<U32>, r: Array<U32> & U32,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat, +upto: Nat,
    +hr: FT.TblTree(p, base, Arr.Arr.fst(Array<U32>, U32, r), G, C, n, 1n+upto),
    +hy: FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, 1n+upto)) ->
  FT.TblTree(1n+p, base,
    Arr.Arr.fst(Array<U32>, U32, Array.swap.lo(U32, ys, r)), G, C, n, 1n+upto):
  (a2, res) = r
  Arr.DPair{hr, hy}

def FT.tbl_swap_hi(+p: Nat, +base: Nat, -xs: Array<U32>, r: Array<U32> & U32,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat, +upto: Nat,
    +hx: FT.TblTree(p, base, xs, G, C, n, 1n+upto),
    +hr: FT.TblTree(p, Nat.add(base, FT.pow2(p)),
           Arr.Arr.fst(Array<U32>, U32, r), G, C, n, 1n+upto)) ->
  FT.TblTree(1n+p, base,
    Arr.Arr.fst(Array<U32>, U32, Array.swap.hi(U32, xs, r)), G, C, n, 1n+upto):
  (a2, res) = r
  Arr.DPair{hx, hr}

def FT.tbl_tree_swap_go_lo(+p: Nat, +base: Nat, -xs: Array<U32>,
    -ys: Array<U32>, +G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n: Nat, +upto: Nat, +i: U32, +v: U32,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +hxs: FT.TblTree(p, base, xs, G, C, n, upto),
    +hys2: FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, 1n+upto),
    d: &a1: Array<U32> -> &a2: Array<U32> ->
       {a1 == xs : Array<U32>} & {a2 == a1 : Array<U32>},
    ih: @xs2: Array<U32> -> FT.TblTree(p, base, xs2, G, C, n, upto) ->
        FT.TblTree(p, base,
          Arr.Arr.fst(Array<U32>, U32,
            Array.swap.go(U32, xs2, Arr.Arr.pow2_u32(p), i, v,
              U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))), G, C, n, 1n+upto)) ->
  FT.TblTree(1n+p, base,
    Arr.Arr.fst(Array<U32>, U32,
      Array.swap.go(U32, ANode{xs, ys}, Arr.Arr.pow2_u32(1n+p), i, v,
        True{})), G, C, n, 1n+upto):
  (xs1, d2) = d
  (xs2, pe) = d2
  (+ex1, +ex2) = pe
  +hxs2 = FT.tbl_tree_transport(p, base, xs, xs2, G, C, n, upto,
            Equal.sym(Array<U32>, xs2, xs,
              Equal.trans(Array<U32>, xs2, xs1, xs, ex2, ex1)), hxs)
  +h2 = ih(xs2, hxs2)
  +h1 : FT.TblTree(p, base,
          Arr.Arr.fst(Array<U32>, U32,
            Array.swap.go(U32, xs1, Arr.Arr.pow2_u32(p), i, v,
              U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))), G, C, n, 1n+upto) =
    FT.tbl_tree_transport(p, base,
      Arr.Arr.fst(Array<U32>, U32,
        Array.swap.go(U32, xs2, Arr.Arr.pow2_u32(p), i, v,
          U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
      Arr.Arr.fst(Array<U32>, U32,
        Array.swap.go(U32, xs1, Arr.Arr.pow2_u32(p), i, v,
          U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
      G, C, n, 1n+upto,
      Equal.cong(Array<U32>, Array<U32>,
        x => Arr.Arr.fst(Array<U32>, U32,
               Array.swap.go(U32, x, Arr.Arr.pow2_u32(p), i, v,
                 U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
        xs2, xs1, ex2),
      h2)
  %ex1 : FT.TblTree(1n+p, base,
           Arr.Arr.fst(Array<U32>, U32,
             Array.swap.go(U32, ANode{_, ys}, Arr.Arr.pow2_u32(1n+p), i, v,
               True{})), G, C, n, 1n+upto)
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    FT.TblTree(1n+p, base,
      Arr.Arr.fst(Array<U32>, U32,
        Array.swap.lo(U32, ys,
          Array.swap.go(U32, xs1, _, i, v, U32.is_lt(i, U32.shr(_))))),
      G, C, n, 1n+upto)
  FT.tbl_swap_lo(p, base, ys,
    Array.swap.go(U32, xs1, Arr.Arr.pow2_u32(p), i, v,
      U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))),
    G, C, n, upto, h1, hys2)

def FT.tbl_tree_swap_go_hi(+p: Nat, +base: Nat, -xs: Array<U32>,
    -ys: Array<U32>, +G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n: Nat, +upto: Nat, +i: U32, +v: U32,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +hxs2: FT.TblTree(p, base, xs, G, C, n, 1n+upto),
    +hys: FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto),
    d: &a1: Array<U32> -> &a2: Array<U32> ->
       {a1 == ys : Array<U32>} & {a2 == a1 : Array<U32>},
    ih: @ys2: Array<U32> ->
        FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys2, G, C, n, upto) ->
        FT.TblTree(p, Nat.add(base, FT.pow2(p)),
          Arr.Arr.fst(Array<U32>, U32,
            Array.swap.go(U32, ys2, Arr.Arr.pow2_u32(p),
              U32.sub(i, Arr.Arr.pow2_u32(p)), v,
              U32.is_lt(U32.sub(i, Arr.Arr.pow2_u32(p)),
                U32.shr(Arr.Arr.pow2_u32(p))))), G, C, n, 1n+upto)) ->
  FT.TblTree(1n+p, base,
    Arr.Arr.fst(Array<U32>, U32,
      Array.swap.go(U32, ANode{xs, ys}, Arr.Arr.pow2_u32(1n+p), i, v,
        False{})), G, C, n, 1n+upto):
  (ys1, d2) = d
  (ys2, pe) = d2
  (+ey1, +ey2) = pe
  +base2 = Nat.add(base, FT.pow2(p))
  +ip = U32.sub(i, Arr.Arr.pow2_u32(p))
  +hys2 = FT.tbl_tree_transport(p, base2, ys, ys2, G, C, n, upto,
            Equal.sym(Array<U32>, ys2, ys,
              Equal.trans(Array<U32>, ys2, ys1, ys, ey2, ey1)), hys)
  +h2 = ih(ys2, hys2)
  +h1 : FT.TblTree(p, base2,
          Arr.Arr.fst(Array<U32>, U32,
            Array.swap.go(U32, ys1, Arr.Arr.pow2_u32(p), ip, v,
              U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))), G, C, n, 1n+upto) =
    FT.tbl_tree_transport(p, base2,
      Arr.Arr.fst(Array<U32>, U32,
        Array.swap.go(U32, ys2, Arr.Arr.pow2_u32(p), ip, v,
          U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
      Arr.Arr.fst(Array<U32>, U32,
        Array.swap.go(U32, ys1, Arr.Arr.pow2_u32(p), ip, v,
          U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
      G, C, n, 1n+upto,
      Equal.cong(Array<U32>, Array<U32>,
        y => Arr.Arr.fst(Array<U32>, U32,
               Array.swap.go(U32, y, Arr.Arr.pow2_u32(p), ip, v,
                 U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
        ys2, ys1, ey2),
      h2)
  %ey1 : FT.TblTree(1n+p, base,
           Arr.Arr.fst(Array<U32>, U32,
             Array.swap.go(U32, ANode{xs, _}, Arr.Arr.pow2_u32(1n+p), i, v,
               False{})), G, C, n, 1n+upto)
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    FT.TblTree(1n+p, base,
      Arr.Arr.fst(Array<U32>, U32,
        Array.swap.hi(U32, xs,
          Array.swap.go(U32, ys1, _, U32.sub(i, _), v,
            U32.is_lt(U32.sub(i, _), U32.shr(_))))),
      G, C, n, 1n+upto)
  FT.tbl_swap_hi(p, base, xs,
    Array.swap.go(U32, ys1, Arr.Arr.pow2_u32(p), ip, v,
      U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))),
    G, C, n, upto, hxs2, h1)

def FT.tbl_tree_swap_go(+d: Nat, +base: Nat, a: Array<U32>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat, +upto: Nat,
    +i: U32, +v: U32, z: Bool,
    +ez: {z == U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(d))) : Bool},
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.Arr.u32_zero_from(d, i) == True{} : Bool},
    +etgt: {Nat.add(base, U32.to_nat(i)) == upto : Nat},
    +ev: {v == FT.tbl_at(G, C, n, upto) : U32},
    +ht: FT.TblTree(d, base, a, G, C, n, upto)) ->
  FT.TblTree(d, base,
    Arr.Arr.fst(Array<U32>, U32,
      Array.swap.go(U32, a, Arr.Arr.pow2_u32(d), i, v, z)),
    G, C, n, 1n+upto):
  match d:
    case 0n:
      match a:
        case ALeaf{old}:
          +ei0 : {i == 0 : U32} = Arr.Arr.u32_eq_zero(i, zi)
          +ebase : {base == upto : Nat} =
            Equal.trans(Nat, base, Nat.add(base, 0n), upto,
              Equal.sym(Nat, Nat.add(base, 0n), base,
                NatProof.NatPrf.add_zero(base)),
              Equal.trans(Nat, Nat.add(base, 0n), Nat.add(base, U32.to_nat(i)),
                upto,
                Equal.cong(U32, Nat, x => Nat.add(base, U32.to_nat(x)), 0, i,
                  Equal.sym(U32, i, 0, ei0)),
                etgt))
          +hlt1 : {Nat.is_lt(base, 1n+upto) == True{} : Bool} =
            Equal.trans(Bool,
              Nat.is_lt(base, 1n+upto), Nat.is_lt(upto, 1n+upto), True{},
              Equal.cong(Nat, Bool, x => Nat.is_lt(x, 1n+upto), base, upto,
                ebase),
              NatProof.Nat.is_lt_succ_self(upto))
          +ev2 : {v == FT.tbl_at(G, C, n, base) : U32} =
            Equal.trans(U32, v, FT.tbl_at(G, C, n, upto),
              FT.tbl_at(G, C, n, base), ev,
              Equal.cong(Nat, U32, x => FT.tbl_at(G, C, n, x), upto, base,
                Equal.sym(Nat, base, upto, ebase)))
          %Equal.sym(Bool, Nat.is_lt(base, 1n+upto), True{}, hlt1) :
            Feedback.Bool.case(Data, _, {v == FT.tbl_at(G, C, n, base) : U32}, Unit)
          ev2
        case ANode{xs, ys}:
          Empty.absurd(
            FT.TblTree(0n, base,
              Arr.Arr.fst(Array<U32>, U32,
                Array.swap.go(U32, ANode{xs, ys}, Arr.Arr.pow2_u32(0n), i, v, z)),
              G, C, n, 1n+upto), ht)
    case 1n++p:
      match a:
        case ALeaf{old}:
          Empty.absurd(
            FT.TblTree(1n+p, base,
              Arr.Arr.fst(Array<U32>, U32,
                Array.swap.go(U32, ALeaf{old}, Arr.Arr.pow2_u32(1n+p), i, v, z)),
              G, C, n, 1n+upto), ht)
        case ANode{xs, ys}:
          match z:
            case True{}:
              +hxs = Arr.Arr.dpair_l(
                       FT.TblTree(p, base, xs, G, C, n, upto),
                       FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto),
                       ht)
              +hys = Arr.Arr.dpair_r(
                       FT.TblTree(p, base, xs, G, C, n, upto),
                       FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto),
                       ht)
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
              +hinat : {Nat.is_lt(U32.to_nat(i), FT.pow2(p)) == True{} : Bool} =
                FT.u32_to_nat_zero_from(p, i, zip)
              +hu_lt : {Nat.is_lt(upto, Nat.add(base, FT.pow2(p)))
                        == True{} : Bool} =
                Equal.trans(Bool,
                  Nat.is_lt(upto, Nat.add(base, FT.pow2(p))),
                  Nat.is_lt(Nat.add(base, U32.to_nat(i)),
                    Nat.add(base, FT.pow2(p))), True{},
                  Equal.cong(Nat, Bool,
                    x => Nat.is_lt(x, Nat.add(base, FT.pow2(p))),
                    upto, Nat.add(base, U32.to_nat(i)),
                    Equal.sym(Nat, Nat.add(base, U32.to_nat(i)), upto, etgt)),
                  FT.nat_lt_add_l(U32.to_nat(i), FT.pow2(p), base, hinat))
              +hge2 : {Nat.is_le(1n+upto, Nat.add(base, FT.pow2(p)))
                       == True{} : Bool} =
                FT.nat_le_succ_of_lt(upto, Nat.add(base, FT.pow2(p)),
                  hu_lt)
              +hys2 = FT.tbl_tree_ge_inc(p, Nat.add(base, FT.pow2(p)), ys,
                        G, C, n, upto, hge2, hys)
              FT.tbl_tree_swap_go_lo(p, base, xs, ys, G, C, n, upto, i, v,
                eshr, hxs, hys2, Arr.Arr.dup(U32, xs),
                xs2 => hxs2 =>
                  FT.tbl_tree_swap_go(p, base, xs2, G, C, n, upto, i, v,
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, etgt, ev, hxs2))
            case False{}:
              +hxs = Arr.Arr.dpair_l(
                       FT.TblTree(p, base, xs, G, C, n, upto),
                       FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto),
                       ht)
              +hys = Arr.Arr.dpair_r(
                       FT.TblTree(p, base, xs, G, C, n, upto),
                       FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto),
                       ht)
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
              +esub : {Nat.add(FT.pow2(p), U32.to_nat(ip)) == U32.to_nat(i) : Nat} =
                FT.u32_to_nat_sub_pow2(p, i, zi, plt, ige)
              +etgt2 : {Nat.add(Nat.add(base, FT.pow2(p)), U32.to_nat(ip))
                        == upto : Nat} =
                Equal.trans(Nat,
                  Nat.add(Nat.add(base, FT.pow2(p)), U32.to_nat(ip)),
                  Nat.add(base, Nat.add(FT.pow2(p), U32.to_nat(ip))),
                  upto,
                  NatProof.NatPrf.add_assoc(base, FT.pow2(p), U32.to_nat(ip)),
                  Equal.trans(Nat,
                    Nat.add(base, Nat.add(FT.pow2(p), U32.to_nat(ip))),
                    Nat.add(base, U32.to_nat(i)), upto,
                    Equal.cong(Nat, Nat, x => Nat.add(base, x),
                      Nat.add(FT.pow2(p), U32.to_nat(ip)), U32.to_nat(i), esub),
                    etgt))
              +hle_l : {Nat.is_le(Nat.add(base, FT.pow2(p)), upto)
                        == True{} : Bool} =
                NatProof.Nat.is_le_eq_r(Nat.add(base, FT.pow2(p)),
                  Nat.add(Nat.add(base, FT.pow2(p)), U32.to_nat(ip)), upto,
                  etgt2,
                  FT.nat_le_add_l(Nat.add(base, FT.pow2(p)), U32.to_nat(ip)))
              +hxs2 = FT.tbl_tree_lt_inc(p, base, xs, G, C, n, upto, hle_l, hxs)
              FT.tbl_tree_swap_go_hi(p, base, xs, ys, G, C, n, upto, i, v,
                eshr, hxs2, hys, Arr.Arr.dup(U32, ys),
                ys2 => hys2 =>
                  FT.tbl_tree_swap_go(p, Nat.add(base, FT.pow2(p)), ys2,
                    G, C, n, upto, ip, v,
                    U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, etgt2, ev, hys2))

def FT.tbl_tree_set_dup3(+d: Nat, -tbl: Array<U32>, a1: Array<U32>,
    b1: Array<U32>, -b2: Array<U32>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat, +upto: Nat,
    +v: U32,
    +ea1: {a1 == tbl : Array<U32>},
    +ea_b1: {b1 == a1 : Array<U32>},
    +eb2: {b2 == b1 : Array<U32>},
    dp3: &c1: Array<U32> -> &c2: Array<U32> ->
         {c1 == b2 : Array<U32>} & {c2 == c1 : Array<U32>},
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hlt: {Nat.is_lt(upto, FT.pow2(d)) == True{} : Bool},
    +ev: {v == FT.tbl_at(G, C, n, upto) : U32},
    +ht: FT.TblTree(d, 0n, tbl, G, C, n, upto)) ->
  FT.TblTree(d, 0n, Array.set(U32, tbl, U32.from_nat(upto), v),
    G, C, n, 1n+upto):
  (c1, dp4) = dp3
  (c2, pe3) = dp4
  (+ec1, +ec2) = pe3
  +idx = U32.from_nat(upto)
  +zi : {Arr.Arr.u32_zero_from(d, idx) == True{} : Bool} =
    FT.u32_zero_from_from_nat(d, upto, hd, hlt)
  +etgt : {U32.to_nat(idx) == upto : Nat} =
    FT.u32_to_nat_from_nat(d, upto, hd, hlt)
  +ea_b2 : {b2 == a1 : Array<U32>} = Equal.trans(Array<U32>, b2, b1, a1, eb2, ea_b1)
  +ec1_b1 : {c1 == b1 : Array<U32>} = Equal.trans(Array<U32>, c1, b2, b1, ec1, eb2)
  +ec2_b1 : {c2 == b1 : Array<U32>} = Equal.trans(Array<U32>, c2, c1, b1, ec2, ec1_b1)
  +ec2_a1 : {c2 == a1 : Array<U32>} = Equal.trans(Array<U32>, c2, b1, a1, ec2_b1, ea_b1)
  +ht1 = FT.tbl_tree_transport(d, 0n, tbl, a1, G, C, n, upto,
           Equal.sym(Array<U32>, a1, tbl, ea1), ht)
  +ht_b1 = FT.tbl_tree_transport(d, 0n, a1, b1, G, C, n, upto,
             Equal.sym(Array<U32>, b1, a1, ea_b1), ht1)
  +hdp_b1 = FT.tbl_tree_depth(d, 0n, b1, G, C, n, upto, ht_b1)
  +hdp_c2 = Arr.Arr.depth_transport(U32, d, b1, c2,
              Equal.sym(Array<U32>, c2, b1, ec2_b1), hdp_b1)
  +em : {U32.and(idx, U32.sub(Arr.Arr.pow2_u32(d), 1)) == idx : U32} =
    Arr.Arr.u32_and_mask(d, idx, zi)
  +eset_c2 : {Array.set(U32, c2, idx, v)
              == Arr.Arr.fst(Array<U32>, U32, Array.swap(U32, c2, idx, v))
              : Array<U32>} =
    Equal.trans(Array<U32>,
      Array.set(U32, c2, idx, v),
      Array.set(U32, c1, idx, v),
      Arr.Arr.fst(Array<U32>, U32, Array.swap(U32, c2, idx, v)),
      Equal.cong(Array<U32>, Array<U32>, x => Array.set(U32, x, idx, v),
        c2, c1, ec2),
      Equal.trans(Array<U32>,
        Array.set(U32, c1, idx, v),
        Arr.Arr.fst(Array<U32>, U32, Array.swap(U32, c1, idx, v)),
        Arr.Arr.fst(Array<U32>, U32, Array.swap(U32, c2, idx, v)),
        Arr.Arr.set_eq(U32, c1, idx, v),
        Equal.cong(Array<U32>, Array<U32>,
          x => Arr.Arr.fst(Array<U32>, U32, Array.swap(U32, x, idx, v)),
          c1, c2, Equal.sym(Array<U32>, c2, c1, ec2))))
  +esw : {Array.set(U32, c2, idx, v)
          == Arr.Arr.fst(Array<U32>, U32,
               Array.swap.go(U32, c2, Arr.Arr.pow2_u32(d), idx, v,
                 U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))) : Array<U32>} =
    Equal.trans(Array<U32>,
      Array.set(U32, c2, idx, v),
      Arr.Arr.fst(Array<U32>, U32, Array.swap(U32, c2, idx, v)),
      Arr.Arr.fst(Array<U32>, U32,
        Array.swap.go(U32, c2, Arr.Arr.pow2_u32(d), idx, v,
          U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))),
      eset_c2,
      Equal.trans(Array<U32>,
        Arr.Arr.fst(Array<U32>, U32, Array.swap(U32, c2, idx, v)),
        Arr.Arr.fst(Array<U32>, U32,
          Array.swap.go(U32, c2, Arr.Arr.pow2_u32(d),
            U32.and(idx, U32.sub(Arr.Arr.pow2_u32(d), 1)), v,
            U32.is_lt(U32.and(idx, U32.sub(Arr.Arr.pow2_u32(d), 1)),
              U32.shr(Arr.Arr.pow2_u32(d))))),
        Arr.Arr.fst(Array<U32>, U32,
          Array.swap.go(U32, c2, Arr.Arr.pow2_u32(d), idx, v,
            U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))),
        Arr.Arr.swap_depth(U32, d, c2, idx, v, hdp_c2),
        Equal.cong(U32, Array<U32>,
          j => Arr.Arr.fst(Array<U32>, U32,
                 Array.swap.go(U32, c2, Arr.Arr.pow2_u32(d), j, v,
                   U32.is_lt(j, U32.shr(Arr.Arr.pow2_u32(d))))),
          U32.and(idx, U32.sub(Arr.Arr.pow2_u32(d), 1)), idx, em)))
  +hgo = FT.tbl_tree_swap_go(d, 0n, a1, G, C, n, upto, idx, v,
           U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))), {==}, hd, zi,
           etgt, ev, ht1)
  +eq_a : {Arr.Arr.fst(Array<U32>, U32,
             Array.swap.go(U32, a1, Arr.Arr.pow2_u32(d), idx, v,
               U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d)))))
           == Array.set(U32, c2, idx, v) : Array<U32>} =
    Equal.trans(Array<U32>,
      Arr.Arr.fst(Array<U32>, U32,
        Array.swap.go(U32, a1, Arr.Arr.pow2_u32(d), idx, v,
          U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))),
      Arr.Arr.fst(Array<U32>, U32,
        Array.swap.go(U32, c2, Arr.Arr.pow2_u32(d), idx, v,
          U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))),
      Array.set(U32, c2, idx, v),
      Equal.cong(Array<U32>, Array<U32>,
        x => Arr.Arr.fst(Array<U32>, U32,
               Array.swap.go(U32, x, Arr.Arr.pow2_u32(d), idx, v,
                 U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))),
        a1, c2, Equal.sym(Array<U32>, c2, a1, ec2_a1)),
      Equal.sym(Array<U32>, Array.set(U32, c2, idx, v),
        Arr.Arr.fst(Array<U32>, U32,
          Array.swap.go(U32, c2, Arr.Arr.pow2_u32(d), idx, v,
            U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))),
        esw))
  %ea1 : FT.TblTree(d, 0n, Array.set(U32, _, idx, v), G, C, n, 1n+upto)
  %ec2_a1 : FT.TblTree(d, 0n, Array.set(U32, _, idx, v), G, C, n, 1n+upto)
  FT.tbl_tree_transport(d, 0n,
    Arr.Arr.fst(Array<U32>, U32,
      Array.swap.go(U32, a1, Arr.Arr.pow2_u32(d), idx, v,
        U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))),
    Array.set(U32, c2, idx, v), G, C, n, 1n+upto, eq_a, hgo)

def FT.tbl_tree_set_dup2(+d: Nat, -tbl: Array<U32>, a1: Array<U32>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat, +upto: Nat,
    +v: U32,
    +ea1: {a1 == tbl : Array<U32>}, -a2: Array<U32>,
    +ea2: {a2 == a1 : Array<U32>},
    dp2: &b1: Array<U32> -> &b2: Array<U32> ->
         {b1 == a2 : Array<U32>} & {b2 == b1 : Array<U32>},
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hlt: {Nat.is_lt(upto, FT.pow2(d)) == True{} : Bool},
    +ev: {v == FT.tbl_at(G, C, n, upto) : U32},
    +ht: FT.TblTree(d, 0n, tbl, G, C, n, upto)) ->
  FT.TblTree(d, 0n, Array.set(U32, tbl, U32.from_nat(upto), v),
    G, C, n, 1n+upto):
  (b1, dp3) = dp2
  (b2, pe2) = dp3
  (+eb1, +eb2) = pe2
  +ea_b1 : {b1 == a1 : Array<U32>} = Equal.trans(Array<U32>, b1, a2, a1, eb1, ea2)
  FT.tbl_tree_set_dup3(d, tbl, a1, b1, b2, G, C, n, upto, v,
    ea1, ea_b1, eb2, Arr.Arr.dup(U32, b2), hd, hlt, ev, ht)

def FT.tbl_tree_set_dup(+d: Nat, -tbl: Array<U32>, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n: Nat, +upto: Nat, +v: U32,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hlt: {Nat.is_lt(upto, FT.pow2(d)) == True{} : Bool},
    +ev: {v == FT.tbl_at(G, C, n, upto) : U32},
    +ht: FT.TblTree(d, 0n, tbl, G, C, n, upto),
    dp: &a1: Array<U32> -> &a2: Array<U32> ->
        {a1 == tbl : Array<U32>} & {a2 == a1 : Array<U32>}) ->
  FT.TblTree(d, 0n, Array.set(U32, tbl, U32.from_nat(upto), v),
    G, C, n, 1n+upto):
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  FT.tbl_tree_set_dup2(d, tbl, a1, G, C, n, upto, v, ea1, a2, ea2,
    Arr.Arr.dup(U32, a2), hd, hlt, ev, ht)

def FT.tbl_tree_set(+d: Nat, tbl: Array<U32>, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n: Nat, +upto: Nat, +v: U32,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hlt: {Nat.is_lt(upto, FT.pow2(d)) == True{} : Bool},
    +ev: {v == FT.tbl_at(G, C, n, upto) : U32},
    +ht: FT.TblTree(d, 0n, tbl, G, C, n, upto)) ->
  FT.TblTree(d, 0n, Array.set(U32, tbl, U32.from_nat(upto), v),
    G, C, n, 1n+upto):
  FT.tbl_tree_set_dup(d, tbl, G, C, n, upto, v, hd, hlt, ev, ht,
    Arr.Arr.dup(U32, tbl))

# Reading `tbl` at any in-range index `< upto` returns `FT.tbl_at(G, C, n, idx)`.
def FT.tbl_get_lo(-ys: Array<U32>, r: Array<U32> & U32,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat, +k: Nat,
    +hr: {Arr.Arr.snd(Array<U32>, U32, r) == FT.tbl_at(G, C, n, k) : U32}) ->
  {Arr.Arr.snd(Array<U32>, U32, Array.swap.lo(U32, ys, r))
   == FT.tbl_at(G, C, n, k) : U32}:
  (a, +v) = r
  hr

def FT.tbl_get_hi(-xs: Array<U32>, r: Array<U32> & U32,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat, +k: Nat,
    +hr: {Arr.Arr.snd(Array<U32>, U32, r) == FT.tbl_at(G, C, n, k) : U32}) ->
  {Arr.Arr.snd(Array<U32>, U32, Array.swap.hi(U32, xs, r))
   == FT.tbl_at(G, C, n, k) : U32}:
  (a, +v) = r
  hr

def FT.tbl_tree_get_go_lo(+p: Nat, +base: Nat, -xs: Array<U32>,
    -ys: Array<U32>, +G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n: Nat, +upto: Nat, +i: U32,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +hxs: FT.TblTree(p, base, xs, G, C, n, upto),
    d: &a1: Array<U32> -> &a2: Array<U32> ->
       {a1 == xs : Array<U32>} & {a2 == a1 : Array<U32>},
    ih: @xs2: Array<U32> -> FT.TblTree(p, base, xs2, G, C, n, upto) ->
        {Arr.Arr.snd(Array<U32>, U32,
           Array.get.go(U32, xs2, Arr.Arr.pow2_u32(p), i,
             U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))))
         == FT.tbl_at(G, C, n, Nat.add(base, U32.to_nat(i))) : U32}) ->
  {Arr.Arr.snd(Array<U32>, U32,
     Array.get.go(U32, ANode{xs, ys}, Arr.Arr.pow2_u32(1n+p), i, True{}))
   == FT.tbl_at(G, C, n, Nat.add(base, U32.to_nat(i))) : U32}:
  (xs1, d2) = d
  (xs2, pe) = d2
  (+ex1, +ex2) = pe
  +hxs2 = FT.tbl_tree_transport(p, base, xs, xs2, G, C, n, upto,
            Equal.sym(Array<U32>, xs2, xs,
              Equal.trans(Array<U32>, xs2, xs1, xs, ex2, ex1)), hxs)
  +h2 = ih(xs2, hxs2)
  +h1 : {Arr.Arr.snd(Array<U32>, U32,
           Array.get.go(U32, xs1, Arr.Arr.pow2_u32(p), i,
             U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))))
         == FT.tbl_at(G, C, n, Nat.add(base, U32.to_nat(i))) : U32} =
    Equal.trans(U32,
      Arr.Arr.snd(Array<U32>, U32,
        Array.get.go(U32, xs1, Arr.Arr.pow2_u32(p), i,
          U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
      Arr.Arr.snd(Array<U32>, U32,
        Array.get.go(U32, xs2, Arr.Arr.pow2_u32(p), i,
          U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
      FT.tbl_at(G, C, n, Nat.add(base, U32.to_nat(i))),
      Equal.cong(Array<U32>, U32,
        x => Arr.Arr.snd(Array<U32>, U32,
               Array.get.go(U32, x, Arr.Arr.pow2_u32(p), i,
                 U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
        xs1, xs2, Equal.sym(Array<U32>, xs2, xs1, ex2)),
      h2)
  %ex1 : {Arr.Arr.snd(Array<U32>, U32,
            Array.get.go(U32, ANode{_, ys}, Arr.Arr.pow2_u32(1n+p), i, True{}))
          == FT.tbl_at(G, C, n, Nat.add(base, U32.to_nat(i))) : U32}
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    {Arr.Arr.snd(Array<U32>, U32,
       Array.swap.lo(U32, ys,
         Array.get.go(U32, xs1, _, i, U32.is_lt(i, U32.shr(_)))))
     == FT.tbl_at(G, C, n, Nat.add(base, U32.to_nat(i))) : U32}
  FT.tbl_get_lo(ys,
    Array.get.go(U32, xs1, Arr.Arr.pow2_u32(p), i,
      U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))),
    G, C, n, Nat.add(base, U32.to_nat(i)), h1)

def FT.tbl_tree_get_go_hi(+p: Nat, +base: Nat, -xs: Array<U32>,
    -ys: Array<U32>, +G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +n: Nat, +upto: Nat, +i: U32,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +eidx: {Nat.add(Nat.add(base, FT.pow2(p)),
              U32.to_nat(U32.sub(i, Arr.Arr.pow2_u32(p))))
            == Nat.add(base, U32.to_nat(i)) : Nat},
    +hys: FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto),
    d: &a1: Array<U32> -> &a2: Array<U32> ->
       {a1 == ys : Array<U32>} & {a2 == a1 : Array<U32>},
    ih: @ys2: Array<U32> ->
        FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys2, G, C, n, upto) ->
        {Arr.Arr.snd(Array<U32>, U32,
           Array.get.go(U32, ys2, Arr.Arr.pow2_u32(p),
             U32.sub(i, Arr.Arr.pow2_u32(p)),
             U32.is_lt(U32.sub(i, Arr.Arr.pow2_u32(p)),
               U32.shr(Arr.Arr.pow2_u32(p)))))
         == FT.tbl_at(G, C, n,
              Nat.add(Nat.add(base, FT.pow2(p)),
                U32.to_nat(U32.sub(i, Arr.Arr.pow2_u32(p))))) : U32}) ->
  {Arr.Arr.snd(Array<U32>, U32,
     Array.get.go(U32, ANode{xs, ys}, Arr.Arr.pow2_u32(1n+p), i, False{}))
   == FT.tbl_at(G, C, n, Nat.add(base, U32.to_nat(i))) : U32}:
  (ys1, d2) = d
  (ys2, pe) = d2
  (+ey1, +ey2) = pe
  +base2 = Nat.add(base, FT.pow2(p))
  +ip = U32.sub(i, Arr.Arr.pow2_u32(p))
  +hys2 = FT.tbl_tree_transport(p, base2, ys, ys2, G, C, n, upto,
            Equal.sym(Array<U32>, ys2, ys,
              Equal.trans(Array<U32>, ys2, ys1, ys, ey2, ey1)), hys)
  +h2 = ih(ys2, hys2)
  +h1 : {Arr.Arr.snd(Array<U32>, U32,
           Array.get.go(U32, ys1, Arr.Arr.pow2_u32(p), ip,
             U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))))
         == FT.tbl_at(G, C, n, Nat.add(base, U32.to_nat(i))) : U32} =
    Equal.trans(U32,
      Arr.Arr.snd(Array<U32>, U32,
        Array.get.go(U32, ys1, Arr.Arr.pow2_u32(p), ip,
          U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
      FT.tbl_at(G, C, n, Nat.add(base2, U32.to_nat(ip))),
      FT.tbl_at(G, C, n, Nat.add(base, U32.to_nat(i))),
      Equal.trans(U32,
        Arr.Arr.snd(Array<U32>, U32,
          Array.get.go(U32, ys1, Arr.Arr.pow2_u32(p), ip,
            U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
        Arr.Arr.snd(Array<U32>, U32,
          Array.get.go(U32, ys2, Arr.Arr.pow2_u32(p), ip,
            U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
        FT.tbl_at(G, C, n, Nat.add(base2, U32.to_nat(ip))),
        Equal.cong(Array<U32>, U32,
          y => Arr.Arr.snd(Array<U32>, U32,
                 Array.get.go(U32, y, Arr.Arr.pow2_u32(p), ip,
                   U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
          ys1, ys2, Equal.sym(Array<U32>, ys2, ys1, ey2)),
        h2),
      Equal.cong(Nat, U32, x => FT.tbl_at(G, C, n, x),
        Nat.add(base2, U32.to_nat(ip)), Nat.add(base, U32.to_nat(i)), eidx))
  %ey1 : {Arr.Arr.snd(Array<U32>, U32,
            Array.get.go(U32, ANode{xs, _}, Arr.Arr.pow2_u32(1n+p), i, False{}))
          == FT.tbl_at(G, C, n, Nat.add(base, U32.to_nat(i))) : U32}
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    {Arr.Arr.snd(Array<U32>, U32,
       Array.swap.hi(U32, xs,
         Array.get.go(U32, ys1, _, U32.sub(i, _),
           U32.is_lt(U32.sub(i, _), U32.shr(_)))))
     == FT.tbl_at(G, C, n, Nat.add(base, U32.to_nat(i))) : U32}
  FT.tbl_get_hi(xs,
    Array.get.go(U32, ys1, Arr.Arr.pow2_u32(p), ip,
      U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))),
    G, C, n, Nat.add(base, U32.to_nat(i)), h1)

def FT.tbl_tree_get_go(+d: Nat, +base: Nat, a: Array<U32>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat, +upto: Nat,
    +i: U32, z: Bool,
    +ez: {z == U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(d))) : Bool},
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.Arr.u32_zero_from(d, i) == True{} : Bool},
    +hin: {Nat.is_lt(Nat.add(base, U32.to_nat(i)), upto) == True{} : Bool},
    +ht: FT.TblTree(d, base, a, G, C, n, upto)) ->
  {Arr.Arr.snd(Array<U32>, U32,
     Array.get.go(U32, a, Arr.Arr.pow2_u32(d), i, z))
   == FT.tbl_at(G, C, n, Nat.add(base, U32.to_nat(i))) : U32}:
  match d:
    case 0n:
      match a:
        case ALeaf{+v}:
          +ei0 : {i == 0 : U32} = Arr.Arr.u32_eq_zero(i, zi)
          +eb : {Nat.add(base, U32.to_nat(i)) == base : Nat} =
            Equal.trans(Nat, Nat.add(base, U32.to_nat(i)), Nat.add(base, 0n),
              base,
              Equal.cong(U32, Nat, x => Nat.add(base, U32.to_nat(x)), i, 0, ei0),
              NatProof.NatPrf.add_zero(base))
          +hltb : {Nat.is_lt(base, upto) == True{} : Bool} =
            Equal.trans(Bool, Nat.is_lt(base, upto),
              Nat.is_lt(Nat.add(base, U32.to_nat(i)), upto), True{},
              Equal.cong(Nat, Bool, x => Nat.is_lt(x, upto), base,
                Nat.add(base, U32.to_nat(i)),
                Equal.sym(Nat, Nat.add(base, U32.to_nat(i)), base, eb)),
              hin)
          +eqv : {v == FT.tbl_at(G, C, n, base) : U32} =
            %hltb : Feedback.Bool.case(Data, _, {v == FT.tbl_at(G, C, n, base) : U32}, Unit)
            ht
          Equal.trans(U32, v, FT.tbl_at(G, C, n, base),
            FT.tbl_at(G, C, n, Nat.add(base, U32.to_nat(i))), eqv,
            Equal.cong(Nat, U32, x => FT.tbl_at(G, C, n, x), base,
              Nat.add(base, U32.to_nat(i)),
              Equal.sym(Nat, Nat.add(base, U32.to_nat(i)), base, eb)))
        case ANode{xs, ys}:
          Empty.absurd(
            {Arr.Arr.snd(Array<U32>, U32,
               Array.get.go(U32, ANode{xs, ys}, Arr.Arr.pow2_u32(0n), i, z))
             == FT.tbl_at(G, C, n, Nat.add(base, U32.to_nat(i))) : U32}, ht)
    case 1n++p:
      match a:
        case ALeaf{v}:
          Empty.absurd(
            {Arr.Arr.snd(Array<U32>, U32,
               Array.get.go(U32, ALeaf{v}, Arr.Arr.pow2_u32(1n+p), i, z))
             == FT.tbl_at(G, C, n, Nat.add(base, U32.to_nat(i))) : U32}, ht)
        case ANode{xs, ys}:
          match z:
            case True{}:
              +hxs = Arr.Arr.dpair_l(
                       FT.TblTree(p, base, xs, G, C, n, upto),
                       FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto),
                       ht)
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
              FT.tbl_tree_get_go_lo(p, base, xs, ys, G, C, n, upto, i, eshr,
                hxs, Arr.Arr.dup(U32, xs),
                xs2 => hxs2 =>
                  FT.tbl_tree_get_go(p, base, xs2, G, C, n, upto, i,
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, hin, hxs2))
            case False{}:
              +hys = Arr.Arr.dpair_r(
                       FT.TblTree(p, base, xs, G, C, n, upto),
                       FT.TblTree(p, Nat.add(base, FT.pow2(p)), ys, G, C, n, upto),
                       ht)
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
              +esub : {Nat.add(FT.pow2(p), U32.to_nat(ip)) == U32.to_nat(i) : Nat} =
                FT.u32_to_nat_sub_pow2(p, i, zi, plt, ige)
              +eidx : {Nat.add(Nat.add(base, FT.pow2(p)), U32.to_nat(ip))
                       == Nat.add(base, U32.to_nat(i)) : Nat} =
                Equal.trans(Nat,
                  Nat.add(Nat.add(base, FT.pow2(p)), U32.to_nat(ip)),
                  Nat.add(base, Nat.add(FT.pow2(p), U32.to_nat(ip))),
                  Nat.add(base, U32.to_nat(i)),
                  NatProof.NatPrf.add_assoc(base, FT.pow2(p), U32.to_nat(ip)),
                  Equal.cong(Nat, Nat, x => Nat.add(base, x),
                    Nat.add(FT.pow2(p), U32.to_nat(ip)), U32.to_nat(i), esub))
              +hin2 : {Nat.is_lt(Nat.add(Nat.add(base, FT.pow2(p)),
                         U32.to_nat(ip)), upto) == True{} : Bool} =
                Equal.trans(Bool,
                  Nat.is_lt(Nat.add(Nat.add(base, FT.pow2(p)), U32.to_nat(ip)),
                    upto),
                  Nat.is_lt(Nat.add(base, U32.to_nat(i)), upto), True{},
                  Equal.cong(Nat, Bool, x => Nat.is_lt(x, upto),
                    Nat.add(Nat.add(base, FT.pow2(p)), U32.to_nat(ip)),
                    Nat.add(base, U32.to_nat(i)), eidx),
                  hin)
              FT.tbl_tree_get_go_hi(p, base, xs, ys, G, C, n, upto, i, eshr,
                eidx, hys, Arr.Arr.dup(U32, ys),
                ys2 => hys2 =>
                  FT.tbl_tree_get_go(p, Nat.add(base, FT.pow2(p)), ys2,
                    G, C, n, upto, ip,
                    U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, hin2, hys2))

def FT.tbl_tree_get_dup2(+d: Nat, -tbl: Array<U32>, a1: Array<U32>,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat, +upto: Nat,
    +k: Nat,
    +ea1: {a1 == tbl : Array<U32>}, -a2: Array<U32>,
    +ea2: {a2 == a1 : Array<U32>},
    dp2: &b1: Array<U32> -> &b2: Array<U32> ->
         {b1 == a2 : Array<U32>} & {b2 == b1 : Array<U32>},
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hu: {Nat.is_le(upto, FT.pow2(d)) == True{} : Bool},
    +hk: {Nat.is_lt(k, upto) == True{} : Bool},
    +ht: FT.TblTree(d, 0n, tbl, G, C, n, upto)) ->
  {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, tbl, U32.from_nat(k)))
   == FT.tbl_at(G, C, n, k) : U32}:
  (b1, dp3) = dp2
  (b2, pe2) = dp3
  (+eb1, +eb2) = pe2
  +idx = U32.from_nat(k)
  +hk_pow : {Nat.is_lt(k, FT.pow2(d)) == True{} : Bool} =
    NatProof.Nat.is_lt_le_trans(k, upto, FT.pow2(d), hk, hu)
  +zi : {Arr.Arr.u32_zero_from(d, idx) == True{} : Bool} =
    FT.u32_zero_from_from_nat(d, k, hd, hk_pow)
  +ek : {U32.to_nat(idx) == k : Nat} = FT.u32_to_nat_from_nat(d, k, hd, hk_pow)
  +hin : {Nat.is_lt(U32.to_nat(idx), upto) == True{} : Bool} =
    Equal.trans(Bool, Nat.is_lt(U32.to_nat(idx), upto), Nat.is_lt(k, upto),
      True{},
      Equal.cong(Nat, Bool, x => Nat.is_lt(x, upto), U32.to_nat(idx), k, ek),
      hk)
  +ea_b1 : {b1 == a1 : Array<U32>} = Equal.trans(Array<U32>, b1, a2, a1, eb1, ea2)
  +ea_b2 : {b2 == a1 : Array<U32>} = Equal.trans(Array<U32>, b2, b1, a1, eb2, ea_b1)
  +ht1 = FT.tbl_tree_transport(d, 0n, tbl, a1, G, C, n, upto,
           Equal.sym(Array<U32>, a1, tbl, ea1), ht)
  +ht_b1 = FT.tbl_tree_transport(d, 0n, a1, b1, G, C, n, upto,
             Equal.sym(Array<U32>, b1, a1, ea_b1), ht1)
  +hdp_b1 = FT.tbl_tree_depth(d, 0n, b1, G, C, n, upto, ht_b1)
  +hdp_b2 = Arr.Arr.depth_transport(U32, d, b1, b2,
              Equal.sym(Array<U32>, b2, b1, eb2), hdp_b1)
  +em : {U32.and(idx, U32.sub(Arr.Arr.pow2_u32(d), 1)) == idx : U32} =
    Arr.Arr.u32_and_mask(d, idx, zi)
  +eg : {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, b2, idx))
         == Arr.Arr.snd(Array<U32>, U32,
              Array.get.go(U32, b2, Arr.Arr.pow2_u32(d), idx,
                U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))) : U32} =
    Equal.trans(U32,
      Arr.Arr.snd(Array<U32>, U32, Array.get(U32, b2, idx)),
      Arr.Arr.snd(Array<U32>, U32,
        Array.get.go(U32, b2, Arr.Arr.pow2_u32(d),
          U32.and(idx, U32.sub(Arr.Arr.pow2_u32(d), 1)),
          U32.is_lt(U32.and(idx, U32.sub(Arr.Arr.pow2_u32(d), 1)),
            U32.shr(Arr.Arr.pow2_u32(d))))),
      Arr.Arr.snd(Array<U32>, U32,
        Array.get.go(U32, b2, Arr.Arr.pow2_u32(d), idx,
          U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))),
      Arr.Arr.get_depth(U32, d, b2, idx, hdp_b2),
      Equal.cong(U32, U32,
        j => Arr.Arr.snd(Array<U32>, U32,
               Array.get.go(U32, b2, Arr.Arr.pow2_u32(d), j,
                 U32.is_lt(j, U32.shr(Arr.Arr.pow2_u32(d))))),
        U32.and(idx, U32.sub(Arr.Arr.pow2_u32(d), 1)), idx, em))
  +ego = FT.tbl_tree_get_go(d, 0n, a1, G, C, n, upto, idx,
           U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))), {==}, hd, zi, hin, ht1)
  %ea1 : {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, _, idx))
          == FT.tbl_at(G, C, n, k) : U32}
  %ea_b2 : {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, _, idx))
            == FT.tbl_at(G, C, n, k) : U32}
  Equal.trans(U32,
    Arr.Arr.snd(Array<U32>, U32, Array.get(U32, b2, idx)),
    Arr.Arr.snd(Array<U32>, U32,
      Array.get.go(U32, a1, Arr.Arr.pow2_u32(d), idx,
        U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))),
    FT.tbl_at(G, C, n, k),
    Equal.trans(U32,
      Arr.Arr.snd(Array<U32>, U32, Array.get(U32, b2, idx)),
      Arr.Arr.snd(Array<U32>, U32,
        Array.get.go(U32, b2, Arr.Arr.pow2_u32(d), idx,
          U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))),
      Arr.Arr.snd(Array<U32>, U32,
        Array.get.go(U32, a1, Arr.Arr.pow2_u32(d), idx,
          U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))),
      eg,
      Equal.cong(Array<U32>, U32,
        x => Arr.Arr.snd(Array<U32>, U32,
               Array.get.go(U32, x, Arr.Arr.pow2_u32(d), idx,
                 U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))),
        b2, a1, ea_b2)),
    Equal.trans(U32,
      Arr.Arr.snd(Array<U32>, U32,
        Array.get.go(U32, a1, Arr.Arr.pow2_u32(d), idx,
          U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))),
      FT.tbl_at(G, C, n, U32.to_nat(idx)),
      FT.tbl_at(G, C, n, k),
      ego,
      Equal.cong(Nat, U32, x => FT.tbl_at(G, C, n, x), U32.to_nat(idx), k, ek)))

def FT.tbl_tree_get_dup(+d: Nat, -tbl: Array<U32>, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n: Nat, +upto: Nat, +k: Nat,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hu: {Nat.is_le(upto, FT.pow2(d)) == True{} : Bool},
    +hk: {Nat.is_lt(k, upto) == True{} : Bool},
    +ht: FT.TblTree(d, 0n, tbl, G, C, n, upto),
    dp: &a1: Array<U32> -> &a2: Array<U32> ->
        {a1 == tbl : Array<U32>} & {a2 == a1 : Array<U32>}) ->
  {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, tbl, U32.from_nat(k)))
   == FT.tbl_at(G, C, n, k) : U32}:
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  FT.tbl_tree_get_dup2(d, tbl, a1, G, C, n, upto, k, ea1, a2, ea2,
    Arr.Arr.dup(U32, a2), hd, hu, hk, ht)

def FT.tbl_tree_get(+d: Nat, tbl: Array<U32>, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n: Nat, +upto: Nat, +k: Nat,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hu: {Nat.is_le(upto, FT.pow2(d)) == True{} : Bool},
    +hk: {Nat.is_lt(k, upto) == True{} : Bool},
    +ht: FT.TblTree(d, 0n, tbl, G, C, n, upto)) ->
  {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, tbl, U32.from_nat(k)))
   == FT.tbl_at(G, C, n, k) : U32}:
  FT.tbl_tree_get_dup(d, tbl, G, C, n, upto, k, hd, hu, hk, ht,
    Arr.Arr.dup(U32, tbl))

# ---------------------------------------------------------------------------
# Section 5: `all_len5`, `fill_tbl_row`, `fill_tbl_go`, and `FT.TblOk`
# ---------------------------------------------------------------------------

def FT.all_len5_go_head(+w: +List<Nat>, +t: +List<+List<Nat>>, ok: Bool,
    +eok: {ok == SolveFast.is_len5(w) : Bool},
    +h: {SolveFast.all_len5_go(w <> t, ok) == True{} : Bool}) ->
  {SolveFast.is_len5(w) == True{} : Bool}:
  match ok:
    case True{}:
      Equal.sym(Bool, True{}, SolveFast.is_len5(w), eok)
    case False{}:
      Empty.absurd({SolveFast.is_len5(w) == True{} : Bool},
        Logic.Proof.false_ne_true(h))

def FT.all_len5_go_tail(+w: +List<Nat>, +t: +List<+List<Nat>>, ok: Bool,
    +h: {SolveFast.all_len5_go(w <> t, ok) == True{} : Bool}) ->
  {SolveFast.all_len5(t) == True{} : Bool}:
  match ok:
    case True{}:
      h
    case False{}:
      Empty.absurd({SolveFast.all_len5(t) == True{} : Bool},
        Logic.Proof.false_ne_true(h))

def FT.all_len5_head(+w: +List<Nat>, +t: +List<+List<Nat>>,
    +h: {SolveFast.all_len5(w <> t) == True{} : Bool}) ->
  {SolveFast.is_len5(w) == True{} : Bool}:
  FT.all_len5_go_head(w, t, SolveFast.is_len5(w), {==}, h)

def FT.all_len5_tail(+w: +List<Nat>, +t: +List<+List<Nat>>,
    +h: {SolveFast.all_len5(w <> t) == True{} : Bool}) ->
  {SolveFast.all_len5(t) == True{} : Bool}:
  FT.all_len5_go_tail(w, t, SolveFast.is_len5(w), h)

def FT.nth_word_append(+pre: +List<+List<Nat>>, +w: +List<Nat>,
    +rest: +List<+List<Nat>>) ->
  {FT.nth_word(List.append(&2, +List<Nat>, pre, w <> rest),
     Groups.len_words(pre)) == w : +List<Nat>}:
  match pre:
    case Nil{}:
      {==}
    case Con{h, t}:
      FT.nth_word_append(t, w, rest)

def FT.len_words_append(+xs: +List<+List<Nat>>, +ys: +List<+List<Nat>>) ->
  {Groups.len_words(List.append(&2, +List<Nat>, xs, ys))
   == Nat.add(Groups.len_words(xs), Groups.len_words(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      Equal.cong(Nat, Nat, x => 1n+x,
        Groups.len_words(List.append(&2, +List<Nat>, t, ys)),
        Nat.add(Groups.len_words(t), Groups.len_words(ys)),
        FT.len_words_append(t, ys))

def FT.list_append_snoc(-A: Data, +xs: +List<A>, +x: A, +ys: +List<A>) ->
  {List.append(&2, A, List.append(&2, A, xs, x <> Nil{}), ys)
   == List.append(&2, A, xs, x <> ys) : +List<A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(+List<A>, +List<A>, l => h <> l,
        List.append(&2, A, List.append(&2, A, t, x <> Nil{}), ys),
        List.append(&2, A, t, x <> ys),
        FT.list_append_snoc(A, t, x, ys))

def FT.tbl_at_append_c(+cpre: +List<+List<Nat>>, +w: +List<Nat>,
    +crest: +List<+List<Nat>>, +G: +List<+List<Nat>>, +n: Nat, +j: Nat,
    +hj: {Nat.is_lt(j, Groups.len_words(G)) == True{} : Bool}) ->
  {FT.tbl_at(G, List.append(&2, +List<Nat>, cpre, w <> crest), n,
     Nat.add(Nat.mul(Groups.len_words(cpre), Groups.len_words(G)), j))
   == FT.fb_code_words(FT.nth_word(G, j), w) : U32}:
  match cpre:
    case Nil{}:
      FT.tbl_at_head(w, crest, G, n, j, hj)
    case Con{+ch, +ct}:
      +m : Nat = Groups.len_words(G)
      +idx : Nat = Nat.add(Nat.mul(Groups.len_words(ct), m), j)
      +ea : {Nat.add(Nat.add(m, Nat.mul(Groups.len_words(ct), m)), j)
             == Nat.add(m, idx) : Nat} =
        NatProof.NatPrf.add_assoc(m, Nat.mul(Groups.len_words(ct), m), j)
      +hf : {Nat.is_lt(Nat.add(m, idx), m) == False{} : Bool} =
        FT.nat_lt_add_false(m, idx)
      +esub : {Nat.sub(Nat.add(m, idx), m) == idx : Nat} =
        FT.nat_sub_add_l(m, idx)
      Equal.trans(U32,
        FT.tbl_at(G, List.append(&2, +List<Nat>, ch <> ct, w <> crest), n,
          Nat.add(Nat.mul(Groups.len_words(ch <> ct), m), j)),
        FT.tbl_at(G, List.append(&2, +List<Nat>, ch <> ct, w <> crest), n,
          Nat.add(m, idx)),
        FT.fb_code_words(FT.nth_word(G, j), w),
        Equal.cong(Nat, U32,
          x => FT.tbl_at(G, List.append(&2, +List<Nat>, ch <> ct, w <> crest),
                 n, x),
          Nat.add(Nat.mul(Groups.len_words(ch <> ct), m), j),
          Nat.add(m, idx), ea),
        Equal.trans(U32,
          FT.tbl_at(G, List.append(&2, +List<Nat>, ch <> ct, w <> crest), n,
            Nat.add(m, idx)),
          FT.tbl_at(G, List.append(&2, +List<Nat>, ct, w <> crest), n,
            Nat.sub(Nat.add(m, idx), m)),
          FT.fb_code_words(FT.nth_word(G, j), w),
          FT.tbl_at_tail(ch, List.append(&2, +List<Nat>, ct, w <> crest), G, n,
            Nat.add(m, idx), hf),
          Equal.trans(U32,
            FT.tbl_at(G, List.append(&2, +List<Nat>, ct, w <> crest), n,
              Nat.sub(Nat.add(m, idx), m)),
            FT.tbl_at(G, List.append(&2, +List<Nat>, ct, w <> crest), n, idx),
            FT.fb_code_words(FT.nth_word(G, j), w),
            Equal.cong(Nat, U32,
              x => FT.tbl_at(G, List.append(&2, +List<Nat>, ct, w <> crest),
                     n, x),
              Nat.sub(Nat.add(m, idx), m), idx, esub),
            FT.tbl_at_append_c(ct, w, crest, G, n, j, hj))))

# One slot of one candidate block. The guess `g0..g4` sits at position
# `|gpre|` of the guess list `gpre ++ (g0..g4) :: grest`, the candidate
# `a0..a4` at position `|cpre|` of the candidate list `cpre ++ (a0..a4) :: rest`,
# and the slot written by this step is `|cpre|*m + |gpre|`, where `m` is the
# number of guesses.
def FT.fill_tbl_col_step_dup(+d: Nat,
    +g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +a0: Nat, +a1: Nat, +a2: Nat, +a3: Nat, +a4: Nat,
    +gpre: +List<+List<Nat>>, +grest: +List<+List<Nat>>,
    +cpre: +List<+List<Nat>>, +rest: +List<+List<Nat>>,
    +m: Nat, +n: Nat, -tbl: Array<U32>, +code: U32,
    +em: {Groups.len_words(List.append(&2, +List<Nat>, gpre,
            (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> grest)) == m
          : Nat},
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hu_lt: {Nat.is_lt(Nat.add(Nat.mul(Groups.len_words(cpre), m),
               Groups.len_words(gpre)), FT.pow2(d)) == True{} : Bool},
    +ecode: {code == FT.tbl_at(
               List.append(&2, +List<Nat>, gpre,
                 (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> grest),
               List.append(&2, +List<Nat>, cpre,
                 (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> rest), n,
               Nat.add(Nat.mul(Groups.len_words(cpre), m),
                 Groups.len_words(gpre))) : U32},
    +ht: FT.TblTree(d, 0n, tbl,
           List.append(&2, +List<Nat>, gpre,
             (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> grest),
           List.append(&2, +List<Nat>, cpre,
             (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> rest), n,
           Nat.add(Nat.mul(Groups.len_words(cpre), m),
             Groups.len_words(gpre))),
    dp: &t1: Array<U32> -> &t2: Array<U32> ->
        {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>},
    rec: @tbl2: Array<U32> ->
         FT.TblTree(d, 0n, tbl2,
           List.append(&2, +List<Nat>, gpre,
             (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> grest),
           List.append(&2, +List<Nat>, cpre,
             (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> rest), n,
           Nat.add(Nat.mul(Groups.len_words(cpre), m),
             Nat.add(Groups.len_words(gpre), 1n))) ->
         FT.TblTree(d, 0n,
           SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, grest,
             U32.inc(U32.from_nat(
               Nat.add(Nat.mul(Groups.len_words(cpre), m),
                 Groups.len_words(gpre)))),
             tbl2),
           List.append(&2, +List<Nat>, gpre,
             (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> grest),
           List.append(&2, +List<Nat>, cpre,
             (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> rest), n,
           Nat.add(Nat.mul(Groups.len_words(cpre), m), m))) ->
  FT.TblTree(d, 0n,
    SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, grest,
      U32.inc(U32.from_nat(
        Nat.add(Nat.mul(Groups.len_words(cpre), m),
          Groups.len_words(gpre)))),
      Array.set(U32, tbl,
        U32.from_nat(Nat.add(Nat.mul(Groups.len_words(cpre), m),
          Groups.len_words(gpre))), code)),
    List.append(&2, +List<Nat>, gpre,
      (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> grest),
    List.append(&2, +List<Nat>, cpre,
      (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> rest), n,
    Nat.add(Nat.mul(Groups.len_words(cpre), m), m)):
  (t1, dp2) = dp
  (t2, pe2) = dp2
  (+et1, +et2) = pe2
  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
  +aw : +List<Nat> = a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))
  +Gfull : +List<+List<Nat>> = List.append(&2, +List<Nat>, gpre, gw <> grest)
  +Cfull : +List<+List<Nat>> = List.append(&2, +List<Nat>, cpre, aw <> rest)
  +base : Nat = Nat.mul(Groups.len_words(cpre), m)
  +idx : Nat = Nat.add(base, Groups.len_words(gpre))
  +ht_t1 = FT.tbl_tree_transport(d, 0n, tbl, t1, Gfull, Cfull, n, idx,
             Equal.sym(Array<U32>, t1, tbl, et1), ht)
  +ht1_t1 = FT.tbl_tree_set(d, t1, Gfull, Cfull, n, idx, code,
              hd, hu_lt, ecode, ht_t1)
  +ht1_t2 = FT.tbl_tree_transport(d, 0n,
              Array.set(U32, t1, U32.from_nat(idx), code),
              Array.set(U32, t2, U32.from_nat(idx), code),
              Gfull, Cfull, n, 1n+idx,
              Equal.cong(Array<U32>, Array<U32>,
                x => Array.set(U32, x, U32.from_nat(idx), code),
                t1, t2, Equal.sym(Array<U32>, t2, t1, et2)),
              ht1_t1)
  +eupto : {Nat.add(base, Nat.add(Groups.len_words(gpre), 1n))
            == 1n+idx : Nat} =
    Equal.trans(Nat,
      Nat.add(base, Nat.add(Groups.len_words(gpre), 1n)),
      Nat.add(Nat.add(base, Groups.len_words(gpre)), 1n),
      1n+idx,
      Equal.sym(Nat,
        Nat.add(Nat.add(base, Groups.len_words(gpre)), 1n),
        Nat.add(base, Nat.add(Groups.len_words(gpre), 1n)),
        NatProof.NatPrf.add_assoc(base, Groups.len_words(gpre), 1n)),
      NatProof.NatPrf.add_comm(idx, 1n))
  +ht1_c2 = FT.tbl_tree_transport_upto(d, 0n,
              Array.set(U32, t2, U32.from_nat(idx), code),
              Gfull, Cfull, n, 1n+idx,
              Nat.add(base, Nat.add(Groups.len_words(gpre), 1n)),
              Equal.sym(Nat,
                Nat.add(base, Nat.add(Groups.len_words(gpre), 1n)),
                1n+idx, eupto),
              ht1_t2)
  +hrec = rec(Array.set(U32, t2, U32.from_nat(idx), code), ht1_c2)
  +et2_tbl : {t2 == tbl : Array<U32>} =
    Equal.trans(Array<U32>, t2, t1, tbl, et2, et1)
  +eset : {Array.set(U32, t2, U32.from_nat(idx), code)
           == Array.set(U32, tbl, U32.from_nat(idx), code) : Array<U32>} =
    Equal.cong(Array<U32>, Array<U32>,
      x => Array.set(U32, x, U32.from_nat(idx), code), t2, tbl, et2_tbl)
  +efill : {SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, grest,
              U32.inc(U32.from_nat(idx)),
              Array.set(U32, t2, U32.from_nat(idx), code))
            == SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, grest,
                 U32.inc(U32.from_nat(idx)),
                 Array.set(U32, tbl, U32.from_nat(idx), code)) : Array<U32>} =
    Equal.cong(Array<U32>, Array<U32>,
      y => SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, grest,
             U32.inc(U32.from_nat(idx)), y),
      Array.set(U32, t2, U32.from_nat(idx), code),
      Array.set(U32, tbl, U32.from_nat(idx), code), eset)
  FT.tbl_tree_transport(d, 0n,
    SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, grest, U32.inc(U32.from_nat(idx)),
      Array.set(U32, t2, U32.from_nat(idx), code)),
    SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, grest, U32.inc(U32.from_nat(idx)),
      Array.set(U32, tbl, U32.from_nat(idx), code)),
    Gfull, Cfull, n, Nat.add(base, m), efill, hrec)

def FT.fill_tbl_col_ok(+grem: +List<+List<Nat>>, +gpre: +List<+List<Nat>>,
    +a0: Nat, +a1: Nat, +a2: Nat, +a3: Nat, +a4: Nat,
    +cpre: +List<+List<Nat>>, +rest: +List<+List<Nat>>,
    +m: Nat, +d: Nat, +n: Nat, tbl: Array<U32>,
    +em: {Groups.len_words(List.append(&2, +List<Nat>, gpre, grem)) == m : Nat},
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hbound: {Nat.is_le(Nat.add(Nat.mul(Groups.len_words(cpre), m), m),
                FT.pow2(d)) == True{} : Bool},
    +hg5: {SolveFast.all_len5(grem) == True{} : Bool},
    +ht: FT.TblTree(d, 0n, tbl,
           List.append(&2, +List<Nat>, gpre, grem),
           List.append(&2, +List<Nat>, cpre,
             (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> rest), n,
           Nat.add(Nat.mul(Groups.len_words(cpre), m),
             Groups.len_words(gpre)))) ->
  FT.TblTree(d, 0n,
    SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, grem,
      U32.from_nat(Nat.add(Nat.mul(Groups.len_words(cpre), m),
        Groups.len_words(gpre))),
      tbl),
    List.append(&2, +List<Nat>, gpre, grem),
    List.append(&2, +List<Nat>, cpre,
      (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> rest), n,
    Nat.add(Nat.mul(Groups.len_words(cpre), m), m)):
  match grem:
    case Nil{}:
      +aw : +List<Nat> = a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))
      +Gfull : +List<+List<Nat>> = List.append(&2, +List<Nat>, gpre, Nil{})
      +Cfull : +List<+List<Nat>> = List.append(&2, +List<Nat>, cpre, aw <> rest)
      +base : Nat = Nat.mul(Groups.len_words(cpre), m)
      +eleng : {Groups.len_words(gpre) == m : Nat} =
        Equal.trans(Nat, Groups.len_words(gpre),
          Nat.add(Groups.len_words(gpre), 0n), m,
          Equal.sym(Nat, Nat.add(Groups.len_words(gpre), 0n),
            Groups.len_words(gpre),
            NatProof.NatPrf.add_zero(Groups.len_words(gpre))),
          Equal.trans(Nat,
            Nat.add(Groups.len_words(gpre), 0n),
            Groups.len_words(List.append(&2, +List<Nat>, gpre, Nil{})),
            m,
            Equal.sym(Nat,
              Groups.len_words(List.append(&2, +List<Nat>, gpre, Nil{})),
              Nat.add(Groups.len_words(gpre), 0n),
              FT.len_words_append(gpre, Nil{})),
            em))
      FT.tbl_tree_transport_upto(d, 0n, tbl, Gfull, Cfull, n,
        Nat.add(base, Groups.len_words(gpre)), Nat.add(base, m),
        Equal.cong(Nat, Nat, x => Nat.add(base, x),
          Groups.len_words(gpre), m, eleng),
        ht)
    case Con{+g, +grest}:
      match g:
        case Nil{}:
          +hgw5 : {SolveFast.is_len5(Nil{}) == True{} : Bool} =
            FT.all_len5_head(Nil{}, grest, hg5)
          Empty.absurd(
            FT.TblTree(d, 0n, tbl,
              List.append(&2, +List<Nat>, gpre, Nil{} <> grest),
              List.append(&2, +List<Nat>, cpre,
                (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> rest), n,
              Nat.add(Nat.mul(Groups.len_words(cpre), m), m)),
            Logic.Proof.false_ne_true(hgw5))
        case Con{+g0, +t1}:
          match t1:
            case Nil{}:
              +hgw5 : {SolveFast.is_len5(g0 <> Nil{}) == True{} : Bool} =
                FT.all_len5_head(g0 <> Nil{}, grest, hg5)
              Empty.absurd(
                FT.TblTree(d, 0n, tbl,
                  List.append(&2, +List<Nat>, gpre, (g0 <> Nil{}) <> grest),
                  List.append(&2, +List<Nat>, cpre,
                    (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> rest), n,
                  Nat.add(Nat.mul(Groups.len_words(cpre), m), m)),
                Logic.Proof.false_ne_true(hgw5))
            case Con{+g1, +t2}:
              match t2:
                case Nil{}:
                  +hgw5 : {SolveFast.is_len5(g0 <> (g1 <> Nil{})) == True{} : Bool} =
                    FT.all_len5_head(g0 <> (g1 <> Nil{}), grest, hg5)
                  Empty.absurd(
                    FT.TblTree(d, 0n, tbl,
                      List.append(&2, +List<Nat>, gpre,
                        (g0 <> (g1 <> Nil{})) <> grest),
                      List.append(&2, +List<Nat>, cpre,
                        (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> rest),
                      n,
                      Nat.add(Nat.mul(Groups.len_words(cpre), m), m)),
                    Logic.Proof.false_ne_true(hgw5))
                case Con{+g2, +t3}:
                  match t3:
                    case Nil{}:
                      +hgw5 : {SolveFast.is_len5(g0 <> (g1 <> (g2 <> Nil{}))) == True{} : Bool} =
                        FT.all_len5_head(g0 <> (g1 <> (g2 <> Nil{})), grest, hg5)
                      Empty.absurd(
                        FT.TblTree(d, 0n, tbl,
                          List.append(&2, +List<Nat>, gpre,
                            (g0 <> (g1 <> (g2 <> Nil{}))) <> grest),
                          List.append(&2, +List<Nat>, cpre,
                            (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> rest),
                          n,
                          Nat.add(Nat.mul(Groups.len_words(cpre), m), m)),
                        Logic.Proof.false_ne_true(hgw5))
                    case Con{+g3, +t4}:
                      match t4:
                        case Nil{}:
                          +hgw5 : {SolveFast.is_len5(g0 <> (g1 <> (g2 <> (g3 <> Nil{})))) == True{} : Bool} =
                            FT.all_len5_head(g0 <> (g1 <> (g2 <> (g3 <> Nil{}))),
                              grest, hg5)
                          Empty.absurd(
                            FT.TblTree(d, 0n, tbl,
                              List.append(&2, +List<Nat>, gpre,
                                (g0 <> (g1 <> (g2 <> (g3 <> Nil{})))) <> grest),
                              List.append(&2, +List<Nat>, cpre,
                                (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> rest),
                              n,
                              Nat.add(Nat.mul(Groups.len_words(cpre), m), m)),
                            Logic.Proof.false_ne_true(hgw5))
                        case Con{+g4, +t5}:
                          match t5:
                            case Con{+g5, +t6}:
                              +gw6 : +List<Nat> =
                                g0 <> (g1 <> (g2 <> (g3 <> (g4 <> (g5 <> t6)))))
                              +hgw5 : {SolveFast.is_len5(gw6) == True{} : Bool} =
                                FT.all_len5_head(gw6, grest, hg5)
                              Empty.absurd(
                                FT.TblTree(d, 0n, tbl,
                                  List.append(&2, +List<Nat>, gpre, gw6 <> grest),
                                  List.append(&2, +List<Nat>, cpre,
                                    (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> rest),
                                  n,
                                  Nat.add(Nat.mul(Groups.len_words(cpre), m), m)),
                                Logic.Proof.false_ne_true(hgw5))
                            case Nil{}:
                              +gw : +List<Nat> =
                                g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
                              +aw : +List<Nat> =
                                a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))
                              +hgrest5 : {SolveFast.all_len5(grest) == True{} : Bool} =
                                FT.all_len5_tail(gw, grest, hg5)
                              +Gfull2 : +List<+List<Nat>> =
                                List.append(&2, +List<Nat>, gpre, gw <> grest)
                              +gpre2 : +List<+List<Nat>> =
                                List.append(&2, +List<Nat>, gpre, gw <> Nil{})
                              +Cfull : +List<+List<Nat>> =
                                List.append(&2, +List<Nat>, cpre, aw <> rest)
                              +egfull : {List.append(&2, +List<Nat>, gpre2, grest)
                                         == Gfull2 : +List<+List<Nat>>} =
                                FT.list_append_snoc(+List<Nat>, gpre, gw, grest)
                              +elen2 : {Groups.len_words(gpre2)
                                        == 1n+Groups.len_words(gpre) : Nat} =
                                Equal.trans(Nat, Groups.len_words(gpre2),
                                  Nat.add(Groups.len_words(gpre), 1n),
                                  1n+Groups.len_words(gpre),
                                  FT.len_words_append(gpre, gw <> Nil{}),
                                  NatProof.NatPrf.add_comm(Groups.len_words(gpre),
                                    1n))
                              +em2 : {Groups.len_words(
                                        List.append(&2, +List<Nat>, gpre2, grest))
                                      == m : Nat} =
                                Equal.trans(Nat,
                                  Groups.len_words(
                                    List.append(&2, +List<Nat>, gpre2, grest)),
                                  Groups.len_words(Gfull2), m,
                                  Equal.cong(+List<+List<Nat>>, Nat,
                                    x => Groups.len_words(x),
                                    List.append(&2, +List<Nat>, gpre2, grest),
                                    Gfull2, egfull),
                                  em)
                              +hle1 : {Nat.is_le(1n+Groups.len_words(gpre),
                                         Groups.len_words(gpre2))
                                        == True{} : Bool} =
                                Equal.trans(Bool,
                                  Nat.is_le(1n+Groups.len_words(gpre),
                                    Groups.len_words(gpre2)),
                                  Nat.is_le(1n+Groups.len_words(gpre),
                                    1n+Groups.len_words(gpre)),
                                  True{},
                                  Equal.cong(Nat, Bool,
                                    x => Nat.is_le(1n+Groups.len_words(gpre), x),
                                    Groups.len_words(gpre2),
                                    1n+Groups.len_words(gpre), elen2),
                                  NatProof.Nat.is_le_refl(1n+Groups.len_words(gpre)))
                              +hle2 : {Nat.is_le(Groups.len_words(gpre2),
                                         Groups.len_words(
                                           List.append(&2, +List<Nat>, gpre2,
                                             grest))) == True{} : Bool} =
                                Equal.trans(Bool,
                                  Nat.is_le(Groups.len_words(gpre2),
                                    Groups.len_words(
                                      List.append(&2, +List<Nat>, gpre2, grest))),
                                  Nat.is_le(Groups.len_words(gpre2),
                                    Nat.add(Groups.len_words(gpre2),
                                      Groups.len_words(grest))),
                                  True{},
                                  Equal.cong(Nat, Bool,
                                    x => Nat.is_le(Groups.len_words(gpre2), x),
                                    Groups.len_words(
                                      List.append(&2, +List<Nat>, gpre2, grest)),
                                    Nat.add(Groups.len_words(gpre2),
                                      Groups.len_words(grest)),
                                    FT.len_words_append(gpre2, grest)),
                                  FT.nat_le_add_l(Groups.len_words(gpre2),
                                    Groups.len_words(grest)))
                              +hle3 : {Nat.is_le(
                                         Groups.len_words(
                                           List.append(&2, +List<Nat>, gpre2,
                                             grest)), m) == True{} : Bool} =
                                Equal.trans(Bool,
                                  Nat.is_le(Groups.len_words(
                                    List.append(&2, +List<Nat>, gpre2, grest)), m),
                                  Nat.is_le(m, m),
                                  True{},
                                  Equal.cong(Nat, Bool, x => Nat.is_le(x, m),
                                    Groups.len_words(
                                      List.append(&2, +List<Nat>, gpre2, grest)),
                                    m, em2),
                                  NatProof.Nat.is_le_refl(m))
                              +hle : {Nat.is_le(1n+Groups.len_words(gpre), m)
                                      == True{} : Bool} =
                                NatProof.Nat.is_le_trans(
                                  1n+Groups.len_words(gpre),
                                  Groups.len_words(gpre2), m,
                                  hle1,
                                  NatProof.Nat.is_le_trans(
                                    Groups.len_words(gpre2),
                                    Groups.len_words(
                                      List.append(&2, +List<Nat>, gpre2, grest)),
                                    m, hle2, hle3))
                              +hgpre_lt : {Nat.is_lt(Groups.len_words(gpre), m)
                                           == True{} : Bool} =
                                NatProof.Nat.is_lt_le_trans(
                                  Groups.len_words(gpre),
                                  1n+Groups.len_words(gpre), m,
                                  NatProof.Nat.is_lt_succ_self(
                                    Groups.len_words(gpre)),
                                  hle)
                              +hj : {Nat.is_lt(Groups.len_words(gpre),
                                        Groups.len_words(Gfull2))
                                     == True{} : Bool} =
                                Equal.trans(Bool,
                                  Nat.is_lt(Groups.len_words(gpre),
                                    Groups.len_words(Gfull2)),
                                  Nat.is_lt(Groups.len_words(gpre), m),
                                  True{},
                                  Equal.cong(Nat, Bool,
                                    x => Nat.is_lt(Groups.len_words(gpre), x),
                                    Groups.len_words(Gfull2), m, em),
                                  hgpre_lt)
                              +base : Nat = Nat.mul(Groups.len_words(cpre), m)
                              +idx : Nat = Nat.add(base, Groups.len_words(gpre))
                              +hidx_lt : {Nat.is_lt(idx, Nat.add(base, m))
                                          == True{} : Bool} =
                                FT.nat_lt_add_l(Groups.len_words(gpre), m, base,
                                  hgpre_lt)
                              +hu_lt : {Nat.is_lt(idx, FT.pow2(d))
                                        == True{} : Bool} =
                                NatProof.Nat.is_lt_le_trans(idx,
                                  Nat.add(base, m), FT.pow2(d), hidx_lt, hbound)
                              +code = SolveFast.feedback_code5(
                                        g0, g1, g2, g3, g4, a0, a1, a2, a3, a4)
                              +ecode : {code == FT.tbl_at(Gfull2, Cfull, n, idx)
                                        : U32} =
                                Equal.trans(U32,
                                  code,
                                  FT.fb_code_words(gw, aw),
                                  FT.tbl_at(Gfull2, Cfull, n, idx),
                                  FF5.FF5.feedback_code5_eq(
                                    g0, g1, g2, g3, g4, a0, a1, a2, a3, a4),
                                  Equal.trans(U32,
                                    FT.fb_code_words(gw, aw),
                                    FT.fb_code_words(
                                      FT.nth_word(Gfull2,
                                        Groups.len_words(gpre)), aw),
                                    FT.tbl_at(Gfull2, Cfull, n, idx),
                                    Equal.cong(+List<Nat>, U32,
                                      x => FT.fb_code_words(x, aw),
                                      gw,
                                      FT.nth_word(Gfull2,
                                        Groups.len_words(gpre)),
                                      Equal.sym(+List<Nat>,
                                        FT.nth_word(Gfull2,
                                          Groups.len_words(gpre)), gw,
                                        FT.nth_word_append(gpre, gw, grest))),
                                    Equal.trans(U32,
                                      FT.fb_code_words(
                                        FT.nth_word(Gfull2,
                                          Groups.len_words(gpre)), aw),
                                      FT.tbl_at(Gfull2, Cfull, n,
                                        Nat.add(Nat.mul(Groups.len_words(cpre),
                                          Groups.len_words(Gfull2)),
                                          Groups.len_words(gpre))),
                                      FT.tbl_at(Gfull2, Cfull, n, idx),
                                      Equal.sym(U32,
                                        FT.tbl_at(Gfull2, Cfull, n,
                                          Nat.add(Nat.mul(
                                            Groups.len_words(cpre),
                                            Groups.len_words(Gfull2)),
                                            Groups.len_words(gpre))),
                                        FT.fb_code_words(
                                          FT.nth_word(Gfull2,
                                            Groups.len_words(gpre)), aw),
                                        FT.tbl_at_append_c(cpre, aw, rest,
                                          Gfull2, n, Groups.len_words(gpre),
                                          hj)),
                                      Equal.cong(Nat, U32,
                                        x => FT.tbl_at(Gfull2, Cfull, n,
                                          Nat.add(Nat.mul(
                                            Groups.len_words(cpre), x),
                                            Groups.len_words(gpre))),
                                        Groups.len_words(Gfull2), m, em))))
                              +ehb : {Nat.is_le(Nat.add(Nat.mul(
                                          Groups.len_words(cpre), m), m),
                                        FT.pow2(d)) == True{} : Bool} =
                                hbound
                              +eug : {Nat.add(Groups.len_words(gpre), 1n)
                                      == Groups.len_words(gpre2) : Nat} =
                                Equal.trans(Nat,
                                  Nat.add(Groups.len_words(gpre), 1n),
                                  1n+Groups.len_words(gpre),
                                  Groups.len_words(gpre2),
                                  NatProof.NatPrf.add_comm(
                                    Groups.len_words(gpre), 1n),
                                  Equal.sym(Nat, Groups.len_words(gpre2),
                                    1n+Groups.len_words(gpre), elen2))
                              +eu2 : {Nat.add(Nat.mul(
                                           Groups.len_words(cpre), m),
                                        Nat.add(Groups.len_words(gpre), 1n))
                                      == Nat.add(Nat.mul(
                                           Groups.len_words(cpre), m),
                                           Groups.len_words(gpre2)) : Nat} =
                                Equal.cong(Nat, Nat,
                                  x => Nat.add(Nat.mul(
                                    Groups.len_words(cpre), m), x),
                                  Nat.add(Groups.len_words(gpre), 1n),
                                  Groups.len_words(gpre2), eug)
                              +efinal : {1n+Nat.add(base,
                                            Groups.len_words(gpre))
                                         == Nat.add(base,
                                              Groups.len_words(gpre2)) : Nat} =
                                Equal.trans(Nat,
                                  1n+Nat.add(base, Groups.len_words(gpre)),
                                  Nat.add(Nat.add(base, Groups.len_words(gpre)),
                                    1n),
                                  Nat.add(base, Groups.len_words(gpre2)),
                                  NatProof.NatPrf.add_comm(1n,
                                    Nat.add(base, Groups.len_words(gpre))),
                                  Equal.trans(Nat,
                                    Nat.add(Nat.add(base,
                                      Groups.len_words(gpre)), 1n),
                                    Nat.add(base,
                                      Nat.add(Groups.len_words(gpre), 1n)),
                                    Nat.add(base, Groups.len_words(gpre2)),
                                    NatProof.NatPrf.add_assoc(base,
                                      Groups.len_words(gpre), 1n),
                                    eu2))
                              +einc : {U32.from_nat(Nat.add(base,
                                          Groups.len_words(gpre2)))
                                       == U32.inc(U32.from_nat(
                                            Nat.add(base,
                                              Groups.len_words(gpre)))) : U32} =
                                Equal.sym(U32,
                                  U32.from_nat(1n+Nat.add(base,
                                    Groups.len_words(gpre))),
                                  U32.from_nat(Nat.add(base,
                                    Groups.len_words(gpre2))),
                                  Equal.cong(Nat, U32, x => U32.from_nat(x),
                                    1n+Nat.add(base, Groups.len_words(gpre)),
                                    Nat.add(base, Groups.len_words(gpre2)),
                                    efinal))
                              FT.fill_tbl_col_step_dup(d, g0, g1, g2, g3, g4,
                                a0, a1, a2, a3, a4, gpre, grest, cpre, rest,
                                m, n, tbl, code, em, hd, hu_lt, ecode, ht,
                                Arr.Arr.dup(U32, tbl),
                                tbl2 => ht2 =>
                                  FT.tbl_tree_transport_gc(d,
                                    SolveFast.fill_tbl_col(a0, a1, a2, a3, a4,
                                      grest,
                                      U32.from_nat(Nat.add(base,
                                        Groups.len_words(gpre2))), tbl2),
                                    SolveFast.fill_tbl_col(a0, a1, a2, a3, a4,
                                      grest,
                                      U32.inc(U32.from_nat(Nat.add(base,
                                        Groups.len_words(gpre)))), tbl2),
                                    List.append(&2, +List<Nat>, gpre2, grest),
                                    Gfull2,
                                    Cfull, Cfull, n,
                                    Nat.add(base, m),
                                    Nat.add(base, m),
                                    Equal.cong(U32, Array<U32>,
                                      u => SolveFast.fill_tbl_col(a0, a1, a2,
                                             a3, a4, grest, u, tbl2),
                                      U32.from_nat(Nat.add(base,
                                        Groups.len_words(gpre2))),
                                      U32.inc(U32.from_nat(Nat.add(base,
                                        Groups.len_words(gpre)))), einc),
                                    egfull,
                                    {==}, {==},
                                    FT.fill_tbl_col_ok(grest, gpre2,
                                      a0, a1, a2, a3, a4, cpre, rest, m, d, n,
                                      tbl2, em2, hd, ehb, hgrest5,
                                      FT.tbl_tree_transport_gc(d, tbl2, tbl2,
                                        Gfull2,
                                        List.append(&2, +List<Nat>, gpre2,
                                          grest),
                                        Cfull, Cfull, n,
                                        Nat.add(base, Nat.add(
                                          Groups.len_words(gpre), 1n)),
                                        Nat.add(base,
                                          Groups.len_words(gpre2)),
                                        {==},
                                        Equal.sym(+List<+List<Nat>>,
                                          List.append(&2, +List<Nat>, gpre2,
                                            grest),
                                          Gfull2, egfull),
                                        {==}, eu2, ht2))))

def FT.mul_add_r(+a: Nat, +b: Nat, +c: Nat) ->
  {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++ap:
      Equal.trans(Nat,
        Nat.add(c, Nat.mul(Nat.add(ap, b), c)),
        Nat.add(c, Nat.add(Nat.mul(ap, c), Nat.mul(b, c))),
        Nat.add(Nat.add(c, Nat.mul(ap, c)), Nat.mul(b, c)),
        Equal.cong(Nat, Nat, x => Nat.add(c, x),
          Nat.mul(Nat.add(ap, b), c),
          Nat.add(Nat.mul(ap, c), Nat.mul(b, c)),
          FT.mul_add_r(ap, b, c)),
        Equal.sym(Nat,
          Nat.add(Nat.add(c, Nat.mul(ap, c)), Nat.mul(b, c)),
          Nat.add(c, Nat.add(Nat.mul(ap, c), Nat.mul(b, c))),
          NatProof.NatPrf.add_assoc(c, Nat.mul(ap, c), Nat.mul(b, c))))


def FT.all_len5_app_r(+xs: +List<+List<Nat>>, +ys: +List<+List<Nat>>,
    +h: {SolveFast.all_len5(List.append(&2, +List<Nat>, xs, ys))
         == True{} : Bool}) ->
  {SolveFast.all_len5(ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{w, +t}:
      +h1 : {SolveFast.all_len5(List.append(&2, +List<Nat>, t, ys))
             == True{} : Bool} =
        FT.all_len5_tail(w, List.append(&2, +List<Nat>, t, ys), h)
      FT.all_len5_app_r(t, ys, h1)

# One candidate block of the table: `a0..a4` at position `|cpre|` of the
# candidate list `Cfull`, with `m` guesses per block.
def FT.all_len5_of(+C1: +List<+List<Nat>>, +C2: +List<+List<Nat>>,
    +e: {C1 == C2 : +List<+List<Nat>>},
    +h: {SolveFast.all_len5(C2) == True{} : Bool}) ->
  {SolveFast.all_len5(C1) == True{} : Bool}:
  Equal.trans(Bool, SolveFast.all_len5(C1), SolveFast.all_len5(C2), True{},
    Equal.cong(+List<+List<Nat>>, Bool, x => SolveFast.all_len5(x), C1, C2, e),
    h)

def FT.fill_tbl_go_step_dup(+d: Nat,
    +a0: Nat, +a1: Nat, +a2: Nat, +a3: Nat, +a4: Nat,
    +cpre: +List<+List<Nat>>, +stop: +List<+List<Nat>>,
    +Cfull: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, +n: Nat, +m: Nat, -tbl: Array<U32>,
    +emG: {Groups.len_words(G) == m : Nat},
    +eC : {Cfull == List.append(&2, +List<Nat>, cpre,
             (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> stop)
           : +List<+List<Nat>>},
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hb_row: {Nat.is_le(Nat.add(Nat.mul(Groups.len_words(cpre), m), m),
                FT.pow2(d)) == True{} : Bool},
    +hg5: {SolveFast.all_len5(G) == True{} : Bool},
    +hc5: {SolveFast.all_len5(
            List.append(&2, +List<Nat>, cpre,
              (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> stop))
           == True{} : Bool},
    +ht: FT.TblTree(d, 0n, tbl, G, Cfull, n,
           Nat.mul(Groups.len_words(cpre), m)),
    dp: &t1: Array<U32> -> &t2: Array<U32> ->
        {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>},
    rec: @tbl2: Array<U32> ->
         FT.TblTree(d, 0n, tbl2, G, Cfull, n,
           Nat.mul(Groups.len_words(
             List.append(&2, +List<Nat>, cpre,
               (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> Nil{})), m)) ->
         FT.TblTree(d, 0n,
           SolveFast.fill_tbl_go(G, stop,
             U32.from_nat(Nat.mul(Groups.len_words(
               List.append(&2, +List<Nat>, cpre,
                 (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> Nil{})), m)),
             U32.from_nat(m), tbl2),
           G, Cfull, n, Nat.mul(n, m))) ->
  FT.TblTree(d, 0n,
    SolveFast.fill_tbl_go(G,
      (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) <> stop,
      U32.from_nat(Nat.mul(Groups.len_words(cpre), m)), U32.from_nat(m),
      tbl),
    G, Cfull, n, Nat.mul(n, m)):
  (t1, dp2) = dp
  (t2, pe2) = dp2
  (+et1, +et2) = pe2
  +aw : +List<Nat> = a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))
  +Cn : +List<+List<Nat>> =
    List.append(&2, +List<Nat>, cpre, aw <> stop)
  +cpre2 : +List<+List<Nat>> = List.append(&2, +List<Nat>, cpre, aw <> Nil{})
  +base : Nat = Nat.mul(Groups.len_words(cpre), m)
  +eC2 : {Cfull == Cn : +List<+List<Nat>>} =
    Equal.trans(+List<+List<Nat>>, Cfull, List.append(&2, +List<Nat>, cpre, aw <> stop),
      Cn, eC, {==})
  +ecfull : {List.append(&2, +List<Nat>, cpre2, stop) == Cn
             : +List<+List<Nat>>} =
    FT.list_append_snoc(+List<Nat>, cpre, aw, stop)
  +eci2 : {Groups.len_words(cpre2)
           == 1n+Groups.len_words(cpre) : Nat} =
    Equal.trans(Nat, Groups.len_words(cpre2),
      Nat.add(Groups.len_words(cpre), 1n), 1n+Groups.len_words(cpre),
      FT.len_words_append(cpre, aw <> Nil{}),
      NatProof.NatPrf.add_comm(Groups.len_words(cpre), 1n))
  +emul2 : {Nat.mul(Groups.len_words(cpre2), m)
            == Nat.add(Nat.mul(Groups.len_words(cpre), m), m) : Nat} =
    Equal.trans(Nat,
      Nat.mul(Groups.len_words(cpre2), m),
      Nat.add(m, Nat.mul(Groups.len_words(cpre), m)),
      Nat.add(Nat.mul(Groups.len_words(cpre), m), m),
      Equal.cong(Nat, Nat, x => Nat.mul(x, m),
        Groups.len_words(cpre2), 1n+Groups.len_words(cpre), eci2),
      NatProof.NatPrf.add_comm(m, Nat.mul(Groups.len_words(cpre), m)))
  +ht_t1 = FT.tbl_tree_transport(d, 0n, tbl, t1, G, Cfull, n, base,
             Equal.sym(Array<U32>, t1, tbl, et1), ht)
  +ht0 : FT.TblTree(d, 0n, t1, G, Cn, n,
            Nat.add(base, Groups.len_words(Nil{}))) =
    FT.tbl_tree_transport_gc(d, t1, t1, G, G, Cfull, Cn, n,
      Nat.add(base, Groups.len_words(Nil{})), Nat.add(base, Groups.len_words(Nil{})),
      {==}, {==}, eC2, {==},
      FT.tbl_tree_transport_upto(d, 0n, t1, G, Cfull, n,
        base, Nat.add(base, Groups.len_words(Nil{})),
        Equal.sym(Nat, Nat.add(base, Groups.len_words(Nil{})), base,
          NatProof.NatPrf.add_zero(base)), ht_t1))
  +ht1_t1 : FT.TblTree(d, 0n,
              SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, G,
                U32.from_nat(base), t1),
              G, Cn, n, Nat.add(base, m)) =
    %Equal.cong(Nat, U32, x => U32.from_nat(x),
       Nat.add(base, Groups.len_words(Nil{})), base,
       NatProof.NatPrf.add_zero(base)) :
      FT.TblTree(d, 0n,
        SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, G, _, t1),
        G, Cn, n, Nat.add(base, m))
    FT.fill_tbl_col_ok(G, Nil{}, a0, a1, a2, a3, a4, cpre, stop, m, d, n,
      t1, emG, hd, hb_row, hg5, ht0)
  +ht1_t2 = FT.tbl_tree_transport_gc(d,
              SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, G,
                U32.from_nat(base), t1),
              SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, G,
                U32.from_nat(base), t2),
              G, G, Cn, Cn, n, Nat.add(base, m), Nat.add(base, m),
              Equal.cong(Array<U32>, Array<U32>,
                x => SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, G,
                       U32.from_nat(base), x),
                t1, t2, Equal.sym(Array<U32>, t2, t1, et2)),
              {==}, {==}, {==},
              ht1_t1)
  +ht1_g2 : FT.TblTree(d, 0n,
              SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, G,
                U32.from_nat(base), t2),
              G, Cfull, n, Nat.mul(Groups.len_words(cpre2), m)) =
    FT.tbl_tree_transport_gc(d,
      SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, G, U32.from_nat(base), t2),
      SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, G, U32.from_nat(base), t2),
      G, G, Cn, Cfull, n, Nat.add(base, m), Nat.mul(Groups.len_words(cpre2), m),
      {==}, {==}, Equal.sym(+List<+List<Nat>>, Cfull, Cn, eC2),
      Equal.sym(Nat, Nat.mul(Groups.len_words(cpre2), m),
        Nat.add(base, m), emul2),
      ht1_t2)
  +hrec = rec(
            SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, G,
              U32.from_nat(base), t2),
            ht1_g2)
  +eu_add : {U32.from_nat(Nat.mul(Groups.len_words(cpre2), m))
             == U32.add(U32.from_nat(base), U32.from_nat(m)) : U32} =
    Equal.trans(U32,
      U32.from_nat(Nat.mul(Groups.len_words(cpre2), m)),
      U32.from_nat(Nat.add(base, m)),
      U32.add(U32.from_nat(base), U32.from_nat(m)),
      Equal.cong(Nat, U32, x => U32.from_nat(x),
        Nat.mul(Groups.len_words(cpre2), m), Nat.add(base, m), emul2),
      Equal.sym(U32,
        U32.add(U32.from_nat(base), U32.from_nat(m)),
        U32.from_nat(Nat.add(base, m)),
        FT.u32_add_from_nat(base, m)))
  %et1 :
    FT.TblTree(d, 0n,
      SolveFast.fill_tbl_go(G, stop,
        U32.add(U32.from_nat(base), U32.from_nat(m)),
        U32.from_nat(m),
        SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, G,
          U32.from_nat(base), _)),
      G, Cfull, n, Nat.mul(n, m))
  %et2 :
    FT.TblTree(d, 0n,
      SolveFast.fill_tbl_go(G, stop,
        U32.add(U32.from_nat(base), U32.from_nat(m)),
        U32.from_nat(m),
        SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, G,
          U32.from_nat(base), _)),
      G, Cfull, n, Nat.mul(n, m))
  %eu_add :
    FT.TblTree(d, 0n,
      SolveFast.fill_tbl_go(G, stop, _, U32.from_nat(m),
        SolveFast.fill_tbl_col(a0, a1, a2, a3, a4, G,
          U32.from_nat(base), t2)),
      G, Cfull, n, Nat.mul(n, m))
  hrec

def FT.fill_tbl_go_ok(+crem: +List<+List<Nat>>, +cpre: +List<+List<Nat>>,
    +Cfull: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, +d: Nat, +n: Nat, +m: Nat, tbl: Array<U32>,
    +emG: {Groups.len_words(G) == m : Nat},
    +eC : {Cfull == List.append(&2, +List<Nat>, cpre, crem)
           : +List<+List<Nat>>},
    +en: {Groups.len_words(Cfull) == n : Nat},
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hbound: {Nat.is_le(Nat.mul(m, n), FT.pow2(d)) == True{} : Bool},
    +hg5: {SolveFast.all_len5(G) == True{} : Bool},
    +hc5: {SolveFast.all_len5(Cfull) == True{} : Bool},
    +ht: FT.TblTree(d, 0n, tbl, G, Cfull, n,
           Nat.mul(Groups.len_words(cpre), m))) ->
  FT.TblTree(d, 0n,
    SolveFast.fill_tbl_go(G, crem,
      U32.from_nat(Nat.mul(Groups.len_words(cpre), m)), U32.from_nat(m), tbl),
    G, Cfull, n, Nat.mul(n, m)):
  match crem:
    case Nil{}:
      +ri : Nat = Groups.len_words(cpre)
      +elen : {Groups.len_words(Cfull) == ri : Nat} =
        Equal.trans(Nat, Groups.len_words(Cfull),
          Groups.len_words(List.append(&2, +List<Nat>, cpre, Nil{})),
          ri,
          Equal.cong(+List<+List<Nat>>, Nat, x => Groups.len_words(x),
            Cfull, List.append(&2, +List<Nat>, cpre, Nil{}), eC),
          Equal.trans(Nat,
            Groups.len_words(List.append(&2, +List<Nat>, cpre, Nil{})),
            Nat.add(ri, Groups.len_words(Nil{})),
            ri,
            FT.len_words_append(cpre, Nil{}),
            NatProof.NatPrf.add_zero(ri)))
      +eri_n : {ri == n : Nat} =
        Equal.trans(Nat, ri, Groups.len_words(Cfull), n,
          Equal.sym(Nat, Groups.len_words(Cfull), ri, elen), en)
      FT.tbl_tree_transport_upto(d, 0n, tbl, G, Cfull, n,
        Nat.mul(ri, m), Nat.mul(n, m),
        Equal.cong(Nat, Nat, x => Nat.mul(x, m), ri, n, eri_n),
        ht)
    case Con{+w, +rest}:
      match w:
        case Nil{}:
          +hc5w : {SolveFast.is_len5(Nil{}) == True{} : Bool} =
            FT.all_len5_head(Nil{}, rest,
              FT.all_len5_app_r(cpre, Nil{} <> rest,
                FT.all_len5_of(
                    List.append(&2, +List<Nat>, cpre, Nil{} <> rest), Cfull,
                Equal.sym(+List<+List<Nat>>, Cfull, 
                    List.append(&2, +List<Nat>, cpre, Nil{} <> rest), eC), hc5)))
          Empty.absurd(
            FT.TblTree(d, 0n, tbl, G, Cfull, n, Nat.mul(n, m)),
            Logic.Proof.false_ne_true(hc5w))
        case Con{+a0, +t1}:
          match t1:
            case Nil{}:
              +hc5aw : {SolveFast.all_len5((a0 <> Nil{}) <> rest) == True{} : Bool} =
                FT.all_len5_app_r(cpre, (a0 <> Nil{}) <> rest,
                  FT.all_len5_of(
                      List.append(&2, +List<Nat>, cpre, (a0 <> Nil{}) <> rest), Cfull,
                Equal.sym(+List<+List<Nat>>, Cfull, 
                      List.append(&2, +List<Nat>, cpre, (a0 <> Nil{}) <> rest), eC), hc5))
              +hc5w : {SolveFast.is_len5(a0 <> Nil{}) == True{} : Bool} =
                FT.all_len5_head(a0 <> Nil{}, rest, hc5aw)
              Empty.absurd(
                FT.TblTree(d, 0n, tbl, G, Cfull, n, Nat.mul(n, m)),
                Logic.Proof.false_ne_true(hc5w))
            case Con{+a1, +t2}:
              match t2:
                case Nil{}:
                  +hc5aw : {SolveFast.all_len5((a0 <> (a1 <> Nil{})) <> rest)
                            == True{} : Bool} =
                    FT.all_len5_app_r(cpre, (a0 <> (a1 <> Nil{})) <> rest,
                      FT.all_len5_of(
                          List.append(&2, +List<Nat>, cpre,
                            (a0 <> (a1 <> Nil{})) <> rest), Cfull,
                Equal.sym(+List<+List<Nat>>, Cfull, 
                          List.append(&2, +List<Nat>, cpre,
                            (a0 <> (a1 <> Nil{})) <> rest), eC), hc5))
                  +hc5w : {SolveFast.is_len5(a0 <> (a1 <> Nil{})) == True{} : Bool} =
                    FT.all_len5_head(a0 <> (a1 <> Nil{}), rest, hc5aw)
                  Empty.absurd(
                    FT.TblTree(d, 0n, tbl, G, Cfull, n, Nat.mul(n, m)),
                    Logic.Proof.false_ne_true(hc5w))
                case Con{+a2, +t3}:
                  match t3:
                    case Nil{}:
                      +hc5aw : {SolveFast.all_len5(
                                  (a0 <> (a1 <> (a2 <> Nil{}))) <> rest)
                                == True{} : Bool} =
                        FT.all_len5_app_r(cpre,
                          (a0 <> (a1 <> (a2 <> Nil{}))) <> rest,
                          FT.all_len5_of(
                              List.append(&2, +List<Nat>, cpre,
                                (a0 <> (a1 <> (a2 <> Nil{}))) <> rest), Cfull,
                Equal.sym(+List<+List<Nat>>, Cfull, 
                              List.append(&2, +List<Nat>, cpre,
                                (a0 <> (a1 <> (a2 <> Nil{}))) <> rest), eC), hc5))
                      +hc5w : {SolveFast.is_len5(a0 <> (a1 <> (a2 <> Nil{})))
                               == True{} : Bool} =
                        FT.all_len5_head(a0 <> (a1 <> (a2 <> Nil{})), rest,
                          hc5aw)
                      Empty.absurd(
                        FT.TblTree(d, 0n, tbl, G, Cfull, n, Nat.mul(n, m)),
                        Logic.Proof.false_ne_true(hc5w))
                    case Con{+a3, +t4}:
                      match t4:
                        case Nil{}:
                          +aw : +List<Nat> =
                            a0 <> (a1 <> (a2 <> (a3 <> Nil{})))
                          +hc5aw : {SolveFast.all_len5(aw <> rest)
                                    == True{} : Bool} =
                            FT.all_len5_app_r(cpre, aw <> rest,
                              FT.all_len5_of(
                                  List.append(&2, +List<Nat>, cpre,
                                    aw <> rest), Cfull,
                Equal.sym(+List<+List<Nat>>, Cfull, 
                                  List.append(&2, +List<Nat>, cpre,
                                    aw <> rest), eC), hc5))
                          +hc5w : {SolveFast.is_len5(aw) == True{} : Bool} =
                            FT.all_len5_head(aw, rest, hc5aw)
                          Empty.absurd(
                            FT.TblTree(d, 0n, tbl, G, Cfull, n,
                              Nat.mul(n, m)),
                            Logic.Proof.false_ne_true(hc5w))
                        case Con{+a4, +t5}:
                          match t5:
                            case Con{+a5, +t6}:
                              +aw6 : +List<Nat> =
                                a0 <> (a1 <> (a2 <> (a3 <> (a4 <> (a5 <> t6)))))
                              +hc5aw : {SolveFast.all_len5(aw6 <> rest)
                                        == True{} : Bool} =
                                FT.all_len5_app_r(cpre, aw6 <> rest,
                                  FT.all_len5_of(
                                      List.append(&2, +List<Nat>, cpre,
                                        aw6 <> rest), Cfull,
                Equal.sym(+List<+List<Nat>>, Cfull, 
                                      List.append(&2, +List<Nat>, cpre,
                                        aw6 <> rest), eC), hc5))
                              +hc5w : {SolveFast.is_len5(aw6) == True{} : Bool} =
                                FT.all_len5_head(aw6, rest, hc5aw)
                              Empty.absurd(
                                FT.TblTree(d, 0n, tbl, G, Cfull, n,
                                  Nat.mul(n, m)),
                                Logic.Proof.false_ne_true(hc5w))
                            case Nil{}:
                              +aw : +List<Nat> =
                                a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))
                              +hc5aw : {SolveFast.all_len5(aw <> rest)
                                        == True{} : Bool} =
                                FT.all_len5_app_r(cpre, aw <> rest,
                                  FT.all_len5_of(
                                      List.append(&2, +List<Nat>, cpre,
                                        aw <> rest), Cfull,
                Equal.sym(+List<+List<Nat>>, Cfull, 
                                      List.append(&2, +List<Nat>, cpre,
                                        aw <> rest), eC), hc5))
                              +hc5r : {SolveFast.all_len5(rest) == True{} : Bool} =
                                FT.all_len5_tail(aw, rest, hc5aw)
                              +cpre2 : +List<+List<Nat>> =
                                List.append(&2, +List<Nat>, cpre, aw <> Nil{})
                              +ecfull : {List.append(&2, +List<Nat>, cpre2, rest)
                                         == List.append(&2, +List<Nat>, cpre,
                                              aw <> rest)
                                         : +List<+List<Nat>>} =
                                FT.list_append_snoc(+List<Nat>, cpre, aw, rest)
                              +eci2 : {Groups.len_words(cpre2)
                                       == 1n+Groups.len_words(cpre) : Nat} =
                                Equal.trans(Nat, Groups.len_words(cpre2),
                                  Nat.add(Groups.len_words(cpre), 1n),
                                  1n+Groups.len_words(cpre),
                                  FT.len_words_append(cpre, aw <> Nil{}),
                                  NatProof.NatPrf.add_comm(
                                    Groups.len_words(cpre), 1n))
                              +hcle : {Nat.is_le(Nat.add(
                                          Groups.len_words(cpre), 1n), n)
                                       == True{} : Bool} =
                                Equal.trans(Bool,
                                  Nat.is_le(Nat.add(Groups.len_words(cpre), 1n),
                                    n),
                                  Nat.is_le(Nat.add(Groups.len_words(cpre), 1n),
                                    Nat.add(Groups.len_words(cpre),
                                      Groups.len_words(w <> rest))),
                                  True{},
                                  Equal.cong(Nat, Bool,
                                    x => Nat.is_le(
                                      Nat.add(Groups.len_words(cpre), 1n), x),
                                    n,
                                    Nat.add(Groups.len_words(cpre),
                                      Groups.len_words(w <> rest)),
                                    Equal.sym(Nat,
                                      Nat.add(Groups.len_words(cpre),
                                        Groups.len_words(w <> rest)),
                                      n,
                                      Equal.trans(Nat,
                                        Nat.add(Groups.len_words(cpre),
                                          Groups.len_words(w <> rest)),
                                        Groups.len_words(
                                          List.append(&2, +List<Nat>, cpre,
                                            w <> rest)),
                                        n,
                                        Equal.sym(Nat,
                                          Groups.len_words(
                                            List.append(&2, +List<Nat>, cpre,
                                              w <> rest)),
                                          Nat.add(Groups.len_words(cpre),
                                            Groups.len_words(w <> rest)),
                                          FT.len_words_append(cpre,
                                            w <> rest)),
                                        Equal.trans(Nat,
                                          Groups.len_words(
                                            List.append(&2, +List<Nat>, cpre,
                                              w <> rest)),
                                          Groups.len_words(Cfull), n,
                                          Equal.cong(+List<+List<Nat>>, Nat,
                                            x => Groups.len_words(x),
                                            List.append(&2, +List<Nat>, cpre,
                                              w <> rest),
                                            Cfull,
                                            Equal.sym(+List<+List<Nat>>, Cfull,
                                              List.append(&2, +List<Nat>, cpre,
                                                w <> rest), eC)),
                                          en)))),
                                  NatProof.Nat.is_le_add_l(1n,
                                    Nat.add(1n, Groups.len_words(rest)),
                                    Groups.len_words(cpre),
                                    FT.nat_le_add_l(1n, Groups.len_words(rest))))
                              +hmul : {Nat.is_le(Nat.mul(m,
                                            Nat.add(Groups.len_words(cpre), 1n)),
                                          Nat.mul(m, n)) == True{} : Bool} =
                                CBN.CB.is_le_mul_r(Nat.add(Groups.len_words(cpre), 1n),
                                  n, m, hcle)
                              +emul0 : {Nat.add(Nat.mul(
                                           Groups.len_words(cpre), m), m)
                                         == Nat.mul(m,
                                              Nat.add(Groups.len_words(cpre),
                                                1n)) : Nat} =
                                Equal.trans(Nat,
                                  Nat.add(Nat.mul(Groups.len_words(cpre), m), m),
                                  Nat.add(Nat.mul(m, Groups.len_words(cpre)), m),
                                  Nat.mul(m,
                                    Nat.add(Groups.len_words(cpre), 1n)),
                                  Equal.cong(Nat, Nat, x => Nat.add(x, m),
                                    Nat.mul(Groups.len_words(cpre), m),
                                    Nat.mul(m, Groups.len_words(cpre)),
                                    CBN.CB.mul_comm(Groups.len_words(cpre), m)),
                                  Equal.trans(Nat,
                                    Nat.add(Nat.mul(m, Groups.len_words(cpre)), m),
                                    Nat.add(Nat.mul(m, Groups.len_words(cpre)),
                                      Nat.mul(m, 1n)),
                                    Nat.mul(m,
                                      Nat.add(Groups.len_words(cpre), 1n)),
                                    Equal.cong(Nat, Nat,
                                      x => Nat.add(Nat.mul(m,
                                        Groups.len_words(cpre)), x),
                                      m, Nat.mul(m, 1n),
                                      Equal.sym(Nat, Nat.mul(m, 1n), m,
                                        CBN.CB.mul_one(m))),
                                    Equal.sym(Nat,
                                      Nat.mul(m,
                                        Nat.add(Groups.len_words(cpre), 1n)),
                                      Nat.add(Nat.mul(m,
                                        Groups.len_words(cpre)),
                                        Nat.mul(m, 1n)),
                                      CBN.CB.mul_add(m,
                                        Groups.len_words(cpre), 1n))))
                              +hb_row : {Nat.is_le(
                                           Nat.add(Nat.mul(
                                             Groups.len_words(cpre), m), m),
                                           FT.pow2(d)) == True{} : Bool} =
                                NatProof.Nat.is_le_trans(
                                  Nat.add(Nat.mul(Groups.len_words(cpre), m), m),
                                  Nat.mul(m, Nat.add(Groups.len_words(cpre), 1n)),
                                  FT.pow2(d),
                                  Equal.trans(Bool,
                                    Nat.is_le(
                                      Nat.add(Nat.mul(
                                        Groups.len_words(cpre), m), m),
                                      Nat.mul(m,
                                        Nat.add(Groups.len_words(cpre), 1n))),
                                    Nat.is_le(
                                      Nat.mul(m,
                                        Nat.add(Groups.len_words(cpre), 1n)),
                                      Nat.mul(m,
                                        Nat.add(Groups.len_words(cpre), 1n))),
                                    True{},
                                    Equal.cong(Nat, Bool,
                                      x => Nat.is_le(x,
                                        Nat.mul(m,
                                          Nat.add(Groups.len_words(cpre), 1n))),
                                      Nat.add(Nat.mul(
                                        Groups.len_words(cpre), m), m),
                                      Nat.mul(m,
                                        Nat.add(Groups.len_words(cpre), 1n)),
                                      emul0),
                                    NatProof.Nat.is_le_refl(
                                      Nat.mul(m,
                                        Nat.add(Groups.len_words(cpre), 1n)))),
                                  NatProof.Nat.is_le_trans(
                                    Nat.mul(m, Nat.add(Groups.len_words(cpre),
                                      1n)),
                                    Nat.mul(m, n),
                                    FT.pow2(d), hmul, hbound))
                              +eC2 : {Cfull == List.append(&2, +List<Nat>, cpre2,
                                         rest) : +List<+List<Nat>>} =
                                Equal.trans(+List<+List<Nat>>, Cfull,
                                  List.append(&2, +List<Nat>, cpre,
                                    aw <> rest),
                                  List.append(&2, +List<Nat>, cpre2, rest),
                                  eC,
                                  Equal.sym(+List<+List<Nat>>,
                                    List.append(&2, +List<Nat>, cpre2, rest),
                                    List.append(&2, +List<Nat>, cpre,
                                      aw <> rest),
                                    ecfull))
                              FT.fill_tbl_go_step_dup(d, a0, a1, a2, a3, a4,
                                cpre, rest, Cfull, G, n, m, tbl, emG, eC,
                                hd, hb_row, hg5,
                                FT.all_len5_of(
                                  List.append(&2, +List<Nat>, cpre, aw <> rest),
                                  Cfull,
                                  Equal.sym(+List<+List<Nat>>, Cfull,
                                    List.append(&2, +List<Nat>, cpre,
                                      aw <> rest), eC),
                                  hc5),
                                ht, Arr.Arr.dup(U32, tbl),
                                tbl2 => ht2 =>
                                  FT.fill_tbl_go_ok(rest, cpre2, Cfull, G, d, n,
                                    m, tbl2, emG, eC2, en, hd, hbound, hg5,
                                    hc5, ht2))

def FT.tbl_depth(+G: +List<+List<Nat>>, +n: Nat) -> Nat:
  Maybe.default(&1, Nat,
    SolveFast.depth_for(Nat.mul(Groups.len_words(G), n)), 0n)

def FT.TblOk(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
             tbl: Array<U32>) -> Data:
  +d = FT.tbl_depth(G, n)
  Arr.Arr.DPair<{Nat.is_lt(d, 32n) == True{} : Bool},
    Arr.Arr.DPair<
      {Nat.is_le(Nat.mul(Groups.len_words(G), n), FT.pow2(d)) == True{} : Bool},
      Arr.Arr.DPair<{Groups.len_words(C) == n : Nat},
        Arr.Arr.DPair<{SolveFast.all_len5(G) == True{} : Bool},
          Arr.Arr.DPair<{SolveFast.all_len5(C) == True{} : Bool},
            FT.TblTree(d, 0n, tbl, G, C, n,
              Nat.mul(Groups.len_words(G), n))>>>>>

def FT.tbl_ok_transport(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    -t1: Array<U32>, -t2: Array<U32>, +et: {t1 == t2 : Array<U32>},
    +h: FT.TblOk(G, C, n, t1)) -> FT.TblOk(G, C, n, t2):
  %et : FT.TblOk(G, C, n, _)
  h

def FT.mk_tbl_ok_go(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    +d: Nat,
    +ed: {SolveFast.depth_for(Nat.mul(Groups.len_words(G), n))
          == Some{d} : Maybe<Nat>},
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hb: {Nat.is_le(Nat.mul(Groups.len_words(G), n), FT.pow2(d))
          == True{} : Bool},
    +en: {Groups.len_words(C) == n : Nat},
    +hg5: {SolveFast.all_len5(G) == True{} : Bool},
    +hc5: {SolveFast.all_len5(C) == True{} : Bool}) ->
  FT.TblOk(G, C, n,
    SolveFast.fill_tbl_go(G, C, 0, U32.from_nat(Groups.len_words(G)),
      Array.new(U32, d, 0))):
  +m : Nat = Groups.len_words(G)
  +emG : {Groups.len_words(G) == m : Nat} = {==}
  +en0 : {Groups.len_words(List.append(&2, +List<Nat>, Nil{}, C)) == n : Nat} =
    en
  +ht0 = FT.fill_tbl_go_ok(C, Nil{}, C, G, d, n, m, Array.new(U32, d, 0), emG,
           {==}, en, hd, hb, hg5, hc5, FT.tbl_tree_new(d, 0n, G, C, n))
  +eupto : {Nat.mul(n, Groups.len_words(G))
            == Nat.mul(Groups.len_words(G), n) : Nat} =
    Equal.trans(Nat,
      Nat.mul(n, Groups.len_words(G)),
      Nat.mul(Groups.len_words(C), Groups.len_words(G)),
      Nat.mul(Groups.len_words(G), n),
      Equal.cong(Nat, Nat, x => Nat.mul(x, Groups.len_words(G)),
        n, Groups.len_words(C), Equal.sym(Nat, Groups.len_words(C), n, en)),
      Equal.trans(Nat,
        Nat.mul(Groups.len_words(C), Groups.len_words(G)),
        Nat.mul(Groups.len_words(G), Groups.len_words(C)),
        Nat.mul(Groups.len_words(G), n),
        CBN.CB.mul_comm(Groups.len_words(C), Groups.len_words(G)),
        Equal.cong(Nat, Nat, x => Nat.mul(Groups.len_words(G), x),
          Groups.len_words(C), n, en)))
  +ht = FT.tbl_tree_transport_upto(d, 0n,
          SolveFast.fill_tbl_go(G, C, 0, U32.from_nat(Groups.len_words(G)),
            Array.new(U32, d, 0)),
          G, C, n,
          Nat.mul(n, Groups.len_words(G)),
          Nat.mul(Groups.len_words(G), n),
          eupto,
          ht0)
  +edef : {FT.tbl_depth(G, n) == d : Nat} =
    Equal.cong(Maybe<Nat>, Nat, m => Maybe.default(&1, Nat, m, 0n),
      SolveFast.depth_for(Nat.mul(Groups.len_words(G), n)), Some{d}, ed)
  %Equal.sym(Nat, FT.tbl_depth(G, n), d, edef) :
    Arr.Arr.DPair<{Nat.is_lt(_, 32n) == True{} : Bool},
      Arr.Arr.DPair<
        {Nat.is_le(Nat.mul(Groups.len_words(G), n), FT.pow2(_)) == True{} : Bool},
        Arr.Arr.DPair<{Groups.len_words(C) == n : Nat},
          Arr.Arr.DPair<{SolveFast.all_len5(G) == True{} : Bool},
            Arr.Arr.DPair<{SolveFast.all_len5(C) == True{} : Bool},
              FT.TblTree(_, 0n,
                SolveFast.fill_tbl_go(G, C, 0, U32.from_nat(Groups.len_words(G)),
                  Array.new(U32, d, 0)),
                G, C, n, Nat.mul(Groups.len_words(G), n))>>>>>
  Arr.DPair{hd, Arr.DPair{hb, Arr.DPair{en, Arr.DPair{hg5, Arr.DPair{hc5, ht}}}}}

# ---------------------------------------------------------------------------
# Section 6: Pure `Bool` validity for `CWord`, guess rows, and `FT.tbl_lookup_eq`
# ---------------------------------------------------------------------------

def FT.has_col_go(+m: Nat, +C: +List<+List<Nat>>, +ci: U32, +w: +List<Nat>,
                  +cur: Nat) -> Bool:
  match C:
    case Nil{}:
      False{}
    case Con{h, rest}:
      Bool.or(
        Bool.and(U32.is_eq(ci, U32.from_nat(Nat.mul(cur, m))),
          Feedback.word_eq(w, h)),
        FT.has_col_go(m, rest, ci, w, 1n+cur))

def FT.has_grow_go(+G: +List<+List<Nat>>, +n: Nat, +row: U32,
                   +g: +List<Nat>, +cur: Nat) -> Bool:
  match G:
    case Nil{}:
      False{}
    case Con{h, rest}:
      Bool.or(
        Bool.and(U32.is_eq(row, U32.from_nat(cur)), Feedback.word_eq(g, h)),
        FT.has_grow_go(rest, n, row, g, 1n+cur))

def FT.gentry_ok_b(+G: +List<+List<Nat>>, +n: Nat, +row: U32,
                   +g: +List<Nat>) -> Bool:
  FT.has_grow_go(G, n, row, g, 0n)

def FT.cword_ok_b(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
                  cw: SolveFast.CWord) -> Bool:
  match cw:
    case SolveFast.CWord{ci, grow, +w}:
      Bool.and(FT.has_col_go(Groups.len_words(G), C, ci, w, 0n),
        FT.gentry_ok_b(G, n, grow, w))

def FT.cwords_ok_b(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
                   cws: +List<SolveFast.CWord>) -> Bool:
  match cws:
    case Nil{}:
      True{}
    case Con{cw, rest}:
      Bool.and(FT.cword_ok_b(G, C, n, cw), FT.cwords_ok_b(G, C, n, rest))

def FT.u32_is_eq_refl(+u: U32) -> {U32.is_eq(u, u) == True{} : Bool}:
  Arr.Arr.u32_is_eq_refl(u)

def FT.bool_or_elim_go(-R: Data, a: Bool, b: Bool,
    +h: {Bool.or(a, b) == True{} : Bool},
    kl: {a == True{} : Bool} -> R,
    kr: {b == True{} : Bool} -> R) -> R:
  match a:
    case True{}:
      kl({==})
    case False{}:
      kr(h)

# `cur` is a candidate index, and the block base of that candidate is `cur*m`,
# where `m` is the number of guesses.
type FT.ColWit<+m: Nat, +C: +List<+List<Nat>>, +ci: U32,
               +w: +List<Nat>> is Data:
  ColWit{col: Nat,
         eci: {ci == U32.from_nat(Nat.mul(col, m)) : U32},
         ew: {w == FT.nth_word(C, col) : +List<Nat>},
         hlt: {Nat.is_lt(col, Groups.len_words(C)) == True{} : Bool},
         h5: {SolveFast.is_len5(w) == True{} : Bool}}

def FT.col_wit_go(+m: Nat, +crem: +List<+List<Nat>>,
    +cpre: +List<+List<Nat>>, +ci: U32, +w: +List<Nat>,
    +h5: {SolveFast.all_len5(crem) == True{} : Bool},
    +h: {FT.has_col_go(m, crem, ci, w, Groups.len_words(cpre))
         == True{} : Bool}) ->
  FT.ColWit<m, List.append(&2, +List<Nat>, cpre, crem), ci, w>:
  match crem:
    case Nil{}:
      Empty.absurd(
        FT.ColWit<m, List.append(&2, +List<Nat>, cpre, Nil{}), ci, w>,
        Logic.Proof.false_ne_true(h))
    case Con{+ch, +ct}:
      +hh5 : {SolveFast.is_len5(ch) == True{} : Bool} =
        FT.all_len5_head(ch, ct, h5)
      +ht5 : {SolveFast.all_len5(ct) == True{} : Bool} =
        FT.all_len5_tail(ch, ct, h5)
      +cur : Nat = Groups.len_words(cpre)
      FT.bool_or_elim_go(
        FT.ColWit<m, List.append(&2, +List<Nat>, cpre, ch <> ct), ci, w>,
        Bool.and(U32.is_eq(ci, U32.from_nat(Nat.mul(cur, m))),
          Feedback.word_eq(w, ch)),
        FT.has_col_go(m, ct, ci, w, 1n+cur), h,
        +hl =>
          +eci : {ci == U32.from_nat(Nat.mul(cur, m)) : U32} =
            Arr.Arr.u32_is_eq_true(ci, U32.from_nat(Nat.mul(cur, m)),
              Logic.Proof.and_true_l(
                U32.is_eq(ci, U32.from_nat(Nat.mul(cur, m))),
                Feedback.word_eq(w, ch), hl))
          +ewh : {w == ch : +List<Nat>} =
            CoverList.Cover.word_eq_true(w, ch,
              Logic.Proof.and_true_r(
                U32.is_eq(ci, U32.from_nat(Nat.mul(cur, m))),
                Feedback.word_eq(w, ch), hl))
          +ew : {w == FT.nth_word(List.append(&2, +List<Nat>, cpre, ch <> ct),
                        cur) : +List<Nat>} =
            Equal.trans(+List<Nat>, w, ch,
              FT.nth_word(List.append(&2, +List<Nat>, cpre, ch <> ct), cur),
              ewh,
              Equal.sym(+List<Nat>,
                FT.nth_word(List.append(&2, +List<Nat>, cpre, ch <> ct), cur),
                ch, FT.nth_word_append(cpre, ch, ct)))
          +elen : {Groups.len_words(List.append(&2, +List<Nat>, cpre, ch <> ct))
                   == 1n+Nat.add(cur, Groups.len_words(ct)) : Nat} =
            Equal.trans(Nat,
              Groups.len_words(List.append(&2, +List<Nat>, cpre, ch <> ct)),
              Nat.add(cur, 1n+Groups.len_words(ct)),
              1n+Nat.add(cur, Groups.len_words(ct)),
              FT.len_words_append(cpre, ch <> ct),
              NatProof.NatPrf.add_succ(cur, Groups.len_words(ct)))
          +hlt : {Nat.is_lt(cur,
                    Groups.len_words(List.append(&2, +List<Nat>, cpre, ch <> ct)))
                  == True{} : Bool} =
            Equal.trans(Bool,
              Nat.is_lt(cur,
                Groups.len_words(List.append(&2, +List<Nat>, cpre, ch <> ct))),
              Nat.is_lt(cur, 1n+Nat.add(cur, Groups.len_words(ct))), True{},
              Equal.cong(Nat, Bool, x => Nat.is_lt(cur, x),
                Groups.len_words(List.append(&2, +List<Nat>, cpre, ch <> ct)),
                1n+Nat.add(cur, Groups.len_words(ct)), elen),
              NatProof.Nat.is_lt_succ_of_le(cur, Nat.add(cur, Groups.len_words(ct)),
                FT.nat_le_add_l(cur, Groups.len_words(ct))))
          +hw5 : {SolveFast.is_len5(w) == True{} : Bool} =
            Equal.trans(Bool, SolveFast.is_len5(w), SolveFast.is_len5(ch),
              True{},
              Equal.cong(+List<Nat>, Bool, x => SolveFast.is_len5(x), w, ch, ewh),
              hh5)
          ColWit{cur, eci, ew, hlt, hw5},
        +hr =>
          +cpre2 = List.append(&2, +List<Nat>, cpre, ch <> Nil{})
          +ec2 : {List.append(&2, +List<Nat>, cpre2, ct)
                  == List.append(&2, +List<Nat>, cpre, ch <> ct)
                  : +List<+List<Nat>>} =
            FT.list_append_snoc(+List<Nat>, cpre, ch, ct)
          +el2 : {Groups.len_words(cpre2) == 1n+cur : Nat} =
            Equal.trans(Nat, Groups.len_words(cpre2), Nat.add(cur, 1n), 1n+cur,
              FT.len_words_append(cpre, ch <> Nil{}),
              NatProof.NatPrf.add_comm(cur, 1n))
          +hr2 : {FT.has_col_go(m, ct, ci, w, Groups.len_words(cpre2))
                  == True{} : Bool} =
            Equal.trans(Bool,
              FT.has_col_go(m, ct, ci, w, Groups.len_words(cpre2)),
              FT.has_col_go(m, ct, ci, w, 1n+cur), True{},
              Equal.cong(Nat, Bool, x => FT.has_col_go(m, ct, ci, w, x),
                Groups.len_words(cpre2), 1n+cur, el2),
              hr)
          %ec2 : FT.ColWit<m, _, ci, w>
          FT.col_wit_go(m, ct, cpre2, ci, w, ht5, hr2))

# `|pre| < |pre ++ (w :: rest)|`: a prefix is shorter than the whole list.
def FT.len_append_cons_lt(+pre: +List<+List<Nat>>, +w: +List<Nat>,
    +rest: +List<+List<Nat>>) ->
  {Nat.is_lt(Groups.len_words(pre),
     Groups.len_words(List.append(&2, +List<Nat>, pre, w <> rest)))
   == True{} : Bool}:
  match pre:
    case Nil{}:
      NatProof.Nat.is_lt_succ_of_le(0n, Groups.len_words(rest),
        NatProof.Nat.is_le_zero_l(Groups.len_words(rest)))
    case Con{p, +pt}:
      FT.len_append_cons_lt(pt, w, rest)

# Slot `col*m + j` holds the feedback of guess `j` against candidate `col`.
def FT.tbl_at_block(+G: +List<+List<Nat>>, +n: Nat, C: +List<+List<Nat>>,
    col: Nat, +j: Nat,
    +hj: {Nat.is_lt(j, Groups.len_words(G)) == True{} : Bool},
    +hcol: {Nat.is_lt(col, Groups.len_words(C)) == True{} : Bool}) ->
  {FT.tbl_at(G, C, n, Nat.add(Nat.mul(col, Groups.len_words(G)), j))
   == FT.fb_code_words(FT.nth_word(G, j), FT.nth_word(C, col)) : U32}:
  match C:
    case Nil{}:
      +hf : {Nat.is_lt(col, 0n) == False{} : Bool} = FT.nat_lt_zero_false(col)
      Empty.absurd(
        {FT.tbl_at(G, Nil{}, n, Nat.add(Nat.mul(col, Groups.len_words(G)), j))
         == FT.fb_code_words(FT.nth_word(G, j),
              FT.nth_word(Nil{}, col)) : U32},
        Logic.Proof.false_ne_true(
          Equal.trans(Bool, False{}, Nat.is_lt(col, 0n), True{},
            Equal.sym(Bool, Nat.is_lt(col, 0n), False{}, hf), hcol)))
    case Con{h, +rest}:
      match col:
        case 0n:
          FT.tbl_at_head(h, rest, G, n, j, hj)
        case 1n++cp:
          +m : Nat = Groups.len_words(G)
          +hf : {Nat.is_lt(Nat.add(m, Nat.add(Nat.mul(cp, m), j)), m)
                 == False{} : Bool} =
            FT.nat_lt_add_false(m, Nat.add(Nat.mul(cp, m), j))
          +eidx : {Nat.add(Nat.mul(1n+cp, m), j)
                   == Nat.add(m, Nat.add(Nat.mul(cp, m), j)) : Nat} =
            NatProof.NatPrf.add_assoc(m, Nat.mul(cp, m), j)
          +esub : {Nat.sub(Nat.add(m, Nat.add(Nat.mul(cp, m), j)), m)
                   == Nat.add(Nat.mul(cp, m), j) : Nat} =
            FT.nat_sub_add_l(m, Nat.add(Nat.mul(cp, m), j))
          +ih : {FT.tbl_at(G, rest, n, Nat.add(Nat.mul(cp, m), j))
                 == FT.fb_code_words(FT.nth_word(G, j),
                      FT.nth_word(rest, cp)) : U32} =
            FT.tbl_at_block(G, n, rest, cp, j, hj, hcol)
          +eb : {FT.tbl_at(G, h <> rest, n,
                    Nat.add(Nat.mul(1n+cp, m), j))
                  == FT.tbl_at(G, rest, n,
                       Nat.add(Nat.mul(cp, m), j)) : U32} =
            Equal.trans(U32,
              FT.tbl_at(G, h <> rest, n, Nat.add(Nat.mul(1n+cp, m), j)),
              FT.tbl_at(G, h <> rest, n,
                Nat.add(m, Nat.add(Nat.mul(cp, m), j))),
              FT.tbl_at(G, rest, n, Nat.add(Nat.mul(cp, m), j)),
              Equal.cong(Nat, U32, x => FT.tbl_at(G, h <> rest, n, x),
                Nat.add(Nat.mul(1n+cp, m), j),
                Nat.add(m, Nat.add(Nat.mul(cp, m), j)), eidx),
              Equal.trans(U32,
                FT.tbl_at(G, h <> rest, n,
                  Nat.add(m, Nat.add(Nat.mul(cp, m), j))),
                FT.tbl_at(G, rest, n,
                  Nat.sub(Nat.add(m, Nat.add(Nat.mul(cp, m), j)), m)),
                FT.tbl_at(G, rest, n, Nat.add(Nat.mul(cp, m), j)),
                FT.tbl_at_tail(h, rest, G, n,
                  Nat.add(m, Nat.add(Nat.mul(cp, m), j)), hf),
                Equal.cong(Nat, U32, x => FT.tbl_at(G, rest, n, x),
                  Nat.sub(Nat.add(m, Nat.add(Nat.mul(cp, m), j)), m),
                  Nat.add(Nat.mul(cp, m), j), esub)))
          Equal.trans(U32,
            FT.tbl_at(G, h <> rest, n, Nat.add(Nat.mul(1n+cp, m), j)),
            FT.tbl_at(G, rest, n, Nat.add(Nat.mul(cp, m), j)),
            FT.fb_code_words(FT.nth_word(G, j), FT.nth_word(rest, cp)),
            eb,
            ih)

# Extract guess-row witness `(idx, row == from_nat(idx), the slot at
# `idx + col*m` holds the code of `g` against `nth_word(C, col)`, is_len5(g))`.
type FT.RowWit<+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
               +row: U32, +g: +List<Nat>, +col: Nat> is Data:
  RowWit{idx: Nat,
         erow: {row == U32.from_nat(idx) : U32},
         hlt: {Nat.is_lt(Nat.add(Nat.mul(col, Groups.len_words(G)), idx),
                 Nat.mul(Groups.len_words(G), n)) == True{} : Bool},
         etbl: {FT.tbl_at(G, C, n,
                  Nat.add(Nat.mul(col, Groups.len_words(G)), idx))
                == FT.fb_code_words(g, FT.nth_word(C, col)) : U32},
         h5: {SolveFast.is_len5(g) == True{} : Bool}}

def FT.row_wit_go(+grem: +List<+List<Nat>>, +gpre: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n: Nat, +row: U32, +g: +List<Nat>, +col: Nat,
    +hcol: {Nat.is_lt(col, n) == True{} : Bool},
    +hcolc: {Nat.is_lt(col, Groups.len_words(C)) == True{} : Bool},
    +h5: {SolveFast.all_len5(grem) == True{} : Bool},
    +h: {FT.has_grow_go(grem, n, row, g, Groups.len_words(gpre))
         == True{} : Bool}) ->
  FT.RowWit<List.append(&2, +List<Nat>, gpre, grem), C, n, row, g, col>:
  match grem:
    case Nil{}:
      Empty.absurd(
        FT.RowWit<List.append(&2, +List<Nat>, gpre, Nil{}), C, n, row, g, col>,
        Logic.Proof.false_ne_true(h))
    case Con{+gh, +gt}:
      +hh5 : {SolveFast.is_len5(gh) == True{} : Bool} =
        FT.all_len5_head(gh, gt, h5)
      +ht5 : {SolveFast.all_len5(gt) == True{} : Bool} =
        FT.all_len5_tail(gh, gt, h5)
      +ri : Nat = Groups.len_words(gpre)
      FT.bool_or_elim_go(
        FT.RowWit<List.append(&2, +List<Nat>, gpre, gh <> gt), C, n, row, g,
          col>,
        Bool.and(U32.is_eq(row, U32.from_nat(ri)), Feedback.word_eq(g, gh)),
        FT.has_grow_go(gt, n, row, g, 1n+ri), h,
        +hl =>
          +erow : {row == U32.from_nat(ri) : U32} =
            Arr.Arr.u32_is_eq_true(row, U32.from_nat(ri),
              Logic.Proof.and_true_l(U32.is_eq(row, U32.from_nat(ri)),
                Feedback.word_eq(g, gh), hl))
          +egh : {g == gh : +List<Nat>} =
            CoverList.Cover.word_eq_true(g, gh,
              Logic.Proof.and_true_r(U32.is_eq(row, U32.from_nat(ri)),
                Feedback.word_eq(g, gh), hl))
          +Gfull = List.append(&2, +List<Nat>, gpre, gh <> gt)
          +hcur : {Nat.is_lt(ri, Groups.len_words(Gfull)) == True{} : Bool} =
            FT.len_append_cons_lt(gpre, gh, gt)
          +hstep : {Nat.is_lt(
                      Nat.add(Nat.mul(col, Groups.len_words(Gfull)), ri),
                      Nat.add(Nat.mul(col, Groups.len_words(Gfull)),
                        Groups.len_words(Gfull))) == True{} : Bool} =
            FT.nat_lt_add_l(ri, Groups.len_words(Gfull),
              Nat.mul(col, Groups.len_words(Gfull)), hcur)
          +eone : {Nat.add(Nat.mul(col, Groups.len_words(Gfull)),
                     Groups.len_words(Gfull))
                   == Nat.mul(1n+col, Groups.len_words(Gfull)) : Nat} =
            NatProof.NatPrf.add_comm(Nat.mul(col, Groups.len_words(Gfull)),
              Groups.len_words(Gfull))
          +hsucc : {Nat.is_le(1n+col, n) == True{} : Bool} =
            FT.nat_le_succ_of_lt(col, n, hcol)
          +hmul : {Nat.is_le(Nat.mul(1n+col, Groups.len_words(Gfull)),
                     Nat.mul(n, Groups.len_words(Gfull))) == True{} : Bool} =
            CBN.CB.is_le_mul_l(1n+col, n, Groups.len_words(Gfull), hsucc)
          +hlt0 : {Nat.is_lt(
                     Nat.add(Nat.mul(col, Groups.len_words(Gfull)), ri),
                     Nat.mul(1n+col, Groups.len_words(Gfull)))
                   == True{} : Bool} =
            Equal.trans(Bool,
              Nat.is_lt(Nat.add(Nat.mul(col, Groups.len_words(Gfull)), ri),
                Nat.mul(1n+col, Groups.len_words(Gfull))),
              Nat.is_lt(Nat.add(Nat.mul(col, Groups.len_words(Gfull)), ri),
                Nat.add(Nat.mul(col, Groups.len_words(Gfull)),
                  Groups.len_words(Gfull))), True{},
              Equal.cong(Nat, Bool,
                x => Nat.is_lt(
                  Nat.add(Nat.mul(col, Groups.len_words(Gfull)), ri), x),
                Nat.mul(1n+col, Groups.len_words(Gfull)),
                Nat.add(Nat.mul(col, Groups.len_words(Gfull)),
                  Groups.len_words(Gfull)),
                Equal.sym(Nat,
                  Nat.add(Nat.mul(col, Groups.len_words(Gfull)),
                    Groups.len_words(Gfull)),
                  Nat.mul(1n+col, Groups.len_words(Gfull)), eone)),
              hstep)
          +hlt : {Nat.is_lt(
                    Nat.add(Nat.mul(col, Groups.len_words(Gfull)), ri),
                    Nat.mul(Groups.len_words(Gfull), n)) == True{} : Bool} =
            Equal.trans(Bool,
              Nat.is_lt(Nat.add(Nat.mul(col, Groups.len_words(Gfull)), ri),
                Nat.mul(Groups.len_words(Gfull), n)),
              Nat.is_lt(Nat.add(Nat.mul(col, Groups.len_words(Gfull)), ri),
                Nat.mul(n, Groups.len_words(Gfull))), True{},
              Equal.cong(Nat, Bool,
                x => Nat.is_lt(
                  Nat.add(Nat.mul(col, Groups.len_words(Gfull)), ri), x),
                Nat.mul(Groups.len_words(Gfull), n),
                Nat.mul(n, Groups.len_words(Gfull)),
                CBN.CB.mul_comm(Groups.len_words(Gfull), n)),
              NatProof.Nat.is_lt_le_trans(
                Nat.add(Nat.mul(col, Groups.len_words(Gfull)), ri),
                Nat.mul(1n+col, Groups.len_words(Gfull)),
                Nat.mul(n, Groups.len_words(Gfull)), hlt0, hmul))
          +enw : {FT.nth_word(Gfull, ri) == gh : +List<Nat>} =
            FT.nth_word_append(gpre, gh, gt)
          +efb1 : {FT.fb_code_words(FT.nth_word(Gfull, ri),
                     FT.nth_word(C, col))
                   == FT.fb_code_words(gh, FT.nth_word(C, col)) : U32} =
            Equal.cong(+List<Nat>, U32,
              x => FT.fb_code_words(x, FT.nth_word(C, col)),
              FT.nth_word(Gfull, ri), gh, enw)
          +efb2 : {FT.fb_code_words(gh, FT.nth_word(C, col))
                   == FT.fb_code_words(g, FT.nth_word(C, col)) : U32} =
            Equal.cong(+List<Nat>, U32,
              x => FT.fb_code_words(x, FT.nth_word(C, col)),
              gh, g, Equal.sym(+List<Nat>, g, gh, egh))
          +etbl : {FT.tbl_at(Gfull, C, n,
                     Nat.add(Nat.mul(col, Groups.len_words(Gfull)), ri))
                   == FT.fb_code_words(g, FT.nth_word(C, col)) : U32} =
            Equal.trans(U32,
              FT.tbl_at(Gfull, C, n,
                Nat.add(Nat.mul(col, Groups.len_words(Gfull)), ri)),
              FT.fb_code_words(gh, FT.nth_word(C, col)),
              FT.fb_code_words(g, FT.nth_word(C, col)),
              Equal.trans(U32,
                FT.tbl_at(Gfull, C, n,
                  Nat.add(Nat.mul(col, Groups.len_words(Gfull)), ri)),
                FT.fb_code_words(FT.nth_word(Gfull, ri),
                  FT.nth_word(C, col)),
                FT.fb_code_words(gh, FT.nth_word(C, col)),
                FT.tbl_at_block(Gfull, n, C, col, ri, hcur, hcolc),
                efb1),
              efb2)
          +hg5 : {SolveFast.is_len5(g) == True{} : Bool} =
            Equal.trans(Bool, SolveFast.is_len5(g), SolveFast.is_len5(gh),
              True{},
              Equal.cong(+List<Nat>, Bool, x => SolveFast.is_len5(x), g, gh, egh),
              hh5)
          RowWit{ri, erow, hlt, etbl, hg5},
        +hr =>
          +gpre2 = List.append(&2, +List<Nat>, gpre, gh <> Nil{})
          +eg2 : {List.append(&2, +List<Nat>, gpre2, gt)
                  == List.append(&2, +List<Nat>, gpre, gh <> gt)
                  : +List<+List<Nat>>} =
            FT.list_append_snoc(+List<Nat>, gpre, gh, gt)
          +el2 : {Groups.len_words(gpre2) == 1n+ri : Nat} =
            Equal.trans(Nat, Groups.len_words(gpre2), Nat.add(ri, 1n), 1n+ri,
              FT.len_words_append(gpre, gh <> Nil{}),
              NatProof.NatPrf.add_comm(ri, 1n))
          +hr2 : {FT.has_grow_go(gt, n, row, g, Groups.len_words(gpre2))
                  == True{} : Bool} =
            Equal.trans(Bool,
              FT.has_grow_go(gt, n, row, g, Groups.len_words(gpre2)),
              FT.has_grow_go(gt, n, row, g, 1n+ri), True{},
              Equal.cong(Nat, Bool, x => FT.has_grow_go(gt, n, row, g, x),
                Groups.len_words(gpre2), 1n+ri, el2),
              hr)
          %eg2 : FT.RowWit<_, C, n, row, g, col>
          FT.row_wit_go(gt, gpre2, C, n, row, g, col, hcol, hcolc, ht5, hr2))

# Main table lookup theorem: returns exact feedback code plus length-5 witnesses.
def FT.tbl_lookup_use_row(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    +d: Nat, +upto: Nat, +row: U32, +g: +List<Nat>, +ci: U32, +w: +List<Nat>,
    tbl: Array<U32>,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hb: {Nat.is_le(upto, FT.pow2(d)) == True{} : Bool},
    +ht: FT.TblTree(d, 0n, tbl, G, C, n, upto),
    +eupto: {upto == Nat.mul(Groups.len_words(G), n) : Nat},
    +col: Nat,
    +eci: {ci == U32.from_nat(Nat.mul(col, Groups.len_words(G))) : U32},
    +ew: {w == FT.nth_word(C, col) : +List<Nat>},
    +hw5: {SolveFast.is_len5(w) == True{} : Bool},
    rwit: FT.RowWit<G, C, n, row, g, col>) ->
  Arr.Arr.DPair<
    {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, tbl, U32.add(row, ci)))
     == FT.fb_code_words(g, w) : U32},
    Arr.Arr.DPair<{SolveFast.is_len5(g) == True{} : Bool},
                  {SolveFast.is_len5(w) == True{} : Bool}>>:
  match rwit:
    case RowWit{+idx, +erow, +hlt, +etbl, +hg5}:
      +m : Nat = Groups.len_words(G)
      +k : Nat = Nat.add(Nat.mul(col, m), idx)
      +eadd : {U32.add(row, ci) == U32.from_nat(k) : U32} =
        Equal.trans(U32,
          U32.add(row, ci),
          U32.add(U32.from_nat(idx), U32.from_nat(Nat.mul(col, m))),
          U32.from_nat(k),
          Equal.trans(U32,
            U32.add(row, ci),
            U32.add(U32.from_nat(idx), ci),
            U32.add(U32.from_nat(idx), U32.from_nat(Nat.mul(col, m))),
            Equal.cong(U32, U32, x => U32.add(x, ci), row, U32.from_nat(idx),
              erow),
            Equal.cong(U32, U32, y => U32.add(U32.from_nat(idx), y), ci,
              U32.from_nat(Nat.mul(col, m)), eci)),
          Equal.trans(U32,
            U32.add(U32.from_nat(idx), U32.from_nat(Nat.mul(col, m))),
            U32.from_nat(Nat.add(idx, Nat.mul(col, m))),
            U32.from_nat(k),
            FT.u32_add_from_nat(idx, Nat.mul(col, m)),
            Equal.cong(Nat, U32, x => U32.from_nat(x),
              Nat.add(idx, Nat.mul(col, m)), k,
              NatProof.NatPrf.add_comm(idx, Nat.mul(col, m)))))
      +hk_lt : {Nat.is_lt(k, upto) == True{} : Bool} =
        Equal.trans(Bool, Nat.is_lt(k, upto),
          Nat.is_lt(k, Nat.mul(Groups.len_words(G), n)), True{},
          Equal.cong(Nat, Bool, x => Nat.is_lt(k, x), upto,
            Nat.mul(Groups.len_words(G), n), eupto),
          hlt)
      +eget : {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, tbl, U32.from_nat(k)))
               == FT.tbl_at(G, C, n, k) : U32} =
        FT.tbl_tree_get(d, tbl, G, C, n, upto, k, hd, hb, hk_lt, ht)
      +eres : {Arr.Arr.snd(Array<U32>, U32,
                 Array.get(U32, tbl, U32.add(row, ci)))
               == FT.fb_code_words(g, w) : U32} =
        Equal.trans(U32,
          Arr.Arr.snd(Array<U32>, U32, Array.get(U32, tbl, U32.add(row, ci))),
          FT.tbl_at(G, C, n, k),
          FT.fb_code_words(g, w),
          Equal.trans(U32,
            Arr.Arr.snd(Array<U32>, U32, Array.get(U32, tbl, U32.add(row, ci))),
            Arr.Arr.snd(Array<U32>, U32, Array.get(U32, tbl, U32.from_nat(k))),
            FT.tbl_at(G, C, n, k),
            Equal.cong(U32, U32,
              u => Arr.Arr.snd(Array<U32>, U32, Array.get(U32, tbl, u)),
              U32.add(row, ci), U32.from_nat(k), eadd),
            eget),
          Equal.trans(U32,
            FT.tbl_at(G, C, n, k),
            FT.fb_code_words(g, FT.nth_word(C, col)),
            FT.fb_code_words(g, w),
            etbl,
            Equal.cong(+List<Nat>, U32, x => FT.fb_code_words(g, x),
              FT.nth_word(C, col), w,
              Equal.sym(+List<Nat>, w, FT.nth_word(C, col), ew))))
      Arr.DPair{eres, Arr.DPair{hg5, hw5}}

def FT.tbl_lookup_use_col(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    +d: Nat, +upto: Nat, +row: U32, +g: +List<Nat>, +ci: U32, +w: +List<Nat>,
    tbl: Array<U32>,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hb: {Nat.is_le(upto, FT.pow2(d)) == True{} : Bool},
    +en: {Groups.len_words(C) == n : Nat},
    +hg5: {SolveFast.all_len5(G) == True{} : Bool},
    +ht: FT.TblTree(d, 0n, tbl, G, C, n, upto),
    +eupto: {upto == Nat.mul(Groups.len_words(G), n) : Nat},
    +hrow: {FT.gentry_ok_b(G, n, row, g) == True{} : Bool},
    cwit: FT.ColWit<Groups.len_words(G), C, ci, w>) ->
  Arr.Arr.DPair<
    {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, tbl, U32.add(row, ci)))
     == FT.fb_code_words(g, w) : U32},
    Arr.Arr.DPair<{SolveFast.is_len5(g) == True{} : Bool},
                  {SolveFast.is_len5(w) == True{} : Bool}>>:
  match cwit:
    case ColWit{+col, +eci, +ew, +hlt, +hw5}:
      +hcol_n : {Nat.is_lt(col, n) == True{} : Bool} =
        Equal.trans(Bool, Nat.is_lt(col, n),
          Nat.is_lt(col, Groups.len_words(C)), True{},
          Equal.cong(Nat, Bool, x => Nat.is_lt(col, x), n, Groups.len_words(C),
            Equal.sym(Nat, Groups.len_words(C), n, en)),
          hlt)
      +rwit = FT.row_wit_go(G, Nil{}, C, n, row, g, col, hcol_n, hlt, hg5,
        hrow)
      FT.tbl_lookup_use_row(G, C, n, d, upto, row, g, ci, w, tbl,
        hd, hb, ht, eupto, col, eci, ew, hw5, rwit)

def FT.tbl_lookup_wit(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    +row: U32, +g: +List<Nat>, +ci: U32, +w: +List<Nat>, tbl: Array<U32>,
    +htbl: FT.TblOk(G, C, n, tbl),
    +hrow: {FT.gentry_ok_b(G, n, row, g) == True{} : Bool},
    +hcol: {FT.has_col_go(Groups.len_words(G), C, ci, w, 0n)
            == True{} : Bool}) ->
  Arr.Arr.DPair<
    {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, tbl, U32.add(row, ci)))
     == FT.fb_code_words(g, w) : U32},
    Arr.Arr.DPair<{SolveFast.is_len5(g) == True{} : Bool},
                  {SolveFast.is_len5(w) == True{} : Bool}>>:
  +d = FT.tbl_depth(G, n)
  +upto = Nat.mul(Groups.len_words(G), n)
  +hd = Arr.Arr.dpair_l({Nat.is_lt(d, 32n) == True{} : Bool},
          Arr.Arr.DPair<{Nat.is_le(upto, FT.pow2(d)) == True{} : Bool},
            Arr.Arr.DPair<{Groups.len_words(C) == n : Nat},
              Arr.Arr.DPair<{SolveFast.all_len5(G) == True{} : Bool},
                Arr.Arr.DPair<{SolveFast.all_len5(C) == True{} : Bool},
                  FT.TblTree(d, 0n, tbl, G, C, n, upto)>>>>, htbl)
  +r1 = Arr.Arr.dpair_r({Nat.is_lt(d, 32n) == True{} : Bool},
          Arr.Arr.DPair<{Nat.is_le(upto, FT.pow2(d)) == True{} : Bool},
            Arr.Arr.DPair<{Groups.len_words(C) == n : Nat},
              Arr.Arr.DPair<{SolveFast.all_len5(G) == True{} : Bool},
                Arr.Arr.DPair<{SolveFast.all_len5(C) == True{} : Bool},
                  FT.TblTree(d, 0n, tbl, G, C, n, upto)>>>>, htbl)
  +hb = Arr.Arr.dpair_l({Nat.is_le(upto, FT.pow2(d)) == True{} : Bool},
          Arr.Arr.DPair<{Groups.len_words(C) == n : Nat},
            Arr.Arr.DPair<{SolveFast.all_len5(G) == True{} : Bool},
              Arr.Arr.DPair<{SolveFast.all_len5(C) == True{} : Bool},
                FT.TblTree(d, 0n, tbl, G, C, n, upto)>>>, r1)
  +r2 = Arr.Arr.dpair_r({Nat.is_le(upto, FT.pow2(d)) == True{} : Bool},
          Arr.Arr.DPair<{Groups.len_words(C) == n : Nat},
            Arr.Arr.DPair<{SolveFast.all_len5(G) == True{} : Bool},
              Arr.Arr.DPair<{SolveFast.all_len5(C) == True{} : Bool},
                FT.TblTree(d, 0n, tbl, G, C, n, upto)>>>, r1)
  +en = Arr.Arr.dpair_l({Groups.len_words(C) == n : Nat},
          Arr.Arr.DPair<{SolveFast.all_len5(G) == True{} : Bool},
            Arr.Arr.DPair<{SolveFast.all_len5(C) == True{} : Bool},
              FT.TblTree(d, 0n, tbl, G, C, n, upto)>>, r2)
  +r3 = Arr.Arr.dpair_r({Groups.len_words(C) == n : Nat},
          Arr.Arr.DPair<{SolveFast.all_len5(G) == True{} : Bool},
            Arr.Arr.DPair<{SolveFast.all_len5(C) == True{} : Bool},
              FT.TblTree(d, 0n, tbl, G, C, n, upto)>>, r2)
  +hg5 = Arr.Arr.dpair_l({SolveFast.all_len5(G) == True{} : Bool},
           Arr.Arr.DPair<{SolveFast.all_len5(C) == True{} : Bool},
             FT.TblTree(d, 0n, tbl, G, C, n, upto)>, r3)
  +r4 = Arr.Arr.dpair_r({SolveFast.all_len5(G) == True{} : Bool},
          Arr.Arr.DPair<{SolveFast.all_len5(C) == True{} : Bool},
            FT.TblTree(d, 0n, tbl, G, C, n, upto)>, r3)
  +hc5 = Arr.Arr.dpair_l({SolveFast.all_len5(C) == True{} : Bool},
           FT.TblTree(d, 0n, tbl, G, C, n, upto), r4)
  +ht = Arr.Arr.dpair_r({SolveFast.all_len5(C) == True{} : Bool},
          FT.TblTree(d, 0n, tbl, G, C, n, upto), r4)
  +cwit = FT.col_wit_go(Groups.len_words(G), C, Nil{}, ci, w, hc5, hcol)
  FT.tbl_lookup_use_col(G, C, n, d, upto, row, g, ci, w, tbl,
    hd, hb, en, hg5, ht, {==}, hrow, cwit)
# ---------------------------------------------------------------------------
# Section 7: `find_grow`, `build_cwords`, `RowWord`, `glist_of_cwords/guesses`
# ---------------------------------------------------------------------------

def FT.find_grow_go_ok(+w: +List<Nat>, +G: +List<+List<Nat>>, +n: Nat,
    +cur: Nat, hit: Bool,
    +ehit: {hit == SolveFast.next_word_hit(w, G) : Bool},
    +hmem: {Tree.member_word(w, G) == True{} : Bool}) ->
  {FT.has_grow_go(G, n,
     SolveFast.find_grow_go(w, G, U32.from_nat(cur), 1, hit),
     w, cur) == True{} : Bool}:
  match G:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Logic.Proof.false_ne_true(hmem))
    case Con{+gh, +gt}:
      match hit:
        case True{}:
          +ewf : {SolveFast.word_eq_fast(w, gh) == True{} : Bool} =
            Equal.sym(Bool, True{}, SolveFast.word_eq_fast(w, gh), ehit)
          +ew : {Feedback.word_eq(w, gh) == True{} : Bool} =
            Equal.trans(Bool, Feedback.word_eq(w, gh),
              SolveFast.word_eq_fast(w, gh), True{},
              Equal.sym(Bool, SolveFast.word_eq_fast(w, gh),
                Feedback.word_eq(w, gh), FG.FG.word_eq_fast_eq(w, gh)),
              ewf)
          +hand : {Bool.and(U32.is_eq(U32.from_nat(cur), U32.from_nat(cur)),
                     Feedback.word_eq(w, gh)) == True{} : Bool} =
            FO.FO.bool_and_intro(
              U32.is_eq(U32.from_nat(cur), U32.from_nat(cur)),
              Feedback.word_eq(w, gh),
              FT.u32_is_eq_refl(U32.from_nat(cur)), ew)
          Equal.cong(Bool, Bool,
            b => Bool.or(b, FT.has_grow_go(gt, n, U32.from_nat(cur), w,
                              Nat.add(1n, cur))),
            Bool.and(U32.is_eq(U32.from_nat(cur), U32.from_nat(cur)),
              Feedback.word_eq(w, gh)), True{}, hand)
        case False{}:
          +ewf : {SolveFast.word_eq_fast(w, gh) == False{} : Bool} =
            Equal.sym(Bool, False{}, SolveFast.word_eq_fast(w, gh), ehit)
          +ew : {Feedback.word_eq(w, gh) == False{} : Bool} =
            Equal.trans(Bool, Feedback.word_eq(w, gh),
              SolveFast.word_eq_fast(w, gh), False{},
              Equal.sym(Bool, SolveFast.word_eq_fast(w, gh),
                Feedback.word_eq(w, gh), FG.FG.word_eq_fast_eq(w, gh)),
              ewf)
          +hmem_t : {Tree.member_word(w, gt) == True{} : Bool} =
            Equal.trans(Bool,
              Tree.member_word(w, gt),
              Feedback.Bool.case(Bool, Feedback.word_eq(w, gh), True{},
                Tree.member_word(w, gt)),
              True{},
              Equal.cong(Bool, Bool,
                b => Feedback.Bool.case(Bool, b, True{}, Tree.member_word(w, gt)),
                False{}, Feedback.word_eq(w, gh),
                Equal.sym(Bool, Feedback.word_eq(w, gh), False{}, ew)),
              hmem)
          +eadd : {U32.add(U32.from_nat(cur), 1) == U32.from_nat(1n+cur) : U32} =
            Equal.trans(U32,
              U32.add(U32.from_nat(cur), 1),
              U32.from_nat(Nat.add(cur, 1n)),
              U32.from_nat(1n+cur),
              FT.u32_add_from_nat(cur, 1n),
              Equal.cong(Nat, U32, x => U32.from_nat(x),
                Nat.add(cur, 1n), 1n+cur,
                NatProof.NatPrf.add_comm(cur, 1n)))
          +ih : {FT.has_grow_go(gt, n,
                   SolveFast.find_grow_go(w, gt,
                     U32.from_nat(1n+cur), 1,
                     SolveFast.next_word_hit(w, gt)),
                   w, 1n+cur) == True{} : Bool} =
            FT.find_grow_go_ok(w, gt, n, 1n+cur,
              SolveFast.next_word_hit(w, gt), {==}, hmem_t)
          +ih2 : {FT.has_grow_go(gt, n,
                    SolveFast.find_grow_go(w, gt,
                      U32.add(U32.from_nat(cur), 1),
                      1, SolveFast.next_word_hit(w, gt)),
                    w, 1n+cur) == True{} : Bool} =
            Equal.trans(Bool,
              FT.has_grow_go(gt, n,
                SolveFast.find_grow_go(w, gt,
                  U32.add(U32.from_nat(cur), 1),
                  1, SolveFast.next_word_hit(w, gt)),
                w, 1n+cur),
              FT.has_grow_go(gt, n,
                SolveFast.find_grow_go(w, gt,
                  U32.from_nat(1n+cur),
                  1, SolveFast.next_word_hit(w, gt)),
                w, 1n+cur),
              True{},
              Equal.cong(U32, Bool,
                u => FT.has_grow_go(gt, n,
                       SolveFast.find_grow_go(w, gt, u, 1,
                         SolveFast.next_word_hit(w, gt)),
                       w, 1n+cur),
                U32.add(U32.from_nat(cur), 1),
                U32.from_nat(1n+cur), eadd),
              ih)
          FT.bool_or_r(
            Bool.and(
              U32.is_eq(
                SolveFast.find_grow_go(w, gt,
                  U32.add(U32.from_nat(cur), 1),
                  1, SolveFast.next_word_hit(w, gt)),
                U32.from_nat(cur)),
              Feedback.word_eq(w, gh)),
            FT.has_grow_go(gt, n,
              SolveFast.find_grow_go(w, gt,
                U32.add(U32.from_nat(cur), 1),
                1, SolveFast.next_word_hit(w, gt)),
              w, 1n+cur),
            ih2)

def FT.find_grow_ok(+w: +List<Nat>, +G: +List<+List<Nat>>, +n: Nat,
    +hmem: {Tree.member_word(w, G) == True{} : Bool}) ->
  {FT.gentry_ok_b(G, n, SolveFast.find_grow(w, G, 1), w)
   == True{} : Bool}:
  FT.find_grow_go_ok(w, G, n, 0n, SolveFast.next_word_hit(w, G), {==}, hmem)

def FT.has_col_append_r(+m: Nat, +cpre: +List<+List<Nat>>,
    +crem: +List<+List<Nat>>, +ci: U32, +w: +List<Nat>, +cur: Nat,
    +h: {FT.has_col_go(m, crem, ci, w, Nat.add(cur, Groups.len_words(cpre)))
         == True{} : Bool}) ->
  {FT.has_col_go(m, List.append(&2, +List<Nat>, cpre, crem), ci, w, cur)
   == True{} : Bool}:
  match cpre:
    case Nil{}:
      Equal.trans(Bool,
        FT.has_col_go(m, crem, ci, w, cur),
        FT.has_col_go(m, crem, ci, w, Nat.add(cur, 0n)), True{},
        Equal.cong(Nat, Bool, x => FT.has_col_go(m, crem, ci, w, x),
          cur, Nat.add(cur, 0n),
          Equal.sym(Nat, Nat.add(cur, 0n), cur, NatProof.NatPrf.add_zero(cur))),
        h)
    case Con{+ch, +ct}:
      +h2 : {FT.has_col_go(m, crem, ci, w,
               Nat.add(1n+cur, Groups.len_words(ct))) == True{} : Bool} =
        Equal.trans(Bool,
          FT.has_col_go(m, crem, ci, w, Nat.add(1n+cur, Groups.len_words(ct))),
          FT.has_col_go(m, crem, ci, w, Nat.add(cur, 1n+Groups.len_words(ct))),
          True{},
          Equal.cong(Nat, Bool, x => FT.has_col_go(m, crem, ci, w, x),
            1n+Nat.add(cur, Groups.len_words(ct)),
            Nat.add(cur, 1n+Groups.len_words(ct)),
            Equal.sym(Nat, Nat.add(cur, 1n+Groups.len_words(ct)),
              1n+Nat.add(cur, Groups.len_words(ct)),
              NatProof.NatPrf.add_succ(cur, Groups.len_words(ct)))),
          h)
      FT.bool_or_r(
        Bool.and(U32.is_eq(ci, U32.from_nat(Nat.mul(cur, m))),
          Feedback.word_eq(w, ch)),
        FT.has_col_go(m, List.append(&2, +List<Nat>, ct, crem), ci, w, 1n+cur),
        FT.has_col_append_r(m, ct, crem, ci, w, 1n+cur, h2))

def FT.build_cwords_words(+C: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +ci: U32, +gcount: U32) ->
  {SolveFast.cwords_words(SolveFast.build_cwords(C, G, ci, gcount)) == C
   : +List<+List<Nat>>}:
  match C:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>, l => w <> l,
        SolveFast.cwords_words(
          SolveFast.build_cwords(rest, G, U32.add(ci, gcount), gcount)),
        rest,
        FT.build_cwords_words(rest, G, U32.add(ci, gcount), gcount))

def FT.build_cwords_ok_go(+crem: +List<+List<Nat>>, +cpre: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, +n: Nat,
    +hai: {FO.FO.all_in_ref(crem, G) == True{} : Bool}) ->
  {FT.cwords_ok_b(G, List.append(&2, +List<Nat>, cpre, crem), n,
     SolveFast.build_cwords(crem, G,
       U32.from_nat(Nat.mul(Groups.len_words(cpre), Groups.len_words(G))),
       U32.from_nat(Groups.len_words(G)))) == True{} : Bool}:
  match crem:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      +cur : Nat = Groups.len_words(cpre)
      +M : Nat = Groups.len_words(G)
      +hmem : {Tree.member_word(w, G) == True{} : Bool} =
        FO.FO.all_in_head(w, rest, G, hai)
      +htai : {FO.FO.all_in_ref(rest, G) == True{} : Bool} =
        FO.FO.all_in_tail(w, rest, G, hai)
      +hhead_col : {FT.has_col_go(M, w <> rest,
                      U32.from_nat(Nat.mul(cur, M)), w,
                      Nat.add(0n, cur)) == True{} : Bool} =
        Equal.cong(Bool, Bool,
          b => Bool.or(b, FT.has_col_go(M, rest,
                          U32.from_nat(Nat.mul(cur, M)), w, 1n+cur)),
          Bool.and(
            U32.is_eq(U32.from_nat(Nat.mul(cur, M)),
              U32.from_nat(Nat.mul(cur, M))),
            Feedback.word_eq(w, w)),
          True{},
          FO.FO.bool_and_intro(
            U32.is_eq(U32.from_nat(Nat.mul(cur, M)),
              U32.from_nat(Nat.mul(cur, M))),
            Feedback.word_eq(w, w),
            FT.u32_is_eq_refl(U32.from_nat(Nat.mul(cur, M))),
            FbProof.FbPrf.word_eq_refl(w)))
      +hcol : {FT.has_col_go(M, List.append(&2, +List<Nat>, cpre, w <> rest),
                 U32.from_nat(Nat.mul(cur, M)), w, 0n) == True{} : Bool} =
        FT.has_col_append_r(M, cpre, w <> rest,
          U32.from_nat(Nat.mul(cur, M)), w, 0n, hhead_col)
      +hgrow : {FT.gentry_ok_b(G, n, SolveFast.find_grow(w, G, 1), w)
                == True{} : Bool} =
        FT.find_grow_ok(w, G, n, hmem)
      +cpre2 = List.append(&2, +List<Nat>, cpre, w <> Nil{})
      +ec2 : {List.append(&2, +List<Nat>, cpre2, rest)
              == List.append(&2, +List<Nat>, cpre, w <> rest)
              : +List<+List<Nat>>} =
        FT.list_append_snoc(+List<Nat>, cpre, w, rest)
      +el2 : {Groups.len_words(cpre2) == 1n+cur : Nat} =
        Equal.trans(Nat, Groups.len_words(cpre2), Nat.add(cur, 1n), 1n+cur,
          FT.len_words_append(cpre, w <> Nil{}),
          NatProof.NatPrf.add_comm(cur, 1n))
      +em : {U32.add(U32.from_nat(Nat.mul(cur, M)), U32.from_nat(M))
             == U32.from_nat(Nat.mul(1n+cur, M)) : U32} =
        Equal.trans(U32,
          U32.add(U32.from_nat(Nat.mul(cur, M)), U32.from_nat(M)),
          U32.from_nat(Nat.add(Nat.mul(cur, M), M)),
          U32.from_nat(Nat.mul(1n+cur, M)),
          FT.u32_add_from_nat(Nat.mul(cur, M), M),
          Equal.cong(Nat, U32, x => U32.from_nat(x),
            Nat.add(Nat.mul(cur, M), M), Nat.mul(1n+cur, M),
            NatProof.NatPrf.add_comm(Nat.mul(cur, M), M)))
      +eci2 : {U32.from_nat(Nat.mul(Groups.len_words(cpre2), M))
               == U32.add(U32.from_nat(Nat.mul(cur, M)),
                    U32.from_nat(M)) : U32} =
        Equal.trans(U32,
          U32.from_nat(Nat.mul(Groups.len_words(cpre2), M)),
          U32.from_nat(Nat.mul(1n+cur, M)),
          U32.add(U32.from_nat(Nat.mul(cur, M)), U32.from_nat(M)),
          Equal.cong(Nat, U32, x => U32.from_nat(Nat.mul(x, M)),
            Groups.len_words(cpre2), 1n+cur, el2),
          Equal.sym(U32, U32.add(U32.from_nat(Nat.mul(cur, M)),
            U32.from_nat(M)), U32.from_nat(Nat.mul(1n+cur, M)), em))
      +hrec0 = FT.build_cwords_ok_go(rest, cpre2, G, n, htai)
      +hrec : {FT.cwords_ok_b(G, List.append(&2, +List<Nat>, cpre, w <> rest),
                 n,
                 SolveFast.build_cwords(rest, G,
                   U32.add(U32.from_nat(Nat.mul(cur, M)), U32.from_nat(M)),
                   U32.from_nat(M))) == True{} : Bool} =
        Equal.trans(Bool,
          FT.cwords_ok_b(G, List.append(&2, +List<Nat>, cpre, w <> rest), n,
            SolveFast.build_cwords(rest, G,
              U32.add(U32.from_nat(Nat.mul(cur, M)), U32.from_nat(M)),
              U32.from_nat(M))),
          FT.cwords_ok_b(G, List.append(&2, +List<Nat>, cpre, w <> rest), n,
            SolveFast.build_cwords(rest, G,
              U32.from_nat(Nat.mul(Groups.len_words(cpre2), M)),
              U32.from_nat(M))),
          True{},
          Equal.cong(U32, Bool,
            u => FT.cwords_ok_b(G,
                   List.append(&2, +List<Nat>, cpre, w <> rest), n,
                   SolveFast.build_cwords(rest, G, u, U32.from_nat(M))),
            U32.add(U32.from_nat(Nat.mul(cur, M)), U32.from_nat(M)),
            U32.from_nat(Nat.mul(Groups.len_words(cpre2), M)),
            Equal.sym(U32,
              U32.from_nat(Nat.mul(Groups.len_words(cpre2), M)),
              U32.add(U32.from_nat(Nat.mul(cur, M)), U32.from_nat(M)),
              eci2)),
          Equal.trans(Bool,
            FT.cwords_ok_b(G, List.append(&2, +List<Nat>, cpre, w <> rest), n,
              SolveFast.build_cwords(rest, G,
                U32.from_nat(Nat.mul(Groups.len_words(cpre2), M)),
                U32.from_nat(M))),
            FT.cwords_ok_b(G, List.append(&2, +List<Nat>, cpre2, rest), n,
              SolveFast.build_cwords(rest, G,
                U32.from_nat(Nat.mul(Groups.len_words(cpre2), M)),
                U32.from_nat(M))),
            True{},
            Equal.cong(+List<+List<Nat>>, Bool,
              l => FT.cwords_ok_b(G, l, n,
                     SolveFast.build_cwords(rest, G,
                       U32.from_nat(Nat.mul(Groups.len_words(cpre2), M)),
                       U32.from_nat(M))),
              List.append(&2, +List<Nat>, cpre, w <> rest),
              List.append(&2, +List<Nat>, cpre2, rest),
              Equal.sym(+List<+List<Nat>>,
                List.append(&2, +List<Nat>, cpre2, rest),
                List.append(&2, +List<Nat>, cpre, w <> rest), ec2)),
            hrec0))
      FO.FO.bool_and_intro(
        Bool.and(
          FT.has_col_go(M, List.append(&2, +List<Nat>, cpre, w <> rest),
            U32.from_nat(Nat.mul(cur, M)), w, 0n),
          FT.gentry_ok_b(G, n, SolveFast.find_grow(w, G, 1), w)),
        FT.cwords_ok_b(G, List.append(&2, +List<Nat>, cpre, w <> rest), n,
          SolveFast.build_cwords(rest, G,
            U32.add(U32.from_nat(Nat.mul(cur, M)), U32.from_nat(M)),
            U32.from_nat(M))),
        FO.FO.bool_and_intro(
          FT.has_col_go(M, List.append(&2, +List<Nat>, cpre, w <> rest),
            U32.from_nat(Nat.mul(cur, M)), w, 0n),
          FT.gentry_ok_b(G, n, SolveFast.find_grow(w, G, 1), w),
          hcol, hgrow),
        hrec)

def FT.build_cwords_ok(+C: +List<+List<Nat>>, +G: +List<+List<Nat>>, +n: Nat,
    +hai: {FO.FO.all_in_ref(C, G) == True{} : Bool}) ->
  {FT.cwords_ok_b(G, C, n,
     SolveFast.build_cwords(C, G, 0, U32.from_nat(Groups.len_words(G))))
   == True{} : Bool}:
  FT.build_cwords_ok_go(C, Nil{}, G, n, hai)

# Unified `(row, word)` list for `glist_walk` covering both `glist_of_cwords`
# and `glist_of_guesses`.
type FT.RowWord is Data:
  RowWord{row: U32, word: +List<Nat>}

def FT.glist_of_rws(+rws: +List<FT.RowWord>, +tail: SolveFast.GList) ->
  SolveFast.GList:
  match rws:
    case Nil{}:
      tail
    case Con{rw, rest}:
      match rw:
        case RowWord{r, w}:
          SolveFast.GTry{r, w, FT.glist_of_rws(rest, tail)}

def FT.rws_words(+rws: +List<FT.RowWord>) -> +List<+List<Nat>>:
  match rws:
    case Nil{}:
      Nil{}
    case Con{rw, rest}:
      match rw:
        case RowWord{r, w}:
          w <> FT.rws_words(rest)

def FT.rws_ok_b(+G: +List<+List<Nat>>, +n: Nat, +rws: +List<FT.RowWord>) -> Bool:
  match rws:
    case Nil{}:
      True{}
    case Con{rw, rest}:
      match rw:
        case RowWord{r, w}:
          Bool.and(FT.gentry_ok_b(G, n, r, w), FT.rws_ok_b(G, n, rest))

def FT.cwords_to_rws(+cs: +List<SolveFast.CWord>) -> +List<FT.RowWord>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{cw, rest}:
      match cw:
        case SolveFast.CWord{ci, grow, w}:
          RowWord{grow, w} <> FT.cwords_to_rws(rest)

def FT.guesses_to_rws(+G: +List<+List<Nat>>, +row: U32, +stride: U32) ->
  +List<FT.RowWord>:
  match G:
    case Nil{}:
      Nil{}
    case Con{g, rest}:
      RowWord{row, g} <> FT.guesses_to_rws(rest, U32.add(row, stride), stride)

def FT.glist_of_cwords_eq(+cs: +List<SolveFast.CWord>, +tail: SolveFast.GList) ->
  {SolveFast.glist_of_cwords(cs, tail)
   == FT.glist_of_rws(FT.cwords_to_rws(cs), tail) : SolveFast.GList}:
  match cs:
    case Nil{}:
      {==}
    case Con{cw, +rest}:
      match cw:
        case SolveFast.CWord{ci, +grow, +w}:
          Equal.cong(SolveFast.GList, SolveFast.GList,
            t => SolveFast.GTry{grow, w, t},
            SolveFast.glist_of_cwords(rest, tail),
            FT.glist_of_rws(FT.cwords_to_rws(rest), tail),
            FT.glist_of_cwords_eq(rest, tail))

def FT.cwords_to_rws_words(+cs: +List<SolveFast.CWord>) ->
  {FT.rws_words(FT.cwords_to_rws(cs)) == SolveFast.cwords_words(cs)
   : +List<+List<Nat>>}:
  match cs:
    case Nil{}:
      {==}
    case Con{cw, +rest}:
      match cw:
        case SolveFast.CWord{ci, grow, +w}:
          Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>, l => w <> l,
            FT.rws_words(FT.cwords_to_rws(rest)),
            SolveFast.cwords_words(rest),
            FT.cwords_to_rws_words(rest))

def FT.cwords_to_rws_ok(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    +cs: +List<SolveFast.CWord>,
    +hok: {FT.cwords_ok_b(G, C, n, cs) == True{} : Bool}) ->
  {FT.rws_ok_b(G, n, FT.cwords_to_rws(cs)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{cw, +rest}:
      match cw:
        case SolveFast.CWord{+ci, +grow, +w}:
          +h1 = Logic.Proof.and_true_l(
                  Bool.and(FT.has_col_go(Groups.len_words(G), C, ci, w, 0n),
                    FT.gentry_ok_b(G, n, grow, w)),
                  FT.cwords_ok_b(G, C, n, rest), hok)
          +hr = Logic.Proof.and_true_r(
                  Bool.and(FT.has_col_go(Groups.len_words(G), C, ci, w, 0n),
                    FT.gentry_ok_b(G, n, grow, w)),
                  FT.cwords_ok_b(G, C, n, rest), hok)
          +hg = Logic.Proof.and_true_r(FT.has_col_go(Groups.len_words(G), C, ci, w, 0n),
                  FT.gentry_ok_b(G, n, grow, w), h1)
          FO.FO.bool_and_intro(FT.gentry_ok_b(G, n, grow, w),
            FT.rws_ok_b(G, n, FT.cwords_to_rws(rest)),
            hg, FT.cwords_to_rws_ok(G, C, n, rest, hr))

def FT.glist_of_guesses_eq(+G: +List<+List<Nat>>, +row: U32, +stride: U32) ->
  {SolveFast.glist_of_guesses(G, row, stride)
   == FT.glist_of_rws(FT.guesses_to_rws(G, row, stride), SolveFast.GEnd{})
   : SolveFast.GList}:
  match G:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      Equal.cong(SolveFast.GList, SolveFast.GList,
        t => SolveFast.GTry{row, g, t},
        SolveFast.glist_of_guesses(rest, U32.add(row, stride), stride),
        FT.glist_of_rws(FT.guesses_to_rws(rest, U32.add(row, stride), stride),
          SolveFast.GEnd{}),
        FT.glist_of_guesses_eq(rest, U32.add(row, stride), stride))

def FT.guesses_to_rws_words(+G: +List<+List<Nat>>, +row: U32, +stride: U32) ->
  {FT.rws_words(FT.guesses_to_rws(G, row, stride)) == G : +List<+List<Nat>>}:
  match G:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>, l => g <> l,
        FT.rws_words(FT.guesses_to_rws(rest, U32.add(row, stride), stride)),
        rest,
        FT.guesses_to_rws_words(rest, U32.add(row, stride), stride))

def FT.has_grow_append_r(+gpre: +List<+List<Nat>>, +grem: +List<+List<Nat>>,
    +n: Nat, +row: U32, +g: +List<Nat>, +cur: Nat,
    +h: {FT.has_grow_go(grem, n, row, g,
           Nat.add(cur, Groups.len_words(gpre))) == True{} : Bool}) ->
  {FT.has_grow_go(List.append(&2, +List<Nat>, gpre, grem), n, row, g, cur)
   == True{} : Bool}:
  match gpre:
    case Nil{}:
      Equal.trans(Bool,
        FT.has_grow_go(grem, n, row, g, cur),
        FT.has_grow_go(grem, n, row, g, Nat.add(cur, 0n)), True{},
        Equal.cong(Nat, Bool, x => FT.has_grow_go(grem, n, row, g, x),
          cur, Nat.add(cur, 0n),
          Equal.sym(Nat, Nat.add(cur, 0n), cur, NatProof.NatPrf.add_zero(cur))),
        h)
    case Con{+gh, +gt}:
      +h2 : {FT.has_grow_go(grem, n, row, g,
               Nat.add(1n+cur, Groups.len_words(gt))) == True{} : Bool} =
        Equal.trans(Bool,
          FT.has_grow_go(grem, n, row, g,
            Nat.add(1n+cur, Groups.len_words(gt))),
          FT.has_grow_go(grem, n, row, g,
            Nat.add(cur, 1n+Groups.len_words(gt))),
          True{},
          Equal.cong(Nat, Bool, x => FT.has_grow_go(grem, n, row, g, x),
            1n+Nat.add(cur, Groups.len_words(gt)),
            Nat.add(cur, 1n+Groups.len_words(gt)),
            Equal.sym(Nat, Nat.add(cur, 1n+Groups.len_words(gt)),
              1n+Nat.add(cur, Groups.len_words(gt)),
              NatProof.NatPrf.add_succ(cur, Groups.len_words(gt)))),
          h)
      FT.bool_or_r(
        Bool.and(U32.is_eq(row, U32.from_nat(cur)), Feedback.word_eq(g, gh)),
        FT.has_grow_go(List.append(&2, +List<Nat>, gt, grem), n, row, g,
          1n+cur),
        FT.has_grow_append_r(gt, grem, n, row, g, 1n+cur, h2))

def FT.guesses_to_rws_ok_go(+grem: +List<+List<Nat>>, +gpre: +List<+List<Nat>>,
    +n: Nat) ->
  {FT.rws_ok_b(List.append(&2, +List<Nat>, gpre, grem), n,
     FT.guesses_to_rws(grem, U32.from_nat(Groups.len_words(gpre)), 1))
   == True{} : Bool}:
  match grem:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      +ri : Nat = Groups.len_words(gpre)
      +hhead : {FT.has_grow_go(g <> rest, n, U32.from_nat(ri), g,
                  Nat.add(0n, ri)) == True{} : Bool} =
        Equal.cong(Bool, Bool,
          b => Bool.or(b, FT.has_grow_go(rest, n, U32.from_nat(ri), g, 1n+ri)),
          Bool.and(U32.is_eq(U32.from_nat(ri), U32.from_nat(ri)),
            Feedback.word_eq(g, g)),
          True{},
          FO.FO.bool_and_intro(
            U32.is_eq(U32.from_nat(ri), U32.from_nat(ri)),
            Feedback.word_eq(g, g),
            FT.u32_is_eq_refl(U32.from_nat(ri)),
            FbProof.FbPrf.word_eq_refl(g)))
      +hg : {FT.gentry_ok_b(List.append(&2, +List<Nat>, gpre, g <> rest), n,
               U32.from_nat(ri), g) == True{} : Bool} =
        FT.has_grow_append_r(gpre, g <> rest, n, U32.from_nat(ri), g, 0n, hhead)
      +gpre2 = List.append(&2, +List<Nat>, gpre, g <> Nil{})
      +eg2 : {List.append(&2, +List<Nat>, gpre2, rest)
              == List.append(&2, +List<Nat>, gpre, g <> rest)
              : +List<+List<Nat>>} =
        FT.list_append_snoc(+List<Nat>, gpre, g, rest)
      +el2 : {Groups.len_words(gpre2) == Nat.add(ri, 1n) : Nat} =
        FT.len_words_append(gpre, g <> Nil{})
      +eu : {U32.add(U32.from_nat(ri), 1)
             == U32.from_nat(Groups.len_words(gpre2)) : U32} =
        Equal.trans(U32,
          U32.add(U32.from_nat(ri), 1),
          U32.from_nat(Nat.add(ri, 1n)),
          U32.from_nat(Groups.len_words(gpre2)),
          FT.u32_add_from_nat(ri, 1n),
          Equal.cong(Nat, U32, x => U32.from_nat(x),
            Nat.add(ri, 1n), Groups.len_words(gpre2),
            Equal.sym(Nat, Groups.len_words(gpre2), Nat.add(ri, 1n), el2)))
      +hrec : {FT.rws_ok_b(List.append(&2, +List<Nat>, gpre, g <> rest), n,
                 FT.guesses_to_rws(rest, U32.add(U32.from_nat(ri), 1), 1))
               == True{} : Bool} =
        Equal.trans(Bool,
          FT.rws_ok_b(List.append(&2, +List<Nat>, gpre, g <> rest), n,
            FT.guesses_to_rws(rest, U32.add(U32.from_nat(ri), 1), 1)),
          FT.rws_ok_b(List.append(&2, +List<Nat>, gpre2, rest), n,
            FT.guesses_to_rws(rest, U32.from_nat(Groups.len_words(gpre2)), 1)),
          True{},
          Equal.trans(Bool,
            FT.rws_ok_b(List.append(&2, +List<Nat>, gpre, g <> rest), n,
              FT.guesses_to_rws(rest, U32.add(U32.from_nat(ri), 1), 1)),
            FT.rws_ok_b(List.append(&2, +List<Nat>, gpre2, rest), n,
              FT.guesses_to_rws(rest, U32.add(U32.from_nat(ri), 1), 1)),
            FT.rws_ok_b(List.append(&2, +List<Nat>, gpre2, rest), n,
              FT.guesses_to_rws(rest, U32.from_nat(Groups.len_words(gpre2)),
                1)),
            Equal.cong(+List<+List<Nat>>, Bool,
              l => FT.rws_ok_b(l, n,
                     FT.guesses_to_rws(rest, U32.add(U32.from_nat(ri), 1), 1)),
              List.append(&2, +List<Nat>, gpre, g <> rest),
              List.append(&2, +List<Nat>, gpre2, rest),
              Equal.sym(+List<+List<Nat>>,
                List.append(&2, +List<Nat>, gpre2, rest),
                List.append(&2, +List<Nat>, gpre, g <> rest), eg2)),
            Equal.cong(U32, Bool,
              u => FT.rws_ok_b(List.append(&2, +List<Nat>, gpre2, rest), n,
                     FT.guesses_to_rws(rest, u, 1)),
              U32.add(U32.from_nat(ri), 1),
              U32.from_nat(Groups.len_words(gpre2)), eu)),
          FT.guesses_to_rws_ok_go(rest, gpre2, n))
      FO.FO.bool_and_intro(
        FT.gentry_ok_b(List.append(&2, +List<Nat>, gpre, g <> rest), n,
          U32.from_nat(ri), g),
        FT.rws_ok_b(List.append(&2, +List<Nat>, gpre, g <> rest), n,
          FT.guesses_to_rws(rest, U32.add(U32.from_nat(ri), 1), 1)),
        hg, hrec)

def FT.guesses_to_rws_ok(+G: +List<+List<Nat>>, +n: Nat) ->
  {FT.rws_ok_b(G, n, FT.guesses_to_rws(G, 0, 1)) == True{} : Bool}:
  FT.guesses_to_rws_ok_go(G, Nil{}, n)

def FT.rev_cwords_ws(r: SolveFast.RevCWordsLen) -> +List<SolveFast.CWord>:
  match r:
    case SolveFast.RevCWordsLen{l, ws}:
      ws

def FT.rev_cwords_ok(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    +xs: +List<SolveFast.CWord>, +acc: +List<SolveFast.CWord>,
    +hxs: {FT.cwords_ok_b(G, C, n, xs) == True{} : Bool},
    +hacc: {FT.cwords_ok_b(G, C, n, acc) == True{} : Bool}, +len: Nat) ->
  {FT.cwords_ok_b(G, C, n,
     FT.rev_cwords_ws(SolveFast.rev_cwords_len(xs, acc, len))) == True{} : Bool}:
  match xs:
    case Nil{}:
      hacc
    case Con{+cw, +t}:
      +hcw = Logic.Proof.and_true_l(FT.cword_ok_b(G, C, n, cw),
               FT.cwords_ok_b(G, C, n, t), hxs)
      +ht = Logic.Proof.and_true_r(FT.cword_ok_b(G, C, n, cw),
              FT.cwords_ok_b(G, C, n, t), hxs)
      FT.rev_cwords_ok(G, C, n, t, cw <> acc, ht,
        FO.FO.bool_and_intro(FT.cword_ok_b(G, C, n, cw),
          FT.cwords_ok_b(G, C, n, acc), hcw, hacc),
        Nat.add(1n, len))

# ---------------------------------------------------------------------------
# Section 8: `TblOk` array depth, `len5` feedback-code corollaries, `cwords_words`
# ---------------------------------------------------------------------------

def FT.tbl_ok_depth(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    tbl: Array<U32>, +htbl: FT.TblOk(G, C, n, tbl)) ->
  Arr.Arr.Depth(U32, FT.tbl_depth(G, n), tbl):
  +d = FT.tbl_depth(G, n)
  +upto = Nat.mul(Groups.len_words(G), n)
  +r1 = Arr.Arr.dpair_r({Nat.is_lt(d, 32n) == True{} : Bool},
          Arr.Arr.DPair<{Nat.is_le(upto, FT.pow2(d)) == True{} : Bool},
            Arr.Arr.DPair<{Groups.len_words(C) == n : Nat},
              Arr.Arr.DPair<{SolveFast.all_len5(G) == True{} : Bool},
                Arr.Arr.DPair<{SolveFast.all_len5(C) == True{} : Bool},
                  FT.TblTree(d, 0n, tbl, G, C, n, upto)>>>>, htbl)
  +r2 = Arr.Arr.dpair_r({Nat.is_le(upto, FT.pow2(d)) == True{} : Bool},
          Arr.Arr.DPair<{Groups.len_words(C) == n : Nat},
            Arr.Arr.DPair<{SolveFast.all_len5(G) == True{} : Bool},
              Arr.Arr.DPair<{SolveFast.all_len5(C) == True{} : Bool},
                FT.TblTree(d, 0n, tbl, G, C, n, upto)>>>, r1)
  +r3 = Arr.Arr.dpair_r({Groups.len_words(C) == n : Nat},
          Arr.Arr.DPair<{SolveFast.all_len5(G) == True{} : Bool},
            Arr.Arr.DPair<{SolveFast.all_len5(C) == True{} : Bool},
              FT.TblTree(d, 0n, tbl, G, C, n, upto)>>, r2)
  +r4 = Arr.Arr.dpair_r({SolveFast.all_len5(G) == True{} : Bool},
          Arr.Arr.DPair<{SolveFast.all_len5(C) == True{} : Bool},
            FT.TblTree(d, 0n, tbl, G, C, n, upto)>, r3)
  +ht = Arr.Arr.dpair_r({SolveFast.all_len5(C) == True{} : Bool},
          FT.TblTree(d, 0n, tbl, G, C, n, upto), r4)
  FT.tbl_tree_depth(d, 0n, tbl, G, C, n, upto, ht)

def FT.is_len5_elim(-R: Data, +w: +List<Nat>,
    +h5: {SolveFast.is_len5(w) == True{} : Bool},
    k: @a0: Nat -> @a1: Nat -> @a2: Nat -> @a3: Nat -> @a4: Nat ->
       {w == a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{})))) : +List<Nat>} -> R) -> R:
  match w:
    case Nil{}:
      Empty.absurd(R, Logic.Proof.false_ne_true(h5))
    case Con{+a0, +t1}:
      match t1:
        case Nil{}:
          Empty.absurd(R, Logic.Proof.false_ne_true(h5))
        case Con{+a1, +t2}:
          match t2:
            case Nil{}:
              Empty.absurd(R, Logic.Proof.false_ne_true(h5))
            case Con{+a2, +t3}:
              match t3:
                case Nil{}:
                  Empty.absurd(R, Logic.Proof.false_ne_true(h5))
                case Con{+a3, +t4}:
                  match t4:
                    case Nil{}:
                      Empty.absurd(R, Logic.Proof.false_ne_true(h5))
                    case Con{+a4, +t5}:
                      match t5:
                        case Nil{}:
                          k(a0, a1, a2, a3, a4, {==})
                        case Con{_, _}:
                          Empty.absurd(R, Logic.Proof.false_ne_true(h5))

def FT.is_fb5_of_len5(+g: +List<Nat>, +w: +List<Nat>,
    +hg: {SolveFast.is_len5(g) == True{} : Bool},
    +hw: {SolveFast.is_len5(w) == True{} : Bool}) ->
  {FF5.FF5.is_fb5(Feedback.feedback(g, w)) == True{} : Bool}:
  FT.is_len5_elim(
    {FF5.FF5.is_fb5(Feedback.feedback(g, w)) == True{} : Bool}, g, hg,
    +g0 => +g1 => +g2 => +g3 => +g4 => +eg =>
      FT.is_len5_elim(
        {FF5.FF5.is_fb5(Feedback.feedback(g, w)) == True{} : Bool}, w, hw,
        +a0 => +a1 => +a2 => +a3 => +a4 => +ew =>
          %Equal.sym(+List<Nat>, g,
             g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), eg) :
            {FF5.FF5.is_fb5(Feedback.feedback(_, w)) == True{} : Bool}
          %Equal.sym(+List<Nat>, w,
             a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{})))), ew) :
            {FF5.FF5.is_fb5(Feedback.feedback(
               g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), _)) == True{} : Bool}
          FF5.FF5.feedback_len5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4)))

def FT.decode_fb_code(+g: +List<Nat>, +w: +List<Nat>,
    +hg: {SolveFast.is_len5(g) == True{} : Bool},
    +hw: {SolveFast.is_len5(w) == True{} : Bool}) ->
  {SolveFast.decode_fb5(FT.fb_code_words(g, w)) == Feedback.feedback(g, w)
   : +List<Feedback.Color>}:
  FF5.FF5.decode_encode_list(Feedback.feedback(g, w),
    FT.is_fb5_of_len5(g, w, hg, hw))

def FT.fb_code_zero_from(+g: +List<Nat>, +w: +List<Nat>,
    +hg: {SolveFast.is_len5(g) == True{} : Bool},
    +hw: {SolveFast.is_len5(w) == True{} : Bool}) ->
  {Arr.Arr.u32_zero_from(10n, FT.fb_code_words(g, w)) == True{} : Bool}:
  FF5.FF5.encode_fb5_list_zero_from(Feedback.feedback(g, w),
    FT.is_fb5_of_len5(g, w, hg, hw))

def FT.fb_code_is_682(+g: +List<Nat>, +w: +List<Nat>,
    +hg: {SolveFast.is_len5(g) == True{} : Bool},
    +hw: {SolveFast.is_len5(w) == True{} : Bool}) ->
  {U32.is_eq(FT.fb_code_words(g, w), 682) == Feedback.word_eq(g, w) : Bool}:
  FT.is_len5_elim(
    {U32.is_eq(FT.fb_code_words(g, w), 682) == Feedback.word_eq(g, w) : Bool},
    g, hg,
    +g0 => +g1 => +g2 => +g3 => +g4 => +eg =>
      FT.is_len5_elim(
        {U32.is_eq(FT.fb_code_words(g, w), 682) == Feedback.word_eq(g, w) : Bool},
        w, hw,
        +a0 => +a1 => +a2 => +a3 => +a4 => +ew =>
          %Equal.sym(+List<Nat>, g,
             g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), eg) :
            {U32.is_eq(FT.fb_code_words(_, w), 682) == Feedback.word_eq(_, w) : Bool}
          %Equal.sym(+List<Nat>, w,
             a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{})))), ew) :
            {U32.is_eq(
               FT.fb_code_words(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), _), 682)
             == Feedback.word_eq(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))), _) : Bool}
          Equal.trans(Bool,
            U32.is_eq(
              FT.fb_code_words(
                g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
                a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))), 682),
            U32.is_eq(
              SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4), 682),
            Feedback.word_eq(
              g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
              a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))),
            Equal.cong(U32, Bool, u => U32.is_eq(u, 682),
              FT.fb_code_words(
                g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
                a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))),
              SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4),
              Equal.sym(U32,
                SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4),
                FT.fb_code_words(
                  g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
                  a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))),
                FF5.FF5.feedback_code5_eq(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4))),
            FF5.FF5.code5_is_682_eq(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4))))

def FT.fb_code_eq_iff(+g1: +List<Nat>, +w1: +List<Nat>,
    +g2: +List<Nat>, +w2: +List<Nat>,
    +hg1: {SolveFast.is_len5(g1) == True{} : Bool},
    +hw1: {SolveFast.is_len5(w1) == True{} : Bool},
    +hg2: {SolveFast.is_len5(g2) == True{} : Bool},
    +hw2: {SolveFast.is_len5(w2) == True{} : Bool}) ->
  {U32.is_eq(FT.fb_code_words(g1, w1), FT.fb_code_words(g2, w2))
   == Feedback.feedback_eq(Feedback.feedback(g1, w1), Feedback.feedback(g2, w2))
   : Bool}:
  FF5.FF5.code_eq_iff_fb_eq(
    Feedback.feedback(g1, w1), Feedback.feedback(g2, w2),
    FT.is_fb5_of_len5(g1, w1, hg1, hw1),
    FT.is_fb5_of_len5(g2, w2, hg2, hw2))

def FT.rev_cwords_len_words(+xs: +List<SolveFast.CWord>,
    +acc: +List<SolveFast.CWord>, +len: Nat) ->
  {SolveFast.cwords_words(FT.rev_cwords_ws(SolveFast.rev_cwords_len(xs, acc, len)))
   == SolveFast.rev_words(SolveFast.cwords_words(xs),
        SolveFast.cwords_words(acc)) : +List<+List<Nat>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{cw, +t}:
      match cw:
        case SolveFast.CWord{+ci, +grow, +w}:
          FT.rev_cwords_len_words(t, SolveFast.CWord{ci, grow, w} <> acc,
            Nat.add(1n, len))

def FT.rev_cwords_len_val(r: SolveFast.RevCWordsLen) -> Nat:
  match r:
    case SolveFast.RevCWordsLen{l, ws}:
      l

def FT.rev_cwords_len_eq(+xs: +List<SolveFast.CWord>,
    +acc: +List<SolveFast.CWord>, +len: Nat) ->
  {FT.rev_cwords_len_val(SolveFast.rev_cwords_len(xs, acc, len))
   == Nat.add(Groups.len_words(SolveFast.cwords_words(xs)), len) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{cw, +t}:
      match cw:
        case SolveFast.CWord{+ci, +grow, +w}:
          Equal.trans(Nat,
            FT.rev_cwords_len_val(
              SolveFast.rev_cwords_len(t, SolveFast.CWord{ci, grow, w} <> acc,
                Nat.add(1n, len))),
            Nat.add(Groups.len_words(SolveFast.cwords_words(t)), 1n+len),
            1n+Nat.add(Groups.len_words(SolveFast.cwords_words(t)), len),
            FT.rev_cwords_len_eq(t, SolveFast.CWord{ci, grow, w} <> acc,
              Nat.add(1n, len)),
            NatProof.NatPrf.add_succ(
              Groups.len_words(SolveFast.cwords_words(t)), len))

def FT.member_of_has_grow(+G: +List<+List<Nat>>, +n: Nat, +row: U32,
    +g: +List<Nat>, +cur: Nat,
    +h: {FT.has_grow_go(G, n, row, g, cur) == True{} : Bool}) ->
  {Tree.member_word(g, G) == True{} : Bool}:
  match G:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, Logic.Proof.false_ne_true(h))
    case Con{+gh, +gt}:
      FT.bool_or_elim_go(
        {Tree.member_word(g, gh <> gt) == True{} : Bool},
        Bool.and(U32.is_eq(row, U32.from_nat(cur)), Feedback.word_eq(g, gh)),
        FT.has_grow_go(gt, n, row, g, 1n+cur), h,
        +hl =>
          +ew : {Feedback.word_eq(g, gh) == True{} : Bool} =
            Logic.Proof.and_true_r(U32.is_eq(row, U32.from_nat(cur)),
              Feedback.word_eq(g, gh), hl)
          Equal.cong(Bool, Bool,
            b => Feedback.Bool.case(Bool, b, True{}, Tree.member_word(g, gt)),
            Feedback.word_eq(g, gh), True{}, ew),
        +hr =>
          +hrec : {Tree.member_word(g, gt) == True{} : Bool} =
            FT.member_of_has_grow(gt, n, row, g, 1n+cur, hr)
          FN.FN.member_cons_r(g, gh, gt, hrec))

def FT.member_of_gentry_ok(+G: +List<+List<Nat>>, +n: Nat, +row: U32,
    +g: +List<Nat>,
    +h: {FT.gentry_ok_b(G, n, row, g) == True{} : Bool}) ->
  {Tree.member_word(g, G) == True{} : Bool}:
  FT.member_of_has_grow(G, n, row, g, 0n, h)

def FT.tbl_get_unpack(-R: (Array<U32> & U32) -> Data,
    -tbl: Array<U32>, +v: U32, r: Array<U32> & U32,
    +efst: {Arr.Arr.fst(Array<U32>, U32, r) == tbl : Array<U32>},
    +esnd: {Arr.Arr.snd(Array<U32>, U32, r) == v : U32},
    k: @t_out: Array<U32> -> @code: U32 ->
       {t_out == tbl : Array<U32>} -> {code == v : U32} -> R((t_out, code))) ->
  R(r):
  (t_out, +code) = r
  k(t_out, code, efst, esnd)

def FT.tbl_get_use_dup3(-R: (Array<U32> & U32) -> Data,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    +row: U32, +g: +List<Nat>, +ci: U32, +w: +List<Nat>,
    -tbl: Array<U32>, t1: Array<U32>, t2a: Array<U32>, -t2b: Array<U32>,
    +et1: {t1 == tbl : Array<U32>},
    +et2a: {t2a == tbl : Array<U32>},
    +et2b: {t2b == tbl : Array<U32>},
    dp3: &t3: Array<U32> -> &t4: Array<U32> ->
         {t3 == t2b : Array<U32>} & {t4 == t3 : Array<U32>},
    +htbl: FT.TblOk(G, C, n, tbl),
    +hrow: {FT.gentry_ok_b(G, n, row, g) == True{} : Bool},
    +hcol: {FT.has_col_go(Groups.len_words(G), C, ci, w, 0n) == True{} : Bool},
    k: @t_out: Array<U32> -> @code: U32 ->
       {t_out == tbl : Array<U32>} ->
       FT.TblOk(G, C, n, t_out) ->
       {code == FT.fb_code_words(g, w) : U32} ->
       {SolveFast.is_len5(g) == True{} : Bool} ->
       {SolveFast.is_len5(w) == True{} : Bool} ->
       R((t_out, code))) ->
  R(Array.get(U32, tbl, U32.add(row, ci))):
  (t3, dp4) = dp3
  (t4, pe3) = dp4
  (+et3_2b, +et4_3) = pe3
  +et3 : {t3 == tbl : Array<U32>} =
    Equal.trans(Array<U32>, t3, t2b, tbl, et3_2b, et2b)
  +et4 : {t4 == tbl : Array<U32>} =
    Equal.trans(Array<U32>, t4, t3, tbl, et4_3, et3)
  +idx = U32.add(row, ci)
  +ht1 = FT.tbl_ok_transport(G, C, n, tbl, t1,
           Equal.sym(Array<U32>, t1, tbl, et1), htbl)
  +hdp1 = FT.tbl_ok_depth(G, C, n, t1, ht1)
  +hdp2a = Arr.Arr.depth_transport(U32, FT.tbl_depth(G, n), t1, t2a,
             Equal.trans(Array<U32>, t1, tbl, t2a, et1,
               Equal.sym(Array<U32>, t2a, tbl, et2a)), hdp1)
  +efst2a : {Arr.Arr.fst(Array<U32>, U32, Array.get(U32, t2a, idx)) == t2a
             : Array<U32>} =
    Arr.Arr.get_fst(U32, FT.tbl_depth(G, n), t2a, idx, hdp2a)
  +efst4 : {Arr.Arr.fst(Array<U32>, U32, Array.get(U32, t4, idx)) == tbl
            : Array<U32>} =
    Equal.trans(Array<U32>,
      Arr.Arr.fst(Array<U32>, U32, Array.get(U32, t4, idx)),
      Arr.Arr.fst(Array<U32>, U32, Array.get(U32, t2a, idx)),
      tbl,
      Equal.cong(Array<U32>, Array<U32>,
        x => Arr.Arr.fst(Array<U32>, U32, Array.get(U32, x, idx)),
        t4, t2a,
        Equal.trans(Array<U32>, t4, tbl, t2a, et4,
          Equal.sym(Array<U32>, t2a, tbl, et2a))),
      Equal.trans(Array<U32>,
        Arr.Arr.fst(Array<U32>, U32, Array.get(U32, t2a, idx)),
        t2a, tbl, efst2a, et2a))
  +ht3 = FT.tbl_ok_transport(G, C, n, tbl, t3,
           Equal.sym(Array<U32>, t3, tbl, et3), htbl)
  +wit = FT.tbl_lookup_wit(G, C, n, row, g, ci, w, t3, ht3, hrow, hcol)
  +esnd3 = Arr.Arr.dpair_l(
             {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, t3, idx))
              == FT.fb_code_words(g, w) : U32},
             Arr.Arr.DPair<{SolveFast.is_len5(g) == True{} : Bool},
                           {SolveFast.is_len5(w) == True{} : Bool}>, wit)
  +r5 = Arr.Arr.dpair_r(
          {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, t3, idx))
           == FT.fb_code_words(g, w) : U32},
          Arr.Arr.DPair<{SolveFast.is_len5(g) == True{} : Bool},
                        {SolveFast.is_len5(w) == True{} : Bool}>, wit)
  +hg5 = Arr.Arr.dpair_l({SolveFast.is_len5(g) == True{} : Bool},
           {SolveFast.is_len5(w) == True{} : Bool}, r5)
  +hw5 = Arr.Arr.dpair_r({SolveFast.is_len5(g) == True{} : Bool},
           {SolveFast.is_len5(w) == True{} : Bool}, r5)
  +esnd4 : {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, t4, idx))
            == FT.fb_code_words(g, w) : U32} =
    Equal.trans(U32,
      Arr.Arr.snd(Array<U32>, U32, Array.get(U32, t4, idx)),
      Arr.Arr.snd(Array<U32>, U32, Array.get(U32, t3, idx)),
      FT.fb_code_words(g, w),
      Equal.cong(Array<U32>, U32,
        x => Arr.Arr.snd(Array<U32>, U32, Array.get(U32, x, idx)),
        t4, t3, et4_3),
      esnd3)
  %et4 : R(Array.get(U32, _, idx))
  FT.tbl_get_unpack(R, tbl, FT.fb_code_words(g, w),
    Array.get(U32, t4, idx), efst4, esnd4,
    t_out => +code => +et_out => +ecode =>
      k(t_out, code, et_out,
        FT.tbl_ok_transport(G, C, n, tbl, t_out,
          Equal.sym(Array<U32>, t_out, tbl, et_out), htbl),
        ecode, hg5, hw5))

def FT.tbl_get_use_dup2(-R: (Array<U32> & U32) -> Data,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    +row: U32, +g: +List<Nat>, +ci: U32, +w: +List<Nat>,
    -tbl: Array<U32>, t1: Array<U32>, -t2: Array<U32>,
    +et1: {t1 == tbl : Array<U32>}, +et2: {t2 == tbl : Array<U32>},
    dp2: &t2a: Array<U32> -> &t2b: Array<U32> ->
         {t2a == t2 : Array<U32>} & {t2b == t2a : Array<U32>},
    +htbl: FT.TblOk(G, C, n, tbl),
    +hrow: {FT.gentry_ok_b(G, n, row, g) == True{} : Bool},
    +hcol: {FT.has_col_go(Groups.len_words(G), C, ci, w, 0n) == True{} : Bool},
    k: @t_out: Array<U32> -> @code: U32 ->
       {t_out == tbl : Array<U32>} ->
       FT.TblOk(G, C, n, t_out) ->
       {code == FT.fb_code_words(g, w) : U32} ->
       {SolveFast.is_len5(g) == True{} : Bool} ->
       {SolveFast.is_len5(w) == True{} : Bool} ->
       R((t_out, code))) ->
  R(Array.get(U32, tbl, U32.add(row, ci))):
  (t2a, dp3) = dp2
  (t2b, pe2) = dp3
  (+et2a_2, +et2b_2a) = pe2
  +et2a : {t2a == tbl : Array<U32>} =
    Equal.trans(Array<U32>, t2a, t2, tbl, et2a_2, et2)
  +et2b : {t2b == tbl : Array<U32>} =
    Equal.trans(Array<U32>, t2b, t2a, tbl, et2b_2a, et2a)
  FT.tbl_get_use_dup3(R, G, C, n, row, g, ci, w, tbl, t1, t2a, t2b,
    et1, et2a, et2b, Arr.Arr.dup(U32, t2b), htbl, hrow, hcol, k)

def FT.tbl_get_use_dup(-R: (Array<U32> & U32) -> Data,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    +row: U32, +g: +List<Nat>, +ci: U32, +w: +List<Nat>,
    -tbl: Array<U32>,
    dp: &t1: Array<U32> -> &t2: Array<U32> ->
        {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>},
    +htbl: FT.TblOk(G, C, n, tbl),
    +hrow: {FT.gentry_ok_b(G, n, row, g) == True{} : Bool},
    +hcol: {FT.has_col_go(Groups.len_words(G), C, ci, w, 0n) == True{} : Bool},
    k: @t_out: Array<U32> -> @code: U32 ->
       {t_out == tbl : Array<U32>} ->
       FT.TblOk(G, C, n, t_out) ->
       {code == FT.fb_code_words(g, w) : U32} ->
       {SolveFast.is_len5(g) == True{} : Bool} ->
       {SolveFast.is_len5(w) == True{} : Bool} ->
       R((t_out, code))) ->
  R(Array.get(U32, tbl, U32.add(row, ci))):
  (t1, dp2) = dp
  (t2, pe) = dp2
  (+et1, +et2_1) = pe
  +et2 : {t2 == tbl : Array<U32>} =
    Equal.trans(Array<U32>, t2, t1, tbl, et2_1, et1)
  FT.tbl_get_use_dup2(R, G, C, n, row, g, ci, w, tbl, t1, t2, et1, et2,
    Arr.Arr.dup(U32, t2), htbl, hrow, hcol, k)

def FT.tbl_get_use(-R: (Array<U32> & U32) -> Data,
    +G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    +row: U32, +g: +List<Nat>, +ci: U32, +w: +List<Nat>,
    tbl: Array<U32>,
    +htbl: FT.TblOk(G, C, n, tbl),
    +hrow: {FT.gentry_ok_b(G, n, row, g) == True{} : Bool},
    +hcol: {FT.has_col_go(Groups.len_words(G), C, ci, w, 0n) == True{} : Bool},
    k: @t_out: Array<U32> -> @code: U32 ->
       {t_out == tbl : Array<U32>} ->
       FT.TblOk(G, C, n, t_out) ->
       {code == FT.fb_code_words(g, w) : U32} ->
       {SolveFast.is_len5(g) == True{} : Bool} ->
       {SolveFast.is_len5(w) == True{} : Bool} ->
       R((t_out, code))) ->
  R(Array.get(U32, tbl, U32.add(row, ci))):
  FT.tbl_get_use_dup(R, G, C, n, row, g, ci, w, tbl, Arr.Arr.dup(U32, tbl),
    htbl, hrow, hcol, k)
