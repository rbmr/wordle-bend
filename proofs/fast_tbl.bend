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

def FT.tbl_at_step(+g: +List<Nat>, +C: +List<+List<Nat>>, +n: Nat, +idx: Nat,
    lt: Bool, rec: Nat -> U32) -> U32:
  match lt:
    case True{}:
      FT.fb_code_words(g, FT.nth_word(C, idx))
    case False{}:
      rec(Nat.sub(idx, n))

def FT.tbl_at(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
              +idx: Nat) -> U32:
  match G:
    case Nil{}:
      0
    case Con{+g, +rest}:
      FT.tbl_at_step(g, C, n, idx, Nat.is_lt(idx, n),
        idx2 => FT.tbl_at(rest, C, n, idx2))

def FT.tbl_at_head(+g: +List<Nat>, +rest: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n: Nat, +idx: Nat,
    +hlt: {Nat.is_lt(idx, n) == True{} : Bool}) ->
  {FT.tbl_at(g <> rest, C, n, idx)
   == FT.fb_code_words(g, FT.nth_word(C, idx)) : U32}:
  Equal.cong(Bool, U32,
    b => FT.tbl_at_step(g, C, n, idx, b, idx2 => FT.tbl_at(rest, C, n, idx2)),
    Nat.is_lt(idx, n), True{}, hlt)

def FT.tbl_at_tail(+g: +List<Nat>, +rest: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n: Nat, +idx: Nat,
    +hf: {Nat.is_lt(idx, n) == False{} : Bool}) ->
  {FT.tbl_at(g <> rest, C, n, idx)
   == FT.tbl_at(rest, C, n, Nat.sub(idx, n)) : U32}:
  Equal.cong(Bool, U32,
    b => FT.tbl_at_step(g, C, n, idx, b, idx2 => FT.tbl_at(rest, C, n, idx2)),
    Nat.is_lt(idx, n), False{}, hf)

# Symbolic depth-indexed `Data` invariant over `tbl: Array<U32>`.
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

def FT.tbl_at_append_g(+gpre: +List<+List<Nat>>, +g: +List<Nat>,
    +grest: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat, +c: Nat,
    +hc: {Nat.is_lt(c, n) == True{} : Bool}) ->
  {FT.tbl_at(List.append(&2, +List<Nat>, gpre, g <> grest), C, n,
     Nat.add(Nat.mul(Groups.len_words(gpre), n), c))
   == FT.fb_code_words(g, FT.nth_word(C, c)) : U32}:
  match gpre:
    case Nil{}:
      FT.tbl_at_head(g, grest, C, n, c, hc)
    case Con{+gh, +gt}:
      +idx : Nat = Nat.add(Nat.mul(Groups.len_words(gt), n), c)
      +ea : {Nat.add(Nat.add(n, Nat.mul(Groups.len_words(gt), n)), c)
             == Nat.add(n, idx) : Nat} =
        NatProof.NatPrf.add_assoc(n, Nat.mul(Groups.len_words(gt), n), c)
      +hf : {Nat.is_lt(Nat.add(n, idx), n) == False{} : Bool} =
        FT.nat_lt_add_false(n, idx)
      +esub : {Nat.sub(Nat.add(n, idx), n) == idx : Nat} =
        FT.nat_sub_add_l(n, idx)
      Equal.trans(U32,
        FT.tbl_at(gh <> List.append(&2, +List<Nat>, gt, g <> grest), C, n,
          Nat.add(Nat.add(n, Nat.mul(Groups.len_words(gt), n)), c)),
        FT.tbl_at(gh <> List.append(&2, +List<Nat>, gt, g <> grest), C, n,
          Nat.add(n, idx)),
        FT.fb_code_words(g, FT.nth_word(C, c)),
        Equal.cong(Nat, U32,
          x => FT.tbl_at(gh <> List.append(&2, +List<Nat>, gt, g <> grest), C, n, x),
          Nat.add(Nat.add(n, Nat.mul(Groups.len_words(gt), n)), c),
          Nat.add(n, idx), ea),
        Equal.trans(U32,
          FT.tbl_at(gh <> List.append(&2, +List<Nat>, gt, g <> grest), C, n,
            Nat.add(n, idx)),
          FT.tbl_at(List.append(&2, +List<Nat>, gt, g <> grest), C, n,
            Nat.sub(Nat.add(n, idx), n)),
          FT.fb_code_words(g, FT.nth_word(C, c)),
          FT.tbl_at_tail(gh, List.append(&2, +List<Nat>, gt, g <> grest), C, n,
            Nat.add(n, idx), hf),
          Equal.trans(U32,
            FT.tbl_at(List.append(&2, +List<Nat>, gt, g <> grest), C, n,
              Nat.sub(Nat.add(n, idx), n)),
            FT.tbl_at(List.append(&2, +List<Nat>, gt, g <> grest), C, n, idx),
            FT.fb_code_words(g, FT.nth_word(C, c)),
            Equal.cong(Nat, U32,
              x => FT.tbl_at(List.append(&2, +List<Nat>, gt, g <> grest), C, n, x),
              Nat.sub(Nat.add(n, idx), n), idx, esub),
            FT.tbl_at_append_g(gt, g, grest, C, n, c, hc))))

def FT.fill_tbl_row_step_dup(+d: Nat, +g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +gpre: +List<+List<Nat>>, +grest: +List<+List<Nat>>,
    +cpre: +List<+List<Nat>>, +aw: +List<Nat>, +rest: +List<+List<Nat>>,
    +n: Nat, -tbl: Array<U32>, +code: U32,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hu_lt: {Nat.is_lt(Nat.add(Nat.mul(Groups.len_words(gpre), n), Groups.len_words(cpre)),
               FT.pow2(d)) == True{} : Bool},
    +ecode: {code == FT.tbl_at(
               List.append(&2, +List<Nat>, gpre,
                 (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> grest),
               List.append(&2, +List<Nat>, cpre, aw <> rest), n,
               Nat.add(Nat.mul(Groups.len_words(gpre), n), Groups.len_words(cpre)))
             : U32},
    +ht: FT.TblTree(d, 0n, tbl,
           List.append(&2, +List<Nat>, gpre,
             (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> grest),
           List.append(&2, +List<Nat>, cpre, aw <> rest), n,
           Nat.add(Nat.mul(Groups.len_words(gpre), n), Groups.len_words(cpre))),
    dp: &t1: Array<U32> -> &t2: Array<U32> ->
        {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>},
    rec: @tbl2: Array<U32> ->
         FT.TblTree(d, 0n, tbl2,
           List.append(&2, +List<Nat>, gpre,
             (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> grest),
           List.append(&2, +List<Nat>,
             List.append(&2, +List<Nat>, cpre, aw <> Nil{}), rest), n,
           Nat.add(Nat.mul(Groups.len_words(gpre), n),
             Groups.len_words(List.append(&2, +List<Nat>, cpre, aw <> Nil{})))) ->
         FT.TblTree(d, 0n,
           SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, rest,
             U32.from_nat(Nat.add(Nat.mul(Groups.len_words(gpre), n),
               Groups.len_words(List.append(&2, +List<Nat>, cpre, aw <> Nil{})))),
             tbl2),
           List.append(&2, +List<Nat>, gpre,
             (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> grest),
           List.append(&2, +List<Nat>,
             List.append(&2, +List<Nat>, cpre, aw <> Nil{}), rest), n,
           Nat.add(Nat.mul(Groups.len_words(gpre), n), n))) ->
  FT.TblTree(d, 0n,
    SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, rest,
      U32.inc(U32.from_nat(Nat.add(Nat.mul(Groups.len_words(gpre), n),
        Groups.len_words(cpre)))),
      Array.set(U32, tbl,
        U32.from_nat(Nat.add(Nat.mul(Groups.len_words(gpre), n),
          Groups.len_words(cpre))),
        code)),
    List.append(&2, +List<Nat>, gpre,
      (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> grest),
    List.append(&2, +List<Nat>, cpre, aw <> rest), n,
    Nat.add(Nat.mul(Groups.len_words(gpre), n), n)):
  (t1, dp2) = dp
  (t2, pe) = dp2
  (+et1, +et2) = pe
  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
  +Gfull : +List<+List<Nat>> = List.append(&2, +List<Nat>, gpre, gw <> grest)
  +Cfull2 : +List<+List<Nat>> = List.append(&2, +List<Nat>, cpre, aw <> rest)
  +cpre2 : +List<+List<Nat>> = List.append(&2, +List<Nat>, cpre, aw <> Nil{})
  +base_r : Nat = Nat.mul(Groups.len_words(gpre), n)
  +ci : Nat = Groups.len_words(cpre)
  +ecfull : {List.append(&2, +List<Nat>, cpre2, rest) == Cfull2 : +List<+List<Nat>>} =
    FT.list_append_snoc(+List<Nat>, cpre, aw, rest)
  +eci2 : {Groups.len_words(cpre2) == 1n+ci : Nat} =
    Equal.trans(Nat, Groups.len_words(cpre2), Nat.add(ci, 1n), 1n+ci,
      FT.len_words_append(cpre, aw <> Nil{}), NatProof.NatPrf.add_comm(ci, 1n))
  +eidx2 : {Nat.add(base_r, Groups.len_words(cpre2)) == 1n+Nat.add(base_r, ci) : Nat} =
    Equal.trans(Nat,
      Nat.add(base_r, Groups.len_words(cpre2)),
      Nat.add(base_r, 1n+ci), 1n+Nat.add(base_r, ci),
      Equal.cong(Nat, Nat, x => Nat.add(base_r, x),
        Groups.len_words(cpre2), 1n+ci, eci2),
      NatProof.NatPrf.add_succ(base_r, ci))
  +ht_t1 = FT.tbl_tree_transport(d, 0n, tbl, t1, Gfull, Cfull2, n,
             Nat.add(base_r, ci), Equal.sym(Array<U32>, t1, tbl, et1), ht)
  +ht1_t1 = FT.tbl_tree_set(d, t1, Gfull, Cfull2, n,
              Nat.add(base_r, ci), code, hd, hu_lt, ecode, ht_t1)
  +ht1_t2 = FT.tbl_tree_transport(d, 0n,
              Array.set(U32, t1, U32.from_nat(Nat.add(base_r, ci)), code),
              Array.set(U32, t2, U32.from_nat(Nat.add(base_r, ci)), code),
              Gfull, Cfull2, n, 1n+Nat.add(base_r, ci),
              Equal.cong(Array<U32>, Array<U32>,
                x => Array.set(U32, x, U32.from_nat(Nat.add(base_r, ci)), code),
                t1, t2, Equal.sym(Array<U32>, t2, t1, et2)),
              ht1_t1)
  +ht1_c2 : FT.TblTree(d, 0n,
              Array.set(U32, t2, U32.from_nat(Nat.add(base_r, ci)), code),
              Gfull, List.append(&2, +List<Nat>, cpre2, rest),
              n, Nat.add(base_r, Groups.len_words(cpre2))) =
    %Equal.sym(+List<+List<Nat>>,
       List.append(&2, +List<Nat>, cpre2, rest), Cfull2, ecfull) :
      FT.TblTree(d, 0n,
        Array.set(U32, t2, U32.from_nat(Nat.add(base_r, ci)), code),
        Gfull, _, n, Nat.add(base_r, Groups.len_words(cpre2)))
    FT.tbl_tree_transport_upto(d, 0n,
      Array.set(U32, t2, U32.from_nat(Nat.add(base_r, ci)), code),
      Gfull, Cfull2, n, 1n+Nat.add(base_r, ci),
      Nat.add(base_r, Groups.len_words(cpre2)),
      Equal.sym(Nat, Nat.add(base_r, Groups.len_words(cpre2)),
        1n+Nat.add(base_r, ci), eidx2),
      ht1_t2)
  +hrec = rec(Array.set(U32, t2, U32.from_nat(Nat.add(base_r, ci)), code), ht1_c2)
  +eu_inc : {U32.from_nat(Nat.add(base_r, Groups.len_words(cpre2)))
             == U32.inc(U32.from_nat(Nat.add(base_r, ci))) : U32} =
    Equal.cong(Nat, U32, x => U32.from_nat(x),
      Nat.add(base_r, Groups.len_words(cpre2)), 1n+Nat.add(base_r, ci), eidx2)
  %et1 :
    FT.TblTree(d, 0n,
      SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, rest,
        U32.inc(U32.from_nat(Nat.add(base_r, ci))),
        Array.set(U32, _, U32.from_nat(Nat.add(base_r, ci)), code)),
      Gfull, Cfull2, n, Nat.add(base_r, n))
  %et2 :
    FT.TblTree(d, 0n,
      SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, rest,
        U32.inc(U32.from_nat(Nat.add(base_r, ci))),
        Array.set(U32, _, U32.from_nat(Nat.add(base_r, ci)), code)),
      Gfull, Cfull2, n, Nat.add(base_r, n))
  %ecfull :
    FT.TblTree(d, 0n,
      SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, rest,
        U32.inc(U32.from_nat(Nat.add(base_r, ci))),
        Array.set(U32, t2, U32.from_nat(Nat.add(base_r, ci)), code)),
      Gfull, _, n, Nat.add(base_r, n))
  %eu_inc :
    FT.TblTree(d, 0n,
      SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, rest, _,
        Array.set(U32, t2, U32.from_nat(Nat.add(base_r, ci)), code)),
      Gfull, List.append(&2, +List<Nat>, cpre2, rest), n, Nat.add(base_r, n))
  hrec

def FT.fill_tbl_row_ok(+crem: +List<+List<Nat>>, +d: Nat,
    +g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +gpre: +List<+List<Nat>>, +grest: +List<+List<Nat>>,
    +cpre: +List<+List<Nat>>,
    +n: Nat, tbl: Array<U32>,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +en: {Nat.add(Groups.len_words(cpre), Groups.len_words(crem)) == n : Nat},
    +hbound: {Nat.is_le(Nat.add(Nat.mul(Groups.len_words(gpre), n), n),
                FT.pow2(d)) == True{} : Bool},
    +hlen5: {SolveFast.all_len5(crem) == True{} : Bool},
    +ht: FT.TblTree(d, 0n, tbl,
           List.append(&2, +List<Nat>, gpre,
             (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> grest),
           List.append(&2, +List<Nat>, cpre, crem), n,
           Nat.add(Nat.mul(Groups.len_words(gpre), n), Groups.len_words(cpre)))) ->
  FT.TblTree(d, 0n,
    SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, crem,
      U32.from_nat(Nat.add(Nat.mul(Groups.len_words(gpre), n),
                     Groups.len_words(cpre))),
      tbl),
    List.append(&2, +List<Nat>, gpre,
      (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> grest),
    List.append(&2, +List<Nat>, cpre, crem), n,
    Nat.add(Nat.mul(Groups.len_words(gpre), n), n)):
  match crem:
    case Nil{}:
      +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
      +Gfull : +List<+List<Nat>> = List.append(&2, +List<Nat>, gpre, gw <> grest)
      +Cfull : +List<+List<Nat>> = List.append(&2, +List<Nat>, cpre, Nil{})
      +base_r : Nat = Nat.mul(Groups.len_words(gpre), n)
      +ci : Nat = Groups.len_words(cpre)
      +eci_n : {ci == n : Nat} =
        Equal.trans(Nat, ci, Nat.add(ci, 0n), n,
          Equal.sym(Nat, Nat.add(ci, 0n), ci, NatProof.NatPrf.add_zero(ci)), en)
      FT.tbl_tree_transport_upto(d, 0n, tbl, Gfull, Cfull, n,
        Nat.add(base_r, ci), Nat.add(base_r, n),
        Equal.cong(Nat, Nat, x => Nat.add(base_r, x), ci, n, eci_n), ht)
    case Con{+w, +rest}:
      match w:
        case Nil{}:
          +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
          +Gfull : +List<+List<Nat>> = List.append(&2, +List<Nat>, gpre, gw <> grest)
          +base_r : Nat = Nat.mul(Groups.len_words(gpre), n)
          +hw5 : {SolveFast.is_len5(Nil{}) == True{} : Bool} =
            FT.all_len5_head(Nil{}, rest, hlen5)
          Empty.absurd(
            FT.TblTree(d, 0n, tbl, Gfull,
              List.append(&2, +List<Nat>, cpre, Nil{} <> rest), n,
              Nat.add(base_r, n)),
            Logic.Proof.false_ne_true(hw5))
        case Con{+a0, +t1}:
          match t1:
            case Nil{}:
              +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
              +Gfull : +List<+List<Nat>> = List.append(&2, +List<Nat>, gpre, gw <> grest)
              +base_r : Nat = Nat.mul(Groups.len_words(gpre), n)
              +hw5 : {SolveFast.is_len5(a0 <> Nil{}) == True{} : Bool} =
                FT.all_len5_head(a0 <> Nil{}, rest, hlen5)
              Empty.absurd(
                FT.TblTree(d, 0n, tbl, Gfull,
                  List.append(&2, +List<Nat>, cpre, (a0 <> Nil{}) <> rest), n,
                  Nat.add(base_r, n)),
                Logic.Proof.false_ne_true(hw5))
            case Con{+a1, +t2}:
              match t2:
                case Nil{}:
                  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
                  +Gfull : +List<+List<Nat>> = List.append(&2, +List<Nat>, gpre, gw <> grest)
                  +base_r : Nat = Nat.mul(Groups.len_words(gpre), n)
                  +hw5 : {SolveFast.is_len5(a0 <> (a1 <> Nil{})) == True{} : Bool} =
                    FT.all_len5_head(a0 <> (a1 <> Nil{}), rest, hlen5)
                  Empty.absurd(
                    FT.TblTree(d, 0n, tbl, Gfull,
                      List.append(&2, +List<Nat>, cpre,
                        (a0 <> (a1 <> Nil{})) <> rest), n, Nat.add(base_r, n)),
                    Logic.Proof.false_ne_true(hw5))
                case Con{+a2, +t3}:
                  match t3:
                    case Nil{}:
                      +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
                      +Gfull : +List<+List<Nat>> = List.append(&2, +List<Nat>, gpre, gw <> grest)
                      +base_r : Nat = Nat.mul(Groups.len_words(gpre), n)
                      +hw5 : {SolveFast.is_len5(a0 <> (a1 <> (a2 <> Nil{}))) == True{} : Bool} =
                        FT.all_len5_head(a0 <> (a1 <> (a2 <> Nil{})), rest, hlen5)
                      Empty.absurd(
                        FT.TblTree(d, 0n, tbl, Gfull,
                          List.append(&2, +List<Nat>, cpre,
                            (a0 <> (a1 <> (a2 <> Nil{}))) <> rest), n,
                          Nat.add(base_r, n)),
                        Logic.Proof.false_ne_true(hw5))
                    case Con{+a3, +t4}:
                      match t4:
                        case Nil{}:
                          +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
                          +Gfull : +List<+List<Nat>> = List.append(&2, +List<Nat>, gpre, gw <> grest)
                          +base_r : Nat = Nat.mul(Groups.len_words(gpre), n)
                          +hw5 : {SolveFast.is_len5(a0 <> (a1 <> (a2 <> (a3 <> Nil{})))) == True{} : Bool} =
                            FT.all_len5_head(a0 <> (a1 <> (a2 <> (a3 <> Nil{}))), rest, hlen5)
                          Empty.absurd(
                            FT.TblTree(d, 0n, tbl, Gfull,
                              List.append(&2, +List<Nat>, cpre,
                                (a0 <> (a1 <> (a2 <> (a3 <> Nil{})))) <> rest),
                              n, Nat.add(base_r, n)),
                            Logic.Proof.false_ne_true(hw5))
                        case Con{+a4, +t5}:
                          match t5:
                            case Con{+a5, +t6}:
                              +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
                              +Gfull : +List<+List<Nat>> = List.append(&2, +List<Nat>, gpre, gw <> grest)
                              +base_r : Nat = Nat.mul(Groups.len_words(gpre), n)
                              +hw5 : {SolveFast.is_len5(a0 <> (a1 <> (a2 <> (a3 <> (a4 <> (a5 <> t6)))))) == True{} : Bool} =
                                FT.all_len5_head(a0 <> (a1 <> (a2 <> (a3 <> (a4 <> (a5 <> t6))))), rest, hlen5)
                              Empty.absurd(
                                FT.TblTree(d, 0n, tbl, Gfull,
                                  List.append(&2, +List<Nat>, cpre,
                                    (a0 <> (a1 <> (a2 <> (a3 <> (a4 <> (a5 <> t6)))))) <> rest),
                                  n, Nat.add(base_r, n)),
                                Logic.Proof.false_ne_true(hw5))
                            case Nil{}:
                              +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
                              +Gfull : +List<+List<Nat>> = List.append(&2, +List<Nat>, gpre, gw <> grest)
                              +base_r : Nat = Nat.mul(Groups.len_words(gpre), n)
                              +ci : Nat = Groups.len_words(cpre)
                              +aw : +List<Nat> =
                                a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))
                              +hr5 : {SolveFast.all_len5(rest) == True{} : Bool} =
                                FT.all_len5_tail(aw, rest, hlen5)
                              +Cfull2 : +List<+List<Nat>> =
                                List.append(&2, +List<Nat>, cpre, aw <> rest)
                              +cpre2 : +List<+List<Nat>> =
                                List.append(&2, +List<Nat>, cpre, aw <> Nil{})
                              +ecfull : {List.append(&2, +List<Nat>, cpre2, rest)
                                         == Cfull2 : +List<+List<Nat>>} =
                                FT.list_append_snoc(+List<Nat>, cpre, aw, rest)
                              +eci2 : {Groups.len_words(cpre2) == 1n+ci : Nat} =
                                Equal.trans(Nat,
                                  Groups.len_words(cpre2),
                                  Nat.add(ci, 1n), 1n+ci,
                                  FT.len_words_append(cpre, aw <> Nil{}),
                                  NatProof.NatPrf.add_comm(ci, 1n))
                              +en2 : {Nat.add(Groups.len_words(cpre2),
                                        Groups.len_words(rest)) == n : Nat} =
                                Equal.trans(Nat,
                                  Nat.add(Groups.len_words(cpre2),
                                    Groups.len_words(rest)),
                                  1n+Nat.add(ci, Groups.len_words(rest)),
                                  n,
                                  Equal.cong(Nat, Nat,
                                    x => Nat.add(x, Groups.len_words(rest)),
                                    Groups.len_words(cpre2), 1n+ci, eci2),
                                  Equal.trans(Nat,
                                    1n+Nat.add(ci, Groups.len_words(rest)),
                                    Nat.add(ci, 1n+Groups.len_words(rest)), n,
                                    Equal.sym(Nat,
                                      Nat.add(ci, 1n+Groups.len_words(rest)),
                                      1n+Nat.add(ci, Groups.len_words(rest)),
                                      NatProof.NatPrf.add_succ(ci,
                                        Groups.len_words(rest))),
                                    en))
                              +hci_lt : {Nat.is_lt(ci, n) == True{} : Bool} =
                                NatProof.Nat.is_lt_le_trans(ci, 1n+ci, n,
                                  NatProof.Nat.is_lt_succ_self(ci),
                                  NatProof.Nat.is_le_eq_r(1n+ci,
                                    Nat.add(1n+ci, Groups.len_words(rest)), n,
                                    Equal.trans(Nat,
                                      Nat.add(1n+ci, Groups.len_words(rest)),
                                      Nat.add(Groups.len_words(cpre2),
                                        Groups.len_words(rest)), n,
                                      Equal.cong(Nat, Nat,
                                        x => Nat.add(x, Groups.len_words(rest)),
                                        1n+ci, Groups.len_words(cpre2),
                                        Equal.sym(Nat, Groups.len_words(cpre2),
                                          1n+ci, eci2)),
                                      en2),
                                    FT.nat_le_add_l(1n+ci,
                                      Groups.len_words(rest))))
                              +hu_lt : {Nat.is_lt(Nat.add(base_r, ci), FT.pow2(d))
                                        == True{} : Bool} =
                                NatProof.Nat.is_lt_le_trans(
                                  Nat.add(base_r, ci), Nat.add(base_r, n),
                                  FT.pow2(d),
                                  FT.nat_lt_add_l(ci, n, base_r, hci_lt),
                                  hbound)
                              +code = SolveFast.feedback_code5(
                                        g0, g1, g2, g3, g4, a0, a1, a2, a3, a4)
                              +ecode : {code == FT.tbl_at(Gfull, Cfull2, n,
                                          Nat.add(base_r, ci)) : U32} =
                                Equal.trans(U32,
                                  code,
                                  FT.fb_code_words(gw, aw),
                                  FT.tbl_at(Gfull, Cfull2, n, Nat.add(base_r, ci)),
                                  FF5.FF5.feedback_code5_eq(
                                    g0, g1, g2, g3, g4, a0, a1, a2, a3, a4),
                                  Equal.trans(U32,
                                    FT.fb_code_words(gw, aw),
                                    FT.fb_code_words(gw, FT.nth_word(Cfull2, ci)),
                                    FT.tbl_at(Gfull, Cfull2, n, Nat.add(base_r, ci)),
                                    Equal.cong(+List<Nat>, U32,
                                      x => FT.fb_code_words(gw, x), aw,
                                      FT.nth_word(Cfull2, ci),
                                      Equal.sym(+List<Nat>,
                                        FT.nth_word(Cfull2, ci), aw,
                                        FT.nth_word_append(cpre, aw, rest))),
                                    Equal.sym(U32,
                                      FT.tbl_at(Gfull, Cfull2, n, Nat.add(base_r, ci)),
                                      FT.fb_code_words(gw, FT.nth_word(Cfull2, ci)),
                                      FT.tbl_at_append_g(gpre, gw, grest, Cfull2,
                                        n, ci, hci_lt))))
                              FT.fill_tbl_row_step_dup(d, g0, g1, g2, g3, g4,
                                gpre, grest, cpre, aw, rest, n, tbl, code,
                                hd, hu_lt, ecode, ht, Arr.Arr.dup(U32, tbl),
                                tbl2 => ht2 =>
                                  FT.fill_tbl_row_ok(rest, d, g0, g1, g2, g3, g4,
                                    gpre, grest, cpre2, n, tbl2,
                                    hd, en2, hbound, hr5, ht2))

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

def FT.fill_tbl_go_step_dup(+d: Nat, +g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +gpre: +List<+List<Nat>>, +rest: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n: Nat, -tbl: Array<U32>,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +en: {Groups.len_words(C) == n : Nat},
    +hb_row: {Nat.is_le(Nat.add(Nat.mul(Groups.len_words(gpre), n), n),
                FT.pow2(d)) == True{} : Bool},
    +hc5: {SolveFast.all_len5(C) == True{} : Bool},
    +ht: FT.TblTree(d, 0n, tbl,
           List.append(&2, +List<Nat>, gpre,
             (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> rest),
           C, n, Nat.mul(Groups.len_words(gpre), n)),
    dp: &t1: Array<U32> -> &t2: Array<U32> ->
        {t1 == tbl : Array<U32>} & {t2 == t1 : Array<U32>},
    rec: @tbl2: Array<U32> ->
         FT.TblTree(d, 0n, tbl2,
           List.append(&2, +List<Nat>,
             List.append(&2, +List<Nat>, gpre,
               (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> Nil{}), rest),
           C, n,
           Nat.mul(Groups.len_words(
             List.append(&2, +List<Nat>, gpre,
               (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> Nil{})), n)) ->
         FT.TblTree(d, 0n,
           SolveFast.fill_tbl_go(rest, C,
             U32.from_nat(Nat.mul(Groups.len_words(
               List.append(&2, +List<Nat>, gpre,
                 (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> Nil{})), n)),
             U32.from_nat(n), tbl2),
           List.append(&2, +List<Nat>,
             List.append(&2, +List<Nat>, gpre,
               (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> Nil{}), rest),
           C, n,
           Nat.mul(Groups.len_words(
             List.append(&2, +List<Nat>,
               List.append(&2, +List<Nat>, gpre,
                 (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> Nil{}), rest)), n))) ->
  FT.TblTree(d, 0n,
    SolveFast.fill_tbl_go(rest, C,
      U32.add(U32.from_nat(Nat.mul(Groups.len_words(gpre), n)), U32.from_nat(n)),
      U32.from_nat(n),
      SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, C,
        U32.from_nat(Nat.mul(Groups.len_words(gpre), n)), tbl)),
    List.append(&2, +List<Nat>, gpre,
      (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> rest),
    C, n,
    Nat.mul(Groups.len_words(
      List.append(&2, +List<Nat>, gpre,
        (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))) <> rest)), n)):
  (t1, dp2) = dp
  (t2, pe) = dp2
  (+et1, +et2) = pe
  +ri : Nat = Groups.len_words(gpre)
  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
  +Gfull2 : +List<+List<Nat>> = List.append(&2, +List<Nat>, gpre, gw <> rest)
  +gpre2 : +List<+List<Nat>> = List.append(&2, +List<Nat>, gpre, gw <> Nil{})
  +egfull : {List.append(&2, +List<Nat>, gpre2, rest) == Gfull2 : +List<+List<Nat>>} =
    FT.list_append_snoc(+List<Nat>, gpre, gw, rest)
  +eri2 : {Groups.len_words(gpre2) == 1n+ri : Nat} =
    Equal.trans(Nat, Groups.len_words(gpre2), Nat.add(ri, 1n), 1n+ri,
      FT.len_words_append(gpre, gw <> Nil{}), NatProof.NatPrf.add_comm(ri, 1n))
  +emul2 : {Nat.mul(Groups.len_words(gpre2), n) == Nat.add(Nat.mul(ri, n), n) : Nat} =
    Equal.trans(Nat,
      Nat.mul(Groups.len_words(gpre2), n),
      Nat.add(n, Nat.mul(ri, n)), Nat.add(Nat.mul(ri, n), n),
      Equal.cong(Nat, Nat, x => Nat.mul(x, n),
        Groups.len_words(gpre2), 1n+ri, eri2),
      NatProof.NatPrf.add_comm(n, Nat.mul(ri, n)))
  +ht_t1 = FT.tbl_tree_transport(d, 0n, tbl, t1, Gfull2, C, n, Nat.mul(ri, n),
             Equal.sym(Array<U32>, t1, tbl, et1), ht)
  +ht0 : FT.TblTree(d, 0n, t1, Gfull2, C, n, Nat.add(Nat.mul(ri, n), 0n)) =
    FT.tbl_tree_transport_upto(d, 0n, t1, Gfull2, C, n,
      Nat.mul(ri, n), Nat.add(Nat.mul(ri, n), 0n),
      Equal.sym(Nat, Nat.add(Nat.mul(ri, n), 0n), Nat.mul(ri, n),
        NatProof.NatPrf.add_zero(Nat.mul(ri, n))), ht_t1)
  +ht1_t1 : FT.TblTree(d, 0n,
              SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, C,
                U32.from_nat(Nat.mul(ri, n)), t1),
              Gfull2, C, n, Nat.add(Nat.mul(ri, n), n)) =
    %Equal.cong(Nat, U32, x => U32.from_nat(x),
       Nat.add(Nat.mul(ri, n), 0n), Nat.mul(ri, n),
       NatProof.NatPrf.add_zero(Nat.mul(ri, n))) :
      FT.TblTree(d, 0n,
        SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, C, _, t1),
        Gfull2, C, n, Nat.add(Nat.mul(ri, n), n))
    FT.fill_tbl_row_ok(C, d, g0, g1, g2, g3, g4, gpre, rest, Nil{}, n,
      t1, hd, en, hb_row, hc5, ht0)
  +ht1_t2 = FT.tbl_tree_transport(d, 0n,
              SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, C,
                U32.from_nat(Nat.mul(ri, n)), t1),
              SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, C,
                U32.from_nat(Nat.mul(ri, n)), t2),
              Gfull2, C, n, Nat.add(Nat.mul(ri, n), n),
              Equal.cong(Array<U32>, Array<U32>,
                x => SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, C,
                       U32.from_nat(Nat.mul(ri, n)), x),
                t1, t2, Equal.sym(Array<U32>, t2, t1, et2)),
              ht1_t1)
  +ht1_g2 : FT.TblTree(d, 0n,
              SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, C,
                U32.from_nat(Nat.mul(ri, n)), t2),
              List.append(&2, +List<Nat>, gpre2, rest),
              C, n, Nat.mul(Groups.len_words(gpre2), n)) =
    %Equal.sym(+List<+List<Nat>>,
       List.append(&2, +List<Nat>, gpre2, rest), Gfull2, egfull) :
      FT.TblTree(d, 0n,
        SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, C,
          U32.from_nat(Nat.mul(ri, n)), t2),
        _, C, n, Nat.mul(Groups.len_words(gpre2), n))
    FT.tbl_tree_transport_upto(d, 0n,
      SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, C,
        U32.from_nat(Nat.mul(ri, n)), t2),
      Gfull2, C, n, Nat.add(Nat.mul(ri, n), n),
      Nat.mul(Groups.len_words(gpre2), n),
      Equal.sym(Nat, Nat.mul(Groups.len_words(gpre2), n),
        Nat.add(Nat.mul(ri, n), n), emul2),
      ht1_t2)
  +hrec = rec(
            SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, C,
              U32.from_nat(Nat.mul(ri, n)), t2),
            ht1_g2)
  +eu_add : {U32.from_nat(Nat.mul(Groups.len_words(gpre2), n))
             == U32.add(U32.from_nat(Nat.mul(ri, n)), U32.from_nat(n)) : U32} =
    Equal.trans(U32,
      U32.from_nat(Nat.mul(Groups.len_words(gpre2), n)),
      U32.from_nat(Nat.add(Nat.mul(ri, n), n)),
      U32.add(U32.from_nat(Nat.mul(ri, n)), U32.from_nat(n)),
      Equal.cong(Nat, U32, x => U32.from_nat(x),
        Nat.mul(Groups.len_words(gpre2), n), Nat.add(Nat.mul(ri, n), n), emul2),
      Equal.sym(U32,
        U32.add(U32.from_nat(Nat.mul(ri, n)), U32.from_nat(n)),
        U32.from_nat(Nat.add(Nat.mul(ri, n), n)),
        FT.u32_add_from_nat(Nat.mul(ri, n), n)))
  %et1 :
    FT.TblTree(d, 0n,
      SolveFast.fill_tbl_go(rest, C,
        U32.add(U32.from_nat(Nat.mul(ri, n)), U32.from_nat(n)),
        U32.from_nat(n),
        SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, C,
          U32.from_nat(Nat.mul(ri, n)), _)),
      Gfull2, C, n, Nat.mul(Groups.len_words(Gfull2), n))
  %et2 :
    FT.TblTree(d, 0n,
      SolveFast.fill_tbl_go(rest, C,
        U32.add(U32.from_nat(Nat.mul(ri, n)), U32.from_nat(n)),
        U32.from_nat(n),
        SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, C,
          U32.from_nat(Nat.mul(ri, n)), _)),
      Gfull2, C, n, Nat.mul(Groups.len_words(Gfull2), n))
  %egfull :
    FT.TblTree(d, 0n,
      SolveFast.fill_tbl_go(rest, C,
        U32.add(U32.from_nat(Nat.mul(ri, n)), U32.from_nat(n)),
        U32.from_nat(n),
        SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, C,
          U32.from_nat(Nat.mul(ri, n)), t2)),
      _, C, n, Nat.mul(Groups.len_words(_), n))
  %eu_add :
    FT.TblTree(d, 0n,
      SolveFast.fill_tbl_go(rest, C, _, U32.from_nat(n),
        SolveFast.fill_tbl_row(g0, g1, g2, g3, g4, C,
          U32.from_nat(Nat.mul(ri, n)), t2)),
      List.append(&2, +List<Nat>, gpre2, rest), C, n,
      Nat.mul(Groups.len_words(List.append(&2, +List<Nat>, gpre2, rest)), n))
  hrec

def FT.fill_tbl_go_ok(+grem: +List<+List<Nat>>, +d: Nat, +gpre: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n: Nat, tbl: Array<U32>,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +en: {Groups.len_words(C) == n : Nat},
    +hbound: {Nat.is_le(
                Nat.mul(Groups.len_words(List.append(&2, +List<Nat>, gpre, grem)), n),
                FT.pow2(d)) == True{} : Bool},
    +hg5: {SolveFast.all_len5(grem) == True{} : Bool},
    +hc5: {SolveFast.all_len5(C) == True{} : Bool},
    +ht: FT.TblTree(d, 0n, tbl,
           List.append(&2, +List<Nat>, gpre, grem), C, n,
           Nat.mul(Groups.len_words(gpre), n))) ->
  FT.TblTree(d, 0n,
    SolveFast.fill_tbl_go(grem, C,
      U32.from_nat(Nat.mul(Groups.len_words(gpre), n)), U32.from_nat(n), tbl),
    List.append(&2, +List<Nat>, gpre, grem), C, n,
    Nat.mul(Groups.len_words(List.append(&2, +List<Nat>, gpre, grem)), n)):
  match grem:
    case Nil{}:
      +Gfull : +List<+List<Nat>> = List.append(&2, +List<Nat>, gpre, Nil{})
      +ri : Nat = Groups.len_words(gpre)
      +elen : {Groups.len_words(List.append(&2, +List<Nat>, gpre, Nil{}))
               == ri : Nat} =
        Equal.trans(Nat,
          Groups.len_words(List.append(&2, +List<Nat>, gpre, Nil{})),
          Nat.add(ri, 0n), ri,
          FT.len_words_append(gpre, Nil{}),
          NatProof.NatPrf.add_zero(ri))
      FT.tbl_tree_transport_upto(d, 0n, tbl, Gfull, C, n,
        Nat.mul(ri, n), Nat.mul(Groups.len_words(Gfull), n),
        Equal.cong(Nat, Nat, x => Nat.mul(x, n), ri, Groups.len_words(Gfull),
          Equal.sym(Nat, Groups.len_words(Gfull), ri, elen)),
        ht)
    case Con{+g, +rest}:
      match g:
        case Nil{}:
          +hgw5 : {SolveFast.is_len5(Nil{}) == True{} : Bool} =
            FT.all_len5_head(Nil{}, rest, hg5)
          Empty.absurd(
            FT.TblTree(d, 0n, tbl,
              List.append(&2, +List<Nat>, gpre, Nil{} <> rest), C, n,
              Nat.mul(Groups.len_words(
                List.append(&2, +List<Nat>, gpre, Nil{} <> rest)), n)),
            Logic.Proof.false_ne_true(hgw5))
        case Con{+g0, +t1}:
          match t1:
            case Nil{}:
              +hgw5 : {SolveFast.is_len5(g0 <> Nil{}) == True{} : Bool} =
                FT.all_len5_head(g0 <> Nil{}, rest, hg5)
              Empty.absurd(
                FT.TblTree(d, 0n, tbl,
                  List.append(&2, +List<Nat>, gpre, (g0 <> Nil{}) <> rest), C, n,
                  Nat.mul(Groups.len_words(
                    List.append(&2, +List<Nat>, gpre, (g0 <> Nil{}) <> rest)), n)),
                Logic.Proof.false_ne_true(hgw5))
            case Con{+g1, +t2}:
              match t2:
                case Nil{}:
                  +hgw5 : {SolveFast.is_len5(g0 <> (g1 <> Nil{})) == True{} : Bool} =
                    FT.all_len5_head(g0 <> (g1 <> Nil{}), rest, hg5)
                  Empty.absurd(
                    FT.TblTree(d, 0n, tbl,
                      List.append(&2, +List<Nat>, gpre,
                        (g0 <> (g1 <> Nil{})) <> rest), C, n,
                      Nat.mul(Groups.len_words(
                        List.append(&2, +List<Nat>, gpre,
                          (g0 <> (g1 <> Nil{})) <> rest)), n)),
                    Logic.Proof.false_ne_true(hgw5))
                case Con{+g2, +t3}:
                  match t3:
                    case Nil{}:
                      +hgw5 : {SolveFast.is_len5(g0 <> (g1 <> (g2 <> Nil{}))) == True{} : Bool} =
                        FT.all_len5_head(g0 <> (g1 <> (g2 <> Nil{})), rest, hg5)
                      Empty.absurd(
                        FT.TblTree(d, 0n, tbl,
                          List.append(&2, +List<Nat>, gpre,
                            (g0 <> (g1 <> (g2 <> Nil{}))) <> rest), C, n,
                          Nat.mul(Groups.len_words(
                            List.append(&2, +List<Nat>, gpre,
                              (g0 <> (g1 <> (g2 <> Nil{}))) <> rest)), n)),
                        Logic.Proof.false_ne_true(hgw5))
                    case Con{+g3, +t4}:
                      match t4:
                        case Nil{}:
                          +hgw5 : {SolveFast.is_len5(g0 <> (g1 <> (g2 <> (g3 <> Nil{})))) == True{} : Bool} =
                            FT.all_len5_head(g0 <> (g1 <> (g2 <> (g3 <> Nil{}))), rest, hg5)
                          Empty.absurd(
                            FT.TblTree(d, 0n, tbl,
                              List.append(&2, +List<Nat>, gpre,
                                (g0 <> (g1 <> (g2 <> (g3 <> Nil{})))) <> rest),
                              C, n,
                              Nat.mul(Groups.len_words(
                                List.append(&2, +List<Nat>, gpre,
                                  (g0 <> (g1 <> (g2 <> (g3 <> Nil{})))) <> rest)), n)),
                            Logic.Proof.false_ne_true(hgw5))
                        case Con{+g4, +t5}:
                          match t5:
                            case Con{+g5, +t6}:
                              +hgw5 : {SolveFast.is_len5(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> (g5 <> t6)))))) == True{} : Bool} =
                                FT.all_len5_head(g0 <> (g1 <> (g2 <> (g3 <> (g4 <> (g5 <> t6))))), rest, hg5)
                              Empty.absurd(
                                FT.TblTree(d, 0n, tbl,
                                  List.append(&2, +List<Nat>, gpre,
                                    (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> (g5 <> t6)))))) <> rest),
                                  C, n,
                                  Nat.mul(Groups.len_words(
                                    List.append(&2, +List<Nat>, gpre,
                                      (g0 <> (g1 <> (g2 <> (g3 <> (g4 <> (g5 <> t6)))))) <> rest)), n)),
                                Logic.Proof.false_ne_true(hgw5))
                            case Nil{}:
                              +ri : Nat = Groups.len_words(gpre)
                              +gw : +List<Nat> =
                                g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
                              +hgr5 : {SolveFast.all_len5(rest) == True{} : Bool} =
                                FT.all_len5_tail(gw, rest, hg5)
                              +Gfull2 : +List<+List<Nat>> =
                                List.append(&2, +List<Nat>, gpre, gw <> rest)
                              +gpre2 : +List<+List<Nat>> =
                                List.append(&2, +List<Nat>, gpre, gw <> Nil{})
                              +egfull : {List.append(&2, +List<Nat>, gpre2, rest)
                                         == Gfull2 : +List<+List<Nat>>} =
                                FT.list_append_snoc(+List<Nat>, gpre, gw, rest)
                              +eri2 : {Groups.len_words(gpre2) == 1n+ri : Nat} =
                                Equal.trans(Nat,
                                  Groups.len_words(gpre2), Nat.add(ri, 1n),
                                  1n+ri,
                                  FT.len_words_append(gpre, gw <> Nil{}),
                                  NatProof.NatPrf.add_comm(ri, 1n))
                              +emul2 : {Nat.mul(Groups.len_words(gpre2), n)
                                        == Nat.add(Nat.mul(ri, n), n) : Nat} =
                                Equal.trans(Nat,
                                  Nat.mul(Groups.len_words(gpre2), n),
                                  Nat.add(n, Nat.mul(ri, n)),
                                  Nat.add(Nat.mul(ri, n), n),
                                  Equal.cong(Nat, Nat, x => Nat.mul(x, n),
                                    Groups.len_words(gpre2), 1n+ri, eri2),
                                  NatProof.NatPrf.add_comm(n, Nat.mul(ri, n)))
                              +elen_full : {Groups.len_words(Gfull2)
                                            == Nat.add(Groups.len_words(gpre2),
                                                 Groups.len_words(rest)) : Nat} =
                                Equal.trans(Nat,
                                  Groups.len_words(Gfull2),
                                  Groups.len_words(
                                    List.append(&2, +List<Nat>, gpre2, rest)),
                                  Nat.add(Groups.len_words(gpre2),
                                    Groups.len_words(rest)),
                                  Equal.cong(+List<+List<Nat>>, Nat,
                                    l => Groups.len_words(l), Gfull2,
                                    List.append(&2, +List<Nat>, gpre2, rest),
                                    Equal.sym(+List<+List<Nat>>,
                                      List.append(&2, +List<Nat>, gpre2, rest),
                                      Gfull2, egfull)),
                                  FT.len_words_append(gpre2, rest))
                              +emul_full : {Nat.mul(Groups.len_words(Gfull2), n)
                                            == Nat.add(
                                                 Nat.mul(Groups.len_words(gpre2), n),
                                                 Nat.mul(Groups.len_words(rest), n))
                                            : Nat} =
                                Equal.trans(Nat,
                                  Nat.mul(Groups.len_words(Gfull2), n),
                                  Nat.mul(
                                    Nat.add(Groups.len_words(gpre2),
                                      Groups.len_words(rest)), n),
                                  Nat.add(Nat.mul(Groups.len_words(gpre2), n),
                                    Nat.mul(Groups.len_words(rest), n)),
                                  Equal.cong(Nat, Nat, x => Nat.mul(x, n),
                                    Groups.len_words(Gfull2),
                                    Nat.add(Groups.len_words(gpre2),
                                      Groups.len_words(rest)),
                                    elen_full),
                                  FT.mul_add_r(Groups.len_words(gpre2),
                                    Groups.len_words(rest), n))
                              +hb_row : {Nat.is_le(Nat.add(Nat.mul(ri, n), n),
                                           FT.pow2(d)) == True{} : Bool} =
                                NatProof.Nat.is_le_trans(
                                  Nat.add(Nat.mul(ri, n), n),
                                  Nat.mul(Groups.len_words(Gfull2), n),
                                  FT.pow2(d),
                                  NatProof.Nat.is_le_eq_l(
                                    Nat.mul(Groups.len_words(Gfull2), n),
                                    Nat.mul(Groups.len_words(gpre2), n),
                                    Nat.add(Nat.mul(ri, n), n), emul2,
                                    NatProof.Nat.is_le_eq_r(
                                      Nat.mul(Groups.len_words(gpre2), n),
                                      Nat.add(
                                        Nat.mul(Groups.len_words(gpre2), n),
                                        Nat.mul(Groups.len_words(rest), n)),
                                      Nat.mul(Groups.len_words(Gfull2), n),
                                      Equal.sym(Nat,
                                        Nat.mul(Groups.len_words(Gfull2), n),
                                        Nat.add(
                                          Nat.mul(Groups.len_words(gpre2), n),
                                          Nat.mul(Groups.len_words(rest), n)),
                                        emul_full),
                                      FT.nat_le_add_l(
                                        Nat.mul(Groups.len_words(gpre2), n),
                                        Nat.mul(Groups.len_words(rest), n)))),
                                  hbound)
                              +hb2 : {Nat.is_le(
                                        Nat.mul(Groups.len_words(
                                          List.append(&2, +List<Nat>, gpre2, rest)), n),
                                        FT.pow2(d)) == True{} : Bool} =
                                NatProof.Nat.is_le_eq_l(FT.pow2(d),
                                  Nat.mul(Groups.len_words(Gfull2), n),
                                  Nat.mul(Groups.len_words(
                                    List.append(&2, +List<Nat>, gpre2, rest)), n),
                                  Equal.cong(+List<+List<Nat>>, Nat,
                                    l => Nat.mul(Groups.len_words(l), n), Gfull2,
                                    List.append(&2, +List<Nat>, gpre2, rest),
                                    Equal.sym(+List<+List<Nat>>,
                                      List.append(&2, +List<Nat>, gpre2, rest),
                                      Gfull2, egfull)),
                                  hbound)
                              FT.fill_tbl_go_step_dup(d, g0, g1, g2, g3, g4,
                                gpre, rest, C, n, tbl, hd, en, hb_row, hc5, ht,
                                Arr.Arr.dup(U32, tbl),
                                tbl2 => ht2 =>
                                  FT.fill_tbl_go_ok(rest, d, gpre2, C, n,
                                    tbl2, hd, en, hb2, hgr5, hc5, ht2))

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
    SolveFast.fill_tbl_go(G, C, 0, U32.from_nat(n), Array.new(U32, d, 0))):
  +ht = FT.fill_tbl_go_ok(G, d, Nil{}, C, n, Array.new(U32, d, 0),
          hd, en, hb, hg5, hc5, FT.tbl_tree_new(d, 0n, G, C, n))
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
                SolveFast.fill_tbl_go(G, C, 0, U32.from_nat(n),
                  Array.new(U32, d, 0)),
                G, C, n, Nat.mul(Groups.len_words(G), n))>>>>>
  Arr.DPair{hd, Arr.DPair{hb, Arr.DPair{en, Arr.DPair{hg5, Arr.DPair{hc5, ht}}}}}

# ---------------------------------------------------------------------------
# Section 6: Pure `Bool` validity for `CWord`, guess rows, and `FT.tbl_lookup_eq`
# ---------------------------------------------------------------------------

def FT.has_col_go(+C: +List<+List<Nat>>, +ci: U32, +w: +List<Nat>,
                  +cur: Nat) -> Bool:
  match C:
    case Nil{}:
      False{}
    case Con{h, rest}:
      Bool.or(
        Bool.and(U32.is_eq(ci, U32.from_nat(cur)), Feedback.word_eq(w, h)),
        FT.has_col_go(rest, ci, w, 1n+cur))

def FT.has_grow_go(+G: +List<+List<Nat>>, +n: Nat, +row: U32,
                   +g: +List<Nat>, +cur: Nat) -> Bool:
  match G:
    case Nil{}:
      False{}
    case Con{h, rest}:
      Bool.or(
        Bool.and(U32.is_eq(row, U32.from_nat(cur)), Feedback.word_eq(g, h)),
        FT.has_grow_go(rest, n, row, g, Nat.add(cur, n)))

def FT.gentry_ok_b(+G: +List<+List<Nat>>, +n: Nat, +row: U32,
                   +g: +List<Nat>) -> Bool:
  FT.has_grow_go(G, n, row, g, 0n)

def FT.cword_ok_b(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
                  cw: SolveFast.CWord) -> Bool:
  match cw:
    case SolveFast.CWord{ci, grow, +w}:
      Bool.and(FT.has_col_go(C, ci, w, 0n), FT.gentry_ok_b(G, n, grow, w))

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

# Extract column witness `(col, ci == from_nat(col), w == nth_word(C, col), col < len(C), is_len5(w))`.
type FT.ColWit<+C: +List<+List<Nat>>, +ci: U32, +w: +List<Nat>> is Data:
  ColWit{col: Nat,
         eci: {ci == U32.from_nat(col) : U32},
         ew: {w == FT.nth_word(C, col) : +List<Nat>},
         hlt: {Nat.is_lt(col, Groups.len_words(C)) == True{} : Bool},
         h5: {SolveFast.is_len5(w) == True{} : Bool}}

def FT.col_wit_go(+crem: +List<+List<Nat>>, +cpre: +List<+List<Nat>>,
    +ci: U32, +w: +List<Nat>,
    +h5: {SolveFast.all_len5(crem) == True{} : Bool},
    +h: {FT.has_col_go(crem, ci, w, Groups.len_words(cpre)) == True{} : Bool}) ->
  FT.ColWit<List.append(&2, +List<Nat>, cpre, crem), ci, w>:
  match crem:
    case Nil{}:
      Empty.absurd(FT.ColWit<List.append(&2, +List<Nat>, cpre, Nil{}), ci, w>,
        Logic.Proof.false_ne_true(h))
    case Con{+ch, +ct}:
      +hh5 : {SolveFast.is_len5(ch) == True{} : Bool} =
        FT.all_len5_head(ch, ct, h5)
      +ht5 : {SolveFast.all_len5(ct) == True{} : Bool} =
        FT.all_len5_tail(ch, ct, h5)
      +cur : Nat = Groups.len_words(cpre)
      FT.bool_or_elim_go(
        FT.ColWit<List.append(&2, +List<Nat>, cpre, ch <> ct), ci, w>,
        Bool.and(U32.is_eq(ci, U32.from_nat(cur)), Feedback.word_eq(w, ch)),
        FT.has_col_go(ct, ci, w, 1n+cur), h,
        +hl =>
          +eci : {ci == U32.from_nat(cur) : U32} =
            Arr.Arr.u32_is_eq_true(ci, U32.from_nat(cur),
              Logic.Proof.and_true_l(U32.is_eq(ci, U32.from_nat(cur)),
                Feedback.word_eq(w, ch), hl))
          +ewh : {w == ch : +List<Nat>} =
            CoverList.Cover.word_eq_true(w, ch,
              Logic.Proof.and_true_r(U32.is_eq(ci, U32.from_nat(cur)),
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
          +hr2 : {FT.has_col_go(ct, ci, w, Groups.len_words(cpre2))
                  == True{} : Bool} =
            Equal.trans(Bool,
              FT.has_col_go(ct, ci, w, Groups.len_words(cpre2)),
              FT.has_col_go(ct, ci, w, 1n+cur), True{},
              Equal.cong(Nat, Bool, x => FT.has_col_go(ct, ci, w, x),
                Groups.len_words(cpre2), 1n+cur, el2),
              hr)
          %ec2 : FT.ColWit<_, ci, w>
          FT.col_wit_go(ct, cpre2, ci, w, ht5, hr2))

# Extract guess-row witness `(r_idx, row == from_nat(r_idx * n), r_idx < len(G), tbl_at(...) == fb_code_words(g, nth_word(C, col)), is_len5(g))`.
type FT.RowWit<+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
               +row: U32, +g: +List<Nat>, +col: Nat> is Data:
  RowWit{idx: Nat,
         erow: {row == U32.from_nat(idx) : U32},
         hlt: {Nat.is_lt(Nat.add(idx, col), Nat.mul(Groups.len_words(G), n))
               == True{} : Bool},
         etbl: {FT.tbl_at(G, C, n, Nat.add(idx, col))
                == FT.fb_code_words(g, FT.nth_word(C, col)) : U32},
         h5: {SolveFast.is_len5(g) == True{} : Bool}}

def FT.row_wit_go(+grem: +List<+List<Nat>>, +gpre: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +n: Nat, +row: U32, +g: +List<Nat>, +col: Nat,
    +hcol: {Nat.is_lt(col, n) == True{} : Bool},
    +h5: {SolveFast.all_len5(grem) == True{} : Bool},
    +h: {FT.has_grow_go(grem, n, row, g,
           Nat.mul(Groups.len_words(gpre), n)) == True{} : Bool}) ->
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
      +cur : Nat = Nat.mul(ri, n)
      FT.bool_or_elim_go(
        FT.RowWit<List.append(&2, +List<Nat>, gpre, gh <> gt), C, n, row, g, col>,
        Bool.and(U32.is_eq(row, U32.from_nat(cur)), Feedback.word_eq(g, gh)),
        FT.has_grow_go(gt, n, row, g, Nat.add(cur, n)), h,
        +hl =>
          +erow : {row == U32.from_nat(cur) : U32} =
            Arr.Arr.u32_is_eq_true(row, U32.from_nat(cur),
              Logic.Proof.and_true_l(U32.is_eq(row, U32.from_nat(cur)),
                Feedback.word_eq(g, gh), hl))
          +egh : {g == gh : +List<Nat>} =
            CoverList.Cover.word_eq_true(g, gh,
              Logic.Proof.and_true_r(U32.is_eq(row, U32.from_nat(cur)),
                Feedback.word_eq(g, gh), hl))
          +Gfull = List.append(&2, +List<Nat>, gpre, gh <> gt)
          +elen : {Groups.len_words(Gfull)
                   == Nat.add(ri, 1n+Groups.len_words(gt)) : Nat} =
            FT.len_words_append(gpre, gh <> gt)
          +emul : {Nat.mul(Groups.len_words(Gfull), n)
                   == Nat.add(cur, Nat.add(n, Nat.mul(Groups.len_words(gt), n)))
                   : Nat} =
            Equal.trans(Nat,
              Nat.mul(Groups.len_words(Gfull), n),
              Nat.mul(Nat.add(ri, 1n+Groups.len_words(gt)), n),
              Nat.add(cur, Nat.add(n, Nat.mul(Groups.len_words(gt), n))),
              Equal.cong(Nat, Nat, x => Nat.mul(x, n),
                Groups.len_words(Gfull), Nat.add(ri, 1n+Groups.len_words(gt)),
                elen),
              FT.mul_add_r(ri, 1n+Groups.len_words(gt), n))
          +hlt : {Nat.is_lt(Nat.add(cur, col),
                    Nat.mul(Groups.len_words(Gfull), n)) == True{} : Bool} =
            Equal.trans(Bool,
              Nat.is_lt(Nat.add(cur, col), Nat.mul(Groups.len_words(Gfull), n)),
              Nat.is_lt(Nat.add(cur, col),
                Nat.add(cur, Nat.add(n, Nat.mul(Groups.len_words(gt), n)))),
              True{},
              Equal.cong(Nat, Bool, x => Nat.is_lt(Nat.add(cur, col), x),
                Nat.mul(Groups.len_words(Gfull), n),
                Nat.add(cur, Nat.add(n, Nat.mul(Groups.len_words(gt), n))),
                emul),
              FT.nat_lt_add_l(col,
                Nat.add(n, Nat.mul(Groups.len_words(gt), n)), cur,
                NatProof.Nat.is_lt_le_trans(col, n,
                  Nat.add(n, Nat.mul(Groups.len_words(gt), n)), hcol,
                  FT.nat_le_add_l(n, Nat.mul(Groups.len_words(gt), n)))))
          +etbl : {FT.tbl_at(Gfull, C, n, Nat.add(cur, col))
                   == FT.fb_code_words(g, FT.nth_word(C, col)) : U32} =
            Equal.trans(U32,
              FT.tbl_at(Gfull, C, n, Nat.add(cur, col)),
              FT.fb_code_words(gh, FT.nth_word(C, col)),
              FT.fb_code_words(g, FT.nth_word(C, col)),
              FT.tbl_at_append_g(gpre, gh, gt, C, n, col, hcol),
              Equal.cong(+List<Nat>, U32,
                x => FT.fb_code_words(x, FT.nth_word(C, col)), gh, g,
                Equal.sym(+List<Nat>, g, gh, egh)))
          +hg5 : {SolveFast.is_len5(g) == True{} : Bool} =
            Equal.trans(Bool, SolveFast.is_len5(g), SolveFast.is_len5(gh),
              True{},
              Equal.cong(+List<Nat>, Bool, x => SolveFast.is_len5(x), g, gh, egh),
              hh5)
          RowWit{cur, erow, hlt, etbl, hg5},
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
          +em2 : {Nat.mul(Groups.len_words(gpre2), n) == Nat.add(cur, n) : Nat} =
            Equal.trans(Nat,
              Nat.mul(Groups.len_words(gpre2), n),
              Nat.add(n, cur), Nat.add(cur, n),
              Equal.cong(Nat, Nat, x => Nat.mul(x, n),
                Groups.len_words(gpre2), 1n+ri, el2),
              NatProof.NatPrf.add_comm(n, cur))
          +hr2 : {FT.has_grow_go(gt, n, row, g,
                    Nat.mul(Groups.len_words(gpre2), n)) == True{} : Bool} =
            Equal.trans(Bool,
              FT.has_grow_go(gt, n, row, g, Nat.mul(Groups.len_words(gpre2), n)),
              FT.has_grow_go(gt, n, row, g, Nat.add(cur, n)), True{},
              Equal.cong(Nat, Bool, x => FT.has_grow_go(gt, n, row, g, x),
                Nat.mul(Groups.len_words(gpre2), n), Nat.add(cur, n), em2),
              hr)
          %eg2 : FT.RowWit<_, C, n, row, g, col>
          FT.row_wit_go(gt, gpre2, C, n, row, g, col, hcol, ht5, hr2))

# Main table lookup theorem: returns exact feedback code plus length-5 witnesses.
def FT.tbl_lookup_use_row(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    +d: Nat, +upto: Nat, +row: U32, +g: +List<Nat>, +ci: U32, +w: +List<Nat>,
    tbl: Array<U32>,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hb: {Nat.is_le(upto, FT.pow2(d)) == True{} : Bool},
    +ht: FT.TblTree(d, 0n, tbl, G, C, n, upto),
    +eupto: {upto == Nat.mul(Groups.len_words(G), n) : Nat},
    +col: Nat,
    +eci: {ci == U32.from_nat(col) : U32},
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
      +k : Nat = Nat.add(idx, col)
      +eadd : {U32.add(row, ci) == U32.from_nat(k) : U32} =
        Equal.trans(U32,
          U32.add(row, ci),
          U32.add(U32.from_nat(idx), U32.from_nat(col)),
          U32.from_nat(k),
          Equal.trans(U32,
            U32.add(row, ci),
            U32.add(U32.from_nat(idx), ci),
            U32.add(U32.from_nat(idx), U32.from_nat(col)),
            Equal.cong(U32, U32, x => U32.add(x, ci), row, U32.from_nat(idx),
              erow),
            Equal.cong(U32, U32, y => U32.add(U32.from_nat(idx), y), ci,
              U32.from_nat(col), eci)),
          FT.u32_add_from_nat(idx, col))
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
    cwit: FT.ColWit<C, ci, w>) ->
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
      +rwit = FT.row_wit_go(G, Nil{}, C, n, row, g, col, hcol_n, hg5, hrow)
      FT.tbl_lookup_use_row(G, C, n, d, upto, row, g, ci, w, tbl,
        hd, hb, ht, eupto, col, eci, ew, hw5, rwit)

def FT.tbl_lookup_wit(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    +row: U32, +g: +List<Nat>, +ci: U32, +w: +List<Nat>, tbl: Array<U32>,
    +htbl: FT.TblOk(G, C, n, tbl),
    +hrow: {FT.gentry_ok_b(G, n, row, g) == True{} : Bool},
    +hcol: {FT.has_col_go(C, ci, w, 0n) == True{} : Bool}) ->
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
  +cwit = FT.col_wit_go(C, Nil{}, ci, w, hc5, hcol)
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
     SolveFast.find_grow_go(w, G, U32.from_nat(cur), U32.from_nat(n), hit),
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
                              Nat.add(cur, n))),
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
          +eadd : {U32.add(U32.from_nat(cur), U32.from_nat(n))
                   == U32.from_nat(Nat.add(cur, n)) : U32} =
            FT.u32_add_from_nat(cur, n)
          +ih : {FT.has_grow_go(gt, n,
                   SolveFast.find_grow_go(w, gt,
                     U32.from_nat(Nat.add(cur, n)), U32.from_nat(n),
                     SolveFast.next_word_hit(w, gt)),
                   w, Nat.add(cur, n)) == True{} : Bool} =
            FT.find_grow_go_ok(w, gt, n, Nat.add(cur, n),
              SolveFast.next_word_hit(w, gt), {==}, hmem_t)
          +ih2 : {FT.has_grow_go(gt, n,
                    SolveFast.find_grow_go(w, gt,
                      U32.add(U32.from_nat(cur), U32.from_nat(n)),
                      U32.from_nat(n), SolveFast.next_word_hit(w, gt)),
                    w, Nat.add(cur, n)) == True{} : Bool} =
            Equal.trans(Bool,
              FT.has_grow_go(gt, n,
                SolveFast.find_grow_go(w, gt,
                  U32.add(U32.from_nat(cur), U32.from_nat(n)),
                  U32.from_nat(n), SolveFast.next_word_hit(w, gt)),
                w, Nat.add(cur, n)),
              FT.has_grow_go(gt, n,
                SolveFast.find_grow_go(w, gt,
                  U32.from_nat(Nat.add(cur, n)),
                  U32.from_nat(n), SolveFast.next_word_hit(w, gt)),
                w, Nat.add(cur, n)),
              True{},
              Equal.cong(U32, Bool,
                u => FT.has_grow_go(gt, n,
                       SolveFast.find_grow_go(w, gt, u, U32.from_nat(n),
                         SolveFast.next_word_hit(w, gt)),
                       w, Nat.add(cur, n)),
                U32.add(U32.from_nat(cur), U32.from_nat(n)),
                U32.from_nat(Nat.add(cur, n)), eadd),
              ih)
          FT.bool_or_r(
            Bool.and(
              U32.is_eq(
                SolveFast.find_grow_go(w, gt,
                  U32.add(U32.from_nat(cur), U32.from_nat(n)),
                  U32.from_nat(n), SolveFast.next_word_hit(w, gt)),
                U32.from_nat(cur)),
              Feedback.word_eq(w, gh)),
            FT.has_grow_go(gt, n,
              SolveFast.find_grow_go(w, gt,
                U32.add(U32.from_nat(cur), U32.from_nat(n)),
                U32.from_nat(n), SolveFast.next_word_hit(w, gt)),
              w, Nat.add(cur, n)),
            ih2)

def FT.find_grow_ok(+w: +List<Nat>, +G: +List<+List<Nat>>, +n: Nat,
    +hmem: {Tree.member_word(w, G) == True{} : Bool}) ->
  {FT.gentry_ok_b(G, n, SolveFast.find_grow(w, G, U32.from_nat(n)), w)
   == True{} : Bool}:
  FT.find_grow_go_ok(w, G, n, 0n, SolveFast.next_word_hit(w, G), {==}, hmem)

def FT.has_col_append_r(+cpre: +List<+List<Nat>>, +crem: +List<+List<Nat>>,
    +ci: U32, +w: +List<Nat>, +cur: Nat,
    +h: {FT.has_col_go(crem, ci, w, Nat.add(cur, Groups.len_words(cpre)))
         == True{} : Bool}) ->
  {FT.has_col_go(List.append(&2, +List<Nat>, cpre, crem), ci, w, cur)
   == True{} : Bool}:
  match cpre:
    case Nil{}:
      Equal.trans(Bool,
        FT.has_col_go(crem, ci, w, cur),
        FT.has_col_go(crem, ci, w, Nat.add(cur, 0n)), True{},
        Equal.cong(Nat, Bool, x => FT.has_col_go(crem, ci, w, x),
          cur, Nat.add(cur, 0n),
          Equal.sym(Nat, Nat.add(cur, 0n), cur, NatProof.NatPrf.add_zero(cur))),
        h)
    case Con{+ch, +ct}:
      +h2 : {FT.has_col_go(crem, ci, w,
               Nat.add(1n+cur, Groups.len_words(ct))) == True{} : Bool} =
        Equal.trans(Bool,
          FT.has_col_go(crem, ci, w, Nat.add(1n+cur, Groups.len_words(ct))),
          FT.has_col_go(crem, ci, w, Nat.add(cur, 1n+Groups.len_words(ct))),
          True{},
          Equal.cong(Nat, Bool, x => FT.has_col_go(crem, ci, w, x),
            1n+Nat.add(cur, Groups.len_words(ct)),
            Nat.add(cur, 1n+Groups.len_words(ct)),
            Equal.sym(Nat, Nat.add(cur, 1n+Groups.len_words(ct)),
              1n+Nat.add(cur, Groups.len_words(ct)),
              NatProof.NatPrf.add_succ(cur, Groups.len_words(ct)))),
          h)
      FT.bool_or_r(
        Bool.and(U32.is_eq(ci, U32.from_nat(cur)), Feedback.word_eq(w, ch)),
        FT.has_col_go(List.append(&2, +List<Nat>, ct, crem), ci, w, 1n+cur),
        FT.has_col_append_r(ct, crem, ci, w, 1n+cur, h2))

def FT.build_cwords_words(+C: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +ci: U32, +stride: U32) ->
  {SolveFast.cwords_words(SolveFast.build_cwords(C, G, ci, stride)) == C
   : +List<+List<Nat>>}:
  match C:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>, l => w <> l,
        SolveFast.cwords_words(
          SolveFast.build_cwords(rest, G, U32.inc(ci), stride)),
        rest,
        FT.build_cwords_words(rest, G, U32.inc(ci), stride))

def FT.build_cwords_ok_go(+crem: +List<+List<Nat>>, +cpre: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, +n: Nat,
    +hai: {FO.FO.all_in_ref(crem, G) == True{} : Bool}) ->
  {FT.cwords_ok_b(G, List.append(&2, +List<Nat>, cpre, crem), n,
     SolveFast.build_cwords(crem, G, U32.from_nat(Groups.len_words(cpre)),
       U32.from_nat(n))) == True{} : Bool}:
  match crem:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      +cur : Nat = Groups.len_words(cpre)
      +hmem : {Tree.member_word(w, G) == True{} : Bool} =
        FO.FO.all_in_head(w, rest, G, hai)
      +htai : {FO.FO.all_in_ref(rest, G) == True{} : Bool} =
        FO.FO.all_in_tail(w, rest, G, hai)
      +hhead_col : {FT.has_col_go(w <> rest, U32.from_nat(cur), w,
                      Nat.add(0n, cur)) == True{} : Bool} =
        Equal.cong(Bool, Bool,
          b => Bool.or(b, FT.has_col_go(rest, U32.from_nat(cur), w, 1n+cur)),
          Bool.and(U32.is_eq(U32.from_nat(cur), U32.from_nat(cur)),
            Feedback.word_eq(w, w)),
          True{},
          FO.FO.bool_and_intro(
            U32.is_eq(U32.from_nat(cur), U32.from_nat(cur)),
            Feedback.word_eq(w, w),
            FT.u32_is_eq_refl(U32.from_nat(cur)),
            FbProof.FbPrf.word_eq_refl(w)))
      +hcol : {FT.has_col_go(List.append(&2, +List<Nat>, cpre, w <> rest),
                 U32.from_nat(cur), w, 0n) == True{} : Bool} =
        FT.has_col_append_r(cpre, w <> rest, U32.from_nat(cur), w, 0n,
          hhead_col)
      +hgrow : {FT.gentry_ok_b(G, n,
                  SolveFast.find_grow(w, G, U32.from_nat(n)), w)
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
      +hrec0 = FT.build_cwords_ok_go(rest, cpre2, G, n, htai)
      +hrec : {FT.cwords_ok_b(G, List.append(&2, +List<Nat>, cpre, w <> rest), n,
                 SolveFast.build_cwords(rest, G, U32.inc(U32.from_nat(cur)),
                   U32.from_nat(n))) == True{} : Bool} =
        Equal.trans(Bool,
          FT.cwords_ok_b(G, List.append(&2, +List<Nat>, cpre, w <> rest), n,
            SolveFast.build_cwords(rest, G, U32.inc(U32.from_nat(cur)),
              U32.from_nat(n))),
          FT.cwords_ok_b(G, List.append(&2, +List<Nat>, cpre2, rest), n,
            SolveFast.build_cwords(rest, G, U32.from_nat(Groups.len_words(cpre2)),
              U32.from_nat(n))),
          True{},
          Equal.trans(Bool,
            FT.cwords_ok_b(G, List.append(&2, +List<Nat>, cpre, w <> rest), n,
              SolveFast.build_cwords(rest, G, U32.inc(U32.from_nat(cur)),
                U32.from_nat(n))),
            FT.cwords_ok_b(G, List.append(&2, +List<Nat>, cpre2, rest), n,
              SolveFast.build_cwords(rest, G, U32.inc(U32.from_nat(cur)),
                U32.from_nat(n))),
            FT.cwords_ok_b(G, List.append(&2, +List<Nat>, cpre2, rest), n,
              SolveFast.build_cwords(rest, G,
                U32.from_nat(Groups.len_words(cpre2)), U32.from_nat(n))),
            Equal.cong(+List<+List<Nat>>, Bool,
              l => FT.cwords_ok_b(G, l, n,
                     SolveFast.build_cwords(rest, G, U32.inc(U32.from_nat(cur)),
                       U32.from_nat(n))),
              List.append(&2, +List<Nat>, cpre, w <> rest),
              List.append(&2, +List<Nat>, cpre2, rest),
              Equal.sym(+List<+List<Nat>>,
                List.append(&2, +List<Nat>, cpre2, rest),
                List.append(&2, +List<Nat>, cpre, w <> rest), ec2)),
            Equal.cong(Nat, Bool,
              x => FT.cwords_ok_b(G, List.append(&2, +List<Nat>, cpre2, rest), n,
                     SolveFast.build_cwords(rest, G, U32.from_nat(x),
                       U32.from_nat(n))),
              1n+cur, Groups.len_words(cpre2),
              Equal.sym(Nat, Groups.len_words(cpre2), 1n+cur, el2))),
          hrec0)
      FO.FO.bool_and_intro(
        Bool.and(
          FT.has_col_go(List.append(&2, +List<Nat>, cpre, w <> rest),
            U32.from_nat(cur), w, 0n),
          FT.gentry_ok_b(G, n, SolveFast.find_grow(w, G, U32.from_nat(n)), w)),
        FT.cwords_ok_b(G, List.append(&2, +List<Nat>, cpre, w <> rest), n,
          SolveFast.build_cwords(rest, G, U32.inc(U32.from_nat(cur)),
            U32.from_nat(n))),
        FO.FO.bool_and_intro(
          FT.has_col_go(List.append(&2, +List<Nat>, cpre, w <> rest),
            U32.from_nat(cur), w, 0n),
          FT.gentry_ok_b(G, n, SolveFast.find_grow(w, G, U32.from_nat(n)), w),
          hcol, hgrow),
        hrec)

def FT.build_cwords_ok(+C: +List<+List<Nat>>, +G: +List<+List<Nat>>, +n: Nat,
    +hai: {FO.FO.all_in_ref(C, G) == True{} : Bool}) ->
  {FT.cwords_ok_b(G, C, n,
     SolveFast.build_cwords(C, G, 0, U32.from_nat(n))) == True{} : Bool}:
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
                  Bool.and(FT.has_col_go(C, ci, w, 0n),
                    FT.gentry_ok_b(G, n, grow, w)),
                  FT.cwords_ok_b(G, C, n, rest), hok)
          +hr = Logic.Proof.and_true_r(
                  Bool.and(FT.has_col_go(C, ci, w, 0n),
                    FT.gentry_ok_b(G, n, grow, w)),
                  FT.cwords_ok_b(G, C, n, rest), hok)
          +hg = Logic.Proof.and_true_r(FT.has_col_go(C, ci, w, 0n),
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
           Nat.add(cur, Nat.mul(Groups.len_words(gpre), n))) == True{} : Bool}) ->
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
               Nat.add(Nat.add(cur, n), Nat.mul(Groups.len_words(gt), n)))
             == True{} : Bool} =
        Equal.trans(Bool,
          FT.has_grow_go(grem, n, row, g,
            Nat.add(Nat.add(cur, n), Nat.mul(Groups.len_words(gt), n))),
          FT.has_grow_go(grem, n, row, g,
            Nat.add(cur, Nat.add(n, Nat.mul(Groups.len_words(gt), n)))),
          True{},
          Equal.cong(Nat, Bool, x => FT.has_grow_go(grem, n, row, g, x),
            Nat.add(Nat.add(cur, n), Nat.mul(Groups.len_words(gt), n)),
            Nat.add(cur, Nat.add(n, Nat.mul(Groups.len_words(gt), n))),
            NatProof.NatPrf.add_assoc(cur, n,
              Nat.mul(Groups.len_words(gt), n))),
          h)
      FT.bool_or_r(
        Bool.and(U32.is_eq(row, U32.from_nat(cur)), Feedback.word_eq(g, gh)),
        FT.has_grow_go(List.append(&2, +List<Nat>, gt, grem), n, row, g,
          Nat.add(cur, n)),
        FT.has_grow_append_r(gt, grem, n, row, g, Nat.add(cur, n), h2))

def FT.guesses_to_rws_ok_go(+grem: +List<+List<Nat>>, +gpre: +List<+List<Nat>>,
    +n: Nat) ->
  {FT.rws_ok_b(List.append(&2, +List<Nat>, gpre, grem), n,
     FT.guesses_to_rws(grem,
       U32.from_nat(Nat.mul(Groups.len_words(gpre), n)), U32.from_nat(n)))
   == True{} : Bool}:
  match grem:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      +ri : Nat = Groups.len_words(gpre)
      +cur : Nat = Nat.mul(ri, n)
      +hhead : {FT.has_grow_go(g <> rest, n, U32.from_nat(cur), g,
                  Nat.add(0n, cur)) == True{} : Bool} =
        Equal.cong(Bool, Bool,
          b => Bool.or(b, FT.has_grow_go(rest, n, U32.from_nat(cur), g,
                            Nat.add(cur, n))),
          Bool.and(U32.is_eq(U32.from_nat(cur), U32.from_nat(cur)),
            Feedback.word_eq(g, g)),
          True{},
          FO.FO.bool_and_intro(
            U32.is_eq(U32.from_nat(cur), U32.from_nat(cur)),
            Feedback.word_eq(g, g),
            FT.u32_is_eq_refl(U32.from_nat(cur)),
            FbProof.FbPrf.word_eq_refl(g)))
      +hg : {FT.gentry_ok_b(List.append(&2, +List<Nat>, gpre, g <> rest), n,
               U32.from_nat(cur), g) == True{} : Bool} =
        FT.has_grow_append_r(gpre, g <> rest, n, U32.from_nat(cur), g, 0n, hhead)
      +gpre2 = List.append(&2, +List<Nat>, gpre, g <> Nil{})
      +eg2 : {List.append(&2, +List<Nat>, gpre2, rest)
              == List.append(&2, +List<Nat>, gpre, g <> rest)
              : +List<+List<Nat>>} =
        FT.list_append_snoc(+List<Nat>, gpre, g, rest)
      +el2 : {Groups.len_words(gpre2) == 1n+ri : Nat} =
        Equal.trans(Nat, Groups.len_words(gpre2), Nat.add(ri, 1n), 1n+ri,
          FT.len_words_append(gpre, g <> Nil{}),
          NatProof.NatPrf.add_comm(ri, 1n))
      +em2 : {Nat.mul(Groups.len_words(gpre2), n) == Nat.add(cur, n) : Nat} =
        Equal.trans(Nat, Nat.mul(Groups.len_words(gpre2), n),
          Nat.add(n, cur), Nat.add(cur, n),
          Equal.cong(Nat, Nat, x => Nat.mul(x, n),
            Groups.len_words(gpre2), 1n+ri, el2),
          NatProof.NatPrf.add_comm(n, cur))
      +eu : {U32.add(U32.from_nat(cur), U32.from_nat(n))
             == U32.from_nat(Nat.mul(Groups.len_words(gpre2), n)) : U32} =
        Equal.trans(U32,
          U32.add(U32.from_nat(cur), U32.from_nat(n)),
          U32.from_nat(Nat.add(cur, n)),
          U32.from_nat(Nat.mul(Groups.len_words(gpre2), n)),
          FT.u32_add_from_nat(cur, n),
          Equal.cong(Nat, U32, x => U32.from_nat(x),
            Nat.add(cur, n), Nat.mul(Groups.len_words(gpre2), n),
            Equal.sym(Nat, Nat.mul(Groups.len_words(gpre2), n),
              Nat.add(cur, n), em2)))
      +hrec : {FT.rws_ok_b(List.append(&2, +List<Nat>, gpre, g <> rest), n,
                 FT.guesses_to_rws(rest,
                   U32.add(U32.from_nat(cur), U32.from_nat(n)),
                   U32.from_nat(n))) == True{} : Bool} =
        Equal.trans(Bool,
          FT.rws_ok_b(List.append(&2, +List<Nat>, gpre, g <> rest), n,
            FT.guesses_to_rws(rest,
              U32.add(U32.from_nat(cur), U32.from_nat(n)), U32.from_nat(n))),
          FT.rws_ok_b(List.append(&2, +List<Nat>, gpre2, rest), n,
            FT.guesses_to_rws(rest,
              U32.from_nat(Nat.mul(Groups.len_words(gpre2), n)),
              U32.from_nat(n))),
          True{},
          Equal.trans(Bool,
            FT.rws_ok_b(List.append(&2, +List<Nat>, gpre, g <> rest), n,
              FT.guesses_to_rws(rest,
                U32.add(U32.from_nat(cur), U32.from_nat(n)), U32.from_nat(n))),
            FT.rws_ok_b(List.append(&2, +List<Nat>, gpre2, rest), n,
              FT.guesses_to_rws(rest,
                U32.add(U32.from_nat(cur), U32.from_nat(n)), U32.from_nat(n))),
            FT.rws_ok_b(List.append(&2, +List<Nat>, gpre2, rest), n,
              FT.guesses_to_rws(rest,
                U32.from_nat(Nat.mul(Groups.len_words(gpre2), n)),
                U32.from_nat(n))),
            Equal.cong(+List<+List<Nat>>, Bool,
              l => FT.rws_ok_b(l, n,
                     FT.guesses_to_rws(rest,
                       U32.add(U32.from_nat(cur), U32.from_nat(n)),
                       U32.from_nat(n))),
              List.append(&2, +List<Nat>, gpre, g <> rest),
              List.append(&2, +List<Nat>, gpre2, rest),
              Equal.sym(+List<+List<Nat>>,
                List.append(&2, +List<Nat>, gpre2, rest),
                List.append(&2, +List<Nat>, gpre, g <> rest), eg2)),
            Equal.cong(U32, Bool,
              u => FT.rws_ok_b(List.append(&2, +List<Nat>, gpre2, rest), n,
                     FT.guesses_to_rws(rest, u, U32.from_nat(n))),
              U32.add(U32.from_nat(cur), U32.from_nat(n)),
              U32.from_nat(Nat.mul(Groups.len_words(gpre2), n)), eu)),
          FT.guesses_to_rws_ok_go(rest, gpre2, n))
      FO.FO.bool_and_intro(
        FT.gentry_ok_b(List.append(&2, +List<Nat>, gpre, g <> rest), n,
          U32.from_nat(cur), g),
        FT.rws_ok_b(List.append(&2, +List<Nat>, gpre, g <> rest), n,
          FT.guesses_to_rws(rest,
            U32.add(U32.from_nat(cur), U32.from_nat(n)), U32.from_nat(n))),
        hg, hrec)

def FT.guesses_to_rws_ok(+G: +List<+List<Nat>>, +n: Nat) ->
  {FT.rws_ok_b(G, n, FT.guesses_to_rws(G, 0, U32.from_nat(n))) == True{} : Bool}:
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
        FT.has_grow_go(gt, n, row, g, Nat.add(cur, n)), h,
        +hl =>
          +ew : {Feedback.word_eq(g, gh) == True{} : Bool} =
            Logic.Proof.and_true_r(U32.is_eq(row, U32.from_nat(cur)),
              Feedback.word_eq(g, gh), hl)
          Equal.cong(Bool, Bool,
            b => Feedback.Bool.case(Bool, b, True{}, Tree.member_word(g, gt)),
            Feedback.word_eq(g, gh), True{}, ew),
        +hr =>
          +hrec : {Tree.member_word(g, gt) == True{} : Bool} =
            FT.member_of_has_grow(gt, n, row, g, Nat.add(cur, n), hr)
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
    +hcol: {FT.has_col_go(C, ci, w, 0n) == True{} : Bool},
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
    +hcol: {FT.has_col_go(C, ci, w, 0n) == True{} : Bool},
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
    +hcol: {FT.has_col_go(C, ci, w, 0n) == True{} : Bool},
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
    +hcol: {FT.has_col_go(C, ci, w, 0n) == True{} : Bool},
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
