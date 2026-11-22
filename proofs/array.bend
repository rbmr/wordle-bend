# Pure specifications for Bend's `Array<T>` and `U32` indexing.
#
# Bend compiles `Array<T>` to flat, in-place mutable C blocks (`blk_read` /
# `blk_write`) while its proof theory sees the balanced binary tree
# `ALeaf` / `ANode`. This module proves the array read/write laws once for any
# depth `d < 32` and `Data` element type `T`:
# - `Arr.depth_new` / `Arr.depth_swap` / `Arr.depth_set`: depth preservation.
# - `Arr.get_new`: reading a freshly created array returns the initial value.
# - `Arr.get_fst`: reading does not modify the array.
# - `Arr.swap_old`: `Array.swap` returns the prior value at the written index.
# - `Arr.get_swap_same` / `Arr.get_set_same`: reading back the written index.
# - `Arr.get_swap_diff` / `Arr.get_set_diff`: reading any distinct in-range index.
import Base
import ./logic.bend as Logic
import ./nat.bend as NatProof

# ---------------------------------------------------------------------------
# Pairs and affine array duplication for proofs
# ---------------------------------------------------------------------------

def Arr.fst(-A: Type, -B: Type, p: A & B) -> A:
  (x, y) = p
  x

def Arr.snd(-A: Type, -B: Type, p: A & B) -> B:
  (x, y) = p
  y

def Arr.dup_node(-T: Data, -xs: Array<T>, -ys: Array<T>,
    rx: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == xs : Array<T>} & {a2 == a1 : Array<T>},
    ry: &b1: Array<T> -> &b2: Array<T> ->
        {b1 == ys : Array<T>} & {b2 == b1 : Array<T>}) ->
  &a1: Array<T> -> &a2: Array<T> ->
  {a1 == ANode{xs, ys} : Array<T>} & {a2 == a1 : Array<T>}:
  (xs1, rx2) = rx
  (xs2, pex) = rx2
  (ex1, ex2) = pex
  (ys1, ry2) = ry
  (ys2, pey) = ry2
  (ey1, ey2) = pey
  e1 = Equal.trans(Array<T>, ANode{xs1, ys1}, ANode{xs, ys1}, ANode{xs, ys},
    Equal.cong(Array<T>, Array<T>, l => ANode{l, ys1}, xs1, xs, ex1),
    Equal.cong(Array<T>, Array<T>, r => ANode{xs, r}, ys1, ys, ey1))
  e2 = Equal.trans(Array<T>, ANode{xs2, ys2}, ANode{xs1, ys2}, ANode{xs1, ys1},
    Equal.cong(Array<T>, Array<T>, l => ANode{l, ys2}, xs2, xs1, ex2),
    Equal.cong(Array<T>, Array<T>, r => ANode{xs1, r}, ys2, ys1, ey2))
  (ANode{xs1, ys1}, (ANode{xs2, ys2}, (e1, e2)))

def Arr.dup(-T: Data, a: Array<T>) ->
  &a1: Array<T> -> &a2: Array<T> ->
  {a1 == a : Array<T>} & {a2 == a1 : Array<T>}:
  match a:
    case ALeaf{+x}:
      (ALeaf{x}, (ALeaf{x}, ({==}, {==})))
    case ANode{xs, ys}:
      Arr.dup_node(T, xs, ys, Arr.dup(T, xs), Arr.dup(T, ys))

# ---------------------------------------------------------------------------
# Word bit-level helpers (powers of two, low-bit masks, subtraction, order)
# ---------------------------------------------------------------------------

def Arr.pow2_word(k: Nat, m: Nat) -> Word(m):
  match k m:
    case _ 0n:
      WNil{}
    case 0n 1n++mp:
      WCon{True{}, Word.zero(mp)}
    case 1n++kp 1n++mp:
      WCon{False{}, Arr.pow2_word(kp, mp)}

def Arr.pow2_u32(k: Nat) -> U32:
  U32{Arr.pow2_word(k, 32n)}

def Arr.mask_word(k: Nat, m: Nat) -> Word(m):
  match k m:
    case _ 0n:
      WNil{}
    case 0n 1n++mp:
      WCon{False{}, Word.zero(mp)}
    case 1n++kp 1n++mp:
      WCon{True{}, Arr.mask_word(kp, mp)}

def Arr.word_zero_from(k: Nat, m: Nat, +w: Word(m)) -> Bool:
  match k m:
    case _ 0n:
      True{}
    case 0n 1n++mp:
      match w:
        case WCon{b, t}:
          Bool.and(Bool.not(b), Arr.word_zero_from(0n, mp, t))
    case 1n++kp 1n++mp:
      match w:
        case WCon{b, t}:
          Arr.word_zero_from(kp, mp, t)

def Arr.u32_zero_from(k: Nat, +u: U32) -> Bool:
  match u:
    case U32{w}:
      Arr.word_zero_from(k, 32n, w)

def Arr.word_bit(k: Nat, m: Nat, +w: Word(m)) -> Bool:
  match k m:
    case _ 0n:
      False{}
    case 0n 1n++mp:
      match w:
        case WCon{b, t}:
          b
    case 1n++kp 1n++mp:
      match w:
        case WCon{b, t}:
          Arr.word_bit(kp, mp, t)

def Arr.word_shl_put_zero(m: Nat) ->
  {Word.shl.put(m, False{}, Word.zero(m)) == Word.zero(m) : Word(m)}:
  match m:
    case 0n:
      {==}
    case 1n++mp:
      Equal.cong(Word(mp), Word(1n+mp), w => WCon{False{}, w},
        Word.shl.put(mp, False{}, Word.zero(mp)), Word.zero(mp),
        Arr.word_shl_put_zero(mp))

def Arr.word_shl_put_one(m: Nat) ->
  {Word.shl.put(m, True{}, Word.zero(m)) == Arr.pow2_word(0n, m) : Word(m)}:
  match m:
    case 0n:
      {==}
    case 1n++mp:
      Equal.cong(Word(mp), Word(1n+mp), w => WCon{True{}, w},
        Word.shl.put(mp, False{}, Word.zero(mp)), Word.zero(mp),
        Arr.word_shl_put_zero(mp))

def Arr.word_shl_put_pow2(+k: Nat, +m: Nat) ->
  {Word.shl.put(m, False{}, Arr.pow2_word(k, m)) == Arr.pow2_word(1n+k, m)
   : Word(m)}:
  match k m:
    case _ 0n:
      {==}
    case 0n 1n++mp:
      Equal.cong(Word(mp), Word(1n+mp), w => WCon{False{}, w},
        Word.shl.put(mp, True{}, Word.zero(mp)), Arr.pow2_word(0n, mp),
        Arr.word_shl_put_one(mp))
    case 1n++kp 1n++mp:
      Equal.cong(Word(mp), Word(1n+mp), w => WCon{False{}, w},
        Word.shl.put(mp, False{}, Arr.pow2_word(kp, mp)),
        Arr.pow2_word(1n+kp, mp),
        Arr.word_shl_put_pow2(kp, mp))

def Arr.word_shl_pow2(+k: Nat, +m: Nat) ->
  {Word.shl(m, Arr.pow2_word(k, m)) == Arr.pow2_word(1n+k, m) : Word(m)}:
  match k m:
    case _ 0n:
      {==}
    case 0n 1n++mp:
      Equal.cong(Word(mp), Word(1n+mp), w => WCon{False{}, w},
        Word.shl.put(mp, True{}, Word.zero(mp)), Arr.pow2_word(0n, mp),
        Arr.word_shl_put_one(mp))
    case 1n++kp 1n++mp:
      Equal.cong(Word(mp), Word(1n+mp), w => WCon{False{}, w},
        Word.shl.put(mp, False{}, Arr.pow2_word(kp, mp)),
        Arr.pow2_word(1n+kp, mp),
        Arr.word_shl_put_pow2(kp, mp))

def Arr.u32_shl_pow2(+k: Nat) ->
  {U32.shl(Arr.pow2_u32(k)) == Arr.pow2_u32(1n+k) : U32}:
  Equal.cong(Word(32n), U32, w => U32{w},
    Word.shl(32n, Arr.pow2_word(k, 32n)), Arr.pow2_word(1n+k, 32n),
    Arr.word_shl_pow2(k, 32n))

def Arr.word_shr_pad_zero(m: Nat) ->
  {Word.shr.pad(m, Word.zero(m)) == Word.zero(1n+m) : Word(1n+m)}:
  match m:
    case 0n:
      {==}
    case 1n++mp:
      Equal.cong(Word(1n+mp), Word(1n+(1n+mp)), w => WCon{False{}, w},
        Word.shr.pad(mp, Word.zero(mp)), Word.zero(1n+mp),
        Arr.word_shr_pad_zero(mp))

def Arr.word_shr_pad_pow2(+k: Nat, +m: Nat,
    +lt: {Nat.is_lt(k, m) == True{} : Bool}) ->
  {Word.shr.pad(m, Arr.pow2_word(k, m)) == Arr.pow2_word(k, 1n+m)
   : Word(1n+m)}:
  match k m:
    case 0n 0n:
      Empty.absurd(
        {Word.shr.pad(0n, Arr.pow2_word(0n, 0n)) == Arr.pow2_word(0n, 1n)
         : Word(1n)},
        Logic.Proof.false_ne_true(lt))
    case 1n++kp 0n:
      Empty.absurd(
        {Word.shr.pad(0n, Arr.pow2_word(1n+kp, 0n)) == Arr.pow2_word(1n+kp, 1n)
         : Word(1n)},
        Logic.Proof.false_ne_true(lt))
    case 0n 1n++mp:
      Equal.cong(Word(1n+mp), Word(1n+(1n+mp)), w => WCon{True{}, w},
        Word.shr.pad(mp, Word.zero(mp)), Word.zero(1n+mp),
        Arr.word_shr_pad_zero(mp))
    case 1n++kp 1n++mp:
      Equal.cong(Word(1n+mp), Word(1n+(1n+mp)), w => WCon{False{}, w},
        Word.shr.pad(mp, Arr.pow2_word(kp, mp)),
        Arr.pow2_word(kp, 1n+mp),
        Arr.word_shr_pad_pow2(kp, mp, lt))

def Arr.word_shr_pow2(+k: Nat, +m: Nat,
    +lt: {Nat.is_lt(1n+k, m) == True{} : Bool}) ->
  {Word.shr(m, Arr.pow2_word(1n+k, m)) == Arr.pow2_word(k, m) : Word(m)}:
  match m:
    case 0n:
      Empty.absurd(
        {Word.shr(0n, Arr.pow2_word(1n+k, 0n)) == Arr.pow2_word(k, 0n)
         : Word(0n)},
        Logic.Proof.false_ne_true(lt))
    case 1n++mp:
      Arr.word_shr_pad_pow2(k, mp, lt)

def Arr.u32_shr_pow2(+k: Nat, +lt: {Nat.is_lt(1n+k, 32n) == True{} : Bool}) ->
  {U32.shr(Arr.pow2_u32(1n+k)) == Arr.pow2_u32(k) : U32}:
  Equal.cong(Word(32n), U32, w => U32{w},
    Word.shr(32n, Arr.pow2_word(1n+k, 32n)), Arr.pow2_word(k, 32n),
    Arr.word_shr_pow2(k, 32n, lt))

def Arr.bool_not_true(b: Bool, e: {Bool.not(b) == True{} : Bool}) ->
  {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Logic.Proof.false_ne_true(e))

def Arr.bool_not_false(b: Bool, e: {Bool.not(b) == False{} : Bool}) ->
  {b == True{} : Bool}:
  match b:
    case False{}:
      Empty.absurd({False{} == True{} : Bool},
        Logic.Proof.false_ne_true(Equal.sym(Bool, True{}, False{}, e)))
    case True{}:
      {==}

def Arr.bool_and_true_r(b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Arr.bool_and_false_r(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Arr.bool_cmp_false_not_lt(b: Bool) ->
  {Cmp.is_lt(Bool.cmp(b, False{})) == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Arr.bool_cmp_true_lt(b: Bool) ->
  {Cmp.is_lt(Bool.cmp(b, True{})) == Bool.not(b) : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Arr.word_eq_zero(+m: Nat, +w: Word(m),
    +hz: {Arr.word_zero_from(0n, m, w) == True{} : Bool}) ->
  {w == Word.zero(m) : Word(m)}:
  match m:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++mp:
      match w:
        case WCon{+b, +t}:
          +hb : {b == False{} : Bool} =
            Arr.bool_not_true(b,
              Logic.Proof.and_true_l(Bool.not(b),
                Arr.word_zero_from(0n, mp, t), hz))
          +ht : {t == Word.zero(mp) : Word(mp)} =
            Arr.word_eq_zero(mp, t,
              Logic.Proof.and_true_r(Bool.not(b),
                Arr.word_zero_from(0n, mp, t), hz))
          Equal.trans(Word(1n+mp),
            WCon{b, t}, WCon{False{}, t}, WCon{False{}, Word.zero(mp)},
            Equal.cong(Bool, Word(1n+mp), x => WCon{x, t}, b, False{}, hb),
            Equal.cong(Word(mp), Word(1n+mp), x => WCon{False{}, x},
              t, Word.zero(mp), ht))

def Arr.word_zero_from_zero(m: Nat) ->
  {Arr.word_zero_from(0n, m, Word.zero(m)) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n++mp:
      Arr.word_zero_from_zero(mp)

def Arr.word_adc_sub_zero_t(+m: Nat, +w: Word(m)) ->
  {Word.adc(m, w, Word.zero(m), True{}, True{}) == w : Word(m)}:
  match m:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++mp:
      match w:
        case WCon{b, +t}:
          match b:
            case False{}:
              Equal.cong(Word(mp), Word(1n+mp), x => WCon{False{}, x},
                Word.adc(mp, t, Word.zero(mp), True{}, True{}), t,
                Arr.word_adc_sub_zero_t(mp, t))
            case True{}:
              Equal.cong(Word(mp), Word(1n+mp), x => WCon{True{}, x},
                Word.adc(mp, t, Word.zero(mp), True{}, True{}), t,
                Arr.word_adc_sub_zero_t(mp, t))

def Arr.word_sub_pow2_one_go(+k: Nat, +m: Nat) ->
  {Word.adc(m, Arr.pow2_word(k, m), Word.zero(m), True{}, False{})
   == Arr.mask_word(k, m) : Word(m)}:
  match k m:
    case _ 0n:
      {==}
    case 0n 1n++mp:
      Equal.cong(Word(mp), Word(1n+mp), x => WCon{False{}, x},
        Word.adc(mp, Word.zero(mp), Word.zero(mp), True{}, True{}),
        Word.zero(mp),
        Arr.word_adc_sub_zero_t(mp, Word.zero(mp)))
    case 1n++kp 1n++mp:
      Equal.cong(Word(mp), Word(1n+mp), x => WCon{True{}, x},
        Word.adc(mp, Arr.pow2_word(kp, mp), Word.zero(mp), True{}, False{}),
        Arr.mask_word(kp, mp),
        Arr.word_sub_pow2_one_go(kp, mp))

def Arr.word_sub_pow2_one(+k: Nat, +m: Nat) ->
  {Word.sub(m, Arr.pow2_word(k, m), Arr.pow2_word(0n, m))
   == Arr.mask_word(k, m) : Word(m)}:
  match k m:
    case _ 0n:
      {==}
    case 0n 1n++mp:
      Equal.cong(Word(mp), Word(1n+mp), x => WCon{False{}, x},
        Word.adc(mp, Word.zero(mp), Word.zero(mp), True{}, True{}),
        Word.zero(mp),
        Arr.word_adc_sub_zero_t(mp, Word.zero(mp)))
    case 1n++kp 1n++mp:
      Equal.cong(Word(mp), Word(1n+mp), x => WCon{True{}, x},
        Word.adc(mp, Arr.pow2_word(kp, mp), Word.zero(mp), True{}, False{}),
        Arr.mask_word(kp, mp),
        Arr.word_sub_pow2_one_go(kp, mp))

def Arr.word_and_zero_r(+m: Nat, +w: Word(m)) ->
  {Word.and(m, w, Word.zero(m)) == Word.zero(m) : Word(m)}:
  match m:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++mp:
      match w:
        case WCon{+b, +t}:
          Equal.trans(Word(1n+mp),
            WCon{Bool.and(b, False{}), Word.and(mp, t, Word.zero(mp))},
            WCon{False{}, Word.and(mp, t, Word.zero(mp))},
            WCon{False{}, Word.zero(mp)},
            Equal.cong(Bool, Word(1n+mp),
              x => WCon{x, Word.and(mp, t, Word.zero(mp))},
              Bool.and(b, False{}), False{}, Arr.bool_and_false_r(b)),
            Equal.cong(Word(mp), Word(1n+mp), x => WCon{False{}, x},
              Word.and(mp, t, Word.zero(mp)), Word.zero(mp),
              Arr.word_and_zero_r(mp, t)))

def Arr.word_and_mask(+k: Nat, +m: Nat, +w: Word(m),
    +hz: {Arr.word_zero_from(k, m, w) == True{} : Bool}) ->
  {Word.and(m, w, Arr.mask_word(k, m)) == w : Word(m)}:
  match k m:
    case _ 0n:
      match w:
        case WNil{}:
          {==}
    case 0n 1n++mp:
      match w:
        case WCon{+b, +t}:
          +hw : {WCon{b, t} == Word.zero(1n+mp) : Word(1n+mp)} =
            Arr.word_eq_zero(1n+mp, WCon{b, t}, hz)
          Equal.trans(Word(1n+mp),
            Word.and(1n+mp, WCon{b, t}, Word.zero(1n+mp)),
            Word.zero(1n+mp),
            WCon{b, t},
            Arr.word_and_zero_r(1n+mp, WCon{b, t}),
            Equal.sym(Word(1n+mp), WCon{b, t}, Word.zero(1n+mp), hw))
    case 1n++kp 1n++mp:
      match w:
        case WCon{+b, +t}:
          Equal.trans(Word(1n+mp),
            WCon{Bool.and(b, True{}), Word.and(mp, t, Arr.mask_word(kp, mp))},
            WCon{b, Word.and(mp, t, Arr.mask_word(kp, mp))},
            WCon{b, t},
            Equal.cong(Bool, Word(1n+mp),
              x => WCon{x, Word.and(mp, t, Arr.mask_word(kp, mp))},
              Bool.and(b, True{}), b, Arr.bool_and_true_r(b)),
            Equal.cong(Word(mp), Word(1n+mp), x => WCon{b, x},
              Word.and(mp, t, Arr.mask_word(kp, mp)), t,
              Arr.word_and_mask(kp, mp, t, hz)))

def Arr.u32_and_mask(+k: Nat, +i: U32,
    +hz: {Arr.u32_zero_from(k, i) == True{} : Bool}) ->
  {U32.and(i, U32.sub(Arr.pow2_u32(k), 1)) == i : U32}:
  match i:
    case U32{+w}:
      Equal.cong(Word(32n), U32, x => U32{x},
        Word.and(32n, w,
          Word.sub(32n, Arr.pow2_word(k, 32n), Arr.pow2_word(0n, 32n))),
        w,
        Equal.trans(Word(32n),
          Word.and(32n, w,
            Word.sub(32n, Arr.pow2_word(k, 32n), Arr.pow2_word(0n, 32n))),
          Word.and(32n, w, Arr.mask_word(k, 32n)),
          w,
          Equal.cong(Word(32n), Word(32n), x => Word.and(32n, w, x),
            Word.sub(32n, Arr.pow2_word(k, 32n), Arr.pow2_word(0n, 32n)),
            Arr.mask_word(k, 32n),
            Arr.word_sub_pow2_one(k, 32n)),
          Arr.word_and_mask(k, 32n, w, hz)))

def Arr.word_cmp_zero_refl(m: Nat) ->
  {Word.cmp(m, Word.zero(m), Word.zero(m)) == EQ{} : Cmp}:
  match m:
    case 0n:
      {==}
    case 1n++mp:
      Equal.cong(Cmp, Cmp, t => Word.cmp.fin(False{}, False{}, t),
        Word.cmp(mp, Word.zero(mp), Word.zero(mp)), EQ{},
        Arr.word_cmp_zero_refl(mp))

def Arr.word_cmp_pow2_step(+kp: Nat, +mp: Nat, +b: Bool, +t: Word(mp), c: Cmp,
    +ec: {c == Word.cmp(mp, t, Arr.pow2_word(kp, mp)) : Cmp},
    +ih: {Cmp.is_lt(Word.cmp(mp, t, Arr.pow2_word(kp, mp)))
          == Bool.not(Arr.word_bit(kp, mp, t)) : Bool}) ->
  {Cmp.is_lt(Word.cmp.fin(b, False{}, Word.cmp(mp, t, Arr.pow2_word(kp, mp))))
   == Bool.not(Arr.word_bit(kp, mp, t)) : Bool}:
  match c:
    case LT{}:
      Equal.trans(Bool,
        Cmp.is_lt(Word.cmp.fin(b, False{},
          Word.cmp(mp, t, Arr.pow2_word(kp, mp)))),
        True{},
        Bool.not(Arr.word_bit(kp, mp, t)),
        Equal.cong(Cmp, Bool, x => Cmp.is_lt(Word.cmp.fin(b, False{}, x)),
          Word.cmp(mp, t, Arr.pow2_word(kp, mp)), LT{},
          Equal.sym(Cmp, LT{}, Word.cmp(mp, t, Arr.pow2_word(kp, mp)), ec)),
        Equal.trans(Bool, True{},
          Cmp.is_lt(Word.cmp(mp, t, Arr.pow2_word(kp, mp))),
          Bool.not(Arr.word_bit(kp, mp, t)),
          Equal.cong(Cmp, Bool, x => Cmp.is_lt(x), LT{},
            Word.cmp(mp, t, Arr.pow2_word(kp, mp)), ec),
          ih))
    case EQ{}:
      Equal.trans(Bool,
        Cmp.is_lt(Word.cmp.fin(b, False{},
          Word.cmp(mp, t, Arr.pow2_word(kp, mp)))),
        Cmp.is_lt(Bool.cmp(b, False{})),
        Bool.not(Arr.word_bit(kp, mp, t)),
        Equal.cong(Cmp, Bool, x => Cmp.is_lt(Word.cmp.fin(b, False{}, x)),
          Word.cmp(mp, t, Arr.pow2_word(kp, mp)), EQ{},
          Equal.sym(Cmp, EQ{}, Word.cmp(mp, t, Arr.pow2_word(kp, mp)), ec)),
        Equal.trans(Bool,
          Cmp.is_lt(Bool.cmp(b, False{})),
          False{},
          Bool.not(Arr.word_bit(kp, mp, t)),
          Arr.bool_cmp_false_not_lt(b),
          Equal.trans(Bool, False{},
            Cmp.is_lt(Word.cmp(mp, t, Arr.pow2_word(kp, mp))),
            Bool.not(Arr.word_bit(kp, mp, t)),
            Equal.cong(Cmp, Bool, x => Cmp.is_lt(x), EQ{},
              Word.cmp(mp, t, Arr.pow2_word(kp, mp)), ec),
            ih)))
    case GT{}:
      Equal.trans(Bool,
        Cmp.is_lt(Word.cmp.fin(b, False{},
          Word.cmp(mp, t, Arr.pow2_word(kp, mp)))),
        False{},
        Bool.not(Arr.word_bit(kp, mp, t)),
        Equal.cong(Cmp, Bool, x => Cmp.is_lt(Word.cmp.fin(b, False{}, x)),
          Word.cmp(mp, t, Arr.pow2_word(kp, mp)), GT{},
          Equal.sym(Cmp, GT{}, Word.cmp(mp, t, Arr.pow2_word(kp, mp)), ec)),
        Equal.trans(Bool, False{},
          Cmp.is_lt(Word.cmp(mp, t, Arr.pow2_word(kp, mp))),
          Bool.not(Arr.word_bit(kp, mp, t)),
          Equal.cong(Cmp, Bool, x => Cmp.is_lt(x), GT{},
            Word.cmp(mp, t, Arr.pow2_word(kp, mp)), ec),
          ih))

# For `w` with all bits above `k` zero and `k < m`, `w < 2^k` iff bit `k` is
# `False{}`.
def Arr.word_cmp_pow2_bit(+k: Nat, +m: Nat, +w: Word(m),
    +hz: {Arr.word_zero_from(1n+k, m, w) == True{} : Bool},
    +lt: {Nat.is_lt(k, m) == True{} : Bool}) ->
  {Cmp.is_lt(Word.cmp(m, w, Arr.pow2_word(k, m)))
   == Bool.not(Arr.word_bit(k, m, w)) : Bool}:
  match k m:
    case 0n 0n:
      Empty.absurd(
        {Cmp.is_lt(Word.cmp(0n, w, Arr.pow2_word(0n, 0n)))
         == Bool.not(Arr.word_bit(0n, 0n, w)) : Bool},
        Logic.Proof.false_ne_true(lt))
    case 1n++kp 0n:
      Empty.absurd(
        {Cmp.is_lt(Word.cmp(0n, w, Arr.pow2_word(1n+kp, 0n)))
         == Bool.not(Arr.word_bit(1n+kp, 0n, w)) : Bool},
        Logic.Proof.false_ne_true(lt))
    case 0n 1n++mp:
      match w:
        case WCon{+b, +t}:
          +ht : {t == Word.zero(mp) : Word(mp)} =
            Arr.word_eq_zero(mp, t, hz)
          +ec : {Word.cmp(mp, t, Word.zero(mp)) == EQ{} : Cmp} =
            Equal.trans(Cmp,
              Word.cmp(mp, t, Word.zero(mp)),
              Word.cmp(mp, Word.zero(mp), Word.zero(mp)),
              EQ{},
              Equal.cong(Word(mp), Cmp, x => Word.cmp(mp, x, Word.zero(mp)),
                t, Word.zero(mp), ht),
              Arr.word_cmp_zero_refl(mp))
          Equal.trans(Bool,
            Cmp.is_lt(Word.cmp.fin(b, True{}, Word.cmp(mp, t, Word.zero(mp)))),
            Cmp.is_lt(Word.cmp.fin(b, True{}, EQ{})),
            Bool.not(b),
            Equal.cong(Cmp, Bool, c => Cmp.is_lt(Word.cmp.fin(b, True{}, c)),
              Word.cmp(mp, t, Word.zero(mp)), EQ{}, ec),
            Arr.bool_cmp_true_lt(b))
    case 1n++kp 1n++mp:
      match w:
        case WCon{+b, +t}:
          Arr.word_cmp_pow2_step(kp, mp, b, t,
            Word.cmp(mp, t, Arr.pow2_word(kp, mp)), {==},
            Arr.word_cmp_pow2_bit(kp, mp, t, hz, lt))

def Arr.word_zero_from_of_bit_false(+k: Nat, +m: Nat, +w: Word(m),
    +hz: {Arr.word_zero_from(1n+k, m, w) == True{} : Bool},
    +hb: {Arr.word_bit(k, m, w) == False{} : Bool}) ->
  {Arr.word_zero_from(k, m, w) == True{} : Bool}:
  match k m:
    case _ 0n:
      {==}
    case 0n 1n++mp:
      match w:
        case WCon{+b, +t}:
          Equal.trans(Bool,
            Bool.and(Bool.not(b), Arr.word_zero_from(0n, mp, t)),
            Arr.word_zero_from(0n, mp, t),
            True{},
            Equal.cong(Bool, Bool,
              x => Bool.and(Bool.not(x), Arr.word_zero_from(0n, mp, t)),
              b, False{}, hb),
            hz)
    case 1n++kp 1n++mp:
      match w:
        case WCon{+b, +t}:
          Arr.word_zero_from_of_bit_false(kp, mp, t, hz, hb)

def Arr.word_sub_pow2_zero_from(+k: Nat, +m: Nat, +w: Word(m),
    +hz: {Arr.word_zero_from(1n+k, m, w) == True{} : Bool},
    +hb: {Arr.word_bit(k, m, w) == True{} : Bool}) ->
  {Arr.word_zero_from(k, m, Word.sub(m, w, Arr.pow2_word(k, m)))
   == True{} : Bool}:
  match k m:
    case _ 0n:
      {==}
    case 0n 1n++mp:
      match w:
        case WCon{+b, +t}:
          +eq1 : {Word.sub(1n+mp, WCon{b, t}, Arr.pow2_word(0n, 1n+mp))
                  == WCon{False{}, Word.adc(mp, t, Word.zero(mp), True{}, True{})}
                  : Word(1n+mp)} =
            Equal.cong(Bool, Word(1n+mp),
              x => Word.sub(1n+mp, WCon{x, t}, Arr.pow2_word(0n, 1n+mp)),
              b, True{}, hb)
          +eq2 : {WCon{False{}, Word.adc(mp, t, Word.zero(mp), True{}, True{})}
                  == WCon{False{}, t} : Word(1n+mp)} =
            Equal.cong(Word(mp), Word(1n+mp), x => WCon{False{}, x},
              Word.adc(mp, t, Word.zero(mp), True{}, True{}), t,
              Arr.word_adc_sub_zero_t(mp, t))
          Equal.trans(Bool,
            Arr.word_zero_from(0n, 1n+mp,
              Word.sub(1n+mp, WCon{b, t}, Arr.pow2_word(0n, 1n+mp))),
            Arr.word_zero_from(0n, 1n+mp, WCon{False{}, t}),
            True{},
            Equal.cong(Word(1n+mp), Bool,
              x => Arr.word_zero_from(0n, 1n+mp, x),
              Word.sub(1n+mp, WCon{b, t}, Arr.pow2_word(0n, 1n+mp)),
              WCon{False{}, t},
              Equal.trans(Word(1n+mp),
                Word.sub(1n+mp, WCon{b, t}, Arr.pow2_word(0n, 1n+mp)),
                WCon{False{}, Word.adc(mp, t, Word.zero(mp), True{}, True{})},
                WCon{False{}, t}, eq1, eq2)),
            hz)
    case 1n++kp 1n++mp:
      match w:
        case WCon{+b, +t}:
          match b:
            case False{}:
              Arr.word_sub_pow2_zero_from(kp, mp, t, hz, hb)
            case True{}:
              Arr.word_sub_pow2_zero_from(kp, mp, t, hz, hb)

def Arr.u32_zero_from_lt(+k: Nat, +u: U32,
    +hz: {Arr.u32_zero_from(1n+k, u) == True{} : Bool},
    +lt: {Nat.is_lt(k, 32n) == True{} : Bool},
    +hlt: {U32.is_lt(u, Arr.pow2_u32(k)) == True{} : Bool}) ->
  {Arr.u32_zero_from(k, u) == True{} : Bool}:
  match u:
    case U32{+w}:
      +hnb : {Bool.not(Arr.word_bit(k, 32n, w)) == True{} : Bool} =
        Equal.trans(Bool,
          Bool.not(Arr.word_bit(k, 32n, w)),
          Cmp.is_lt(Word.cmp(32n, w, Arr.pow2_word(k, 32n))),
          True{},
          Equal.sym(Bool,
            Cmp.is_lt(Word.cmp(32n, w, Arr.pow2_word(k, 32n))),
            Bool.not(Arr.word_bit(k, 32n, w)),
            Arr.word_cmp_pow2_bit(k, 32n, w, hz, lt)),
          hlt)
      Arr.word_zero_from_of_bit_false(k, 32n, w, hz,
        Arr.bool_not_true(Arr.word_bit(k, 32n, w), hnb))

def Arr.u32_zero_from_ge(+k: Nat, +u: U32,
    +hz: {Arr.u32_zero_from(1n+k, u) == True{} : Bool},
    +lt: {Nat.is_lt(k, 32n) == True{} : Bool},
    +hge: {U32.is_lt(u, Arr.pow2_u32(k)) == False{} : Bool}) ->
  {Arr.u32_zero_from(k, U32.sub(u, Arr.pow2_u32(k))) == True{} : Bool}:
  match u:
    case U32{+w}:
      +hnb : {Bool.not(Arr.word_bit(k, 32n, w)) == False{} : Bool} =
        Equal.trans(Bool,
          Bool.not(Arr.word_bit(k, 32n, w)),
          Cmp.is_lt(Word.cmp(32n, w, Arr.pow2_word(k, 32n))),
          False{},
          Equal.sym(Bool,
            Cmp.is_lt(Word.cmp(32n, w, Arr.pow2_word(k, 32n))),
            Bool.not(Arr.word_bit(k, 32n, w)),
            Arr.word_cmp_pow2_bit(k, 32n, w, hz, lt)),
          hge)
      Arr.word_sub_pow2_zero_from(k, 32n, w, hz,
        Arr.bool_not_false(Arr.word_bit(k, 32n, w), hnb))

# ---------------------------------------------------------------------------
# Word equality, subtraction injectivity, and `U32.is_eq` reflection
# ---------------------------------------------------------------------------

def Arr.word_head(+p: Nat, w: Word(1n+p)) -> Bool:
  match w:
    case WCon{b, t}:
      b

def Arr.word_tail(+p: Nat, w: Word(1n+p)) -> Word(p):
  match w:
    case WCon{b, t}:
      t

def Arr.full_add_inj_l(a1: Bool, a2: Bool, b: Bool, c: Bool,
    e: {Arr.fst(Bool, Bool, Bool.full_add(a1, b, c))
        == Arr.fst(Bool, Bool, Bool.full_add(a2, b, c)) : Bool}) ->
  {a1 == a2 : Bool}:
  match a1 a2 b c:
    case False{} False{} _ _:
      {==}
    case True{} True{} _ _:
      {==}
    case False{} True{} False{} False{}:
      e
    case False{} True{} False{} True{}:
      Equal.sym(Bool, True{}, False{}, e)
    case False{} True{} True{} False{}:
      Equal.sym(Bool, True{}, False{}, e)
    case False{} True{} True{} True{}:
      e
    case True{} False{} False{} False{}:
      e
    case True{} False{} False{} True{}:
      Equal.sym(Bool, False{}, True{}, e)
    case True{} False{} True{} False{}:
      Equal.sym(Bool, False{}, True{}, e)
    case True{} False{} True{} True{}:
      e

def Arr.word_adc_con_head(+p: Nat, +at: Word(p), +bt: Word(p), +f: Bool,
    sk: Bool & Bool) ->
  {Arr.word_head(p, Word.adc.con(p, at, bt, f, sk))
   == Arr.fst(Bool, Bool, sk) : Bool}:
  (s, k) = sk
  {==}

def Arr.word_adc_con_tail(+p: Nat, +at: Word(p), +bt: Word(p), +f: Bool,
    sk: Bool & Bool) ->
  {Arr.word_tail(p, Word.adc.con(p, at, bt, f, sk))
   == Word.adc(p, at, bt, f, Arr.snd(Bool, Bool, sk)) : Word(p)}:
  (s, k) = sk
  {==}

def Arr.word_adc_inj_step(+p: Nat, +a1: Bool, +a2: Bool, +at1: Word(p),
    +at2: Word(p), +bb: Bool, +bt: Word(p), +f: Bool, +c: Bool, +b2: Bool,
    +e: {Word.adc.con(p, at1, bt, f, Bool.full_add(a1, b2, c))
        == Word.adc.con(p, at2, bt, f, Bool.full_add(a2, b2, c))
        : Word(1n+p)},
    ih: @c2: Bool ->
        {Word.adc(p, at1, bt, f, c2) == Word.adc(p, at2, bt, f, c2)
         : Word(p)} ->
        {at1 == at2 : Word(p)}) ->
  {WCon{a1, at1} == WCon{a2, at2} : Word(1n+p)}:
  +eh : {Arr.fst(Bool, Bool, Bool.full_add(a1, b2, c))
         == Arr.fst(Bool, Bool, Bool.full_add(a2, b2, c)) : Bool} =
    Equal.trans(Bool,
      Arr.fst(Bool, Bool, Bool.full_add(a1, b2, c)),
      Arr.word_head(p, Word.adc.con(p, at1, bt, f, Bool.full_add(a1, b2, c))),
      Arr.fst(Bool, Bool, Bool.full_add(a2, b2, c)),
      Equal.sym(Bool,
        Arr.word_head(p, Word.adc.con(p, at1, bt, f, Bool.full_add(a1, b2, c))),
        Arr.fst(Bool, Bool, Bool.full_add(a1, b2, c)),
        Arr.word_adc_con_head(p, at1, bt, f, Bool.full_add(a1, b2, c))),
      Equal.trans(Bool,
        Arr.word_head(p, Word.adc.con(p, at1, bt, f, Bool.full_add(a1, b2, c))),
        Arr.word_head(p, Word.adc.con(p, at2, bt, f, Bool.full_add(a2, b2, c))),
        Arr.fst(Bool, Bool, Bool.full_add(a2, b2, c)),
        Equal.cong(Word(1n+p), Bool, w => Arr.word_head(p, w),
          Word.adc.con(p, at1, bt, f, Bool.full_add(a1, b2, c)),
          Word.adc.con(p, at2, bt, f, Bool.full_add(a2, b2, c)), e),
        Arr.word_adc_con_head(p, at2, bt, f, Bool.full_add(a2, b2, c))))
  +ea : {a1 == a2 : Bool} = Arr.full_add_inj_l(a1, a2, b2, c, eh)
  +et0 : {Word.adc(p, at1, bt, f, Arr.snd(Bool, Bool, Bool.full_add(a1, b2, c)))
          == Word.adc(p, at2, bt, f, Arr.snd(Bool, Bool, Bool.full_add(a2, b2, c)))
          : Word(p)} =
    Equal.trans(Word(p),
      Word.adc(p, at1, bt, f, Arr.snd(Bool, Bool, Bool.full_add(a1, b2, c))),
      Arr.word_tail(p, Word.adc.con(p, at1, bt, f, Bool.full_add(a1, b2, c))),
      Word.adc(p, at2, bt, f, Arr.snd(Bool, Bool, Bool.full_add(a2, b2, c))),
      Equal.sym(Word(p),
        Arr.word_tail(p, Word.adc.con(p, at1, bt, f, Bool.full_add(a1, b2, c))),
        Word.adc(p, at1, bt, f, Arr.snd(Bool, Bool, Bool.full_add(a1, b2, c))),
        Arr.word_adc_con_tail(p, at1, bt, f, Bool.full_add(a1, b2, c))),
      Equal.trans(Word(p),
        Arr.word_tail(p, Word.adc.con(p, at1, bt, f, Bool.full_add(a1, b2, c))),
        Arr.word_tail(p, Word.adc.con(p, at2, bt, f, Bool.full_add(a2, b2, c))),
        Word.adc(p, at2, bt, f, Arr.snd(Bool, Bool, Bool.full_add(a2, b2, c))),
        Equal.cong(Word(1n+p), Word(p), w => Arr.word_tail(p, w),
          Word.adc.con(p, at1, bt, f, Bool.full_add(a1, b2, c)),
          Word.adc.con(p, at2, bt, f, Bool.full_add(a2, b2, c)), e),
        Arr.word_adc_con_tail(p, at2, bt, f, Bool.full_add(a2, b2, c))))
  +et1 : {Word.adc(p, at1, bt, f, Arr.snd(Bool, Bool, Bool.full_add(a2, b2, c)))
          == Word.adc(p, at2, bt, f, Arr.snd(Bool, Bool, Bool.full_add(a2, b2, c)))
          : Word(p)} =
    Equal.trans(Word(p),
      Word.adc(p, at1, bt, f, Arr.snd(Bool, Bool, Bool.full_add(a2, b2, c))),
      Word.adc(p, at1, bt, f, Arr.snd(Bool, Bool, Bool.full_add(a1, b2, c))),
      Word.adc(p, at2, bt, f, Arr.snd(Bool, Bool, Bool.full_add(a2, b2, c))),
      Equal.cong(Bool, Word(p),
        x => Word.adc(p, at1, bt, f, Arr.snd(Bool, Bool, Bool.full_add(x, b2, c))),
        a2, a1, Equal.sym(Bool, a1, a2, ea)),
      et0)
  +eat : {at1 == at2 : Word(p)} =
    ih(Arr.snd(Bool, Bool, Bool.full_add(a2, b2, c)), et1)
  Equal.trans(Word(1n+p),
    WCon{a1, at1}, WCon{a2, at1}, WCon{a2, at2},
    Equal.cong(Bool, Word(1n+p), x => WCon{x, at1}, a1, a2, ea),
    Equal.cong(Word(p), Word(1n+p), x => WCon{a2, x}, at1, at2, eat))

def Arr.word_adc_inj_l(+m: Nat, +a1: Word(m), +a2: Word(m), +b: Word(m),
    +f: Bool, +c: Bool,
    e: {Word.adc(m, a1, b, f, c) == Word.adc(m, a2, b, f, c) : Word(m)}) ->
  {a1 == a2 : Word(m)}:
  match m:
    case 0n:
      match a1 a2:
        case WNil{} WNil{}:
          {==}
    case 1n++p:
      match a1 a2 b f:
        case WCon{+ab1, +at1} WCon{+ab2, +at2} WCon{+bb, +bt} False{}:
          Arr.word_adc_inj_step(p, ab1, ab2, at1, at2, bb, bt, False{}, c, bb,
            e, c2 => e2 => Arr.word_adc_inj_l(p, at1, at2, bt, False{}, c2, e2))
        case WCon{+ab1, +at1} WCon{+ab2, +at2} WCon{+bb, +bt} True{}:
          Arr.word_adc_inj_step(p, ab1, ab2, at1, at2, bb, bt, True{}, c,
            Bool.not(bb), e,
            c2 => e2 => Arr.word_adc_inj_l(p, at1, at2, bt, True{}, c2, e2))

def Arr.u32_word(u: U32) -> Word(32n):
  match u:
    case U32{x}:
      x

def Arr.u32_sub_inj_l(+i: U32, +j: U32, +h: U32,
    e: {U32.sub(i, h) == U32.sub(j, h) : U32}) -> {i == j : U32}:
  match i j h:
    case U32{+wi} U32{+wj} U32{+wh}:
      +ew : {Word.sub(32n, wi, wh) == Word.sub(32n, wj, wh) : Word(32n)} =
        Equal.cong(U32, Word(32n), Arr.u32_word,
          U32{Word.sub(32n, wi, wh)}, U32{Word.sub(32n, wj, wh)}, e)
      Equal.cong(Word(32n), U32, x => U32{x}, wi, wj,
        Arr.word_adc_inj_l(32n, wi, wj, wh, True{}, True{}, ew))

def Arr.word_cmp_refl(+m: Nat, +w: Word(m)) ->
  {Word.cmp(m, w, w) == EQ{} : Cmp}:
  match m:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++mp:
      match w:
        case WCon{b, +t}:
          match b:
            case False{}:
              Equal.cong(Cmp, Cmp, c => Word.cmp.fin(False{}, False{}, c),
                Word.cmp(mp, t, t), EQ{}, Arr.word_cmp_refl(mp, t))
            case True{}:
              Equal.cong(Cmp, Cmp, c => Word.cmp.fin(True{}, True{}, c),
                Word.cmp(mp, t, t), EQ{}, Arr.word_cmp_refl(mp, t))

def Arr.u32_is_eq_refl(+u: U32) -> {U32.is_eq(u, u) == True{} : Bool}:
  match u:
    case U32{+w}:
      Equal.cong(Cmp, Bool, c => Cmp.is_eq(c),
        Word.cmp(32n, w, w), EQ{}, Arr.word_cmp_refl(32n, w))

def Arr.u32_ne_of_eq_false(+i: U32, +j: U32,
    +ef: {U32.is_eq(i, j) == False{} : Bool},
    eq: {i == j : U32}) -> Empty:
  +et : {U32.is_eq(i, j) == True{} : Bool} =
    Equal.trans(Bool, U32.is_eq(i, j), U32.is_eq(j, j), True{},
      Equal.cong(U32, Bool, x => U32.is_eq(x, j), i, j, eq),
      Arr.u32_is_eq_refl(j))
  Logic.Proof.false_ne_true(
    Equal.trans(Bool, False{}, U32.is_eq(i, j), True{},
      Equal.sym(Bool, U32.is_eq(i, j), False{}, ef), et))

def Arr.bool_cmp_eq_true(a: Bool, b: Bool,
    e: {Cmp.is_eq(Bool.cmp(a, b)) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case True{} True{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, Logic.Proof.false_ne_true(e))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, Logic.Proof.false_ne_true(e))

def Arr.word_cmp_fin_eq_l(a: Bool, b: Bool, c: Cmp,
    e: {Cmp.is_eq(Word.cmp.fin(a, b, c)) == True{} : Bool}) ->
  {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, Logic.Proof.false_ne_true(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, Logic.Proof.false_ne_true(e))

def Arr.word_cmp_fin_eq_b(a: Bool, b: Bool, c: Cmp,
    e: {Cmp.is_eq(Word.cmp.fin(a, b, c)) == True{} : Bool}) ->
  {a == b : Bool}:
  match c:
    case LT{}:
      Empty.absurd({a == b : Bool}, Logic.Proof.false_ne_true(e))
    case EQ{}:
      Arr.bool_cmp_eq_true(a, b, e)
    case GT{}:
      Empty.absurd({a == b : Bool}, Logic.Proof.false_ne_true(e))

def Arr.word_cmp_eq_true(+m: Nat, +a: Word(m), +b: Word(m),
    +e: {Cmp.is_eq(Word.cmp(m, a, b)) == True{} : Bool}) ->
  {a == b : Word(m)}:
  match m:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n++mp:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          +eh : {ab == bb : Bool} =
            Arr.word_cmp_fin_eq_b(ab, bb, Word.cmp(mp, at, bt), e)
          +et : {at == bt : Word(mp)} =
            Arr.word_cmp_eq_true(mp, at, bt,
              Arr.word_cmp_fin_eq_l(ab, bb, Word.cmp(mp, at, bt), e))
          Equal.trans(Word(1n+mp),
            WCon{ab, at}, WCon{bb, at}, WCon{bb, bt},
            Equal.cong(Bool, Word(1n+mp), x => WCon{x, at}, ab, bb, eh),
            Equal.cong(Word(mp), Word(1n+mp), x => WCon{bb, x}, at, bt, et))

def Arr.u32_is_eq_true(+a: U32, +b: U32,
    e: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+wa} U32{+wb}:
      Equal.cong(Word(32n), U32, x => U32{x}, wa, wb,
        Arr.word_cmp_eq_true(32n, wa, wb, e))

def Arr.u32_sub_ne_go(+i: U32, +j: U32, +h: U32,
    +ef: {U32.is_eq(i, j) == False{} : Bool},
    eqb: Bool, +ee: {eqb == U32.is_eq(U32.sub(i, h), U32.sub(j, h)) : Bool}) ->
  {U32.is_eq(U32.sub(i, h), U32.sub(j, h)) == False{} : Bool}:
  match eqb:
    case False{}:
      Equal.sym(Bool, False{}, U32.is_eq(U32.sub(i, h), U32.sub(j, h)), ee)
    case True{}:
      +esub : {U32.sub(i, h) == U32.sub(j, h) : U32} =
        Arr.u32_is_eq_true(U32.sub(i, h), U32.sub(j, h),
          Equal.sym(Bool, True{}, U32.is_eq(U32.sub(i, h), U32.sub(j, h)), ee))
      Empty.absurd(
        {U32.is_eq(U32.sub(i, h), U32.sub(j, h)) == False{} : Bool},
        Arr.u32_ne_of_eq_false(i, j, ef, Arr.u32_sub_inj_l(i, j, h, esub)))

def Arr.u32_sub_ne(+i: U32, +j: U32, +h: U32,
    +ef: {U32.is_eq(i, j) == False{} : Bool}) ->
  {U32.is_eq(U32.sub(i, h), U32.sub(j, h)) == False{} : Bool}:
  Arr.u32_sub_ne_go(i, j, h, ef, U32.is_eq(U32.sub(i, h), U32.sub(j, h)), {==})

# ---------------------------------------------------------------------------
# Array depth, size, read, and swap laws
# ---------------------------------------------------------------------------

type Arr.DPair<-A: Data, -B: Data> is Data:
  DPair{l: A, r: B}

def Arr.dpair_l(-A: Data, -B: Data, p: Arr.DPair<A, B>) -> A:
  DPair{l, r} = p
  l

def Arr.dpair_r(-A: Data, -B: Data, p: Arr.DPair<A, B>) -> B:
  DPair{l, r} = p
  r

def Arr.Depth(-T: Type, d: Nat, a: Array<T>) -> Data:
  match d a:
    case 0n ALeaf{_}:
      Unit
    case 1n++p ANode{xs, ys}:
      Arr.DPair<Arr.Depth(T, p, xs), Arr.Depth(T, p, ys)>
    case _ _:
      Empty

def Arr.depth_transport(-T: Type, +d: Nat, -a1: Array<T>, -a2: Array<T>,
    e: {a1 == a2 : Array<T>}, hd: Arr.Depth(T, d, a1)) -> Arr.Depth(T, d, a2):
  %e : Arr.Depth(T, d, _)
  hd

def Arr.depth_new(-T: Data, +d: Nat, +v: T) -> Arr.Depth(T, d, Array.new(T, d, v)):
  match d:
    case 0n:
      Unit{}
    case 1n++p:
      DPair{Arr.depth_new(T, p, v), Arr.depth_new(T, p, v)}

def Arr.size_node_fst(-T: Type, -ys: Array<T>, r: Array<T> & U32,
    -xs: Array<T>, ih: {Arr.fst(Array<T>, U32, r) == xs : Array<T>}) ->
  {Arr.fst(Array<T>, U32, Array.size.node(T, ys, r)) == ANode{xs, ys}
   : Array<T>}:
  (xs2, n) = r
  Equal.cong(Array<T>, Array<T>, l => ANode{l, ys}, xs2, xs, ih)

def Arr.size_fst_node(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>,
    +hdx: Arr.Depth(T, p, xs),
    d: &a1: Array<T> -> &a2: Array<T> ->
       {a1 == xs : Array<T>} & {a2 == a1 : Array<T>},
    ih: @xs2: Array<T> -> Arr.Depth(T, p, xs2) ->
        {Arr.fst(Array<T>, U32, Array.size(T, xs2)) == xs2 : Array<T>}) ->
  {Arr.fst(Array<T>, U32, Array.size(T, ANode{xs, ys})) == ANode{xs, ys}
   : Array<T>}:
  (xs1, d2) = d
  (xs2, pe) = d2
  (+ex1, +ex2) = pe
  +hdx2 : Arr.Depth(T, p, xs2) =
    Arr.depth_transport(T, p, xs, xs2,
      Equal.sym(Array<T>, xs2, xs, Equal.trans(Array<T>, xs2, xs1, xs, ex2, ex1)),
      hdx)
  +p1 : {Arr.fst(Array<T>, U32, Array.size(T, xs1)) == xs1 : Array<T>} =
    Equal.trans(Array<T>,
      Arr.fst(Array<T>, U32, Array.size(T, xs1)),
      Arr.fst(Array<T>, U32, Array.size(T, xs2)),
      xs1,
      Equal.cong(Array<T>, Array<T>, x => Arr.fst(Array<T>, U32, Array.size(T, x)),
        xs1, xs2, Equal.sym(Array<T>, xs2, xs1, ex2)),
      Equal.trans(Array<T>,
        Arr.fst(Array<T>, U32, Array.size(T, xs2)), xs2, xs1,
        ih(xs2, hdx2), ex2))
  %ex1 : {Arr.fst(Array<T>, U32, Array.size(T, ANode{_, ys})) == ANode{_, ys}
          : Array<T>}
  Arr.size_node_fst(T, ys, Array.size(T, xs1), xs1, p1)

def Arr.size_fst(-T: Data, +d: Nat, a: Array<T>, +hd: Arr.Depth(T, d, a)) ->
  {Arr.fst(Array<T>, U32, Array.size(T, a)) == a : Array<T>}:
  match d a:
    case 0n ALeaf{x}:
      {==}
    case 1n++p ANode{xs, ys}:
      DPair{+hdx, +hdy} = hd
      Arr.size_fst_node(T, p, xs, ys, hdx, Arr.dup(T, xs),
        x => h => Arr.size_fst(T, p, x, h))
    case 0n ANode{xs, ys}:
      Empty.absurd(
        {Arr.fst(Array<T>, U32, Array.size(T, ANode{xs, ys})) == ANode{xs, ys}
         : Array<T>}, hd)
    case 1n++p ALeaf{x}:
      Empty.absurd(
        {Arr.fst(Array<T>, U32, Array.size(T, ALeaf{x})) == ALeaf{x}
         : Array<T>}, hd)

def Arr.size_node_snd(-T: Type, -ys: Array<T>, r: Array<T> & U32, +p: Nat,
    ih: {Arr.snd(Array<T>, U32, r) == Arr.pow2_u32(p) : U32}) ->
  {Arr.snd(Array<T>, U32, Array.size.node(T, ys, r)) == Arr.pow2_u32(1n+p)
   : U32}:
  (xs2, n) = r
  Equal.trans(U32,
    U32.shl(n), U32.shl(Arr.pow2_u32(p)), Arr.pow2_u32(1n+p),
    Equal.cong(U32, U32, u => U32.shl(u), n, Arr.pow2_u32(p), ih),
    Arr.u32_shl_pow2(p))

def Arr.size_of_depth_node(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>,
    d: &a1: Array<T> -> &a2: Array<T> ->
       {a1 == xs : Array<T>} & {a2 == a1 : Array<T>},
    +hdx: Arr.Depth(T, p, xs),
    ih: @xs2: Array<T> -> Arr.Depth(T, p, xs2) ->
        {Arr.snd(Array<T>, U32, Array.size(T, xs2)) == Arr.pow2_u32(p) : U32}) ->
  {Arr.snd(Array<T>, U32, Array.size(T, ANode{xs, ys})) == Arr.pow2_u32(1n+p)
   : U32}:
  (xs1, d2) = d
  (xs2, pe) = d2
  (+ex1, +ex2) = pe
  +hdx2 : Arr.Depth(T, p, xs2) =
    Arr.depth_transport(T, p, xs, xs2,
      Equal.sym(Array<T>, xs2, xs, Equal.trans(Array<T>, xs2, xs1, xs, ex2, ex1)),
      hdx)
  +p1 : {Arr.snd(Array<T>, U32, Array.size(T, xs1)) == Arr.pow2_u32(p) : U32} =
    Equal.trans(U32,
      Arr.snd(Array<T>, U32, Array.size(T, xs1)),
      Arr.snd(Array<T>, U32, Array.size(T, xs2)),
      Arr.pow2_u32(p),
      Equal.cong(Array<T>, U32, x => Arr.snd(Array<T>, U32, Array.size(T, x)),
        xs1, xs2, Equal.sym(Array<T>, xs2, xs1, ex2)),
      ih(xs2, hdx2))
  %ex1 : {Arr.snd(Array<T>, U32, Array.size(T, ANode{_, ys}))
          == Arr.pow2_u32(1n+p) : U32}
  Arr.size_node_snd(T, ys, Array.size(T, xs1), p, p1)

def Arr.size_of_depth(-T: Data, +d: Nat, a: Array<T>, +hd: Arr.Depth(T, d, a)) ->
  {Arr.snd(Array<T>, U32, Array.size(T, a)) == Arr.pow2_u32(d) : U32}:
  match d a:
    case 0n ALeaf{x}:
      {==}
    case 1n++p ANode{xs, ys}:
      DPair{+hdx, +hdy} = hd
      Arr.size_of_depth_node(T, p, xs, ys, Arr.dup(T, xs), hdx,
        x => h => Arr.size_of_depth(T, p, x, h))
    case 0n ANode{xs, ys}:
      Empty.absurd(
        {Arr.snd(Array<T>, U32, Array.size(T, ANode{xs, ys})) == Arr.pow2_u32(0n)
         : U32}, hd)
    case 1n++p ALeaf{x}:
      Empty.absurd(
        {Arr.snd(Array<T>, U32, Array.size(T, ALeaf{x})) == Arr.pow2_u32(1n+p)
         : U32}, hd)

def Arr.depth_swap_lo(-T: Type, +p: Nat, -ys: Array<T>, r: Array<T> & T,
    +hdx: Arr.Depth(T, p, Arr.fst(Array<T>, T, r)),
    +hdy: Arr.Depth(T, p, ys)) ->
  Arr.Depth(T, 1n+p, Arr.fst(Array<T>, T, Array.swap.lo(T, ys, r))):
  (nxs, old) = r
  DPair{hdx, hdy}

def Arr.depth_swap_hi(-T: Type, +p: Nat, -xs: Array<T>, r: Array<T> & T,
    +hdx: Arr.Depth(T, p, xs),
    +hdy: Arr.Depth(T, p, Arr.fst(Array<T>, T, r))) ->
  Arr.Depth(T, 1n+p, Arr.fst(Array<T>, T, Array.swap.hi(T, xs, r))):
  (nys, old) = r
  DPair{hdx, hdy}

def Arr.depth_swap_go_lo(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>,
    +n: U32, +i: U32, +v: T,
    d: &a1: Array<T> -> &a2: Array<T> ->
       {a1 == xs : Array<T>} & {a2 == a1 : Array<T>},
    +hdx: Arr.Depth(T, p, xs), +hdy: Arr.Depth(T, p, ys),
    ih: @xs2: Array<T> -> Arr.Depth(T, p, xs2) ->
        Arr.Depth(T, p, Arr.fst(Array<T>, T,
          Array.swap.go(T, xs2, U32.shr(n), i, v,
            U32.is_lt(i, U32.shr(U32.shr(n))))))) ->
  Arr.Depth(T, 1n+p, Arr.fst(Array<T>, T,
    Array.swap.go(T, ANode{xs, ys}, n, i, v, True{}))):
  (xs1, d2) = d
  (xs2, pe) = d2
  (+ex1, +ex2) = pe
  +h = U32.shr(n)
  +z2 = U32.is_lt(i, U32.shr(h))
  +hdx2 : Arr.Depth(T, p, xs2) =
    Arr.depth_transport(T, p, xs, xs2,
      Equal.sym(Array<T>, xs2, xs, Equal.trans(Array<T>, xs2, xs1, xs, ex2, ex1)),
      hdx)
  +hd_res : Arr.Depth(T, p, Arr.fst(Array<T>, T, Array.swap.go(T, xs1, h, i, v, z2))) =
    Arr.depth_transport(T, p,
      Arr.fst(Array<T>, T, Array.swap.go(T, xs2, h, i, v, z2)),
      Arr.fst(Array<T>, T, Array.swap.go(T, xs1, h, i, v, z2)),
      Equal.cong(Array<T>, Array<T>,
        x => Arr.fst(Array<T>, T, Array.swap.go(T, x, h, i, v, z2)),
        xs2, xs1, ex2),
      ih(xs2, hdx2))
  %ex1 : Arr.Depth(T, 1n+p, Arr.fst(Array<T>, T,
           Array.swap.go(T, ANode{_, ys}, n, i, v, True{})))
  Arr.depth_swap_lo(T, p, ys, Array.swap.go(T, xs1, h, i, v, z2), hd_res, hdy)

def Arr.depth_swap_go_hi(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>,
    +n: U32, +i: U32, +v: T,
    d: &a1: Array<T> -> &a2: Array<T> ->
       {a1 == ys : Array<T>} & {a2 == a1 : Array<T>},
    +hdx: Arr.Depth(T, p, xs), +hdy: Arr.Depth(T, p, ys),
    ih: @ys2: Array<T> -> Arr.Depth(T, p, ys2) ->
        Arr.Depth(T, p, Arr.fst(Array<T>, T,
          Array.swap.go(T, ys2, U32.shr(n), U32.sub(i, U32.shr(n)), v,
            U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))))) ->
  Arr.Depth(T, 1n+p, Arr.fst(Array<T>, T,
    Array.swap.go(T, ANode{xs, ys}, n, i, v, False{}))):
  (ys1, d2) = d
  (ys2, pe) = d2
  (+ey1, +ey2) = pe
  +h = U32.shr(n)
  +j = U32.sub(i, h)
  +z2 = U32.is_lt(j, U32.shr(h))
  +hdy2 : Arr.Depth(T, p, ys2) =
    Arr.depth_transport(T, p, ys, ys2,
      Equal.sym(Array<T>, ys2, ys, Equal.trans(Array<T>, ys2, ys1, ys, ey2, ey1)),
      hdy)
  +hd_res : Arr.Depth(T, p, Arr.fst(Array<T>, T, Array.swap.go(T, ys1, h, j, v, z2))) =
    Arr.depth_transport(T, p,
      Arr.fst(Array<T>, T, Array.swap.go(T, ys2, h, j, v, z2)),
      Arr.fst(Array<T>, T, Array.swap.go(T, ys1, h, j, v, z2)),
      Equal.cong(Array<T>, Array<T>,
        x => Arr.fst(Array<T>, T, Array.swap.go(T, x, h, j, v, z2)),
        ys2, ys1, ey2),
      ih(ys2, hdy2))
  %ey1 : Arr.Depth(T, 1n+p, Arr.fst(Array<T>, T,
           Array.swap.go(T, ANode{xs, _}, n, i, v, False{})))
  Arr.depth_swap_hi(T, p, xs, Array.swap.go(T, ys1, h, j, v, z2), hdx, hd_res)

def Arr.depth_swap_go(-T: Data, +d: Nat, a: Array<T>, +n: U32, +i: U32, +v: T,
    z: Bool, +hd: Arr.Depth(T, d, a)) ->
  Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap.go(T, a, n, i, v, z))):
  match d a z:
    case 0n ALeaf{x} _:
      Unit{}
    case 1n++p ANode{xs, ys} True{}:
      DPair{+hdx, +hdy} = hd
      +h = U32.shr(n)
      +z2 = U32.is_lt(i, U32.shr(h))
      Arr.depth_swap_go_lo(T, p, xs, ys, n, i, v, Arr.dup(T, xs), hdx, hdy,
        x => hx => Arr.depth_swap_go(T, p, x, h, i, v, z2, hx))
    case 1n++p ANode{xs, ys} False{}:
      DPair{+hdx, +hdy} = hd
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      +z2 = U32.is_lt(j, U32.shr(h))
      Arr.depth_swap_go_hi(T, p, xs, ys, n, i, v, Arr.dup(T, ys), hdx, hdy,
        y => hy => Arr.depth_swap_go(T, p, y, h, j, v, z2, hy))
    case 0n ANode{xs, ys} _:
      Empty.absurd(
        Arr.Depth(T, 0n, Arr.fst(Array<T>, T,
          Array.swap.go(T, ANode{xs, ys}, n, i, v, z))), hd)
    case 1n++p ALeaf{x} _:
      Empty.absurd(
        Arr.Depth(T, 1n+p, Arr.fst(Array<T>, T,
          Array.swap.go(T, ALeaf{x}, n, i, v, z))), hd)

def Arr.depth_swap_at(-T: Data, +d: Nat, +i: U32, +v: T, an: Array<T> & U32,
    +hd: Arr.Depth(T, d, Arr.fst(Array<T>, U32, an))) ->
  Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap.at(T, i, v, an))):
  (a, +n) = an
  +j = U32.and(i, U32.sub(n, 1))
  Arr.depth_swap_go(T, d, a, n, j, v, U32.is_lt(j, U32.shr(n)), hd)

def Arr.depth_swap_dup(-T: Data, +d: Nat, -a: Array<T>, +i: U32, +v: T,
    dp: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == a : Array<T>} & {a2 == a1 : Array<T>},
    +hd: Arr.Depth(T, d, a)) ->
  Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, a, i, v))):
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  +hd1 : Arr.Depth(T, d, a1) =
    Arr.depth_transport(T, d, a, a1, Equal.sym(Array<T>, a1, a, ea1), hd)
  +hd2 : Arr.Depth(T, d, a2) =
    Arr.depth_transport(T, d, a1, a2, Equal.sym(Array<T>, a2, a1, ea2), hd1)
  +hd_an : Arr.Depth(T, d, Arr.fst(Array<T>, U32, Array.size(T, a1))) =
    Arr.depth_transport(T, d, a1, Arr.fst(Array<T>, U32, Array.size(T, a1)),
      Equal.sym(Array<T>, Arr.fst(Array<T>, U32, Array.size(T, a1)), a1,
        Equal.trans(Array<T>,
          Arr.fst(Array<T>, U32, Array.size(T, a1)),
          Arr.fst(Array<T>, U32, Array.size(T, a2)),
          a1,
          Equal.cong(Array<T>, Array<T>,
            x => Arr.fst(Array<T>, U32, Array.size(T, x)),
            a1, a2, Equal.sym(Array<T>, a2, a1, ea2)),
          Equal.trans(Array<T>,
            Arr.fst(Array<T>, U32, Array.size(T, a2)), a2, a1,
            Arr.size_fst(T, d, a2, hd2), ea2))),
      hd1)
  %ea1 : Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, _, i, v)))
  Arr.depth_swap_at(T, d, i, v, Array.size(T, a1), hd_an)

def Arr.depth_swap(-T: Data, +d: Nat, a: Array<T>, +i: U32, +v: T,
    +hd: Arr.Depth(T, d, a)) ->
  Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, a, i, v))):
  Arr.depth_swap_dup(T, d, a, i, v, Arr.dup(T, a), hd)

def Arr.set_eq_fst_swap(-T: Type, r: Array<T> & T) ->
  {Array.set.fin(T, r) == Arr.fst(Array<T>, T, r) : Array<T>}:
  (na, old) = r
  {==}

def Arr.set_eq_dup(-T: Data, -a: Array<T>, +i: U32, +v: T,
    dp: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == a : Array<T>} & {a2 == a1 : Array<T>}) ->
  {Array.set(T, a, i, v) == Arr.fst(Array<T>, T, Array.swap(T, a, i, v))
   : Array<T>}:
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  %ea1 : {Array.set(T, _, i, v) == Arr.fst(Array<T>, T, Array.swap(T, _, i, v))
          : Array<T>}
  Arr.set_eq_fst_swap(T, Array.swap(T, a1, i, v))

def Arr.set_eq(-T: Data, a: Array<T>, +i: U32, +v: T) ->
  {Array.set(T, a, i, v) == Arr.fst(Array<T>, T, Array.swap(T, a, i, v))
   : Array<T>}:
  Arr.set_eq_dup(T, a, i, v, Arr.dup(T, a))

def Arr.depth_set_dup(-T: Data, +d: Nat, -a: Array<T>, +i: U32, +v: T,
    dp: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == a : Array<T>} & {a2 == a1 : Array<T>},
    +hd: Arr.Depth(T, d, a)) -> Arr.Depth(T, d, Array.set(T, a, i, v)):
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  +hd1 : Arr.Depth(T, d, a1) =
    Arr.depth_transport(T, d, a, a1, Equal.sym(Array<T>, a1, a, ea1), hd)
  +hd_sw : Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v))) =
    Arr.depth_swap(T, d, a1, i, v, hd1)
  +eset : {Array.set(T, a1, i, v) == Arr.fst(Array<T>, T, Array.swap(T, a1, i, v))
           : Array<T>} =
    Equal.trans(Array<T>,
      Array.set(T, a1, i, v),
      Array.set(T, a2, i, v),
      Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)),
      Equal.cong(Array<T>, Array<T>, x => Array.set(T, x, i, v),
        a1, a2, Equal.sym(Array<T>, a2, a1, ea2)),
      Equal.trans(Array<T>,
        Array.set(T, a2, i, v),
        Arr.fst(Array<T>, T, Array.swap(T, a2, i, v)),
        Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)),
        Arr.set_eq(T, a2, i, v),
        Equal.cong(Array<T>, Array<T>,
          x => Arr.fst(Array<T>, T, Array.swap(T, x, i, v)),
          a2, a1, ea2)))
  %ea1 : Arr.Depth(T, d, Array.set(T, _, i, v))
  Arr.depth_transport(T, d,
    Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)),
    Array.set(T, a1, i, v),
    Equal.sym(Array<T>, Array.set(T, a1, i, v),
      Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), eset),
    hd_sw)

def Arr.depth_set(-T: Data, +d: Nat, a: Array<T>, +i: U32, +v: T,
    +hd: Arr.Depth(T, d, a)) -> Arr.Depth(T, d, Array.set(T, a, i, v)):
  Arr.depth_set_dup(T, d, a, i, v, Arr.dup(T, a), hd)

# Common pair-projection lemmas for `Array.swap.lo` and `Array.swap.hi`.
def Arr.fst_lo(-T: Type, -ys: Array<T>, g: Array<T> & T, -xs: Array<T>,
    ih: {Arr.fst(Array<T>, T, g) == xs : Array<T>}) ->
  {Arr.fst(Array<T>, T, Array.swap.lo(T, ys, g)) == ANode{xs, ys} : Array<T>}:
  (a2, res) = g
  Equal.cong(Array<T>, Array<T>, l => ANode{l, ys}, a2, xs, ih)

def Arr.fst_hi(-T: Type, -xs: Array<T>, g: Array<T> & T, -ys: Array<T>,
    ih: {Arr.fst(Array<T>, T, g) == ys : Array<T>}) ->
  {Arr.fst(Array<T>, T, Array.swap.hi(T, xs, g)) == ANode{xs, ys} : Array<T>}:
  (a2, res) = g
  Equal.cong(Array<T>, Array<T>, r => ANode{xs, r}, a2, ys, ih)

def Arr.snd_lo(-T: Type, -ys: Array<T>, g: Array<T> & T, -v: T,
    ih: {Arr.snd(Array<T>, T, g) == v : T}) ->
  {Arr.snd(Array<T>, T, Array.swap.lo(T, ys, g)) == v : T}:
  (a2, res) = g
  ih

def Arr.snd_hi(-T: Type, -xs: Array<T>, g: Array<T> & T, -v: T,
    ih: {Arr.snd(Array<T>, T, g) == v : T}) ->
  {Arr.snd(Array<T>, T, Array.swap.hi(T, xs, g)) == v : T}:
  (a2, res) = g
  ih

# Reading an array leaves the returned array equal to the input array.
def Arr.get_fst_go_lo(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>, +n: U32,
    +i: U32, +hdx: Arr.Depth(T, p, xs),
    d: &a1: Array<T> -> &a2: Array<T> ->
       {a1 == xs : Array<T>} & {a2 == a1 : Array<T>},
    ih: @xs2: Array<T> -> Arr.Depth(T, p, xs2) ->
        {Arr.fst(Array<T>, T,
           Array.get.go(T, xs2, U32.shr(n), i,
             U32.is_lt(i, U32.shr(U32.shr(n))))) == xs2 : Array<T>}) ->
  {Arr.fst(Array<T>, T, Array.get.go(T, ANode{xs, ys}, n, i, True{}))
   == ANode{xs, ys} : Array<T>}:
  (xs1, d2) = d
  (xs2, pe) = d2
  (+ex1, +ex2) = pe
  +h = U32.shr(n)
  +z2 = U32.is_lt(i, U32.shr(h))
  +hdx2 : Arr.Depth(T, p, xs2) =
    Arr.depth_transport(T, p, xs, xs2,
      Equal.sym(Array<T>, xs2, xs, Equal.trans(Array<T>, xs2, xs1, xs, ex2, ex1)),
      hdx)
  +p1 : {Arr.fst(Array<T>, T, Array.get.go(T, xs1, h, i, z2)) == xs1
         : Array<T>} =
    Equal.trans(Array<T>,
      Arr.fst(Array<T>, T, Array.get.go(T, xs1, h, i, z2)),
      Arr.fst(Array<T>, T, Array.get.go(T, xs2, h, i, z2)),
      xs1,
      Equal.cong(Array<T>, Array<T>,
        x => Arr.fst(Array<T>, T, Array.get.go(T, x, h, i, z2)),
        xs1, xs2, Equal.sym(Array<T>, xs2, xs1, ex2)),
      Equal.trans(Array<T>,
        Arr.fst(Array<T>, T, Array.get.go(T, xs2, h, i, z2)), xs2, xs1,
        ih(xs2, hdx2), ex2))
  %ex1 : {Arr.fst(Array<T>, T, Array.get.go(T, ANode{_, ys}, n, i, True{}))
          == ANode{_, ys} : Array<T>}
  Arr.fst_lo(T, ys, Array.get.go(T, xs1, h, i, z2), xs1, p1)

def Arr.get_fst_go_hi(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>, +n: U32,
    +i: U32, +hdy: Arr.Depth(T, p, ys),
    d: &a1: Array<T> -> &a2: Array<T> ->
       {a1 == ys : Array<T>} & {a2 == a1 : Array<T>},
    ih: @ys2: Array<T> -> Arr.Depth(T, p, ys2) ->
        {Arr.fst(Array<T>, T,
           Array.get.go(T, ys2, U32.shr(n), U32.sub(i, U32.shr(n)),
             U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))) == ys2
         : Array<T>}) ->
  {Arr.fst(Array<T>, T, Array.get.go(T, ANode{xs, ys}, n, i, False{}))
   == ANode{xs, ys} : Array<T>}:
  (ys1, d2) = d
  (ys2, pe) = d2
  (+ey1, +ey2) = pe
  +h = U32.shr(n)
  +j = U32.sub(i, h)
  +z2 = U32.is_lt(j, U32.shr(h))
  +hdy2 : Arr.Depth(T, p, ys2) =
    Arr.depth_transport(T, p, ys, ys2,
      Equal.sym(Array<T>, ys2, ys, Equal.trans(Array<T>, ys2, ys1, ys, ey2, ey1)),
      hdy)
  +p1 : {Arr.fst(Array<T>, T, Array.get.go(T, ys1, h, j, z2)) == ys1
         : Array<T>} =
    Equal.trans(Array<T>,
      Arr.fst(Array<T>, T, Array.get.go(T, ys1, h, j, z2)),
      Arr.fst(Array<T>, T, Array.get.go(T, ys2, h, j, z2)),
      ys1,
      Equal.cong(Array<T>, Array<T>,
        x => Arr.fst(Array<T>, T, Array.get.go(T, x, h, j, z2)),
        ys1, ys2, Equal.sym(Array<T>, ys2, ys1, ey2)),
      Equal.trans(Array<T>,
        Arr.fst(Array<T>, T, Array.get.go(T, ys2, h, j, z2)), ys2, ys1,
        ih(ys2, hdy2), ey2))
  %ey1 : {Arr.fst(Array<T>, T, Array.get.go(T, ANode{xs, _}, n, i, False{}))
          == ANode{xs, _} : Array<T>}
  Arr.fst_hi(T, xs, Array.get.go(T, ys1, h, j, z2), ys1, p1)

def Arr.get_fst_go(-T: Data, +d: Nat, a: Array<T>, +n: U32, +i: U32, z: Bool,
    +hd: Arr.Depth(T, d, a)) ->
  {Arr.fst(Array<T>, T, Array.get.go(T, a, n, i, z)) == a : Array<T>}:
  match d a z:
    case 0n ALeaf{+x} _:
      {==}
    case 1n++p ANode{xs, ys} True{}:
      DPair{+hdx, +hdy} = hd
      +h = U32.shr(n)
      +z2 = U32.is_lt(i, U32.shr(h))
      Arr.get_fst_go_lo(T, p, xs, ys, n, i, hdx, Arr.dup(T, xs),
        x => hx => Arr.get_fst_go(T, p, x, h, i, z2, hx))
    case 1n++p ANode{xs, ys} False{}:
      DPair{+hdx, +hdy} = hd
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      +z2 = U32.is_lt(j, U32.shr(h))
      Arr.get_fst_go_hi(T, p, xs, ys, n, i, hdy, Arr.dup(T, ys),
        y => hy => Arr.get_fst_go(T, p, y, h, j, z2, hy))
    case 0n ANode{xs, ys} _:
      Empty.absurd(
        {Arr.fst(Array<T>, T, Array.get.go(T, ANode{xs, ys}, n, i, z))
         == ANode{xs, ys} : Array<T>}, hd)
    case 1n++p ALeaf{x} _:
      Empty.absurd(
        {Arr.fst(Array<T>, T, Array.get.go(T, ALeaf{x}, n, i, z))
         == ALeaf{x} : Array<T>}, hd)

def Arr.get_fst_at(-T: Data, +d: Nat, +i: U32, an: Array<T> & U32,
    +hd: Arr.Depth(T, d, Arr.fst(Array<T>, U32, an))) ->
  {Arr.fst(Array<T>, T, Array.get.at(T, i, an)) == Arr.fst(Array<T>, U32, an)
   : Array<T>}:
  (a, +n) = an
  +j = U32.and(i, U32.sub(n, 1))
  Arr.get_fst_go(T, d, a, n, j, U32.is_lt(j, U32.shr(n)), hd)

def Arr.get_fst_dup(-T: Data, +d: Nat, -a: Array<T>, +i: U32,
    +hd: Arr.Depth(T, d, a),
    dp: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == a : Array<T>} & {a2 == a1 : Array<T>}) ->
  {Arr.fst(Array<T>, T, Array.get(T, a, i)) == a : Array<T>}:
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  +hd1 : Arr.Depth(T, d, a1) =
    Arr.depth_transport(T, d, a, a1, Equal.sym(Array<T>, a1, a, ea1), hd)
  +hd2 : Arr.Depth(T, d, a2) =
    Arr.depth_transport(T, d, a1, a2, Equal.sym(Array<T>, a2, a1, ea2), hd1)
  +es : {Arr.fst(Array<T>, U32, Array.size(T, a1)) == a1 : Array<T>} =
    Equal.trans(Array<T>,
      Arr.fst(Array<T>, U32, Array.size(T, a1)),
      Arr.fst(Array<T>, U32, Array.size(T, a2)),
      a1,
      Equal.cong(Array<T>, Array<T>,
        x => Arr.fst(Array<T>, U32, Array.size(T, x)),
        a1, a2, Equal.sym(Array<T>, a2, a1, ea2)),
      Equal.trans(Array<T>,
        Arr.fst(Array<T>, U32, Array.size(T, a2)), a2, a1,
        Arr.size_fst(T, d, a2, hd2), ea2))
  +hd_an : Arr.Depth(T, d, Arr.fst(Array<T>, U32, Array.size(T, a1))) =
    Arr.depth_transport(T, d, a1, Arr.fst(Array<T>, U32, Array.size(T, a1)),
      Equal.sym(Array<T>, Arr.fst(Array<T>, U32, Array.size(T, a1)), a1, es),
      hd1)
  %ea1 : {Arr.fst(Array<T>, T, Array.get(T, _, i)) == _ : Array<T>}
  Equal.trans(Array<T>,
    Arr.fst(Array<T>, T, Array.get.at(T, i, Array.size(T, a1))),
    Arr.fst(Array<T>, U32, Array.size(T, a1)),
    a1,
    Arr.get_fst_at(T, d, i, Array.size(T, a1), hd_an),
    es)

def Arr.get_fst(-T: Data, +d: Nat, a: Array<T>, +i: U32,
    +hd: Arr.Depth(T, d, a)) ->
  {Arr.fst(Array<T>, T, Array.get(T, a, i)) == a : Array<T>}:
  Arr.get_fst_dup(T, d, a, i, hd, Arr.dup(T, a))

# Reading a freshly constructed `Array.new(T, d, v)` returns `v`.
def Arr.get_new_go(-T: Data, +d: Nat, +v: T, +n: U32, +i: U32, z: Bool) ->
  {Arr.snd(Array<T>, T, Array.get.go(T, Array.new(T, d, v), n, i, z)) == v : T}:
  match d z:
    case 0n _:
      {==}
    case 1n++p True{}:
      +h = U32.shr(n)
      +z2 = U32.is_lt(i, U32.shr(h))
      Arr.snd_lo(T, Array.new(T, p, v),
        Array.get.go(T, Array.new(T, p, v), h, i, z2), v,
        Arr.get_new_go(T, p, v, h, i, z2))
    case 1n++p False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      +z2 = U32.is_lt(j, U32.shr(h))
      Arr.snd_hi(T, Array.new(T, p, v),
        Array.get.go(T, Array.new(T, p, v), h, j, z2), v,
        Arr.get_new_go(T, p, v, h, j, z2))

def Arr.get_new_at(-T: Data, +d: Nat, +v: T, +i: U32, an: Array<T> & U32,
    ef: {Arr.fst(Array<T>, U32, an) == Array.new(T, d, v) : Array<T>}) ->
  {Arr.snd(Array<T>, T, Array.get.at(T, i, an)) == v : T}:
  (a, +n) = an
  +j = U32.and(i, U32.sub(n, 1))
  %Equal.sym(Array<T>, a, Array.new(T, d, v), ef) :
    {Arr.snd(Array<T>, T, Array.get.go(T, _, n, j, U32.is_lt(j, U32.shr(n))))
     == v : T}
  Arr.get_new_go(T, d, v, n, j, U32.is_lt(j, U32.shr(n)))

def Arr.get_new(-T: Data, +d: Nat, +v: T, +i: U32) ->
  {Arr.snd(Array<T>, T, Array.get(T, Array.new(T, d, v), i)) == v : T}:
  Arr.get_new_at(T, d, v, i, Array.size(T, Array.new(T, d, v)),
    Arr.size_fst(T, d, Array.new(T, d, v), Arr.depth_new(T, d, v)))

# `Array.swap` returns the prior value stored at index `i`.
def Arr.swap_old_lo(-T: Data, -ys: Array<T>, r: Array<T> & T, g: Array<T> & T,
    ih: {Arr.snd(Array<T>, T, r) == Arr.snd(Array<T>, T, g) : T}) ->
  {Arr.snd(Array<T>, T, Array.swap.lo(T, ys, r))
   == Arr.snd(Array<T>, T, Array.swap.lo(T, ys, g)) : T}:
  (r1, rv) = r
  (g1, gv) = g
  ih

def Arr.swap_old_hi(-T: Data, -xs: Array<T>, r: Array<T> & T, g: Array<T> & T,
    ih: {Arr.snd(Array<T>, T, r) == Arr.snd(Array<T>, T, g) : T}) ->
  {Arr.snd(Array<T>, T, Array.swap.hi(T, xs, r))
   == Arr.snd(Array<T>, T, Array.swap.hi(T, xs, g)) : T}:
  (r1, rv) = r
  (g1, gv) = g
  ih

def Arr.swap_old_go_lo2(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>,
    xs1: Array<T>, +n: U32, +i: U32, +v: T,
    +ex1: {xs1 == xs : Array<T>}, -xs2: Array<T>,
    +ex2: {xs2 == xs1 : Array<T>}, +hdx: Arr.Depth(T, p, xs),
    d2: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == xs2 : Array<T>} & {a2 == a1 : Array<T>},
    ih: @xs3: Array<T> -> Arr.Depth(T, p, xs3) ->
        {Arr.snd(Array<T>, T,
           Array.swap.go(T, xs3, U32.shr(n), i, v,
             U32.is_lt(i, U32.shr(U32.shr(n)))))
         == Arr.snd(Array<T>, T,
              Array.get.go(T, xs3, U32.shr(n), i,
                U32.is_lt(i, U32.shr(U32.shr(n))))) : T}) ->
  {Arr.snd(Array<T>, T, Array.swap.go(T, ANode{xs, ys}, n, i, v, True{}))
   == Arr.snd(Array<T>, T, Array.get.go(T, ANode{xs, ys}, n, i, True{})) : T}:
  (xs2a, d3) = d2
  (xs2b, pe2) = d3
  (+e2a, +e2b) = pe2
  +h = U32.shr(n)
  +z2 = U32.is_lt(i, U32.shr(h))
  +ea1 : {xs2a == xs1 : Array<T>} =
    Equal.trans(Array<T>, xs2a, xs2, xs1, e2a, ex2)
  +eb1 : {xs2b == xs1 : Array<T>} =
    Equal.trans(Array<T>, xs2b, xs2a, xs1, e2b, ea1)
  +hdx2b : Arr.Depth(T, p, xs2b) =
    Arr.depth_transport(T, p, xs, xs2b,
      Equal.sym(Array<T>, xs2b, xs, Equal.trans(Array<T>, xs2b, xs1, xs, eb1, ex1)),
      hdx)
  +p1 : {Arr.snd(Array<T>, T, Array.swap.go(T, xs1, h, i, v, z2))
         == Arr.snd(Array<T>, T, Array.get.go(T, xs2a, h, i, z2)) : T} =
    Equal.trans(T,
      Arr.snd(Array<T>, T, Array.swap.go(T, xs1, h, i, v, z2)),
      Arr.snd(Array<T>, T, Array.swap.go(T, xs2b, h, i, v, z2)),
      Arr.snd(Array<T>, T, Array.get.go(T, xs2a, h, i, z2)),
      Equal.cong(Array<T>, T,
        x => Arr.snd(Array<T>, T, Array.swap.go(T, x, h, i, v, z2)),
        xs1, xs2b, Equal.sym(Array<T>, xs2b, xs1, eb1)),
      Equal.trans(T,
        Arr.snd(Array<T>, T, Array.swap.go(T, xs2b, h, i, v, z2)),
        Arr.snd(Array<T>, T, Array.get.go(T, xs2b, h, i, z2)),
        Arr.snd(Array<T>, T, Array.get.go(T, xs2a, h, i, z2)),
        ih(xs2b, hdx2b),
        Equal.cong(Array<T>, T,
          x => Arr.snd(Array<T>, T, Array.get.go(T, x, h, i, z2)),
          xs2b, xs2a, e2b)))
  %ex1 : {Arr.snd(Array<T>, T, Array.swap.go(T, ANode{_, ys}, n, i, v, True{}))
          == Arr.snd(Array<T>, T, Array.get.go(T, ANode{_, ys}, n, i, True{}))
          : T}
  Equal.trans(T,
    Arr.snd(Array<T>, T, Array.swap.lo(T, ys, Array.swap.go(T, xs1, h, i, v, z2))),
    Arr.snd(Array<T>, T, Array.swap.lo(T, ys, Array.get.go(T, xs2a, h, i, z2))),
    Arr.snd(Array<T>, T, Array.swap.lo(T, ys, Array.get.go(T, xs1, h, i, z2))),
    Arr.swap_old_lo(T, ys,
      Array.swap.go(T, xs1, h, i, v, z2),
      Array.get.go(T, xs2a, h, i, z2), p1),
    Equal.cong(Array<T>, T,
      x => Arr.snd(Array<T>, T, Array.swap.lo(T, ys, Array.get.go(T, x, h, i, z2))),
      xs2a, xs1, ea1))

def Arr.swap_old_go_lo(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>, +n: U32,
    +i: U32, +v: T, +hdx: Arr.Depth(T, p, xs),
    d1: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == xs : Array<T>} & {a2 == a1 : Array<T>},
    ih: @xs3: Array<T> -> Arr.Depth(T, p, xs3) ->
        {Arr.snd(Array<T>, T,
           Array.swap.go(T, xs3, U32.shr(n), i, v,
             U32.is_lt(i, U32.shr(U32.shr(n)))))
         == Arr.snd(Array<T>, T,
              Array.get.go(T, xs3, U32.shr(n), i,
                U32.is_lt(i, U32.shr(U32.shr(n))))) : T}) ->
  {Arr.snd(Array<T>, T, Array.swap.go(T, ANode{xs, ys}, n, i, v, True{}))
   == Arr.snd(Array<T>, T, Array.get.go(T, ANode{xs, ys}, n, i, True{})) : T}:
  (xs1, d2) = d1
  (xs2, pe) = d2
  (+ex1, +ex2) = pe
  Arr.swap_old_go_lo2(T, p, xs, ys, xs1, n, i, v, ex1, xs2, ex2, hdx,
    Arr.dup(T, xs2), ih)

def Arr.swap_old_go_hi2(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>,
    ys1: Array<T>, +n: U32, +i: U32, +v: T,
    +ey1: {ys1 == ys : Array<T>}, -ys2: Array<T>,
    +ey2: {ys2 == ys1 : Array<T>}, +hdy: Arr.Depth(T, p, ys),
    d2: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == ys2 : Array<T>} & {a2 == a1 : Array<T>},
    ih: @ys3: Array<T> -> Arr.Depth(T, p, ys3) ->
        {Arr.snd(Array<T>, T,
           Array.swap.go(T, ys3, U32.shr(n), U32.sub(i, U32.shr(n)), v,
             U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))))
         == Arr.snd(Array<T>, T,
              Array.get.go(T, ys3, U32.shr(n), U32.sub(i, U32.shr(n)),
                U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))) : T}) ->
  {Arr.snd(Array<T>, T, Array.swap.go(T, ANode{xs, ys}, n, i, v, False{}))
   == Arr.snd(Array<T>, T, Array.get.go(T, ANode{xs, ys}, n, i, False{})) : T}:
  (ys2a, d3) = d2
  (ys2b, pe2) = d3
  (+e2a, +e2b) = pe2
  +h = U32.shr(n)
  +j = U32.sub(i, h)
  +z2 = U32.is_lt(j, U32.shr(h))
  +ea1 : {ys2a == ys1 : Array<T>} =
    Equal.trans(Array<T>, ys2a, ys2, ys1, e2a, ey2)
  +eb1 : {ys2b == ys1 : Array<T>} =
    Equal.trans(Array<T>, ys2b, ys2a, ys1, e2b, ea1)
  +hdy2b : Arr.Depth(T, p, ys2b) =
    Arr.depth_transport(T, p, ys, ys2b,
      Equal.sym(Array<T>, ys2b, ys, Equal.trans(Array<T>, ys2b, ys1, ys, eb1, ey1)),
      hdy)
  +p1 : {Arr.snd(Array<T>, T, Array.swap.go(T, ys1, h, j, v, z2))
         == Arr.snd(Array<T>, T, Array.get.go(T, ys2a, h, j, z2)) : T} =
    Equal.trans(T,
      Arr.snd(Array<T>, T, Array.swap.go(T, ys1, h, j, v, z2)),
      Arr.snd(Array<T>, T, Array.swap.go(T, ys2b, h, j, v, z2)),
      Arr.snd(Array<T>, T, Array.get.go(T, ys2a, h, j, z2)),
      Equal.cong(Array<T>, T,
        x => Arr.snd(Array<T>, T, Array.swap.go(T, x, h, j, v, z2)),
        ys1, ys2b, Equal.sym(Array<T>, ys2b, ys1, eb1)),
      Equal.trans(T,
        Arr.snd(Array<T>, T, Array.swap.go(T, ys2b, h, j, v, z2)),
        Arr.snd(Array<T>, T, Array.get.go(T, ys2b, h, j, z2)),
        Arr.snd(Array<T>, T, Array.get.go(T, ys2a, h, j, z2)),
        ih(ys2b, hdy2b),
        Equal.cong(Array<T>, T,
          x => Arr.snd(Array<T>, T, Array.get.go(T, x, h, j, z2)),
          ys2b, ys2a, e2b)))
  %ey1 : {Arr.snd(Array<T>, T, Array.swap.go(T, ANode{xs, _}, n, i, v, False{}))
          == Arr.snd(Array<T>, T, Array.get.go(T, ANode{xs, _}, n, i, False{}))
          : T}
  Equal.trans(T,
    Arr.snd(Array<T>, T, Array.swap.hi(T, xs, Array.swap.go(T, ys1, h, j, v, z2))),
    Arr.snd(Array<T>, T, Array.swap.hi(T, xs, Array.get.go(T, ys2a, h, j, z2))),
    Arr.snd(Array<T>, T, Array.swap.hi(T, xs, Array.get.go(T, ys1, h, j, z2))),
    Arr.swap_old_hi(T, xs,
      Array.swap.go(T, ys1, h, j, v, z2),
      Array.get.go(T, ys2a, h, j, z2), p1),
    Equal.cong(Array<T>, T,
      x => Arr.snd(Array<T>, T, Array.swap.hi(T, xs, Array.get.go(T, x, h, j, z2))),
      ys2a, ys1, ea1))

def Arr.swap_old_go_hi(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>, +n: U32,
    +i: U32, +v: T, +hdy: Arr.Depth(T, p, ys),
    d1: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == ys : Array<T>} & {a2 == a1 : Array<T>},
    ih: @ys3: Array<T> -> Arr.Depth(T, p, ys3) ->
        {Arr.snd(Array<T>, T,
           Array.swap.go(T, ys3, U32.shr(n), U32.sub(i, U32.shr(n)), v,
             U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))))
         == Arr.snd(Array<T>, T,
              Array.get.go(T, ys3, U32.shr(n), U32.sub(i, U32.shr(n)),
                U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))) : T}) ->
  {Arr.snd(Array<T>, T, Array.swap.go(T, ANode{xs, ys}, n, i, v, False{}))
   == Arr.snd(Array<T>, T, Array.get.go(T, ANode{xs, ys}, n, i, False{})) : T}:
  (ys1, d2) = d1
  (ys2, pe) = d2
  (+ey1, +ey2) = pe
  Arr.swap_old_go_hi2(T, p, xs, ys, ys1, n, i, v, ey1, ys2, ey2, hdy,
    Arr.dup(T, ys2), ih)

def Arr.swap_old_go(-T: Data, +d: Nat, a: Array<T>, +n: U32, +i: U32, +v: T,
    z: Bool, +hd: Arr.Depth(T, d, a)) ->
  {Arr.snd(Array<T>, T, Array.swap.go(T, a, n, i, v, z))
   == Arr.snd(Array<T>, T, Array.get.go(T, a, n, i, z)) : T}:
  match d a z:
    case 0n ALeaf{+x} _:
      {==}
    case 1n++p ANode{xs, ys} True{}:
      DPair{+hdx, +hdy} = hd
      +h = U32.shr(n)
      +z2 = U32.is_lt(i, U32.shr(h))
      Arr.swap_old_go_lo(T, p, xs, ys, n, i, v, hdx, Arr.dup(T, xs),
        x => hx => Arr.swap_old_go(T, p, x, h, i, v, z2, hx))
    case 1n++p ANode{xs, ys} False{}:
      DPair{+hdx, +hdy} = hd
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      +z2 = U32.is_lt(j, U32.shr(h))
      Arr.swap_old_go_hi(T, p, xs, ys, n, i, v, hdy, Arr.dup(T, ys),
        y => hy => Arr.swap_old_go(T, p, y, h, j, v, z2, hy))
    case 0n ANode{xs, ys} _:
      Empty.absurd(
        {Arr.snd(Array<T>, T, Array.swap.go(T, ANode{xs, ys}, n, i, v, z))
         == Arr.snd(Array<T>, T, Array.get.go(T, ANode{xs, ys}, n, i, z)) : T},
        hd)
    case 1n++p ALeaf{x} _:
      Empty.absurd(
        {Arr.snd(Array<T>, T, Array.swap.go(T, ALeaf{x}, n, i, v, z))
         == Arr.snd(Array<T>, T, Array.get.go(T, ALeaf{x}, n, i, z)) : T},
        hd)

def Arr.swap_old_at(-T: Data, +d: Nat, +i: U32, +v: T, an: Array<T> & U32,
    +hd: Arr.Depth(T, d, Arr.fst(Array<T>, U32, an))) ->
  {Arr.snd(Array<T>, T, Array.swap.at(T, i, v, an))
   == Arr.snd(Array<T>, T, Array.get.at(T, i, an)) : T}:
  (a, +n) = an
  +j = U32.and(i, U32.sub(n, 1))
  Arr.swap_old_go(T, d, a, n, j, v, U32.is_lt(j, U32.shr(n)), hd)

def Arr.swap_old_dup(-T: Data, +d: Nat, -a: Array<T>, +i: U32, +v: T,
    +hd: Arr.Depth(T, d, a),
    dp: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == a : Array<T>} & {a2 == a1 : Array<T>}) ->
  {Arr.snd(Array<T>, T, Array.swap(T, a, i, v))
   == Arr.snd(Array<T>, T, Array.get(T, a, i)) : T}:
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  +hd1 : Arr.Depth(T, d, a1) =
    Arr.depth_transport(T, d, a, a1, Equal.sym(Array<T>, a1, a, ea1), hd)
  +hd2 : Arr.Depth(T, d, a2) =
    Arr.depth_transport(T, d, a1, a2, Equal.sym(Array<T>, a2, a1, ea2), hd1)
  +es : {Arr.fst(Array<T>, U32, Array.size(T, a1)) == a1 : Array<T>} =
    Equal.trans(Array<T>,
      Arr.fst(Array<T>, U32, Array.size(T, a1)),
      Arr.fst(Array<T>, U32, Array.size(T, a2)),
      a1,
      Equal.cong(Array<T>, Array<T>,
        x => Arr.fst(Array<T>, U32, Array.size(T, x)),
        a1, a2, Equal.sym(Array<T>, a2, a1, ea2)),
      Equal.trans(Array<T>,
        Arr.fst(Array<T>, U32, Array.size(T, a2)), a2, a1,
        Arr.size_fst(T, d, a2, hd2), ea2))
  +hd_an : Arr.Depth(T, d, Arr.fst(Array<T>, U32, Array.size(T, a1))) =
    Arr.depth_transport(T, d, a1, Arr.fst(Array<T>, U32, Array.size(T, a1)),
      Equal.sym(Array<T>, Arr.fst(Array<T>, U32, Array.size(T, a1)), a1, es),
      hd1)
  %ea1 : {Arr.snd(Array<T>, T, Array.swap(T, _, i, v))
          == Arr.snd(Array<T>, T, Array.get(T, _, i)) : T}
  Arr.swap_old_at(T, d, i, v, Array.size(T, a1), hd_an)

def Arr.swap_old(-T: Data, +d: Nat, a: Array<T>, +i: U32, +v: T,
    +hd: Arr.Depth(T, d, a)) ->
  {Arr.snd(Array<T>, T, Array.swap(T, a, i, v))
   == Arr.snd(Array<T>, T, Array.get(T, a, i)) : T}:
  Arr.swap_old_dup(T, d, a, i, v, hd, Arr.dup(T, a))

# Reading back the index just written by `Array.swap` returns the new value.
def Arr.get_swap_lo(-T: Data, -ys: Array<T>, r: Array<T> & T, +n: U32, +i: U32,
    +v: T,
    ih: {Arr.snd(Array<T>, T,
           Array.get.go(T, Arr.fst(Array<T>, T, r), U32.shr(n), i,
             U32.is_lt(i, U32.shr(U32.shr(n))))) == v : T}) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.lo(T, ys, r)), n, i,
       True{})) == v : T}:
  (nxs, old) = r
  Arr.snd_lo(T, ys,
    Array.get.go(T, nxs, U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n)))),
    v, ih)

def Arr.get_swap_hi(-T: Data, -xs: Array<T>, r: Array<T> & T, +n: U32, +i: U32,
    +v: T,
    ih: {Arr.snd(Array<T>, T,
           Array.get.go(T, Arr.fst(Array<T>, T, r), U32.shr(n),
             U32.sub(i, U32.shr(n)),
             U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))) == v : T}) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.hi(T, xs, r)), n, i,
       False{})) == v : T}:
  (nys, old) = r
  Arr.snd_hi(T, xs,
    Array.get.go(T, nys, U32.shr(n), U32.sub(i, U32.shr(n)),
      U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))),
    v, ih)

def Arr.get_swap_same_lo(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>,
    +n: U32, +i: U32, +v: T, +hdx: Arr.Depth(T, p, xs),
    d: &a1: Array<T> -> &a2: Array<T> ->
       {a1 == xs : Array<T>} & {a2 == a1 : Array<T>},
    ih: @xs2: Array<T> -> Arr.Depth(T, p, xs2) ->
        {Arr.snd(Array<T>, T,
           Array.get.go(T,
             Arr.fst(Array<T>, T,
               Array.swap.go(T, xs2, U32.shr(n), i, v,
                 U32.is_lt(i, U32.shr(U32.shr(n))))),
             U32.shr(n), i, U32.is_lt(i, U32.shr(U32.shr(n))))) == v : T}) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T,
       Arr.fst(Array<T>, T, Array.swap.go(T, ANode{xs, ys}, n, i, v, True{})),
       n, i, True{})) == v : T}:
  (xs1, d2) = d
  (xs2, pe) = d2
  (+ex1, +ex2) = pe
  +h = U32.shr(n)
  +z2 = U32.is_lt(i, U32.shr(h))
  +hdx2 : Arr.Depth(T, p, xs2) =
    Arr.depth_transport(T, p, xs, xs2,
      Equal.sym(Array<T>, xs2, xs, Equal.trans(Array<T>, xs2, xs1, xs, ex2, ex1)),
      hdx)
  +p1 : {Arr.snd(Array<T>, T,
           Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, xs1, h, i, v, z2)),
             h, i, z2)) == v : T} =
    Equal.trans(T,
      Arr.snd(Array<T>, T,
        Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, xs1, h, i, v, z2)),
          h, i, z2)),
      Arr.snd(Array<T>, T,
        Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, xs2, h, i, v, z2)),
          h, i, z2)),
      v,
      Equal.cong(Array<T>, T,
        x => Arr.snd(Array<T>, T,
               Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, x, h, i, v, z2)),
                 h, i, z2)),
        xs1, xs2, Equal.sym(Array<T>, xs2, xs1, ex2)),
      ih(xs2, hdx2))
  %ex1 : {Arr.snd(Array<T>, T,
            Array.get.go(T,
              Arr.fst(Array<T>, T, Array.swap.go(T, ANode{_, ys}, n, i, v, True{})),
              n, i, True{})) == v : T}
  Arr.get_swap_lo(T, ys, Array.swap.go(T, xs1, h, i, v, z2), n, i, v, p1)

def Arr.get_swap_same_hi(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>,
    +n: U32, +i: U32, +v: T, +hdy: Arr.Depth(T, p, ys),
    d: &a1: Array<T> -> &a2: Array<T> ->
       {a1 == ys : Array<T>} & {a2 == a1 : Array<T>},
    ih: @ys2: Array<T> -> Arr.Depth(T, p, ys2) ->
        {Arr.snd(Array<T>, T,
           Array.get.go(T,
             Arr.fst(Array<T>, T,
               Array.swap.go(T, ys2, U32.shr(n), U32.sub(i, U32.shr(n)), v,
                 U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))),
             U32.shr(n), U32.sub(i, U32.shr(n)),
             U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))) == v : T}) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T,
       Arr.fst(Array<T>, T, Array.swap.go(T, ANode{xs, ys}, n, i, v, False{})),
       n, i, False{})) == v : T}:
  (ys1, d2) = d
  (ys2, pe) = d2
  (+ey1, +ey2) = pe
  +h = U32.shr(n)
  +j = U32.sub(i, h)
  +z2 = U32.is_lt(j, U32.shr(h))
  +hdy2 : Arr.Depth(T, p, ys2) =
    Arr.depth_transport(T, p, ys, ys2,
      Equal.sym(Array<T>, ys2, ys, Equal.trans(Array<T>, ys2, ys1, ys, ey2, ey1)),
      hdy)
  +p1 : {Arr.snd(Array<T>, T,
           Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, ys1, h, j, v, z2)),
             h, j, z2)) == v : T} =
    Equal.trans(T,
      Arr.snd(Array<T>, T,
        Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, ys1, h, j, v, z2)),
          h, j, z2)),
      Arr.snd(Array<T>, T,
        Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, ys2, h, j, v, z2)),
          h, j, z2)),
      v,
      Equal.cong(Array<T>, T,
        x => Arr.snd(Array<T>, T,
               Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, x, h, j, v, z2)),
                 h, j, z2)),
        ys1, ys2, Equal.sym(Array<T>, ys2, ys1, ey2)),
      ih(ys2, hdy2))
  %ey1 : {Arr.snd(Array<T>, T,
            Array.get.go(T,
              Arr.fst(Array<T>, T, Array.swap.go(T, ANode{xs, _}, n, i, v, False{})),
              n, i, False{})) == v : T}
  Arr.get_swap_hi(T, xs, Array.swap.go(T, ys1, h, j, v, z2), n, i, v, p1)

def Arr.get_swap_same_go(-T: Data, +d: Nat, a: Array<T>, +n: U32, +i: U32,
    +v: T, z: Bool, +hd: Arr.Depth(T, d, a)) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, a, n, i, v, z)),
       n, i, z)) == v : T}:
  match d a z:
    case 0n ALeaf{x} _:
      {==}
    case 1n++p ANode{xs, ys} True{}:
      DPair{+hdx, +hdy} = hd
      +h = U32.shr(n)
      +z2 = U32.is_lt(i, U32.shr(h))
      Arr.get_swap_same_lo(T, p, xs, ys, n, i, v, hdx, Arr.dup(T, xs),
        x => hx => Arr.get_swap_same_go(T, p, x, h, i, v, z2, hx))
    case 1n++p ANode{xs, ys} False{}:
      DPair{+hdx, +hdy} = hd
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      +z2 = U32.is_lt(j, U32.shr(h))
      Arr.get_swap_same_hi(T, p, xs, ys, n, i, v, hdy, Arr.dup(T, ys),
        y => hy => Arr.get_swap_same_go(T, p, y, h, j, v, z2, hy))
    case 0n ANode{xs, ys} _:
      Empty.absurd(
        {Arr.snd(Array<T>, T,
           Array.get.go(T,
             Arr.fst(Array<T>, T, Array.swap.go(T, ANode{xs, ys}, n, i, v, z)),
             n, i, z)) == v : T}, hd)
    case 1n++p ALeaf{x} _:
      Empty.absurd(
        {Arr.snd(Array<T>, T,
           Array.get.go(T,
             Arr.fst(Array<T>, T, Array.swap.go(T, ALeaf{x}, n, i, v, z)),
             n, i, z)) == v : T}, hd)

# `Array.get` and `Array.swap` on a depth-`d` array reduce to `.go` at `2^d`.
def Arr.get_at_depth(-T: Data, +d: Nat, +i: U32, an: Array<T> & U32,
    -a0: Array<T>,
    ef: {Arr.fst(Array<T>, U32, an) == a0 : Array<T>},
    es: {Arr.snd(Array<T>, U32, an) == Arr.pow2_u32(d) : U32}) ->
  {Arr.snd(Array<T>, T, Array.get.at(T, i, an))
   == Arr.snd(Array<T>, T,
        Array.get.go(T, a0, Arr.pow2_u32(d),
          U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
          U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
            U32.shr(Arr.pow2_u32(d))))) : T}:
  (a, +n) = an
  %Equal.sym(Array<T>, a, a0, ef) :
    {Arr.snd(Array<T>, T,
       Array.get.go(T, _, n, U32.and(i, U32.sub(n, 1)),
         U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))))
     == Arr.snd(Array<T>, T,
          Array.get.go(T, a0, Arr.pow2_u32(d),
            U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
            U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
              U32.shr(Arr.pow2_u32(d))))) : T}
  Equal.cong(U32, T,
    m => Arr.snd(Array<T>, T,
           Array.get.go(T, a0, m, U32.and(i, U32.sub(m, 1)),
             U32.is_lt(U32.and(i, U32.sub(m, 1)), U32.shr(m)))),
    n, Arr.pow2_u32(d), es)

def Arr.get_depth_dup2(-T: Data, +d: Nat, -a: Array<T>, a1: Array<T>, +i: U32,
    +ea1: {a1 == a : Array<T>}, -a2: Array<T>, +ea2: {a2 == a1 : Array<T>},
    dp2: &b1: Array<T> -> &b2: Array<T> ->
         {b1 == a2 : Array<T>} & {b2 == b1 : Array<T>},
    +hd: Arr.Depth(T, d, a)) ->
  {Arr.snd(Array<T>, T, Array.get(T, a, i))
   == Arr.snd(Array<T>, T,
        Array.get.go(T, a, Arr.pow2_u32(d),
          U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
          U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
            U32.shr(Arr.pow2_u32(d))))) : T}:
  (a2a, dp3) = dp2
  (a2b, pe2) = dp3
  (+e2a, +e2b) = pe2
  +ea_2a : {a2a == a1 : Array<T>} =
    Equal.trans(Array<T>, a2a, a2, a1, e2a, ea2)
  +ea_2b : {a2b == a1 : Array<T>} =
    Equal.trans(Array<T>, a2b, a2a, a1, e2b, ea_2a)
  +hd_2a : Arr.Depth(T, d, a2a) =
    Arr.depth_transport(T, d, a, a2a,
      Equal.sym(Array<T>, a2a, a,
        Equal.trans(Array<T>, a2a, a1, a, ea_2a, ea1)), hd)
  +hd_2b : Arr.Depth(T, d, a2b) =
    Arr.depth_transport(T, d, a, a2b,
      Equal.sym(Array<T>, a2b, a,
        Equal.trans(Array<T>, a2b, a1, a, ea_2b, ea1)), hd)
  +ef : {Arr.fst(Array<T>, U32, Array.size(T, a1)) == a1 : Array<T>} =
    Equal.trans(Array<T>,
      Arr.fst(Array<T>, U32, Array.size(T, a1)),
      Arr.fst(Array<T>, U32, Array.size(T, a2a)),
      a1,
      Equal.cong(Array<T>, Array<T>,
        x => Arr.fst(Array<T>, U32, Array.size(T, x)),
        a1, a2a, Equal.sym(Array<T>, a2a, a1, ea_2a)),
      Equal.trans(Array<T>,
        Arr.fst(Array<T>, U32, Array.size(T, a2a)), a2a, a1,
        Arr.size_fst(T, d, a2a, hd_2a), ea_2a))
  +es : {Arr.snd(Array<T>, U32, Array.size(T, a1)) == Arr.pow2_u32(d) : U32} =
    Equal.trans(U32,
      Arr.snd(Array<T>, U32, Array.size(T, a1)),
      Arr.snd(Array<T>, U32, Array.size(T, a2b)),
      Arr.pow2_u32(d),
      Equal.cong(Array<T>, U32,
        x => Arr.snd(Array<T>, U32, Array.size(T, x)),
        a1, a2b, Equal.sym(Array<T>, a2b, a1, ea_2b)),
      Arr.size_of_depth(T, d, a2b, hd_2b))
  %ea1 : {Arr.snd(Array<T>, T, Array.get(T, _, i))
          == Arr.snd(Array<T>, T,
               Array.get.go(T, _, Arr.pow2_u32(d),
                 U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
                 U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
                   U32.shr(Arr.pow2_u32(d))))) : T}
  Arr.get_at_depth(T, d, i, Array.size(T, a1), a1, ef, es)

def Arr.get_depth_dup(-T: Data, +d: Nat, -a: Array<T>, +i: U32,
    dp: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == a : Array<T>} & {a2 == a1 : Array<T>},
    +hd: Arr.Depth(T, d, a)) ->
  {Arr.snd(Array<T>, T, Array.get(T, a, i))
   == Arr.snd(Array<T>, T,
        Array.get.go(T, a, Arr.pow2_u32(d),
          U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
          U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
            U32.shr(Arr.pow2_u32(d))))) : T}:
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  Arr.get_depth_dup2(T, d, a, a1, i, ea1, a2, ea2, Arr.dup(T, a2), hd)

def Arr.get_depth(-T: Data, +d: Nat, a: Array<T>, +i: U32,
    +hd: Arr.Depth(T, d, a)) ->
  {Arr.snd(Array<T>, T, Array.get(T, a, i))
   == Arr.snd(Array<T>, T,
        Array.get.go(T, a, Arr.pow2_u32(d),
          U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
          U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
            U32.shr(Arr.pow2_u32(d))))) : T}:
  Arr.get_depth_dup(T, d, a, i, Arr.dup(T, a), hd)

def Arr.swap_at_depth(-T: Data, +d: Nat, +i: U32, +v: T, an: Array<T> & U32,
    -a0: Array<T>,
    ef: {Arr.fst(Array<T>, U32, an) == a0 : Array<T>},
    es: {Arr.snd(Array<T>, U32, an) == Arr.pow2_u32(d) : U32}) ->
  {Arr.fst(Array<T>, T, Array.swap.at(T, i, v, an))
   == Arr.fst(Array<T>, T,
        Array.swap.go(T, a0, Arr.pow2_u32(d),
          U32.and(i, U32.sub(Arr.pow2_u32(d), 1)), v,
          U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
            U32.shr(Arr.pow2_u32(d))))) : Array<T>}:
  (a, +n) = an
  %Equal.sym(Array<T>, a, a0, ef) :
    {Arr.fst(Array<T>, T,
       Array.swap.go(T, _, n, U32.and(i, U32.sub(n, 1)), v,
         U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))))
     == Arr.fst(Array<T>, T,
          Array.swap.go(T, a0, Arr.pow2_u32(d),
            U32.and(i, U32.sub(Arr.pow2_u32(d), 1)), v,
            U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
              U32.shr(Arr.pow2_u32(d))))) : Array<T>}
  Equal.cong(U32, Array<T>,
    m => Arr.fst(Array<T>, T,
           Array.swap.go(T, a0, m, U32.and(i, U32.sub(m, 1)), v,
             U32.is_lt(U32.and(i, U32.sub(m, 1)), U32.shr(m)))),
    n, Arr.pow2_u32(d), es)

def Arr.swap_depth_dup2(-T: Data, +d: Nat, -a: Array<T>, a1: Array<T>, +i: U32,
    +v: T, +ea1: {a1 == a : Array<T>}, -a2: Array<T>,
    +ea2: {a2 == a1 : Array<T>},
    dp2: &b1: Array<T> -> &b2: Array<T> ->
         {b1 == a2 : Array<T>} & {b2 == b1 : Array<T>},
    +hd: Arr.Depth(T, d, a)) ->
  {Arr.fst(Array<T>, T, Array.swap(T, a, i, v))
   == Arr.fst(Array<T>, T,
        Array.swap.go(T, a, Arr.pow2_u32(d),
          U32.and(i, U32.sub(Arr.pow2_u32(d), 1)), v,
          U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
            U32.shr(Arr.pow2_u32(d))))) : Array<T>}:
  (a2a, dp3) = dp2
  (a2b, pe2) = dp3
  (+e2a, +e2b) = pe2
  +ea_2a : {a2a == a1 : Array<T>} =
    Equal.trans(Array<T>, a2a, a2, a1, e2a, ea2)
  +ea_2b : {a2b == a1 : Array<T>} =
    Equal.trans(Array<T>, a2b, a2a, a1, e2b, ea_2a)
  +hd_2a : Arr.Depth(T, d, a2a) =
    Arr.depth_transport(T, d, a, a2a,
      Equal.sym(Array<T>, a2a, a,
        Equal.trans(Array<T>, a2a, a1, a, ea_2a, ea1)), hd)
  +hd_2b : Arr.Depth(T, d, a2b) =
    Arr.depth_transport(T, d, a, a2b,
      Equal.sym(Array<T>, a2b, a,
        Equal.trans(Array<T>, a2b, a1, a, ea_2b, ea1)), hd)
  +ef : {Arr.fst(Array<T>, U32, Array.size(T, a1)) == a1 : Array<T>} =
    Equal.trans(Array<T>,
      Arr.fst(Array<T>, U32, Array.size(T, a1)),
      Arr.fst(Array<T>, U32, Array.size(T, a2a)),
      a1,
      Equal.cong(Array<T>, Array<T>,
        x => Arr.fst(Array<T>, U32, Array.size(T, x)),
        a1, a2a, Equal.sym(Array<T>, a2a, a1, ea_2a)),
      Equal.trans(Array<T>,
        Arr.fst(Array<T>, U32, Array.size(T, a2a)), a2a, a1,
        Arr.size_fst(T, d, a2a, hd_2a), ea_2a))
  +es : {Arr.snd(Array<T>, U32, Array.size(T, a1)) == Arr.pow2_u32(d) : U32} =
    Equal.trans(U32,
      Arr.snd(Array<T>, U32, Array.size(T, a1)),
      Arr.snd(Array<T>, U32, Array.size(T, a2b)),
      Arr.pow2_u32(d),
      Equal.cong(Array<T>, U32,
        x => Arr.snd(Array<T>, U32, Array.size(T, x)),
        a1, a2b, Equal.sym(Array<T>, a2b, a1, ea_2b)),
      Arr.size_of_depth(T, d, a2b, hd_2b))
  %ea1 : {Arr.fst(Array<T>, T, Array.swap(T, _, i, v))
          == Arr.fst(Array<T>, T,
               Array.swap.go(T, _, Arr.pow2_u32(d),
                 U32.and(i, U32.sub(Arr.pow2_u32(d), 1)), v,
                 U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
                   U32.shr(Arr.pow2_u32(d))))) : Array<T>}
  Arr.swap_at_depth(T, d, i, v, Array.size(T, a1), a1, ef, es)

def Arr.swap_depth_dup(-T: Data, +d: Nat, -a: Array<T>, +i: U32, +v: T,
    dp: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == a : Array<T>} & {a2 == a1 : Array<T>},
    +hd: Arr.Depth(T, d, a)) ->
  {Arr.fst(Array<T>, T, Array.swap(T, a, i, v))
   == Arr.fst(Array<T>, T,
        Array.swap.go(T, a, Arr.pow2_u32(d),
          U32.and(i, U32.sub(Arr.pow2_u32(d), 1)), v,
          U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
            U32.shr(Arr.pow2_u32(d))))) : Array<T>}:
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  Arr.swap_depth_dup2(T, d, a, a1, i, v, ea1, a2, ea2, Arr.dup(T, a2), hd)

def Arr.swap_depth(-T: Data, +d: Nat, a: Array<T>, +i: U32, +v: T,
    +hd: Arr.Depth(T, d, a)) ->
  {Arr.fst(Array<T>, T, Array.swap(T, a, i, v))
   == Arr.fst(Array<T>, T,
        Array.swap.go(T, a, Arr.pow2_u32(d),
          U32.and(i, U32.sub(Arr.pow2_u32(d), 1)), v,
          U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
            U32.shr(Arr.pow2_u32(d))))) : Array<T>}:
  Arr.swap_depth_dup(T, d, a, i, v, Arr.dup(T, a), hd)

def Arr.swap_depth_pair_dup(-T: Data, +d: Nat, -a: Array<T>, +i: U32, +v: T,
    +hd: Arr.Depth(T, d, a),
    dp: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == a : Array<T>} & {a2 == a1 : Array<T>}) ->
  Arr.DPair<
    Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, a, i, v))),
    {Arr.fst(Array<T>, T, Array.swap(T, a, i, v))
     == Arr.fst(Array<T>, T,
          Array.swap.go(T, a, Arr.pow2_u32(d),
            U32.and(i, U32.sub(Arr.pow2_u32(d), 1)), v,
            U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
              U32.shr(Arr.pow2_u32(d))))) : Array<T>}>:
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  +hd1 : Arr.Depth(T, d, a1) =
    Arr.depth_transport(T, d, a, a1, Equal.sym(Array<T>, a1, a, ea1), hd)
  +hd2 : Arr.Depth(T, d, a2) =
    Arr.depth_transport(T, d, a1, a2, Equal.sym(Array<T>, a2, a1, ea2), hd1)
  +hd_sw1 : Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v))) =
    Arr.depth_swap(T, d, a1, i, v, hd1)
  +esw1 : {Arr.fst(Array<T>, T, Array.swap(T, a1, i, v))
           == Arr.fst(Array<T>, T,
                Array.swap.go(T, a1, Arr.pow2_u32(d),
                  U32.and(i, U32.sub(Arr.pow2_u32(d), 1)), v,
                  U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
                    U32.shr(Arr.pow2_u32(d))))) : Array<T>} =
    Equal.trans(Array<T>,
      Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)),
      Arr.fst(Array<T>, T, Array.swap(T, a2, i, v)),
      Arr.fst(Array<T>, T,
        Array.swap.go(T, a1, Arr.pow2_u32(d),
          U32.and(i, U32.sub(Arr.pow2_u32(d), 1)), v,
          U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
            U32.shr(Arr.pow2_u32(d))))),
      Equal.cong(Array<T>, Array<T>,
        x => Arr.fst(Array<T>, T, Array.swap(T, x, i, v)),
        a1, a2, Equal.sym(Array<T>, a2, a1, ea2)),
      Equal.trans(Array<T>,
        Arr.fst(Array<T>, T, Array.swap(T, a2, i, v)),
        Arr.fst(Array<T>, T,
          Array.swap.go(T, a2, Arr.pow2_u32(d),
            U32.and(i, U32.sub(Arr.pow2_u32(d), 1)), v,
            U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
              U32.shr(Arr.pow2_u32(d))))),
        Arr.fst(Array<T>, T,
          Array.swap.go(T, a1, Arr.pow2_u32(d),
            U32.and(i, U32.sub(Arr.pow2_u32(d), 1)), v,
            U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
              U32.shr(Arr.pow2_u32(d))))),
        Arr.swap_depth(T, d, a2, i, v, hd2),
        Equal.cong(Array<T>, Array<T>,
          x => Arr.fst(Array<T>, T,
                 Array.swap.go(T, x, Arr.pow2_u32(d),
                   U32.and(i, U32.sub(Arr.pow2_u32(d), 1)), v,
                   U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
                     U32.shr(Arr.pow2_u32(d))))),
          a2, a1, ea2)))
  %ea1 : Arr.DPair<
           Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, _, i, v))),
           {Arr.fst(Array<T>, T, Array.swap(T, _, i, v))
            == Arr.fst(Array<T>, T,
                 Array.swap.go(T, _, Arr.pow2_u32(d),
                   U32.and(i, U32.sub(Arr.pow2_u32(d), 1)), v,
                   U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
                     U32.shr(Arr.pow2_u32(d))))) : Array<T>}>
  DPair{hd_sw1, esw1}

def Arr.swap_depth_pair(-T: Data, +d: Nat, a: Array<T>, +i: U32, +v: T,
    +hd: Arr.Depth(T, d, a)) ->
  Arr.DPair<
    Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, a, i, v))),
    {Arr.fst(Array<T>, T, Array.swap(T, a, i, v))
     == Arr.fst(Array<T>, T,
          Array.swap.go(T, a, Arr.pow2_u32(d),
            U32.and(i, U32.sub(Arr.pow2_u32(d), 1)), v,
            U32.is_lt(U32.and(i, U32.sub(Arr.pow2_u32(d), 1)),
              U32.shr(Arr.pow2_u32(d))))) : Array<T>}>:
  Arr.swap_depth_pair_dup(T, d, a, i, v, hd, Arr.dup(T, a))

def Arr.get_swap_same_dup2(-T: Data, +d: Nat, -a: Array<T>, a1: Array<T>,
    +i: U32, +v: T, +ea1: {a1 == a : Array<T>}, -a2: Array<T>,
    +ea2: {a2 == a1 : Array<T>},
    dp2: &b1: Array<T> -> &b2: Array<T> ->
         {b1 == a2 : Array<T>} & {b2 == b1 : Array<T>},
    +hd: Arr.Depth(T, d, a)) ->
  {Arr.snd(Array<T>, T,
     Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a, i, v)), i)) == v : T}:
  (a2a, dp3) = dp2
  (a2b, pe2) = dp3
  (+e2a, +e2b) = pe2
  +ea_2a : {a2a == a1 : Array<T>} =
    Equal.trans(Array<T>, a2a, a2, a1, e2a, ea2)
  +ea_2b : {a2b == a1 : Array<T>} =
    Equal.trans(Array<T>, a2b, a2a, a1, e2b, ea_2a)
  +n : U32 = Arr.pow2_u32(d)
  +j : U32 = U32.and(i, U32.sub(n, 1))
  +z : Bool = U32.is_lt(j, U32.shr(n))
  +hd1 : Arr.Depth(T, d, a1) =
    Arr.depth_transport(T, d, a, a1, Equal.sym(Array<T>, a1, a, ea1), hd)
  +hd2a : Arr.Depth(T, d, a2a) =
    Arr.depth_transport(T, d, a1, a2a, Equal.sym(Array<T>, a2a, a1, ea_2a), hd1)
  +hd2b : Arr.Depth(T, d, a2b) =
    Arr.depth_transport(T, d, a1, a2b, Equal.sym(Array<T>, a2b, a1, ea_2b), hd1)
  +p2a = Arr.swap_depth_pair(T, d, a2a, i, v, hd2a)
  +hd_sw2a : Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v))) =
    Arr.dpair_l(
      Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v))),
      {Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v))
       == Arr.fst(Array<T>, T, Array.swap.go(T, a2a, n, j, v, z)) : Array<T>},
      p2a)
  +esw2a : {Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v))
            == Arr.fst(Array<T>, T, Array.swap.go(T, a2a, n, j, v, z))
            : Array<T>} =
    Arr.dpair_r(
      Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v))),
      {Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v))
       == Arr.fst(Array<T>, T, Array.swap.go(T, a2a, n, j, v, z)) : Array<T>},
      p2a)
  +esw : {Arr.fst(Array<T>, T, Array.swap(T, a1, i, v))
          == Arr.fst(Array<T>, T, Array.swap.go(T, a1, n, j, v, z)) : Array<T>} =
    Equal.trans(Array<T>,
      Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)),
      Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v)),
      Arr.fst(Array<T>, T, Array.swap.go(T, a1, n, j, v, z)),
      Equal.cong(Array<T>, Array<T>,
        x => Arr.fst(Array<T>, T, Array.swap(T, x, i, v)),
        a1, a2a, Equal.sym(Array<T>, a2a, a1, ea_2a)),
      Equal.trans(Array<T>,
        Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v)),
        Arr.fst(Array<T>, T, Array.swap.go(T, a2a, n, j, v, z)),
        Arr.fst(Array<T>, T, Array.swap.go(T, a1, n, j, v, z)),
        esw2a,
        Equal.cong(Array<T>, Array<T>,
          x => Arr.fst(Array<T>, T, Array.swap.go(T, x, n, j, v, z)),
          a2a, a1, ea_2a)))
  +hd_sw1 : Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v))) =
    Arr.depth_transport(T, d,
      Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v)),
      Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)),
      Equal.cong(Array<T>, Array<T>,
        x => Arr.fst(Array<T>, T, Array.swap(T, x, i, v)), a2a, a1, ea_2a),
      hd_sw2a)
  +eget : {Arr.snd(Array<T>, T,
             Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), i))
           == Arr.snd(Array<T>, T,
                Array.get.go(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)),
                  n, j, z)) : T} =
    Arr.get_depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), i, hd_sw1)
  +ego : {Arr.snd(Array<T>, T,
            Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, a1, n, j, v, z)),
              n, j, z)) == v : T} =
    Equal.trans(T,
      Arr.snd(Array<T>, T,
        Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, a1, n, j, v, z)),
          n, j, z)),
      Arr.snd(Array<T>, T,
        Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, a2b, n, j, v, z)),
          n, j, z)),
      v,
      Equal.cong(Array<T>, T,
        x => Arr.snd(Array<T>, T,
               Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, x, n, j, v, z)),
                 n, j, z)),
        a1, a2b, Equal.sym(Array<T>, a2b, a1, ea_2b)),
      Arr.get_swap_same_go(T, d, a2b, n, j, v, z, hd2b))
  %ea1 : {Arr.snd(Array<T>, T,
            Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, _, i, v)), i))
          == v : T}
  Equal.trans(T,
    Arr.snd(Array<T>, T,
      Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), i)),
    Arr.snd(Array<T>, T,
      Array.get.go(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), n, j, z)),
    v,
    eget,
    Equal.trans(T,
      Arr.snd(Array<T>, T,
        Array.get.go(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), n, j, z)),
      Arr.snd(Array<T>, T,
        Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, a1, n, j, v, z)),
          n, j, z)),
      v,
      Equal.cong(Array<T>, T, x => Arr.snd(Array<T>, T, Array.get.go(T, x, n, j, z)),
        Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)),
        Arr.fst(Array<T>, T, Array.swap.go(T, a1, n, j, v, z)),
        esw),
      ego))

def Arr.get_swap_same_dup(-T: Data, +d: Nat, -a: Array<T>, +i: U32, +v: T,
    dp: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == a : Array<T>} & {a2 == a1 : Array<T>},
    +hd: Arr.Depth(T, d, a)) ->
  {Arr.snd(Array<T>, T,
     Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a, i, v)), i)) == v : T}:
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  Arr.get_swap_same_dup2(T, d, a, a1, i, v, ea1, a2, ea2, Arr.dup(T, a2), hd)

def Arr.get_swap_same(-T: Data, +d: Nat, a: Array<T>, +i: U32, +v: T,
    +hd: Arr.Depth(T, d, a)) ->
  {Arr.snd(Array<T>, T,
     Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a, i, v)), i)) == v : T}:
  Arr.get_swap_same_dup(T, d, a, i, v, Arr.dup(T, a), hd)

# Reading a distinct in-range index after `Array.swap` returns its prior value.
def Arr.get_swap_diff_cross_lh(-T: Data, -xs: Array<T>, -ys: Array<T>,
    r: Array<T> & T, +n: U32, +j: U32, g: Array<T> & T,
    +eg: {g == Array.get.go(T, ys, U32.shr(n), U32.sub(j, U32.shr(n)),
                 U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n))))
          : Array<T> & T}) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.lo(T, ys, r)), n, j,
       False{}))
   == Arr.snd(Array<T>, T,
        Array.get.go(T, ANode{xs, ys}, n, j, False{})) : T}:
  (nxs, old) = r
  (ny, v) = g
  %eg : {Arr.snd(Array<T>, T, Array.swap.hi(T, nxs, _))
         == Arr.snd(Array<T>, T, Array.swap.hi(T, xs, _)) : T}
  {==}

def Arr.get_swap_diff_cross_hl(-T: Data, -xs: Array<T>, -ys: Array<T>,
    r: Array<T> & T, +n: U32, +j: U32, g: Array<T> & T,
    +eg: {g == Array.get.go(T, xs, U32.shr(n), j,
                 U32.is_lt(j, U32.shr(U32.shr(n)))) : Array<T> & T}) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.hi(T, xs, r)), n, j,
       True{}))
   == Arr.snd(Array<T>, T,
        Array.get.go(T, ANode{xs, ys}, n, j, True{})) : T}:
  (nys, old) = r
  (nx, v) = g
  %eg : {Arr.snd(Array<T>, T, Array.swap.lo(T, nys, _))
         == Arr.snd(Array<T>, T, Array.swap.lo(T, ys, _)) : T}
  {==}

def Arr.get_swap_diff_lo_go(-T: Data, -ys: Array<T>, r: Array<T> & T,
    g1: Array<T> & T, g2: Array<T> & T, +n: U32, +j: U32,
    eg1: {g1 == Array.get.go(T, Arr.fst(Array<T>, T, r), U32.shr(n), j,
                  U32.is_lt(j, U32.shr(U32.shr(n)))) : Array<T> & T},
    ih: {Arr.snd(Array<T>, T, g1) == Arr.snd(Array<T>, T, g2) : T}) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.lo(T, ys, r)), n, j,
       True{}))
   == Arr.snd(Array<T>, T, Array.swap.lo(T, ys, g2)) : T}:
  (nxs, old) = r
  (a1, v1) = g1
  (a2, v2) = g2
  Equal.trans(T,
    Arr.snd(Array<T>, T,
      Array.swap.lo(T, ys,
        Array.get.go(T, nxs, U32.shr(n), j, U32.is_lt(j, U32.shr(U32.shr(n)))))),
    Arr.snd(Array<T>, T, Array.swap.lo(T, ys, Tuple{a1, v1})),
    v2,
    Equal.cong(Array<T> & T, T, x => Arr.snd(Array<T>, T, Array.swap.lo(T, ys, x)),
      Array.get.go(T, nxs, U32.shr(n), j, U32.is_lt(j, U32.shr(U32.shr(n)))),
      Tuple{a1, v1},
      Equal.sym(Array<T> & T, Tuple{a1, v1},
        Array.get.go(T, nxs, U32.shr(n), j, U32.is_lt(j, U32.shr(U32.shr(n)))),
        eg1)),
    ih)

def Arr.get_swap_diff_hi_go(-T: Data, -xs: Array<T>, r: Array<T> & T,
    g1: Array<T> & T, g2: Array<T> & T, +n: U32, +j: U32,
    eg1: {g1 == Array.get.go(T, Arr.fst(Array<T>, T, r), U32.shr(n),
                  U32.sub(j, U32.shr(n)),
                  U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n))))
          : Array<T> & T},
    ih: {Arr.snd(Array<T>, T, g1) == Arr.snd(Array<T>, T, g2) : T}) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.hi(T, xs, r)), n, j,
       False{}))
   == Arr.snd(Array<T>, T, Array.swap.hi(T, xs, g2)) : T}:
  (nys, old) = r
  (a1, v1) = g1
  (a2, v2) = g2
  Equal.trans(T,
    Arr.snd(Array<T>, T,
      Array.swap.hi(T, xs,
        Array.get.go(T, nys, U32.shr(n), U32.sub(j, U32.shr(n)),
          U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n)))))),
    Arr.snd(Array<T>, T, Array.swap.hi(T, xs, Tuple{a1, v1})),
    v2,
    Equal.cong(Array<T> & T, T, x => Arr.snd(Array<T>, T, Array.swap.hi(T, xs, x)),
      Array.get.go(T, nys, U32.shr(n), U32.sub(j, U32.shr(n)),
        U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n)))),
      Tuple{a1, v1},
      Equal.sym(Array<T> & T, Tuple{a1, v1},
        Array.get.go(T, nys, U32.shr(n), U32.sub(j, U32.shr(n)),
          U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n)))),
        eg1)),
    ih)

def Arr.get_swap_diff_same_lo3(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>,
    xs1: Array<T>, xs2a: Array<T>, -xs2b: Array<T>, +i: U32, +j: U32, +v: T,
    +esh: {U32.shr(Arr.pow2_u32(1n+p)) == Arr.pow2_u32(p) : U32},
    +ex1: {xs1 == xs : Array<T>}, +ea1: {xs2a == xs1 : Array<T>},
    +eb1: {xs2b == xs1 : Array<T>},
    +hdx: Arr.Depth(T, p, xs),
    d3: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == xs2b : Array<T>} & {a2 == a1 : Array<T>},
    ih: @xs3: Array<T> -> Arr.Depth(T, p, xs3) ->
        {Arr.snd(Array<T>, T,
           Array.get.go(T,
             Arr.fst(Array<T>, T,
               Array.swap.go(T, xs3, Arr.pow2_u32(p), i, v,
                 U32.is_lt(i, U32.shr(Arr.pow2_u32(p))))),
             Arr.pow2_u32(p), j, U32.is_lt(j, U32.shr(Arr.pow2_u32(p)))))
         == Arr.snd(Array<T>, T,
              Array.get.go(T, xs3, Arr.pow2_u32(p), j,
                U32.is_lt(j, U32.shr(Arr.pow2_u32(p))))) : T}) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T,
       Arr.fst(Array<T>, T,
         Array.swap.go(T, ANode{xs, ys}, Arr.pow2_u32(1n+p), i, v, True{})),
       Arr.pow2_u32(1n+p), j, True{}))
   == Arr.snd(Array<T>, T,
        Array.get.go(T, ANode{xs, ys}, Arr.pow2_u32(1n+p), j, True{})) : T}:
  (xs3a, d4) = d3
  (xs3b, pe3) = d4
  (+e3a, +e3b) = pe3
  +n : U32 = Arr.pow2_u32(1n+p)
  +h : U32 = U32.shr(n)
  +zi : Bool = U32.is_lt(i, U32.shr(h))
  +zj : Bool = U32.is_lt(j, U32.shr(h))
  +e3a1 : {xs3a == xs1 : Array<T>} =
    Equal.trans(Array<T>, xs3a, xs2b, xs1, e3a, eb1)
  +e3b1 : {xs3b == xs1 : Array<T>} =
    Equal.trans(Array<T>, xs3b, xs3a, xs1, e3b, e3a1)
  +hdx3b : Arr.Depth(T, p, xs3b) =
    Arr.depth_transport(T, p, xs, xs3b,
      Equal.sym(Array<T>, xs3b, xs,
        Equal.trans(Array<T>, xs3b, xs1, xs, e3b1, ex1)), hdx)
  +ih_h : {Arr.snd(Array<T>, T,
             Array.get.go(T,
               Arr.fst(Array<T>, T, Array.swap.go(T, xs3b, h, i, v, zi)),
               h, j, zj))
           == Arr.snd(Array<T>, T, Array.get.go(T, xs3b, h, j, zj)) : T} =
    (%Equal.sym(U32, h, Arr.pow2_u32(p), esh) :
      {Arr.snd(Array<T>, T,
         Array.get.go(T,
           Arr.fst(Array<T>, T,
             Array.swap.go(T, xs3b, _, i, v, U32.is_lt(i, U32.shr(_)))),
           _, j, U32.is_lt(j, U32.shr(_))))
       == Arr.snd(Array<T>, T,
            Array.get.go(T, xs3b, _, j, U32.is_lt(j, U32.shr(_)))) : T};
     ih(xs3b, hdx3b))
  +p_mid : {Arr.snd(Array<T>, T,
              Array.get.go(T,
                Arr.fst(Array<T>, T, Array.swap.go(T, xs3a, h, i, v, zi)),
                h, j, zj))
            == Arr.snd(Array<T>, T, Array.get.go(T, xs2a, h, j, zj)) : T} =
    Equal.trans(T,
      Arr.snd(Array<T>, T,
        Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, xs3a, h, i, v, zi)),
          h, j, zj)),
      Arr.snd(Array<T>, T,
        Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, xs3b, h, i, v, zi)),
          h, j, zj)),
      Arr.snd(Array<T>, T, Array.get.go(T, xs2a, h, j, zj)),
      Equal.cong(Array<T>, T,
        x => Arr.snd(Array<T>, T,
               Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, x, h, i, v, zi)),
                 h, j, zj)),
        xs3a, xs3b, Equal.sym(Array<T>, xs3b, xs3a, e3b)),
      Equal.trans(T,
        Arr.snd(Array<T>, T,
          Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, xs3b, h, i, v, zi)),
            h, j, zj)),
        Arr.snd(Array<T>, T, Array.get.go(T, xs3b, h, j, zj)),
        Arr.snd(Array<T>, T, Array.get.go(T, xs2a, h, j, zj)),
        ih_h,
        Equal.cong(Array<T>, T,
          x => Arr.snd(Array<T>, T, Array.get.go(T, x, h, j, zj)),
          xs3b, xs2a,
          Equal.trans(Array<T>, xs3b, xs1, xs2a, e3b1,
            Equal.sym(Array<T>, xs2a, xs1, ea1)))))
  +eg1 : {Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, xs3a, h, i, v, zi)),
            h, j, zj)
          == Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, xs1, h, i, v, zi)),
               h, j, zj) : Array<T> & T} =
    Equal.cong(Array<T>, Array<T> & T,
      x => Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, x, h, i, v, zi)),
             h, j, zj),
      xs3a, xs1, e3a1)
  %ex1 : {Arr.snd(Array<T>, T,
            Array.get.go(T,
              Arr.fst(Array<T>, T, Array.swap.go(T, ANode{_, ys}, n, i, v, True{})),
              n, j, True{}))
          == Arr.snd(Array<T>, T, Array.get.go(T, ANode{_, ys}, n, j, True{}))
          : T}
  Equal.trans(T,
    Arr.snd(Array<T>, T,
      Array.get.go(T,
        Arr.fst(Array<T>, T, Array.swap.lo(T, ys, Array.swap.go(T, xs1, h, i, v, zi))),
        n, j, True{})),
    Arr.snd(Array<T>, T, Array.swap.lo(T, ys, Array.get.go(T, xs2a, h, j, zj))),
    Arr.snd(Array<T>, T, Array.swap.lo(T, ys, Array.get.go(T, xs1, h, j, zj))),
    Arr.get_swap_diff_lo_go(T, ys,
      Array.swap.go(T, xs1, h, i, v, zi),
      Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, xs3a, h, i, v, zi)),
        h, j, zj),
      Array.get.go(T, xs2a, h, j, zj), n, j, eg1, p_mid),
    Equal.cong(Array<T>, T,
      x => Arr.snd(Array<T>, T, Array.swap.lo(T, ys, Array.get.go(T, x, h, j, zj))),
      xs2a, xs1, ea1))

def Arr.get_swap_diff_same_lo2(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>,
    xs1: Array<T>, +i: U32, +j: U32, +v: T,
    +esh: {U32.shr(Arr.pow2_u32(1n+p)) == Arr.pow2_u32(p) : U32},
    +ex1: {xs1 == xs : Array<T>}, -xs2: Array<T>,
    +ex2: {xs2 == xs1 : Array<T>},
    +hdx: Arr.Depth(T, p, xs),
    d2: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == xs2 : Array<T>} & {a2 == a1 : Array<T>},
    ih: @xs3: Array<T> -> Arr.Depth(T, p, xs3) ->
        {Arr.snd(Array<T>, T,
           Array.get.go(T,
             Arr.fst(Array<T>, T,
               Array.swap.go(T, xs3, Arr.pow2_u32(p), i, v,
                 U32.is_lt(i, U32.shr(Arr.pow2_u32(p))))),
             Arr.pow2_u32(p), j, U32.is_lt(j, U32.shr(Arr.pow2_u32(p)))))
         == Arr.snd(Array<T>, T,
              Array.get.go(T, xs3, Arr.pow2_u32(p), j,
                U32.is_lt(j, U32.shr(Arr.pow2_u32(p))))) : T}) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T,
       Arr.fst(Array<T>, T,
         Array.swap.go(T, ANode{xs, ys}, Arr.pow2_u32(1n+p), i, v, True{})),
       Arr.pow2_u32(1n+p), j, True{}))
   == Arr.snd(Array<T>, T,
        Array.get.go(T, ANode{xs, ys}, Arr.pow2_u32(1n+p), j, True{})) : T}:
  (xs2a, d3) = d2
  (xs2b, pe2) = d3
  (+e2a, +e2b) = pe2
  +ea1 : {xs2a == xs1 : Array<T>} =
    Equal.trans(Array<T>, xs2a, xs2, xs1, e2a, ex2)
  +eb1 : {xs2b == xs1 : Array<T>} =
    Equal.trans(Array<T>, xs2b, xs2a, xs1, e2b, ea1)
  Arr.get_swap_diff_same_lo3(T, p, xs, ys, xs1, xs2a, xs2b, i, j, v, esh, ex1,
    ea1, eb1, hdx, Arr.dup(T, xs2b), ih)

def Arr.get_swap_diff_same_lo(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>,
    +i: U32, +j: U32, +v: T,
    +esh: {U32.shr(Arr.pow2_u32(1n+p)) == Arr.pow2_u32(p) : U32},
    +hdx: Arr.Depth(T, p, xs),
    d: &a1: Array<T> -> &a2: Array<T> ->
       {a1 == xs : Array<T>} & {a2 == a1 : Array<T>},
    ih: @xs3: Array<T> -> Arr.Depth(T, p, xs3) ->
        {Arr.snd(Array<T>, T,
           Array.get.go(T,
             Arr.fst(Array<T>, T,
               Array.swap.go(T, xs3, Arr.pow2_u32(p), i, v,
                 U32.is_lt(i, U32.shr(Arr.pow2_u32(p))))),
             Arr.pow2_u32(p), j, U32.is_lt(j, U32.shr(Arr.pow2_u32(p)))))
         == Arr.snd(Array<T>, T,
              Array.get.go(T, xs3, Arr.pow2_u32(p), j,
                U32.is_lt(j, U32.shr(Arr.pow2_u32(p))))) : T}) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T,
       Arr.fst(Array<T>, T,
         Array.swap.go(T, ANode{xs, ys}, Arr.pow2_u32(1n+p), i, v, True{})),
       Arr.pow2_u32(1n+p), j, True{}))
   == Arr.snd(Array<T>, T,
        Array.get.go(T, ANode{xs, ys}, Arr.pow2_u32(1n+p), j, True{})) : T}:
  (xs1, d2) = d
  (xs2, pe) = d2
  (+ex1, +ex2) = pe
  Arr.get_swap_diff_same_lo2(T, p, xs, ys, xs1, i, j, v, esh, ex1, xs2, ex2,
    hdx, Arr.dup(T, xs2), ih)

def Arr.get_swap_diff_same_hi3(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>,
    ys1: Array<T>, ys2a: Array<T>, -ys2b: Array<T>, +i: U32, +j: U32, +v: T,
    +esh: {U32.shr(Arr.pow2_u32(1n+p)) == Arr.pow2_u32(p) : U32},
    +ey1: {ys1 == ys : Array<T>}, +ea1: {ys2a == ys1 : Array<T>},
    +eb1: {ys2b == ys1 : Array<T>},
    +hdy: Arr.Depth(T, p, ys),
    d3: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == ys2b : Array<T>} & {a2 == a1 : Array<T>},
    ih: @ys3: Array<T> -> Arr.Depth(T, p, ys3) ->
        {Arr.snd(Array<T>, T,
           Array.get.go(T,
             Arr.fst(Array<T>, T,
               Array.swap.go(T, ys3, Arr.pow2_u32(p),
                 U32.sub(i, Arr.pow2_u32(p)), v,
                 U32.is_lt(U32.sub(i, Arr.pow2_u32(p)),
                   U32.shr(Arr.pow2_u32(p))))),
             Arr.pow2_u32(p), U32.sub(j, Arr.pow2_u32(p)),
             U32.is_lt(U32.sub(j, Arr.pow2_u32(p)), U32.shr(Arr.pow2_u32(p)))))
         == Arr.snd(Array<T>, T,
              Array.get.go(T, ys3, Arr.pow2_u32(p),
                U32.sub(j, Arr.pow2_u32(p)),
                U32.is_lt(U32.sub(j, Arr.pow2_u32(p)),
                  U32.shr(Arr.pow2_u32(p))))) : T}) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T,
       Arr.fst(Array<T>, T,
         Array.swap.go(T, ANode{xs, ys}, Arr.pow2_u32(1n+p), i, v, False{})),
       Arr.pow2_u32(1n+p), j, False{}))
   == Arr.snd(Array<T>, T,
        Array.get.go(T, ANode{xs, ys}, Arr.pow2_u32(1n+p), j, False{})) : T}:
  (ys3a, d4) = d3
  (ys3b, pe3) = d4
  (+e3a, +e3b) = pe3
  +n : U32 = Arr.pow2_u32(1n+p)
  +h : U32 = U32.shr(n)
  +ii : U32 = U32.sub(i, h)
  +jj : U32 = U32.sub(j, h)
  +zi : Bool = U32.is_lt(ii, U32.shr(h))
  +zj : Bool = U32.is_lt(jj, U32.shr(h))
  +e3a1 : {ys3a == ys1 : Array<T>} =
    Equal.trans(Array<T>, ys3a, ys2b, ys1, e3a, eb1)
  +e3b1 : {ys3b == ys1 : Array<T>} =
    Equal.trans(Array<T>, ys3b, ys3a, ys1, e3b, e3a1)
  +hdy3b : Arr.Depth(T, p, ys3b) =
    Arr.depth_transport(T, p, ys, ys3b,
      Equal.sym(Array<T>, ys3b, ys,
        Equal.trans(Array<T>, ys3b, ys1, ys, e3b1, ey1)), hdy)
  +ih_h : {Arr.snd(Array<T>, T,
             Array.get.go(T,
               Arr.fst(Array<T>, T, Array.swap.go(T, ys3b, h, ii, v, zi)),
               h, jj, zj))
           == Arr.snd(Array<T>, T, Array.get.go(T, ys3b, h, jj, zj)) : T} =
    (%Equal.sym(U32, h, Arr.pow2_u32(p), esh) :
      {Arr.snd(Array<T>, T,
         Array.get.go(T,
           Arr.fst(Array<T>, T,
             Array.swap.go(T, ys3b, _, U32.sub(i, _), v,
               U32.is_lt(U32.sub(i, _), U32.shr(_)))),
           _, U32.sub(j, _), U32.is_lt(U32.sub(j, _), U32.shr(_))))
       == Arr.snd(Array<T>, T,
            Array.get.go(T, ys3b, _, U32.sub(j, _),
              U32.is_lt(U32.sub(j, _), U32.shr(_)))) : T};
     ih(ys3b, hdy3b))
  +p_mid : {Arr.snd(Array<T>, T,
              Array.get.go(T,
                Arr.fst(Array<T>, T, Array.swap.go(T, ys3a, h, ii, v, zi)),
                h, jj, zj))
            == Arr.snd(Array<T>, T, Array.get.go(T, ys2a, h, jj, zj)) : T} =
    Equal.trans(T,
      Arr.snd(Array<T>, T,
        Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, ys3a, h, ii, v, zi)),
          h, jj, zj)),
      Arr.snd(Array<T>, T,
        Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, ys3b, h, ii, v, zi)),
          h, jj, zj)),
      Arr.snd(Array<T>, T, Array.get.go(T, ys2a, h, jj, zj)),
      Equal.cong(Array<T>, T,
        x => Arr.snd(Array<T>, T,
               Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, x, h, ii, v, zi)),
                 h, jj, zj)),
        ys3a, ys3b, Equal.sym(Array<T>, ys3b, ys3a, e3b)),
      Equal.trans(T,
        Arr.snd(Array<T>, T,
          Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, ys3b, h, ii, v, zi)),
            h, jj, zj)),
        Arr.snd(Array<T>, T, Array.get.go(T, ys3b, h, jj, zj)),
        Arr.snd(Array<T>, T, Array.get.go(T, ys2a, h, jj, zj)),
        ih_h,
        Equal.cong(Array<T>, T,
          x => Arr.snd(Array<T>, T, Array.get.go(T, x, h, jj, zj)),
          ys3b, ys2a,
          Equal.trans(Array<T>, ys3b, ys1, ys2a, e3b1,
            Equal.sym(Array<T>, ys2a, ys1, ea1)))))
  +eg1 : {Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, ys3a, h, ii, v, zi)),
            h, jj, zj)
          == Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, ys1, h, ii, v, zi)),
               h, jj, zj) : Array<T> & T} =
    Equal.cong(Array<T>, Array<T> & T,
      x => Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, x, h, ii, v, zi)),
             h, jj, zj),
      ys3a, ys1, e3a1)
  %ey1 : {Arr.snd(Array<T>, T,
            Array.get.go(T,
              Arr.fst(Array<T>, T, Array.swap.go(T, ANode{xs, _}, n, i, v, False{})),
              n, j, False{}))
          == Arr.snd(Array<T>, T, Array.get.go(T, ANode{xs, _}, n, j, False{}))
          : T}
  Equal.trans(T,
    Arr.snd(Array<T>, T,
      Array.get.go(T,
        Arr.fst(Array<T>, T, Array.swap.hi(T, xs, Array.swap.go(T, ys1, h, ii, v, zi))),
        n, j, False{})),
    Arr.snd(Array<T>, T, Array.swap.hi(T, xs, Array.get.go(T, ys2a, h, jj, zj))),
    Arr.snd(Array<T>, T, Array.swap.hi(T, xs, Array.get.go(T, ys1, h, jj, zj))),
    Arr.get_swap_diff_hi_go(T, xs,
      Array.swap.go(T, ys1, h, ii, v, zi),
      Array.get.go(T, Arr.fst(Array<T>, T, Array.swap.go(T, ys3a, h, ii, v, zi)),
        h, jj, zj),
      Array.get.go(T, ys2a, h, jj, zj), n, j, eg1, p_mid),
    Equal.cong(Array<T>, T,
      x => Arr.snd(Array<T>, T, Array.swap.hi(T, xs, Array.get.go(T, x, h, jj, zj))),
      ys2a, ys1, ea1))

def Arr.get_swap_diff_same_hi2(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>,
    ys1: Array<T>, +i: U32, +j: U32, +v: T,
    +esh: {U32.shr(Arr.pow2_u32(1n+p)) == Arr.pow2_u32(p) : U32},
    +ey1: {ys1 == ys : Array<T>}, -ys2: Array<T>,
    +ey2: {ys2 == ys1 : Array<T>},
    +hdy: Arr.Depth(T, p, ys),
    d2: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == ys2 : Array<T>} & {a2 == a1 : Array<T>},
    ih: @ys3: Array<T> -> Arr.Depth(T, p, ys3) ->
        {Arr.snd(Array<T>, T,
           Array.get.go(T,
             Arr.fst(Array<T>, T,
               Array.swap.go(T, ys3, Arr.pow2_u32(p),
                 U32.sub(i, Arr.pow2_u32(p)), v,
                 U32.is_lt(U32.sub(i, Arr.pow2_u32(p)),
                   U32.shr(Arr.pow2_u32(p))))),
             Arr.pow2_u32(p), U32.sub(j, Arr.pow2_u32(p)),
             U32.is_lt(U32.sub(j, Arr.pow2_u32(p)), U32.shr(Arr.pow2_u32(p)))))
         == Arr.snd(Array<T>, T,
              Array.get.go(T, ys3, Arr.pow2_u32(p),
                U32.sub(j, Arr.pow2_u32(p)),
                U32.is_lt(U32.sub(j, Arr.pow2_u32(p)),
                  U32.shr(Arr.pow2_u32(p))))) : T}) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T,
       Arr.fst(Array<T>, T,
         Array.swap.go(T, ANode{xs, ys}, Arr.pow2_u32(1n+p), i, v, False{})),
       Arr.pow2_u32(1n+p), j, False{}))
   == Arr.snd(Array<T>, T,
        Array.get.go(T, ANode{xs, ys}, Arr.pow2_u32(1n+p), j, False{})) : T}:
  (ys2a, d3) = d2
  (ys2b, pe2) = d3
  (+e2a, +e2b) = pe2
  +ea1 : {ys2a == ys1 : Array<T>} =
    Equal.trans(Array<T>, ys2a, ys2, ys1, e2a, ey2)
  +eb1 : {ys2b == ys1 : Array<T>} =
    Equal.trans(Array<T>, ys2b, ys2a, ys1, e2b, ea1)
  Arr.get_swap_diff_same_hi3(T, p, xs, ys, ys1, ys2a, ys2b, i, j, v, esh, ey1,
    ea1, eb1, hdy, Arr.dup(T, ys2b), ih)

def Arr.get_swap_diff_same_hi(-T: Data, +p: Nat, -xs: Array<T>, -ys: Array<T>,
    +i: U32, +j: U32, +v: T,
    +esh: {U32.shr(Arr.pow2_u32(1n+p)) == Arr.pow2_u32(p) : U32},
    +hdy: Arr.Depth(T, p, ys),
    d: &a1: Array<T> -> &a2: Array<T> ->
       {a1 == ys : Array<T>} & {a2 == a1 : Array<T>},
    ih: @ys3: Array<T> -> Arr.Depth(T, p, ys3) ->
        {Arr.snd(Array<T>, T,
           Array.get.go(T,
             Arr.fst(Array<T>, T,
               Array.swap.go(T, ys3, Arr.pow2_u32(p),
                 U32.sub(i, Arr.pow2_u32(p)), v,
                 U32.is_lt(U32.sub(i, Arr.pow2_u32(p)),
                   U32.shr(Arr.pow2_u32(p))))),
             Arr.pow2_u32(p), U32.sub(j, Arr.pow2_u32(p)),
             U32.is_lt(U32.sub(j, Arr.pow2_u32(p)), U32.shr(Arr.pow2_u32(p)))))
         == Arr.snd(Array<T>, T,
              Array.get.go(T, ys3, Arr.pow2_u32(p),
                U32.sub(j, Arr.pow2_u32(p)),
                U32.is_lt(U32.sub(j, Arr.pow2_u32(p)),
                  U32.shr(Arr.pow2_u32(p))))) : T}) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T,
       Arr.fst(Array<T>, T,
         Array.swap.go(T, ANode{xs, ys}, Arr.pow2_u32(1n+p), i, v, False{})),
       Arr.pow2_u32(1n+p), j, False{}))
   == Arr.snd(Array<T>, T,
        Array.get.go(T, ANode{xs, ys}, Arr.pow2_u32(1n+p), j, False{})) : T}:
  (ys1, d2) = d
  (ys2, pe) = d2
  (+ey1, +ey2) = pe
  Arr.get_swap_diff_same_hi2(T, p, xs, ys, ys1, i, j, v, esh, ey1, ys2, ey2,
    hdy, Arr.dup(T, ys2), ih)

def Arr.u32_eq_zero(+u: U32, +hz: {Arr.u32_zero_from(0n, u) == True{} : Bool}) ->
  {u == U32{Word.zero(32n)} : U32}:
  match u:
    case U32{+w}:
      Equal.cong(Word(32n), U32, x => U32{x}, w, Word.zero(32n),
        Arr.word_eq_zero(32n, w, hz))

def Arr.get_swap_diff_node(-T: Data, +p: Nat, xs: Array<T>, ys: Array<T>,
    +i: U32, +j: U32, +v: T,
    +hdx: Arr.Depth(T, p, xs), +hdy: Arr.Depth(T, p, ys),
    +hlt: {Nat.is_lt(1n+p, 32n) == True{} : Bool},
    +zi: {Arr.u32_zero_from(1n+p, i) == True{} : Bool},
    +zj: {Arr.u32_zero_from(1n+p, j) == True{} : Bool},
    +neq: {U32.is_eq(i, j) == False{} : Bool},
    bi: Bool, bj: Bool,
    +ebi: {bi == U32.is_lt(i, U32.shr(Arr.pow2_u32(1n+p))) : Bool},
    +ebj: {bj == U32.is_lt(j, U32.shr(Arr.pow2_u32(1n+p))) : Bool},
    ih_l: @xs3: Array<T> -> Arr.Depth(T, p, xs3) ->
          {Arr.u32_zero_from(p, i) == True{} : Bool} ->
          {Arr.u32_zero_from(p, j) == True{} : Bool} ->
          {Arr.snd(Array<T>, T,
             Array.get.go(T,
               Arr.fst(Array<T>, T,
                 Array.swap.go(T, xs3, Arr.pow2_u32(p), i, v,
                   U32.is_lt(i, U32.shr(Arr.pow2_u32(p))))),
               Arr.pow2_u32(p), j, U32.is_lt(j, U32.shr(Arr.pow2_u32(p)))))
           == Arr.snd(Array<T>, T,
                Array.get.go(T, xs3, Arr.pow2_u32(p), j,
                  U32.is_lt(j, U32.shr(Arr.pow2_u32(p))))) : T},
    ih_r: @ys3: Array<T> -> Arr.Depth(T, p, ys3) ->
          {Arr.u32_zero_from(p, U32.sub(i, Arr.pow2_u32(p))) == True{} : Bool} ->
          {Arr.u32_zero_from(p, U32.sub(j, Arr.pow2_u32(p))) == True{} : Bool} ->
          {Arr.snd(Array<T>, T,
             Array.get.go(T,
               Arr.fst(Array<T>, T,
                 Array.swap.go(T, ys3, Arr.pow2_u32(p),
                   U32.sub(i, Arr.pow2_u32(p)), v,
                   U32.is_lt(U32.sub(i, Arr.pow2_u32(p)),
                     U32.shr(Arr.pow2_u32(p))))),
               Arr.pow2_u32(p), U32.sub(j, Arr.pow2_u32(p)),
               U32.is_lt(U32.sub(j, Arr.pow2_u32(p)),
                 U32.shr(Arr.pow2_u32(p)))))
           == Arr.snd(Array<T>, T,
                Array.get.go(T, ys3, Arr.pow2_u32(p),
                  U32.sub(j, Arr.pow2_u32(p)),
                  U32.is_lt(U32.sub(j, Arr.pow2_u32(p)),
                    U32.shr(Arr.pow2_u32(p))))) : T}) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T,
       Arr.fst(Array<T>, T,
         Array.swap.go(T, ANode{xs, ys}, Arr.pow2_u32(1n+p), i, v, bi)),
       Arr.pow2_u32(1n+p), j, bj))
   == Arr.snd(Array<T>, T,
        Array.get.go(T, ANode{xs, ys}, Arr.pow2_u32(1n+p), j, bj)) : T}:
  match bi bj:
    case True{} False{}:
      +n : U32 = Arr.pow2_u32(1n+p)
      +h : U32 = U32.shr(n)
      +jj : U32 = U32.sub(j, h)
      Arr.get_swap_diff_cross_lh(T, xs, ys,
        Array.swap.go(T, xs, h, i, v, U32.is_lt(i, U32.shr(h))),
        n, j, Array.get.go(T, ys, h, jj, U32.is_lt(jj, U32.shr(h))), {==})
    case False{} True{}:
      +n : U32 = Arr.pow2_u32(1n+p)
      +h : U32 = U32.shr(n)
      +ii : U32 = U32.sub(i, h)
      Arr.get_swap_diff_cross_hl(T, xs, ys,
        Array.swap.go(T, ys, h, ii, v, U32.is_lt(ii, U32.shr(h))),
        n, j, Array.get.go(T, xs, h, j, U32.is_lt(j, U32.shr(h))), {==})
    case True{} True{}:
      +esh : {U32.shr(Arr.pow2_u32(1n+p)) == Arr.pow2_u32(p) : U32} =
        Arr.u32_shr_pow2(p, hlt)
      +plt : {Nat.is_lt(p, 32n) == True{} : Bool} =
        NatProof.Nat.is_le_lt_trans(p, 1n+p, 32n,
          NatProof.Nat.is_le_of_lt(p, 1n+p, NatProof.Nat.is_lt_succ_self(p)), hlt)
      +hi_lt : {U32.is_lt(i, Arr.pow2_u32(p)) == True{} : Bool} =
        Equal.trans(Bool,
          U32.is_lt(i, Arr.pow2_u32(p)),
          U32.is_lt(i, U32.shr(Arr.pow2_u32(1n+p))),
          True{},
          Equal.cong(U32, Bool, x => U32.is_lt(i, x),
            Arr.pow2_u32(p), U32.shr(Arr.pow2_u32(1n+p)),
            Equal.sym(U32, U32.shr(Arr.pow2_u32(1n+p)), Arr.pow2_u32(p), esh)),
          Equal.sym(Bool, True{}, U32.is_lt(i, U32.shr(Arr.pow2_u32(1n+p))), ebi))
      +hj_lt : {U32.is_lt(j, Arr.pow2_u32(p)) == True{} : Bool} =
        Equal.trans(Bool,
          U32.is_lt(j, Arr.pow2_u32(p)),
          U32.is_lt(j, U32.shr(Arr.pow2_u32(1n+p))),
          True{},
          Equal.cong(U32, Bool, x => U32.is_lt(j, x),
            Arr.pow2_u32(p), U32.shr(Arr.pow2_u32(1n+p)),
            Equal.sym(U32, U32.shr(Arr.pow2_u32(1n+p)), Arr.pow2_u32(p), esh)),
          Equal.sym(Bool, True{}, U32.is_lt(j, U32.shr(Arr.pow2_u32(1n+p))), ebj))
      +zip : {Arr.u32_zero_from(p, i) == True{} : Bool} =
        Arr.u32_zero_from_lt(p, i, zi, plt, hi_lt)
      +zjp : {Arr.u32_zero_from(p, j) == True{} : Bool} =
        Arr.u32_zero_from_lt(p, j, zj, plt, hj_lt)
      Arr.get_swap_diff_same_lo(T, p, xs, ys, i, j, v, esh, hdx, Arr.dup(T, xs),
        x => hx => ih_l(x, hx, zip, zjp))
    case False{} False{}:
      +esh : {U32.shr(Arr.pow2_u32(1n+p)) == Arr.pow2_u32(p) : U32} =
        Arr.u32_shr_pow2(p, hlt)
      +plt : {Nat.is_lt(p, 32n) == True{} : Bool} =
        NatProof.Nat.is_le_lt_trans(p, 1n+p, 32n,
          NatProof.Nat.is_le_of_lt(p, 1n+p, NatProof.Nat.is_lt_succ_self(p)), hlt)
      +hi_ge : {U32.is_lt(i, Arr.pow2_u32(p)) == False{} : Bool} =
        Equal.trans(Bool,
          U32.is_lt(i, Arr.pow2_u32(p)),
          U32.is_lt(i, U32.shr(Arr.pow2_u32(1n+p))),
          False{},
          Equal.cong(U32, Bool, x => U32.is_lt(i, x),
            Arr.pow2_u32(p), U32.shr(Arr.pow2_u32(1n+p)),
            Equal.sym(U32, U32.shr(Arr.pow2_u32(1n+p)), Arr.pow2_u32(p), esh)),
          Equal.sym(Bool, False{}, U32.is_lt(i, U32.shr(Arr.pow2_u32(1n+p))), ebi))
      +hj_ge : {U32.is_lt(j, Arr.pow2_u32(p)) == False{} : Bool} =
        Equal.trans(Bool,
          U32.is_lt(j, Arr.pow2_u32(p)),
          U32.is_lt(j, U32.shr(Arr.pow2_u32(1n+p))),
          False{},
          Equal.cong(U32, Bool, x => U32.is_lt(j, x),
            Arr.pow2_u32(p), U32.shr(Arr.pow2_u32(1n+p)),
            Equal.sym(U32, U32.shr(Arr.pow2_u32(1n+p)), Arr.pow2_u32(p), esh)),
          Equal.sym(Bool, False{}, U32.is_lt(j, U32.shr(Arr.pow2_u32(1n+p))), ebj))
      +zip : {Arr.u32_zero_from(p, U32.sub(i, Arr.pow2_u32(p))) == True{} : Bool} =
        Arr.u32_zero_from_ge(p, i, zi, plt, hi_ge)
      +zjp : {Arr.u32_zero_from(p, U32.sub(j, Arr.pow2_u32(p))) == True{} : Bool} =
        Arr.u32_zero_from_ge(p, j, zj, plt, hj_ge)
      Arr.get_swap_diff_same_hi(T, p, xs, ys, i, j, v, esh, hdy, Arr.dup(T, ys),
        y => hy => ih_r(y, hy, zip, zjp))

def Arr.get_swap_diff_go(-T: Data, +d: Nat, a: Array<T>, +i: U32, +j: U32,
    +v: T, +hd: Arr.Depth(T, d, a),
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.u32_zero_from(d, i) == True{} : Bool},
    +zj: {Arr.u32_zero_from(d, j) == True{} : Bool},
    +neq: {U32.is_eq(i, j) == False{} : Bool}) ->
  {Arr.snd(Array<T>, T,
     Array.get.go(T,
       Arr.fst(Array<T>, T,
         Array.swap.go(T, a, Arr.pow2_u32(d), i, v,
           U32.is_lt(i, U32.shr(Arr.pow2_u32(d))))),
       Arr.pow2_u32(d), j, U32.is_lt(j, U32.shr(Arr.pow2_u32(d)))))
   == Arr.snd(Array<T>, T,
        Array.get.go(T, a, Arr.pow2_u32(d), j,
          U32.is_lt(j, U32.shr(Arr.pow2_u32(d))))) : T}:
  match d a:
    case 0n ALeaf{x}:
      +ei : {i == U32{Word.zero(32n)} : U32} = Arr.u32_eq_zero(i, zi)
      +ej : {j == U32{Word.zero(32n)} : U32} = Arr.u32_eq_zero(j, zj)
      Empty.absurd(
        {Arr.snd(Array<T>, T,
           Array.get.go(T,
             Arr.fst(Array<T>, T,
               Array.swap.go(T, ALeaf{x}, Arr.pow2_u32(0n), i, v,
                 U32.is_lt(i, U32.shr(Arr.pow2_u32(0n))))),
             Arr.pow2_u32(0n), j, U32.is_lt(j, U32.shr(Arr.pow2_u32(0n)))))
         == Arr.snd(Array<T>, T,
              Array.get.go(T, ALeaf{x}, Arr.pow2_u32(0n), j,
                U32.is_lt(j, U32.shr(Arr.pow2_u32(0n))))) : T},
        Arr.u32_ne_of_eq_false(i, j, neq,
          Equal.trans(U32, i, U32{Word.zero(32n)}, j, ei,
            Equal.sym(U32, j, U32{Word.zero(32n)}, ej))))
    case 1n++p ANode{xs, ys}:
      DPair{+hdx, +hdy} = hd
      +plt : {Nat.is_lt(p, 32n) == True{} : Bool} =
        NatProof.Nat.is_le_lt_trans(p, 1n+p, 32n,
          NatProof.Nat.is_le_of_lt(p, 1n+p, NatProof.Nat.is_lt_succ_self(p)), hlt)
      Arr.get_swap_diff_node(T, p, xs, ys, i, j, v, hdx, hdy, hlt, zi, zj, neq,
        U32.is_lt(i, U32.shr(Arr.pow2_u32(1n+p))),
        U32.is_lt(j, U32.shr(Arr.pow2_u32(1n+p))),
        {==}, {==},
        x => hx => zip => zjp =>
          Arr.get_swap_diff_go(T, p, x, i, j, v, hx, plt, zip, zjp, neq),
        y => hy => zip => zjp =>
          Arr.get_swap_diff_go(T, p, y,
            U32.sub(i, Arr.pow2_u32(p)), U32.sub(j, Arr.pow2_u32(p)), v,
            hy, plt, zip, zjp, Arr.u32_sub_ne(i, j, Arr.pow2_u32(p), neq)))
    case 0n ANode{xs, ys}:
      Empty.absurd(
        {Arr.snd(Array<T>, T,
           Array.get.go(T,
             Arr.fst(Array<T>, T,
               Array.swap.go(T, ANode{xs, ys}, Arr.pow2_u32(0n), i, v,
                 U32.is_lt(i, U32.shr(Arr.pow2_u32(0n))))),
             Arr.pow2_u32(0n), j, U32.is_lt(j, U32.shr(Arr.pow2_u32(0n)))))
         == Arr.snd(Array<T>, T,
              Array.get.go(T, ANode{xs, ys}, Arr.pow2_u32(0n), j,
                U32.is_lt(j, U32.shr(Arr.pow2_u32(0n))))) : T}, hd)
    case 1n++p ALeaf{x}:
      Empty.absurd(
        {Arr.snd(Array<T>, T,
           Array.get.go(T,
             Arr.fst(Array<T>, T,
               Array.swap.go(T, ALeaf{x}, Arr.pow2_u32(1n+p), i, v,
                 U32.is_lt(i, U32.shr(Arr.pow2_u32(1n+p))))),
             Arr.pow2_u32(1n+p), j, U32.is_lt(j, U32.shr(Arr.pow2_u32(1n+p)))))
         == Arr.snd(Array<T>, T,
              Array.get.go(T, ALeaf{x}, Arr.pow2_u32(1n+p), j,
                U32.is_lt(j, U32.shr(Arr.pow2_u32(1n+p))))) : T}, hd)

def Arr.get_swap_diff_dup3(-T: Data, +d: Nat, -a: Array<T>, a1: Array<T>,
    a2a: Array<T>, -a2b: Array<T>, +i: U32, +j: U32, +v: T,
    +ea1: {a1 == a : Array<T>}, +ea2a: {a2a == a1 : Array<T>},
    +ea2b: {a2b == a1 : Array<T>},
    +hd: Arr.Depth(T, d, a),
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.u32_zero_from(d, i) == True{} : Bool},
    +zj: {Arr.u32_zero_from(d, j) == True{} : Bool},
    +neq: {U32.is_eq(i, j) == False{} : Bool},
    dp3: &b1: Array<T> -> &b2: Array<T> ->
         {b1 == a2b : Array<T>} & {b2 == b1 : Array<T>}) ->
  {Arr.snd(Array<T>, T,
     Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a, i, v)), j))
   == Arr.snd(Array<T>, T, Array.get(T, a, j)) : T}:
  (a3a, dp4) = dp3
  (a3b, pe3) = dp4
  (+e3a, +e3b) = pe3
  +e3a1 : {a3a == a1 : Array<T>} =
    Equal.trans(Array<T>, a3a, a2b, a1, e3a, ea2b)
  +e3b1 : {a3b == a1 : Array<T>} =
    Equal.trans(Array<T>, a3b, a3a, a1, e3b, e3a1)
  +n : U32 = Arr.pow2_u32(d)
  +emi : {U32.and(i, U32.sub(n, 1)) == i : U32} = Arr.u32_and_mask(d, i, zi)
  +emj : {U32.and(j, U32.sub(n, 1)) == j : U32} = Arr.u32_and_mask(d, j, zj)
  +hd1 : Arr.Depth(T, d, a1) =
    Arr.depth_transport(T, d, a, a1, Equal.sym(Array<T>, a1, a, ea1), hd)
  +hd2a : Arr.Depth(T, d, a2a) =
    Arr.depth_transport(T, d, a1, a2a, Equal.sym(Array<T>, a2a, a1, ea2a), hd1)
  +hd3a : Arr.Depth(T, d, a3a) =
    Arr.depth_transport(T, d, a1, a3a, Equal.sym(Array<T>, a3a, a1, e3a1), hd1)
  +hd3b : Arr.Depth(T, d, a3b) =
    Arr.depth_transport(T, d, a1, a3b, Equal.sym(Array<T>, a3b, a1, e3b1), hd1)
  +p2a = Arr.swap_depth_pair(T, d, a2a, i, v, hd2a)
  +hd_sw2a : Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v))) =
    Arr.dpair_l(
      Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v))),
      {Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v))
       == Arr.fst(Array<T>, T,
            Array.swap.go(T, a2a, n, U32.and(i, U32.sub(n, 1)), v,
              U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)))) : Array<T>},
      p2a)
  +esw2a : {Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v))
            == Arr.fst(Array<T>, T,
                 Array.swap.go(T, a2a, n, U32.and(i, U32.sub(n, 1)), v,
                   U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n))))
            : Array<T>} =
    Arr.dpair_r(
      Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v))),
      {Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v))
       == Arr.fst(Array<T>, T,
            Array.swap.go(T, a2a, n, U32.and(i, U32.sub(n, 1)), v,
              U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)))) : Array<T>},
      p2a)
  +esw : {Arr.fst(Array<T>, T, Array.swap(T, a1, i, v))
          == Arr.fst(Array<T>, T,
               Array.swap.go(T, a1, n, i, v, U32.is_lt(i, U32.shr(n))))
          : Array<T>} =
    Equal.trans(Array<T>,
      Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)),
      Arr.fst(Array<T>, T,
        Array.swap.go(T, a1, n, U32.and(i, U32.sub(n, 1)), v,
          U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)))),
      Arr.fst(Array<T>, T,
        Array.swap.go(T, a1, n, i, v, U32.is_lt(i, U32.shr(n)))),
      Equal.trans(Array<T>,
        Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)),
        Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v)),
        Arr.fst(Array<T>, T,
          Array.swap.go(T, a1, n, U32.and(i, U32.sub(n, 1)), v,
            U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)))),
        Equal.cong(Array<T>, Array<T>,
          x => Arr.fst(Array<T>, T, Array.swap(T, x, i, v)),
          a1, a2a, Equal.sym(Array<T>, a2a, a1, ea2a)),
        Equal.trans(Array<T>,
          Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v)),
          Arr.fst(Array<T>, T,
            Array.swap.go(T, a2a, n, U32.and(i, U32.sub(n, 1)), v,
              U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)))),
          Arr.fst(Array<T>, T,
            Array.swap.go(T, a1, n, U32.and(i, U32.sub(n, 1)), v,
              U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)))),
          esw2a,
          Equal.cong(Array<T>, Array<T>,
            x => Arr.fst(Array<T>, T,
                   Array.swap.go(T, x, n, U32.and(i, U32.sub(n, 1)), v,
                     U32.is_lt(U32.and(i, U32.sub(n, 1)), U32.shr(n)))),
            a2a, a1, ea2a))),
      Equal.cong(U32, Array<T>,
        u => Arr.fst(Array<T>, T,
               Array.swap.go(T, a1, n, u, v, U32.is_lt(u, U32.shr(n)))),
        U32.and(i, U32.sub(n, 1)), i, emi))
  +hd_sw1 : Arr.Depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v))) =
    Arr.depth_transport(T, d,
      Arr.fst(Array<T>, T, Array.swap(T, a2a, i, v)),
      Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)),
      Equal.cong(Array<T>, Array<T>,
        x => Arr.fst(Array<T>, T, Array.swap(T, x, i, v)), a2a, a1, ea2a),
      hd_sw2a)
  +eget1 : {Arr.snd(Array<T>, T,
              Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), j))
            == Arr.snd(Array<T>, T,
                 Array.get.go(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)),
                   n, j, U32.is_lt(j, U32.shr(n)))) : T} =
    Equal.trans(T,
      Arr.snd(Array<T>, T,
        Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), j)),
      Arr.snd(Array<T>, T,
        Array.get.go(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), n,
          U32.and(j, U32.sub(n, 1)),
          U32.is_lt(U32.and(j, U32.sub(n, 1)), U32.shr(n)))),
      Arr.snd(Array<T>, T,
        Array.get.go(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), n, j,
          U32.is_lt(j, U32.shr(n)))),
      Arr.get_depth(T, d, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), j, hd_sw1),
      Equal.cong(U32, T,
        u => Arr.snd(Array<T>, T,
               Array.get.go(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)),
                 n, u, U32.is_lt(u, U32.shr(n)))),
        U32.and(j, U32.sub(n, 1)), j, emj))
  +eget2 : {Arr.snd(Array<T>, T, Array.get(T, a1, j))
            == Arr.snd(Array<T>, T,
                 Array.get.go(T, a1, n, j, U32.is_lt(j, U32.shr(n)))) : T} =
    Equal.trans(T,
      Arr.snd(Array<T>, T, Array.get(T, a1, j)),
      Arr.snd(Array<T>, T,
        Array.get.go(T, a1, n, U32.and(j, U32.sub(n, 1)),
          U32.is_lt(U32.and(j, U32.sub(n, 1)), U32.shr(n)))),
      Arr.snd(Array<T>, T, Array.get.go(T, a1, n, j, U32.is_lt(j, U32.shr(n)))),
      Equal.trans(T,
        Arr.snd(Array<T>, T, Array.get(T, a1, j)),
        Arr.snd(Array<T>, T, Array.get(T, a3a, j)),
        Arr.snd(Array<T>, T,
          Array.get.go(T, a1, n, U32.and(j, U32.sub(n, 1)),
            U32.is_lt(U32.and(j, U32.sub(n, 1)), U32.shr(n)))),
        Equal.cong(Array<T>, T, x => Arr.snd(Array<T>, T, Array.get(T, x, j)),
          a1, a3a, Equal.sym(Array<T>, a3a, a1, e3a1)),
        Equal.trans(T,
          Arr.snd(Array<T>, T, Array.get(T, a3a, j)),
          Arr.snd(Array<T>, T,
            Array.get.go(T, a3a, n, U32.and(j, U32.sub(n, 1)),
              U32.is_lt(U32.and(j, U32.sub(n, 1)), U32.shr(n)))),
          Arr.snd(Array<T>, T,
            Array.get.go(T, a1, n, U32.and(j, U32.sub(n, 1)),
              U32.is_lt(U32.and(j, U32.sub(n, 1)), U32.shr(n)))),
          Arr.get_depth(T, d, a3a, j, hd3a),
          Equal.cong(Array<T>, T,
            x => Arr.snd(Array<T>, T,
                   Array.get.go(T, x, n, U32.and(j, U32.sub(n, 1)),
                     U32.is_lt(U32.and(j, U32.sub(n, 1)), U32.shr(n)))),
            a3a, a1, e3a1))),
      Equal.cong(U32, T,
        u => Arr.snd(Array<T>, T,
               Array.get.go(T, a1, n, u, U32.is_lt(u, U32.shr(n)))),
        U32.and(j, U32.sub(n, 1)), j, emj))
  +ego : {Arr.snd(Array<T>, T,
            Array.get.go(T,
              Arr.fst(Array<T>, T,
                Array.swap.go(T, a1, n, i, v, U32.is_lt(i, U32.shr(n)))),
              n, j, U32.is_lt(j, U32.shr(n))))
          == Arr.snd(Array<T>, T,
               Array.get.go(T, a1, n, j, U32.is_lt(j, U32.shr(n)))) : T} =
    Equal.trans(T,
      Arr.snd(Array<T>, T,
        Array.get.go(T,
          Arr.fst(Array<T>, T,
            Array.swap.go(T, a1, n, i, v, U32.is_lt(i, U32.shr(n)))),
          n, j, U32.is_lt(j, U32.shr(n)))),
      Arr.snd(Array<T>, T,
        Array.get.go(T,
          Arr.fst(Array<T>, T,
            Array.swap.go(T, a3b, n, i, v, U32.is_lt(i, U32.shr(n)))),
          n, j, U32.is_lt(j, U32.shr(n)))),
      Arr.snd(Array<T>, T, Array.get.go(T, a1, n, j, U32.is_lt(j, U32.shr(n)))),
      Equal.cong(Array<T>, T,
        x => Arr.snd(Array<T>, T,
               Array.get.go(T,
                 Arr.fst(Array<T>, T,
                   Array.swap.go(T, x, n, i, v, U32.is_lt(i, U32.shr(n)))),
                 n, j, U32.is_lt(j, U32.shr(n)))),
        a1, a3b, Equal.sym(Array<T>, a3b, a1, e3b1)),
      Equal.trans(T,
        Arr.snd(Array<T>, T,
          Array.get.go(T,
            Arr.fst(Array<T>, T,
              Array.swap.go(T, a3b, n, i, v, U32.is_lt(i, U32.shr(n)))),
            n, j, U32.is_lt(j, U32.shr(n)))),
        Arr.snd(Array<T>, T,
          Array.get.go(T, a3b, n, j, U32.is_lt(j, U32.shr(n)))),
        Arr.snd(Array<T>, T,
          Array.get.go(T, a1, n, j, U32.is_lt(j, U32.shr(n)))),
        Arr.get_swap_diff_go(T, d, a3b, i, j, v, hd3b, hlt, zi, zj, neq),
        Equal.cong(Array<T>, T,
          x => Arr.snd(Array<T>, T,
                 Array.get.go(T, x, n, j, U32.is_lt(j, U32.shr(n)))),
          a3b, a1, e3b1)))
  %ea1 : {Arr.snd(Array<T>, T,
            Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, _, i, v)), j))
          == Arr.snd(Array<T>, T, Array.get(T, _, j)) : T}
  Equal.trans(T,
    Arr.snd(Array<T>, T,
      Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), j)),
    Arr.snd(Array<T>, T,
      Array.get.go(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), n, j,
        U32.is_lt(j, U32.shr(n)))),
    Arr.snd(Array<T>, T, Array.get(T, a1, j)),
    eget1,
    Equal.trans(T,
      Arr.snd(Array<T>, T,
        Array.get.go(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), n, j,
          U32.is_lt(j, U32.shr(n)))),
      Arr.snd(Array<T>, T, Array.get.go(T, a1, n, j, U32.is_lt(j, U32.shr(n)))),
      Arr.snd(Array<T>, T, Array.get(T, a1, j)),
      Equal.trans(T,
        Arr.snd(Array<T>, T,
          Array.get.go(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), n, j,
            U32.is_lt(j, U32.shr(n)))),
        Arr.snd(Array<T>, T,
          Array.get.go(T,
            Arr.fst(Array<T>, T,
              Array.swap.go(T, a1, n, i, v, U32.is_lt(i, U32.shr(n)))),
            n, j, U32.is_lt(j, U32.shr(n)))),
        Arr.snd(Array<T>, T, Array.get.go(T, a1, n, j, U32.is_lt(j, U32.shr(n)))),
        Equal.cong(Array<T>, T,
          x => Arr.snd(Array<T>, T,
                 Array.get.go(T, x, n, j, U32.is_lt(j, U32.shr(n)))),
          Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)),
          Arr.fst(Array<T>, T,
            Array.swap.go(T, a1, n, i, v, U32.is_lt(i, U32.shr(n)))),
          esw),
        ego),
      Equal.sym(T,
        Arr.snd(Array<T>, T, Array.get(T, a1, j)),
        Arr.snd(Array<T>, T, Array.get.go(T, a1, n, j, U32.is_lt(j, U32.shr(n)))),
        eget2)))

def Arr.get_swap_diff_dup2(-T: Data, +d: Nat, -a: Array<T>, a1: Array<T>,
    +i: U32, +j: U32, +v: T, +ea1: {a1 == a : Array<T>}, -a2: Array<T>,
    +ea2: {a2 == a1 : Array<T>}, +hd: Arr.Depth(T, d, a),
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.u32_zero_from(d, i) == True{} : Bool},
    +zj: {Arr.u32_zero_from(d, j) == True{} : Bool},
    +neq: {U32.is_eq(i, j) == False{} : Bool},
    dp2: &b1: Array<T> -> &b2: Array<T> ->
         {b1 == a2 : Array<T>} & {b2 == b1 : Array<T>}) ->
  {Arr.snd(Array<T>, T,
     Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a, i, v)), j))
   == Arr.snd(Array<T>, T, Array.get(T, a, j)) : T}:
  (a2a, dp3) = dp2
  (a2b, pe2) = dp3
  (+e2a, +e2b) = pe2
  +ea2a : {a2a == a1 : Array<T>} =
    Equal.trans(Array<T>, a2a, a2, a1, e2a, ea2)
  +ea2b : {a2b == a1 : Array<T>} =
    Equal.trans(Array<T>, a2b, a2a, a1, e2b, ea2a)
  Arr.get_swap_diff_dup3(T, d, a, a1, a2a, a2b, i, j, v, ea1, ea2a, ea2b, hd,
    hlt, zi, zj, neq, Arr.dup(T, a2b))

def Arr.get_swap_diff_dup(-T: Data, +d: Nat, -a: Array<T>, +i: U32, +j: U32,
    +v: T, +hd: Arr.Depth(T, d, a),
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.u32_zero_from(d, i) == True{} : Bool},
    +zj: {Arr.u32_zero_from(d, j) == True{} : Bool},
    +neq: {U32.is_eq(i, j) == False{} : Bool},
    dp: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == a : Array<T>} & {a2 == a1 : Array<T>}) ->
  {Arr.snd(Array<T>, T,
     Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a, i, v)), j))
   == Arr.snd(Array<T>, T, Array.get(T, a, j)) : T}:
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  Arr.get_swap_diff_dup2(T, d, a, a1, i, j, v, ea1, a2, ea2, hd, hlt, zi, zj,
    neq, Arr.dup(T, a2))

def Arr.get_swap_diff(-T: Data, +d: Nat, a: Array<T>, +i: U32, +j: U32, +v: T,
    +hd: Arr.Depth(T, d, a),
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.u32_zero_from(d, i) == True{} : Bool},
    +zj: {Arr.u32_zero_from(d, j) == True{} : Bool},
    +neq: {U32.is_eq(i, j) == False{} : Bool}) ->
  {Arr.snd(Array<T>, T,
     Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a, i, v)), j))
   == Arr.snd(Array<T>, T, Array.get(T, a, j)) : T}:
  Arr.get_swap_diff_dup(T, d, a, i, j, v, hd, hlt, zi, zj, neq, Arr.dup(T, a))

def Arr.get_set_same_dup(-T: Data, +d: Nat, -a: Array<T>, +i: U32, +v: T,
    +hd: Arr.Depth(T, d, a),
    dp: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == a : Array<T>} & {a2 == a1 : Array<T>}) ->
  {Arr.snd(Array<T>, T, Array.get(T, Array.set(T, a, i, v), i)) == v : T}:
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  +hd2 : Arr.Depth(T, d, a2) =
    Arr.depth_transport(T, d, a, a2,
      Equal.sym(Array<T>, a2, a, Equal.trans(Array<T>, a2, a1, a, ea2, ea1)),
      hd)
  %ea1 : {Arr.snd(Array<T>, T, Array.get(T, Array.set(T, _, i, v), i)) == v : T}
  Equal.trans(T,
    Arr.snd(Array<T>, T, Array.get(T, Array.set(T, a1, i, v), i)),
    Arr.snd(Array<T>, T,
      Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), i)),
    v,
    Equal.cong(Array<T>, T, x => Arr.snd(Array<T>, T, Array.get(T, x, i)),
      Array.set(T, a1, i, v),
      Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)),
      Arr.set_eq(T, a1, i, v)),
    Equal.trans(T,
      Arr.snd(Array<T>, T,
        Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), i)),
      Arr.snd(Array<T>, T,
        Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a2, i, v)), i)),
      v,
      Equal.cong(Array<T>, T,
        x => Arr.snd(Array<T>, T,
               Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, x, i, v)), i)),
        a1, a2, Equal.sym(Array<T>, a2, a1, ea2)),
      Arr.get_swap_same(T, d, a2, i, v, hd2)))

def Arr.get_set_same(-T: Data, +d: Nat, a: Array<T>, +i: U32, +v: T,
    +hd: Arr.Depth(T, d, a)) ->
  {Arr.snd(Array<T>, T, Array.get(T, Array.set(T, a, i, v), i)) == v : T}:
  Arr.get_set_same_dup(T, d, a, i, v, hd, Arr.dup(T, a))

def Arr.get_set_diff_dup(-T: Data, +d: Nat, -a: Array<T>, +i: U32, +j: U32,
    +v: T, +hd: Arr.Depth(T, d, a),
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.u32_zero_from(d, i) == True{} : Bool},
    +zj: {Arr.u32_zero_from(d, j) == True{} : Bool},
    +neq: {U32.is_eq(i, j) == False{} : Bool},
    dp: &a1: Array<T> -> &a2: Array<T> ->
        {a1 == a : Array<T>} & {a2 == a1 : Array<T>}) ->
  {Arr.snd(Array<T>, T, Array.get(T, Array.set(T, a, i, v), j))
   == Arr.snd(Array<T>, T, Array.get(T, a, j)) : T}:
  (a1, dp2) = dp
  (a2, pe) = dp2
  (+ea1, +ea2) = pe
  +hd2 : Arr.Depth(T, d, a2) =
    Arr.depth_transport(T, d, a, a2,
      Equal.sym(Array<T>, a2, a, Equal.trans(Array<T>, a2, a1, a, ea2, ea1)),
      hd)
  %ea1 : {Arr.snd(Array<T>, T, Array.get(T, Array.set(T, _, i, v), j))
          == Arr.snd(Array<T>, T, Array.get(T, _, j)) : T}
  Equal.trans(T,
    Arr.snd(Array<T>, T, Array.get(T, Array.set(T, a1, i, v), j)),
    Arr.snd(Array<T>, T,
      Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), j)),
    Arr.snd(Array<T>, T, Array.get(T, a1, j)),
    Equal.cong(Array<T>, T, x => Arr.snd(Array<T>, T, Array.get(T, x, j)),
      Array.set(T, a1, i, v),
      Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)),
      Arr.set_eq(T, a1, i, v)),
    Equal.trans(T,
      Arr.snd(Array<T>, T,
        Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a1, i, v)), j)),
      Arr.snd(Array<T>, T,
        Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a2, i, v)), j)),
      Arr.snd(Array<T>, T, Array.get(T, a1, j)),
      Equal.cong(Array<T>, T,
        x => Arr.snd(Array<T>, T,
               Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, x, i, v)), j)),
        a1, a2, Equal.sym(Array<T>, a2, a1, ea2)),
      Equal.trans(T,
        Arr.snd(Array<T>, T,
          Array.get(T, Arr.fst(Array<T>, T, Array.swap(T, a2, i, v)), j)),
        Arr.snd(Array<T>, T, Array.get(T, a2, j)),
        Arr.snd(Array<T>, T, Array.get(T, a1, j)),
        Arr.get_swap_diff(T, d, a2, i, j, v, hd2, hlt, zi, zj, neq),
        Equal.cong(Array<T>, T, x => Arr.snd(Array<T>, T, Array.get(T, x, j)),
          a2, a1, ea2))))

def Arr.get_set_diff(-T: Data, +d: Nat, a: Array<T>, +i: U32, +j: U32, +v: T,
    +hd: Arr.Depth(T, d, a),
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.u32_zero_from(d, i) == True{} : Bool},
    +zj: {Arr.u32_zero_from(d, j) == True{} : Bool},
    +neq: {U32.is_eq(i, j) == False{} : Bool}) ->
  {Arr.snd(Array<T>, T, Array.get(T, Array.set(T, a, i, v), j))
   == Arr.snd(Array<T>, T, Array.get(T, a, j)) : T}:
  Arr.get_set_diff_dup(T, d, a, i, j, v, hd, hlt, zi, zj, neq, Arr.dup(T, a))
