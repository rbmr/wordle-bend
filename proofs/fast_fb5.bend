# Equivalence and bit-layout laws for the zero-allocation 5-letter feedback
# encoder (`SolveFast.feedback_code5`) and decoder (`SolveFast.decode_fb5`).
#
# A 5-letter feedback is packed into 10 bits of a `U32` (`Gray = 0`,
# `Yellow = 1`, `Green = 2` at bit offsets `0, 2, 4, 6, 8`; all-green = 682).
# This module proves:
# - `decode_fb5(encode_fb5(c0..c4)) == [c0, c1, c2, c3, c4]` and
#   `Arr.u32_zero_from(10n, encode_fb5(c0..c4)) == True{}`;
# - `feedback_code5(g0..g4, a0..a4) == encode_fb5_list(Feedback.feedback(...))`;
# - `decode_fb5(feedback_code5(g0..g4, a0..a4)) == Feedback.feedback(...)`;
# - `U32.is_eq(feedback_code5(g0..g4, a0..a4), 682) == Feedback.word_eq(...)`.
import Base
import ../src/feedback.bend as Feedback
import ../src/solve_fast.bend as SolveFast
import ./logic.bend as Logic
import ./feedback.bend as FbProof
import ./fast_groups.bend as FG
import ./array.bend as Arr

# ---------------------------------------------------------------------------
# Bitwise Word / U32 algebra for `U32.or`, `U32.and`, and `u32_zero_from`
# ---------------------------------------------------------------------------

def FF5.bool_or_false_l(b: Bool) -> {Bool.or(False{}, b) == b : Bool}:
  {==}

def FF5.bool_or_false_r(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def FF5.bool_or_assoc(a: Bool, b: Bool, c: Bool) ->
  {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def FF5.bool_and_or_distrib(a: Bool, b: Bool, c: Bool) ->
  {Bool.and(Bool.or(a, b), c) == Bool.or(Bool.and(a, c), Bool.and(b, c)) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} _ _:
      {==}

def FF5.bool_not_or(a: Bool, b: Bool) ->
  {Bool.not(Bool.or(a, b)) == Bool.and(Bool.not(a), Bool.not(b)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def FF5.bool_and_true_intro(a: Bool, b: Bool,
    +ea: {a == True{} : Bool}, +eb: {b == True{} : Bool}) ->
  {Bool.and(a, b) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(a, b), Bool.and(True{}, b), True{},
    Equal.cong(Bool, Bool, x => Bool.and(x, b), a, True{}, ea), eb)

def FF5.word_or_zero_l(+m: Nat, +w: Word(m)) ->
  {Word.or(m, Word.zero(m), w) == w : Word(m)}:
  match m:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++mp:
      match w:
        case WCon{+b, +t}:
          Equal.cong(Word(mp), Word(1n+mp), x => WCon{b, x},
            Word.or(mp, Word.zero(mp), t), t, FF5.word_or_zero_l(mp, t))

def FF5.word_or_zero_r(+m: Nat, +w: Word(m)) ->
  {Word.or(m, w, Word.zero(m)) == w : Word(m)}:
  match m:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++mp:
      match w:
        case WCon{+b, +t}:
          Equal.trans(Word(1n+mp),
            WCon{Bool.or(b, False{}), Word.or(mp, t, Word.zero(mp))},
            WCon{b, Word.or(mp, t, Word.zero(mp))},
            WCon{b, t},
            Equal.cong(Bool, Word(1n+mp),
              x => WCon{x, Word.or(mp, t, Word.zero(mp))},
              Bool.or(b, False{}), b, FF5.bool_or_false_r(b)),
            Equal.cong(Word(mp), Word(1n+mp), x => WCon{b, x},
              Word.or(mp, t, Word.zero(mp)), t, FF5.word_or_zero_r(mp, t)))

def FF5.word_or_assoc(+m: Nat, +a: Word(m), +b: Word(m), +c: Word(m)) ->
  {Word.or(m, Word.or(m, a, b), c) == Word.or(m, a, Word.or(m, b, c)) : Word(m)}:
  match m:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n++mp:
      match a b c:
        case WCon{+ab, +at} WCon{+bb, +bt} WCon{+cb, +ct}:
          Equal.trans(Word(1n+mp),
            WCon{Bool.or(Bool.or(ab, bb), cb),
                 Word.or(mp, Word.or(mp, at, bt), ct)},
            WCon{Bool.or(ab, Bool.or(bb, cb)),
                 Word.or(mp, Word.or(mp, at, bt), ct)},
            WCon{Bool.or(ab, Bool.or(bb, cb)),
                 Word.or(mp, at, Word.or(mp, bt, ct))},
            Equal.cong(Bool, Word(1n+mp),
              x => WCon{x, Word.or(mp, Word.or(mp, at, bt), ct)},
              Bool.or(Bool.or(ab, bb), cb), Bool.or(ab, Bool.or(bb, cb)),
              FF5.bool_or_assoc(ab, bb, cb)),
            Equal.cong(Word(mp), Word(1n+mp),
              x => WCon{Bool.or(ab, Bool.or(bb, cb)), x},
              Word.or(mp, Word.or(mp, at, bt), ct),
              Word.or(mp, at, Word.or(mp, bt, ct)),
              FF5.word_or_assoc(mp, at, bt, ct)))

def FF5.word_and_or_distrib(+m: Nat, +a: Word(m), +b: Word(m), +c: Word(m)) ->
  {Word.and(m, Word.or(m, a, b), c)
   == Word.or(m, Word.and(m, a, c), Word.and(m, b, c)) : Word(m)}:
  match m:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n++mp:
      match a b c:
        case WCon{+ab, +at} WCon{+bb, +bt} WCon{+cb, +ct}:
          Equal.trans(Word(1n+mp),
            WCon{Bool.and(Bool.or(ab, bb), cb),
                 Word.and(mp, Word.or(mp, at, bt), ct)},
            WCon{Bool.or(Bool.and(ab, cb), Bool.and(bb, cb)),
                 Word.and(mp, Word.or(mp, at, bt), ct)},
            WCon{Bool.or(Bool.and(ab, cb), Bool.and(bb, cb)),
                 Word.or(mp, Word.and(mp, at, ct), Word.and(mp, bt, ct))},
            Equal.cong(Bool, Word(1n+mp),
              x => WCon{x, Word.and(mp, Word.or(mp, at, bt), ct)},
              Bool.and(Bool.or(ab, bb), cb),
              Bool.or(Bool.and(ab, cb), Bool.and(bb, cb)),
              FF5.bool_and_or_distrib(ab, bb, cb)),
            Equal.cong(Word(mp), Word(1n+mp),
              x => WCon{Bool.or(Bool.and(ab, cb), Bool.and(bb, cb)), x},
              Word.and(mp, Word.or(mp, at, bt), ct),
              Word.or(mp, Word.and(mp, at, ct), Word.and(mp, bt, ct)),
              FF5.word_and_or_distrib(mp, at, bt, ct)))

def FF5.word_or_zero_from(+k: Nat, +m: Nat, +a: Word(m), +b: Word(m),
    +ha: {Arr.Arr.word_zero_from(k, m, a) == True{} : Bool},
    +hb: {Arr.Arr.word_zero_from(k, m, b) == True{} : Bool}) ->
  {Arr.Arr.word_zero_from(k, m, Word.or(m, a, b)) == True{} : Bool}:
  match k m:
    case _ 0n:
      {==}
    case 0n 1n++mp:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          +na : {Bool.not(ab) == True{} : Bool} =
            Logic.Proof.and_true_l(Bool.not(ab),
              Arr.Arr.word_zero_from(0n, mp, at), ha)
          +ta : {Arr.Arr.word_zero_from(0n, mp, at) == True{} : Bool} =
            Logic.Proof.and_true_r(Bool.not(ab),
              Arr.Arr.word_zero_from(0n, mp, at), ha)
          +nb : {Bool.not(bb) == True{} : Bool} =
            Logic.Proof.and_true_l(Bool.not(bb),
              Arr.Arr.word_zero_from(0n, mp, bt), hb)
          +tb : {Arr.Arr.word_zero_from(0n, mp, bt) == True{} : Bool} =
            Logic.Proof.and_true_r(Bool.not(bb),
              Arr.Arr.word_zero_from(0n, mp, bt), hb)
          +nh : {Bool.not(Bool.or(ab, bb)) == True{} : Bool} =
            Equal.trans(Bool, Bool.not(Bool.or(ab, bb)),
              Bool.and(Bool.not(ab), Bool.not(bb)), True{},
              FF5.bool_not_or(ab, bb),
              FF5.bool_and_true_intro(Bool.not(ab), Bool.not(bb), na, nb))
          FF5.bool_and_true_intro(Bool.not(Bool.or(ab, bb)),
            Arr.Arr.word_zero_from(0n, mp, Word.or(mp, at, bt)),
            nh, FF5.word_or_zero_from(0n, mp, at, bt, ta, tb))
    case 1n++kp 1n++mp:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          FF5.word_or_zero_from(kp, mp, at, bt, ha, hb)

def FF5.u32_or_zero_l(+u: U32) -> {U32.or(0, u) == u : U32}:
  match u:
    case U32{+w}:
      Equal.cong(Word(32n), U32, x => U32{x},
        Word.or(32n, Word.zero(32n), w), w, FF5.word_or_zero_l(32n, w))

def FF5.u32_or_zero_r(+u: U32) -> {U32.or(u, 0) == u : U32}:
  match u:
    case U32{+w}:
      Equal.cong(Word(32n), U32, x => U32{x},
        Word.or(32n, w, Word.zero(32n)), w, FF5.word_or_zero_r(32n, w))

def FF5.u32_or_assoc(+a: U32, +b: U32, +c: U32) ->
  {U32.or(U32.or(a, b), c) == U32.or(a, U32.or(b, c)) : U32}:
  match a b c:
    case U32{+wa} U32{+wb} U32{+wc}:
      Equal.cong(Word(32n), U32, x => U32{x},
        Word.or(32n, Word.or(32n, wa, wb), wc),
        Word.or(32n, wa, Word.or(32n, wb, wc)),
        FF5.word_or_assoc(32n, wa, wb, wc))

def FF5.u32_and_or_distrib(+a: U32, +b: U32, +c: U32) ->
  {U32.and(U32.or(a, b), c) == U32.or(U32.and(a, c), U32.and(b, c)) : U32}:
  match a b c:
    case U32{+wa} U32{+wb} U32{+wc}:
      Equal.cong(Word(32n), U32, x => U32{x},
        Word.and(32n, Word.or(32n, wa, wb), wc),
        Word.or(32n, Word.and(32n, wa, wc), Word.and(32n, wb, wc)),
        FF5.word_and_or_distrib(32n, wa, wb, wc))

def FF5.u32_or_zero_from(+k: Nat, +a: U32, +b: U32,
    +ha: {Arr.Arr.u32_zero_from(k, a) == True{} : Bool},
    +hb: {Arr.Arr.u32_zero_from(k, b) == True{} : Bool}) ->
  {Arr.Arr.u32_zero_from(k, U32.or(a, b)) == True{} : Bool}:
  match a b:
    case U32{+wa} U32{+wb}:
      FF5.word_or_zero_from(k, 32n, wa, wb, ha, hb)

# ---------------------------------------------------------------------------
# 10-bit bounds, round-trip `decode_fb5(encode_fb5(...))`, and injectivity
# ---------------------------------------------------------------------------

def FF5.col_zero_from_10(c: Feedback.Color, +y: U32, +g: U32,
    +hy: {Arr.Arr.u32_zero_from(10n, y) == True{} : Bool},
    +hg: {Arr.Arr.u32_zero_from(10n, g) == True{} : Bool}) ->
  {Arr.Arr.u32_zero_from(10n, SolveFast.col_u32(c, y, g)) == True{} : Bool}:
  match c:
    case Feedback.Gray{}:
      {==}
    case Feedback.Yellow{}:
      hy
    case Feedback.Green{}:
      hg

def FF5.encode_fb5_zero_from(+c0: Feedback.Color, +c1: Feedback.Color,
    +c2: Feedback.Color, +c3: Feedback.Color, +c4: Feedback.Color) ->
  {Arr.Arr.u32_zero_from(10n, SolveFast.encode_fb5(c0, c1, c2, c3, c4))
   == True{} : Bool}:
  +z0 = FF5.col_zero_from_10(c0, 1, 2, {==}, {==})
  +z1 = FF5.col_zero_from_10(c1, 4, 8, {==}, {==})
  +z2 = FF5.col_zero_from_10(c2, 16, 32, {==}, {==})
  +z3 = FF5.col_zero_from_10(c3, 64, 128, {==}, {==})
  +z4 = FF5.col_zero_from_10(c4, 256, 512, {==}, {==})
  +z34 = FF5.u32_or_zero_from(10n,
           SolveFast.col_u32(c3, 64, 128), SolveFast.col_u32(c4, 256, 512),
           z3, z4)
  +z234 = FF5.u32_or_zero_from(10n,
            SolveFast.col_u32(c2, 16, 32),
            U32.or(SolveFast.col_u32(c3, 64, 128),
                   SolveFast.col_u32(c4, 256, 512)),
            z2, z34)
  +z1234 = FF5.u32_or_zero_from(10n,
             SolveFast.col_u32(c1, 4, 8),
             U32.or(SolveFast.col_u32(c2, 16, 32),
               U32.or(SolveFast.col_u32(c3, 64, 128),
                      SolveFast.col_u32(c4, 256, 512))),
             z1, z234)
  FF5.u32_or_zero_from(10n,
    SolveFast.col_u32(c0, 1, 2),
    U32.or(SolveFast.col_u32(c1, 4, 8),
      U32.or(SolveFast.col_u32(c2, 16, 32),
        U32.or(SolveFast.col_u32(c3, 64, 128),
               SolveFast.col_u32(c4, 256, 512)))),
    z0, z1234)

# Helper: masking an OR of two disjoint bitfields cancels the zeroed side.
def FF5.and_or_l_zero(+a: U32, +b: U32, +m: U32,
    +ha: {U32.and(a, m) == 0 : U32}) ->
  {U32.and(U32.or(a, b), m) == U32.and(b, m) : U32}:
  Equal.trans(U32,
    U32.and(U32.or(a, b), m),
    U32.or(U32.and(a, m), U32.and(b, m)),
    U32.and(b, m),
    FF5.u32_and_or_distrib(a, b, m),
    Equal.trans(U32,
      U32.or(U32.and(a, m), U32.and(b, m)),
      U32.or(0, U32.and(b, m)),
      U32.and(b, m),
      Equal.cong(U32, U32, x => U32.or(x, U32.and(b, m)),
        U32.and(a, m), 0, ha),
      FF5.u32_or_zero_l(U32.and(b, m))))

def FF5.and_or_r_zero(+a: U32, +b: U32, +m: U32,
    +hb: {U32.and(b, m) == 0 : U32}) ->
  {U32.and(U32.or(a, b), m) == U32.and(a, m) : U32}:
  Equal.trans(U32,
    U32.and(U32.or(a, b), m),
    U32.or(U32.and(a, m), U32.and(b, m)),
    U32.and(a, m),
    FF5.u32_and_or_distrib(a, b, m),
    Equal.trans(U32,
      U32.or(U32.and(a, m), U32.and(b, m)),
      U32.or(U32.and(a, m), 0),
      U32.and(a, m),
      Equal.cong(U32, U32, x => U32.or(U32.and(a, m), x),
        U32.and(b, m), 0, hb),
      FF5.u32_or_zero_r(U32.and(a, m))))

def FF5.and_or_both_zero(+a: U32, +b: U32, +m: U32,
    +ha: {U32.and(a, m) == 0 : U32}, +hb: {U32.and(b, m) == 0 : U32}) ->
  {U32.and(U32.or(a, b), m) == 0 : U32}:
  Equal.trans(U32, U32.and(U32.or(a, b), m), U32.and(b, m), 0,
    FF5.and_or_l_zero(a, b, m, ha), hb)

def FF5.word_and_zero_l(+m: Nat, +w: Word(m)) ->
  {Word.and(m, Word.zero(m), w) == Word.zero(m) : Word(m)}:
  match m:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++mp:
      match w:
        case WCon{+b, +t}:
          Equal.cong(Word(mp), Word(1n+mp), x => WCon{False{}, x},
            Word.and(mp, Word.zero(mp), t), Word.zero(mp),
            FF5.word_and_zero_l(mp, t))

def FF5.u32_and_zero_l(+u: U32) -> {U32.and(0, u) == 0 : U32}:
  match u:
    case U32{+w}:
      Equal.cong(Word(32n), U32, x => U32{x},
        Word.and(32n, Word.zero(32n), w), Word.zero(32n),
        FF5.word_and_zero_l(32n, w))

def FF5.col_and_zero(c: Feedback.Color, +y: U32, +g: U32, +m: U32,
    +hy: {U32.and(y, m) == 0 : U32}, +hg: {U32.and(g, m) == 0 : U32}) ->
  {U32.and(SolveFast.col_u32(c, y, g), m) == 0 : U32}:
  match c:
    case Feedback.Gray{}:
      FF5.u32_and_zero_l(m)
    case Feedback.Yellow{}:
      hy
    case Feedback.Green{}:
      hg

def FF5.decode_slot_g_eq(is_g: Bool, +u: U32, +v: U32, +ym: U32,
    +ey: {U32.and(u, ym) == U32.and(v, ym) : U32}) ->
  {SolveFast.decode_slot_g(is_g, u, ym) == SolveFast.decode_slot_g(is_g, v, ym)
   : Feedback.Color}:
  match is_g:
    case True{}:
      {==}
    case False{}:
      Equal.cong(U32, Feedback.Color,
        x => SolveFast.decode_slot_y(U32.is_eq(x, ym)),
        U32.and(u, ym), U32.and(v, ym), ey)

def FF5.decode_slot_eq(+u: U32, +v: U32, +gm: U32, +ym: U32,
    +eg: {U32.and(u, gm) == U32.and(v, gm) : U32},
    +ey: {U32.and(u, ym) == U32.and(v, ym) : U32}) ->
  {SolveFast.decode_slot(u, gm, ym) == SolveFast.decode_slot(v, gm, ym)
   : Feedback.Color}:
  +e1 : {SolveFast.decode_slot_g(U32.is_eq(U32.and(u, gm), gm), u, ym)
         == SolveFast.decode_slot_g(U32.is_eq(U32.and(v, gm), gm), u, ym)
         : Feedback.Color} =
    Equal.cong(U32, Feedback.Color,
      x => SolveFast.decode_slot_g(U32.is_eq(x, gm), u, ym),
      U32.and(u, gm), U32.and(v, gm), eg)
  +e2 : {SolveFast.decode_slot_g(U32.is_eq(U32.and(v, gm), gm), u, ym)
         == SolveFast.decode_slot_g(U32.is_eq(U32.and(v, gm), gm), v, ym)
         : Feedback.Color} =
    FF5.decode_slot_g_eq(U32.is_eq(U32.and(v, gm), gm), u, v, ym, ey)
  Equal.trans(Feedback.Color,
    SolveFast.decode_slot(u, gm, ym),
    SolveFast.decode_slot_g(U32.is_eq(U32.and(v, gm), gm), u, ym),
    SolveFast.decode_slot(v, gm, ym),
    e1, e2)

def FF5.decode_col_self(c: Feedback.Color, +y: U32, +g: U32,
    +eg0: {SolveFast.decode_slot(0, g, y) == Feedback.Gray{} : Feedback.Color},
    +egy: {SolveFast.decode_slot(y, g, y) == Feedback.Yellow{} : Feedback.Color},
    +egg: {SolveFast.decode_slot(g, g, y) == Feedback.Green{} : Feedback.Color}) ->
  {SolveFast.decode_slot(SolveFast.col_u32(c, y, g), g, y) == c
   : Feedback.Color}:
  match c:
    case Feedback.Gray{}:
      eg0
    case Feedback.Yellow{}:
      egy
    case Feedback.Green{}:
      egg

# Extract each of the 5 color slots from `encode_fb5(c0, c1, c2, c3, c4)`.
def FF5.encode_and_slot0(+c0: Feedback.Color, +c1: Feedback.Color,
    +c2: Feedback.Color, +c3: Feedback.Color, +c4: Feedback.Color, +m: U32,
    +h1y: {U32.and(4, m) == 0 : U32}, +h1g: {U32.and(8, m) == 0 : U32},
    +h2y: {U32.and(16, m) == 0 : U32}, +h2g: {U32.and(32, m) == 0 : U32},
    +h3y: {U32.and(64, m) == 0 : U32}, +h3g: {U32.and(128, m) == 0 : U32},
    +h4y: {U32.and(256, m) == 0 : U32}, +h4g: {U32.and(512, m) == 0 : U32}) ->
  {U32.and(SolveFast.encode_fb5(c0, c1, c2, c3, c4), m)
   == U32.and(SolveFast.col_u32(c0, 1, 2), m) : U32}:
  +z1 = FF5.col_and_zero(c1, 4, 8, m, h1y, h1g)
  +z2 = FF5.col_and_zero(c2, 16, 32, m, h2y, h2g)
  +z3 = FF5.col_and_zero(c3, 64, 128, m, h3y, h3g)
  +z4 = FF5.col_and_zero(c4, 256, 512, m, h4y, h4g)
  +z34 = FF5.and_or_both_zero(SolveFast.col_u32(c3, 64, 128),
           SolveFast.col_u32(c4, 256, 512), m, z3, z4)
  +z234 = FF5.and_or_both_zero(SolveFast.col_u32(c2, 16, 32),
            U32.or(SolveFast.col_u32(c3, 64, 128),
                   SolveFast.col_u32(c4, 256, 512)), m, z2, z34)
  +z1234 = FF5.and_or_both_zero(SolveFast.col_u32(c1, 4, 8),
             U32.or(SolveFast.col_u32(c2, 16, 32),
               U32.or(SolveFast.col_u32(c3, 64, 128),
                      SolveFast.col_u32(c4, 256, 512))), m, z1, z234)
  FF5.and_or_r_zero(SolveFast.col_u32(c0, 1, 2),
    U32.or(SolveFast.col_u32(c1, 4, 8),
      U32.or(SolveFast.col_u32(c2, 16, 32),
        U32.or(SolveFast.col_u32(c3, 64, 128),
               SolveFast.col_u32(c4, 256, 512)))), m, z1234)

def FF5.encode_and_slot1(+c0: Feedback.Color, +c1: Feedback.Color,
    +c2: Feedback.Color, +c3: Feedback.Color, +c4: Feedback.Color, +m: U32,
    +h0y: {U32.and(1, m) == 0 : U32}, +h0g: {U32.and(2, m) == 0 : U32},
    +h2y: {U32.and(16, m) == 0 : U32}, +h2g: {U32.and(32, m) == 0 : U32},
    +h3y: {U32.and(64, m) == 0 : U32}, +h3g: {U32.and(128, m) == 0 : U32},
    +h4y: {U32.and(256, m) == 0 : U32}, +h4g: {U32.and(512, m) == 0 : U32}) ->
  {U32.and(SolveFast.encode_fb5(c0, c1, c2, c3, c4), m)
   == U32.and(SolveFast.col_u32(c1, 4, 8), m) : U32}:
  +z0 = FF5.col_and_zero(c0, 1, 2, m, h0y, h0g)
  +z2 = FF5.col_and_zero(c2, 16, 32, m, h2y, h2g)
  +z3 = FF5.col_and_zero(c3, 64, 128, m, h3y, h3g)
  +z4 = FF5.col_and_zero(c4, 256, 512, m, h4y, h4g)
  +z34 = FF5.and_or_both_zero(SolveFast.col_u32(c3, 64, 128),
           SolveFast.col_u32(c4, 256, 512), m, z3, z4)
  +z234 = FF5.and_or_both_zero(SolveFast.col_u32(c2, 16, 32),
            U32.or(SolveFast.col_u32(c3, 64, 128),
                   SolveFast.col_u32(c4, 256, 512)), m, z2, z34)
  +r1 = U32.or(SolveFast.col_u32(c1, 4, 8),
          U32.or(SolveFast.col_u32(c2, 16, 32),
            U32.or(SolveFast.col_u32(c3, 64, 128),
                   SolveFast.col_u32(c4, 256, 512))))
  Equal.trans(U32,
    U32.and(U32.or(SolveFast.col_u32(c0, 1, 2), r1), m),
    U32.and(r1, m),
    U32.and(SolveFast.col_u32(c1, 4, 8), m),
    FF5.and_or_l_zero(SolveFast.col_u32(c0, 1, 2), r1, m, z0),
    FF5.and_or_r_zero(SolveFast.col_u32(c1, 4, 8),
      U32.or(SolveFast.col_u32(c2, 16, 32),
        U32.or(SolveFast.col_u32(c3, 64, 128),
               SolveFast.col_u32(c4, 256, 512))), m, z234))

def FF5.encode_and_slot2(+c0: Feedback.Color, +c1: Feedback.Color,
    +c2: Feedback.Color, +c3: Feedback.Color, +c4: Feedback.Color, +m: U32,
    +h0y: {U32.and(1, m) == 0 : U32}, +h0g: {U32.and(2, m) == 0 : U32},
    +h1y: {U32.and(4, m) == 0 : U32}, +h1g: {U32.and(8, m) == 0 : U32},
    +h3y: {U32.and(64, m) == 0 : U32}, +h3g: {U32.and(128, m) == 0 : U32},
    +h4y: {U32.and(256, m) == 0 : U32}, +h4g: {U32.and(512, m) == 0 : U32}) ->
  {U32.and(SolveFast.encode_fb5(c0, c1, c2, c3, c4), m)
   == U32.and(SolveFast.col_u32(c2, 16, 32), m) : U32}:
  +z0 = FF5.col_and_zero(c0, 1, 2, m, h0y, h0g)
  +z1 = FF5.col_and_zero(c1, 4, 8, m, h1y, h1g)
  +z3 = FF5.col_and_zero(c3, 64, 128, m, h3y, h3g)
  +z4 = FF5.col_and_zero(c4, 256, 512, m, h4y, h4g)
  +z34 = FF5.and_or_both_zero(SolveFast.col_u32(c3, 64, 128),
           SolveFast.col_u32(c4, 256, 512), m, z3, z4)
  +r2 = U32.or(SolveFast.col_u32(c2, 16, 32),
          U32.or(SolveFast.col_u32(c3, 64, 128),
                 SolveFast.col_u32(c4, 256, 512)))
  +r1 = U32.or(SolveFast.col_u32(c1, 4, 8), r2)
  Equal.trans(U32,
    U32.and(U32.or(SolveFast.col_u32(c0, 1, 2), r1), m),
    U32.and(r1, m),
    U32.and(SolveFast.col_u32(c2, 16, 32), m),
    FF5.and_or_l_zero(SolveFast.col_u32(c0, 1, 2), r1, m, z0),
    Equal.trans(U32,
      U32.and(r1, m),
      U32.and(r2, m),
      U32.and(SolveFast.col_u32(c2, 16, 32), m),
      FF5.and_or_l_zero(SolveFast.col_u32(c1, 4, 8), r2, m, z1),
      FF5.and_or_r_zero(SolveFast.col_u32(c2, 16, 32),
        U32.or(SolveFast.col_u32(c3, 64, 128),
               SolveFast.col_u32(c4, 256, 512)), m, z34)))

def FF5.encode_and_slot3(+c0: Feedback.Color, +c1: Feedback.Color,
    +c2: Feedback.Color, +c3: Feedback.Color, +c4: Feedback.Color, +m: U32,
    +h0y: {U32.and(1, m) == 0 : U32}, +h0g: {U32.and(2, m) == 0 : U32},
    +h1y: {U32.and(4, m) == 0 : U32}, +h1g: {U32.and(8, m) == 0 : U32},
    +h2y: {U32.and(16, m) == 0 : U32}, +h2g: {U32.and(32, m) == 0 : U32},
    +h4y: {U32.and(256, m) == 0 : U32}, +h4g: {U32.and(512, m) == 0 : U32}) ->
  {U32.and(SolveFast.encode_fb5(c0, c1, c2, c3, c4), m)
   == U32.and(SolveFast.col_u32(c3, 64, 128), m) : U32}:
  +z0 = FF5.col_and_zero(c0, 1, 2, m, h0y, h0g)
  +z1 = FF5.col_and_zero(c1, 4, 8, m, h1y, h1g)
  +z2 = FF5.col_and_zero(c2, 16, 32, m, h2y, h2g)
  +z4 = FF5.col_and_zero(c4, 256, 512, m, h4y, h4g)
  +r3 = U32.or(SolveFast.col_u32(c3, 64, 128), SolveFast.col_u32(c4, 256, 512))
  +r2 = U32.or(SolveFast.col_u32(c2, 16, 32), r3)
  +r1 = U32.or(SolveFast.col_u32(c1, 4, 8), r2)
  Equal.trans(U32,
    U32.and(U32.or(SolveFast.col_u32(c0, 1, 2), r1), m),
    U32.and(r1, m),
    U32.and(SolveFast.col_u32(c3, 64, 128), m),
    FF5.and_or_l_zero(SolveFast.col_u32(c0, 1, 2), r1, m, z0),
    Equal.trans(U32,
      U32.and(r1, m),
      U32.and(r2, m),
      U32.and(SolveFast.col_u32(c3, 64, 128), m),
      FF5.and_or_l_zero(SolveFast.col_u32(c1, 4, 8), r2, m, z1),
      Equal.trans(U32,
        U32.and(r2, m),
        U32.and(r3, m),
        U32.and(SolveFast.col_u32(c3, 64, 128), m),
        FF5.and_or_l_zero(SolveFast.col_u32(c2, 16, 32), r3, m, z2),
        FF5.and_or_r_zero(SolveFast.col_u32(c3, 64, 128),
          SolveFast.col_u32(c4, 256, 512), m, z4))))

def FF5.encode_and_slot4(+c0: Feedback.Color, +c1: Feedback.Color,
    +c2: Feedback.Color, +c3: Feedback.Color, +c4: Feedback.Color, +m: U32,
    +h0y: {U32.and(1, m) == 0 : U32}, +h0g: {U32.and(2, m) == 0 : U32},
    +h1y: {U32.and(4, m) == 0 : U32}, +h1g: {U32.and(8, m) == 0 : U32},
    +h2y: {U32.and(16, m) == 0 : U32}, +h2g: {U32.and(32, m) == 0 : U32},
    +h3y: {U32.and(64, m) == 0 : U32}, +h3g: {U32.and(128, m) == 0 : U32}) ->
  {U32.and(SolveFast.encode_fb5(c0, c1, c2, c3, c4), m)
   == U32.and(SolveFast.col_u32(c4, 256, 512), m) : U32}:
  +z0 = FF5.col_and_zero(c0, 1, 2, m, h0y, h0g)
  +z1 = FF5.col_and_zero(c1, 4, 8, m, h1y, h1g)
  +z2 = FF5.col_and_zero(c2, 16, 32, m, h2y, h2g)
  +z3 = FF5.col_and_zero(c3, 64, 128, m, h3y, h3g)
  +r3 = U32.or(SolveFast.col_u32(c3, 64, 128), SolveFast.col_u32(c4, 256, 512))
  +r2 = U32.or(SolveFast.col_u32(c2, 16, 32), r3)
  +r1 = U32.or(SolveFast.col_u32(c1, 4, 8), r2)
  Equal.trans(U32,
    U32.and(U32.or(SolveFast.col_u32(c0, 1, 2), r1), m),
    U32.and(r1, m),
    U32.and(SolveFast.col_u32(c4, 256, 512), m),
    FF5.and_or_l_zero(SolveFast.col_u32(c0, 1, 2), r1, m, z0),
    Equal.trans(U32,
      U32.and(r1, m),
      U32.and(r2, m),
      U32.and(SolveFast.col_u32(c4, 256, 512), m),
      FF5.and_or_l_zero(SolveFast.col_u32(c1, 4, 8), r2, m, z1),
      Equal.trans(U32,
        U32.and(r2, m),
        U32.and(r3, m),
        U32.and(SolveFast.col_u32(c4, 256, 512), m),
        FF5.and_or_l_zero(SolveFast.col_u32(c2, 16, 32), r3, m, z2),
        FF5.and_or_l_zero(SolveFast.col_u32(c3, 64, 128),
          SolveFast.col_u32(c4, 256, 512), m, z3))))

def FF5.decode_encode(+c0: Feedback.Color, +c1: Feedback.Color,
    +c2: Feedback.Color, +c3: Feedback.Color, +c4: Feedback.Color) ->
  {SolveFast.decode_fb5(SolveFast.encode_fb5(c0, c1, c2, c3, c4))
   == c0 <> (c1 <> (c2 <> (c3 <> (c4 <> Nil{}))))
   : +List<Feedback.Color>}:
  +u : U32 = SolveFast.encode_fb5(c0, c1, c2, c3, c4)
  +e0 : {SolveFast.decode_slot(u, 2, 1) == c0 : Feedback.Color} =
    Equal.trans(Feedback.Color,
      SolveFast.decode_slot(u, 2, 1),
      SolveFast.decode_slot(SolveFast.col_u32(c0, 1, 2), 2, 1),
      c0,
      FF5.decode_slot_eq(u, SolveFast.col_u32(c0, 1, 2), 2, 1,
        FF5.encode_and_slot0(c0, c1, c2, c3, c4, 2,
          {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
        FF5.encode_and_slot0(c0, c1, c2, c3, c4, 1,
          {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})),
      FF5.decode_col_self(c0, 1, 2, {==}, {==}, {==}))
  +e1 : {SolveFast.decode_slot(u, 8, 4) == c1 : Feedback.Color} =
    Equal.trans(Feedback.Color,
      SolveFast.decode_slot(u, 8, 4),
      SolveFast.decode_slot(SolveFast.col_u32(c1, 4, 8), 8, 4),
      c1,
      FF5.decode_slot_eq(u, SolveFast.col_u32(c1, 4, 8), 8, 4,
        FF5.encode_and_slot1(c0, c1, c2, c3, c4, 8,
          {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
        FF5.encode_and_slot1(c0, c1, c2, c3, c4, 4,
          {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})),
      FF5.decode_col_self(c1, 4, 8, {==}, {==}, {==}))
  +e2 : {SolveFast.decode_slot(u, 32, 16) == c2 : Feedback.Color} =
    Equal.trans(Feedback.Color,
      SolveFast.decode_slot(u, 32, 16),
      SolveFast.decode_slot(SolveFast.col_u32(c2, 16, 32), 32, 16),
      c2,
      FF5.decode_slot_eq(u, SolveFast.col_u32(c2, 16, 32), 32, 16,
        FF5.encode_and_slot2(c0, c1, c2, c3, c4, 32,
          {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
        FF5.encode_and_slot2(c0, c1, c2, c3, c4, 16,
          {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})),
      FF5.decode_col_self(c2, 16, 32, {==}, {==}, {==}))
  +e3 : {SolveFast.decode_slot(u, 128, 64) == c3 : Feedback.Color} =
    Equal.trans(Feedback.Color,
      SolveFast.decode_slot(u, 128, 64),
      SolveFast.decode_slot(SolveFast.col_u32(c3, 64, 128), 128, 64),
      c3,
      FF5.decode_slot_eq(u, SolveFast.col_u32(c3, 64, 128), 128, 64,
        FF5.encode_and_slot3(c0, c1, c2, c3, c4, 128,
          {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
        FF5.encode_and_slot3(c0, c1, c2, c3, c4, 64,
          {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})),
      FF5.decode_col_self(c3, 64, 128, {==}, {==}, {==}))
  +e4 : {SolveFast.decode_slot(u, 512, 256) == c4 : Feedback.Color} =
    Equal.trans(Feedback.Color,
      SolveFast.decode_slot(u, 512, 256),
      SolveFast.decode_slot(SolveFast.col_u32(c4, 256, 512), 512, 256),
      c4,
      FF5.decode_slot_eq(u, SolveFast.col_u32(c4, 256, 512), 512, 256,
        FF5.encode_and_slot4(c0, c1, c2, c3, c4, 512,
          {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}),
        FF5.encode_and_slot4(c0, c1, c2, c3, c4, 256,
          {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})),
      FF5.decode_col_self(c4, 256, 512, {==}, {==}, {==}))
  %e0 : {SolveFast.decode_slot(u, 2, 1)
         <> (SolveFast.decode_slot(u, 8, 4)
         <> (SolveFast.decode_slot(u, 32, 16)
         <> (SolveFast.decode_slot(u, 128, 64)
         <> (SolveFast.decode_slot(u, 512, 256) <> Nil{}))))
         == _ <> (c1 <> (c2 <> (c3 <> (c4 <> Nil{}))))
         : +List<Feedback.Color>}
  %e1 : {SolveFast.decode_slot(u, 2, 1)
         <> (SolveFast.decode_slot(u, 8, 4)
         <> (SolveFast.decode_slot(u, 32, 16)
         <> (SolveFast.decode_slot(u, 128, 64)
         <> (SolveFast.decode_slot(u, 512, 256) <> Nil{}))))
         == SolveFast.decode_slot(u, 2, 1)
         <> (_ <> (c2 <> (c3 <> (c4 <> Nil{}))))
         : +List<Feedback.Color>}
  %e2 : {SolveFast.decode_slot(u, 2, 1)
         <> (SolveFast.decode_slot(u, 8, 4)
         <> (SolveFast.decode_slot(u, 32, 16)
         <> (SolveFast.decode_slot(u, 128, 64)
         <> (SolveFast.decode_slot(u, 512, 256) <> Nil{}))))
         == SolveFast.decode_slot(u, 2, 1)
         <> (SolveFast.decode_slot(u, 8, 4)
         <> (_ <> (c3 <> (c4 <> Nil{}))))
         : +List<Feedback.Color>}
  %e3 : {SolveFast.decode_slot(u, 2, 1)
         <> (SolveFast.decode_slot(u, 8, 4)
         <> (SolveFast.decode_slot(u, 32, 16)
         <> (SolveFast.decode_slot(u, 128, 64)
         <> (SolveFast.decode_slot(u, 512, 256) <> Nil{}))))
         == SolveFast.decode_slot(u, 2, 1)
         <> (SolveFast.decode_slot(u, 8, 4)
         <> (SolveFast.decode_slot(u, 32, 16)
         <> (_ <> (c4 <> Nil{}))))
         : +List<Feedback.Color>}
  %e4 : {SolveFast.decode_slot(u, 2, 1)
         <> (SolveFast.decode_slot(u, 8, 4)
         <> (SolveFast.decode_slot(u, 32, 16)
         <> (SolveFast.decode_slot(u, 128, 64)
         <> (SolveFast.decode_slot(u, 512, 256) <> Nil{}))))
         == SolveFast.decode_slot(u, 2, 1)
         <> (SolveFast.decode_slot(u, 8, 4)
         <> (SolveFast.decode_slot(u, 32, 16)
         <> (SolveFast.decode_slot(u, 128, 64)
         <> (_ <> Nil{}))))
         : +List<Feedback.Color>}
  {==}

# List-level 5-color encoder and predicate.
def FF5.is_fb5(+fb: +List<Feedback.Color>) -> Bool:
  match fb:
    case Nil{}:
      False{}
    case Con{c0, t1}:
      match t1:
        case Nil{}:
          False{}
        case Con{c1, t2}:
          match t2:
            case Nil{}:
              False{}
            case Con{c2, t3}:
              match t3:
                case Nil{}:
                  False{}
                case Con{c3, t4}:
                  match t4:
                    case Nil{}:
                      False{}
                    case Con{c4, t5}:
                      match t5:
                        case Nil{}:
                          True{}
                        case Con{c5, t6}:
                          False{}

def FF5.encode_fb5_list(+fb: +List<Feedback.Color>) -> U32:
  match fb:
    case Nil{}:
      0
    case Con{c0, t1}:
      match t1:
        case Nil{}:
          0
        case Con{c1, t2}:
          match t2:
            case Nil{}:
              0
            case Con{c2, t3}:
              match t3:
                case Nil{}:
                  0
                case Con{c3, t4}:
                  match t4:
                    case Nil{}:
                      0
                    case Con{c4, t5}:
                      match t5:
                        case Nil{}:
                          SolveFast.encode_fb5(c0, c1, c2, c3, c4)
                        case Con{c5, t6}:
                          0

def FF5.decode_encode_list(+fb: +List<Feedback.Color>,
    +h5: {FF5.is_fb5(fb) == True{} : Bool}) ->
  {SolveFast.decode_fb5(FF5.encode_fb5_list(fb)) == fb : +List<Feedback.Color>}:
  match fb:
    case Nil{}:
      Empty.absurd(
        {SolveFast.decode_fb5(FF5.encode_fb5_list(Nil{})) == Nil{}
         : +List<Feedback.Color>},
        Logic.Proof.false_ne_true(h5))
    case Con{+c0, +t1}:
      match t1:
        case Nil{}:
          Empty.absurd(
            {SolveFast.decode_fb5(FF5.encode_fb5_list(c0 <> Nil{}))
             == c0 <> Nil{} : +List<Feedback.Color>},
            Logic.Proof.false_ne_true(h5))
        case Con{+c1, +t2}:
          match t2:
            case Nil{}:
              Empty.absurd(
                {SolveFast.decode_fb5(FF5.encode_fb5_list(c0 <> (c1 <> Nil{})))
                 == c0 <> (c1 <> Nil{}) : +List<Feedback.Color>},
                Logic.Proof.false_ne_true(h5))
            case Con{+c2, +t3}:
              match t3:
                case Nil{}:
                  Empty.absurd(
                    {SolveFast.decode_fb5(
                       FF5.encode_fb5_list(c0 <> (c1 <> (c2 <> Nil{}))))
                     == c0 <> (c1 <> (c2 <> Nil{})) : +List<Feedback.Color>},
                    Logic.Proof.false_ne_true(h5))
                case Con{+c3, +t4}:
                  match t4:
                    case Nil{}:
                      Empty.absurd(
                        {SolveFast.decode_fb5(
                           FF5.encode_fb5_list(
                             c0 <> (c1 <> (c2 <> (c3 <> Nil{})))))
                         == c0 <> (c1 <> (c2 <> (c3 <> Nil{})))
                         : +List<Feedback.Color>},
                        Logic.Proof.false_ne_true(h5))
                    case Con{+c4, +t5}:
                      match t5:
                        case Nil{}:
                          FF5.decode_encode(c0, c1, c2, c3, c4)
                        case Con{+c5, +t6}:
                          Empty.absurd(
                            {SolveFast.decode_fb5(
                               FF5.encode_fb5_list(
                                 c0 <> (c1 <> (c2 <> (c3 <> (c4 <> (c5 <> t6)))))))
                             == c0 <> (c1 <> (c2 <> (c3 <> (c4 <> (c5 <> t6)))))
                             : +List<Feedback.Color>},
                            Logic.Proof.false_ne_true(h5))

def FF5.encode_fb5_list_zero_from(+fb: +List<Feedback.Color>,
    +h5: {FF5.is_fb5(fb) == True{} : Bool}) ->
  {Arr.Arr.u32_zero_from(10n, FF5.encode_fb5_list(fb)) == True{} : Bool}:
  match fb:
    case Nil{}:
      Empty.absurd(
        {Arr.Arr.u32_zero_from(10n, FF5.encode_fb5_list(Nil{})) == True{}
         : Bool},
        Logic.Proof.false_ne_true(h5))
    case Con{+c0, +t1}:
      match t1:
        case Nil{}:
          Empty.absurd(
            {Arr.Arr.u32_zero_from(10n, FF5.encode_fb5_list(c0 <> Nil{}))
             == True{} : Bool},
            Logic.Proof.false_ne_true(h5))
        case Con{+c1, +t2}:
          match t2:
            case Nil{}:
              Empty.absurd(
                {Arr.Arr.u32_zero_from(10n,
                   FF5.encode_fb5_list(c0 <> (c1 <> Nil{}))) == True{} : Bool},
                Logic.Proof.false_ne_true(h5))
            case Con{+c2, +t3}:
              match t3:
                case Nil{}:
                  Empty.absurd(
                    {Arr.Arr.u32_zero_from(10n,
                       FF5.encode_fb5_list(c0 <> (c1 <> (c2 <> Nil{}))))
                     == True{} : Bool},
                    Logic.Proof.false_ne_true(h5))
                case Con{+c3, +t4}:
                  match t4:
                    case Nil{}:
                      Empty.absurd(
                        {Arr.Arr.u32_zero_from(10n,
                           FF5.encode_fb5_list(
                             c0 <> (c1 <> (c2 <> (c3 <> Nil{})))))
                         == True{} : Bool},
                        Logic.Proof.false_ne_true(h5))
                    case Con{+c4, +t5}:
                      match t5:
                        case Nil{}:
                          FF5.encode_fb5_zero_from(c0, c1, c2, c3, c4)
                        case Con{+c5, +t6}:
                          Empty.absurd(
                            {Arr.Arr.u32_zero_from(10n,
                               FF5.encode_fb5_list(
                                 c0 <> (c1 <> (c2 <> (c3 <> (c4 <> (c5 <> t6)))))))
                             == True{} : Bool},
                            Logic.Proof.false_ne_true(h5))

# Reflection: `Feedback.feedback_eq(f1, f2) == True{}` iff `f1 == f2`.
def FF5.color_eq_true(a: Feedback.Color, b: Feedback.Color,
    +e: {Feedback.Color.eq(a, b) == True{} : Bool}) -> {a == b : Feedback.Color}:
  match a b:
    case Feedback.Gray{} Feedback.Gray{}:
      {==}
    case Feedback.Yellow{} Feedback.Yellow{}:
      {==}
    case Feedback.Green{} Feedback.Green{}:
      {==}
    case Feedback.Gray{} Feedback.Yellow{}:
      Empty.absurd({Feedback.Gray{} == Feedback.Yellow{} : Feedback.Color},
        Logic.Proof.false_ne_true(e))
    case Feedback.Gray{} Feedback.Green{}:
      Empty.absurd({Feedback.Gray{} == Feedback.Green{} : Feedback.Color},
        Logic.Proof.false_ne_true(e))
    case Feedback.Yellow{} Feedback.Gray{}:
      Empty.absurd({Feedback.Yellow{} == Feedback.Gray{} : Feedback.Color},
        Logic.Proof.false_ne_true(e))
    case Feedback.Yellow{} Feedback.Green{}:
      Empty.absurd({Feedback.Yellow{} == Feedback.Green{} : Feedback.Color},
        Logic.Proof.false_ne_true(e))
    case Feedback.Green{} Feedback.Gray{}:
      Empty.absurd({Feedback.Green{} == Feedback.Gray{} : Feedback.Color},
        Logic.Proof.false_ne_true(e))
    case Feedback.Green{} Feedback.Yellow{}:
      Empty.absurd({Feedback.Green{} == Feedback.Yellow{} : Feedback.Color},
        Logic.Proof.false_ne_true(e))

def FF5.fb_eq_go_true(+a: +List<Feedback.Color>, +b: +List<Feedback.Color>,
    same: Bool, +es: {same == SolveFast.next_fb_same(a, b) : Bool},
    +et: {SolveFast.feedback_eq_go(a, b, same) == True{} : Bool}) ->
  {a == b : +List<Feedback.Color>}:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          {==}
        case Con{+bh, +bt}:
          Empty.absurd({Nil{} == bh <> bt : +List<Feedback.Color>},
            Logic.Proof.false_ne_true(et))
    case Con{+ah, +at}:
      match b:
        case Nil{}:
          Empty.absurd({ah <> at == Nil{} : +List<Feedback.Color>},
            Logic.Proof.false_ne_true(et))
        case Con{+bh, +bt}:
          match same:
            case False{}:
              Empty.absurd({ah <> at == bh <> bt : +List<Feedback.Color>},
                Logic.Proof.false_ne_true(et))
            case True{}:
              +eh : {ah == bh : Feedback.Color} =
                FF5.color_eq_true(ah, bh,
                  Equal.sym(Bool, True{}, Feedback.Color.eq(ah, bh), es))
              +er : {at == bt : +List<Feedback.Color>} =
                FF5.fb_eq_go_true(at, bt, SolveFast.next_fb_same(at, bt),
                  {==}, et)
              %eh : {ah <> at == _ <> bt : +List<Feedback.Color>}
              %er : {ah <> at == ah <> _ : +List<Feedback.Color>}
              {==}

def FF5.feedback_eq_true(+a: +List<Feedback.Color>, +b: +List<Feedback.Color>,
    +et: {Feedback.feedback_eq(a, b) == True{} : Bool}) ->
  {a == b : +List<Feedback.Color>}:
  +ef : {SolveFast.feedback_eq_fast(a, b) == True{} : Bool} =
    Equal.trans(Bool, SolveFast.feedback_eq_fast(a, b),
      Feedback.feedback_eq(a, b), True{},
      FG.FG.feedback_eq_fast_eq(a, b), et)
  FF5.fb_eq_go_true(a, b, SolveFast.next_fb_same(a, b), {==}, ef)

def FF5.code_eq_iff_fb_eq_go(+f1: +List<Feedback.Color>,
    +f2: +List<Feedback.Color>,
    +h1: {FF5.is_fb5(f1) == True{} : Bool},
    +h2: {FF5.is_fb5(f2) == True{} : Bool},
    b1: Bool, +eb1: {b1 == U32.is_eq(FF5.encode_fb5_list(f1),
                              FF5.encode_fb5_list(f2)) : Bool},
    b2: Bool, +eb2: {b2 == Feedback.feedback_eq(f1, f2) : Bool}) ->
  {U32.is_eq(FF5.encode_fb5_list(f1), FF5.encode_fb5_list(f2))
   == Feedback.feedback_eq(f1, f2) : Bool}:
  match b1 b2:
    case True{} True{}:
      Equal.trans(Bool,
        U32.is_eq(FF5.encode_fb5_list(f1), FF5.encode_fb5_list(f2)),
        True{}, Feedback.feedback_eq(f1, f2),
        Equal.sym(Bool, True{},
          U32.is_eq(FF5.encode_fb5_list(f1), FF5.encode_fb5_list(f2)), eb1),
        eb2)
    case False{} False{}:
      Equal.trans(Bool,
        U32.is_eq(FF5.encode_fb5_list(f1), FF5.encode_fb5_list(f2)),
        False{}, Feedback.feedback_eq(f1, f2),
        Equal.sym(Bool, False{},
          U32.is_eq(FF5.encode_fb5_list(f1), FF5.encode_fb5_list(f2)), eb1),
        eb2)
    case True{} False{}:
      +ec : {FF5.encode_fb5_list(f1) == FF5.encode_fb5_list(f2) : U32} =
        Arr.Arr.u32_is_eq_true(FF5.encode_fb5_list(f1), FF5.encode_fb5_list(f2),
          Equal.sym(Bool, True{},
            U32.is_eq(FF5.encode_fb5_list(f1), FF5.encode_fb5_list(f2)), eb1))
      +ef : {f1 == f2 : +List<Feedback.Color>} =
        Equal.trans(+List<Feedback.Color>, f1,
          SolveFast.decode_fb5(FF5.encode_fb5_list(f1)), f2,
          Equal.sym(+List<Feedback.Color>,
            SolveFast.decode_fb5(FF5.encode_fb5_list(f1)), f1,
            FF5.decode_encode_list(f1, h1)),
          Equal.trans(+List<Feedback.Color>,
            SolveFast.decode_fb5(FF5.encode_fb5_list(f1)),
            SolveFast.decode_fb5(FF5.encode_fb5_list(f2)), f2,
            Equal.cong(U32, +List<Feedback.Color>, u => SolveFast.decode_fb5(u),
              FF5.encode_fb5_list(f1), FF5.encode_fb5_list(f2), ec),
            FF5.decode_encode_list(f2, h2)))
      +ert : {Feedback.feedback_eq(f1, f2) == True{} : Bool} =
        Equal.trans(Bool, Feedback.feedback_eq(f1, f2),
          Feedback.feedback_eq(f1, f1), True{},
          Equal.cong(+List<Feedback.Color>, Bool,
            x => Feedback.feedback_eq(f1, x), f2, f1,
            Equal.sym(+List<Feedback.Color>, f1, f2, ef)),
          FbProof.FbPrf.feedback_eq_refl(f1))
      Empty.absurd(
        {U32.is_eq(FF5.encode_fb5_list(f1), FF5.encode_fb5_list(f2))
         == Feedback.feedback_eq(f1, f2) : Bool},
        Logic.Proof.false_ne_true(
          Equal.trans(Bool, False{}, Feedback.feedback_eq(f1, f2), True{},
            eb2, ert)))
    case False{} True{}:
      +ef : {f1 == f2 : +List<Feedback.Color>} =
        FF5.feedback_eq_true(f1, f2,
          Equal.sym(Bool, True{}, Feedback.feedback_eq(f1, f2), eb2))
      +ect : {U32.is_eq(FF5.encode_fb5_list(f1), FF5.encode_fb5_list(f2))
              == True{} : Bool} =
        Equal.trans(Bool,
          U32.is_eq(FF5.encode_fb5_list(f1), FF5.encode_fb5_list(f2)),
          U32.is_eq(FF5.encode_fb5_list(f1), FF5.encode_fb5_list(f1)),
          True{},
          Equal.cong(+List<Feedback.Color>, Bool,
            x => U32.is_eq(FF5.encode_fb5_list(f1), FF5.encode_fb5_list(x)),
            f2, f1, Equal.sym(+List<Feedback.Color>, f1, f2, ef)),
          Arr.Arr.u32_is_eq_refl(FF5.encode_fb5_list(f1)))
      Empty.absurd(
        {U32.is_eq(FF5.encode_fb5_list(f1), FF5.encode_fb5_list(f2))
         == Feedback.feedback_eq(f1, f2) : Bool},
        Logic.Proof.false_ne_true(
          Equal.trans(Bool, False{},
            U32.is_eq(FF5.encode_fb5_list(f1), FF5.encode_fb5_list(f2)),
            True{}, eb1, ect)))

def FF5.code_eq_iff_fb_eq(+f1: +List<Feedback.Color>,
    +f2: +List<Feedback.Color>,
    +h1: {FF5.is_fb5(f1) == True{} : Bool},
    +h2: {FF5.is_fb5(f2) == True{} : Bool}) ->
  {U32.is_eq(FF5.encode_fb5_list(f1), FF5.encode_fb5_list(f2))
   == Feedback.feedback_eq(f1, f2) : Bool}:
  FF5.code_eq_iff_fb_eq_go(f1, f2, h1, h2,
    U32.is_eq(FF5.encode_fb5_list(f1), FF5.encode_fb5_list(f2)), {==},
    Feedback.feedback_eq(f1, f2), {==})

# ---------------------------------------------------------------------------
# Equivalence of `feedback_code5` to `encode_fb5_list(Feedback.feedback(...))`
# ---------------------------------------------------------------------------

def FF5.opt_cons(p: Nat, +r: +List<Nat>) -> +List<Nat>:
  match p:
    case 0n:
      r
    case 1n+a:
      a <> r

def FF5.opt_pool(+p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat,
    +p4: Nat) -> +List<Nat>:
  FF5.opt_cons(p0,
    FF5.opt_cons(p1,
      FF5.opt_cons(p2,
        FF5.opt_cons(p3,
          FF5.opt_cons(p4, Nil{})))))

def FF5.opt_cons_ng_slot(+a: Nat, +r: +List<Nat>, same: Bool) ->
  {FF5.opt_cons(SolveFast.ng_slot(a, same), r)
   == SolveFast.non_green_pick(a, r, same) : +List<Nat>}:
  match same:
    case True{}:
      {==}
    case False{}:
      {==}

def FF5.opt_pool_non_green(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +a0: Nat, +a1: Nat, +a2: Nat, +a3: Nat, +a4: Nat) ->
  {FF5.opt_pool(
     SolveFast.ng_slot(a0, Nat.is_eq(g0, a0)),
     SolveFast.ng_slot(a1, Nat.is_eq(g1, a1)),
     SolveFast.ng_slot(a2, Nat.is_eq(g2, a2)),
     SolveFast.ng_slot(a3, Nat.is_eq(g3, a3)),
     SolveFast.ng_slot(a4, Nat.is_eq(g4, a4)))
   == SolveFast.non_green_fast(
        g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
        a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{})))))
   : +List<Nat>}:
  +e4 = FF5.opt_cons_ng_slot(a4, Nil{}, Nat.is_eq(g4, a4))
  +r4 = SolveFast.non_green_pick(a4, Nil{}, Nat.is_eq(g4, a4))
  +e3 = Equal.trans(+List<Nat>,
          FF5.opt_cons(SolveFast.ng_slot(a3, Nat.is_eq(g3, a3)),
            FF5.opt_cons(SolveFast.ng_slot(a4, Nat.is_eq(g4, a4)), Nil{})),
          FF5.opt_cons(SolveFast.ng_slot(a3, Nat.is_eq(g3, a3)), r4),
          SolveFast.non_green_pick(a3, r4, Nat.is_eq(g3, a3)),
          Equal.cong(+List<Nat>, +List<Nat>,
            x => FF5.opt_cons(SolveFast.ng_slot(a3, Nat.is_eq(g3, a3)), x),
            FF5.opt_cons(SolveFast.ng_slot(a4, Nat.is_eq(g4, a4)), Nil{}),
            r4, e4),
          FF5.opt_cons_ng_slot(a3, r4, Nat.is_eq(g3, a3)))
  +r3 = SolveFast.non_green_pick(a3, r4, Nat.is_eq(g3, a3))
  +e2 = Equal.trans(+List<Nat>,
          FF5.opt_cons(SolveFast.ng_slot(a2, Nat.is_eq(g2, a2)),
            FF5.opt_cons(SolveFast.ng_slot(a3, Nat.is_eq(g3, a3)),
              FF5.opt_cons(SolveFast.ng_slot(a4, Nat.is_eq(g4, a4)), Nil{}))),
          FF5.opt_cons(SolveFast.ng_slot(a2, Nat.is_eq(g2, a2)), r3),
          SolveFast.non_green_pick(a2, r3, Nat.is_eq(g2, a2)),
          Equal.cong(+List<Nat>, +List<Nat>,
            x => FF5.opt_cons(SolveFast.ng_slot(a2, Nat.is_eq(g2, a2)), x),
            FF5.opt_cons(SolveFast.ng_slot(a3, Nat.is_eq(g3, a3)),
              FF5.opt_cons(SolveFast.ng_slot(a4, Nat.is_eq(g4, a4)), Nil{})),
            r3, e3),
          FF5.opt_cons_ng_slot(a2, r3, Nat.is_eq(g2, a2)))
  +r2 = SolveFast.non_green_pick(a2, r3, Nat.is_eq(g2, a2))
  +e1 = Equal.trans(+List<Nat>,
          FF5.opt_cons(SolveFast.ng_slot(a1, Nat.is_eq(g1, a1)),
            FF5.opt_cons(SolveFast.ng_slot(a2, Nat.is_eq(g2, a2)),
              FF5.opt_cons(SolveFast.ng_slot(a3, Nat.is_eq(g3, a3)),
                FF5.opt_cons(SolveFast.ng_slot(a4, Nat.is_eq(g4, a4)), Nil{})))),
          FF5.opt_cons(SolveFast.ng_slot(a1, Nat.is_eq(g1, a1)), r2),
          SolveFast.non_green_pick(a1, r2, Nat.is_eq(g1, a1)),
          Equal.cong(+List<Nat>, +List<Nat>,
            x => FF5.opt_cons(SolveFast.ng_slot(a1, Nat.is_eq(g1, a1)), x),
            FF5.opt_cons(SolveFast.ng_slot(a2, Nat.is_eq(g2, a2)),
              FF5.opt_cons(SolveFast.ng_slot(a3, Nat.is_eq(g3, a3)),
                FF5.opt_cons(SolveFast.ng_slot(a4, Nat.is_eq(g4, a4)), Nil{}))),
            r2, e2),
          FF5.opt_cons_ng_slot(a1, r2, Nat.is_eq(g1, a1)))
  +r1 = SolveFast.non_green_pick(a1, r2, Nat.is_eq(g1, a1))
  Equal.trans(+List<Nat>,
    FF5.opt_cons(SolveFast.ng_slot(a0, Nat.is_eq(g0, a0)),
      FF5.opt_cons(SolveFast.ng_slot(a1, Nat.is_eq(g1, a1)),
        FF5.opt_cons(SolveFast.ng_slot(a2, Nat.is_eq(g2, a2)),
          FF5.opt_cons(SolveFast.ng_slot(a3, Nat.is_eq(g3, a3)),
            FF5.opt_cons(SolveFast.ng_slot(a4, Nat.is_eq(g4, a4)), Nil{}))))),
    FF5.opt_cons(SolveFast.ng_slot(a0, Nat.is_eq(g0, a0)), r1),
    SolveFast.non_green_pick(a0, r1, Nat.is_eq(g0, a0)),
    Equal.cong(+List<Nat>, +List<Nat>,
      x => FF5.opt_cons(SolveFast.ng_slot(a0, Nat.is_eq(g0, a0)), x),
      FF5.opt_cons(SolveFast.ng_slot(a1, Nat.is_eq(g1, a1)),
        FF5.opt_cons(SolveFast.ng_slot(a2, Nat.is_eq(g2, a2)),
          FF5.opt_cons(SolveFast.ng_slot(a3, Nat.is_eq(g3, a3)),
            FF5.opt_cons(SolveFast.ng_slot(a4, Nat.is_eq(g4, a4)), Nil{})))),
      r1, e1),
    FF5.opt_cons_ng_slot(a0, r1, Nat.is_eq(g0, a0)))

# Single-slot consumption laws for `opt_cons(p, r)`.
def FF5.consume_color_of(+x: Nat, +pool: +List<Nat>) -> Feedback.Color:
  SolveFast.consume_color_fast(x, pool, Feedback.next_letter_same(x, pool))

def FF5.consume_pool_of(+x: Nat, +pool: +List<Nat>) -> +List<Nat>:
  SolveFast.consume_pool_fast(x, pool, Feedback.next_letter_same(x, pool))

def FF5.opt_consume_true(+x: Nat, p: Nat, +r: +List<Nat>,
    +et: {Nat.is_eq(Nat.add(1n, x), p) == True{} : Bool}) ->
  Arr.Arr.DPair<
    {FF5.consume_color_of(x, FF5.opt_cons(p, r)) == Feedback.Yellow{}
     : Feedback.Color},
    {FF5.consume_pool_of(x, FF5.opt_cons(p, r)) == r : +List<Nat>}>:
  match p:
    case 0n:
      Empty.absurd(
        Arr.Arr.DPair<
          {FF5.consume_color_of(x, r) == Feedback.Yellow{} : Feedback.Color},
          {FF5.consume_pool_of(x, r) == r : +List<Nat>}>,
        Logic.Proof.false_ne_true(et))
    case 1n++a:
      Arr.DPair{
        Equal.cong(Bool, Feedback.Color,
          b => SolveFast.consume_color_fast(x, a <> r, b),
          Nat.is_eq(x, a), True{}, et),
        Equal.cong(Bool, +List<Nat>,
          b => SolveFast.consume_pool_fast(x, a <> r, b),
          Nat.is_eq(x, a), True{}, et)}

def FF5.opt_consume_false(+x: Nat, p: Nat, +r: +List<Nat>,
    +ef: {Nat.is_eq(Nat.add(1n, x), p) == False{} : Bool}) ->
  Arr.Arr.DPair<
    {FF5.consume_color_of(x, FF5.opt_cons(p, r))
     == FF5.consume_color_of(x, r) : Feedback.Color},
    {FF5.consume_pool_of(x, FF5.opt_cons(p, r))
     == FF5.opt_cons(p, FF5.consume_pool_of(x, r)) : +List<Nat>}>:
  match p:
    case 0n:
      Arr.DPair{{==}, {==}}
    case 1n++a:
      Arr.DPair{
        Equal.cong(Bool, Feedback.Color,
          b => SolveFast.consume_color_fast(x, a <> r, b),
          Nat.is_eq(x, a), False{}, ef),
        Equal.cong(Bool, +List<Nat>,
          b => SolveFast.consume_pool_fast(x, a <> r, b),
          Nat.is_eq(x, a), False{}, ef)}

# Step-by-step specifications for `fb5_s4`, `fb5_s3`, `fb5_s2`, `fb5_s1`, `fb5_s0`.
def FF5.encode_tail1(+fb: +List<Feedback.Color>) -> U32:
  match fb:
    case Nil{}:
      0
    case Con{c4, t}:
      SolveFast.col_u32(c4, 256, 512)

def FF5.encode_tail2(+fb: +List<Feedback.Color>) -> U32:
  match fb:
    case Nil{}:
      0
    case Con{c3, t}:
      U32.or(SolveFast.col_u32(c3, 64, 128), FF5.encode_tail1(t))

def FF5.encode_tail3(+fb: +List<Feedback.Color>) -> U32:
  match fb:
    case Nil{}:
      0
    case Con{c2, t}:
      U32.or(SolveFast.col_u32(c2, 16, 32), FF5.encode_tail2(t))

def FF5.encode_tail4(+fb: +List<Feedback.Color>) -> U32:
  match fb:
    case Nil{}:
      0
    case Con{c1, t}:
      U32.or(SolveFast.col_u32(c1, 4, 8), FF5.encode_tail3(t))

def FF5.encode_tail5(+fb: +List<Feedback.Color>) -> U32:
  match fb:
    case Nil{}:
      0
    case Con{c0, t}:
      U32.or(SolveFast.col_u32(c0, 1, 2), FF5.encode_tail4(t))

def FF5.encode_tail5_eq(+c0: Feedback.Color, +c1: Feedback.Color,
    +c2: Feedback.Color, +c3: Feedback.Color, +c4: Feedback.Color) ->
  {FF5.encode_tail5(c0 <> (c1 <> (c2 <> (c3 <> (c4 <> Nil{})))))
   == SolveFast.encode_fb5(c0, c1, c2, c3, c4) : U32}:
  {==}

# Helper for step 4: `fb5_s4_c*` matches `U32.or(acc, col_u32(consume_color_of(g4, ...), 256, 512))`.
def FF5.s4_c4_eq(eq: Bool, +acc: U32, +g4: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g4), p4) : Bool}) ->
  {SolveFast.fb5_s4_c4(eq, acc)
   == U32.or(acc,
        SolveFast.col_u32(FF5.consume_color_of(g4, FF5.opt_cons(p4, Nil{})),
          256, 512)) : U32}:
  match eq:
    case True{}:
      +pr = FF5.opt_consume_true(g4, p4, Nil{},
              Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g4), p4), eeq))
      +ec = Arr.Arr.dpair_l(
              {FF5.consume_color_of(g4, FF5.opt_cons(p4, Nil{}))
               == Feedback.Yellow{} : Feedback.Color},
              {FF5.consume_pool_of(g4, FF5.opt_cons(p4, Nil{}))
               == Nil{} : +List<Nat>}, pr)
      Equal.cong(Feedback.Color, U32,
        c => U32.or(acc, SolveFast.col_u32(c, 256, 512)),
        Feedback.Yellow{}, FF5.consume_color_of(g4, FF5.opt_cons(p4, Nil{})),
        Equal.sym(Feedback.Color,
          FF5.consume_color_of(g4, FF5.opt_cons(p4, Nil{})),
          Feedback.Yellow{}, ec))
    case False{}:
      +pr = FF5.opt_consume_false(g4, p4, Nil{},
              Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g4), p4), eeq))
      +ec = Arr.Arr.dpair_l(
              {FF5.consume_color_of(g4, FF5.opt_cons(p4, Nil{}))
               == Feedback.Gray{} : Feedback.Color},
              {FF5.consume_pool_of(g4, FF5.opt_cons(p4, Nil{}))
               == FF5.opt_cons(p4, Nil{}) : +List<Nat>}, pr)
      Equal.trans(U32, acc, U32.or(acc, 0),
        U32.or(acc,
          SolveFast.col_u32(FF5.consume_color_of(g4, FF5.opt_cons(p4, Nil{})),
            256, 512)),
        Equal.sym(U32, U32.or(acc, 0), acc, FF5.u32_or_zero_r(acc)),
        Equal.cong(Feedback.Color, U32,
          c => U32.or(acc, SolveFast.col_u32(c, 256, 512)),
          Feedback.Gray{}, FF5.consume_color_of(g4, FF5.opt_cons(p4, Nil{})),
          Equal.sym(Feedback.Color,
            FF5.consume_color_of(g4, FF5.opt_cons(p4, Nil{})),
            Feedback.Gray{}, ec)))

def FF5.s4_c3_eq(eq: Bool, +acc: U32, +g4: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g4), p3) : Bool}) ->
  {SolveFast.fb5_s4_c3(eq, acc, Nat.add(1n, g4), p4)
   == U32.or(acc,
        SolveFast.col_u32(
          FF5.consume_color_of(g4, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))),
          256, 512)) : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p4, Nil{})
      +pr = FF5.opt_consume_true(g4, p3, r,
              Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g4), p3), eeq))
      +ec = Arr.Arr.dpair_l(
              {FF5.consume_color_of(g4, FF5.opt_cons(p3, r))
               == Feedback.Yellow{} : Feedback.Color},
              {FF5.consume_pool_of(g4, FF5.opt_cons(p3, r)) == r : +List<Nat>},
              pr)
      Equal.cong(Feedback.Color, U32,
        c => U32.or(acc, SolveFast.col_u32(c, 256, 512)),
        Feedback.Yellow{}, FF5.consume_color_of(g4, FF5.opt_cons(p3, r)),
        Equal.sym(Feedback.Color,
          FF5.consume_color_of(g4, FF5.opt_cons(p3, r)),
          Feedback.Yellow{}, ec))
    case False{}:
      +r = FF5.opt_cons(p4, Nil{})
      +pr = FF5.opt_consume_false(g4, p3, r,
              Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g4), p3), eeq))
      +ec = Arr.Arr.dpair_l(
              {FF5.consume_color_of(g4, FF5.opt_cons(p3, r))
               == FF5.consume_color_of(g4, r) : Feedback.Color},
              {FF5.consume_pool_of(g4, FF5.opt_cons(p3, r))
               == FF5.opt_cons(p3, FF5.consume_pool_of(g4, r)) : +List<Nat>},
              pr)
      Equal.trans(U32,
        SolveFast.fb5_s4_c4(Nat.is_eq(Nat.add(1n, g4), p4), acc),
        U32.or(acc, SolveFast.col_u32(FF5.consume_color_of(g4, r), 256, 512)),
        U32.or(acc,
          SolveFast.col_u32(FF5.consume_color_of(g4, FF5.opt_cons(p3, r)),
            256, 512)),
        FF5.s4_c4_eq(Nat.is_eq(Nat.add(1n, g4), p4), acc, g4, p4, {==}),
        Equal.cong(Feedback.Color, U32,
          c => U32.or(acc, SolveFast.col_u32(c, 256, 512)),
          FF5.consume_color_of(g4, r),
          FF5.consume_color_of(g4, FF5.opt_cons(p3, r)),
          Equal.sym(Feedback.Color,
            FF5.consume_color_of(g4, FF5.opt_cons(p3, r)),
            FF5.consume_color_of(g4, r), ec)))

def FF5.s4_c2_eq(eq: Bool, +acc: U32, +g4: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g4), p2) : Bool}) ->
  {SolveFast.fb5_s4_c2(eq, acc, Nat.add(1n, g4), p3, p4)
   == U32.or(acc,
        SolveFast.col_u32(
          FF5.consume_color_of(g4,
            FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))),
          256, 512)) : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))
      +pr = FF5.opt_consume_true(g4, p2, r,
              Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g4), p2), eeq))
      +ec = Arr.Arr.dpair_l(
              {FF5.consume_color_of(g4, FF5.opt_cons(p2, r))
               == Feedback.Yellow{} : Feedback.Color},
              {FF5.consume_pool_of(g4, FF5.opt_cons(p2, r)) == r : +List<Nat>},
              pr)
      Equal.cong(Feedback.Color, U32,
        c => U32.or(acc, SolveFast.col_u32(c, 256, 512)),
        Feedback.Yellow{}, FF5.consume_color_of(g4, FF5.opt_cons(p2, r)),
        Equal.sym(Feedback.Color,
          FF5.consume_color_of(g4, FF5.opt_cons(p2, r)),
          Feedback.Yellow{}, ec))
    case False{}:
      +r = FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))
      +pr = FF5.opt_consume_false(g4, p2, r,
              Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g4), p2), eeq))
      +ec = Arr.Arr.dpair_l(
              {FF5.consume_color_of(g4, FF5.opt_cons(p2, r))
               == FF5.consume_color_of(g4, r) : Feedback.Color},
              {FF5.consume_pool_of(g4, FF5.opt_cons(p2, r))
               == FF5.opt_cons(p2, FF5.consume_pool_of(g4, r)) : +List<Nat>},
              pr)
      Equal.trans(U32,
        SolveFast.fb5_s4_c3(Nat.is_eq(Nat.add(1n, g4), p3), acc,
          Nat.add(1n, g4), p4),
        U32.or(acc, SolveFast.col_u32(FF5.consume_color_of(g4, r), 256, 512)),
        U32.or(acc,
          SolveFast.col_u32(FF5.consume_color_of(g4, FF5.opt_cons(p2, r)),
            256, 512)),
        FF5.s4_c3_eq(Nat.is_eq(Nat.add(1n, g4), p3), acc, g4, p3, p4, {==}),
        Equal.cong(Feedback.Color, U32,
          c => U32.or(acc, SolveFast.col_u32(c, 256, 512)),
          FF5.consume_color_of(g4, r),
          FF5.consume_color_of(g4, FF5.opt_cons(p2, r)),
          Equal.sym(Feedback.Color,
            FF5.consume_color_of(g4, FF5.opt_cons(p2, r)),
            FF5.consume_color_of(g4, r), ec)))

def FF5.s4_c1_eq(eq: Bool, +acc: U32, +g4: Nat, +p1: Nat, +p2: Nat, +p3: Nat,
    +p4: Nat, +eeq: {eq == Nat.is_eq(Nat.add(1n, g4), p1) : Bool}) ->
  {SolveFast.fb5_s4_c1(eq, acc, Nat.add(1n, g4), p2, p3, p4)
   == U32.or(acc,
        SolveFast.col_u32(
          FF5.consume_color_of(g4,
            FF5.opt_cons(p1,
              FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))),
          256, 512)) : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))
      +pr = FF5.opt_consume_true(g4, p1, r,
              Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g4), p1), eeq))
      +ec = Arr.Arr.dpair_l(
              {FF5.consume_color_of(g4, FF5.opt_cons(p1, r))
               == Feedback.Yellow{} : Feedback.Color},
              {FF5.consume_pool_of(g4, FF5.opt_cons(p1, r)) == r : +List<Nat>},
              pr)
      Equal.cong(Feedback.Color, U32,
        c => U32.or(acc, SolveFast.col_u32(c, 256, 512)),
        Feedback.Yellow{}, FF5.consume_color_of(g4, FF5.opt_cons(p1, r)),
        Equal.sym(Feedback.Color,
          FF5.consume_color_of(g4, FF5.opt_cons(p1, r)),
          Feedback.Yellow{}, ec))
    case False{}:
      +r = FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))
      +pr = FF5.opt_consume_false(g4, p1, r,
              Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g4), p1), eeq))
      +ec = Arr.Arr.dpair_l(
              {FF5.consume_color_of(g4, FF5.opt_cons(p1, r))
               == FF5.consume_color_of(g4, r) : Feedback.Color},
              {FF5.consume_pool_of(g4, FF5.opt_cons(p1, r))
               == FF5.opt_cons(p1, FF5.consume_pool_of(g4, r)) : +List<Nat>},
              pr)
      Equal.trans(U32,
        SolveFast.fb5_s4_c2(Nat.is_eq(Nat.add(1n, g4), p2), acc,
          Nat.add(1n, g4), p3, p4),
        U32.or(acc, SolveFast.col_u32(FF5.consume_color_of(g4, r), 256, 512)),
        U32.or(acc,
          SolveFast.col_u32(FF5.consume_color_of(g4, FF5.opt_cons(p1, r)),
            256, 512)),
        FF5.s4_c2_eq(Nat.is_eq(Nat.add(1n, g4), p2), acc, g4, p2, p3, p4, {==}),
        Equal.cong(Feedback.Color, U32,
          c => U32.or(acc, SolveFast.col_u32(c, 256, 512)),
          FF5.consume_color_of(g4, r),
          FF5.consume_color_of(g4, FF5.opt_cons(p1, r)),
          Equal.sym(Feedback.Color,
            FF5.consume_color_of(g4, FF5.opt_cons(p1, r)),
            FF5.consume_color_of(g4, r), ec)))

def FF5.s4_c0_eq(eq: Bool, +acc: U32, +g4: Nat, +p0: Nat, +p1: Nat, +p2: Nat,
    +p3: Nat, +p4: Nat, +eeq: {eq == Nat.is_eq(Nat.add(1n, g4), p0) : Bool}) ->
  {SolveFast.fb5_s4_c0(eq, acc, Nat.add(1n, g4), p1, p2, p3, p4)
   == U32.or(acc,
        SolveFast.col_u32(
          FF5.consume_color_of(g4, FF5.opt_pool(p0, p1, p2, p3, p4)),
          256, 512)) : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p1,
             FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))
      +pr = FF5.opt_consume_true(g4, p0, r,
              Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g4), p0), eeq))
      +ec = Arr.Arr.dpair_l(
              {FF5.consume_color_of(g4, FF5.opt_cons(p0, r))
               == Feedback.Yellow{} : Feedback.Color},
              {FF5.consume_pool_of(g4, FF5.opt_cons(p0, r)) == r : +List<Nat>},
              pr)
      Equal.cong(Feedback.Color, U32,
        c => U32.or(acc, SolveFast.col_u32(c, 256, 512)),
        Feedback.Yellow{}, FF5.consume_color_of(g4, FF5.opt_cons(p0, r)),
        Equal.sym(Feedback.Color,
          FF5.consume_color_of(g4, FF5.opt_cons(p0, r)),
          Feedback.Yellow{}, ec))
    case False{}:
      +r = FF5.opt_cons(p1,
             FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))
      +pr = FF5.opt_consume_false(g4, p0, r,
              Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g4), p0), eeq))
      +ec = Arr.Arr.dpair_l(
              {FF5.consume_color_of(g4, FF5.opt_cons(p0, r))
               == FF5.consume_color_of(g4, r) : Feedback.Color},
              {FF5.consume_pool_of(g4, FF5.opt_cons(p0, r))
               == FF5.opt_cons(p0, FF5.consume_pool_of(g4, r)) : +List<Nat>},
              pr)
      Equal.trans(U32,
        SolveFast.fb5_s4_c1(Nat.is_eq(Nat.add(1n, g4), p1), acc,
          Nat.add(1n, g4), p2, p3, p4),
        U32.or(acc, SolveFast.col_u32(FF5.consume_color_of(g4, r), 256, 512)),
        U32.or(acc,
          SolveFast.col_u32(FF5.consume_color_of(g4, FF5.opt_cons(p0, r)),
            256, 512)),
        FF5.s4_c1_eq(Nat.is_eq(Nat.add(1n, g4), p1), acc, g4, p1, p2, p3, p4,
          {==}),
        Equal.cong(Feedback.Color, U32,
          c => U32.or(acc, SolveFast.col_u32(c, 256, 512)),
          FF5.consume_color_of(g4, r),
          FF5.consume_color_of(g4, FF5.opt_cons(p0, r)),
          Equal.sym(Feedback.Color,
            FF5.consume_color_of(g4, FF5.opt_cons(p0, r)),
            FF5.consume_color_of(g4, r), ec)))

def FF5.fb5_s4_eq(+acc: U32, +g4: Nat, +a4: Nat, e4: Bool,
    +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) ->
  {SolveFast.fb5_s4(acc, g4, e4, p0, p1, p2, p3, p4)
   == U32.or(acc,
        FF5.encode_tail1(
          SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
            FF5.opt_pool(p0, p1, p2, p3, p4), e4))) : U32}:
  match e4:
    case True{}:
      {==}
    case False{}:
      FF5.s4_c0_eq(Nat.is_eq(Nat.add(1n, g4), p0), acc, g4,
        p0, p1, p2, p3, p4, {==})

# Generic chain helper: given a continuation `cont(acc2, p0..p4) == U32.or(acc2, rest(opt_pool(p0..p4)))`,
# consuming `g` from `p0..p4` with yellow bit `ybit` produces
# `U32.or(acc, U32.or(col_u32(consume_color_of(g, opt_pool), ybit, gbit), rest(consume_pool_of(g, opt_pool))))`.
# We write the 5-slot consumption helper cleanly once for each step (`s3`, `s2`, `s1`, `s0`).
def FF5.s3_after(+acc: U32, +ybit: U32, +g4: Nat, +a4: Nat, +e4: Bool,
    +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) ->
  {SolveFast.fb5_s4(U32.or(acc, ybit), g4, e4, p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(ybit,
          FF5.encode_tail1(
            SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
              FF5.opt_pool(p0, p1, p2, p3, p4), e4)))) : U32}:
  +t1 = FF5.encode_tail1(
          SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
            FF5.opt_pool(p0, p1, p2, p3, p4), e4))
  Equal.trans(U32,
    SolveFast.fb5_s4(U32.or(acc, ybit), g4, e4, p0, p1, p2, p3, p4),
    U32.or(U32.or(acc, ybit), t1),
    U32.or(acc, U32.or(ybit, t1)),
    FF5.fb5_s4_eq(U32.or(acc, ybit), g4, a4, e4, ee4, p0, p1, p2, p3, p4),
    FF5.u32_or_assoc(acc, ybit, t1))

def FF5.s3_pool_rewrite(+acc: U32, +g3: Nat, +g4: Nat, +a4: Nat, +e4: Bool,
    +c: Feedback.Color, +pool: +List<Nat>, +pool2: +List<Nat>,
    +ec: {FF5.consume_color_of(g3, pool) == c : Feedback.Color},
    +ep: {FF5.consume_pool_of(g3, pool) == pool2 : +List<Nat>}) ->
  {U32.or(acc,
     U32.or(SolveFast.col_u32(c, 64, 128),
       FF5.encode_tail1(
         SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{}, pool2, e4))))
   == U32.or(acc,
        U32.or(SolveFast.col_u32(FF5.consume_color_of(g3, pool), 64, 128),
          FF5.encode_tail1(
            SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
              FF5.consume_pool_of(g3, pool), e4)))) : U32}:
  %ec : {U32.or(acc,
           U32.or(SolveFast.col_u32(_, 64, 128),
             FF5.encode_tail1(
               SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{}, pool2, e4))))
         == U32.or(acc,
              U32.or(SolveFast.col_u32(FF5.consume_color_of(g3, pool), 64, 128),
                FF5.encode_tail1(
                  SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
                    FF5.consume_pool_of(g3, pool), e4)))) : U32}
  %ep : {U32.or(acc,
           U32.or(SolveFast.col_u32(FF5.consume_color_of(g3, pool), 64, 128),
             FF5.encode_tail1(
               SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{}, _, e4))))
         == U32.or(acc,
              U32.or(SolveFast.col_u32(FF5.consume_color_of(g3, pool), 64, 128),
                FF5.encode_tail1(
                  SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
                    FF5.consume_pool_of(g3, pool), e4)))) : U32}
  {==}

def FF5.s3_c4_eq(eq: Bool, +acc: U32, +g3: Nat, +g4: Nat, +a4: Nat, +e4: Bool,
    +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g3), p4) : Bool}) ->
  {SolveFast.fb5_s3_c4(eq, acc, g4, e4, p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{})),
            64, 128),
          FF5.encode_tail1(
            SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
              FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
                FF5.opt_cons(p3, FF5.consume_pool_of(g3,
                  FF5.opt_cons(p4, Nil{})))))),
              e4)))) : U32}:
  match eq:
    case True{}:
      +pr = FF5.opt_consume_true(g3, p4, Nil{},
              Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g3), p4), eeq))
      +ec = Arr.Arr.dpair_l(
              {FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{}))
               == Feedback.Yellow{} : Feedback.Color},
              {FF5.consume_pool_of(g3, FF5.opt_cons(p4, Nil{}))
               == Nil{} : +List<Nat>}, pr)
      +ep = Arr.Arr.dpair_r(
              {FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{}))
               == Feedback.Yellow{} : Feedback.Color},
              {FF5.consume_pool_of(g3, FF5.opt_cons(p4, Nil{}))
               == Nil{} : +List<Nat>}, pr)
      Equal.trans(U32,
        SolveFast.fb5_s4(U32.or(acc, 64), g4, e4, p0, p1, p2, p3, 0n),
        U32.or(acc,
          U32.or(64,
            FF5.encode_tail1(
              SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
                FF5.opt_pool(p0, p1, p2, p3, 0n), e4)))),
        U32.or(acc,
          U32.or(
            SolveFast.col_u32(FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{})),
              64, 128),
            FF5.encode_tail1(
              SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
                FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
                  FF5.opt_cons(p3, FF5.consume_pool_of(g3,
                    FF5.opt_cons(p4, Nil{})))))), e4)))),
        FF5.s3_after(acc, 64, g4, a4, e4, ee4, p0, p1, p2, p3, 0n),
        Equal.trans(U32,
          U32.or(acc,
            U32.or(64,
              FF5.encode_tail1(
                SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
                  FF5.opt_pool(p0, p1, p2, p3, 0n), e4)))),
          U32.or(acc,
            U32.or(
              SolveFast.col_u32(FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{})),
                64, 128),
              FF5.encode_tail1(
                SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
                  FF5.opt_pool(p0, p1, p2, p3, 0n), e4)))),
          U32.or(acc,
            U32.or(
              SolveFast.col_u32(FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{})),
                64, 128),
              FF5.encode_tail1(
                SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
                  FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
                    FF5.opt_cons(p3, FF5.consume_pool_of(g3,
                      FF5.opt_cons(p4, Nil{})))))), e4)))),
          Equal.cong(Feedback.Color, U32,
            c => U32.or(acc,
                   U32.or(SolveFast.col_u32(c, 64, 128),
                     FF5.encode_tail1(
                       SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
                         FF5.opt_pool(p0, p1, p2, p3, 0n), e4)))),
            Feedback.Yellow{}, FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{})),
            Equal.sym(Feedback.Color,
              FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{})),
              Feedback.Yellow{}, ec)),
          Equal.cong(+List<Nat>, U32,
            q => U32.or(acc,
                   U32.or(
                     SolveFast.col_u32(
                       FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{})),
                       64, 128),
                     FF5.encode_tail1(
                       SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
                         FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
                           FF5.opt_cons(p3, q)))), e4)))),
            Nil{}, FF5.consume_pool_of(g3, FF5.opt_cons(p4, Nil{})),
            Equal.sym(+List<Nat>,
              FF5.consume_pool_of(g3, FF5.opt_cons(p4, Nil{})), Nil{}, ep))))
    case False{}:
      +pr = FF5.opt_consume_false(g3, p4, Nil{},
              Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g3), p4), eeq))
      +ec = Arr.Arr.dpair_l(
              {FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{}))
               == Feedback.Gray{} : Feedback.Color},
              {FF5.consume_pool_of(g3, FF5.opt_cons(p4, Nil{}))
               == FF5.opt_cons(p4, Nil{}) : +List<Nat>}, pr)
      +ep = Arr.Arr.dpair_r(
              {FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{}))
               == Feedback.Gray{} : Feedback.Color},
              {FF5.consume_pool_of(g3, FF5.opt_cons(p4, Nil{}))
               == FF5.opt_cons(p4, Nil{}) : +List<Nat>}, pr)
      +t1 = FF5.encode_tail1(
              SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
                FF5.opt_pool(p0, p1, p2, p3, p4), e4))
      Equal.trans(U32,
        SolveFast.fb5_s4(acc, g4, e4, p0, p1, p2, p3, p4),
        U32.or(acc, U32.or(0, t1)),
        U32.or(acc,
          U32.or(
            SolveFast.col_u32(FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{})),
              64, 128),
            FF5.encode_tail1(
              SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
                FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
                  FF5.opt_cons(p3, FF5.consume_pool_of(g3,
                    FF5.opt_cons(p4, Nil{})))))), e4)))),
        Equal.trans(U32,
          SolveFast.fb5_s4(acc, g4, e4, p0, p1, p2, p3, p4),
          U32.or(acc, t1),
          U32.or(acc, U32.or(0, t1)),
          FF5.fb5_s4_eq(acc, g4, a4, e4, ee4, p0, p1, p2, p3, p4),
          Equal.cong(U32, U32, x => U32.or(acc, x), t1, U32.or(0, t1),
            Equal.sym(U32, U32.or(0, t1), t1, FF5.u32_or_zero_l(t1)))),
        Equal.trans(U32,
          U32.or(acc, U32.or(0, t1)),
          U32.or(acc,
            U32.or(
              SolveFast.col_u32(FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{})),
                64, 128), t1)),
          U32.or(acc,
            U32.or(
              SolveFast.col_u32(FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{})),
                64, 128),
              FF5.encode_tail1(
                SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
                  FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
                    FF5.opt_cons(p3, FF5.consume_pool_of(g3,
                      FF5.opt_cons(p4, Nil{})))))), e4)))),
          Equal.cong(Feedback.Color, U32,
            c => U32.or(acc, U32.or(SolveFast.col_u32(c, 64, 128), t1)),
            Feedback.Gray{}, FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{})),
            Equal.sym(Feedback.Color,
              FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{})),
              Feedback.Gray{}, ec)),
          Equal.cong(+List<Nat>, U32,
            q => U32.or(acc,
                   U32.or(
                     SolveFast.col_u32(
                       FF5.consume_color_of(g3, FF5.opt_cons(p4, Nil{})),
                       64, 128),
                     FF5.encode_tail1(
                       SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
                         FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
                           FF5.opt_cons(p3, q)))), e4)))),
            FF5.opt_cons(p4, Nil{}),
            FF5.consume_pool_of(g3, FF5.opt_cons(p4, Nil{})),
            Equal.sym(+List<Nat>,
              FF5.consume_pool_of(g3, FF5.opt_cons(p4, Nil{})),
              FF5.opt_cons(p4, Nil{}), ep))))


# Generic hit/miss rewrite lemmas reused across all 5-slot steps `s3..s0`.
def FF5.step_hit_eq(-F: +List<Nat> -> U32, -P: +List<Nat> -> +List<Nat>,
    +acc: U32, +ybit: U32, +gbit: U32, +g: Nat, +p: Nat, +r: +List<Nat>,
    +et: {Nat.is_eq(Nat.add(1n, g), p) == True{} : Bool}) ->
  {U32.or(acc, U32.or(ybit, F(P(r))))
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g, FF5.opt_cons(p, r)),
            ybit, gbit),
          F(P(FF5.consume_pool_of(g, FF5.opt_cons(p, r)))))) : U32}:
  +pr = FF5.opt_consume_true(g, p, r, et)
  +ec = Arr.Arr.dpair_l(
          {FF5.consume_color_of(g, FF5.opt_cons(p, r)) == Feedback.Yellow{}
           : Feedback.Color},
          {FF5.consume_pool_of(g, FF5.opt_cons(p, r)) == r : +List<Nat>}, pr)
  +ep = Arr.Arr.dpair_r(
          {FF5.consume_color_of(g, FF5.opt_cons(p, r)) == Feedback.Yellow{}
           : Feedback.Color},
          {FF5.consume_pool_of(g, FF5.opt_cons(p, r)) == r : +List<Nat>}, pr)
  %ec : {U32.or(acc, U32.or(SolveFast.col_u32(_, ybit, gbit), F(P(r))))
         == U32.or(acc,
              U32.or(
                SolveFast.col_u32(FF5.consume_color_of(g, FF5.opt_cons(p, r)),
                  ybit, gbit),
                F(P(FF5.consume_pool_of(g, FF5.opt_cons(p, r)))))) : U32}
  %ep : {U32.or(acc,
           U32.or(
             SolveFast.col_u32(FF5.consume_color_of(g, FF5.opt_cons(p, r)),
               ybit, gbit),
             F(P(_))))
         == U32.or(acc,
              U32.or(
                SolveFast.col_u32(FF5.consume_color_of(g, FF5.opt_cons(p, r)),
                  ybit, gbit),
                F(P(FF5.consume_pool_of(g, FF5.opt_cons(p, r)))))) : U32}
  {==}

def FF5.step_miss_eq(-F: +List<Nat> -> U32, -P: +List<Nat> -> +List<Nat>,
    +acc: U32, +ybit: U32, +gbit: U32, +g: Nat, +p: Nat, +r: +List<Nat>,
    +ef: {Nat.is_eq(Nat.add(1n, g), p) == False{} : Bool}) ->
  {U32.or(acc,
     U32.or(
       SolveFast.col_u32(FF5.consume_color_of(g, r), ybit, gbit),
       F(P(FF5.opt_cons(p, FF5.consume_pool_of(g, r))))))
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g, FF5.opt_cons(p, r)),
            ybit, gbit),
          F(P(FF5.consume_pool_of(g, FF5.opt_cons(p, r)))))) : U32}:
  +pr = FF5.opt_consume_false(g, p, r, ef)
  +ec = Arr.Arr.dpair_l(
          {FF5.consume_color_of(g, FF5.opt_cons(p, r))
           == FF5.consume_color_of(g, r) : Feedback.Color},
          {FF5.consume_pool_of(g, FF5.opt_cons(p, r))
           == FF5.opt_cons(p, FF5.consume_pool_of(g, r)) : +List<Nat>}, pr)
  +ep = Arr.Arr.dpair_r(
          {FF5.consume_color_of(g, FF5.opt_cons(p, r))
           == FF5.consume_color_of(g, r) : Feedback.Color},
          {FF5.consume_pool_of(g, FF5.opt_cons(p, r))
           == FF5.opt_cons(p, FF5.consume_pool_of(g, r)) : +List<Nat>}, pr)
  %ec : {U32.or(acc,
           U32.or(
             SolveFast.col_u32(_, ybit, gbit),
             F(P(FF5.opt_cons(p, FF5.consume_pool_of(g, r))))))
         == U32.or(acc,
              U32.or(
                SolveFast.col_u32(FF5.consume_color_of(g, FF5.opt_cons(p, r)),
                  ybit, gbit),
                F(P(FF5.consume_pool_of(g, FF5.opt_cons(p, r)))))) : U32}
  %ep : {U32.or(acc,
           U32.or(
             SolveFast.col_u32(FF5.consume_color_of(g, FF5.opt_cons(p, r)),
               ybit, gbit),
             F(P(_))))
         == U32.or(acc,
              U32.or(
                SolveFast.col_u32(FF5.consume_color_of(g, FF5.opt_cons(p, r)),
                  ybit, gbit),
                F(P(FF5.consume_pool_of(g, FF5.opt_cons(p, r)))))) : U32}
  {==}

def FF5.s3_tail(+g4: Nat, +a4: Nat, +e4: Bool, +pool: +List<Nat>) -> U32:
  FF5.encode_tail1(SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{}, pool, e4))

def FF5.s3_c3_eq(eq: Bool, +acc: U32, +g3: Nat, +g4: Nat, +a4: Nat, +e4: Bool,
    +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g3), p3) : Bool}) ->
  {SolveFast.fb5_s3_c3(eq, acc, Nat.add(1n, g3), g4, e4, p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g3, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))),
            64, 128),
          FF5.s3_tail(g4, a4, e4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.consume_pool_of(g3,
                FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))))))) : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p4, Nil{})
      Equal.trans(U32,
        SolveFast.fb5_s4(U32.or(acc, 64), g4, e4, p0, p1, p2, 0n, p4),
        U32.or(acc, U32.or(64, FF5.s3_tail(g4, a4, e4,
          FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2, r)))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g3, FF5.opt_cons(p3, r)),
            64, 128),
          FF5.s3_tail(g4, a4, e4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.consume_pool_of(g3, FF5.opt_cons(p3, r)))))))),
        FF5.s3_after(acc, 64, g4, a4, e4, ee4, p0, p1, p2, 0n, p4),
        FF5.step_hit_eq(q => FF5.s3_tail(g4, a4, e4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2, q))),
          acc, 64, 128, g3, p3, r,
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g3), p3), eeq)))
    case False{}:
      +r = FF5.opt_cons(p4, Nil{})
      Equal.trans(U32,
        SolveFast.fb5_s3_c4(Nat.is_eq(Nat.add(1n, g3), p4), acc, g4, e4,
          p0, p1, p2, p3, p4),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g3, r), 64, 128),
          FF5.s3_tail(g4, a4, e4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.opt_cons(p3, FF5.consume_pool_of(g3, r)))))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g3, FF5.opt_cons(p3, r)),
            64, 128),
          FF5.s3_tail(g4, a4, e4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.consume_pool_of(g3, FF5.opt_cons(p3, r)))))))),
        FF5.s3_c4_eq(Nat.is_eq(Nat.add(1n, g3), p4), acc, g3, g4, a4, e4, ee4,
          p0, p1, p2, p3, p4, {==}),
        FF5.step_miss_eq(q => FF5.s3_tail(g4, a4, e4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2, q))),
          acc, 64, 128, g3, p3, r,
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g3), p3), eeq)))

def FF5.s3_c2_eq(eq: Bool, +acc: U32, +g3: Nat, +g4: Nat, +a4: Nat, +e4: Bool,
    +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g3), p2) : Bool}) ->
  {SolveFast.fb5_s3_c2(eq, acc, Nat.add(1n, g3), g4, e4, p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g3,
              FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))),
            64, 128),
          FF5.s3_tail(g4, a4, e4,
            FF5.opt_cons(p0, FF5.opt_cons(p1,
              FF5.consume_pool_of(g3,
                FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))))))))
   : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))
      Equal.trans(U32,
        SolveFast.fb5_s4(U32.or(acc, 64), g4, e4, p0, p1, 0n, p3, p4),
        U32.or(acc, U32.or(64, FF5.s3_tail(g4, a4, e4,
          FF5.opt_cons(p0, FF5.opt_cons(p1, r))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g3, FF5.opt_cons(p2, r)),
            64, 128),
          FF5.s3_tail(g4, a4, e4,
            FF5.opt_cons(p0, FF5.opt_cons(p1,
              FF5.consume_pool_of(g3, FF5.opt_cons(p2, r))))))),
        FF5.s3_after(acc, 64, g4, a4, e4, ee4, p0, p1, 0n, p3, p4),
        FF5.step_hit_eq(q => FF5.s3_tail(g4, a4, e4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, q)),
          acc, 64, 128, g3, p2, r,
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g3), p2), eeq)))
    case False{}:
      +r = FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))
      Equal.trans(U32,
        SolveFast.fb5_s3_c3(Nat.is_eq(Nat.add(1n, g3), p3), acc,
          Nat.add(1n, g3), g4, e4, p0, p1, p2, p3, p4),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g3, r), 64, 128),
          FF5.s3_tail(g4, a4, e4,
            FF5.opt_cons(p0, FF5.opt_cons(p1,
              FF5.opt_cons(p2, FF5.consume_pool_of(g3, r))))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g3, FF5.opt_cons(p2, r)),
            64, 128),
          FF5.s3_tail(g4, a4, e4,
            FF5.opt_cons(p0, FF5.opt_cons(p1,
              FF5.consume_pool_of(g3, FF5.opt_cons(p2, r))))))),
        FF5.s3_c3_eq(Nat.is_eq(Nat.add(1n, g3), p3), acc, g3, g4, a4, e4, ee4,
          p0, p1, p2, p3, p4, {==}),
        FF5.step_miss_eq(q => FF5.s3_tail(g4, a4, e4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, q)),
          acc, 64, 128, g3, p2, r,
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g3), p2), eeq)))

def FF5.s3_c1_eq(eq: Bool, +acc: U32, +g3: Nat, +g4: Nat, +a4: Nat, +e4: Bool,
    +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g3), p1) : Bool}) ->
  {SolveFast.fb5_s3_c1(eq, acc, Nat.add(1n, g3), g4, e4, p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g3,
              FF5.opt_cons(p1,
                FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))),
            64, 128),
          FF5.s3_tail(g4, a4, e4,
            FF5.opt_cons(p0,
              FF5.consume_pool_of(g3,
                FF5.opt_cons(p1,
                  FF5.opt_cons(p2, FF5.opt_cons(p3,
                    FF5.opt_cons(p4, Nil{}))))))))) : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))
      Equal.trans(U32,
        SolveFast.fb5_s4(U32.or(acc, 64), g4, e4, p0, 0n, p2, p3, p4),
        U32.or(acc, U32.or(64, FF5.s3_tail(g4, a4, e4, FF5.opt_cons(p0, r)))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g3, FF5.opt_cons(p1, r)),
            64, 128),
          FF5.s3_tail(g4, a4, e4,
            FF5.opt_cons(p0, FF5.consume_pool_of(g3, FF5.opt_cons(p1, r)))))),
        FF5.s3_after(acc, 64, g4, a4, e4, ee4, p0, 0n, p2, p3, p4),
        FF5.step_hit_eq(q => FF5.s3_tail(g4, a4, e4, q),
          q => FF5.opt_cons(p0, q),
          acc, 64, 128, g3, p1, r,
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g3), p1), eeq)))
    case False{}:
      +r = FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))
      Equal.trans(U32,
        SolveFast.fb5_s3_c2(Nat.is_eq(Nat.add(1n, g3), p2), acc,
          Nat.add(1n, g3), g4, e4, p0, p1, p2, p3, p4),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g3, r), 64, 128),
          FF5.s3_tail(g4, a4, e4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.consume_pool_of(g3, r)))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g3, FF5.opt_cons(p1, r)),
            64, 128),
          FF5.s3_tail(g4, a4, e4,
            FF5.opt_cons(p0, FF5.consume_pool_of(g3, FF5.opt_cons(p1, r)))))),
        FF5.s3_c2_eq(Nat.is_eq(Nat.add(1n, g3), p2), acc, g3, g4, a4, e4, ee4,
          p0, p1, p2, p3, p4, {==}),
        FF5.step_miss_eq(q => FF5.s3_tail(g4, a4, e4, q),
          q => FF5.opt_cons(p0, q),
          acc, 64, 128, g3, p1, r,
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g3), p1), eeq)))

def FF5.s3_c0_eq(eq: Bool, +acc: U32, +g3: Nat, +g4: Nat, +a4: Nat, +e4: Bool,
    +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g3), p0) : Bool}) ->
  {SolveFast.fb5_s3_c0(eq, acc, Nat.add(1n, g3), g4, e4, p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g3, FF5.opt_pool(p0, p1, p2, p3, p4)),
            64, 128),
          FF5.s3_tail(g4, a4, e4,
            FF5.consume_pool_of(g3, FF5.opt_pool(p0, p1, p2, p3, p4))))) : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p1,
             FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))
      Equal.trans(U32,
        SolveFast.fb5_s4(U32.or(acc, 64), g4, e4, 0n, p1, p2, p3, p4),
        U32.or(acc, U32.or(64, FF5.s3_tail(g4, a4, e4, r))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g3, FF5.opt_cons(p0, r)),
            64, 128),
          FF5.s3_tail(g4, a4, e4,
            FF5.consume_pool_of(g3, FF5.opt_cons(p0, r))))),
        FF5.s3_after(acc, 64, g4, a4, e4, ee4, 0n, p1, p2, p3, p4),
        FF5.step_hit_eq(q => FF5.s3_tail(g4, a4, e4, q), q => q,
          acc, 64, 128, g3, p0, r,
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g3), p0), eeq)))
    case False{}:
      +r = FF5.opt_cons(p1,
             FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))
      Equal.trans(U32,
        SolveFast.fb5_s3_c1(Nat.is_eq(Nat.add(1n, g3), p1), acc,
          Nat.add(1n, g3), g4, e4, p0, p1, p2, p3, p4),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g3, r), 64, 128),
          FF5.s3_tail(g4, a4, e4,
            FF5.opt_cons(p0, FF5.consume_pool_of(g3, r))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g3, FF5.opt_cons(p0, r)),
            64, 128),
          FF5.s3_tail(g4, a4, e4,
            FF5.consume_pool_of(g3, FF5.opt_cons(p0, r))))),
        FF5.s3_c1_eq(Nat.is_eq(Nat.add(1n, g3), p1), acc, g3, g4, a4, e4, ee4,
          p0, p1, p2, p3, p4, {==}),
        FF5.step_miss_eq(q => FF5.s3_tail(g4, a4, e4, q), q => q,
          acc, 64, 128, g3, p0, r,
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g3), p0), eeq)))

def FF5.fb5_s3_eq(+acc: U32, +g3: Nat, +a3: Nat, e3: Bool,
    +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) ->
  {SolveFast.fb5_s3(acc, g3, e3, g4, e4, p0, p1, p2, p3, p4)
   == U32.or(acc,
        FF5.encode_tail2(
          SolveFast.feedback_go_fast(g3 <> (g4 <> Nil{}), a3 <> (a4 <> Nil{}),
            FF5.opt_pool(p0, p1, p2, p3, p4), e3))) : U32}:
  match e3:
    case True{}:
      %ee4 : {SolveFast.fb5_s4(U32.or(acc, 128), g4, e4, p0, p1, p2, p3, p4)
              == U32.or(acc, U32.or(128,
                   FF5.encode_tail1(
                     SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
                       FF5.opt_pool(p0, p1, p2, p3, p4), _)))) : U32}
      FF5.s3_after(acc, 128, g4, a4, e4, ee4, p0, p1, p2, p3, p4)
    case False{}:
      %ee4 : {SolveFast.fb5_s3_c0(Nat.is_eq(Nat.add(1n, g3), p0), acc,
                Nat.add(1n, g3), g4, e4, p0, p1, p2, p3, p4)
              == U32.or(acc,
                   U32.or(
                     SolveFast.col_u32(
                       FF5.consume_color_of(g3, FF5.opt_pool(p0, p1, p2, p3, p4)),
                       64, 128),
                     FF5.encode_tail1(
                       SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{},
                         FF5.consume_pool_of(g3, FF5.opt_pool(p0, p1, p2, p3, p4)),
                         _)))) : U32}
      FF5.s3_c0_eq(Nat.is_eq(Nat.add(1n, g3), p0), acc, g3, g4, a4, e4, ee4,
        p0, p1, p2, p3, p4, {==})

# Step 2 (`fb5_s2_c4..c0`, `fb5_s2`)
def FF5.s2_tail(+g3: Nat, +a3: Nat, +e3: Bool, +g4: Nat, +a4: Nat,
    +pool: +List<Nat>) -> U32:
  FF5.encode_tail2(
    SolveFast.feedback_go_fast(g3 <> (g4 <> Nil{}), a3 <> (a4 <> Nil{}),
      pool, e3))

def FF5.s2_after(+acc: U32, +ybit: U32, +g3: Nat, +a3: Nat, +e3: Bool,
    +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) ->
  {SolveFast.fb5_s3(U32.or(acc, ybit), g3, e3, g4, e4, p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(ybit,
          FF5.s2_tail(g3, a3, e3, g4, a4, FF5.opt_pool(p0, p1, p2, p3, p4))))
   : U32}:
  +t2 = FF5.s2_tail(g3, a3, e3, g4, a4, FF5.opt_pool(p0, p1, p2, p3, p4))
  Equal.trans(U32,
    SolveFast.fb5_s3(U32.or(acc, ybit), g3, e3, g4, e4, p0, p1, p2, p3, p4),
    U32.or(U32.or(acc, ybit), t2),
    U32.or(acc, U32.or(ybit, t2)),
    FF5.fb5_s3_eq(U32.or(acc, ybit), g3, a3, e3, ee3, g4, a4, e4, ee4,
      p0, p1, p2, p3, p4),
    FF5.u32_or_assoc(acc, ybit, t2))

def FF5.s2_c4_eq(eq: Bool, +acc: U32, +g2: Nat, +g3: Nat, +a3: Nat, +e3: Bool,
    +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g2), p4) : Bool}) ->
  {SolveFast.fb5_s2_c4(eq, acc, g3, e3, g4, e4, p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g2, FF5.opt_cons(p4, Nil{})),
            16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.opt_cons(p3, FF5.consume_pool_of(g2,
                FF5.opt_cons(p4, Nil{}))))))))) : U32}:
  match eq:
    case True{}:
      Equal.trans(U32,
        SolveFast.fb5_s3(U32.or(acc, 16), g3, e3, g4, e4, p0, p1, p2, p3, 0n),
        U32.or(acc, U32.or(16, FF5.s2_tail(g3, a3, e3, g4, a4,
          FF5.opt_pool(p0, p1, p2, p3, 0n)))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g2, FF5.opt_cons(p4, Nil{})),
            16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.opt_cons(p3, FF5.consume_pool_of(g2,
                FF5.opt_cons(p4, Nil{}))))))))),
        FF5.s2_after(acc, 16, g3, a3, e3, ee3, g4, a4, e4, ee4,
          p0, p1, p2, p3, 0n),
        FF5.step_hit_eq(q => FF5.s2_tail(g3, a3, e3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
                 FF5.opt_cons(p3, q)))),
          acc, 16, 32, g2, p4, Nil{},
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g2), p4), eeq)))
    case False{}:
      +t2 = FF5.s2_tail(g3, a3, e3, g4, a4, FF5.opt_pool(p0, p1, p2, p3, p4))
      Equal.trans(U32,
        SolveFast.fb5_s3(acc, g3, e3, g4, e4, p0, p1, p2, p3, p4),
        U32.or(acc, U32.or(0, t2)),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g2, FF5.opt_cons(p4, Nil{})),
            16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.opt_cons(p3, FF5.consume_pool_of(g2,
                FF5.opt_cons(p4, Nil{}))))))))),
        Equal.trans(U32,
          SolveFast.fb5_s3(acc, g3, e3, g4, e4, p0, p1, p2, p3, p4),
          U32.or(acc, t2),
          U32.or(acc, U32.or(0, t2)),
          FF5.fb5_s3_eq(acc, g3, a3, e3, ee3, g4, a4, e4, ee4,
            p0, p1, p2, p3, p4),
          Equal.cong(U32, U32, x => U32.or(acc, x), t2, U32.or(0, t2),
            Equal.sym(U32, U32.or(0, t2), t2, FF5.u32_or_zero_l(t2)))),
        FF5.step_miss_eq(q => FF5.s2_tail(g3, a3, e3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
                 FF5.opt_cons(p3, q)))),
          acc, 16, 32, g2, p4, Nil{},
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g2), p4), eeq)))

def FF5.s2_c3_eq(eq: Bool, +acc: U32, +g2: Nat, +g3: Nat, +a3: Nat, +e3: Bool,
    +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g2), p3) : Bool}) ->
  {SolveFast.fb5_s2_c3(eq, acc, Nat.add(1n, g2), g3, e3, g4, e4,
     p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))),
            16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.consume_pool_of(g2,
                FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))))))) : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p4, Nil{})
      Equal.trans(U32,
        SolveFast.fb5_s3(U32.or(acc, 16), g3, e3, g4, e4, p0, p1, p2, 0n, p4),
        U32.or(acc, U32.or(16, FF5.s2_tail(g3, a3, e3, g4, a4,
          FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2, r)))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g2, FF5.opt_cons(p3, r)),
            16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.consume_pool_of(g2, FF5.opt_cons(p3, r)))))))),
        FF5.s2_after(acc, 16, g3, a3, e3, ee3, g4, a4, e4, ee4,
          p0, p1, p2, 0n, p4),
        FF5.step_hit_eq(q => FF5.s2_tail(g3, a3, e3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2, q))),
          acc, 16, 32, g2, p3, r,
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g2), p3), eeq)))
    case False{}:
      +r = FF5.opt_cons(p4, Nil{})
      Equal.trans(U32,
        SolveFast.fb5_s2_c4(Nat.is_eq(Nat.add(1n, g2), p4), acc, g3, e3, g4, e4,
          p0, p1, p2, p3, p4),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g2, r), 16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.opt_cons(p3, FF5.consume_pool_of(g2, r)))))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g2, FF5.opt_cons(p3, r)),
            16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.consume_pool_of(g2, FF5.opt_cons(p3, r)))))))),
        FF5.s2_c4_eq(Nat.is_eq(Nat.add(1n, g2), p4), acc, g2, g3, a3, e3, ee3,
          g4, a4, e4, ee4, p0, p1, p2, p3, p4, {==}),
        FF5.step_miss_eq(q => FF5.s2_tail(g3, a3, e3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2, q))),
          acc, 16, 32, g2, p3, r,
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g2), p3), eeq)))

def FF5.s2_c2_eq(eq: Bool, +acc: U32, +g2: Nat, +g3: Nat, +a3: Nat, +e3: Bool,
    +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g2), p2) : Bool}) ->
  {SolveFast.fb5_s2_c2(eq, acc, Nat.add(1n, g2), g3, e3, g4, e4,
     p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g2,
              FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))),
            16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1,
              FF5.consume_pool_of(g2,
                FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))))))))
   : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))
      Equal.trans(U32,
        SolveFast.fb5_s3(U32.or(acc, 16), g3, e3, g4, e4, p0, p1, 0n, p3, p4),
        U32.or(acc, U32.or(16, FF5.s2_tail(g3, a3, e3, g4, a4,
          FF5.opt_cons(p0, FF5.opt_cons(p1, r))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g2, FF5.opt_cons(p2, r)),
            16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1,
              FF5.consume_pool_of(g2, FF5.opt_cons(p2, r))))))),
        FF5.s2_after(acc, 16, g3, a3, e3, ee3, g4, a4, e4, ee4,
          p0, p1, 0n, p3, p4),
        FF5.step_hit_eq(q => FF5.s2_tail(g3, a3, e3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, q)),
          acc, 16, 32, g2, p2, r,
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g2), p2), eeq)))
    case False{}:
      +r = FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))
      Equal.trans(U32,
        SolveFast.fb5_s2_c3(Nat.is_eq(Nat.add(1n, g2), p3), acc,
          Nat.add(1n, g2), g3, e3, g4, e4, p0, p1, p2, p3, p4),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g2, r), 16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1,
              FF5.opt_cons(p2, FF5.consume_pool_of(g2, r))))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g2, FF5.opt_cons(p2, r)),
            16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1,
              FF5.consume_pool_of(g2, FF5.opt_cons(p2, r))))))),
        FF5.s2_c3_eq(Nat.is_eq(Nat.add(1n, g2), p3), acc, g2, g3, a3, e3, ee3,
          g4, a4, e4, ee4, p0, p1, p2, p3, p4, {==}),
        FF5.step_miss_eq(q => FF5.s2_tail(g3, a3, e3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, q)),
          acc, 16, 32, g2, p2, r,
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g2), p2), eeq)))

def FF5.s2_c1_eq(eq: Bool, +acc: U32, +g2: Nat, +g3: Nat, +a3: Nat, +e3: Bool,
    +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g2), p1) : Bool}) ->
  {SolveFast.fb5_s2_c1(eq, acc, Nat.add(1n, g2), g3, e3, g4, e4,
     p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g2,
              FF5.opt_cons(p1,
                FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))),
            16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.opt_cons(p0,
              FF5.consume_pool_of(g2,
                FF5.opt_cons(p1,
                  FF5.opt_cons(p2, FF5.opt_cons(p3,
                    FF5.opt_cons(p4, Nil{}))))))))) : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))
      Equal.trans(U32,
        SolveFast.fb5_s3(U32.or(acc, 16), g3, e3, g4, e4, p0, 0n, p2, p3, p4),
        U32.or(acc, U32.or(16, FF5.s2_tail(g3, a3, e3, g4, a4,
          FF5.opt_cons(p0, r)))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g2, FF5.opt_cons(p1, r)),
            16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.opt_cons(p0, FF5.consume_pool_of(g2, FF5.opt_cons(p1, r)))))),
        FF5.s2_after(acc, 16, g3, a3, e3, ee3, g4, a4, e4, ee4,
          p0, 0n, p2, p3, p4),
        FF5.step_hit_eq(q => FF5.s2_tail(g3, a3, e3, g4, a4, q),
          q => FF5.opt_cons(p0, q),
          acc, 16, 32, g2, p1, r,
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g2), p1), eeq)))
    case False{}:
      +r = FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))
      Equal.trans(U32,
        SolveFast.fb5_s2_c2(Nat.is_eq(Nat.add(1n, g2), p2), acc,
          Nat.add(1n, g2), g3, e3, g4, e4, p0, p1, p2, p3, p4),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g2, r), 16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.consume_pool_of(g2, r)))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g2, FF5.opt_cons(p1, r)),
            16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.opt_cons(p0, FF5.consume_pool_of(g2, FF5.opt_cons(p1, r)))))),
        FF5.s2_c2_eq(Nat.is_eq(Nat.add(1n, g2), p2), acc, g2, g3, a3, e3, ee3,
          g4, a4, e4, ee4, p0, p1, p2, p3, p4, {==}),
        FF5.step_miss_eq(q => FF5.s2_tail(g3, a3, e3, g4, a4, q),
          q => FF5.opt_cons(p0, q),
          acc, 16, 32, g2, p1, r,
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g2), p1), eeq)))

def FF5.s2_c0_eq(eq: Bool, +acc: U32, +g2: Nat, +g3: Nat, +a3: Nat, +e3: Bool,
    +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g2), p0) : Bool}) ->
  {SolveFast.fb5_s2_c0(eq, acc, Nat.add(1n, g2), g3, e3, g4, e4,
     p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g2, FF5.opt_pool(p0, p1, p2, p3, p4)),
            16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.consume_pool_of(g2, FF5.opt_pool(p0, p1, p2, p3, p4))))) : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p1,
             FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))
      Equal.trans(U32,
        SolveFast.fb5_s3(U32.or(acc, 16), g3, e3, g4, e4, 0n, p1, p2, p3, p4),
        U32.or(acc, U32.or(16, FF5.s2_tail(g3, a3, e3, g4, a4, r))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g2, FF5.opt_cons(p0, r)),
            16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.consume_pool_of(g2, FF5.opt_cons(p0, r))))),
        FF5.s2_after(acc, 16, g3, a3, e3, ee3, g4, a4, e4, ee4,
          0n, p1, p2, p3, p4),
        FF5.step_hit_eq(q => FF5.s2_tail(g3, a3, e3, g4, a4, q), q => q,
          acc, 16, 32, g2, p0, r,
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g2), p0), eeq)))
    case False{}:
      +r = FF5.opt_cons(p1,
             FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))
      Equal.trans(U32,
        SolveFast.fb5_s2_c1(Nat.is_eq(Nat.add(1n, g2), p1), acc,
          Nat.add(1n, g2), g3, e3, g4, e4, p0, p1, p2, p3, p4),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g2, r), 16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.opt_cons(p0, FF5.consume_pool_of(g2, r))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g2, FF5.opt_cons(p0, r)),
            16, 32),
          FF5.s2_tail(g3, a3, e3, g4, a4,
            FF5.consume_pool_of(g2, FF5.opt_cons(p0, r))))),
        FF5.s2_c1_eq(Nat.is_eq(Nat.add(1n, g2), p1), acc, g2, g3, a3, e3, ee3,
          g4, a4, e4, ee4, p0, p1, p2, p3, p4, {==}),
        FF5.step_miss_eq(q => FF5.s2_tail(g3, a3, e3, g4, a4, q), q => q,
          acc, 16, 32, g2, p0, r,
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g2), p0), eeq)))

def FF5.fb5_s2_eq(+acc: U32, +g2: Nat, +a2: Nat, e2: Bool,
    +ee2: {e2 == Nat.is_eq(g2, a2) : Bool},
    +g3: Nat, +a3: Nat, +e3: Bool, +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) ->
  {SolveFast.fb5_s2(acc, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)
   == U32.or(acc,
        FF5.encode_tail3(
          SolveFast.feedback_go_fast(
            g2 <> (g3 <> (g4 <> Nil{})), a2 <> (a3 <> (a4 <> Nil{})),
            FF5.opt_pool(p0, p1, p2, p3, p4), e2))) : U32}:
  match e2:
    case True{}:
      %ee3 : {SolveFast.fb5_s3(U32.or(acc, 32), g3, e3, g4, e4,
                p0, p1, p2, p3, p4)
              == U32.or(acc, U32.or(32,
                   FF5.s2_tail(g3, a3, _, g4, a4,
                     FF5.opt_pool(p0, p1, p2, p3, p4)))) : U32}
      FF5.s2_after(acc, 32, g3, a3, e3, ee3, g4, a4, e4, ee4,
        p0, p1, p2, p3, p4)
    case False{}:
      %ee3 : {SolveFast.fb5_s2_c0(Nat.is_eq(Nat.add(1n, g2), p0), acc,
                Nat.add(1n, g2), g3, e3, g4, e4, p0, p1, p2, p3, p4)
              == U32.or(acc,
                   U32.or(
                     SolveFast.col_u32(
                       FF5.consume_color_of(g2, FF5.opt_pool(p0, p1, p2, p3, p4)),
                       16, 32),
                     FF5.s2_tail(g3, a3, _, g4, a4,
                       FF5.consume_pool_of(g2,
                         FF5.opt_pool(p0, p1, p2, p3, p4))))) : U32}
      FF5.s2_c0_eq(Nat.is_eq(Nat.add(1n, g2), p0), acc, g2, g3, a3, e3, ee3,
        g4, a4, e4, ee4, p0, p1, p2, p3, p4, {==})

# Step 1 (`fb5_s1_c4..c0`, `fb5_s1`)
def FF5.s1_tail(+g2: Nat, +a2: Nat, +e2: Bool, +g3: Nat, +a3: Nat,
    +g4: Nat, +a4: Nat, +pool: +List<Nat>) -> U32:
  FF5.encode_tail3(
    SolveFast.feedback_go_fast(
      g2 <> (g3 <> (g4 <> Nil{})), a2 <> (a3 <> (a4 <> Nil{})), pool, e2))

def FF5.s1_after(+acc: U32, +ybit: U32,
    +g2: Nat, +a2: Nat, +e2: Bool, +ee2: {e2 == Nat.is_eq(g2, a2) : Bool},
    +g3: Nat, +a3: Nat, +e3: Bool, +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) ->
  {SolveFast.fb5_s2(U32.or(acc, ybit), g2, e2, g3, e3, g4, e4,
     p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(ybit,
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_pool(p0, p1, p2, p3, p4)))) : U32}:
  +t3 = FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4, FF5.opt_pool(p0, p1, p2, p3, p4))
  Equal.trans(U32,
    SolveFast.fb5_s2(U32.or(acc, ybit), g2, e2, g3, e3, g4, e4,
      p0, p1, p2, p3, p4),
    U32.or(U32.or(acc, ybit), t3),
    U32.or(acc, U32.or(ybit, t3)),
    FF5.fb5_s2_eq(U32.or(acc, ybit), g2, a2, e2, ee2, g3, a3, e3, ee3,
      g4, a4, e4, ee4, p0, p1, p2, p3, p4),
    FF5.u32_or_assoc(acc, ybit, t3))

def FF5.s1_c4_eq(eq: Bool, +acc: U32, +g1: Nat,
    +g2: Nat, +a2: Nat, +e2: Bool, +ee2: {e2 == Nat.is_eq(g2, a2) : Bool},
    +g3: Nat, +a3: Nat, +e3: Bool, +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g1), p4) : Bool}) ->
  {SolveFast.fb5_s1_c4(eq, acc, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g1, FF5.opt_cons(p4, Nil{})),
            4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.opt_cons(p3, FF5.consume_pool_of(g1,
                FF5.opt_cons(p4, Nil{}))))))))) : U32}:
  match eq:
    case True{}:
      Equal.trans(U32,
        SolveFast.fb5_s2(U32.or(acc, 4), g2, e2, g3, e3, g4, e4,
          p0, p1, p2, p3, 0n),
        U32.or(acc, U32.or(4, FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
          FF5.opt_pool(p0, p1, p2, p3, 0n)))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g1, FF5.opt_cons(p4, Nil{})),
            4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.opt_cons(p3, FF5.consume_pool_of(g1,
                FF5.opt_cons(p4, Nil{}))))))))),
        FF5.s1_after(acc, 4, g2, a2, e2, ee2, g3, a3, e3, ee3, g4, a4, e4, ee4,
          p0, p1, p2, p3, 0n),
        FF5.step_hit_eq(q => FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
                 FF5.opt_cons(p3, q)))),
          acc, 4, 8, g1, p4, Nil{},
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g1), p4), eeq)))
    case False{}:
      +t3 = FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
              FF5.opt_pool(p0, p1, p2, p3, p4))
      Equal.trans(U32,
        SolveFast.fb5_s2(acc, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4),
        U32.or(acc, U32.or(0, t3)),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g1, FF5.opt_cons(p4, Nil{})),
            4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.opt_cons(p3, FF5.consume_pool_of(g1,
                FF5.opt_cons(p4, Nil{}))))))))),
        Equal.trans(U32,
          SolveFast.fb5_s2(acc, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4),
          U32.or(acc, t3),
          U32.or(acc, U32.or(0, t3)),
          FF5.fb5_s2_eq(acc, g2, a2, e2, ee2, g3, a3, e3, ee3, g4, a4, e4, ee4,
            p0, p1, p2, p3, p4),
          Equal.cong(U32, U32, x => U32.or(acc, x), t3, U32.or(0, t3),
            Equal.sym(U32, U32.or(0, t3), t3, FF5.u32_or_zero_l(t3)))),
        FF5.step_miss_eq(q => FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
                 FF5.opt_cons(p3, q)))),
          acc, 4, 8, g1, p4, Nil{},
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g1), p4), eeq)))

def FF5.s1_c3_eq(eq: Bool, +acc: U32, +g1: Nat,
    +g2: Nat, +a2: Nat, +e2: Bool, +ee2: {e2 == Nat.is_eq(g2, a2) : Bool},
    +g3: Nat, +a3: Nat, +e3: Bool, +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g1), p3) : Bool}) ->
  {SolveFast.fb5_s1_c3(eq, acc, Nat.add(1n, g1), g2, e2, g3, e3, g4, e4,
     p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g1, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))),
            4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.consume_pool_of(g1,
                FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))))))) : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p4, Nil{})
      Equal.trans(U32,
        SolveFast.fb5_s2(U32.or(acc, 4), g2, e2, g3, e3, g4, e4,
          p0, p1, p2, 0n, p4),
        U32.or(acc, U32.or(4, FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
          FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2, r)))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g1, FF5.opt_cons(p3, r)),
            4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.consume_pool_of(g1, FF5.opt_cons(p3, r)))))))),
        FF5.s1_after(acc, 4, g2, a2, e2, ee2, g3, a3, e3, ee3, g4, a4, e4, ee4,
          p0, p1, p2, 0n, p4),
        FF5.step_hit_eq(q => FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2, q))),
          acc, 4, 8, g1, p3, r,
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g1), p3), eeq)))
    case False{}:
      +r = FF5.opt_cons(p4, Nil{})
      Equal.trans(U32,
        SolveFast.fb5_s1_c4(Nat.is_eq(Nat.add(1n, g1), p4), acc, g2, e2,
          g3, e3, g4, e4, p0, p1, p2, p3, p4),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g1, r), 4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.opt_cons(p3, FF5.consume_pool_of(g1, r)))))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g1, FF5.opt_cons(p3, r)),
            4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.consume_pool_of(g1, FF5.opt_cons(p3, r)))))))),
        FF5.s1_c4_eq(Nat.is_eq(Nat.add(1n, g1), p4), acc, g1, g2, a2, e2, ee2,
          g3, a3, e3, ee3, g4, a4, e4, ee4, p0, p1, p2, p3, p4, {==}),
        FF5.step_miss_eq(q => FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2, q))),
          acc, 4, 8, g1, p3, r,
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g1), p3), eeq)))

def FF5.s1_c2_eq(eq: Bool, +acc: U32, +g1: Nat,
    +g2: Nat, +a2: Nat, +e2: Bool, +ee2: {e2 == Nat.is_eq(g2, a2) : Bool},
    +g3: Nat, +a3: Nat, +e3: Bool, +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g1), p2) : Bool}) ->
  {SolveFast.fb5_s1_c2(eq, acc, Nat.add(1n, g1), g2, e2, g3, e3, g4, e4,
     p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g1,
              FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))),
            4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1,
              FF5.consume_pool_of(g1,
                FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))))))))
   : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))
      Equal.trans(U32,
        SolveFast.fb5_s2(U32.or(acc, 4), g2, e2, g3, e3, g4, e4,
          p0, p1, 0n, p3, p4),
        U32.or(acc, U32.or(4, FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
          FF5.opt_cons(p0, FF5.opt_cons(p1, r))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g1, FF5.opt_cons(p2, r)),
            4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1,
              FF5.consume_pool_of(g1, FF5.opt_cons(p2, r))))))),
        FF5.s1_after(acc, 4, g2, a2, e2, ee2, g3, a3, e3, ee3, g4, a4, e4, ee4,
          p0, p1, 0n, p3, p4),
        FF5.step_hit_eq(q => FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, q)),
          acc, 4, 8, g1, p2, r,
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g1), p2), eeq)))
    case False{}:
      +r = FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))
      Equal.trans(U32,
        SolveFast.fb5_s1_c3(Nat.is_eq(Nat.add(1n, g1), p3), acc,
          Nat.add(1n, g1), g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g1, r), 4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1,
              FF5.opt_cons(p2, FF5.consume_pool_of(g1, r))))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g1, FF5.opt_cons(p2, r)),
            4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1,
              FF5.consume_pool_of(g1, FF5.opt_cons(p2, r))))))),
        FF5.s1_c3_eq(Nat.is_eq(Nat.add(1n, g1), p3), acc, g1, g2, a2, e2, ee2,
          g3, a3, e3, ee3, g4, a4, e4, ee4, p0, p1, p2, p3, p4, {==}),
        FF5.step_miss_eq(q => FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, q)),
          acc, 4, 8, g1, p2, r,
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g1), p2), eeq)))

def FF5.s1_c1_eq(eq: Bool, +acc: U32, +g1: Nat,
    +g2: Nat, +a2: Nat, +e2: Bool, +ee2: {e2 == Nat.is_eq(g2, a2) : Bool},
    +g3: Nat, +a3: Nat, +e3: Bool, +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g1), p1) : Bool}) ->
  {SolveFast.fb5_s1_c1(eq, acc, Nat.add(1n, g1), g2, e2, g3, e3, g4, e4,
     p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g1,
              FF5.opt_cons(p1,
                FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))),
            4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_cons(p0,
              FF5.consume_pool_of(g1,
                FF5.opt_cons(p1,
                  FF5.opt_cons(p2, FF5.opt_cons(p3,
                    FF5.opt_cons(p4, Nil{}))))))))) : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))
      Equal.trans(U32,
        SolveFast.fb5_s2(U32.or(acc, 4), g2, e2, g3, e3, g4, e4,
          p0, 0n, p2, p3, p4),
        U32.or(acc, U32.or(4, FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
          FF5.opt_cons(p0, r)))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g1, FF5.opt_cons(p1, r)),
            4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.consume_pool_of(g1, FF5.opt_cons(p1, r)))))),
        FF5.s1_after(acc, 4, g2, a2, e2, ee2, g3, a3, e3, ee3, g4, a4, e4, ee4,
          p0, 0n, p2, p3, p4),
        FF5.step_hit_eq(q => FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4, q),
          q => FF5.opt_cons(p0, q),
          acc, 4, 8, g1, p1, r,
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g1), p1), eeq)))
    case False{}:
      +r = FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))
      Equal.trans(U32,
        SolveFast.fb5_s1_c2(Nat.is_eq(Nat.add(1n, g1), p2), acc,
          Nat.add(1n, g1), g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g1, r), 4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.consume_pool_of(g1, r)))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g1, FF5.opt_cons(p1, r)),
            4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.consume_pool_of(g1, FF5.opt_cons(p1, r)))))),
        FF5.s1_c2_eq(Nat.is_eq(Nat.add(1n, g1), p2), acc, g1, g2, a2, e2, ee2,
          g3, a3, e3, ee3, g4, a4, e4, ee4, p0, p1, p2, p3, p4, {==}),
        FF5.step_miss_eq(q => FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4, q),
          q => FF5.opt_cons(p0, q),
          acc, 4, 8, g1, p1, r,
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g1), p1), eeq)))

def FF5.s1_c0_eq(eq: Bool, +acc: U32, +g1: Nat,
    +g2: Nat, +a2: Nat, +e2: Bool, +ee2: {e2 == Nat.is_eq(g2, a2) : Bool},
    +g3: Nat, +a3: Nat, +e3: Bool, +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g1), p0) : Bool}) ->
  {SolveFast.fb5_s1_c0(eq, acc, Nat.add(1n, g1), g2, e2, g3, e3, g4, e4,
     p0, p1, p2, p3, p4)
   == U32.or(acc,
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g1, FF5.opt_pool(p0, p1, p2, p3, p4)),
            4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.consume_pool_of(g1, FF5.opt_pool(p0, p1, p2, p3, p4))))) : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p1,
             FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))
      Equal.trans(U32,
        SolveFast.fb5_s2(U32.or(acc, 4), g2, e2, g3, e3, g4, e4,
          0n, p1, p2, p3, p4),
        U32.or(acc, U32.or(4, FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4, r))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g1, FF5.opt_cons(p0, r)),
            4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.consume_pool_of(g1, FF5.opt_cons(p0, r))))),
        FF5.s1_after(acc, 4, g2, a2, e2, ee2, g3, a3, e3, ee3, g4, a4, e4, ee4,
          0n, p1, p2, p3, p4),
        FF5.step_hit_eq(q => FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4, q), q => q,
          acc, 4, 8, g1, p0, r,
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g1), p0), eeq)))
    case False{}:
      +r = FF5.opt_cons(p1,
             FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))
      Equal.trans(U32,
        SolveFast.fb5_s1_c1(Nat.is_eq(Nat.add(1n, g1), p1), acc,
          Nat.add(1n, g1), g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g1, r), 4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.consume_pool_of(g1, r))))),
        U32.or(acc, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g1, FF5.opt_cons(p0, r)),
            4, 8),
          FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4,
            FF5.consume_pool_of(g1, FF5.opt_cons(p0, r))))),
        FF5.s1_c1_eq(Nat.is_eq(Nat.add(1n, g1), p1), acc, g1, g2, a2, e2, ee2,
          g3, a3, e3, ee3, g4, a4, e4, ee4, p0, p1, p2, p3, p4, {==}),
        FF5.step_miss_eq(q => FF5.s1_tail(g2, a2, e2, g3, a3, g4, a4, q), q => q,
          acc, 4, 8, g1, p0, r,
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g1), p0), eeq)))

def FF5.fb5_s1_eq(+acc: U32, +g1: Nat, +a1: Nat, e1: Bool,
    +ee1: {e1 == Nat.is_eq(g1, a1) : Bool},
    +g2: Nat, +a2: Nat, +e2: Bool, +ee2: {e2 == Nat.is_eq(g2, a2) : Bool},
    +g3: Nat, +a3: Nat, +e3: Bool, +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) ->
  {SolveFast.fb5_s1(acc, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)
   == U32.or(acc,
        FF5.encode_tail4(
          SolveFast.feedback_go_fast(
            g1 <> (g2 <> (g3 <> (g4 <> Nil{}))),
            a1 <> (a2 <> (a3 <> (a4 <> Nil{}))),
            FF5.opt_pool(p0, p1, p2, p3, p4), e1))) : U32}:
  match e1:
    case True{}:
      %ee2 : {SolveFast.fb5_s2(U32.or(acc, 8), g2, e2, g3, e3, g4, e4,
                p0, p1, p2, p3, p4)
              == U32.or(acc, U32.or(8,
                   FF5.s1_tail(g2, a2, _, g3, a3, g4, a4,
                     FF5.opt_pool(p0, p1, p2, p3, p4)))) : U32}
      FF5.s1_after(acc, 8, g2, a2, e2, ee2, g3, a3, e3, ee3, g4, a4, e4, ee4,
        p0, p1, p2, p3, p4)
    case False{}:
      %ee2 : {SolveFast.fb5_s1_c0(Nat.is_eq(Nat.add(1n, g1), p0), acc,
                Nat.add(1n, g1), g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)
              == U32.or(acc,
                   U32.or(
                     SolveFast.col_u32(
                       FF5.consume_color_of(g1, FF5.opt_pool(p0, p1, p2, p3, p4)),
                       4, 8),
                     FF5.s1_tail(g2, a2, _, g3, a3, g4, a4,
                       FF5.consume_pool_of(g1,
                         FF5.opt_pool(p0, p1, p2, p3, p4))))) : U32}
      FF5.s1_c0_eq(Nat.is_eq(Nat.add(1n, g1), p0), acc, g1, g2, a2, e2, ee2,
        g3, a3, e3, ee3, g4, a4, e4, ee4, p0, p1, p2, p3, p4, {==})

# Step 0 (`fb5_s0_c4..c0`, `fb5_s0`)
def FF5.s0_tail(+g1: Nat, +a1: Nat, +e1: Bool, +g2: Nat, +a2: Nat,
    +g3: Nat, +a3: Nat, +g4: Nat, +a4: Nat, +pool: +List<Nat>) -> U32:
  FF5.encode_tail4(
    SolveFast.feedback_go_fast(
      g1 <> (g2 <> (g3 <> (g4 <> Nil{}))),
      a1 <> (a2 <> (a3 <> (a4 <> Nil{}))), pool, e1))

def FF5.s0_after(+ybit: U32,
    +g1: Nat, +a1: Nat, +e1: Bool, +ee1: {e1 == Nat.is_eq(g1, a1) : Bool},
    +g2: Nat, +a2: Nat, +e2: Bool, +ee2: {e2 == Nat.is_eq(g2, a2) : Bool},
    +g3: Nat, +a3: Nat, +e3: Bool, +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) ->
  {SolveFast.fb5_s1(ybit, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)
   == U32.or(0,
        U32.or(ybit,
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.opt_pool(p0, p1, p2, p3, p4)))) : U32}:
  +t4 = FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
          FF5.opt_pool(p0, p1, p2, p3, p4))
  Equal.trans(U32,
    SolveFast.fb5_s1(ybit, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4),
    U32.or(ybit, t4),
    U32.or(0, U32.or(ybit, t4)),
    FF5.fb5_s1_eq(ybit, g1, a1, e1, ee1, g2, a2, e2, ee2, g3, a3, e3, ee3,
      g4, a4, e4, ee4, p0, p1, p2, p3, p4),
    Equal.sym(U32, U32.or(0, U32.or(ybit, t4)), U32.or(ybit, t4),
      FF5.u32_or_zero_l(U32.or(ybit, t4))))

def FF5.s0_c4_eq(eq: Bool, +g0: Nat,
    +g1: Nat, +a1: Nat, +e1: Bool, +ee1: {e1 == Nat.is_eq(g1, a1) : Bool},
    +g2: Nat, +a2: Nat, +e2: Bool, +ee2: {e2 == Nat.is_eq(g2, a2) : Bool},
    +g3: Nat, +a3: Nat, +e3: Bool, +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g0), p4) : Bool}) ->
  {SolveFast.fb5_s0_c4(eq, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)
   == U32.or(0,
        U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g0, FF5.opt_cons(p4, Nil{})),
            1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.opt_cons(p3, FF5.consume_pool_of(g0,
                FF5.opt_cons(p4, Nil{}))))))))) : U32}:
  match eq:
    case True{}:
      Equal.trans(U32,
        SolveFast.fb5_s1(1, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, 0n),
        U32.or(0, U32.or(1, FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
          FF5.opt_pool(p0, p1, p2, p3, 0n)))),
        U32.or(0, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g0, FF5.opt_cons(p4, Nil{})),
            1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.opt_cons(p3, FF5.consume_pool_of(g0,
                FF5.opt_cons(p4, Nil{}))))))))),
        FF5.s0_after(1, g1, a1, e1, ee1, g2, a2, e2, ee2, g3, a3, e3, ee3,
          g4, a4, e4, ee4, p0, p1, p2, p3, 0n),
        FF5.step_hit_eq(q => FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
                 FF5.opt_cons(p3, q)))),
          0, 1, 2, g0, p4, Nil{},
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g0), p4), eeq)))
    case False{}:
      Equal.trans(U32,
        SolveFast.fb5_s1(0, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4),
        U32.or(0, U32.or(0, FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
          FF5.opt_pool(p0, p1, p2, p3, p4)))),
        U32.or(0, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g0, FF5.opt_cons(p4, Nil{})),
            1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.opt_cons(p3, FF5.consume_pool_of(g0,
                FF5.opt_cons(p4, Nil{}))))))))),
        FF5.s0_after(0, g1, a1, e1, ee1, g2, a2, e2, ee2, g3, a3, e3, ee3,
          g4, a4, e4, ee4, p0, p1, p2, p3, p4),
        FF5.step_miss_eq(q => FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
                 FF5.opt_cons(p3, q)))),
          0, 1, 2, g0, p4, Nil{},
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g0), p4), eeq)))

def FF5.s0_c3_eq(eq: Bool, +g0: Nat,
    +g1: Nat, +a1: Nat, +e1: Bool, +ee1: {e1 == Nat.is_eq(g1, a1) : Bool},
    +g2: Nat, +a2: Nat, +e2: Bool, +ee2: {e2 == Nat.is_eq(g2, a2) : Bool},
    +g3: Nat, +a3: Nat, +e3: Bool, +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g0), p3) : Bool}) ->
  {SolveFast.fb5_s0_c3(eq, Nat.add(1n, g0), g1, e1, g2, e2, g3, e3, g4, e4,
     p0, p1, p2, p3, p4)
   == U32.or(0,
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g0, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))),
            1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.consume_pool_of(g0,
                FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))))))) : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p4, Nil{})
      Equal.trans(U32,
        SolveFast.fb5_s1(1, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, 0n, p4),
        U32.or(0, U32.or(1, FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
          FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2, r)))))),
        U32.or(0, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g0, FF5.opt_cons(p3, r)),
            1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.consume_pool_of(g0, FF5.opt_cons(p3, r)))))))),
        FF5.s0_after(1, g1, a1, e1, ee1, g2, a2, e2, ee2, g3, a3, e3, ee3,
          g4, a4, e4, ee4, p0, p1, p2, 0n, p4),
        FF5.step_hit_eq(q => FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2, q))),
          0, 1, 2, g0, p3, r,
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g0), p3), eeq)))
    case False{}:
      +r = FF5.opt_cons(p4, Nil{})
      Equal.trans(U32,
        SolveFast.fb5_s0_c4(Nat.is_eq(Nat.add(1n, g0), p4), g1, e1, g2, e2,
          g3, e3, g4, e4, p0, p1, p2, p3, p4),
        U32.or(0, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g0, r), 1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.opt_cons(p3, FF5.consume_pool_of(g0, r)))))))),
        U32.or(0, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g0, FF5.opt_cons(p3, r)),
            1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2,
              FF5.consume_pool_of(g0, FF5.opt_cons(p3, r)))))))),
        FF5.s0_c4_eq(Nat.is_eq(Nat.add(1n, g0), p4), g0, g1, a1, e1, ee1,
          g2, a2, e2, ee2, g3, a3, e3, ee3, g4, a4, e4, ee4,
          p0, p1, p2, p3, p4, {==}),
        FF5.step_miss_eq(q => FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.opt_cons(p2, q))),
          0, 1, 2, g0, p3, r,
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g0), p3), eeq)))

def FF5.s0_c2_eq(eq: Bool, +g0: Nat,
    +g1: Nat, +a1: Nat, +e1: Bool, +ee1: {e1 == Nat.is_eq(g1, a1) : Bool},
    +g2: Nat, +a2: Nat, +e2: Bool, +ee2: {e2 == Nat.is_eq(g2, a2) : Bool},
    +g3: Nat, +a3: Nat, +e3: Bool, +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g0), p2) : Bool}) ->
  {SolveFast.fb5_s0_c2(eq, Nat.add(1n, g0), g1, e1, g2, e2, g3, e3, g4, e4,
     p0, p1, p2, p3, p4)
   == U32.or(0,
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g0,
              FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))),
            1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1,
              FF5.consume_pool_of(g0,
                FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))))))))
   : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))
      Equal.trans(U32,
        SolveFast.fb5_s1(1, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, 0n, p3, p4),
        U32.or(0, U32.or(1, FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
          FF5.opt_cons(p0, FF5.opt_cons(p1, r))))),
        U32.or(0, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g0, FF5.opt_cons(p2, r)),
            1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1,
              FF5.consume_pool_of(g0, FF5.opt_cons(p2, r))))))),
        FF5.s0_after(1, g1, a1, e1, ee1, g2, a2, e2, ee2, g3, a3, e3, ee3,
          g4, a4, e4, ee4, p0, p1, 0n, p3, p4),
        FF5.step_hit_eq(q => FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, q)),
          0, 1, 2, g0, p2, r,
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g0), p2), eeq)))
    case False{}:
      +r = FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))
      Equal.trans(U32,
        SolveFast.fb5_s0_c3(Nat.is_eq(Nat.add(1n, g0), p3), Nat.add(1n, g0),
          g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4),
        U32.or(0, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g0, r), 1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1,
              FF5.opt_cons(p2, FF5.consume_pool_of(g0, r))))))),
        U32.or(0, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g0, FF5.opt_cons(p2, r)),
            1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1,
              FF5.consume_pool_of(g0, FF5.opt_cons(p2, r))))))),
        FF5.s0_c3_eq(Nat.is_eq(Nat.add(1n, g0), p3), g0, g1, a1, e1, ee1,
          g2, a2, e2, ee2, g3, a3, e3, ee3, g4, a4, e4, ee4,
          p0, p1, p2, p3, p4, {==}),
        FF5.step_miss_eq(q => FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4, q),
          q => FF5.opt_cons(p0, FF5.opt_cons(p1, q)),
          0, 1, 2, g0, p2, r,
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g0), p2), eeq)))

def FF5.s0_c1_eq(eq: Bool, +g0: Nat,
    +g1: Nat, +a1: Nat, +e1: Bool, +ee1: {e1 == Nat.is_eq(g1, a1) : Bool},
    +g2: Nat, +a2: Nat, +e2: Bool, +ee2: {e2 == Nat.is_eq(g2, a2) : Bool},
    +g3: Nat, +a3: Nat, +e3: Bool, +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g0), p1) : Bool}) ->
  {SolveFast.fb5_s0_c1(eq, Nat.add(1n, g0), g1, e1, g2, e2, g3, e3, g4, e4,
     p0, p1, p2, p3, p4)
   == U32.or(0,
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g0,
              FF5.opt_cons(p1,
                FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))),
            1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.opt_cons(p0,
              FF5.consume_pool_of(g0,
                FF5.opt_cons(p1,
                  FF5.opt_cons(p2, FF5.opt_cons(p3,
                    FF5.opt_cons(p4, Nil{}))))))))) : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))
      Equal.trans(U32,
        SolveFast.fb5_s1(1, g1, e1, g2, e2, g3, e3, g4, e4, p0, 0n, p2, p3, p4),
        U32.or(0, U32.or(1, FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
          FF5.opt_cons(p0, r)))),
        U32.or(0, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g0, FF5.opt_cons(p1, r)),
            1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.consume_pool_of(g0, FF5.opt_cons(p1, r)))))),
        FF5.s0_after(1, g1, a1, e1, ee1, g2, a2, e2, ee2, g3, a3, e3, ee3,
          g4, a4, e4, ee4, p0, 0n, p2, p3, p4),
        FF5.step_hit_eq(q => FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4, q),
          q => FF5.opt_cons(p0, q),
          0, 1, 2, g0, p1, r,
          Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g0), p1), eeq)))
    case False{}:
      +r = FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{})))
      Equal.trans(U32,
        SolveFast.fb5_s0_c2(Nat.is_eq(Nat.add(1n, g0), p2), Nat.add(1n, g0),
          g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4),
        U32.or(0, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g0, r), 1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.opt_cons(p1, FF5.consume_pool_of(g0, r)))))),
        U32.or(0, U32.or(
          SolveFast.col_u32(FF5.consume_color_of(g0, FF5.opt_cons(p1, r)),
            1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.opt_cons(p0, FF5.consume_pool_of(g0, FF5.opt_cons(p1, r)))))),
        FF5.s0_c2_eq(Nat.is_eq(Nat.add(1n, g0), p2), g0, g1, a1, e1, ee1,
          g2, a2, e2, ee2, g3, a3, e3, ee3, g4, a4, e4, ee4,
          p0, p1, p2, p3, p4, {==}),
        FF5.step_miss_eq(q => FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4, q),
          q => FF5.opt_cons(p0, q),
          0, 1, 2, g0, p1, r,
          Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g0), p1), eeq)))

def FF5.s0_c0_eq(eq: Bool, +g0: Nat,
    +g1: Nat, +a1: Nat, +e1: Bool, +ee1: {e1 == Nat.is_eq(g1, a1) : Bool},
    +g2: Nat, +a2: Nat, +e2: Bool, +ee2: {e2 == Nat.is_eq(g2, a2) : Bool},
    +g3: Nat, +a3: Nat, +e3: Bool, +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat,
    +eeq: {eq == Nat.is_eq(Nat.add(1n, g0), p0) : Bool}) ->
  {SolveFast.fb5_s0_c0(eq, Nat.add(1n, g0), g1, e1, g2, e2, g3, e3, g4, e4,
     p0, p1, p2, p3, p4)
   == U32.or(
        SolveFast.col_u32(
          FF5.consume_color_of(g0, FF5.opt_pool(p0, p1, p2, p3, p4)),
          1, 2),
        FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
          FF5.consume_pool_of(g0, FF5.opt_pool(p0, p1, p2, p3, p4)))) : U32}:
  match eq:
    case True{}:
      +r = FF5.opt_cons(p1,
             FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))
      +res : U32 =
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g0, FF5.opt_pool(p0, p1, p2, p3, p4)), 1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.consume_pool_of(g0, FF5.opt_pool(p0, p1, p2, p3, p4))))
      Equal.trans(U32,
        SolveFast.fb5_s1(1, g1, e1, g2, e2, g3, e3, g4, e4, 0n, p1, p2, p3, p4),
        U32.or(0, res),
        res,
        Equal.trans(U32,
          SolveFast.fb5_s1(1, g1, e1, g2, e2, g3, e3, g4, e4,
            0n, p1, p2, p3, p4),
          U32.or(0, U32.or(1, FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4, r))),
          U32.or(0, res),
          FF5.s0_after(1, g1, a1, e1, ee1, g2, a2, e2, ee2, g3, a3, e3, ee3,
            g4, a4, e4, ee4, 0n, p1, p2, p3, p4),
          FF5.step_hit_eq(q => FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4, q),
            q => q, 0, 1, 2, g0, p0, r,
            Equal.sym(Bool, True{}, Nat.is_eq(Nat.add(1n, g0), p0), eeq))),
        FF5.u32_or_zero_l(res))
    case False{}:
      +r = FF5.opt_cons(p1,
             FF5.opt_cons(p2, FF5.opt_cons(p3, FF5.opt_cons(p4, Nil{}))))
      +res : U32 =
        U32.or(
          SolveFast.col_u32(
            FF5.consume_color_of(g0, FF5.opt_pool(p0, p1, p2, p3, p4)), 1, 2),
          FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
            FF5.consume_pool_of(g0, FF5.opt_pool(p0, p1, p2, p3, p4))))
      Equal.trans(U32,
        SolveFast.fb5_s0_c1(Nat.is_eq(Nat.add(1n, g0), p1), Nat.add(1n, g0),
          g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4),
        U32.or(0, res),
        res,
        Equal.trans(U32,
          SolveFast.fb5_s0_c1(Nat.is_eq(Nat.add(1n, g0), p1), Nat.add(1n, g0),
            g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4),
          U32.or(0, U32.or(
            SolveFast.col_u32(FF5.consume_color_of(g0, r), 1, 2),
            FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4,
              FF5.opt_cons(p0, FF5.consume_pool_of(g0, r))))),
          U32.or(0, res),
          FF5.s0_c1_eq(Nat.is_eq(Nat.add(1n, g0), p1), g0, g1, a1, e1, ee1,
            g2, a2, e2, ee2, g3, a3, e3, ee3, g4, a4, e4, ee4,
            p0, p1, p2, p3, p4, {==}),
          FF5.step_miss_eq(q => FF5.s0_tail(g1, a1, e1, g2, a2, g3, a3, g4, a4, q),
            q => q, 0, 1, 2, g0, p0, r,
            Equal.sym(Bool, False{}, Nat.is_eq(Nat.add(1n, g0), p0), eeq))),
        FF5.u32_or_zero_l(res))

def FF5.fb5_s0_eq(+g0: Nat, +a0: Nat, e0: Bool,
    +ee0: {e0 == Nat.is_eq(g0, a0) : Bool},
    +g1: Nat, +a1: Nat, +e1: Bool, +ee1: {e1 == Nat.is_eq(g1, a1) : Bool},
    +g2: Nat, +a2: Nat, +e2: Bool, +ee2: {e2 == Nat.is_eq(g2, a2) : Bool},
    +g3: Nat, +a3: Nat, +e3: Bool, +ee3: {e3 == Nat.is_eq(g3, a3) : Bool},
    +g4: Nat, +a4: Nat, +e4: Bool, +ee4: {e4 == Nat.is_eq(g4, a4) : Bool},
    +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) ->
  {SolveFast.fb5_s0(g0, e0, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)
   == FF5.encode_tail5(
        SolveFast.feedback_go_fast(
          g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
          a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{})))),
          FF5.opt_pool(p0, p1, p2, p3, p4), e0)) : U32}:
  match e0:
    case True{}:
      %ee1 : {SolveFast.fb5_s1(2, g1, e1, g2, e2, g3, e3, g4, e4,
                p0, p1, p2, p3, p4)
              == U32.or(2,
                   FF5.s0_tail(g1, a1, _, g2, a2, g3, a3, g4, a4,
                     FF5.opt_pool(p0, p1, p2, p3, p4))) : U32}
      FF5.fb5_s1_eq(2, g1, a1, e1, ee1, g2, a2, e2, ee2, g3, a3, e3, ee3,
        g4, a4, e4, ee4, p0, p1, p2, p3, p4)
    case False{}:
      %ee1 : {SolveFast.fb5_s0_c0(Nat.is_eq(Nat.add(1n, g0), p0),
                Nat.add(1n, g0), g1, e1, g2, e2, g3, e3, g4, e4,
                p0, p1, p2, p3, p4)
              == U32.or(
                   SolveFast.col_u32(
                     FF5.consume_color_of(g0, FF5.opt_pool(p0, p1, p2, p3, p4)),
                     1, 2),
                   FF5.s0_tail(g1, a1, _, g2, a2, g3, a3, g4, a4,
                     FF5.consume_pool_of(g0,
                       FF5.opt_pool(p0, p1, p2, p3, p4)))) : U32}
      FF5.s0_c0_eq(Nat.is_eq(Nat.add(1n, g0), p0), g0, g1, a1, e1, ee1,
        g2, a2, e2, ee2, g3, a3, e3, ee3, g4, a4, e4, ee4,
        p0, p1, p2, p3, p4, {==})

# `feedback_go_fast` on 5-letter words always produces a 5-element feedback
# list whose `encode_tail5` equals `encode_fb5_list`.
def FF5.is_len1(+xs: +List<Feedback.Color>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{c, t}:
      match t:
        case Nil{}:
          True{}
        case Con{c2, t2}:
          False{}

def FF5.is_len2(+xs: +List<Feedback.Color>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{c, t}:
      FF5.is_len1(t)

def FF5.is_len3(+xs: +List<Feedback.Color>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{c, t}:
      FF5.is_len2(t)

def FF5.is_len4(+xs: +List<Feedback.Color>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{c, t}:
      FF5.is_len3(t)

def FF5.fb_go_len1(+g4: Nat, +a4: Nat, +pool: +List<Nat>, e4: Bool) ->
  {FF5.is_len1(SolveFast.feedback_go_fast(g4 <> Nil{}, a4 <> Nil{}, pool, e4))
   == True{} : Bool}:
  match e4:
    case True{}:
      {==}
    case False{}:
      {==}

def FF5.fb_go_len2(+g3: Nat, +a3: Nat, +g4: Nat, +a4: Nat, +pool: +List<Nat>,
    e3: Bool) ->
  {FF5.is_len2(
     SolveFast.feedback_go_fast(g3 <> (g4 <> Nil{}), a3 <> (a4 <> Nil{}),
       pool, e3)) == True{} : Bool}:
  match e3:
    case True{}:
      FF5.fb_go_len1(g4, a4, pool, Nat.is_eq(g4, a4))
    case False{}:
      FF5.fb_go_len1(g4, a4, FF5.consume_pool_of(g3, pool), Nat.is_eq(g4, a4))

def FF5.fb_go_len3(+g2: Nat, +a2: Nat, +g3: Nat, +a3: Nat, +g4: Nat, +a4: Nat,
    +pool: +List<Nat>, e2: Bool) ->
  {FF5.is_len3(
     SolveFast.feedback_go_fast(
       g2 <> (g3 <> (g4 <> Nil{})), a2 <> (a3 <> (a4 <> Nil{})), pool, e2))
   == True{} : Bool}:
  match e2:
    case True{}:
      FF5.fb_go_len2(g3, a3, g4, a4, pool, Nat.is_eq(g3, a3))
    case False{}:
      FF5.fb_go_len2(g3, a3, g4, a4, FF5.consume_pool_of(g2, pool),
        Nat.is_eq(g3, a3))

def FF5.fb_go_len4(+g1: Nat, +a1: Nat, +g2: Nat, +a2: Nat, +g3: Nat, +a3: Nat,
    +g4: Nat, +a4: Nat, +pool: +List<Nat>, e1: Bool) ->
  {FF5.is_len4(
     SolveFast.feedback_go_fast(
       g1 <> (g2 <> (g3 <> (g4 <> Nil{}))),
       a1 <> (a2 <> (a3 <> (a4 <> Nil{}))), pool, e1)) == True{} : Bool}:
  match e1:
    case True{}:
      FF5.fb_go_len3(g2, a2, g3, a3, g4, a4, pool, Nat.is_eq(g2, a2))
    case False{}:
      FF5.fb_go_len3(g2, a2, g3, a3, g4, a4, FF5.consume_pool_of(g1, pool),
        Nat.is_eq(g2, a2))

def FF5.is_fb5_cons(+c0: Feedback.Color, +xs: +List<Feedback.Color>,
    +h4: {FF5.is_len4(xs) == True{} : Bool}) ->
  {FF5.is_fb5(c0 <> xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      h4
    case Con{c1, t2}:
      match t2:
        case Nil{}:
          h4
        case Con{c2, t3}:
          match t3:
            case Nil{}:
              h4
            case Con{c3, t4}:
              match t4:
                case Nil{}:
                  h4
                case Con{c4, t5}:
                  match t5:
                    case Nil{}:
                      {==}
                    case Con{c5, t6}:
                      h4

def FF5.fb_go_len5(+g0: Nat, +a0: Nat, +g1: Nat, +a1: Nat, +g2: Nat, +a2: Nat,
    +g3: Nat, +a3: Nat, +g4: Nat, +a4: Nat, +pool: +List<Nat>, e0: Bool) ->
  {FF5.is_fb5(
     SolveFast.feedback_go_fast(
       g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
       a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{})))), pool, e0))
   == True{} : Bool}:
  match e0:
    case True{}:
      FF5.is_fb5_cons(Feedback.Green{},
        SolveFast.feedback_go_fast(
          g1 <> (g2 <> (g3 <> (g4 <> Nil{}))),
          a1 <> (a2 <> (a3 <> (a4 <> Nil{}))), pool, Nat.is_eq(g1, a1)),
        FF5.fb_go_len4(g1, a1, g2, a2, g3, a3, g4, a4, pool, Nat.is_eq(g1, a1)))
    case False{}:
      FF5.is_fb5_cons(FF5.consume_color_of(g0, pool),
        SolveFast.feedback_go_fast(
          g1 <> (g2 <> (g3 <> (g4 <> Nil{}))),
          a1 <> (a2 <> (a3 <> (a4 <> Nil{}))),
          FF5.consume_pool_of(g0, pool), Nat.is_eq(g1, a1)),
        FF5.fb_go_len4(g1, a1, g2, a2, g3, a3, g4, a4,
          FF5.consume_pool_of(g0, pool), Nat.is_eq(g1, a1)))

def FF5.encode_tail5_of_fb5(+fb: +List<Feedback.Color>,
    +h5: {FF5.is_fb5(fb) == True{} : Bool}) ->
  {FF5.encode_tail5(fb) == FF5.encode_fb5_list(fb) : U32}:
  match fb:
    case Nil{}:
      Empty.absurd(
        {FF5.encode_tail5(Nil{}) == FF5.encode_fb5_list(Nil{}) : U32},
        Logic.Proof.false_ne_true(h5))
    case Con{+c0, +t1}:
      match t1:
        case Nil{}:
          Empty.absurd(
            {FF5.encode_tail5(c0 <> Nil{}) == FF5.encode_fb5_list(c0 <> Nil{})
             : U32},
            Logic.Proof.false_ne_true(h5))
        case Con{+c1, +t2}:
          match t2:
            case Nil{}:
              Empty.absurd(
                {FF5.encode_tail5(c0 <> (c1 <> Nil{}))
                 == FF5.encode_fb5_list(c0 <> (c1 <> Nil{})) : U32},
                Logic.Proof.false_ne_true(h5))
            case Con{+c2, +t3}:
              match t3:
                case Nil{}:
                  Empty.absurd(
                    {FF5.encode_tail5(c0 <> (c1 <> (c2 <> Nil{})))
                     == FF5.encode_fb5_list(c0 <> (c1 <> (c2 <> Nil{}))) : U32},
                    Logic.Proof.false_ne_true(h5))
                case Con{+c3, +t4}:
                  match t4:
                    case Nil{}:
                      Empty.absurd(
                        {FF5.encode_tail5(c0 <> (c1 <> (c2 <> (c3 <> Nil{}))))
                         == FF5.encode_fb5_list(
                              c0 <> (c1 <> (c2 <> (c3 <> Nil{})))) : U32},
                        Logic.Proof.false_ne_true(h5))
                    case Con{+c4, +t5}:
                      match t5:
                        case Nil{}:
                          {==}
                        case Con{+c5, +t6}:
                          Empty.absurd(
                            {FF5.encode_tail5(
                               c0 <> (c1 <> (c2 <> (c3 <> (c4 <> (c5 <> t6))))))
                             == FF5.encode_fb5_list(
                                  c0 <> (c1 <> (c2 <> (c3 <> (c4 <> (c5 <> t6))))))
                             : U32},
                            Logic.Proof.false_ne_true(h5))

# Top-level theorems for `SolveFast.feedback_code5`.
def FF5.feedback_len5(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +a0: Nat, +a1: Nat, +a2: Nat, +a3: Nat, +a4: Nat) ->
  {FF5.is_fb5(
     Feedback.feedback(
       g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
       a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{})))))) == True{} : Bool}:
  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
  +aw : +List<Nat> = a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))
  Equal.trans(Bool,
    FF5.is_fb5(Feedback.feedback(gw, aw)),
    FF5.is_fb5(SolveFast.feedback_fast(gw, aw)),
    True{},
    Equal.cong(+List<Feedback.Color>, Bool, f => FF5.is_fb5(f),
      Feedback.feedback(gw, aw), SolveFast.feedback_fast(gw, aw),
      Equal.sym(+List<Feedback.Color>, SolveFast.feedback_fast(gw, aw),
        Feedback.feedback(gw, aw), FG.FG.feedback_eq(gw, aw))),
    FF5.fb_go_len5(g0, a0, g1, a1, g2, a2, g3, a3, g4, a4,
      SolveFast.non_green_fast(gw, aw), Nat.is_eq(g0, a0)))

def FF5.feedback_code5_eq(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +a0: Nat, +a1: Nat, +a2: Nat, +a3: Nat, +a4: Nat) ->
  {SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4)
   == FF5.encode_fb5_list(
        Feedback.feedback(
          g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
          a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{})))))) : U32}:
  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
  +aw : +List<Nat> = a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))
  +p0 = SolveFast.ng_slot(a0, Nat.is_eq(g0, a0))
  +p1 = SolveFast.ng_slot(a1, Nat.is_eq(g1, a1))
  +p2 = SolveFast.ng_slot(a2, Nat.is_eq(g2, a2))
  +p3 = SolveFast.ng_slot(a3, Nat.is_eq(g3, a3))
  +p4 = SolveFast.ng_slot(a4, Nat.is_eq(g4, a4))
  +e1 : {SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4)
         == FF5.encode_tail5(
              SolveFast.feedback_go_fast(gw, aw,
                FF5.opt_pool(p0, p1, p2, p3, p4), Nat.is_eq(g0, a0))) : U32} =
    FF5.fb5_s0_eq(g0, a0, Nat.is_eq(g0, a0), {==},
      g1, a1, Nat.is_eq(g1, a1), {==},
      g2, a2, Nat.is_eq(g2, a2), {==},
      g3, a3, Nat.is_eq(g3, a3), {==},
      g4, a4, Nat.is_eq(g4, a4), {==}, p0, p1, p2, p3, p4)
  +e2 : {FF5.encode_tail5(
           SolveFast.feedback_go_fast(gw, aw,
             FF5.opt_pool(p0, p1, p2, p3, p4), Nat.is_eq(g0, a0)))
         == FF5.encode_tail5(SolveFast.feedback_fast(gw, aw)) : U32} =
    Equal.cong(+List<Nat>, U32,
      pl => FF5.encode_tail5(
              SolveFast.feedback_go_fast(gw, aw, pl, Nat.is_eq(g0, a0))),
      FF5.opt_pool(p0, p1, p2, p3, p4), SolveFast.non_green_fast(gw, aw),
      FF5.opt_pool_non_green(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4))
  +e3 : {FF5.encode_tail5(SolveFast.feedback_fast(gw, aw))
         == FF5.encode_tail5(Feedback.feedback(gw, aw)) : U32} =
    Equal.cong(+List<Feedback.Color>, U32, f => FF5.encode_tail5(f),
      SolveFast.feedback_fast(gw, aw), Feedback.feedback(gw, aw),
      FG.FG.feedback_eq(gw, aw))
  +e4 : {FF5.encode_tail5(Feedback.feedback(gw, aw))
         == FF5.encode_fb5_list(Feedback.feedback(gw, aw)) : U32} =
    FF5.encode_tail5_of_fb5(Feedback.feedback(gw, aw),
      FF5.feedback_len5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4))
  Equal.trans(U32,
    SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4),
    FF5.encode_tail5(SolveFast.feedback_fast(gw, aw)),
    FF5.encode_fb5_list(Feedback.feedback(gw, aw)),
    Equal.trans(U32,
      SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4),
      FF5.encode_tail5(
        SolveFast.feedback_go_fast(gw, aw,
          FF5.opt_pool(p0, p1, p2, p3, p4), Nat.is_eq(g0, a0))),
      FF5.encode_tail5(SolveFast.feedback_fast(gw, aw)), e1, e2),
    Equal.trans(U32,
      FF5.encode_tail5(SolveFast.feedback_fast(gw, aw)),
      FF5.encode_tail5(Feedback.feedback(gw, aw)),
      FF5.encode_fb5_list(Feedback.feedback(gw, aw)), e3, e4))

def FF5.decode_feedback_code5(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +a0: Nat, +a1: Nat, +a2: Nat, +a3: Nat, +a4: Nat) ->
  {SolveFast.decode_fb5(
     SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4))
   == Feedback.feedback(
        g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
        a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{})))))
   : +List<Feedback.Color>}:
  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
  +aw : +List<Nat> = a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))
  Equal.trans(+List<Feedback.Color>,
    SolveFast.decode_fb5(
      SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4)),
    SolveFast.decode_fb5(FF5.encode_fb5_list(Feedback.feedback(gw, aw))),
    Feedback.feedback(gw, aw),
    Equal.cong(U32, +List<Feedback.Color>, u => SolveFast.decode_fb5(u),
      SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4),
      FF5.encode_fb5_list(Feedback.feedback(gw, aw)),
      FF5.feedback_code5_eq(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4)),
    FF5.decode_encode_list(Feedback.feedback(gw, aw),
      FF5.feedback_len5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4)))

def FF5.code5_zero_from(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +a0: Nat, +a1: Nat, +a2: Nat, +a3: Nat, +a4: Nat) ->
  {Arr.Arr.u32_zero_from(10n,
     SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4))
   == True{} : Bool}:
  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
  +aw : +List<Nat> = a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))
  Equal.trans(Bool,
    Arr.Arr.u32_zero_from(10n,
      SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4)),
    Arr.Arr.u32_zero_from(10n, FF5.encode_fb5_list(Feedback.feedback(gw, aw))),
    True{},
    Equal.cong(U32, Bool, u => Arr.Arr.u32_zero_from(10n, u),
      SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4),
      FF5.encode_fb5_list(Feedback.feedback(gw, aw)),
      FF5.feedback_code5_eq(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4)),
    FF5.encode_fb5_list_zero_from(Feedback.feedback(gw, aw),
      FF5.feedback_len5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4)))

# All-green characterization: `U32.is_eq(feedback_code5(...), 682)` equals
# `Feedback.word_eq([g0..g4], [a0..a4])`.
def FF5.consume_color_ne_green(+x: Nat, +pool: +List<Nat>, same: Bool) ->
  {Feedback.Color.eq(SolveFast.consume_color_fast(x, pool, same),
     Feedback.Green{}) == False{} : Bool}:
  match pool:
    case Nil{}:
      {==}
    case Con{h, t}:
      match same:
        case True{}:
          {==}
        case False{}:
          FF5.consume_color_ne_green(x, t, Feedback.next_letter_same(x, t))

def FF5.all_green(+fb: +List<Feedback.Color>) -> Bool:
  match fb:
    case Nil{}:
      True{}
    case Con{c, t}:
      Bool.and(Feedback.Color.eq(c, Feedback.Green{}), FF5.all_green(t))

def FF5.all_green_of_eq(+fb: +List<Feedback.Color>,
    +e: {fb == Feedback.Green{} <> (Feedback.Green{} <> (Feedback.Green{}
               <> (Feedback.Green{} <> (Feedback.Green{} <> Nil{}))))
         : +List<Feedback.Color>}) ->
  {FF5.all_green(fb) == True{} : Bool}:
  Equal.cong(+List<Feedback.Color>, Bool, f => FF5.all_green(f), fb,
    Feedback.Green{} <> (Feedback.Green{} <> (Feedback.Green{}
    <> (Feedback.Green{} <> (Feedback.Green{} <> Nil{})))), e)

def FF5.all_green_false_of_head(+c: Feedback.Color, +t: +List<Feedback.Color>,
    +hf: {Feedback.Color.eq(c, Feedback.Green{}) == False{} : Bool}) ->
  {FF5.all_green(c <> t) == False{} : Bool}:
  Equal.cong(Bool, Bool, b => Bool.and(b, FF5.all_green(t)),
    Feedback.Color.eq(c, Feedback.Green{}), False{}, hf)

def FF5.len_nat(+xs: +List<Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(1n, FF5.len_nat(t))

def FF5.len_color(+xs: +List<Feedback.Color>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(1n, FF5.len_color(t))

def FF5.fb_go_all_green_eq(+g: +List<Nat>, +a: +List<Nat>, +pool: +List<Nat>,
    same: Bool, +es: {same == Feedback.next_same(g, a) : Bool},
    +el: {Nat.is_eq(FF5.len_nat(g), FF5.len_nat(a)) == True{} : Bool}) ->
  {FF5.all_green(SolveFast.feedback_go_fast(g, a, pool, same))
   == SolveFast.word_eq_go(g, a, same) : Bool}:
  match g:
    case Nil{}:
      match a:
        case Nil{}:
          {==}
        case Con{ah, at}:
          Empty.absurd(
            {FF5.all_green(Nil{}) == SolveFast.word_eq_go(Nil{}, ah <> at, same)
             : Bool},
            Logic.Proof.false_ne_true(el))
    case Con{+gh, +gt}:
      match a:
        case Nil{}:
          Empty.absurd(
            {FF5.all_green(SolveFast.feedback_go_fast(gh <> gt, Nil{}, pool, same))
             == SolveFast.word_eq_go(gh <> gt, Nil{}, same) : Bool},
            Logic.Proof.false_ne_true(el))
        case Con{+ah, +at}:
          match same:
            case True{}:
              FF5.fb_go_all_green_eq(gt, at, pool,
                Feedback.next_same(gt, at), {==}, el)
            case False{}:
              FF5.all_green_false_of_head(
                FF5.consume_color_of(gh, pool),
                SolveFast.feedback_go_fast(gt, at,
                  FF5.consume_pool_of(gh, pool), Feedback.next_same(gt, at)),
                FF5.consume_color_ne_green(gh, pool,
                  Feedback.next_letter_same(gh, pool)))

def FF5.all_green_go_eq(+fb: +List<Feedback.Color>, +gs: +List<Feedback.Color>,
    same: Bool, +es: {same == SolveFast.next_fb_same(fb, gs) : Bool},
    +hg: {FF5.all_green(gs) == True{} : Bool},
    +el: {Nat.is_eq(FF5.len_color(fb), FF5.len_color(gs))
          == True{} : Bool}) ->
  {FF5.all_green(fb) == SolveFast.feedback_eq_go(fb, gs, same) : Bool}:
  match fb:
    case Nil{}:
      match gs:
        case Nil{}:
          {==}
        case Con{gh, gt}:
          Empty.absurd(
            {True{} == SolveFast.feedback_eq_go(Nil{}, gh <> gt, same) : Bool},
            Logic.Proof.false_ne_true(el))
    case Con{+c, +t}:
      match gs:
        case Nil{}:
          Empty.absurd(
            {FF5.all_green(c <> t)
             == SolveFast.feedback_eq_go(c <> t, Nil{}, same) : Bool},
            Logic.Proof.false_ne_true(el))
        case Con{+gh, +gt}:
          match same:
            case True{}:
              +egh : {gh == Feedback.Green{} : Feedback.Color} =
                FF5.color_eq_true(gh, Feedback.Green{},
                  Logic.Proof.and_true_l(
                    Feedback.Color.eq(gh, Feedback.Green{}),
                    FF5.all_green(gt), hg))
              +hgt : {FF5.all_green(gt) == True{} : Bool} =
                Logic.Proof.and_true_r(
                  Feedback.Color.eq(gh, Feedback.Green{}),
                  FF5.all_green(gt), hg)
              +ec : {Feedback.Color.eq(c, Feedback.Green{}) == True{} : Bool} =
                Equal.trans(Bool,
                  Feedback.Color.eq(c, Feedback.Green{}),
                  Feedback.Color.eq(c, gh),
                  True{},
                  Equal.cong(Feedback.Color, Bool,
                    x => Feedback.Color.eq(c, x), Feedback.Green{}, gh,
                    Equal.sym(Feedback.Color, gh, Feedback.Green{}, egh)),
                  Equal.sym(Bool, True{}, Feedback.Color.eq(c, gh), es))
              Equal.trans(Bool,
                Bool.and(Feedback.Color.eq(c, Feedback.Green{}),
                  FF5.all_green(t)),
                FF5.all_green(t),
                SolveFast.feedback_eq_go(t, gt, SolveFast.next_fb_same(t, gt)),
                Equal.cong(Bool, Bool, b => Bool.and(b, FF5.all_green(t)),
                  Feedback.Color.eq(c, Feedback.Green{}), True{}, ec),
                FF5.all_green_go_eq(t, gt, SolveFast.next_fb_same(t, gt),
                  {==}, hgt, el))
            case False{}:
              +egh : {gh == Feedback.Green{} : Feedback.Color} =
                FF5.color_eq_true(gh, Feedback.Green{},
                  Logic.Proof.and_true_l(
                    Feedback.Color.eq(gh, Feedback.Green{}),
                    FF5.all_green(gt), hg))
              +ec : {Feedback.Color.eq(c, Feedback.Green{}) == False{} : Bool} =
                Equal.trans(Bool,
                  Feedback.Color.eq(c, Feedback.Green{}),
                  Feedback.Color.eq(c, gh),
                  False{},
                  Equal.cong(Feedback.Color, Bool,
                    x => Feedback.Color.eq(c, x), Feedback.Green{}, gh,
                    Equal.sym(Feedback.Color, gh, Feedback.Green{}, egh)),
                  Equal.sym(Bool, False{}, Feedback.Color.eq(c, gh), es))
              FF5.all_green_false_of_head(c, t, ec)

def FF5.len_color_of_fb5(+fb: +List<Feedback.Color>,
    +h5: {FF5.is_fb5(fb) == True{} : Bool}) ->
  {FF5.len_color(fb) == 5n : Nat}:
  match fb:
    case Nil{}:
      Empty.absurd({0n == 5n : Nat}, Logic.Proof.false_ne_true(h5))
    case Con{c0, t1}:
      match t1:
        case Nil{}:
          Empty.absurd({1n == 5n : Nat}, Logic.Proof.false_ne_true(h5))
        case Con{c1, t2}:
          match t2:
            case Nil{}:
              Empty.absurd({2n == 5n : Nat}, Logic.Proof.false_ne_true(h5))
            case Con{c2, t3}:
              match t3:
                case Nil{}:
                  Empty.absurd({3n == 5n : Nat}, Logic.Proof.false_ne_true(h5))
                case Con{c3, t4}:
                  match t4:
                    case Nil{}:
                      Empty.absurd({4n == 5n : Nat},
                        Logic.Proof.false_ne_true(h5))
                    case Con{c4, t5}:
                      match t5:
                        case Nil{}:
                          {==}
                        case Con{c5, t6}:
                          Empty.absurd(
                            {FF5.len_color(
                               c0 <> (c1 <> (c2 <> (c3 <> (c4 <> (c5 <> t6))))))
                             == 5n : Nat},
                            Logic.Proof.false_ne_true(h5))

def FF5.all_green_fb5_iff(+fb: +List<Feedback.Color>,
    +h5: {FF5.is_fb5(fb) == True{} : Bool}) ->
  {FF5.all_green(fb)
   == Feedback.feedback_eq(fb,
        Feedback.Green{} <> (Feedback.Green{} <> (Feedback.Green{}
        <> (Feedback.Green{} <> (Feedback.Green{} <> Nil{}))))) : Bool}:
  +g5 : +List<Feedback.Color> = Feedback.Green{} <> (Feedback.Green{} <> (Feedback.Green{}
        <> (Feedback.Green{} <> (Feedback.Green{} <> Nil{}))))
  +el : {Nat.is_eq(FF5.len_color(fb), 5n) == True{} : Bool} =
    Equal.cong(Nat, Bool, x => Nat.is_eq(x, 5n),
      FF5.len_color(fb), 5n, FF5.len_color_of_fb5(fb, h5))
  Equal.trans(Bool,
    FF5.all_green(fb),
    SolveFast.feedback_eq_fast(fb, g5),
    Feedback.feedback_eq(fb, g5),
    FF5.all_green_go_eq(fb, g5, SolveFast.next_fb_same(fb, g5),
      {==}, {==}, el),
    FG.FG.feedback_eq_fast_eq(fb, g5))

def FF5.code5_is_682_eq(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
    +a0: Nat, +a1: Nat, +a2: Nat, +a3: Nat, +a4: Nat) ->
  {U32.is_eq(
     SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4), 682)
   == Feedback.word_eq(
        g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{})))),
        a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))) : Bool}:
  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
  +aw : +List<Nat> = a0 <> (a1 <> (a2 <> (a3 <> (a4 <> Nil{}))))
  +fb = Feedback.feedback(gw, aw)
  +g5 : +List<Feedback.Color> = Feedback.Green{} <> (Feedback.Green{} <> (Feedback.Green{}
        <> (Feedback.Green{} <> (Feedback.Green{} <> Nil{}))))
  +h5 = FF5.feedback_len5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4)
  +e1 : {U32.is_eq(
           SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4), 682)
         == U32.is_eq(FF5.encode_fb5_list(fb), FF5.encode_fb5_list(g5)) : Bool} =
    Equal.cong(U32, Bool, u => U32.is_eq(u, 682),
      SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4),
      FF5.encode_fb5_list(fb),
      FF5.feedback_code5_eq(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4))
  +e2 : {U32.is_eq(FF5.encode_fb5_list(fb), FF5.encode_fb5_list(g5))
         == Feedback.feedback_eq(fb, g5) : Bool} =
    FF5.code_eq_iff_fb_eq(fb, g5, h5, {==})
  +e3 : {Feedback.feedback_eq(fb, g5) == FF5.all_green(fb) : Bool} =
    Equal.sym(Bool, FF5.all_green(fb), Feedback.feedback_eq(fb, g5),
      FF5.all_green_fb5_iff(fb, h5))
  +e4 : {FF5.all_green(fb) == FF5.all_green(SolveFast.feedback_fast(gw, aw))
         : Bool} =
    Equal.cong(+List<Feedback.Color>, Bool, f => FF5.all_green(f),
      fb, SolveFast.feedback_fast(gw, aw),
      Equal.sym(+List<Feedback.Color>, SolveFast.feedback_fast(gw, aw), fb,
        FG.FG.feedback_eq(gw, aw)))
  +e5 : {FF5.all_green(SolveFast.feedback_fast(gw, aw))
         == SolveFast.word_eq_fast(gw, aw) : Bool} =
    FF5.fb_go_all_green_eq(gw, aw, SolveFast.non_green_fast(gw, aw),
      Feedback.next_same(gw, aw), {==}, {==})
  +e6 : {SolveFast.word_eq_fast(gw, aw) == Feedback.word_eq(gw, aw) : Bool} =
    FG.FG.word_eq_fast_eq(gw, aw)
  Equal.trans(Bool,
    U32.is_eq(
      SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4), 682),
    Feedback.feedback_eq(fb, g5),
    Feedback.word_eq(gw, aw),
    Equal.trans(Bool,
      U32.is_eq(
        SolveFast.feedback_code5(g0, g1, g2, g3, g4, a0, a1, a2, a3, a4), 682),
      U32.is_eq(FF5.encode_fb5_list(fb), FF5.encode_fb5_list(g5)),
      Feedback.feedback_eq(fb, g5), e1, e2),
    Equal.trans(Bool,
      Feedback.feedback_eq(fb, g5),
      FF5.all_green(SolveFast.feedback_fast(gw, aw)),
      Feedback.word_eq(gw, aw),
      Equal.trans(Bool,
        Feedback.feedback_eq(fb, g5), FF5.all_green(fb),
        FF5.all_green(SolveFast.feedback_fast(gw, aw)), e3, e4),
      Equal.trans(Bool,
        FF5.all_green(SolveFast.feedback_fast(gw, aw)),
        SolveFast.word_eq_fast(gw, aw), Feedback.word_eq(gw, aw), e5, e6)))

