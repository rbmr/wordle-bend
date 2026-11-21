# Proofs for the JSON text laws: the printer's decimal numerals and the
# agreement between the printer and the reference renderer, plus the recogniser
# lemmas for the printed arrays.
#
# The digit bridge is `Digits.show_letter`: the printer's least-significant-first
# digit list and `Spec.decimal` are the same numeral, so `Json.show_letter` and
# `Spec.decimal` agree for every `Nat`. The renderer proof then walks the tree.
#
# The recogniser part covers decimal letters, guess arrays, feedback arrays,
# kids arrays and whole trees, which proves the well-formedness law.
import Base
import ./decimal.bend as Dec
import ./nat.bend as NP
import ./logic.bend as L
import ../src/spec_json.bend as Spec
import ../src/json.bend as Json
import ../src/feedback.bend as Feedback
import ../src/tree.bend as Tree

def ZLC.contra(n: Nat, pos: {Nat.is_lt(0n, n) == True{} : Bool},
    h: {Nat.is_le(n, 0n) == True{} : Bool}) -> Empty:
  e0 = NP.Nat.eq_zero_of_le_zero(n, h)
  econg = Equal.cong(Nat, Bool, x => Nat.is_lt(0n, x), n, 0n, e0)
  e = Equal.trans(Bool, Nat.is_lt(0n, 0n), Nat.is_lt(0n, n), True{},
                  Equal.sym(Bool, Nat.is_lt(0n, n), Nat.is_lt(0n, 0n), econg), pos)
  L.Proof.false_ne_true(e)

def Digits.irrel(f1: Nat, f2: Nat, n: Nat, qr: Nat & Nat,
    ok: {qr == Nat.divmod(n, 10n) : Nat & Nat},
    pos: {Nat.is_lt(0n, n) == True{} : Bool},
    h1: {Nat.is_le(n, f1) == True{} : Bool},
    h2: {Nat.is_le(n, f2) == True{} : Bool}) ->
  {Spec.decimal.digits(f1, n, qr) == Spec.decimal.digits(f2, n, qr) : +List<Nat>}:
  match f1:
    case 0n:
      Empty.absurd({Spec.decimal.digits(0n, n, qr) == Spec.decimal.digits(f2, n, qr) : +List<Nat>},
                   ZLC.contra(n, pos, h1))
    case 1n++g:
      match f2:
        case 0n:
          Empty.absurd({Spec.decimal.digits(1n+g, n, qr) == Spec.decimal.digits(0n, n, qr) : +List<Nat>},
                       ZLC.contra(n, pos, h2))
        case 1n++h:
          match n:
            case 0n:
              Empty.absurd({Spec.decimal.digits(1n+g, 0n, qr) == Spec.decimal.digits(1n+h, 0n, qr) : +List<Nat>},
                           L.Proof.false_ne_true(pos))
            case 1n++p:
              match qr:
                case (q, r):
                  match q:
                    case 0n:
                      {==}
                    case 1n++qp:
                      q_eq = Equal.cong(Nat & Nat, Nat, Pair.fst(Nat, Nat),
                                        qr, Nat.divmod(1n+p, 10n), ok)
                      q_lt_n0 = Dec.ShowS.div_lt_self(1n+p, pos)
                      q_eq_cong = Equal.cong(Nat, Bool, x => Nat.is_lt(x, 1n+p),
                                            1n+qp, Dec.ShowS.fst(1n+p), q_eq)
                      +q_lt_n = Equal.trans(Bool, Nat.is_lt(1n+qp, 1n+p),
                                           Nat.is_lt(Dec.ShowS.fst(1n+p), 1n+p), True{},
                                           q_eq_cong, q_lt_n0)
                      q_le_g = NP.Nat.is_le_of_lt_succ(1n+qp, g,
                                 NP.Nat.is_lt_le_trans(1n+qp, 1n+p, 1n+g, q_lt_n, h1))
                      q_le_h = NP.Nat.is_le_of_lt_succ(1n+qp, h,
                                 NP.Nat.is_lt_le_trans(1n+qp, 1n+p, 1n+h, q_lt_n, h2))
                      ih = Digits.irrel(g, h, 1n+qp, Nat.divmod(1n+qp, 10n), {==}, {==}, q_le_g, q_le_h)
                      Equal.cong(+List<Nat>, +List<Nat>,
                                 l => List.append(&2, Nat, l, Con{r, Nil{}}),
                                 Spec.decimal.digits(g, 1n+qp, Nat.divmod(1n+qp, 10n)),
                                 Spec.decimal.digits(h, 1n+qp, Nat.divmod(1n+qp, 10n)),
                                 ih)

# --- digit helpers

def Digits.char_digit(d: Json.Digit) ->
  {Json.Digit.char(d) == Spec.digit_char(Json.Digit.nat(d)) : String}:
  match d:
    case Json.D0{}:
      {==}
    case Json.D1{}:
      {==}
    case Json.D2{}:
      {==}
    case Json.D3{}:
      {==}
    case Json.D4{}:
      {==}
    case Json.D5{}:
      {==}
    case Json.D6{}:
      {==}
    case Json.D7{}:
      {==}
    case Json.D8{}:
      {==}
    case Json.D9{}:
      {==}

def Digits.nat_lt10(d: Json.Digit) ->
  {Nat.is_lt(Json.Digit.nat(d), 10n) == True{} : Bool}:
  match d:
    case Json.D0{}:
      {==}
    case Json.D1{}:
      {==}
    case Json.D2{}:
      {==}
    case Json.D3{}:
      {==}
    case Json.D4{}:
      {==}
    case Json.D5{}:
      {==}
    case Json.D6{}:
      {==}
    case Json.D7{}:
      {==}
    case Json.D8{}:
      {==}
    case Json.D9{}:
      {==}

# --- string append

def Str.append_assoc(a: String, b: String, c: String) ->
  {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, r => SCon{h, r},
                 String.append(String.append(t, b), c),
                 String.append(t, String.append(b, c)),
                 Str.append_assoc(t, b, c))

def Str.append_nil(s: String) ->
  {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, r => SCon{h, r},
                 String.append(t, SNil{}), t, Str.append_nil(t))

def CharsProof.chars_snoc(+xs: +List<Nat>, +d: Nat) ->
  {Spec.decimal.chars(List.append(&2, Nat, xs, Con{d, Nil{}}))
    == String.append(Spec.decimal.chars(xs), Spec.digit_char(d)) : String}:
  match xs:
    case Nil{}:
      Str.append_nil(Spec.digit_char(d))
    case Con{h, t}:
      ih = CharsProof.chars_snoc(t, d)
      e1 = Equal.cong(String, String, s => String.append(Spec.digit_char(h), s),
                      Spec.decimal.chars(List.append(&2, Nat, t, Con{d, Nil{}})),
                      String.append(Spec.decimal.chars(t), Spec.digit_char(d)), ih)
      e2 = Str.append_assoc(Spec.digit_char(h), Spec.decimal.chars(t), Spec.digit_char(d))
      Equal.trans(String,
        Spec.decimal.chars(List.append(&2, Nat, Con{h, t}, Con{d, Nil{}})),
        String.append(Spec.digit_char(h), String.append(Spec.decimal.chars(t), Spec.digit_char(d))),
        String.append(String.append(Spec.digit_char(h), Spec.decimal.chars(t)), Spec.digit_char(d)),
        e1, Equal.sym(String,
          String.append(String.append(Spec.digit_char(h), Spec.decimal.chars(t)), Spec.digit_char(d)),
          String.append(Spec.digit_char(h), String.append(Spec.decimal.chars(t), Spec.digit_char(d))),
          e2))

# --- arithmetic around ten times a positive number

def Digits.lt_succ_r(+v: Nat) -> {Nat.is_lt(v, Nat.add(v, 1n)) == True{} : Bool}:
  cong = Equal.cong(Nat, Bool, x => Nat.is_lt(v, x),
                    Nat.add(1n, v), Nat.add(v, 1n),
                    Equal.sym(Nat, Nat.add(v, 1n), Nat.add(1n, v), Dec.AddS.add_one(v)))
  Equal.trans(Bool, Nat.is_lt(v, Nat.add(v, 1n)), Nat.is_lt(v, Nat.add(1n, v)), True{},
              Equal.sym(Bool, Nat.is_lt(v, Nat.add(1n, v)), Nat.is_lt(v, Nat.add(v, 1n)), cong),
              NP.Nat.is_lt_succ_self(v))

def Digits.succ_le_ten_add(+v: Nat, +d: Nat,
    posv: {Nat.is_lt(0n, v) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(v, 1n), Nat.add(Nat.mul(10n, v), d)) == True{} : Bool}:
  +q10 : Nat = Nat.mul(10n, v)
  e1 = Dec.Ord.le_succ_ten(v, posv)
  e2 = NP.Nat.is_le_add_self_l(d, q10)
  e2c = Dec.AddS.add_comm(d, q10)
  e2c_cong = Equal.cong(Nat, Bool, x => Nat.is_le(q10, x),
                        Nat.add(d, q10), Nat.add(q10, d), e2c)
  e2b = Equal.trans(Bool, Nat.is_le(q10, Nat.add(q10, d)),
                    Nat.is_le(q10, Nat.add(d, q10)), True{},
                    Equal.sym(Bool, Nat.is_le(q10, Nat.add(d, q10)),
                              Nat.is_le(q10, Nat.add(q10, d)), e2c_cong), e2)
  NP.Nat.is_le_trans(Nat.add(v, 1n), q10, Nat.add(q10, d), e1, e2b)

def Nat.succ_pred(+n: Nat, pos: {Nat.is_lt(0n, n) == True{} : Bool}) ->
  {Nat.add(1n, NP.NatPrf.pred(n)) == n : Nat}:
  match n:
    case 0n:
      Empty.absurd({Nat.add(1n, NP.NatPrf.pred(0n)) == 0n : Nat}, L.Proof.false_ne_true(pos))
    case 1n++p:
      {==}

# --- decimal of ten times v plus a digit

def Digits.decimal_add_digit(+v: Nat, +d: Nat,
    posv: {Nat.is_lt(0n, v) == True{} : Bool},
    ltd: {Nat.is_lt(d, 10n) == True{} : Bool}) ->
  {Spec.decimal(Nat.add(Nat.mul(10n, v), d))
    == String.append(Spec.decimal(v), Spec.digit_char(d)) : String}:
  match v:
    case 0n:
      Empty.absurd({Spec.decimal(Nat.add(Nat.mul(10n, 0n), d))
                    == String.append(Spec.decimal(0n), Spec.digit_char(d)) : String},
                   L.Proof.false_ne_true(posv))
    case 1n++vp:
      +n : Nat = Nat.add(Nat.mul(10n, 1n+vp), d)
      +pn : Nat = NP.NatPrf.pred(n)
      posn : {Nat.is_lt(0n, n) == True{} : Bool} = {==}
      qr_eq = Dec.DivS.divmod10(1n+vp, d, ltd)
      e_digits = Equal.cong(Nat & Nat, +List<Nat>,
                  qr => Spec.decimal.digits(n, n, qr),
                  Nat.divmod(n, 10n), (1n+vp, d), qr_eq)
      e_chars1 = Equal.cong(+List<Nat>, String, Spec.decimal.chars,
                   Spec.decimal.digits(n, n, Nat.divmod(n, 10n)),
                   Spec.decimal.digits(n, n, (1n+vp, d)), e_digits)
      e_unfold : {Spec.decimal.digits(n, n, (1n+vp, d))
                  == List.append(&2, Nat,
                       Spec.decimal.digits(pn, 1n+vp, Nat.divmod(1n+vp, 10n)),
                       Con{d, Nil{}}) : +List<Nat>} = {==}
      le_v1_n = Digits.succ_le_ten_add(1n+vp, d, {==})
      v_lt_n = NP.Nat.is_lt_le_trans(1n+vp, Nat.add(1n+vp, 1n), n,
                 Digits.lt_succ_r(1n+vp), le_v1_n)
      e_n = Nat.succ_pred(n, posn)
      v_lt_1pn_cong = Equal.cong(Nat, Bool, x => Nat.is_lt(1n+vp, x),
                         n, Nat.add(1n, pn), Equal.sym(Nat, Nat.add(1n, pn), n, e_n))
      v_lt_1pn = Equal.trans(Bool, Nat.is_lt(1n+vp, Nat.add(1n, pn)), Nat.is_lt(1n+vp, n), True{},
                    Equal.sym(Bool, Nat.is_lt(1n+vp, n), Nat.is_lt(1n+vp, Nat.add(1n, pn)),
                              v_lt_1pn_cong), v_lt_n)
      v_le_pn = NP.Nat.is_le_of_lt_succ(1n+vp, pn, v_lt_1pn)
      e_irrel = Digits.irrel(pn, 1n+vp, 1n+vp, Nat.divmod(1n+vp, 10n), {==}, {==},
                             v_le_pn, NP.Nat.is_le_refl(1n+vp))
      e_append = Equal.cong(+List<Nat>, +List<Nat>,
                   l => List.append(&2, Nat, l, Con{d, Nil{}}),
                   Spec.decimal.digits(pn, 1n+vp, Nat.divmod(1n+vp, 10n)),
                   Spec.decimal.digits(1n+vp, 1n+vp, Nat.divmod(1n+vp, 10n)),
                   e_irrel)
      e_digits2 = Equal.trans(+List<Nat>, Spec.decimal.digits(n, n, (1n+vp, d)),
                     List.append(&2, Nat, Spec.decimal.digits(pn, 1n+vp, Nat.divmod(1n+vp, 10n)), Con{d, Nil{}}),
                     List.append(&2, Nat, Spec.decimal.digits(1n+vp, 1n+vp, Nat.divmod(1n+vp, 10n)), Con{d, Nil{}}),
                     e_unfold, e_append)
      e_chars2 = Equal.cong(+List<Nat>, String, Spec.decimal.chars,
                    Spec.decimal.digits(n, n, (1n+vp, d)),
                    List.append(&2, Nat, Spec.decimal.digits(1n+vp, 1n+vp, Nat.divmod(1n+vp, 10n)), Con{d, Nil{}}),
                    e_digits2)
      e_snoc = CharsProof.chars_snoc(Spec.decimal.digits(1n+vp, 1n+vp, Nat.divmod(1n+vp, 10n)), d)
      Equal.trans(String, Spec.decimal(n),
        Spec.decimal.chars(List.append(&2, Nat, Spec.decimal.digits(1n+vp, 1n+vp, Nat.divmod(1n+vp, 10n)), Con{d, Nil{}})),
        String.append(Spec.decimal(1n+vp), Spec.digit_char(d)),
        Equal.trans(String, Spec.decimal(n),
          Spec.decimal.chars(Spec.decimal.digits(n, n, Nat.divmod(n, 10n))),
          Spec.decimal.chars(List.append(&2, Nat, Spec.decimal.digits(1n+vp, 1n+vp, Nat.divmod(1n+vp, 10n)), Con{d, Nil{}})),
          {==},
          Equal.trans(String,
            Spec.decimal.chars(Spec.decimal.digits(n, n, Nat.divmod(n, 10n))),
            Spec.decimal.chars(Spec.decimal.digits(n, n, (1n+vp, d))),
            Spec.decimal.chars(List.append(&2, Nat, Spec.decimal.digits(1n+vp, 1n+vp, Nat.divmod(1n+vp, 10n)), Con{d, Nil{}})),
            e_chars1, e_chars2)),
        Equal.trans(String,
          Spec.decimal.chars(List.append(&2, Nat, Spec.decimal.digits(1n+vp, 1n+vp, Nat.divmod(1n+vp, 10n)), Con{d, Nil{}})),
          String.append(Spec.decimal.chars(Spec.decimal.digits(1n+vp, 1n+vp, Nat.divmod(1n+vp, 10n))), Spec.digit_char(d)),
          String.append(Spec.decimal(1n+vp), Spec.digit_char(d)),
          e_snoc, {==}))

# --- canonical digit lists

def Dig.NZ(d: Json.Digit) -> Bool:
  match d:
    case Json.D0{}:
      False{}
    case Json.D1{}:
      True{}
    case Json.D2{}:
      True{}
    case Json.D3{}:
      True{}
    case Json.D4{}:
      True{}
    case Json.D5{}:
      True{}
    case Json.D6{}:
      True{}
    case Json.D7{}:
      True{}
    case Json.D8{}:
      True{}
    case Json.D9{}:
      True{}

def Dig.Canon(ds: +List<Json.Digit>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, t}:
      match t:
        case Nil{}:
          Dig.NZ(d)
        case Con{_, _}:
          Dig.Canon(t)

def Dig.add_pos_l(+a: Nat, +b: Nat,
    apos: {Nat.is_lt(0n, a) == True{} : Bool}) ->
  {Nat.is_lt(0n, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.add(0n, b)) == True{} : Bool},
                   L.Proof.false_ne_true(apos))
    case 1n++p:
      {==}

def Dig.mul_ten_pos(+v: Nat, pos: {Nat.is_lt(0n, v) == True{} : Bool}) ->
  {Nat.is_lt(0n, Nat.mul(10n, v)) == True{} : Bool}:
  match v:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, Nat.mul(10n, 0n)) == True{} : Bool},
                   L.Proof.false_ne_true(pos))
    case 1n++p:
      {==}
def Dig.value_pos(ds: +List<Json.Digit>, +c: {Dig.Canon(ds) == True{} : Bool}) ->
  {Nat.is_lt(0n, Json.digits_value(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      Empty.absurd({Nat.is_lt(0n, Json.digits_value(Nil{})) == True{} : Bool}, L.Proof.false_ne_true(c))
    case Con{d, t}:
      match d:
        case Json.D0{}:
          match t:
            case Nil{}:
              Empty.absurd({Nat.is_lt(0n, Json.digits_value(Con{Json.D0{}, Nil{}})) == True{} : Bool}, L.Proof.false_ne_true(c))
            case Con{+h, +t2}:
              +v : Nat = Json.digits_value(Con{h, t2})
              vpos = Dig.value_pos(Con{h, t2}, c)
              Dig.add_pos_l(Nat.mul(10n, v), Json.Digit.nat(Json.D0{}), Dig.mul_ten_pos(v, vpos))
        case Json.D1{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              +v : Nat = Json.digits_value(Con{h, t2})
              vpos = Dig.value_pos(Con{h, t2}, c)
              Dig.add_pos_l(Nat.mul(10n, v), Json.Digit.nat(Json.D1{}), Dig.mul_ten_pos(v, vpos))
        case Json.D2{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              +v : Nat = Json.digits_value(Con{h, t2})
              vpos = Dig.value_pos(Con{h, t2}, c)
              Dig.add_pos_l(Nat.mul(10n, v), Json.Digit.nat(Json.D2{}), Dig.mul_ten_pos(v, vpos))
        case Json.D3{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              +v : Nat = Json.digits_value(Con{h, t2})
              vpos = Dig.value_pos(Con{h, t2}, c)
              Dig.add_pos_l(Nat.mul(10n, v), Json.Digit.nat(Json.D3{}), Dig.mul_ten_pos(v, vpos))
        case Json.D4{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              +v : Nat = Json.digits_value(Con{h, t2})
              vpos = Dig.value_pos(Con{h, t2}, c)
              Dig.add_pos_l(Nat.mul(10n, v), Json.Digit.nat(Json.D4{}), Dig.mul_ten_pos(v, vpos))
        case Json.D5{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              +v : Nat = Json.digits_value(Con{h, t2})
              vpos = Dig.value_pos(Con{h, t2}, c)
              Dig.add_pos_l(Nat.mul(10n, v), Json.Digit.nat(Json.D5{}), Dig.mul_ten_pos(v, vpos))
        case Json.D6{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              +v : Nat = Json.digits_value(Con{h, t2})
              vpos = Dig.value_pos(Con{h, t2}, c)
              Dig.add_pos_l(Nat.mul(10n, v), Json.Digit.nat(Json.D6{}), Dig.mul_ten_pos(v, vpos))
        case Json.D7{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              +v : Nat = Json.digits_value(Con{h, t2})
              vpos = Dig.value_pos(Con{h, t2}, c)
              Dig.add_pos_l(Nat.mul(10n, v), Json.Digit.nat(Json.D7{}), Dig.mul_ten_pos(v, vpos))
        case Json.D8{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              +v : Nat = Json.digits_value(Con{h, t2})
              vpos = Dig.value_pos(Con{h, t2}, c)
              Dig.add_pos_l(Nat.mul(10n, v), Json.Digit.nat(Json.D8{}), Dig.mul_ten_pos(v, vpos))
        case Json.D9{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              +v : Nat = Json.digits_value(Con{h, t2})
              vpos = Dig.value_pos(Con{h, t2}, c)
              Dig.add_pos_l(Nat.mul(10n, v), Json.Digit.nat(Json.D9{}), Dig.mul_ten_pos(v, vpos))
def Dig.show_value(ds: +List<Json.Digit>, +c: {Dig.Canon(ds) == True{} : Bool}) ->
  {Json.digits_show(ds) == Spec.decimal(Json.digits_value(ds)) : String}:
  match ds:
    case Nil{}:
      Empty.absurd({Json.digits_show(Nil{}) == Spec.decimal(Json.digits_value(Nil{})) : String}, L.Proof.false_ne_true(c))
    case Con{d, t}:
      match d:
        case Json.D0{}:
          match t:
            case Nil{}:
              Empty.absurd({Json.digits_show(Con{Json.D0{}, Nil{}}) == Spec.decimal(Json.digits_value(Con{Json.D0{}, Nil{}})) : String}, L.Proof.false_ne_true(c))
            case Con{+h, +t2}:
              ih = Dig.show_value(Con{h, t2}, c)
              vpos = Dig.value_pos(Con{h, t2}, c)
              e_app = Digits.decimal_add_digit(Json.digits_value(Con{h, t2}), Json.Digit.nat(Json.D0{}),
                                               vpos, Digits.nat_lt10(Json.D0{}))
              e_ih = Equal.cong(String, String, s => String.append(s, Json.Digit.char(Json.D0{})),
                                Json.digits_show(Con{h, t2}), Spec.decimal(Json.digits_value(Con{h, t2})),
                                ih)
              e_char = Digits.char_digit(Json.D0{})
              e_mid = Equal.trans(String,
                        String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D0{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Json.Digit.char(Json.D0{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D0{}))),
                        e_ih,
                        Equal.cong(String, String,
                          s => String.append(Spec.decimal(Json.digits_value(Con{h, t2})), s),
                          Json.Digit.char(Json.D0{}), Spec.digit_char(Json.Digit.nat(Json.D0{})), e_char))
              Equal.trans(String,
                String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D0{})),
                String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D0{}))),
                Spec.decimal(Json.digits_value(Con{Json.D0{}, Con{h, t2}})),
                e_mid,
                Equal.sym(String,
                  Spec.decimal(Nat.add(Nat.mul(10n, Json.digits_value(Con{h, t2})), Json.Digit.nat(Json.D0{}))),
                  String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D0{}))),
                  e_app))
        case Json.D1{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              ih = Dig.show_value(Con{h, t2}, c)
              vpos = Dig.value_pos(Con{h, t2}, c)
              e_app = Digits.decimal_add_digit(Json.digits_value(Con{h, t2}), Json.Digit.nat(Json.D1{}),
                                               vpos, Digits.nat_lt10(Json.D1{}))
              e_ih = Equal.cong(String, String, s => String.append(s, Json.Digit.char(Json.D1{})),
                                Json.digits_show(Con{h, t2}), Spec.decimal(Json.digits_value(Con{h, t2})),
                                ih)
              e_char = Digits.char_digit(Json.D1{})
              e_mid = Equal.trans(String,
                        String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D1{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Json.Digit.char(Json.D1{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D1{}))),
                        e_ih,
                        Equal.cong(String, String,
                          s => String.append(Spec.decimal(Json.digits_value(Con{h, t2})), s),
                          Json.Digit.char(Json.D1{}), Spec.digit_char(Json.Digit.nat(Json.D1{})), e_char))
              Equal.trans(String,
                String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D1{})),
                String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D1{}))),
                Spec.decimal(Json.digits_value(Con{Json.D1{}, Con{h, t2}})),
                e_mid,
                Equal.sym(String,
                  Spec.decimal(Nat.add(Nat.mul(10n, Json.digits_value(Con{h, t2})), Json.Digit.nat(Json.D1{}))),
                  String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D1{}))),
                  e_app))
        case Json.D2{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              ih = Dig.show_value(Con{h, t2}, c)
              vpos = Dig.value_pos(Con{h, t2}, c)
              e_app = Digits.decimal_add_digit(Json.digits_value(Con{h, t2}), Json.Digit.nat(Json.D2{}),
                                               vpos, Digits.nat_lt10(Json.D2{}))
              e_ih = Equal.cong(String, String, s => String.append(s, Json.Digit.char(Json.D2{})),
                                Json.digits_show(Con{h, t2}), Spec.decimal(Json.digits_value(Con{h, t2})),
                                ih)
              e_char = Digits.char_digit(Json.D2{})
              e_mid = Equal.trans(String,
                        String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D2{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Json.Digit.char(Json.D2{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D2{}))),
                        e_ih,
                        Equal.cong(String, String,
                          s => String.append(Spec.decimal(Json.digits_value(Con{h, t2})), s),
                          Json.Digit.char(Json.D2{}), Spec.digit_char(Json.Digit.nat(Json.D2{})), e_char))
              Equal.trans(String,
                String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D2{})),
                String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D2{}))),
                Spec.decimal(Json.digits_value(Con{Json.D2{}, Con{h, t2}})),
                e_mid,
                Equal.sym(String,
                  Spec.decimal(Nat.add(Nat.mul(10n, Json.digits_value(Con{h, t2})), Json.Digit.nat(Json.D2{}))),
                  String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D2{}))),
                  e_app))
        case Json.D3{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              ih = Dig.show_value(Con{h, t2}, c)
              vpos = Dig.value_pos(Con{h, t2}, c)
              e_app = Digits.decimal_add_digit(Json.digits_value(Con{h, t2}), Json.Digit.nat(Json.D3{}),
                                               vpos, Digits.nat_lt10(Json.D3{}))
              e_ih = Equal.cong(String, String, s => String.append(s, Json.Digit.char(Json.D3{})),
                                Json.digits_show(Con{h, t2}), Spec.decimal(Json.digits_value(Con{h, t2})),
                                ih)
              e_char = Digits.char_digit(Json.D3{})
              e_mid = Equal.trans(String,
                        String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D3{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Json.Digit.char(Json.D3{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D3{}))),
                        e_ih,
                        Equal.cong(String, String,
                          s => String.append(Spec.decimal(Json.digits_value(Con{h, t2})), s),
                          Json.Digit.char(Json.D3{}), Spec.digit_char(Json.Digit.nat(Json.D3{})), e_char))
              Equal.trans(String,
                String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D3{})),
                String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D3{}))),
                Spec.decimal(Json.digits_value(Con{Json.D3{}, Con{h, t2}})),
                e_mid,
                Equal.sym(String,
                  Spec.decimal(Nat.add(Nat.mul(10n, Json.digits_value(Con{h, t2})), Json.Digit.nat(Json.D3{}))),
                  String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D3{}))),
                  e_app))
        case Json.D4{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              ih = Dig.show_value(Con{h, t2}, c)
              vpos = Dig.value_pos(Con{h, t2}, c)
              e_app = Digits.decimal_add_digit(Json.digits_value(Con{h, t2}), Json.Digit.nat(Json.D4{}),
                                               vpos, Digits.nat_lt10(Json.D4{}))
              e_ih = Equal.cong(String, String, s => String.append(s, Json.Digit.char(Json.D4{})),
                                Json.digits_show(Con{h, t2}), Spec.decimal(Json.digits_value(Con{h, t2})),
                                ih)
              e_char = Digits.char_digit(Json.D4{})
              e_mid = Equal.trans(String,
                        String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D4{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Json.Digit.char(Json.D4{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D4{}))),
                        e_ih,
                        Equal.cong(String, String,
                          s => String.append(Spec.decimal(Json.digits_value(Con{h, t2})), s),
                          Json.Digit.char(Json.D4{}), Spec.digit_char(Json.Digit.nat(Json.D4{})), e_char))
              Equal.trans(String,
                String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D4{})),
                String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D4{}))),
                Spec.decimal(Json.digits_value(Con{Json.D4{}, Con{h, t2}})),
                e_mid,
                Equal.sym(String,
                  Spec.decimal(Nat.add(Nat.mul(10n, Json.digits_value(Con{h, t2})), Json.Digit.nat(Json.D4{}))),
                  String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D4{}))),
                  e_app))
        case Json.D5{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              ih = Dig.show_value(Con{h, t2}, c)
              vpos = Dig.value_pos(Con{h, t2}, c)
              e_app = Digits.decimal_add_digit(Json.digits_value(Con{h, t2}), Json.Digit.nat(Json.D5{}),
                                               vpos, Digits.nat_lt10(Json.D5{}))
              e_ih = Equal.cong(String, String, s => String.append(s, Json.Digit.char(Json.D5{})),
                                Json.digits_show(Con{h, t2}), Spec.decimal(Json.digits_value(Con{h, t2})),
                                ih)
              e_char = Digits.char_digit(Json.D5{})
              e_mid = Equal.trans(String,
                        String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D5{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Json.Digit.char(Json.D5{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D5{}))),
                        e_ih,
                        Equal.cong(String, String,
                          s => String.append(Spec.decimal(Json.digits_value(Con{h, t2})), s),
                          Json.Digit.char(Json.D5{}), Spec.digit_char(Json.Digit.nat(Json.D5{})), e_char))
              Equal.trans(String,
                String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D5{})),
                String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D5{}))),
                Spec.decimal(Json.digits_value(Con{Json.D5{}, Con{h, t2}})),
                e_mid,
                Equal.sym(String,
                  Spec.decimal(Nat.add(Nat.mul(10n, Json.digits_value(Con{h, t2})), Json.Digit.nat(Json.D5{}))),
                  String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D5{}))),
                  e_app))
        case Json.D6{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              ih = Dig.show_value(Con{h, t2}, c)
              vpos = Dig.value_pos(Con{h, t2}, c)
              e_app = Digits.decimal_add_digit(Json.digits_value(Con{h, t2}), Json.Digit.nat(Json.D6{}),
                                               vpos, Digits.nat_lt10(Json.D6{}))
              e_ih = Equal.cong(String, String, s => String.append(s, Json.Digit.char(Json.D6{})),
                                Json.digits_show(Con{h, t2}), Spec.decimal(Json.digits_value(Con{h, t2})),
                                ih)
              e_char = Digits.char_digit(Json.D6{})
              e_mid = Equal.trans(String,
                        String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D6{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Json.Digit.char(Json.D6{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D6{}))),
                        e_ih,
                        Equal.cong(String, String,
                          s => String.append(Spec.decimal(Json.digits_value(Con{h, t2})), s),
                          Json.Digit.char(Json.D6{}), Spec.digit_char(Json.Digit.nat(Json.D6{})), e_char))
              Equal.trans(String,
                String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D6{})),
                String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D6{}))),
                Spec.decimal(Json.digits_value(Con{Json.D6{}, Con{h, t2}})),
                e_mid,
                Equal.sym(String,
                  Spec.decimal(Nat.add(Nat.mul(10n, Json.digits_value(Con{h, t2})), Json.Digit.nat(Json.D6{}))),
                  String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D6{}))),
                  e_app))
        case Json.D7{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              ih = Dig.show_value(Con{h, t2}, c)
              vpos = Dig.value_pos(Con{h, t2}, c)
              e_app = Digits.decimal_add_digit(Json.digits_value(Con{h, t2}), Json.Digit.nat(Json.D7{}),
                                               vpos, Digits.nat_lt10(Json.D7{}))
              e_ih = Equal.cong(String, String, s => String.append(s, Json.Digit.char(Json.D7{})),
                                Json.digits_show(Con{h, t2}), Spec.decimal(Json.digits_value(Con{h, t2})),
                                ih)
              e_char = Digits.char_digit(Json.D7{})
              e_mid = Equal.trans(String,
                        String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D7{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Json.Digit.char(Json.D7{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D7{}))),
                        e_ih,
                        Equal.cong(String, String,
                          s => String.append(Spec.decimal(Json.digits_value(Con{h, t2})), s),
                          Json.Digit.char(Json.D7{}), Spec.digit_char(Json.Digit.nat(Json.D7{})), e_char))
              Equal.trans(String,
                String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D7{})),
                String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D7{}))),
                Spec.decimal(Json.digits_value(Con{Json.D7{}, Con{h, t2}})),
                e_mid,
                Equal.sym(String,
                  Spec.decimal(Nat.add(Nat.mul(10n, Json.digits_value(Con{h, t2})), Json.Digit.nat(Json.D7{}))),
                  String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D7{}))),
                  e_app))
        case Json.D8{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              ih = Dig.show_value(Con{h, t2}, c)
              vpos = Dig.value_pos(Con{h, t2}, c)
              e_app = Digits.decimal_add_digit(Json.digits_value(Con{h, t2}), Json.Digit.nat(Json.D8{}),
                                               vpos, Digits.nat_lt10(Json.D8{}))
              e_ih = Equal.cong(String, String, s => String.append(s, Json.Digit.char(Json.D8{})),
                                Json.digits_show(Con{h, t2}), Spec.decimal(Json.digits_value(Con{h, t2})),
                                ih)
              e_char = Digits.char_digit(Json.D8{})
              e_mid = Equal.trans(String,
                        String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D8{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Json.Digit.char(Json.D8{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D8{}))),
                        e_ih,
                        Equal.cong(String, String,
                          s => String.append(Spec.decimal(Json.digits_value(Con{h, t2})), s),
                          Json.Digit.char(Json.D8{}), Spec.digit_char(Json.Digit.nat(Json.D8{})), e_char))
              Equal.trans(String,
                String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D8{})),
                String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D8{}))),
                Spec.decimal(Json.digits_value(Con{Json.D8{}, Con{h, t2}})),
                e_mid,
                Equal.sym(String,
                  Spec.decimal(Nat.add(Nat.mul(10n, Json.digits_value(Con{h, t2})), Json.Digit.nat(Json.D8{}))),
                  String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D8{}))),
                  e_app))
        case Json.D9{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              ih = Dig.show_value(Con{h, t2}, c)
              vpos = Dig.value_pos(Con{h, t2}, c)
              e_app = Digits.decimal_add_digit(Json.digits_value(Con{h, t2}), Json.Digit.nat(Json.D9{}),
                                               vpos, Digits.nat_lt10(Json.D9{}))
              e_ih = Equal.cong(String, String, s => String.append(s, Json.Digit.char(Json.D9{})),
                                Json.digits_show(Con{h, t2}), Spec.decimal(Json.digits_value(Con{h, t2})),
                                ih)
              e_char = Digits.char_digit(Json.D9{})
              e_mid = Equal.trans(String,
                        String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D9{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Json.Digit.char(Json.D9{})),
                        String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D9{}))),
                        e_ih,
                        Equal.cong(String, String,
                          s => String.append(Spec.decimal(Json.digits_value(Con{h, t2})), s),
                          Json.Digit.char(Json.D9{}), Spec.digit_char(Json.Digit.nat(Json.D9{})), e_char))
              Equal.trans(String,
                String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D9{})),
                String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D9{}))),
                Spec.decimal(Json.digits_value(Con{Json.D9{}, Con{h, t2}})),
                e_mid,
                Equal.sym(String,
                  Spec.decimal(Nat.add(Nat.mul(10n, Json.digits_value(Con{h, t2})), Json.Digit.nat(Json.D9{}))),
                  String.append(Spec.decimal(Json.digits_value(Con{h, t2})), Spec.digit_char(Json.Digit.nat(Json.D9{}))),
                  e_app))
def Dig.inc_canon(ds: +List<Json.Digit>, +c: {Dig.Canon(ds) == True{} : Bool}) ->
  {Dig.Canon(Json.digits_inc(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      Empty.absurd({Dig.Canon(Json.digits_inc(Nil{})) == True{} : Bool}, L.Proof.false_ne_true(c))
    case Con{d, t}:
      match d:
        case Json.D0{}:
          match t:
            case Nil{}:
              Empty.absurd({Dig.Canon(Json.digits_inc(Con{Json.D0{}, Nil{}})) == True{} : Bool}, L.Proof.false_ne_true(c))
            case Con{+h, +t2}:
              c
        case Json.D1{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              c
        case Json.D2{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              c
        case Json.D3{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              c
        case Json.D4{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              c
        case Json.D5{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              c
        case Json.D6{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              c
        case Json.D7{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              c
        case Json.D8{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              c
        case Json.D9{}:
          match t:
            case Nil{}:
              {==}
            case Con{+h, +t2}:
              match h:
                case Json.D0{}:
                  Dig.inc_canon(Con{Json.D0{}, t2}, c)
                case Json.D1{}:
                  Dig.inc_canon(Con{Json.D1{}, t2}, c)
                case Json.D2{}:
                  Dig.inc_canon(Con{Json.D2{}, t2}, c)
                case Json.D3{}:
                  Dig.inc_canon(Con{Json.D3{}, t2}, c)
                case Json.D4{}:
                  Dig.inc_canon(Con{Json.D4{}, t2}, c)
                case Json.D5{}:
                  Dig.inc_canon(Con{Json.D5{}, t2}, c)
                case Json.D6{}:
                  Dig.inc_canon(Con{Json.D6{}, t2}, c)
                case Json.D7{}:
                  Dig.inc_canon(Con{Json.D7{}, t2}, c)
                case Json.D8{}:
                  Dig.inc_canon(Con{Json.D8{}, t2}, c)
                case Json.D9{}:
                  Dig.inc_canon(Con{Json.D9{}, t2}, c)
def Dig.canon_lsb(n: Nat, pos: {Nat.is_lt(0n, n) == True{} : Bool}) ->
  {Dig.Canon(Json.digits_lsb(n)) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Dig.Canon(Json.digits_lsb(0n)) == True{} : Bool}, L.Proof.false_ne_true(pos))
    case 1n++p:
      match p:
        case 0n:
          {==}
        case 1n++pp:
          Dig.inc_canon(Json.digits_lsb(p), Dig.canon_lsb(p, {==}))

# Adding one carries through the least significant digits.
def Digits.value_inc(ds: +List<Json.Digit>) ->
  {Json.digits_value(Json.digits_inc(ds)) == Nat.add(Json.digits_value(ds), 1n) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, +t}:
      match d:
        case Json.D0{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 0n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 1n),
            Dec.AddS.add_assoc(Nat.mul(10n, Json.digits_value(t)), 0n, 1n))
        case Json.D1{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 1n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 2n),
            Dec.AddS.add_assoc(Nat.mul(10n, Json.digits_value(t)), 1n, 1n))
        case Json.D2{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 2n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 3n),
            Dec.AddS.add_assoc(Nat.mul(10n, Json.digits_value(t)), 2n, 1n))
        case Json.D3{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 3n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 4n),
            Dec.AddS.add_assoc(Nat.mul(10n, Json.digits_value(t)), 3n, 1n))
        case Json.D4{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 4n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 5n),
            Dec.AddS.add_assoc(Nat.mul(10n, Json.digits_value(t)), 4n, 1n))
        case Json.D5{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 5n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 6n),
            Dec.AddS.add_assoc(Nat.mul(10n, Json.digits_value(t)), 5n, 1n))
        case Json.D6{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 6n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 7n),
            Dec.AddS.add_assoc(Nat.mul(10n, Json.digits_value(t)), 6n, 1n))
        case Json.D7{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 7n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 8n),
            Dec.AddS.add_assoc(Nat.mul(10n, Json.digits_value(t)), 7n, 1n))
        case Json.D8{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 8n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 9n),
            Dec.AddS.add_assoc(Nat.mul(10n, Json.digits_value(t)), 8n, 1n))
        case Json.D9{}:
          +v : Nat = Json.digits_value(t)
          e0 = Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(10n, x), 0n),
                  Json.digits_value(Json.digits_inc(t)), Nat.add(v, 1n),
                  Digits.value_inc(t))
          e1 = Dec.AddS.add_zero(Nat.mul(10n, Nat.add(v, 1n)))
          e2 = Dec.MulS.mul_ten_succ(v)
          e3 = Equal.sym(Nat,
                  Nat.add(Nat.add(Nat.mul(10n, v), 9n), 1n),
                  Nat.add(Nat.mul(10n, v), 10n),
                  Dec.AddS.add_assoc(Nat.mul(10n, v), 9n, 1n))
          Equal.trans(Nat,
            Nat.add(Nat.mul(10n, Json.digits_value(Json.digits_inc(t))), 0n),
            Nat.add(Nat.mul(10n, Nat.add(v, 1n)), 0n),
            Nat.add(Nat.add(Nat.mul(10n, v), 9n), 1n),
            e0,
            Equal.trans(Nat,
              Nat.add(Nat.mul(10n, Nat.add(v, 1n)), 0n),
              Nat.add(Nat.mul(10n, v), 10n),
              Nat.add(Nat.add(Nat.mul(10n, v), 9n), 1n),
              Equal.trans(Nat,
                Nat.add(Nat.mul(10n, Nat.add(v, 1n)), 0n),
                Nat.mul(10n, Nat.add(v, 1n)),
                Nat.add(Nat.mul(10n, v), 10n), e1, e2),
              e3))

def Digits.value_digits(n: Nat) -> {Json.digits_value(Json.digits_lsb(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      e1 = Digits.value_inc(Json.digits_lsb(p))
      e2 = Equal.cong(Nat, Nat, x => Nat.add(x, 1n),
             Json.digits_value(Json.digits_lsb(p)), p, Digits.value_digits(p))
      e3 = Dec.AddS.add_one(p)
      Equal.trans(Nat, Json.digits_value(Json.digits_lsb(1n+p)),
                  Nat.add(Json.digits_value(Json.digits_lsb(p)), 1n),
                  1n+p, e1,
                  Equal.trans(Nat,
                    Nat.add(Json.digits_value(Json.digits_lsb(p)), 1n),
                    Nat.add(p, 1n), 1n+p, e2, e3))

def Dig.show_decimal(n: Nat) ->
  {Json.digits_show(Json.digits_lsb(n)) == Spec.decimal(n) : String}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      e_show = Dig.show_value(Json.digits_lsb(1n+p), Dig.canon_lsb(1n+p, {==}))
      e_val = Digits.value_digits(1n+p)
      e_dec = Equal.cong(Nat, String, Spec.decimal,
                         Json.digits_value(Json.digits_lsb(1n+p)), 1n+p, e_val)
      Equal.trans(String,
        Json.digits_show(Json.digits_lsb(1n+p)),
        Spec.decimal(Json.digits_value(Json.digits_lsb(1n+p))),
        Spec.decimal(1n+p),
        e_show, e_dec)

def Dig.show_letter(n: Nat) ->
  {Json.show_letter(n) == Spec.decimal(n) : String}:
  Dig.show_decimal(n)

# --- printer against renderer

def RenderProof.color(c: Feedback.Color) ->
  {Json.Color.code(c) == Spec.render_color(c) : String}:
  match c:
    case Feedback.Gray{}:
      {==}
    case Feedback.Yellow{}:
      {==}
    case Feedback.Green{}:
      {==}

def RenderProof.fb_more(xs: +List<Feedback.Color>) ->
  {Json.show_feedback.more(xs) == Spec.render_feedback.more(xs) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      e_h = RenderProof.color(h)
      e_t = RenderProof.fb_more(t)
      e1 = Equal.cong(String, String,
             s => String.append(String.append(",", s), Json.show_feedback.more(t)),
             Json.Color.code(h), Spec.render_color(h), e_h)
      e2 = Equal.cong(String, String,
             s => String.append(String.append(",", Spec.render_color(h)), s),
             Json.show_feedback.more(t), Spec.render_feedback.more(t), e_t)
      Equal.trans(String,
        String.append(String.append(",", Json.Color.code(h)), Json.show_feedback.more(t)),
        String.append(String.append(",", Spec.render_color(h)), Json.show_feedback.more(t)),
        String.append(String.append(",", Spec.render_color(h)), Spec.render_feedback.more(t)),
        e1, e2)

def RenderProof.fb_body(xs: +List<Feedback.Color>) ->
  {Json.show_feedback.body(xs) == Spec.render_feedback.body(xs) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      e_h = RenderProof.color(h)
      e_t = RenderProof.fb_more(t)
      e1 = Equal.cong(String, String,
             s => String.append(s, Json.show_feedback.more(t)),
             Json.Color.code(h), Spec.render_color(h), e_h)
      e2 = Equal.cong(String, String,
             s => String.append(Spec.render_color(h), s),
             Json.show_feedback.more(t), Spec.render_feedback.more(t), e_t)
      Equal.trans(String,
        String.append(Json.Color.code(h), Json.show_feedback.more(t)),
        String.append(Spec.render_color(h), Json.show_feedback.more(t)),
        String.append(Spec.render_color(h), Spec.render_feedback.more(t)),
        e1, e2)

def RenderProof.feedback(xs: +List<Feedback.Color>) ->
  {Json.show_feedback(xs) == Spec.render_feedback(xs) : String}:
  e = RenderProof.fb_body(xs)
  e1 = Equal.cong(String, String, s => String.append("[", s),
                  Json.show_feedback.body(xs), Spec.render_feedback.body(xs), e)
  e2 = Equal.cong(String, String, s => String.append(s, "]"),
                  String.append("[", Json.show_feedback.body(xs)),
                  String.append("[", Spec.render_feedback.body(xs)), e1)
  e2

def RenderProof.nats_more(xs: +List<Nat>) ->
  {Json.show_nats.more(xs) == Spec.render_nats.more(xs) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      e_h = Dig.show_letter(h)
      e_t = RenderProof.nats_more(t)
      e1 = Equal.cong(String, String,
             s => String.append(String.append(",", s), Json.show_nats.more(t)),
             Json.show_letter(h), Spec.decimal(h), e_h)
      e2 = Equal.cong(String, String,
             s => String.append(String.append(",", Spec.decimal(h)), s),
             Json.show_nats.more(t), Spec.render_nats.more(t), e_t)
      Equal.trans(String,
        String.append(String.append(",", Json.show_letter(h)), Json.show_nats.more(t)),
        String.append(String.append(",", Spec.decimal(h)), Json.show_nats.more(t)),
        String.append(String.append(",", Spec.decimal(h)), Spec.render_nats.more(t)),
        e1, e2)

def RenderProof.nats_body(xs: +List<Nat>) ->
  {Json.show_nats.body(xs) == Spec.render_nats.body(xs) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      e_h = Dig.show_letter(h)
      e_t = RenderProof.nats_more(t)
      e1 = Equal.cong(String, String,
             s => String.append(s, Json.show_nats.more(t)),
             Json.show_letter(h), Spec.decimal(h), e_h)
      e2 = Equal.cong(String, String,
             s => String.append(Spec.decimal(h), s),
             Json.show_nats.more(t), Spec.render_nats.more(t), e_t)
      Equal.trans(String,
        String.append(Json.show_letter(h), Json.show_nats.more(t)),
        String.append(Spec.decimal(h), Json.show_nats.more(t)),
        String.append(Spec.decimal(h), Spec.render_nats.more(t)),
        e1, e2)

def RenderProof.nats(xs: +List<Nat>) ->
  {Json.show_nats(xs) == Spec.render_nats(xs) : String}:
  e = RenderProof.nats_body(xs)
  e1 = Equal.cong(String, String, s => String.append("[", s),
                  Json.show_nats.body(xs), Spec.render_nats.body(xs), e)
  Equal.cong(String, String, s => String.append(s, "]"),
             String.append("[", Json.show_nats.body(xs)),
             String.append("[", Spec.render_nats.body(xs)), e1)

def RenderProof.kids_body(kids: +List<Tree.Child>, prefix: String) ->
  {Json.show_kids.body(kids, prefix) == Spec.render_kids.body(kids, prefix) : String}:
  match kids:
    case Nil{}:
      {==}
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          match child:
            case Tree.Node{g, ckids}:
              e_f = RenderProof.fb_body(f)
              e_g = RenderProof.nats_body(g)
              e_k = RenderProof.kids_body(ckids, "")
              e_r = RenderProof.kids_body(rest, ",")
              %e_f : {String.append(prefix, SCon{'[', SCon{'[', String.append(String.append(Json.show_feedback.body(f), "]"), SCon{',', SCon{'[', SCon{'[', String.append(String.append(Json.show_nats.body(g), "]"), SCon{',', SCon{'[', String.append(Json.show_kids.body(ckids, ""), SCon{']', SCon{']', SCon{']', Json.show_kids.body(rest, ",")}}})}})}}})}}) == String.append(prefix, SCon{'[', SCon{'[', String.append(String.append(_, "]"), SCon{',', SCon{'[', SCon{'[', String.append(String.append(Spec.render_nats.body(g), "]"), SCon{',', SCon{'[', String.append(Spec.render_kids.body(ckids, ""), SCon{']', SCon{']', SCon{']', Spec.render_kids.body(rest, ",")}}})}})}}})}}) : String}
              %e_g : {String.append(prefix, SCon{'[', SCon{'[', String.append(String.append(Json.show_feedback.body(f), "]"), SCon{',', SCon{'[', SCon{'[', String.append(String.append(Json.show_nats.body(g), "]"), SCon{',', SCon{'[', String.append(Json.show_kids.body(ckids, ""), SCon{']', SCon{']', SCon{']', Json.show_kids.body(rest, ",")}}})}})}}})}}) == String.append(prefix, SCon{'[', SCon{'[', String.append(String.append(Json.show_feedback.body(f), "]"), SCon{',', SCon{'[', SCon{'[', String.append(String.append(_, "]"), SCon{',', SCon{'[', String.append(Spec.render_kids.body(ckids, ""), SCon{']', SCon{']', SCon{']', Spec.render_kids.body(rest, ",")}}})}})}}})}}) : String}
              %e_k : {String.append(prefix, SCon{'[', SCon{'[', String.append(String.append(Json.show_feedback.body(f), "]"), SCon{',', SCon{'[', SCon{'[', String.append(String.append(Json.show_nats.body(g), "]"), SCon{',', SCon{'[', String.append(Json.show_kids.body(ckids, ""), SCon{']', SCon{']', SCon{']', Json.show_kids.body(rest, ",")}}})}})}}})}}) == String.append(prefix, SCon{'[', SCon{'[', String.append(String.append(Json.show_feedback.body(f), "]"), SCon{',', SCon{'[', SCon{'[', String.append(String.append(Json.show_nats.body(g), "]"), SCon{',', SCon{'[', String.append(_, SCon{']', SCon{']', SCon{']', Spec.render_kids.body(rest, ",")}}})}})}}})}}) : String}
              %e_r : {String.append(prefix, SCon{'[', SCon{'[', String.append(String.append(Json.show_feedback.body(f), "]"), SCon{',', SCon{'[', SCon{'[', String.append(String.append(Json.show_nats.body(g), "]"), SCon{',', SCon{'[', String.append(Json.show_kids.body(ckids, ""), SCon{']', SCon{']', SCon{']', Json.show_kids.body(rest, ",")}}})}})}}})}}) == String.append(prefix, SCon{'[', SCon{'[', String.append(String.append(Json.show_feedback.body(f), "]"), SCon{',', SCon{'[', SCon{'[', String.append(String.append(Json.show_nats.body(g), "]"), SCon{',', SCon{'[', String.append(Json.show_kids.body(ckids, ""), SCon{']', SCon{']', SCon{']', _}}})}})}}})}}) : String}
              {==}

def RenderProof.kids(kids: +List<Tree.Child>) ->
  {Json.show_kids(kids) == Spec.render_kids(kids) : String}:
  e = RenderProof.kids_body(kids, "")
  e1 = Equal.cong(String, String, s => String.append("[", s),
                  Json.show_kids.body(kids, ""), Spec.render_kids.body(kids, ""), e)
  Equal.cong(String, String, s => String.append(s, "]"),
             String.append("[", Json.show_kids.body(kids, "")),
             String.append("[", Spec.render_kids.body(kids, "")), e1)

def RenderProof.print(t: Tree.Tree) ->
  {Json.print(t) == Spec.render(t) : String}:
  match t:
    case Tree.Node{g, kids}:
      e_n = RenderProof.nats_body(g)
      e_k = RenderProof.kids_body(kids, "")
      %e_n : {SCon{'[', SCon{'[', String.append(String.append(Json.show_nats.body(g), "]"), SCon{',', SCon{'[', String.append(String.append(Json.show_kids.body(kids, ""), "]"), "]")}})}} == SCon{'[', SCon{'[', String.append(String.append(_, "]"), SCon{',', SCon{'[', String.append(String.append(Spec.render_kids.body(kids, ""), "]"), "]")}})}} : String}
      %e_k : {SCon{'[', SCon{'[', String.append(String.append(Json.show_nats.body(g), "]"), SCon{',', SCon{'[', String.append(String.append(Json.show_kids.body(kids, ""), "]"), "]")}})}} == SCon{'[', SCon{'[', String.append(String.append(Json.show_nats.body(g), "]"), SCon{',', SCon{'[', String.append(String.append(_, "]"), "]")}})}} : String}
      {==}

# --- the recogniser accepts the printer output

def Rec.Start(st: Spec.State) -> Type:
  match st:
    case Spec.SValue{}:
      Unit
    case Spec.SOpen{}:
      Unit
    case Spec.SDigits{}:
      Empty
    case Spec.SAfter{}:
      Empty

def Rec.d0_start(+rest: String, +stack: +List<Unit>, st: Spec.State,
    ok: Rec.Start(st)) ->
  {Spec.recognise.go(String.append("0", rest), st, stack)
    == Spec.recognise.go(rest, Spec.SAfter{}, stack) : Maybe<String>}:
  match st:
    case Spec.SValue{}:
      {==}
    case Spec.SOpen{}:
      {==}
    case Spec.SDigits{}:
      match ok:
    case Spec.SAfter{}:
      match ok:

def Rec.d0_digits(+rest: String, +stack: +List<Unit>) ->
  {Spec.recognise.go(String.append("0", rest), Spec.SDigits{}, stack)
    == Spec.recognise.go(rest, Spec.SDigits{}, stack) : Maybe<String>}:
  {==}

def Rec.d_nonzero_start(d: Json.Digit, +rest: String, +stack: +List<Unit>,
    st: Spec.State, ok: Rec.Start(st), nz: {Dig.NZ(d) == True{} : Bool}) ->
  {Spec.recognise.go(String.append(Json.Digit.char(d), rest), st, stack)
    == Spec.recognise.go(rest, Spec.SDigits{}, stack) : Maybe<String>}:
  match d:
    case Json.D0{}:
      Empty.absurd({Spec.recognise.go(String.append(Json.Digit.char(Json.D0{}), rest), st, stack)
                    == Spec.recognise.go(rest, Spec.SDigits{}, stack) : Maybe<String>},
                   L.Proof.false_ne_true(nz))
    case Json.D1{}:
      match st:
        case Spec.SValue{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SDigits{}:
          match ok:
        case Spec.SAfter{}:
          match ok:
    case Json.D2{}:
      match st:
        case Spec.SValue{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SDigits{}:
          match ok:
        case Spec.SAfter{}:
          match ok:
    case Json.D3{}:
      match st:
        case Spec.SValue{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SDigits{}:
          match ok:
        case Spec.SAfter{}:
          match ok:
    case Json.D4{}:
      match st:
        case Spec.SValue{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SDigits{}:
          match ok:
        case Spec.SAfter{}:
          match ok:
    case Json.D5{}:
      match st:
        case Spec.SValue{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SDigits{}:
          match ok:
        case Spec.SAfter{}:
          match ok:
    case Json.D6{}:
      match st:
        case Spec.SValue{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SDigits{}:
          match ok:
        case Spec.SAfter{}:
          match ok:
    case Json.D7{}:
      match st:
        case Spec.SValue{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SDigits{}:
          match ok:
        case Spec.SAfter{}:
          match ok:
    case Json.D8{}:
      match st:
        case Spec.SValue{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SDigits{}:
          match ok:
        case Spec.SAfter{}:
          match ok:
    case Json.D9{}:
      match st:
        case Spec.SValue{}:
          {==}
        case Spec.SOpen{}:
          {==}
        case Spec.SDigits{}:
          match ok:
        case Spec.SAfter{}:
          match ok:

def Rec.d_digits(d: Json.Digit, +rest: String, +stack: +List<Unit>) ->
  {Spec.recognise.go(String.append(Json.Digit.char(d), rest), Spec.SDigits{}, stack)
    == Spec.recognise.go(rest, Spec.SDigits{}, stack) : Maybe<String>}:
  match d:
    case Json.D0{}:
      {==}
    case Json.D1{}:
      {==}
    case Json.D2{}:
      {==}
    case Json.D3{}:
      {==}
    case Json.D4{}:
      {==}
    case Json.D5{}:
      {==}
    case Json.D6{}:
      {==}
    case Json.D7{}:
      {==}
    case Json.D8{}:
      {==}
    case Json.D9{}:
      {==}

def Rec.digits_canon(ds: +List<Json.Digit>, +c: {Dig.Canon(ds) == True{} : Bool},
    +rest: String, +stack: +List<Unit>, st: Spec.State, ok: Rec.Start(st)) ->
  {Spec.recognise.go(String.append(Json.digits_show(ds), rest), st, stack)
    == Spec.recognise.go(rest, Spec.SDigits{}, stack) : Maybe<String>}:
  match ds:
    case Nil{}:
      Empty.absurd({Spec.recognise.go(String.append(Json.digits_show(Nil{}), rest), st, stack)
                    == Spec.recognise.go(rest, Spec.SDigits{}, stack) : Maybe<String>},
                   L.Proof.false_ne_true(c))
    case Con{d, t}:
      match d:
        case Json.D0{}:
          match t:
            case Nil{}:
              Empty.absurd({Spec.recognise.go(String.append(Json.digits_show(Con{Json.D0{}, Nil{}}), rest), st, stack)
                            == Spec.recognise.go(rest, Spec.SDigits{}, stack) : Maybe<String>},
                           L.Proof.false_ne_true(c))
            case Con{+h, +t2}:
              ih = Rec.digits_canon(Con{h, t2}, c, String.append(Json.Digit.char(Json.D0{}), rest), stack, st, ok)
              e_assoc = Str.append_assoc(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D0{}), rest)
              e_l = Equal.cong(String, Maybe<String>,
                       s => Spec.recognise.go(s, st, stack),
                       String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D0{})), rest),
                       String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D0{}), rest)),
                       e_assoc)
              ih2 = Rec.d_digits(Json.D0{}, rest, stack)
              Equal.trans(Maybe<String>,
                Spec.recognise.go(String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D0{})), rest), st, stack),
                Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D0{}), rest)), st, stack),
                Spec.recognise.go(rest, Spec.SDigits{}, stack),
                e_l,
                Equal.trans(Maybe<String>,
                  Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D0{}), rest)), st, stack),
                  Spec.recognise.go(String.append(Json.Digit.char(Json.D0{}), rest), Spec.SDigits{}, stack),
                  Spec.recognise.go(rest, Spec.SDigits{}, stack),
                  ih, ih2))
        case Json.D1{}:
          match t:
            case Nil{}:
              Rec.d_nonzero_start(Json.D1{}, rest, stack, st, ok, {==})
            case Con{+h, +t2}:
              ih = Rec.digits_canon(Con{h, t2}, c, String.append(Json.Digit.char(Json.D1{}), rest), stack, st, ok)
              e_assoc = Str.append_assoc(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D1{}), rest)
              e_l = Equal.cong(String, Maybe<String>,
                       s => Spec.recognise.go(s, st, stack),
                       String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D1{})), rest),
                       String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D1{}), rest)),
                       e_assoc)
              ih2 = Rec.d_digits(Json.D1{}, rest, stack)
              Equal.trans(Maybe<String>,
                Spec.recognise.go(String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D1{})), rest), st, stack),
                Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D1{}), rest)), st, stack),
                Spec.recognise.go(rest, Spec.SDigits{}, stack),
                e_l,
                Equal.trans(Maybe<String>,
                  Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D1{}), rest)), st, stack),
                  Spec.recognise.go(String.append(Json.Digit.char(Json.D1{}), rest), Spec.SDigits{}, stack),
                  Spec.recognise.go(rest, Spec.SDigits{}, stack),
                  ih, ih2))
        case Json.D2{}:
          match t:
            case Nil{}:
              Rec.d_nonzero_start(Json.D2{}, rest, stack, st, ok, {==})
            case Con{+h, +t2}:
              ih = Rec.digits_canon(Con{h, t2}, c, String.append(Json.Digit.char(Json.D2{}), rest), stack, st, ok)
              e_assoc = Str.append_assoc(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D2{}), rest)
              e_l = Equal.cong(String, Maybe<String>,
                       s => Spec.recognise.go(s, st, stack),
                       String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D2{})), rest),
                       String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D2{}), rest)),
                       e_assoc)
              ih2 = Rec.d_digits(Json.D2{}, rest, stack)
              Equal.trans(Maybe<String>,
                Spec.recognise.go(String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D2{})), rest), st, stack),
                Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D2{}), rest)), st, stack),
                Spec.recognise.go(rest, Spec.SDigits{}, stack),
                e_l,
                Equal.trans(Maybe<String>,
                  Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D2{}), rest)), st, stack),
                  Spec.recognise.go(String.append(Json.Digit.char(Json.D2{}), rest), Spec.SDigits{}, stack),
                  Spec.recognise.go(rest, Spec.SDigits{}, stack),
                  ih, ih2))
        case Json.D3{}:
          match t:
            case Nil{}:
              Rec.d_nonzero_start(Json.D3{}, rest, stack, st, ok, {==})
            case Con{+h, +t2}:
              ih = Rec.digits_canon(Con{h, t2}, c, String.append(Json.Digit.char(Json.D3{}), rest), stack, st, ok)
              e_assoc = Str.append_assoc(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D3{}), rest)
              e_l = Equal.cong(String, Maybe<String>,
                       s => Spec.recognise.go(s, st, stack),
                       String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D3{})), rest),
                       String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D3{}), rest)),
                       e_assoc)
              ih2 = Rec.d_digits(Json.D3{}, rest, stack)
              Equal.trans(Maybe<String>,
                Spec.recognise.go(String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D3{})), rest), st, stack),
                Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D3{}), rest)), st, stack),
                Spec.recognise.go(rest, Spec.SDigits{}, stack),
                e_l,
                Equal.trans(Maybe<String>,
                  Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D3{}), rest)), st, stack),
                  Spec.recognise.go(String.append(Json.Digit.char(Json.D3{}), rest), Spec.SDigits{}, stack),
                  Spec.recognise.go(rest, Spec.SDigits{}, stack),
                  ih, ih2))
        case Json.D4{}:
          match t:
            case Nil{}:
              Rec.d_nonzero_start(Json.D4{}, rest, stack, st, ok, {==})
            case Con{+h, +t2}:
              ih = Rec.digits_canon(Con{h, t2}, c, String.append(Json.Digit.char(Json.D4{}), rest), stack, st, ok)
              e_assoc = Str.append_assoc(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D4{}), rest)
              e_l = Equal.cong(String, Maybe<String>,
                       s => Spec.recognise.go(s, st, stack),
                       String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D4{})), rest),
                       String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D4{}), rest)),
                       e_assoc)
              ih2 = Rec.d_digits(Json.D4{}, rest, stack)
              Equal.trans(Maybe<String>,
                Spec.recognise.go(String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D4{})), rest), st, stack),
                Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D4{}), rest)), st, stack),
                Spec.recognise.go(rest, Spec.SDigits{}, stack),
                e_l,
                Equal.trans(Maybe<String>,
                  Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D4{}), rest)), st, stack),
                  Spec.recognise.go(String.append(Json.Digit.char(Json.D4{}), rest), Spec.SDigits{}, stack),
                  Spec.recognise.go(rest, Spec.SDigits{}, stack),
                  ih, ih2))
        case Json.D5{}:
          match t:
            case Nil{}:
              Rec.d_nonzero_start(Json.D5{}, rest, stack, st, ok, {==})
            case Con{+h, +t2}:
              ih = Rec.digits_canon(Con{h, t2}, c, String.append(Json.Digit.char(Json.D5{}), rest), stack, st, ok)
              e_assoc = Str.append_assoc(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D5{}), rest)
              e_l = Equal.cong(String, Maybe<String>,
                       s => Spec.recognise.go(s, st, stack),
                       String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D5{})), rest),
                       String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D5{}), rest)),
                       e_assoc)
              ih2 = Rec.d_digits(Json.D5{}, rest, stack)
              Equal.trans(Maybe<String>,
                Spec.recognise.go(String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D5{})), rest), st, stack),
                Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D5{}), rest)), st, stack),
                Spec.recognise.go(rest, Spec.SDigits{}, stack),
                e_l,
                Equal.trans(Maybe<String>,
                  Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D5{}), rest)), st, stack),
                  Spec.recognise.go(String.append(Json.Digit.char(Json.D5{}), rest), Spec.SDigits{}, stack),
                  Spec.recognise.go(rest, Spec.SDigits{}, stack),
                  ih, ih2))
        case Json.D6{}:
          match t:
            case Nil{}:
              Rec.d_nonzero_start(Json.D6{}, rest, stack, st, ok, {==})
            case Con{+h, +t2}:
              ih = Rec.digits_canon(Con{h, t2}, c, String.append(Json.Digit.char(Json.D6{}), rest), stack, st, ok)
              e_assoc = Str.append_assoc(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D6{}), rest)
              e_l = Equal.cong(String, Maybe<String>,
                       s => Spec.recognise.go(s, st, stack),
                       String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D6{})), rest),
                       String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D6{}), rest)),
                       e_assoc)
              ih2 = Rec.d_digits(Json.D6{}, rest, stack)
              Equal.trans(Maybe<String>,
                Spec.recognise.go(String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D6{})), rest), st, stack),
                Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D6{}), rest)), st, stack),
                Spec.recognise.go(rest, Spec.SDigits{}, stack),
                e_l,
                Equal.trans(Maybe<String>,
                  Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D6{}), rest)), st, stack),
                  Spec.recognise.go(String.append(Json.Digit.char(Json.D6{}), rest), Spec.SDigits{}, stack),
                  Spec.recognise.go(rest, Spec.SDigits{}, stack),
                  ih, ih2))
        case Json.D7{}:
          match t:
            case Nil{}:
              Rec.d_nonzero_start(Json.D7{}, rest, stack, st, ok, {==})
            case Con{+h, +t2}:
              ih = Rec.digits_canon(Con{h, t2}, c, String.append(Json.Digit.char(Json.D7{}), rest), stack, st, ok)
              e_assoc = Str.append_assoc(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D7{}), rest)
              e_l = Equal.cong(String, Maybe<String>,
                       s => Spec.recognise.go(s, st, stack),
                       String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D7{})), rest),
                       String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D7{}), rest)),
                       e_assoc)
              ih2 = Rec.d_digits(Json.D7{}, rest, stack)
              Equal.trans(Maybe<String>,
                Spec.recognise.go(String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D7{})), rest), st, stack),
                Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D7{}), rest)), st, stack),
                Spec.recognise.go(rest, Spec.SDigits{}, stack),
                e_l,
                Equal.trans(Maybe<String>,
                  Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D7{}), rest)), st, stack),
                  Spec.recognise.go(String.append(Json.Digit.char(Json.D7{}), rest), Spec.SDigits{}, stack),
                  Spec.recognise.go(rest, Spec.SDigits{}, stack),
                  ih, ih2))
        case Json.D8{}:
          match t:
            case Nil{}:
              Rec.d_nonzero_start(Json.D8{}, rest, stack, st, ok, {==})
            case Con{+h, +t2}:
              ih = Rec.digits_canon(Con{h, t2}, c, String.append(Json.Digit.char(Json.D8{}), rest), stack, st, ok)
              e_assoc = Str.append_assoc(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D8{}), rest)
              e_l = Equal.cong(String, Maybe<String>,
                       s => Spec.recognise.go(s, st, stack),
                       String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D8{})), rest),
                       String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D8{}), rest)),
                       e_assoc)
              ih2 = Rec.d_digits(Json.D8{}, rest, stack)
              Equal.trans(Maybe<String>,
                Spec.recognise.go(String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D8{})), rest), st, stack),
                Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D8{}), rest)), st, stack),
                Spec.recognise.go(rest, Spec.SDigits{}, stack),
                e_l,
                Equal.trans(Maybe<String>,
                  Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D8{}), rest)), st, stack),
                  Spec.recognise.go(String.append(Json.Digit.char(Json.D8{}), rest), Spec.SDigits{}, stack),
                  Spec.recognise.go(rest, Spec.SDigits{}, stack),
                  ih, ih2))
        case Json.D9{}:
          match t:
            case Nil{}:
              Rec.d_nonzero_start(Json.D9{}, rest, stack, st, ok, {==})
            case Con{+h, +t2}:
              ih = Rec.digits_canon(Con{h, t2}, c, String.append(Json.Digit.char(Json.D9{}), rest), stack, st, ok)
              e_assoc = Str.append_assoc(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D9{}), rest)
              e_l = Equal.cong(String, Maybe<String>,
                       s => Spec.recognise.go(s, st, stack),
                       String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D9{})), rest),
                       String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D9{}), rest)),
                       e_assoc)
              ih2 = Rec.d_digits(Json.D9{}, rest, stack)
              Equal.trans(Maybe<String>,
                Spec.recognise.go(String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(Json.D9{})), rest), st, stack),
                Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D9{}), rest)), st, stack),
                Spec.recognise.go(rest, Spec.SDigits{}, stack),
                e_l,
                Equal.trans(Maybe<String>,
                  Spec.recognise.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(Json.D9{}), rest)), st, stack),
                  Spec.recognise.go(String.append(Json.Digit.char(Json.D9{}), rest), Spec.SDigits{}, stack),
                  Spec.recognise.go(rest, Spec.SDigits{}, stack),
                  ih, ih2))
def Rec.letter_zero(+rest: String, +stack: +List<Unit>, st: Spec.State,
    ok: Rec.Start(st)) ->
  {Spec.recognise.go(String.append(Json.show_letter(0n), rest), st, stack)
    == Spec.recognise.go(rest, Spec.SAfter{}, stack) : Maybe<String>}:
  Rec.d0_start(rest, stack, st, ok)

def Rec.letter_pos(n: Nat, pos: {Nat.is_lt(0n, n) == True{} : Bool},
    +rest: String, +stack: +List<Unit>, st: Spec.State, ok: Rec.Start(st)) ->
  {Spec.recognise.go(String.append(Json.show_letter(n), rest), st, stack)
    == Spec.recognise.go(rest, Spec.SDigits{}, stack) : Maybe<String>}:
  match n:
    case 0n:
      Empty.absurd({Spec.recognise.go(String.append(Json.show_letter(0n), rest), st, stack)
                    == Spec.recognise.go(rest, Spec.SDigits{}, stack) : Maybe<String>},
                   L.Proof.false_ne_true(pos))
    case 1n++p:
      Rec.digits_canon(Json.digits_lsb(1n+p), Dig.canon_lsb(1n+p, {==}), rest, stack, st, ok)

def Rec.EndState(st: Spec.State) -> Type:
  match st:
    case Spec.SValue{}:
      Empty
    case Spec.SOpen{}:
      Empty
    case Spec.SDigits{}:
      Unit
    case Spec.SAfter{}:
      Unit

def Rec.after_comma(st: Spec.State, ok: Rec.EndState(st),
    +rest: String, +s: +List<Unit>) ->
  {Spec.recognise.go(String.append(",", rest), st, Unit{} <> s)
    == Spec.recognise.go(rest, Spec.SValue{}, Unit{} <> s) : Maybe<String>}:
  match st:
    case Spec.SValue{}:
      match ok:
    case Spec.SOpen{}:
      match ok:
    case Spec.SDigits{}:
      {==}
    case Spec.SAfter{}:
      {==}

def Rec.after_close(st: Spec.State, ok: Rec.EndState(st),
    +rest: String, +s: +List<Unit>) ->
  {Spec.recognise.go(String.append("]", rest), st, Unit{} <> s)
    == Spec.recognise.go(rest, Spec.SAfter{}, s) : Maybe<String>}:
  match st:
    case Spec.SValue{}:
      match ok:
    case Spec.SOpen{}:
      match ok:
    case Spec.SDigits{}:
      {==}
    case Spec.SAfter{}:
      {==}

def Rec.nats_body_cons(t: +List<Nat>, h: Nat, +rest: String, +s: +List<Unit>,
    st: Spec.State, ok: Rec.Start(st)) ->
  {Spec.recognise.go(String.append(Json.show_nats.body(h <> t), String.append("]", rest)), st, Unit{} <> s)
    == Spec.recognise.go(rest, Spec.SAfter{}, s) : Maybe<String>}:
  match t:
    case Nil{}:
      match h:
      case 0n:
        e_assoc = Str.append_assoc(Json.show_letter(0n), Json.show_nats.more(Nil{}), String.append("]", rest))
        e_cong = Equal.cong(String, Maybe<String>,
                       s0 => Spec.recognise.go(s0, st, Unit{} <> s),
                       String.append(String.append(Json.show_letter(0n), Json.show_nats.more(Nil{})), String.append("]", rest)),
                       String.append(Json.show_letter(0n), String.append(Json.show_nats.more(Nil{}), String.append("]", rest))),
                       e_assoc)
        e_l = Rec.letter_zero(String.append(Json.show_nats.more(Nil{}), String.append("]", rest)),
                     Unit{} <> s, st, ok)
        Equal.trans(Maybe<String>,
          Spec.recognise.go(String.append(Json.show_nats.body(0n <> Nil{}), String.append("]", rest)), st, Unit{} <> s),
          Spec.recognise.go(String.append(Json.show_letter(0n), String.append(Json.show_nats.more(Nil{}), String.append("]", rest))), st, Unit{} <> s),
          Spec.recognise.go(rest, Spec.SAfter{}, s),
              e_cong, e_l)
      case 1n++p:
        e_assoc = Str.append_assoc(Json.show_letter(1n+p), Json.show_nats.more(Nil{}), String.append("]", rest))
        e_cong = Equal.cong(String, Maybe<String>,
                       s0 => Spec.recognise.go(s0, st, Unit{} <> s),
                       String.append(String.append(Json.show_letter(1n+p), Json.show_nats.more(Nil{})), String.append("]", rest)),
                       String.append(Json.show_letter(1n+p), String.append(Json.show_nats.more(Nil{}), String.append("]", rest))),
                       e_assoc)
        e_l = Rec.letter_pos(1n+p, {==})(String.append(Json.show_nats.more(Nil{}), String.append("]", rest)),
                     Unit{} <> s, st, ok)
        Equal.trans(Maybe<String>,
          Spec.recognise.go(String.append(Json.show_nats.body((1n+p) <> Nil{}), String.append("]", rest)), st, Unit{} <> s),
          Spec.recognise.go(String.append(Json.show_letter(1n+p), String.append(Json.show_nats.more(Nil{}), String.append("]", rest))), st, Unit{} <> s),
          Spec.recognise.go(rest, Spec.SAfter{}, s),
              e_cong, e_l)
    case Con{+h2, +t2}:
      match h:
      case 0n:
            e_rec = Rec.nats_body_cons(t2, h2, rest, s, Spec.SValue{}, Unit{})
        e_assoc = Str.append_assoc(Json.show_letter(0n), Json.show_nats.more(Con{h2, t2}), String.append("]", rest))
        e_cong = Equal.cong(String, Maybe<String>,
                       s0 => Spec.recognise.go(s0, st, Unit{} <> s),
                       String.append(String.append(Json.show_letter(0n), Json.show_nats.more(Con{h2, t2})), String.append("]", rest)),
                       String.append(Json.show_letter(0n), String.append(Json.show_nats.more(Con{h2, t2}), String.append("]", rest))),
                       e_assoc)
        e_l = Rec.letter_zero(String.append(Json.show_nats.more(Con{h2, t2}), String.append("]", rest)),
                     Unit{} <> s, st, ok)
        Equal.trans(Maybe<String>,
          Spec.recognise.go(String.append(Json.show_nats.body(0n <> Con{h2, t2}), String.append("]", rest)), st, Unit{} <> s),
          Spec.recognise.go(String.append(Json.show_letter(0n), String.append(Json.show_nats.more(Con{h2, t2}), String.append("]", rest))), st, Unit{} <> s),
          Spec.recognise.go(rest, Spec.SAfter{}, s),
              e_cong,
              Equal.trans(Maybe<String>,
                Spec.recognise.go(String.append(Json.show_letter(0n), String.append(Json.show_nats.more(Con{h2, t2}), String.append("]", rest))), st, Unit{} <> s),
                Spec.recognise.go(String.append(Json.show_nats.body(h2 <> t2), String.append("]", rest)), Spec.SValue{}, Unit{} <> s),
                Spec.recognise.go(rest, Spec.SAfter{}, s),
                e_l, e_rec))
      case 1n++p:
            e_rec = Rec.nats_body_cons(t2, h2, rest, s, Spec.SValue{}, Unit{})
        e_assoc = Str.append_assoc(Json.show_letter(1n+p), Json.show_nats.more(Con{h2, t2}), String.append("]", rest))
        e_cong = Equal.cong(String, Maybe<String>,
                       s0 => Spec.recognise.go(s0, st, Unit{} <> s),
                       String.append(String.append(Json.show_letter(1n+p), Json.show_nats.more(Con{h2, t2})), String.append("]", rest)),
                       String.append(Json.show_letter(1n+p), String.append(Json.show_nats.more(Con{h2, t2}), String.append("]", rest))),
                       e_assoc)
        e_l = Rec.letter_pos(1n+p, {==})(String.append(Json.show_nats.more(Con{h2, t2}), String.append("]", rest)),
                     Unit{} <> s, st, ok)
        Equal.trans(Maybe<String>,
          Spec.recognise.go(String.append(Json.show_nats.body((1n+p) <> Con{h2, t2}), String.append("]", rest)), st, Unit{} <> s),
          Spec.recognise.go(String.append(Json.show_letter(1n+p), String.append(Json.show_nats.more(Con{h2, t2}), String.append("]", rest))), st, Unit{} <> s),
          Spec.recognise.go(rest, Spec.SAfter{}, s),
              e_cong,
              Equal.trans(Maybe<String>,
                Spec.recognise.go(String.append(Json.show_letter(1n+p), String.append(Json.show_nats.more(Con{h2, t2}), String.append("]", rest))), st, Unit{} <> s),
                Spec.recognise.go(String.append(Json.show_nats.body(h2 <> t2), String.append("]", rest)), Spec.SValue{}, Unit{} <> s),
                Spec.recognise.go(rest, Spec.SAfter{}, s),
                e_l, e_rec))

def Rec.close_open(+rest: String, +s: +List<Unit>) ->
  {Spec.recognise.go(String.append("]", rest), Spec.SOpen{}, Unit{} <> s)
    == Spec.recognise.go(rest, Spec.SAfter{}, s) : Maybe<String>}:
  {==}

def Rec.nats_body_open(xs: +List<Nat>, +rest: String, +s: +List<Unit>) ->
  {Spec.recognise.go(String.append(Json.show_nats.body(xs), String.append("]", rest)),
                      Spec.SOpen{}, Unit{} <> s)
    == Spec.recognise.go(rest, Spec.SAfter{}, s) : Maybe<String>}:
  match xs:
    case Nil{}:
      Rec.close_open(rest, s)
    case Con{h, t}:
      Rec.nats_body_cons(t, h, rest, s, Spec.SOpen{}, Unit{})

def Rec.open_array(inner: String, +rest: String, +s: +List<Unit>, st: Spec.State,
    ok: Rec.Start(st)) ->
  {Spec.recognise.go(String.append("[", String.append(inner, String.append("]", rest))), st, s)
    == Spec.recognise.go(String.append(inner, String.append("]", rest)), Spec.SOpen{}, Unit{} <> s)
   : Maybe<String>}:
  match st:
    case Spec.SValue{}:
      {==}
    case Spec.SOpen{}:
      {==}
    case Spec.SDigits{}:
      match ok:
    case Spec.SAfter{}:
      match ok:

def Rec.nats(+xs: +List<Nat>, +rest: String, +s: +List<Unit>, st: Spec.State,
    ok: Rec.Start(st)) ->
  {Spec.recognise.go(String.append(Json.show_nats(xs), rest), st, s)
    == Spec.recognise.go(rest, Spec.SAfter{}, s) : Maybe<String>}:
  +body : String = Json.show_nats.body(xs)
  +tail : String = String.append("]", rest)
  e_assoc1 = Str.append_assoc(String.append("[", body), "]", rest)
  e_assoc2 = Str.append_assoc("[", body, tail)
  e_assoc = Equal.trans(String,
    String.append(String.append(String.append("[", body), "]"), rest),
    String.append(String.append("[", body), tail),
    String.append("[", String.append(body, tail)), e_assoc1, e_assoc2)
  e_cong = Equal.cong(String, Maybe<String>, s0 => Spec.recognise.go(s0, st, s),
    String.append(String.append(String.append("[", body), "]"), rest),
    String.append("[", String.append(body, tail)), e_assoc)
  e_open = Rec.open_array(body, rest, s, st, ok)
  e_body = Rec.nats_body_open(xs, rest, s)
  Equal.trans(Maybe<String>,
    Spec.recognise.go(String.append(Json.show_nats(xs), rest), st, s),
    Spec.recognise.go(String.append("[", String.append(body, tail)), st, s),
    Spec.recognise.go(rest, Spec.SAfter{}, s),
    e_cong,
    Equal.trans(Maybe<String>,
      Spec.recognise.go(String.append("[", String.append(body, tail)), st, s),
      Spec.recognise.go(String.append(body, tail), Spec.SOpen{}, Unit{} <> s),
      Spec.recognise.go(rest, Spec.SAfter{}, s),
      e_open, e_body))

def FbNat.color_nat(c: Feedback.Color) -> Nat:
  match c:
    case Feedback.Gray{}:
      0n
    case Feedback.Yellow{}:
      1n
    case Feedback.Green{}:
      2n

def FbNat.to_nats(xs: +List<Feedback.Color>) -> +List<Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      FbNat.color_nat(h) <> FbNat.to_nats(t)

def FbNat.code(c: Feedback.Color) ->
  {Json.Color.code(c) == Json.show_letter(FbNat.color_nat(c)) : String}:
  match c:
    case Feedback.Gray{}:
      {==}
    case Feedback.Yellow{}:
      {==}
    case Feedback.Green{}:
      {==}

def FbNat.more(xs: +List<Feedback.Color>) ->
  {Json.show_feedback.more(xs) == Json.show_nats.more(FbNat.to_nats(xs)) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      e_h = FbNat.code(h)
      e_t = FbNat.more(t)
      e1 = Equal.cong(String, String,
             s => String.append(String.append(",", s), Json.show_feedback.more(t)),
             Json.Color.code(h), Json.show_letter(FbNat.color_nat(h)), e_h)
      e2 = Equal.cong(String, String,
             s => String.append(String.append(",", Json.show_letter(FbNat.color_nat(h))), s),
             Json.show_feedback.more(t), Json.show_nats.more(FbNat.to_nats(t)), e_t)
      Equal.trans(String,
        String.append(String.append(",", Json.Color.code(h)), Json.show_feedback.more(t)),
        String.append(String.append(",", Json.show_letter(FbNat.color_nat(h))), Json.show_feedback.more(t)),
        String.append(String.append(",", Json.show_letter(FbNat.color_nat(h))), Json.show_nats.more(FbNat.to_nats(t))),
        e1, e2)

def FbNat.body(xs: +List<Feedback.Color>) ->
  {Json.show_feedback.body(xs) == Json.show_nats.body(FbNat.to_nats(xs)) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      e_h = FbNat.code(h)
      e_t = FbNat.more(t)
      e1 = Equal.cong(String, String,
             s => String.append(s, Json.show_feedback.more(t)),
             Json.Color.code(h), Json.show_letter(FbNat.color_nat(h)), e_h)
      e2 = Equal.cong(String, String,
             s => String.append(Json.show_letter(FbNat.color_nat(h)), s),
             Json.show_feedback.more(t), Json.show_nats.more(FbNat.to_nats(t)), e_t)
      Equal.trans(String,
        String.append(Json.Color.code(h), Json.show_feedback.more(t)),
        String.append(Json.show_letter(FbNat.color_nat(h)), Json.show_feedback.more(t)),
        String.append(Json.show_letter(FbNat.color_nat(h)), Json.show_nats.more(FbNat.to_nats(t))),
        e1, e2)

def FbNat.feedback(xs: +List<Feedback.Color>) ->
  {Json.show_feedback(xs) == Json.show_nats(FbNat.to_nats(xs)) : String}:
  e = FbNat.body(xs)
  e1 = Equal.cong(String, String, s => String.append("[", s),
                  Json.show_feedback.body(xs), Json.show_nats.body(FbNat.to_nats(xs)), e)
  Equal.cong(String, String, s => String.append(s, "]"),
             String.append("[", Json.show_feedback.body(xs)),
             String.append("[", Json.show_nats.body(FbNat.to_nats(xs))), e1)

def Rec.feedback(+xs: +List<Feedback.Color>, +rest: String, +s: +List<Unit>,
    st: Spec.State, ok: Rec.Start(st)) ->
  {Spec.recognise.go(String.append(Json.show_feedback(xs), rest), st, s)
    == Spec.recognise.go(rest, Spec.SAfter{}, s) : Maybe<String>}:
  e_str = FbNat.feedback(xs)
  e_cong = Equal.cong(String, Maybe<String>,
    s0 => Spec.recognise.go(String.append(s0, rest), st, s),
    Json.show_feedback(xs), Json.show_nats(FbNat.to_nats(xs)), e_str)
  Equal.trans(Maybe<String>,
    Spec.recognise.go(String.append(Json.show_feedback(xs), rest), st, s),
    Spec.recognise.go(String.append(Json.show_nats(FbNat.to_nats(xs)), rest), st, s),
    Spec.recognise.go(rest, Spec.SAfter{}, s),
    e_cong, Rec.nats(FbNat.to_nats(xs), rest, s, st, ok))

# --- the kids array and the whole tree

type KidsMode is Data:
  KFirst{}
  KNext{}

def Rec.KidsFirstGoal(+kids: +List<Tree.Child>, +rest: String, +s: +List<Unit>) -> Type:
  {Spec.recognise.go(String.append(Json.show_kids.body(kids, ""), String.append("]", rest)),
                       Spec.SOpen{}, Unit{} <> s)
    == Spec.recognise.go(rest, Spec.SAfter{}, s) : Maybe<String>}

def Rec.KidsNextGoal(+kids: +List<Tree.Child>, +rest: String, +s: +List<Unit>) -> Type:
  {Spec.recognise.go(String.append(Json.show_kids.body(kids, ","), String.append("]", rest)),
                       Spec.SAfter{}, Unit{} <> s)
    == Spec.recognise.go(rest, Spec.SAfter{}, s) : Maybe<String>}

def Rec.KidsGoal(+kids: +List<Tree.Child>, mode: KidsMode, +rest: String, +s: +List<Unit>) -> Type:
  match mode:
    case KFirst{}:
      Rec.KidsFirstGoal(kids, rest, s)
    case KNext{}:
      Rec.KidsNextGoal(kids, rest, s)

def Rec.KidsCoreGoal(+f: +List<Feedback.Color>, +g: +List<Nat>,
    +ckids: +List<Tree.Child>, +restkids: +List<Tree.Child>,
    +rest: String, +s: +List<Unit>) -> Type:
  {Spec.recognise.go(
    String.append(
      String.append(Json.show_feedback(f),
        String.append(",", String.append("[",
          String.append(Json.show_nats(g),
            String.append(",", String.append("[",
              String.append(Json.show_kids.body(ckids, ""),
                String.append("]]]", Json.show_kids.body(restkids, ","))))))))),
      String.append("]", rest)),
    Spec.SOpen{}, Unit{} <> Unit{} <> s)
   == Spec.recognise.go(rest, Spec.SAfter{}, s) : Maybe<String>}

def Rec.kids_core(+f: +List<Feedback.Color>, +g: +List<Nat>,
    +ckids: +List<Tree.Child>, +restkids: +List<Tree.Child>,
    +rest: String, +s: +List<Unit>,
    recK: @r: String -> @s0: +List<Unit> -> Rec.KidsFirstGoal(ckids, r, s0),
    recR: @r: String -> @s0: +List<Unit> -> Rec.KidsNextGoal(restkids, r, s0)) ->
  Rec.KidsCoreGoal(f, g, ckids, restkids, rest, s):
  +Br : String = Json.show_kids.body(restkids, ",")
  +Bd : String = Json.show_kids.body(ckids, "")
  +Ss : String = String.append("]]]", Br)
  +Y3 : String = String.append(Bd, Ss)
  +Y2tail : String = String.append("[", Y3)
  +Y2 : String = String.append(",", Y2tail)
  +Y1tail : String = String.append(Json.show_nats(g), Y2)
  +Y1 : String = String.append("[", Y1tail)
  +Y : String = String.append(",", Y1)
  +Z : String = String.append("]", rest)
  +Gstr : String = String.append(String.append(Json.show_feedback(f), Y), Z)
  e_assoc = Str.append_assoc(Json.show_feedback(f), Y, Z)
  e1 = Equal.cong(String, Maybe<String>,
         ss => Spec.recognise.go(ss, Spec.SOpen{}, Unit{} <> Unit{} <> s),
         String.append(String.append(Json.show_feedback(f), Y), Z),
         String.append(Json.show_feedback(f), String.append(Y, Z)),
         e_assoc)
  e_fb = Rec.feedback(f, String.append(Y, Z), Unit{} <> Unit{} <> s,
                      Spec.SOpen{}, Unit{})
  e_comma1 = Rec.after_comma(Spec.SAfter{}, Unit{}, String.append(Y1, Z),
                             Unit{} <> s)
  e_assoc2 = Str.append_assoc(Json.show_nats(g), Y2, Z)
  e3 = Equal.cong(String, Maybe<String>,
         ss => Spec.recognise.go(ss, Spec.SOpen{}, Unit{} <> Unit{} <> Unit{} <> s),
         String.append(String.append(Json.show_nats(g), Y2), Z),
         String.append(Json.show_nats(g), String.append(Y2, Z)),
         e_assoc2)
  e_nats = Rec.nats(g, String.append(Y2, Z),
                    Unit{} <> Unit{} <> Unit{} <> s, Spec.SOpen{}, Unit{})
  e_comma2 = Rec.after_comma(Spec.SAfter{}, Unit{}, String.append(Y2tail, Z),
                             Unit{} <> Unit{} <> s)
  e_assoc3 = Str.append_assoc(Bd, Ss, Z)
  e4 = Equal.cong(String, Maybe<String>,
         ss => Spec.recognise.go(ss, Spec.SOpen{}, Unit{} <> Unit{} <> Unit{} <> Unit{} <> s),
         String.append(String.append(Bd, Ss), Z),
         String.append(Bd, String.append(Ss, Z)),
         e_assoc3)
  e_kids = recK(String.append("]]", String.append(Br, Z)),
                Unit{} <> Unit{} <> Unit{} <> s)
  e_close1 = Rec.after_close(Spec.SAfter{}, Unit{},
               String.append("]", String.append(Br, Z)),
               Unit{} <> Unit{} <> s)
  e_close2 = Rec.after_close(Spec.SAfter{}, Unit{}, String.append(Br, Z),
                             Unit{} <> s)
  e_tail = recR(rest, s)
  Equal.trans(Maybe<String>,
    Spec.recognise.go(Gstr, Spec.SOpen{}, Unit{} <> Unit{} <> s),
    Spec.recognise.go(String.append(Json.show_feedback(f), String.append(Y, Z)),
                      Spec.SOpen{}, Unit{} <> Unit{} <> s),
    Spec.recognise.go(rest, Spec.SAfter{}, s),
    e1,
    Equal.trans(Maybe<String>,
      Spec.recognise.go(String.append(Json.show_feedback(f), String.append(Y, Z)),
                        Spec.SOpen{}, Unit{} <> Unit{} <> s),
      Spec.recognise.go(String.append(Y, Z), Spec.SAfter{}, Unit{} <> Unit{} <> s),
      Spec.recognise.go(rest, Spec.SAfter{}, s),
      e_fb,
      Equal.trans(Maybe<String>,
        Spec.recognise.go(String.append(Y, Z), Spec.SAfter{}, Unit{} <> Unit{} <> s),
        Spec.recognise.go(String.append(Y1, Z), Spec.SValue{}, Unit{} <> Unit{} <> s),
        Spec.recognise.go(rest, Spec.SAfter{}, s),
        e_comma1,
        Equal.trans(Maybe<String>,
          Spec.recognise.go(String.append(Y1, Z), Spec.SValue{}, Unit{} <> Unit{} <> s),
          Spec.recognise.go(String.append(Y1tail, Z), Spec.SOpen{}, Unit{} <> Unit{} <> Unit{} <> s),
          Spec.recognise.go(rest, Spec.SAfter{}, s),
          {==},
          Equal.trans(Maybe<String>,
            Spec.recognise.go(String.append(Y1tail, Z), Spec.SOpen{}, Unit{} <> Unit{} <> Unit{} <> s),
            Spec.recognise.go(String.append(Json.show_nats(g), String.append(Y2, Z)),
                              Spec.SOpen{}, Unit{} <> Unit{} <> Unit{} <> s),
            Spec.recognise.go(rest, Spec.SAfter{}, s),
            e3,
            Equal.trans(Maybe<String>,
              Spec.recognise.go(String.append(Json.show_nats(g), String.append(Y2, Z)),
                                Spec.SOpen{}, Unit{} <> Unit{} <> Unit{} <> s),
              Spec.recognise.go(String.append(Y2, Z), Spec.SAfter{}, Unit{} <> Unit{} <> Unit{} <> s),
              Spec.recognise.go(rest, Spec.SAfter{}, s),
              e_nats,
              Equal.trans(Maybe<String>,
                Spec.recognise.go(String.append(Y2, Z), Spec.SAfter{}, Unit{} <> Unit{} <> Unit{} <> s),
                Spec.recognise.go(String.append(Y2tail, Z), Spec.SValue{}, Unit{} <> Unit{} <> Unit{} <> s),
                Spec.recognise.go(rest, Spec.SAfter{}, s),
                e_comma2,
                Equal.trans(Maybe<String>,
                  Spec.recognise.go(String.append(Y2tail, Z), Spec.SValue{}, Unit{} <> Unit{} <> Unit{} <> s),
                  Spec.recognise.go(String.append(Y3, Z), Spec.SOpen{}, Unit{} <> Unit{} <> Unit{} <> Unit{} <> s),
                  Spec.recognise.go(rest, Spec.SAfter{}, s),
                  {==},
                  Equal.trans(Maybe<String>,
                    Spec.recognise.go(String.append(Y3, Z), Spec.SOpen{}, Unit{} <> Unit{} <> Unit{} <> Unit{} <> s),
                    Spec.recognise.go(String.append(Bd, String.append(Ss, Z)),
                                      Spec.SOpen{}, Unit{} <> Unit{} <> Unit{} <> Unit{} <> s),
                    Spec.recognise.go(rest, Spec.SAfter{}, s),
                    e4,
                    Equal.trans(Maybe<String>,
                      Spec.recognise.go(String.append(Bd, String.append(Ss, Z)),
                                        Spec.SOpen{}, Unit{} <> Unit{} <> Unit{} <> Unit{} <> s),
                      Spec.recognise.go(String.append("]]", String.append(Br, Z)),
                                        Spec.SAfter{}, Unit{} <> Unit{} <> Unit{} <> s),
                      Spec.recognise.go(rest, Spec.SAfter{}, s),
                      e_kids,
                      Equal.trans(Maybe<String>,
                        Spec.recognise.go(String.append("]]", String.append(Br, Z)),
                                          Spec.SAfter{}, Unit{} <> Unit{} <> Unit{} <> s),
                        Spec.recognise.go(String.append("]", String.append(Br, Z)),
                                          Spec.SAfter{}, Unit{} <> Unit{} <> s),
                        Spec.recognise.go(rest, Spec.SAfter{}, s),
                        e_close1,
                        Equal.trans(Maybe<String>,
                          Spec.recognise.go(String.append("]", String.append(Br, Z)),
                                            Spec.SAfter{}, Unit{} <> Unit{} <> s),
                          Spec.recognise.go(String.append(Br, Z),
                                            Spec.SAfter{}, Unit{} <> s),
                          Spec.recognise.go(rest, Spec.SAfter{}, s),
                          e_close2,
                          e_tail))))))))))))

def Rec.kids_run(kids: +List<Tree.Child>, mode: KidsMode, +rest: String, +s: +List<Unit>) ->
    Rec.KidsGoal(kids, mode, rest, s):
  match kids:
    case Nil{}:
      match mode:
        case KFirst{}:
          Rec.close_open(rest, s)
        case KNext{}:
          Rec.after_close(Spec.SAfter{}, Unit{}, rest, s)
    case Con{c, +restkids}:
      match c:
        case Tree.Child{f, child}:
          match child:
            case Tree.Node{+g, +ckids}:
              match mode:
                case KFirst{}:
                  corev : Rec.KidsCoreGoal(f, g, ckids, restkids, rest, s) =
                    Rec.kids_core(f, g, ckids, restkids, rest, s,
                      r => s0 => Rec.kids_run(ckids, KFirst{}, r, s0),
                      r => s0 => Rec.kids_run(restkids, KNext{}, r, s0))
                  corev
                case KNext{}:
                  corev : Rec.KidsCoreGoal(f, g, ckids, restkids, rest, s) =
                    Rec.kids_core(f, g, ckids, restkids, rest, s,
                      r => s0 => Rec.kids_run(ckids, KFirst{}, r, s0),
                      r => s0 => Rec.kids_run(restkids, KNext{}, r, s0))
                  corev

def Rec.tree_after_open(+g: +List<Nat>, +kids: +List<Tree.Child>, +rest: String, +s: +List<Unit>) ->
  {Spec.recognise.go(
     String.append(
       String.append(Json.show_nats(g),
         String.append(",", String.append(Json.show_kids(kids), "]"))),
       rest),
     Spec.SOpen{}, Unit{} <> s)
   == Spec.recognise.go(rest, Spec.SAfter{}, s) : Maybe<String>}:
  +K : String = Json.show_kids(kids)
  +body : String = Json.show_kids.body(kids, "")
  +C : String = String.append(body, "]")
  +B : String = String.append(K, "]")
  +A : String = String.append(",", B)
  +Z : String = String.append("]", rest)
  +restN : String = String.append(",", String.append(B, rest))
  e_assoc1 = Str.append_assoc(Json.show_nats(g), A, rest)
  e1 = Equal.cong(String, Maybe<String>,
         ss => Spec.recognise.go(ss, Spec.SOpen{}, Unit{} <> s),
         String.append(String.append(Json.show_nats(g), A), rest),
         String.append(Json.show_nats(g), String.append(A, rest)),
         e_assoc1)
  e_nats = Rec.nats(g, restN, Unit{} <> s, Spec.SOpen{}, Unit{})
  e_comma = Rec.after_comma(Spec.SAfter{}, Unit{}, String.append(B, rest), s)
  e_assoc2 = Str.append_assoc(C, "]", rest)
  e2 = Equal.cong(String, Maybe<String>,
         ss => Spec.recognise.go(ss, Spec.SOpen{}, Unit{} <> Unit{} <> s),
         String.append(String.append(C, "]"), rest),
         String.append(C, String.append("]", rest)),
         e_assoc2)
  e_assoc3 = Str.append_assoc(body, "]", String.append("]", rest))
  e3 = Equal.cong(String, Maybe<String>,
         ss => Spec.recognise.go(ss, Spec.SOpen{}, Unit{} <> Unit{} <> s),
         String.append(String.append(body, "]"), String.append("]", rest)),
         String.append(body, String.append("]", String.append("]", rest))),
         e_assoc3)
  e_kids = Rec.kids_run(kids, KFirst{}, Z, Unit{} <> s)
  e_close = Rec.after_close(Spec.SAfter{}, Unit{}, rest, s)
  Equal.trans(Maybe<String>,
    Spec.recognise.go(String.append(String.append(Json.show_nats(g), A), rest),
                      Spec.SOpen{}, Unit{} <> s),
    Spec.recognise.go(String.append(Json.show_nats(g), String.append(A, rest)),
                      Spec.SOpen{}, Unit{} <> s),
    Spec.recognise.go(rest, Spec.SAfter{}, s),
    e1,
    Equal.trans(Maybe<String>,
      Spec.recognise.go(String.append(Json.show_nats(g), String.append(A, rest)),
                        Spec.SOpen{}, Unit{} <> s),
      Spec.recognise.go(restN, Spec.SAfter{}, Unit{} <> s),
      Spec.recognise.go(rest, Spec.SAfter{}, s),
      e_nats,
      Equal.trans(Maybe<String>,
        Spec.recognise.go(restN, Spec.SAfter{}, Unit{} <> s),
        Spec.recognise.go(String.append(B, rest), Spec.SValue{}, Unit{} <> s),
        Spec.recognise.go(rest, Spec.SAfter{}, s),
        e_comma,
        Equal.trans(Maybe<String>,
          Spec.recognise.go(String.append(B, rest), Spec.SValue{}, Unit{} <> s),
          Spec.recognise.go(String.append(String.append(C, "]"), rest),
                            Spec.SOpen{}, Unit{} <> Unit{} <> s),
          Spec.recognise.go(rest, Spec.SAfter{}, s),
          {==},
          Equal.trans(Maybe<String>,
            Spec.recognise.go(String.append(String.append(C, "]"), rest),
                              Spec.SOpen{}, Unit{} <> Unit{} <> s),
            Spec.recognise.go(String.append(C, String.append("]", rest)),
                              Spec.SOpen{}, Unit{} <> Unit{} <> s),
            Spec.recognise.go(rest, Spec.SAfter{}, s),
            e2,
            Equal.trans(Maybe<String>,
              Spec.recognise.go(String.append(C, String.append("]", rest)),
                                Spec.SOpen{}, Unit{} <> Unit{} <> s),
              Spec.recognise.go(String.append(body, String.append("]", String.append("]", rest))),
                                Spec.SOpen{}, Unit{} <> Unit{} <> s),
              Spec.recognise.go(rest, Spec.SAfter{}, s),
              e3,
              Equal.trans(Maybe<String>,
                Spec.recognise.go(String.append(body, String.append("]", String.append("]", rest))),
                                  Spec.SOpen{}, Unit{} <> Unit{} <> s),
                Spec.recognise.go(Z, Spec.SAfter{}, Unit{} <> s),
                Spec.recognise.go(rest, Spec.SAfter{}, s),
                e_kids,
                e_close)))))))

def Rec.tree(t: Tree.Tree, +rest: String, +s: +List<Unit>, st: Spec.State, ok: Rec.Start(st)) ->
  {Spec.recognise.go(String.append(Json.print(t), rest), st, s)
    == Spec.recognise.go(rest, Spec.SAfter{}, s) : Maybe<String>}:
  match t:
    case Tree.Node{g, kids}:
      match st:
        case Spec.SValue{}:
          Rec.tree_after_open(g, kids, rest, s)
        case Spec.SOpen{}:
          Rec.tree_after_open(g, kids, rest, s)
        case Spec.SDigits{}:
          match ok:
        case Spec.SAfter{}:
          match ok:
