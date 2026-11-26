# Ghost region predicates for the flat count machine.
#
# The machine keeps its scratch in cells 0..767 of the flat `Array<U32>`:
#   0 .. 255    count cells, each 0 or 1
#   256 .. 511  touched list, one code per cell
#   512         result cell
# 768 ..        packed table and candidate range, never written by `dcount`.
#
# The proofs relate those cells to ghost `List`s through `CM.Store` for the
# array and the predicates below for the meaning of each region.  The count
# region stores `Bool.to_u32(mem(code, nl))`, so a count-cell read gives
# `v = to_u32(b)` for a `Bool` variable `b` and is decided by a case split,
# never by bit arithmetic.
import Base
import ./core_list.bend as CS
import ./core_nat.bend as CN
import ./nat.bend as NatProof
import ./logic.bend as Logic

# `mem(x, xs)` over `Nat` codes.
def CR.mem(+x: Nat, +xs: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{y, rest}:
      Bool.or(Nat.is_eq(x, y), CR.mem(x, rest))

def CR.mem_head_same(+x: Nat, +xs: +List<Nat>) ->
  {CR.mem(x, x <> xs) == True{} : Bool}:
  Equal.trans(Bool,
    Bool.or(Nat.is_eq(x, x), CR.mem(x, xs)),
    Bool.or(True{}, CR.mem(x, xs)),
    True{},
    Equal.cong(Bool, Bool, b => Bool.or(b, CR.mem(x, xs)),
      Nat.is_eq(x, x), True{}, NatProof.NatPrf.is_eq_refl(x)),
    {==})

def CR.mem_cons_diff(+x: Nat, +y: Nat, +xs: +List<Nat>,
    +hne: {Nat.is_eq(x, y) == False{} : Bool}) ->
  {CR.mem(x, y <> xs) == CR.mem(x, xs) : Bool}:
  Equal.cong(Bool, Bool, b => Bool.or(b, CR.mem(x, xs)),
    Nat.is_eq(x, y), False{}, hne)

# `drop` on ghost lists: the "everything from `b` on" tail.
def CR.drop(+n: Nat, +xs: +List<U32>) -> +List<U32>:
  match n:
    case 0n:
      xs
    case 1n+np:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          CR.drop(np, t)

# Writing below the dropped prefix leaves the tail equal, so every cell from
# `b` on is unchanged without a per-cell induction.
def CR.drop_set_below(+b: Nat, +xs: +List<U32>, +i: Nat, +v: U32,
    +h: {Nat.is_lt(i, b) == True{} : Bool}) ->
  {CR.drop(b, CS.CS.set(xs, i, v)) == CR.drop(b, xs) : +List<U32>}:
  match b:
    case 0n:
      Empty.absurd(
        {CR.drop(0n, CS.CS.set(xs, i, v)) == CR.drop(0n, xs) : +List<U32>},
        NatProof.Nat.not_lt_zero(i, h))
    case 1n+bp:
      match xs:
        case Nil{}:
          {==}
        case Con{x, rest}:
          match i:
            case 0n:
              {==}
            case 1n+ip:
              CR.drop_set_below(bp, rest, ip, v, h)

# `a < a + b` for a positive `b`; `Nat.add` recurses on its left argument, so
# this is an induction on `a`.
def CR.lt_add_pos(a: Nat, b: Nat,
    +hb: {Nat.is_lt(0n, b) == True{} : Bool}) ->
  {Nat.is_lt(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      hb
    case 1n+ap:
      CR.lt_add_pos(ap, b, hb)

# The count region: cell `i < 256` is `1` exactly for the codes in `nl`.
def CR.Count(+i: Nat, +n: Nat, xs: +List<U32>, +nl: +List<Nat>) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+np:
      {CS.CS.nth(xs, i) == Bool.to_u32(CR.mem(i, nl)) : U32}
      & CR.Count(1n+i, np, xs, nl)

def CR.count_get(+n: Nat, +d: Nat, +i: Nat, xs: +List<U32>, +nl: +List<Nat>,
    hc: CR.Count(i, n, xs, nl),
    +hd: {Nat.is_lt(d, n) == True{} : Bool}) ->
  {CS.CS.nth(xs, Nat.add(d, i)) == Bool.to_u32(CR.mem(Nat.add(d, i), nl))
   : U32}:
  match n:
    case 0n:
      Empty.absurd(
        {CS.CS.nth(xs, Nat.add(d, i))
         == Bool.to_u32(CR.mem(Nat.add(d, i), nl)) : U32},
        NatProof.Nat.not_lt_zero(d, hd))
    case 1n+np:
      match d:
        case 0n:
          (hhead, _) = hc
          hhead
        case 1n+dp:
          (_, htail) = hc
          +hd2 : {Nat.is_lt(dp, np) == True{} : Bool} = hd
          +ih = CR.count_get(np, dp, Nat.add(1n, i), xs, nl, htail, hd2)
          +eidx : {Nat.add(dp, Nat.add(1n, i))
                   == Nat.add(1n, Nat.add(dp, i)) : Nat} =
            NatProof.NatPrf.add_succ(dp, i)
          Equal.trans(U32,
            CS.CS.nth(xs, Nat.add(1n, Nat.add(dp, i))),
            CS.CS.nth(xs, Nat.add(dp, Nat.add(1n, i))),
            Bool.to_u32(CR.mem(Nat.add(1n, Nat.add(dp, i)), nl)),
            Equal.cong(Nat, U32, z => CS.CS.nth(xs, z),
              Nat.add(1n, Nat.add(dp, i)), Nat.add(dp, Nat.add(1n, i)),
              Equal.sym(Nat, Nat.add(dp, Nat.add(1n, i)),
                Nat.add(1n, Nat.add(dp, i)), eidx)),
            Equal.trans(U32,
              CS.CS.nth(xs, Nat.add(dp, Nat.add(1n, i))),
              Bool.to_u32(CR.mem(Nat.add(dp, Nat.add(1n, i)), nl)),
              Bool.to_u32(CR.mem(Nat.add(1n, Nat.add(dp, i)), nl)),
              ih,
              Equal.cong(Nat, U32, z => Bool.to_u32(CR.mem(z, nl)),
                Nat.add(dp, Nat.add(1n, i)), Nat.add(1n, Nat.add(dp, i)),
                eidx)))

# A write below the count region's base leaves the region unchanged (the array
# and the ghost list are untouched in the region).
def CR.count_set_before(+n: Nat, +i: Nat, +w: Nat, +v: U32,
    +xs: +List<U32>, +nl: +List<Nat>,
    hc: CR.Count(i, n, xs, nl),
    +hw: {Nat.is_lt(w, i) == True{} : Bool}) ->
  CR.Count(i, n, CS.CS.set(xs, w, v), nl):
  match n:
    case 0n:
      hc
    case 1n+np:
      (hhead, htail) = hc
      +hne : {Nat.is_eq(w, i) == False{} : Bool} =
        CN.core_nat_eq_false_of_lt(w, i, hw)
      +hh : {CS.CS.nth(CS.CS.set(xs, w, v), i) == CS.CS.nth(xs, i) : U32} =
        CS.CS.nth_set_diff(xs, w, i, v, hne)
      +hh2 : {CS.CS.nth(CS.CS.set(xs, w, v), i)
              == Bool.to_u32(CR.mem(i, nl)) : U32} =
        Equal.trans(U32, CS.CS.nth(CS.CS.set(xs, w, v), i), CS.CS.nth(xs, i),
          Bool.to_u32(CR.mem(i, nl)), hh, hhead)
      +hw2 : {Nat.is_lt(w, 1n+i) == True{} : Bool} =
        NatProof.Nat.is_lt_succ_of_le(w, i,
          NatProof.Nat.is_le_of_lt(w, i, hw))
      (hh2, CR.count_set_before(np, 1n+i, w, v, xs, nl, htail, hw2))

# A write at or above the count region's end leaves the region unchanged.
def CR.count_set_after(+n: Nat, +i: Nat, +w: Nat, +v: U32,
    +xs: +List<U32>, +nl: +List<Nat>,
    hc: CR.Count(i, n, xs, nl),
    +hw: {Nat.is_le(Nat.add(i, n), w) == True{} : Bool}) ->
  CR.Count(i, n, CS.CS.set(xs, w, v), nl):
  match n:
    case 0n:
      hc
    case 1n+np:
      (hhead, htail) = hc
      +hilt : {Nat.is_lt(i, w) == True{} : Bool} =
        NatProof.Nat.is_lt_le_trans(i, Nat.add(i, 1n+np), w,
          CR.lt_add_pos(i, 1n+np, {==}), hw)
      +hne : {Nat.is_eq(i, w) == False{} : Bool} =
        CN.core_nat_eq_false_of_lt(i, w, hilt)
      +hnes : {Nat.is_eq(w, i) == False{} : Bool} =
        CN.core_nat_eq_false_sym(i, w, hne)
      +hh : {CS.CS.nth(CS.CS.set(xs, w, v), i) == CS.CS.nth(xs, i) : U32} =
        CS.CS.nth_set_diff(xs, w, i, v, hnes)
      +hh2 : {CS.CS.nth(CS.CS.set(xs, w, v), i)
              == Bool.to_u32(CR.mem(i, nl)) : U32} =
        Equal.trans(U32, CS.CS.nth(CS.CS.set(xs, w, v), i), CS.CS.nth(xs, i),
          Bool.to_u32(CR.mem(i, nl)), hh, hhead)
      +esucc : {Nat.add(i, 1n+np) == Nat.add(1n+i, np) : Nat} =
        NatProof.NatPrf.add_succ(i, np)
      +hw2 : {Nat.is_le(Nat.add(1n+i, np), w) == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(w, Nat.add(i, 1n+np), Nat.add(1n+i, np),
          esucc, hw)
      (hh2, CR.count_set_after(np, 1n+i, w, v, xs, nl, htail, hw2))

# Adding a code outside the region to the ghost membership list leaves the
# region unchanged.
def CR.count_cons_outside(+n: Nat, +i: Nat, +w: Nat,
    +xs: +List<U32>, +nl: +List<Nat>,
    hc: CR.Count(i, n, xs, nl),
    +hw: {Nat.is_le(Nat.add(i, n), w) == True{} : Bool}) ->
  CR.Count(i, n, xs, w <> nl):
  match n:
    case 0n:
      hc
    case 1n+np:
      (hhead, htail) = hc
      +hilt : {Nat.is_lt(i, w) == True{} : Bool} =
        NatProof.Nat.is_lt_le_trans(i, Nat.add(i, 1n+np), w,
          CR.lt_add_pos(i, 1n+np, {==}), hw)
      +hne : {Nat.is_eq(i, w) == False{} : Bool} =
        CN.core_nat_eq_false_of_lt(i, w, hilt)
      +hh : {Bool.to_u32(CR.mem(i, w <> nl))
             == Bool.to_u32(CR.mem(i, nl)) : U32} =
        Equal.cong(Bool, U32, b => Bool.to_u32(b),
          CR.mem(i, w <> nl), CR.mem(i, nl),
          CR.mem_cons_diff(i, w, nl, hne))
      +hh2 : {CS.CS.nth(xs, i) == Bool.to_u32(CR.mem(i, w <> nl)) : U32} =
        Equal.trans(U32, CS.CS.nth(xs, i), Bool.to_u32(CR.mem(i, nl)),
          Bool.to_u32(CR.mem(i, w <> nl)), hhead,
          Equal.sym(U32, Bool.to_u32(CR.mem(i, w <> nl)),
            Bool.to_u32(CR.mem(i, nl)), hh))
      +esucc : {Nat.add(i, 1n+np) == Nat.add(1n+i, np) : Nat} =
        NatProof.NatPrf.add_succ(i, np)
      +hw2 : {Nat.is_le(Nat.add(1n+i, np), w) == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(w, Nat.add(i, 1n+np), Nat.add(1n+i, np),
          esucc, hw)
      (hh2, CR.count_cons_outside(np, 1n+i, w, xs, nl, htail, hw2))

# The value a count-cell read hands to the machine: `1 - v` is a closed term
# once `v` has been written as `to_u32(b)`.
def CR.count_new(+b: Bool, +v: U32,
    +hv: {v == Bool.to_u32(b) : U32}) ->
  {U32.sub(1, v) == Bool.to_u32(Bool.not(b)) : U32}:
  match b:
    case True{}:
      Equal.cong(U32, U32, x => U32.sub(1, x), v, 1, hv)
    case False{}:
      Equal.cong(U32, U32, x => U32.sub(1, x), v, 0, hv)

# The touched region: cell `256 + j` holds the `j`-th code.
def CR.Touch(+j: Nat, xs: +List<U32>, +tl: +List<Nat>) -> Type:
  match tl:
    case Nil{}:
      Unit
    case Con{c, rest}:
      {CS.CS.nth(xs, Nat.add(256n, j)) == U32.from_nat(c) : U32}
      & CR.Touch(1n+j, xs, rest)

def CR.touch_head(+j: Nat, xs: +List<U32>, +c: Nat, +rest: +List<Nat>,
    hc: CR.Touch(j, xs, c <> rest)) ->
  {CS.CS.nth(xs, Nat.add(256n, j)) == U32.from_nat(c) : U32}:
  (hhead, _) = hc
  hhead

# The result cell and the untouched tail.
def CR.Res(xs: +List<U32>, +t: U32) -> Type:
  {CS.CS.nth(xs, 512n) == t : U32}

def CR.Agree(xs: +List<U32>, +xs0: +List<U32>) -> Type:
  {CR.drop(768n, xs) == CR.drop(768n, xs0) : +List<U32>}

def CR.agree_after_set(xs: +List<U32>, +xs0: +List<U32>, +i: Nat, +v: U32,
    ha: CR.Agree(xs, xs0),
    +h: {Nat.is_lt(i, 768n) == True{} : Bool}) ->
  CR.Agree(CS.CS.set(xs, i, v), xs0):
  Equal.trans(+List<U32>,
    CR.drop(768n, CS.CS.set(xs, i, v)), CR.drop(768n, xs), CR.drop(768n, xs0),
    CR.drop_set_below(768n, xs, i, v, h), ha)

# Adding a code below the region's base to the ghost membership list leaves the
# region unchanged.
def CR.count_cons_before(+n: Nat, +i: Nat, +w: Nat,
    +xs: +List<U32>, +nl: +List<Nat>,
    hc: CR.Count(i, n, xs, nl),
    +hw: {Nat.is_lt(w, i) == True{} : Bool}) ->
  CR.Count(i, n, xs, w <> nl):
  match n:
    case 0n:
      hc
    case 1n+np:
      (hhead, htail) = hc
      +hne : {Nat.is_eq(i, w) == False{} : Bool} =
        CN.core_nat_eq_false_sym(w, i,
          CN.core_nat_eq_false_of_lt(w, i, hw))
      +hh : {Bool.to_u32(CR.mem(i, w <> nl))
             == Bool.to_u32(CR.mem(i, nl)) : U32} =
        Equal.cong(Bool, U32, b => Bool.to_u32(b),
          CR.mem(i, w <> nl), CR.mem(i, nl),
          CR.mem_cons_diff(i, w, nl, hne))
      +hh2 : {CS.CS.nth(xs, i) == Bool.to_u32(CR.mem(i, w <> nl)) : U32} =
        Equal.trans(U32, CS.CS.nth(xs, i), Bool.to_u32(CR.mem(i, nl)),
          Bool.to_u32(CR.mem(i, w <> nl)), hhead,
          Equal.sym(U32, Bool.to_u32(CR.mem(i, w <> nl)),
            Bool.to_u32(CR.mem(i, nl)), hh))
      +hw2 : {Nat.is_lt(w, 1n+i) == True{} : Bool} =
        NatProof.Nat.is_lt_succ_of_le(w, i,
          NatProof.Nat.is_le_of_lt(w, i, hw))
      (hh2, CR.count_cons_before(np, 1n+i, w, xs, nl, htail, hw2))

# The head write of the count region: writing `1` at cell `i` and adding `i` to
# the ghost list.
def CR.count_head(+i: Nat, +np: Nat, +xs: +List<U32>, +nl: +List<Nat>,
    hc: CR.Count(i, 1n+np, xs, nl),
    +hi: {Nat.is_lt(i, CS.CS.len(xs)) == True{} : Bool}) ->
  CR.Count(i, 1n+np, CS.CS.set(xs, i, 1), i <> nl):
  (hhead, htail) = hc
  +hsame : {CS.CS.nth(CS.CS.set(xs, i, 1), i) == 1 : U32} =
    CS.CS.nth_set_same(xs, i, 1, hi)
  +hrhs : {Bool.to_u32(CR.mem(i, i <> nl)) == 1 : U32} =
    Equal.trans(U32, Bool.to_u32(CR.mem(i, i <> nl)), Bool.to_u32(True{}), 1,
      Equal.cong(Bool, U32, b => Bool.to_u32(b), CR.mem(i, i <> nl), True{},
        CR.mem_head_same(i, nl)),
      {==})
  +hhead2 : {CS.CS.nth(CS.CS.set(xs, i, 1), i)
             == Bool.to_u32(CR.mem(i, i <> nl)) : U32} =
    Equal.trans(U32, CS.CS.nth(CS.CS.set(xs, i, 1), i), 1,
      Bool.to_u32(CR.mem(i, i <> nl)), hsame,
      Equal.sym(U32, Bool.to_u32(CR.mem(i, i <> nl)), 1, hrhs))
  +hlt1 : {Nat.is_lt(i, 1n+i) == True{} : Bool} =
    NatProof.Nat.is_lt_succ_self(i)
  ht1 : CR.Count(1n+i, np, xs, i <> nl) =
    CR.count_cons_before(np, 1n+i, i, xs, nl, htail, hlt1)
  ht2 : CR.Count(1n+i, np, CS.CS.set(xs, i, 1), i <> nl) =
    CR.count_set_before(np, 1n+i, i, 1, xs, i <> nl, ht1, hlt1)
  (hhead2, ht2)

# Rewriting a strict bound's first argument (both directions are just `%e`).
def CR.is_lt_rewrite(+a: Nat, +b: Nat, +c: Nat, +e: {a == b : Nat},
    h: {Nat.is_lt(a, c) == True{} : Bool}) ->
  {Nat.is_lt(b, c) == True{} : Bool}:
  %e : {Nat.is_lt(_, c) == True{} : Bool}
  h

# Moving a count-region proof from one write index to a propositionally equal
# one (the two occurrences of the index in the array and the ghost list).
def CR.count_shift(+n: Nat, +i: Nat, +w1: Nat, +w2: Nat,
    +e: {w1 == w2 : Nat}, +xs: +List<U32>, +nl: +List<Nat>,
    hc: CR.Count(i, n, CS.CS.set(xs, w1, 1), w1 <> nl)) ->
  CR.Count(i, n, CS.CS.set(xs, w2, 1), w2 <> nl):
  match n:
    case 0n:
      hc
    case 1n+np:
      (hhead, htail) = hc
      +ea : {CS.CS.nth(CS.CS.set(xs, w2, 1), i)
             == CS.CS.nth(CS.CS.set(xs, w1, 1), i) : U32} =
        Equal.cong(Nat, U32, z => CS.CS.nth(CS.CS.set(xs, z, 1), i),
          w2, w1, Equal.sym(Nat, w1, w2, e))
      +eb : {Bool.to_u32(CR.mem(i, w1 <> nl))
             == Bool.to_u32(CR.mem(i, w2 <> nl)) : U32} =
        Equal.cong(Nat, U32, z => Bool.to_u32(CR.mem(i, z <> nl)), w1, w2, e)
      +hh2 : {CS.CS.nth(CS.CS.set(xs, w2, 1), i)
              == Bool.to_u32(CR.mem(i, w2 <> nl)) : U32} =
        Equal.trans(U32, CS.CS.nth(CS.CS.set(xs, w2, 1), i),
          CS.CS.nth(CS.CS.set(xs, w1, 1), i), Bool.to_u32(CR.mem(i, w2 <> nl)),
          ea,
          Equal.trans(U32, CS.CS.nth(CS.CS.set(xs, w1, 1), i),
            Bool.to_u32(CR.mem(i, w1 <> nl)),
            Bool.to_u32(CR.mem(i, w2 <> nl)), hhead, eb))
      (hh2, CR.count_shift(np, 1n+i, w1, w2, e, xs, nl, htail))

# The count-region update the candidate pass needs: writing `1` at the cell of
# code `i + d` (with `d < n`) and adding that code to the ghost membership
# list.  The array write and the list update are the two changes the machine
# makes in phase 3.
def CR.count_set_new(+n: Nat, +i: Nat, +d: Nat, +xs: +List<U32>,
    +nl: +List<Nat>,
    hc: CR.Count(i, n, xs, nl),
    +hd: {Nat.is_lt(d, n) == True{} : Bool},
    +hend: {Nat.is_lt(Nat.add(i, n), CS.CS.len(xs)) == True{} : Bool}) ->
  CR.Count(i, n, CS.CS.set(xs, Nat.add(i, d), 1), Nat.add(i, d) <> nl):
  match n:
    case 0n:
      Empty.absurd(
        CR.Count(i, 0n, CS.CS.set(xs, Nat.add(i, d), 1), Nat.add(i, d) <> nl),
        NatProof.Nat.not_lt_zero(d, hd))
    case 1n+np:
      match d:
        case 0n:
          +hi : {Nat.is_lt(i, CS.CS.len(xs)) == True{} : Bool} =
            NatProof.Nat.is_lt_le_trans(i, Nat.add(i, 1n+np), CS.CS.len(xs),
              CR.lt_add_pos(i, 1n+np, {==}),
              NatProof.Nat.is_le_of_lt(Nat.add(i, 1n+np), CS.CS.len(xs),
                hend))
          +ez : {Nat.add(i, 0n) == i : Nat} = NatProof.NatPrf.add_zero(i)
          CR.count_shift(1n+np, i, i, Nat.add(i, 0n),
            Equal.sym(Nat, Nat.add(i, 0n), i, ez), xs, nl,
            CR.count_head(i, np, xs, nl, hc, hi))
        case 1n+dp:
          (hhead, htail) = hc
          +hlt : {Nat.is_lt(i, Nat.add(i, 1n+dp)) == True{} : Bool} =
            CR.lt_add_pos(i, 1n+dp, {==})
          +hne : {Nat.is_eq(i, Nat.add(i, 1n+dp)) == False{} : Bool} =
            CN.core_nat_eq_false_of_lt(i, Nat.add(i, 1n+dp), hlt)
          +hnes : {Nat.is_eq(Nat.add(i, 1n+dp), i) == False{} : Bool} =
            CN.core_nat_eq_false_sym(i, Nat.add(i, 1n+dp), hne)
          +hh : {CS.CS.nth(CS.CS.set(xs, Nat.add(i, 1n+dp), 1), i)
                 == CS.CS.nth(xs, i) : U32} =
            CS.CS.nth_set_diff(xs, Nat.add(i, 1n+dp), i, 1, hnes)
          +hh2 : {CS.CS.nth(CS.CS.set(xs, Nat.add(i, 1n+dp), 1), i)
                  == Bool.to_u32(CR.mem(i, nl)) : U32} =
            Equal.trans(U32, CS.CS.nth(CS.CS.set(xs, Nat.add(i, 1n+dp), 1), i),
              CS.CS.nth(xs, i), Bool.to_u32(CR.mem(i, nl)), hh, hhead)
          +hg : {Bool.to_u32(CR.mem(i, Nat.add(i, 1n+dp) <> nl))
                 == Bool.to_u32(CR.mem(i, nl)) : U32} =
            Equal.cong(Bool, U32, b => Bool.to_u32(b),
              CR.mem(i, Nat.add(i, 1n+dp) <> nl), CR.mem(i, nl),
              CR.mem_cons_diff(i, Nat.add(i, 1n+dp), nl, hne))
          +hhead2 : {CS.CS.nth(CS.CS.set(xs, Nat.add(i, 1n+dp), 1), i)
                     == Bool.to_u32(CR.mem(i, Nat.add(i, 1n+dp) <> nl))
                     : U32} =
            Equal.trans(U32, CS.CS.nth(CS.CS.set(xs, Nat.add(i, 1n+dp), 1), i),
              Bool.to_u32(CR.mem(i, nl)),
              Bool.to_u32(CR.mem(i, Nat.add(i, 1n+dp) <> nl)), hh2,
              Equal.sym(U32,
                Bool.to_u32(CR.mem(i, Nat.add(i, 1n+dp) <> nl)),
                Bool.to_u32(CR.mem(i, nl)), hg))
          +esucc : {Nat.add(1n+i, dp) == Nat.add(i, 1n+dp) : Nat} =
            Equal.sym(Nat, Nat.add(i, 1n+dp), Nat.add(1n+i, dp),
              NatProof.NatPrf.add_succ(i, dp))
          +esucc2 : {Nat.add(i, 1n+np) == Nat.add(1n+i, np) : Nat} =
            NatProof.NatPrf.add_succ(i, np)
          +hend2 : {Nat.is_lt(Nat.add(1n+i, np), CS.CS.len(xs))
                    == True{} : Bool} =
            CR.is_lt_rewrite(Nat.add(i, 1n+np), Nat.add(1n+i, np),
              CS.CS.len(xs), esucc2, hend)
          (hhead2,
           CR.count_shift(np, 1n+i, Nat.add(1n+i, dp), Nat.add(i, 1n+dp),
             esucc, xs, nl,
             CR.count_set_new(np, 1n+i, dp, xs, nl, htail, hd, hend2)))
