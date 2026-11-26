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

# The clear-pass ghost operation: remove every occurrence of a code.  The clear
# pass writes a touched code's count cell to `0`; duplicate candidate lines put
# the same code in the ghost list more than once, so a single clear removes all
# of them (`rem` would leave the second copy marked, and the count cell would
# then disagree with the ghost list).
def CR.rem_cons(b: Bool, +y: Nat, +r: +List<Nat>) -> +List<Nat>:
  match b:
    case True{}:
      r
    case False{}:
      y <> r

def CR.rem_all(+x: Nat, +xs: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{y, rest}:
      +r = CR.rem_all(x, rest)
      CR.rem_cons(Nat.is_eq(x, y), y, r)

# `rem_all` at a member: the head disappears (the machine's `Nat.is_eq` decides
# it at run time; here the hypothesis is the value the decision produced).
def CR.rem_all_hit(+x: Nat, +y: Nat, +xs: +List<Nat>,
    +he: {Nat.is_eq(x, y) == True{} : Bool}) ->
  {CR.rem_all(x, y <> xs) == CR.rem_all(x, xs) : +List<Nat>}:
  Equal.trans(+List<Nat>, CR.rem_all(x, y <> xs),
    CR.rem_cons(True{}, y, CR.rem_all(x, xs)), CR.rem_all(x, xs),
    Equal.cong(Bool, +List<Nat>, b => CR.rem_cons(b, y, CR.rem_all(x, xs)),
      Nat.is_eq(x, y), True{}, he),
    {==})

def CR.rem_all_miss(+x: Nat, +y: Nat, +xs: +List<Nat>,
    +he: {Nat.is_eq(x, y) == False{} : Bool}) ->
  {CR.rem_all(x, y <> xs) == y <> CR.rem_all(x, xs) : +List<Nat>}:
  Equal.trans(+List<Nat>, CR.rem_all(x, y <> xs),
    CR.rem_cons(False{}, y, CR.rem_all(x, xs)), y <> CR.rem_all(x, xs),
    Equal.cong(Bool, +List<Nat>, b => CR.rem_cons(b, y, CR.rem_all(x, xs)),
      Nat.is_eq(x, y), False{}, he),
    {==})

# The head step of "the removed code is no longer a member".
def CR.mem_rem_cons(+x: Nat, +y: Nat, +r: +List<Nat>, b: Bool,
    +hb: {b == Nat.is_eq(x, y) : Bool},
    +h: {CR.mem(x, r) == False{} : Bool}) ->
  {CR.mem(x, CR.rem_cons(b, y, r)) == False{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      +he : {Nat.is_eq(x, y) == False{} : Bool} =
        Equal.sym(Bool, False{}, Nat.is_eq(x, y), hb)
      +e1 : {Bool.or(Nat.is_eq(x, y), CR.mem(x, r))
             == Bool.or(False{}, CR.mem(x, r)) : Bool} =
        Equal.cong(Bool, Bool, a => Bool.or(a, CR.mem(x, r)),
          Nat.is_eq(x, y), False{}, he)
      +e2 : {Bool.or(False{}, CR.mem(x, r)) == Bool.or(False{}, False{}) : Bool} =
        Equal.cong(Bool, Bool, a => Bool.or(False{}, a),
          CR.mem(x, r), False{}, h)
      Equal.trans(Bool, Bool.or(Nat.is_eq(x, y), CR.mem(x, r)),
        Bool.or(False{}, CR.mem(x, r)), False{}, e1,
        Equal.trans(Bool, Bool.or(False{}, CR.mem(x, r)),
          Bool.or(False{}, False{}), False{}, e2, {==}))

# `rem_all` removes the code from the ghost membership list for good, so the
# cleared cell's `to_u32(mem ...)` is `to_u32(False) = 0`.
def CR.mem_rem_all_self(+x: Nat, +xs: +List<Nat>) ->
  {CR.mem(x, CR.rem_all(x, xs)) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{y, rest}:
      +h = CR.mem_rem_all_self(x, rest)
      CR.mem_rem_cons(x, y, CR.rem_all(x, rest), Nat.is_eq(x, y), {==}, h)

# `is_eq(c, y) = True` is `c == y`, and `x != c` then gives `is_eq(x, y) = False`.
def CR.ne_of_eq_true(+x: Nat, +c: Nat, +y: Nat,
    +he: {Nat.is_eq(c, y) == True{} : Bool},
    +hne: {Nat.is_eq(x, c) == False{} : Bool}) ->
  {Nat.is_eq(x, y) == False{} : Bool}:
  +ecy : {c == y : Nat} = NatProof.NatPrf.is_eq_true(c, y, he)
  +eg : {Nat.is_eq(x, y) == Nat.is_eq(x, c) : Bool} =
    Equal.cong(Nat, Bool, z => Nat.is_eq(x, z), y, c, Equal.sym(Nat, c, y, ecy))
  Equal.trans(Bool, Nat.is_eq(x, y), Nat.is_eq(x, c), False{}, eg, hne)

# The head step of "any other code keeps its membership": removing `c` from the
# ghost list does not change whether `x != c` occurs.
def CR.mem_rem_cons_ne(+x: Nat, +c: Nat, +y: Nat, +r: +List<Nat>, b: Bool,
    +hb: {b == Nat.is_eq(c, y) : Bool},
    +hne: {Nat.is_eq(x, c) == False{} : Bool},
    +h: {CR.mem(x, CR.rem_all(c, r)) == CR.mem(x, r) : Bool}) ->
  {CR.mem(x, CR.rem_cons(b, y, CR.rem_all(c, r)))
   == CR.mem(x, y <> r) : Bool}:
  match b:
    case True{}:
      +he : {Nat.is_eq(c, y) == True{} : Bool} =
        Equal.sym(Bool, True{}, Nat.is_eq(c, y), hb)
      +hfy : {Nat.is_eq(x, y) == False{} : Bool} = CR.ne_of_eq_true(x, c, y, he, hne)
      +e0 : {CR.mem(x, y <> r) == Bool.or(False{}, CR.mem(x, r)) : Bool} =
        Equal.cong(Bool, Bool, a => Bool.or(a, CR.mem(x, r)),
          Nat.is_eq(x, y), False{}, hfy)
      Equal.trans(Bool, CR.mem(x, CR.rem_cons(True{}, y, CR.rem_all(c, r))),
        CR.mem(x, r), CR.mem(x, y <> r), h,
        Equal.sym(Bool, CR.mem(x, y <> r), CR.mem(x, r),
          Equal.trans(Bool, CR.mem(x, y <> r),
            Bool.or(False{}, CR.mem(x, r)), CR.mem(x, r), e0, {==})))
    case False{}:
      Equal.cong(Bool, Bool, a => Bool.or(Nat.is_eq(x, y), a),
        CR.mem(x, CR.rem_all(c, r)), CR.mem(x, r), h)

def CR.mem_rem_all_ne(+x: Nat, +c: Nat, +xs: +List<Nat>,
    +hne: {Nat.is_eq(x, c) == False{} : Bool}) ->
  {CR.mem(x, CR.rem_all(c, xs)) == CR.mem(x, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{y, rest}:
      +h = CR.mem_rem_all_ne(x, c, rest, hne)
      CR.mem_rem_cons_ne(x, c, y, rest, Nat.is_eq(c, y), {==}, hne, h)

# Removing a code below the region's base from the ghost list leaves the region
# unchanged (the membership of every cell in the region is untouched).
def CR.count_rem_before(+n: Nat, +i: Nat, +w: Nat, +xs: +List<U32>,
    +nl: +List<Nat>,
    hc: CR.Count(i, n, xs, nl),
    +hw: {Nat.is_lt(w, i) == True{} : Bool}) ->
  CR.Count(i, n, xs, CR.rem_all(w, nl)):
  match n:
    case 0n:
      hc
    case 1n+np:
      (hhead, htail) = hc
      +hne : {Nat.is_eq(i, w) == False{} : Bool} =
        CN.core_nat_eq_false_sym(w, i, CN.core_nat_eq_false_of_lt(w, i, hw))
      +hg : {Bool.to_u32(CR.mem(i, CR.rem_all(w, nl)))
             == Bool.to_u32(CR.mem(i, nl)) : U32} =
        Equal.cong(Bool, U32, b => Bool.to_u32(b),
          CR.mem(i, CR.rem_all(w, nl)), CR.mem(i, nl),
          CR.mem_rem_all_ne(i, w, nl, hne))
      +hh2 : {CS.CS.nth(xs, i)
              == Bool.to_u32(CR.mem(i, CR.rem_all(w, nl))) : U32} =
        Equal.trans(U32, CS.CS.nth(xs, i), Bool.to_u32(CR.mem(i, nl)),
          Bool.to_u32(CR.mem(i, CR.rem_all(w, nl))), hhead,
          Equal.sym(U32, Bool.to_u32(CR.mem(i, CR.rem_all(w, nl))),
            Bool.to_u32(CR.mem(i, nl)), hg))
      +hw2 : {Nat.is_lt(w, 1n+i) == True{} : Bool} =
        NatProof.Nat.is_lt_succ_of_le(w, i,
          NatProof.Nat.is_le_of_lt(w, i, hw))
      (hh2, CR.count_rem_before(np, 1n+i, w, xs, nl, htail, hw2))

# The head write of the clear pass: writing `0` at a marked cell and removing
# the code from the ghost list (`count_head` is the same step for `1`).
def CR.count_head_clear(+i: Nat, +np: Nat, +xs: +List<U32>, +nl: +List<Nat>,
    hc: CR.Count(i, 1n+np, xs, nl),
    +hi: {Nat.is_lt(i, CS.CS.len(xs)) == True{} : Bool}) ->
  CR.Count(i, 1n+np, CS.CS.set(xs, i, 0), CR.rem_all(i, nl)):
  (hhead, htail) = hc
  +hsame : {CS.CS.nth(CS.CS.set(xs, i, 0), i) == 0 : U32} =
    CS.CS.nth_set_same(xs, i, 0, hi)
  +hfalse : {CR.mem(i, CR.rem_all(i, nl)) == False{} : Bool} =
    CR.mem_rem_all_self(i, nl)
  +hrhs : {Bool.to_u32(CR.mem(i, CR.rem_all(i, nl))) == 0 : U32} =
    Equal.trans(U32, Bool.to_u32(CR.mem(i, CR.rem_all(i, nl))),
      Bool.to_u32(False{}), 0,
      Equal.cong(Bool, U32, b => Bool.to_u32(b),
        CR.mem(i, CR.rem_all(i, nl)), False{}, hfalse),
      {==})
  +hhead2 : {CS.CS.nth(CS.CS.set(xs, i, 0), i)
             == Bool.to_u32(CR.mem(i, CR.rem_all(i, nl))) : U32} =
    Equal.trans(U32, CS.CS.nth(CS.CS.set(xs, i, 0), i), 0,
      Bool.to_u32(CR.mem(i, CR.rem_all(i, nl))), hsame,
      Equal.sym(U32, Bool.to_u32(CR.mem(i, CR.rem_all(i, nl))), 0, hrhs))
  +hlt1 : {Nat.is_lt(i, 1n+i) == True{} : Bool} =
    NatProof.Nat.is_lt_succ_self(i)
  ht1 : CR.Count(1n+i, np, xs, CR.rem_all(i, nl)) =
    CR.count_rem_before(np, 1n+i, i, xs, nl, htail, hlt1)
  ht2 : CR.Count(1n+i, np, CS.CS.set(xs, i, 0), CR.rem_all(i, nl)) =
    CR.count_set_before(np, 1n+i, i, 0, xs, CR.rem_all(i, nl), ht1, hlt1)
  (hhead2, ht2)

# Moving a clear-region proof from one write index to a propositionally equal
# one (`count_shift` for the clear write and the `rem_all` ghost list).
def CR.count_clear_shift(+n: Nat, +i: Nat, +w1: Nat, +w2: Nat,
    +e: {w1 == w2 : Nat}, +xs: +List<U32>, +nl: +List<Nat>,
    hc: CR.Count(i, n, CS.CS.set(xs, w1, 0), CR.rem_all(w1, nl))) ->
  CR.Count(i, n, CS.CS.set(xs, w2, 0), CR.rem_all(w2, nl)):
  match n:
    case 0n:
      hc
    case 1n+np:
      (hhead, htail) = hc
      +ea : {CS.CS.nth(CS.CS.set(xs, w2, 0), i)
             == CS.CS.nth(CS.CS.set(xs, w1, 0), i) : U32} =
        Equal.cong(Nat, U32, z => CS.CS.nth(CS.CS.set(xs, z, 0), i),
          w2, w1, Equal.sym(Nat, w1, w2, e))
      +eb : {Bool.to_u32(CR.mem(i, CR.rem_all(w1, nl)))
             == Bool.to_u32(CR.mem(i, CR.rem_all(w2, nl))) : U32} =
        Equal.cong(Nat, U32, z => Bool.to_u32(CR.mem(i, CR.rem_all(z, nl))),
          w1, w2, e)
      +hh2 : {CS.CS.nth(CS.CS.set(xs, w2, 0), i)
              == Bool.to_u32(CR.mem(i, CR.rem_all(w2, nl))) : U32} =
        Equal.trans(U32, CS.CS.nth(CS.CS.set(xs, w2, 0), i),
          CS.CS.nth(CS.CS.set(xs, w1, 0), i),
          Bool.to_u32(CR.mem(i, CR.rem_all(w2, nl))), ea,
          Equal.trans(U32, CS.CS.nth(CS.CS.set(xs, w1, 0), i),
            Bool.to_u32(CR.mem(i, CR.rem_all(w1, nl))),
            Bool.to_u32(CR.mem(i, CR.rem_all(w2, nl))), hhead, eb))
      (hh2, CR.count_clear_shift(np, 1n+i, w1, w2, e, xs, nl, htail))

# The clear-pass update of the count region: writing `0` at the cell of code
# `i + d` (with `d < n`) and removing that code from the ghost list.  No
# membership hypothesis is needed: clearing an unmarked cell and removing an
# absent code agree cell by cell (`rem_all` is the identity when the code is
# absent, and the cell is already `0`).
def CR.count_clear(+n: Nat, +i: Nat, +d: Nat, +xs: +List<U32>,
    +nl: +List<Nat>,
    hc: CR.Count(i, n, xs, nl),
    +hd: {Nat.is_lt(d, n) == True{} : Bool},
    +hend: {Nat.is_lt(Nat.add(i, n), CS.CS.len(xs)) == True{} : Bool}) ->
  CR.Count(i, n, CS.CS.set(xs, Nat.add(i, d), 0), CR.rem_all(Nat.add(i, d), nl)):
  match n:
    case 0n:
      Empty.absurd(
        CR.Count(i, 0n, CS.CS.set(xs, Nat.add(i, d), 0),
          CR.rem_all(Nat.add(i, d), nl)),
        NatProof.Nat.not_lt_zero(d, hd))
    case 1n+np:
      match d:
        case 0n:
          +hi : {Nat.is_lt(i, CS.CS.len(xs)) == True{} : Bool} =
            NatProof.Nat.is_lt_le_trans(i, Nat.add(i, 1n+np), CS.CS.len(xs),
              CR.lt_add_pos(i, 1n+np, {==}),
              NatProof.Nat.is_le_of_lt(Nat.add(i, 1n+np), CS.CS.len(xs), hend))
          +ez : {Nat.add(i, 0n) == i : Nat} = NatProof.NatPrf.add_zero(i)
          CR.count_clear_shift(1n+np, i, i, Nat.add(i, 0n),
            Equal.sym(Nat, Nat.add(i, 0n), i, ez), xs, nl,
            CR.count_head_clear(i, np, xs, nl, hc, hi))
        case 1n+dp:
          (hhead, htail) = hc
          +hlt : {Nat.is_lt(i, Nat.add(i, 1n+dp)) == True{} : Bool} =
            CR.lt_add_pos(i, 1n+dp, {==})
          +hne : {Nat.is_eq(i, Nat.add(i, 1n+dp)) == False{} : Bool} =
            CN.core_nat_eq_false_of_lt(i, Nat.add(i, 1n+dp), hlt)
          +hnes : {Nat.is_eq(Nat.add(i, 1n+dp), i) == False{} : Bool} =
            CN.core_nat_eq_false_sym(i, Nat.add(i, 1n+dp), hne)
          +hh : {CS.CS.nth(CS.CS.set(xs, Nat.add(i, 1n+dp), 0), i)
                 == CS.CS.nth(xs, i) : U32} =
            CS.CS.nth_set_diff(xs, Nat.add(i, 1n+dp), i, 0, hnes)
          +hh2 : {CS.CS.nth(CS.CS.set(xs, Nat.add(i, 1n+dp), 0), i)
                  == Bool.to_u32(CR.mem(i, nl)) : U32} =
            Equal.trans(U32, CS.CS.nth(CS.CS.set(xs, Nat.add(i, 1n+dp), 0), i),
              CS.CS.nth(xs, i), Bool.to_u32(CR.mem(i, nl)), hh, hhead)
          +hg : {Bool.to_u32(CR.mem(i, CR.rem_all(Nat.add(i, 1n+dp), nl)))
                 == Bool.to_u32(CR.mem(i, nl)) : U32} =
            Equal.cong(Bool, U32, b => Bool.to_u32(b),
              CR.mem(i, CR.rem_all(Nat.add(i, 1n+dp), nl)), CR.mem(i, nl),
              CR.mem_rem_all_ne(i, Nat.add(i, 1n+dp), nl, hne))
          +hhead2 : {CS.CS.nth(CS.CS.set(xs, Nat.add(i, 1n+dp), 0), i)
                     == Bool.to_u32(CR.mem(i, CR.rem_all(Nat.add(i, 1n+dp), nl)))
                     : U32} =
            Equal.trans(U32, CS.CS.nth(CS.CS.set(xs, Nat.add(i, 1n+dp), 0), i),
              Bool.to_u32(CR.mem(i, nl)),
              Bool.to_u32(CR.mem(i, CR.rem_all(Nat.add(i, 1n+dp), nl))), hh2,
              Equal.sym(U32,
                Bool.to_u32(CR.mem(i, CR.rem_all(Nat.add(i, 1n+dp), nl))),
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
           CR.count_clear_shift(np, 1n+i, Nat.add(1n+i, dp), Nat.add(i, 1n+dp),
             esucc, xs, nl,
             CR.count_clear(np, 1n+i, dp, xs, nl, htail, hd, hend2)))

# --------------------------------------------------------------- touched list ---
#
# The machine appends each first occurrence at cell `256 + t`, where `t` is the
# number of distinct codes so far.  In ghost terms the touched list grows at its
# end, so the two update lemmas are "append at the end" (`touch_append`) and
# "a write at the end leaves the list" (`touch_out`, the duplicate case, where
# the machine writes the same code into the free slot past the list).

def CR.nlen(+tl: +List<Nat>) -> Nat:
  match tl:
    case Nil{}:
      0n
    case Con{d, rest}:
      Nat.add(1n, CR.nlen(rest))

def CR.snoc(+c: Nat, +tl: +List<Nat>) -> +List<Nat>:
  match tl:
    case Nil{}:
      c <> Nil{}
    case Con{d, rest}:
      d <> CR.snoc(c, rest)

# `a < b` transports to a propositionally equal `a`.
def CR.lt_rewrite_l(+a1: Nat, +a2: Nat, +b: Nat, +e: {a1 == a2 : Nat},
    h: {Nat.is_lt(a1, b) == True{} : Bool}) ->
  {Nat.is_lt(a2, b) == True{} : Bool}:
  %e : {Nat.is_lt(_, b) == True{} : Bool}
  h

# `a < b` transports to a propositionally equal `b`.
def CR.lt_rewrite_r(+a: Nat, +b1: Nat, +b2: Nat, +e: {b1 == b2 : Nat},
    h: {Nat.is_lt(a, b1) == True{} : Bool}) ->
  {Nat.is_lt(a, b2) == True{} : Bool}:
  %e : {Nat.is_lt(a, _) == True{} : Bool}
  h

# `Nat.add(a,b) == Nat.add(a,b')` from `b == b'`.
def CR.add_cong_r(+a: Nat, +b1: Nat, +b2: Nat, +e: {b1 == b2 : Nat}) ->
  {Nat.add(a, b1) == Nat.add(a, b2) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.add(a, z), b1, b2, e)

# The cell index of the append point, `256 + j + len tl`, is strictly beyond
# every cell of the region that starts at `256 + j`.
def CR.lt_append(+j: Nat, +m: Nat) ->
  {Nat.is_lt(Nat.add(256n, j), Nat.add(256n, Nat.add(j, 1n+m))) == True{} : Bool}:
  +ea : {Nat.add(Nat.add(256n, j), 1n+m) == Nat.add(256n, Nat.add(j, 1n+m)) : Nat} =
    NatProof.NatPrf.add_assoc(256n, j, 1n+m)
  +h : {Nat.is_lt(Nat.add(256n, j), Nat.add(Nat.add(256n, j), 1n+m)) == True{} : Bool} =
    CR.lt_add_pos(Nat.add(256n, j), 1n+m, {==})
  CR.lt_rewrite_r(Nat.add(256n, j), Nat.add(Nat.add(256n, j), 1n+m),
    Nat.add(256n, Nat.add(j, 1n+m)), ea, h)

# Appending a code at the append point extends the touched region.
def CR.touch_append(+tl: +List<Nat>, +j: Nat, +w: Nat, +xs: +List<U32>, +c: Nat,
    hc: CR.Touch(j, xs, tl),
    +hlen: {w == Nat.add(256n, Nat.add(j, CR.nlen(tl))) : Nat},
    +hlt: {Nat.is_lt(w, CS.CS.len(xs)) == True{} : Bool}) ->
  CR.Touch(j, CS.CS.set(xs, w, U32.from_nat(c)), CR.snoc(c, tl)):
  match tl:
    case Nil{}:
      +e0 : {Nat.add(j, 0n) == j : Nat} = NatProof.NatPrf.add_zero(j)
      +eq : {w == Nat.add(256n, j) : Nat} =
        Equal.trans(Nat, w, Nat.add(256n, Nat.add(j, 0n)), Nat.add(256n, j),
          hlen, CR.add_cong_r(256n, Nat.add(j, 0n), j, e0))
      +hli : {Nat.is_lt(Nat.add(256n, j), CS.CS.len(xs)) == True{} : Bool} =
        CR.lt_rewrite_l(w, Nat.add(256n, j), CS.CS.len(xs), eq, hlt)
      +e1 : {CS.CS.nth(CS.CS.set(xs, w, U32.from_nat(c)), Nat.add(256n, j))
             == CS.CS.nth(CS.CS.set(xs, Nat.add(256n, j), U32.from_nat(c)),
                          Nat.add(256n, j)) : U32} =
        Equal.cong(Nat, U32,
          z => CS.CS.nth(CS.CS.set(xs, z, U32.from_nat(c)), Nat.add(256n, j)),
          w, Nat.add(256n, j), eq)
      (Equal.trans(U32,
        CS.CS.nth(CS.CS.set(xs, w, U32.from_nat(c)), Nat.add(256n, j)),
        CS.CS.nth(CS.CS.set(xs, Nat.add(256n, j), U32.from_nat(c)),
          Nat.add(256n, j)),
        U32.from_nat(c), e1,
        CS.CS.nth_set_same(xs, Nat.add(256n, j), U32.from_nat(c), hli)), Unit{})
    case Con{d, rest}:
      (hhead, htail) = hc
      +esucc : {Nat.add(j, Nat.add(1n, CR.nlen(rest)))
                == Nat.add(1n+j, CR.nlen(rest)) : Nat} =
        NatProof.NatPrf.add_succ(j, CR.nlen(rest))
      +hlen2 : {w == Nat.add(256n, Nat.add(1n+j, CR.nlen(rest))) : Nat} =
        Equal.trans(Nat, w,
          Nat.add(256n, Nat.add(j, Nat.add(1n, CR.nlen(rest)))),
          Nat.add(256n, Nat.add(1n+j, CR.nlen(rest))), hlen,
          CR.add_cong_r(256n, Nat.add(j, Nat.add(1n, CR.nlen(rest))),
            Nat.add(1n+j, CR.nlen(rest)), esucc))
      +hlw : {Nat.is_lt(Nat.add(256n, j), w) == True{} : Bool} =
        CR.lt_rewrite_r(Nat.add(256n, j),
          Nat.add(256n, Nat.add(j, 1n+CR.nlen(rest))), w,
          Equal.sym(Nat, w, Nat.add(256n, Nat.add(j, 1n+CR.nlen(rest))), hlen),
          CR.lt_append(j, CR.nlen(rest)))
      +hne : {Nat.is_eq(Nat.add(256n, j), w) == False{} : Bool} =
        CN.core_nat_eq_false_of_lt(Nat.add(256n, j), w, hlw)
      +hnes : {Nat.is_eq(w, Nat.add(256n, j)) == False{} : Bool} =
        CN.core_nat_eq_false_sym(Nat.add(256n, j), w, hne)
      +hh : {CS.CS.nth(CS.CS.set(xs, w, U32.from_nat(c)), Nat.add(256n, j))
             == CS.CS.nth(xs, Nat.add(256n, j)) : U32} =
        CS.CS.nth_set_diff(xs, w, Nat.add(256n, j), U32.from_nat(c), hnes)
      +hh2 : {CS.CS.nth(CS.CS.set(xs, w, U32.from_nat(c)), Nat.add(256n, j))
              == U32.from_nat(d) : U32} =
        Equal.trans(U32,
          CS.CS.nth(CS.CS.set(xs, w, U32.from_nat(c)), Nat.add(256n, j)),
          CS.CS.nth(xs, Nat.add(256n, j)), U32.from_nat(d), hh, hhead)
      (hh2, CR.touch_append(rest, 1n+j, w, xs, c, htail, hlen2, hlt))

# A write at the append point leaves the touched region unchanged (the machine
# writes the code there even when it is already counted).
def CR.touch_out(+tl: +List<Nat>, +j: Nat, +w: Nat, +xs: +List<U32>, +v: U32,
    hc: CR.Touch(j, xs, tl),
    +hlen: {w == Nat.add(256n, Nat.add(j, CR.nlen(tl))) : Nat}) ->
  CR.Touch(j, CS.CS.set(xs, w, v), tl):
  match tl:
    case Nil{}:
      hc
    case Con{d, rest}:
      (hhead, htail) = hc
      +esucc : {Nat.add(j, Nat.add(1n, CR.nlen(rest)))
                == Nat.add(1n+j, CR.nlen(rest)) : Nat} =
        NatProof.NatPrf.add_succ(j, CR.nlen(rest))
      +hlen2 : {w == Nat.add(256n, Nat.add(1n+j, CR.nlen(rest))) : Nat} =
        Equal.trans(Nat, w,
          Nat.add(256n, Nat.add(j, Nat.add(1n, CR.nlen(rest)))),
          Nat.add(256n, Nat.add(1n+j, CR.nlen(rest))), hlen,
          CR.add_cong_r(256n, Nat.add(j, Nat.add(1n, CR.nlen(rest))),
            Nat.add(1n+j, CR.nlen(rest)), esucc))
      +hlw : {Nat.is_lt(Nat.add(256n, j), w) == True{} : Bool} =
        CR.lt_rewrite_r(Nat.add(256n, j),
          Nat.add(256n, Nat.add(j, 1n+CR.nlen(rest))), w,
          Equal.sym(Nat, w, Nat.add(256n, Nat.add(j, 1n+CR.nlen(rest))), hlen),
          CR.lt_append(j, CR.nlen(rest)))
      +hne : {Nat.is_eq(Nat.add(256n, j), w) == False{} : Bool} =
        CN.core_nat_eq_false_of_lt(Nat.add(256n, j), w, hlw)
      +hnes : {Nat.is_eq(w, Nat.add(256n, j)) == False{} : Bool} =
        CN.core_nat_eq_false_sym(Nat.add(256n, j), w, hne)
      +hh : {CS.CS.nth(CS.CS.set(xs, w, v), Nat.add(256n, j))
             == CS.CS.nth(xs, Nat.add(256n, j)) : U32} =
        CS.CS.nth_set_diff(xs, w, Nat.add(256n, j), v, hnes)
      +hh2 : {CS.CS.nth(CS.CS.set(xs, w, v), Nat.add(256n, j))
              == U32.from_nat(d) : U32} =
        Equal.trans(U32, CS.CS.nth(CS.CS.set(xs, w, v), Nat.add(256n, j)),
          CS.CS.nth(xs, Nat.add(256n, j)), U32.from_nat(d), hh, hhead)
      (hh2, CR.touch_out(rest, 1n+j, w, xs, v, htail, hlen2))

# ------------------------------------------------------- counter invariant ---
#
# The machine keeps `t` = the number of distinct codes seen, and increments it
# by `U32.sub(1, v)` where `v` is the count cell's old value (0/1).  The ghost
# counter invariant is `t = len(dedup nl)`; this is its step, and it is stated
# on the raw `dedup_cons` so no rewrite of a computed `mem` is needed (the
# machine's `CS.dedup(code <> nl)` unfolds to exactly this instantiation).

def CR.len_dedup_cons(+c: U32, b: Bool, +d: +List<U32>) ->
  {CS.CS.len(CS.CS.dedup_cons(c, b, d))
   == Nat.add(CS.CS.len(d), U32.to_nat(Bool.to_u32(Bool.not(b)))) : Nat}:
  match b:
    case True{}:
      +ez : {Nat.add(CS.CS.len(d), 0n) == CS.CS.len(d) : Nat} =
        NatProof.NatPrf.add_zero(CS.CS.len(d))
      Equal.sym(Nat, Nat.add(CS.CS.len(d), 0n), CS.CS.len(d), ez)
    case False{}:
      Equal.sym(Nat, Nat.add(CS.CS.len(d), 1n), Nat.add(1n, CS.CS.len(d)),
        NatProof.NatPrf.add_comm(CS.CS.len(d), 1n))

def CR.len_dedup_add(+c: U32, +nl: +List<U32>) ->
  {CS.CS.len(CS.CS.dedup(c <> nl))
   == Nat.add(CS.CS.len(CS.CS.dedup(nl)),
              U32.to_nat(Bool.to_u32(Bool.not(CS.CS.mem(c, nl))))) : Nat}:
  CR.len_dedup_cons(c, CS.CS.mem(c, nl), CS.CS.dedup(nl))

# --------------------------------------------------- region independence ---
#
# Each machine phase writes exactly one region, so every other region's proof
# must survive that write.  `count_set_before`/`count_set_after` already cover
# the count region; these are the touched-list and result counterparts.

# The touched region's start grows by one per induction step, so the bound
# `w < 256 + j` must move with it.
def CR.lt_shift(+j: Nat, +w: Nat,
    +hw: {Nat.is_lt(w, Nat.add(256n, j)) == True{} : Bool}) ->
  {Nat.is_lt(w, Nat.add(256n, Nat.add(1n, j))) == True{} : Bool}:
  +e : {Nat.add(256n, Nat.add(1n, j)) == Nat.add(1n, Nat.add(256n, j)) : Nat} =
    {==}
  +h1 : {Nat.is_lt(w, Nat.add(1n, Nat.add(256n, j))) == True{} : Bool} =
    NatProof.Nat.is_lt_le_trans(w, Nat.add(256n, j),
      Nat.add(1n, Nat.add(256n, j)), hw,
      NatProof.Nat.is_le_of_lt(Nat.add(256n, j), Nat.add(1n, Nat.add(256n, j)),
        NatProof.Nat.is_lt_succ_self(Nat.add(256n, j))))
  CR.lt_rewrite_r(w, Nat.add(1n, Nat.add(256n, j)),
    Nat.add(256n, Nat.add(1n, j)), Equal.sym(Nat, Nat.add(256n, Nat.add(1n, j)),
      Nat.add(1n, Nat.add(256n, j)), e), h1)

# A write below the touched region (`w < 256 + j`) leaves it unchanged; the
# machine's count-cell write is at a code `< 256`.
def CR.touch_set_below(+tl: +List<Nat>, +j: Nat, +w: Nat, +xs: +List<U32>,
    +v: U32,
    hc: CR.Touch(j, xs, tl),
    +hw: {Nat.is_lt(w, Nat.add(256n, j)) == True{} : Bool}) ->
  CR.Touch(j, CS.CS.set(xs, w, v), tl):
  match tl:
    case Nil{}:
      hc
    case Con{d, rest}:
      (hhead, htail) = hc
      +hne : {Nat.is_eq(w, Nat.add(256n, j)) == False{} : Bool} =
        CN.core_nat_eq_false_of_lt(w, Nat.add(256n, j), hw)
      +hhead2 : {CS.CS.nth(CS.CS.set(xs, w, v), Nat.add(256n, j))
                 == U32.from_nat(d) : U32} =
        Equal.trans(U32, CS.CS.nth(CS.CS.set(xs, w, v), Nat.add(256n, j)),
          CS.CS.nth(xs, Nat.add(256n, j)), U32.from_nat(d),
          CS.CS.nth_set_diff(xs, w, Nat.add(256n, j), v, hne), hhead)
      (hhead2,
       CR.touch_set_below(rest, 1n+j, w, xs, v, htail, CR.lt_shift(j, w, hw)))

# A write at or above the touched region's end leaves it unchanged; the
# machine's result-cell write is at 512 and the region ends at `256 + len tl`.
def CR.touch_set_above(+tl: +List<Nat>, +j: Nat, +w: Nat, +xs: +List<U32>,
    +v: U32,
    hc: CR.Touch(j, xs, tl),
    +hle: {Nat.is_lt(Nat.add(256n, Nat.add(j, CR.nlen(tl))), w)
           == True{} : Bool}) ->
  CR.Touch(j, CS.CS.set(xs, w, v), tl):
  match tl:
    case Nil{}:
      hc
    case Con{d, rest}:
      (hhead, htail) = hc
      +hend : {Nat.is_lt(Nat.add(256n, j),
        Nat.add(256n, Nat.add(j, 1n+CR.nlen(rest)))) == True{} : Bool} =
        CR.lt_append(j, CR.nlen(rest))
      +h2 : {Nat.is_lt(Nat.add(256n, j), w) == True{} : Bool} =
        NatProof.Nat.is_lt_le_trans(Nat.add(256n, j),
          Nat.add(256n, Nat.add(j, 1n+CR.nlen(rest))), w, hend,
          NatProof.Nat.is_le_of_lt(Nat.add(256n, Nat.add(j, 1n+CR.nlen(rest))),
            w, hle))
      +hne : {Nat.is_eq(w, Nat.add(256n, j)) == False{} : Bool} =
        CN.core_nat_eq_false_sym(Nat.add(256n, j), w,
          CN.core_nat_eq_false_of_lt(Nat.add(256n, j), w, h2))
      +hhead2 : {CS.CS.nth(CS.CS.set(xs, w, v), Nat.add(256n, j))
                 == U32.from_nat(d) : U32} =
        Equal.trans(U32, CS.CS.nth(CS.CS.set(xs, w, v), Nat.add(256n, j)),
          CS.CS.nth(xs, Nat.add(256n, j)), U32.from_nat(d),
          CS.CS.nth_set_diff(xs, w, Nat.add(256n, j), v, hne), hhead)
      +esucc : {Nat.add(j, Nat.add(1n, CR.nlen(rest)))
                == Nat.add(1n+j, CR.nlen(rest)) : Nat} =
        NatProof.NatPrf.add_succ(j, CR.nlen(rest))
      +hle2 : {Nat.is_lt(Nat.add(256n, Nat.add(1n+j, CR.nlen(rest))), w)
               == True{} : Bool} =
        CR.lt_rewrite_l(Nat.add(256n, Nat.add(j, 1n+CR.nlen(rest))),
          Nat.add(256n, Nat.add(1n+j, CR.nlen(rest))), w,
          CR.add_cong_r(256n, Nat.add(j, Nat.add(1n, CR.nlen(rest))),
            Nat.add(1n+j, CR.nlen(rest)), esucc), hle)
      (hhead2,
       CR.touch_set_above(rest, 1n+j, w, xs, v, htail, hle2))

# A write at the result cell establishes `CR.Res`.
def CR.res_set(+xs: +List<U32>, +t: U32,
    +hi: {Nat.is_lt(512n, CS.CS.len(xs)) == True{} : Bool}) ->
  CR.Res(CS.CS.set(xs, 512n, t), t):
  CS.CS.nth_set_same(xs, 512n, t, hi)
