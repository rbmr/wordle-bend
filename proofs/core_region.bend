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
