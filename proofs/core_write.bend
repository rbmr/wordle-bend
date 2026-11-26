# Writes for the flat-array cell model.
#
# `CM.Store` (`proofs/core_store.bend`) relates the runtime `Array<U32>` to a
# ghost `List<U32>` of cell values.  The count machine writes cells, so the
# model needs the write direction: a write inside a subtree's range updates the
# ghost list at that cell, and a write outside a range leaves the subtree's
# model alone.  The outside direction is what makes the sibling subtree survive
# a write into the other child, and it is stated as a strict bound only
# (`before` / `after`), so no index arithmetic beyond `Nat.is_lt` is needed.
#
# `Array.set` is `fst(Array.swap)` and `Array.swap` masks its index against the
# block size, so the wrapper `CM.store_set` follows the same chain as
# `CM.store_read` in `core_store.bend`: depth, size, mask, then the recursive
# write lemma on `Array.swap.go`.
import Base
import ./array.bend as Arr
import ./nat.bend as NatProof
import ./fast_tbl.bend as FT
import ./core_list.bend as CS
import ./core_nat.bend as CN
import ./core_store.bend as CMem

# The ghost list is long enough for a subtree whose cells are
# `base .. base + 2^d - 1`.  Only a leaf write needs it (`nth` on a short list
# returns 0, so `nth_set_same` needs the cell to exist).  The predicate is
# written out where it is used: a `def` returning a `Bool` equality is a
# `Type`, so it could not be a reusable (`+`) hypothesis.

# `x <= x + y`.
def CW.le_add_r(+x: Nat, +y: Nat) ->
  {Nat.is_le(x, Nat.add(x, y)) == True{} : Bool}:
  +h1 : {Nat.is_le(x, Nat.add(y, x)) == True{} : Bool} =
    NatProof.Nat.is_le_add_self_l(y, x)
  Equal.trans(Bool, Nat.is_le(x, Nat.add(x, y)), Nat.is_le(x, Nat.add(y, x)),
    True{},
    Equal.sym(Bool, Nat.is_le(x, Nat.add(y, x)), Nat.is_le(x, Nat.add(x, y)),
      Equal.cong(Nat, Bool, z => Nat.is_le(x, z), Nat.add(y, x),
        Nat.add(x, y), NatProof.NatPrf.add_comm(y, x))),
    h1)

# `base <= base + 2^d` implies nothing about `2^d`; these two lemmas shift the
# bound from a parent's range to a child's range.
def CW.sub_node_l(+p: Nat, +base: Nat, +xs: +List<U32>,
    +h: {Nat.is_le(Nat.add(base, FT.FT.pow2(1n+p)), CS.CS.len(xs))
         == True{} : Bool}) ->
  {Nat.is_le(Nat.add(base, FT.FT.pow2(p)), CS.CS.len(xs)) == True{} : Bool}:
  NatProof.Nat.is_le_trans(Nat.add(base, FT.FT.pow2(p)),
    Nat.add(Nat.add(base, FT.FT.pow2(p)), FT.FT.pow2(p)),
    CS.CS.len(xs),
    CW.le_add_r(Nat.add(base, FT.FT.pow2(p)), FT.FT.pow2(p)),
    Equal.trans(Bool,
      Nat.is_le(Nat.add(Nat.add(base, FT.FT.pow2(p)), FT.FT.pow2(p)),
        CS.CS.len(xs)),
      Nat.is_le(Nat.add(base, Nat.add(FT.FT.pow2(p), FT.FT.pow2(p))),
        CS.CS.len(xs)),
      True{},
      Equal.cong(Nat, Bool, z => Nat.is_le(z, CS.CS.len(xs)),
        Nat.add(Nat.add(base, FT.FT.pow2(p)), FT.FT.pow2(p)),
        Nat.add(base, Nat.add(FT.FT.pow2(p), FT.FT.pow2(p))),
        NatProof.NatPrf.add_assoc(base, FT.FT.pow2(p), FT.FT.pow2(p))),
      h))

def CW.sub_node_r(+p: Nat, +base: Nat, +xs: +List<U32>,
    +h: {Nat.is_le(Nat.add(base, FT.FT.pow2(1n+p)), CS.CS.len(xs))
         == True{} : Bool}) ->
  {Nat.is_le(Nat.add(Nat.add(base, FT.FT.pow2(p)), FT.FT.pow2(p)),
     CS.CS.len(xs)) == True{} : Bool}:
  Equal.trans(Bool,
    Nat.is_le(Nat.add(Nat.add(base, FT.FT.pow2(p)), FT.FT.pow2(p)),
      CS.CS.len(xs)),
    Nat.is_le(Nat.add(base, Nat.add(FT.FT.pow2(p), FT.FT.pow2(p))),
      CS.CS.len(xs)),
    True{},
    Equal.cong(Nat, Bool, z => Nat.is_le(z, CS.CS.len(xs)),
      Nat.add(Nat.add(base, FT.FT.pow2(p)), FT.FT.pow2(p)),
      Nat.add(base, Nat.add(FT.FT.pow2(p), FT.FT.pow2(p))),
      NatProof.NatPrf.add_assoc(base, FT.FT.pow2(p), FT.FT.pow2(p))),
    h)

# A write leaves the length bound alone.
def CW.sub_set(+d: Nat, +base: Nat, +xs: +List<U32>, +i: Nat, +v: U32,
    +h: {Nat.is_le(Nat.add(base, FT.FT.pow2(d)), CS.CS.len(xs))
         == True{} : Bool}) ->
  {Nat.is_le(Nat.add(base, FT.FT.pow2(d)), CS.CS.len(CS.CS.set(xs, i, v)))
   == True{} : Bool}:
  Equal.trans(Bool,
    Nat.is_le(Nat.add(base, FT.FT.pow2(d)), CS.CS.len(CS.CS.set(xs, i, v))),
    Nat.is_le(Nat.add(base, FT.FT.pow2(d)), CS.CS.len(xs)),
    True{},
    Equal.cong(Nat, Bool, z => Nat.is_le(Nat.add(base, FT.FT.pow2(d)), z),
      CS.CS.len(CS.CS.set(xs, i, v)), CS.CS.len(xs),
      CS.CS.len_set(xs, i, v)),
    h)

# At the root the range starts at 0.
def CW.sub_zero(+d: Nat, +xs: +List<U32>,
    +h: {CS.CS.len(xs) == FT.FT.pow2(d) : Nat}) ->
  {Nat.is_le(Nat.add(0n, FT.FT.pow2(d)), CS.CS.len(xs)) == True{} : Bool}:
  Equal.trans(Bool,
    Nat.is_le(FT.FT.pow2(d), CS.CS.len(xs)),
    Nat.is_le(FT.FT.pow2(d), FT.FT.pow2(d)),
    True{},
    Equal.cong(Nat, Bool, z => Nat.is_le(FT.FT.pow2(d), z),
      CS.CS.len(xs), FT.FT.pow2(d), h),
    NatProof.Nat.is_le_refl(FT.FT.pow2(d)))

# A write strictly below a subtree's range leaves its model unchanged.
def CW.store_before(+d: Nat, +base: Nat, a: Array<U32>, +xs: +List<U32>,
    +w: Nat, +v: U32,
    +h: {Nat.is_lt(w, base) == True{} : Bool},
    +hs: CMem.CM.Store(d, base, a, xs)) ->
  CMem.CM.Store(d, base, a, CS.CS.set(xs, w, v)):
  match d:
    case 0n:
      match a:
        case ALeaf{x}:
          +hne : {Nat.is_eq(w, base) == False{} : Bool} =
            CN.core_nat_eq_false_of_lt(w, base, h)
          Equal.trans(U32, x, CS.CS.nth(xs, base),
            CS.CS.nth(CS.CS.set(xs, w, v), base), hs,
            Equal.sym(U32, CS.CS.nth(CS.CS.set(xs, w, v), base),
              CS.CS.nth(xs, base),
              CS.CS.nth_set_diff(xs, w, base, v, hne)))
        case ANode{x, y}:
          Empty.absurd(CMem.CM.Store(0n, base, ANode{x, y},
            CS.CS.set(xs, w, v)), hs)
    case 1n++p:
      match a:
        case ALeaf{x}:
          Empty.absurd(CMem.CM.Store(1n+p, base, ALeaf{x},
            CS.CS.set(xs, w, v)), hs)
        case ANode{x, y}:
          Arr.DPair{+hx, +hy} = hs
          +hb : {Nat.is_lt(w, Nat.add(base, FT.FT.pow2(p))) == True{} : Bool} =
            NatProof.Nat.is_lt_le_trans(w, base, Nat.add(base, FT.FT.pow2(p)),
              h, CW.le_add_r(base, FT.FT.pow2(p)))
          Arr.DPair{
            CW.store_before(p, base, x, xs, w, v, h, hx),
            CW.store_before(p, Nat.add(base, FT.FT.pow2(p)), y, xs, w, v,
              hb, hy)}

# A write at or after the end of a subtree's range leaves its model unchanged.
def CW.store_after(+d: Nat, +base: Nat, a: Array<U32>, +xs: +List<U32>,
    +w: Nat, +v: U32,
    +h: {Nat.is_le(Nat.add(base, FT.FT.pow2(d)), w) == True{} : Bool},
    +hs: CMem.CM.Store(d, base, a, xs)) ->
  CMem.CM.Store(d, base, a, CS.CS.set(xs, w, v)):
  match d:
    case 0n:
      match a:
        case ALeaf{x}:
          +hlt : {Nat.is_lt(base, w) == True{} : Bool} =
            CN.core_nat_lt_of_le_succ(base, w,
              Equal.trans(Bool, Nat.is_le(1n+base, w),
                Nat.is_le(Nat.add(base, 1n), w), True{},
                Equal.cong(Nat, Bool, z => Nat.is_le(z, w),
                  1n+base, Nat.add(base, 1n),
                  Equal.sym(Nat, Nat.add(base, 1n), 1n+base,
                    NatProof.NatPrf.add_comm(base, 1n))),
                h))
          +hne : {Nat.is_eq(w, base) == False{} : Bool} =
            CN.core_nat_eq_false_sym(base, w,
              CN.core_nat_eq_false_of_lt(base, w, hlt))
          Equal.trans(U32, x, CS.CS.nth(xs, base),
            CS.CS.nth(CS.CS.set(xs, w, v), base), hs,
            Equal.sym(U32, CS.CS.nth(CS.CS.set(xs, w, v), base),
              CS.CS.nth(xs, base),
              CS.CS.nth_set_diff(xs, w, base, v, hne)))
        case ANode{x, y}:
          Empty.absurd(CMem.CM.Store(0n, base, ANode{x, y},
            CS.CS.set(xs, w, v)), hs)
    case 1n++p:
      match a:
        case ALeaf{x}:
          Empty.absurd(CMem.CM.Store(1n+p, base, ALeaf{x},
            CS.CS.set(xs, w, v)), hs)
        case ANode{x, y}:
          Arr.DPair{+hx, +hy} = hs
          +hge : {Nat.is_le(Nat.add(Nat.add(base, FT.FT.pow2(p)),
                       FT.FT.pow2(p)), w) == True{} : Bool} =
            Equal.trans(Bool,
              Nat.is_le(Nat.add(Nat.add(base, FT.FT.pow2(p)), FT.FT.pow2(p)), w),
              Nat.is_le(Nat.add(base, Nat.add(FT.FT.pow2(p), FT.FT.pow2(p))), w),
              True{},
              Equal.cong(Nat, Bool, z => Nat.is_le(z, w),
                Nat.add(Nat.add(base, FT.FT.pow2(p)), FT.FT.pow2(p)),
                Nat.add(base, Nat.add(FT.FT.pow2(p), FT.FT.pow2(p))),
                NatProof.NatPrf.add_assoc(base, FT.FT.pow2(p),
                  FT.FT.pow2(p))),
              h)
          Arr.DPair{
            CW.store_after(p, base, x, xs, w, v,
              NatProof.Nat.is_le_trans(Nat.add(base, FT.FT.pow2(p)),
                Nat.add(Nat.add(base, FT.FT.pow2(p)), FT.FT.pow2(p)), w,
                CW.le_add_r(Nat.add(base, FT.FT.pow2(p)), FT.FT.pow2(p)),
                hge), hx),
            CW.store_after(p, Nat.add(base, FT.FT.pow2(p)), y, xs, w, v,
              hge, hy)}

# Rewriting the ghost list of a model whose cells did not change: the same
# array models two propositionally equal ghost lists.
def CW.store_ghost(+d: Nat, +base: Nat, a: Array<U32>, +xs1: +List<U32>,
    +xs2: +List<U32>, +e: {xs1 == xs2 : +List<U32>},
    +hs: CMem.CM.Store(d, base, a, xs1)) -> CMem.CM.Store(d, base, a, xs2):
  %e : CMem.CM.Store(d, base, a, _)
  hs

# Building the node case.  The recursive call's result arrives as a pair-valued
# parameter, which is matched here so `fst(swap.lo ...)` reduces to an `ANode`
# and `Store` unfolds to the `DPair` of the two child models.  Same shape as
# `FT.tbl_swap_lo` in `fast_tbl.bend`.
def CW.store_swap_lo(+p: Nat, +base: Nat, -ys: Array<U32>, r: Array<U32> & U32,
    +xs: +List<U32>, +i: U32, +v: U32,
    +hr: CMem.CM.Store(p, base, Arr.Arr.fst(Array<U32>, U32, r),
           CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v)),
    +hy: CMem.CM.Store(p, Nat.add(base, FT.FT.pow2(p)), ys,
           CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v))) ->
  CMem.CM.Store(1n+p, base,
    Arr.Arr.fst(Array<U32>, U32, Array.swap.lo(U32, ys, r)),
    CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v)):
  (a2, res) = r
  Arr.DPair{hr, hy}

def CW.store_swap_hi(+p: Nat, +base: Nat, -xs: Array<U32>, r: Array<U32> & U32,
    +ys: +List<U32>, +i: U32, +v: U32,
    +hx: CMem.CM.Store(p, base, xs,
           CS.CS.set(ys, Nat.add(base, U32.to_nat(i)), v)),
    +hr: CMem.CM.Store(p, Nat.add(base, FT.FT.pow2(p)),
           Arr.Arr.fst(Array<U32>, U32, r),
           CS.CS.set(ys, Nat.add(base, U32.to_nat(i)), v))) ->
  CMem.CM.Store(1n+p, base,
    Arr.Arr.fst(Array<U32>, U32, Array.swap.hi(U32, xs, r)),
    CS.CS.set(ys, Nat.add(base, U32.to_nat(i)), v)):
  (a2, res) = r
  Arr.DPair{hx, hr}
