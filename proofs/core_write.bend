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
import ./core_cells.bend as OldCells

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
def CW.store_ghost(+d: Nat, +base: Nat, -a: Array<U32>, +xs1: +List<U32>,
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

# The node case of the write lemma.  The goal's arrays are `-`-erased and only
# appear in types; the live work runs on `Arr.dup` copies, whose results are
# transported back along the copy equalities.  This is the same shape as
# `FT.tbl_tree_swap_go_lo` in `fast_tbl.bend`.
def CW.store_swap_lo_core(+p: Nat, +base: Nat, -x: Array<U32>, -y: Array<U32>,
    +xs: +List<U32>, +n: U32, +i: U32, +v: U32,
    +hx: CMem.CM.Store(p, base, x, xs),
    +hy: CMem.CM.Store(p, Nat.add(base, FT.FT.pow2(p)), y, xs),
    +hw: {Nat.is_lt(Nat.add(base, U32.to_nat(i)),
            Nat.add(base, FT.FT.pow2(p))) == True{} : Bool},
    dx: &x1: Array<U32> -> &x2: Array<U32> ->
        {x1 == x : Array<U32>} & {x2 == x1 : Array<U32>},
    dy: &y1: Array<U32> -> &y2: Array<U32> ->
        {y1 == y : Array<U32>} & {y2 == y1 : Array<U32>},
    ih: @x3: Array<U32> -> CMem.CM.Store(p, base, x3, xs) ->
        CMem.CM.Store(p, base,
          Arr.Arr.fst(Array<U32>, U32,
            Array.swap.go(U32, x3, U32.shr(n), i, v,
              U32.is_lt(i, U32.shr(U32.shr(n))))),
          CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v))) ->
  CMem.CM.Store(1n+p, base,
    Arr.Arr.fst(Array<U32>, U32,
      Array.swap.lo(U32, y,
        Array.swap.go(U32, x, U32.shr(n), i, v,
          U32.is_lt(i, U32.shr(U32.shr(n)))))),
    CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v)):
  (x1, d2) = dx
  (x2, pe) = d2
  (+ex1, +ex2) = pe
  (y1, e2) = dy
  (y2, qe) = e2
  (+ey1, +ey2) = qe
  +ex2x : {x2 == x : Array<U32>} =
    Equal.trans(Array<U32>, x2, x1, x, ex2, ex1)
  +hx2 = CMem.CM.store_transport(p, base, x, x2, xs,
            Equal.sym(Array<U32>, x2, x, ex2x), hx)
  +hr2 = ih(x2, hx2)
  +hy1 = CMem.CM.store_transport(p, Nat.add(base, FT.FT.pow2(p)), y, y1, xs,
            Equal.sym(Array<U32>, y1, y, ey1), hy)
  +hpr1 = CW.store_before(p, Nat.add(base, FT.FT.pow2(p)), y1, xs,
             Nat.add(base, U32.to_nat(i)), v, hw, hy1)
  +earr : {Arr.Arr.fst(Array<U32>, U32,
             Array.swap.go(U32, x2, U32.shr(n), i, v,
               U32.is_lt(i, U32.shr(U32.shr(n)))))
           == Arr.Arr.fst(Array<U32>, U32,
                Array.swap.go(U32, x1, U32.shr(n), i, v,
                  U32.is_lt(i, U32.shr(U32.shr(n))))) : Array<U32>} =
    Equal.cong(Array<U32> & U32, Array<U32>,
      q => Arr.Arr.fst(Array<U32>, U32, q),
      Array.swap.go(U32, x2, U32.shr(n), i, v,
        U32.is_lt(i, U32.shr(U32.shr(n)))),
      Array.swap.go(U32, x1, U32.shr(n), i, v,
        U32.is_lt(i, U32.shr(U32.shr(n)))),
      Equal.cong(Array<U32>, Array<U32> & U32,
        z => Array.swap.go(U32, z, U32.shr(n), i, v,
               U32.is_lt(i, U32.shr(U32.shr(n)))),
        x2, x1, ex2))
  +hr1 = CMem.CM.store_transport(p, base,
             Arr.Arr.fst(Array<U32>, U32,
               Array.swap.go(U32, x2, U32.shr(n), i, v,
                 U32.is_lt(i, U32.shr(U32.shr(n))))),
             Arr.Arr.fst(Array<U32>, U32,
               Array.swap.go(U32, x1, U32.shr(n), i, v,
                 U32.is_lt(i, U32.shr(U32.shr(n))))),
             CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v), earr, hr2)
  +hp1 = CW.store_swap_lo(p, base, y1,
             Array.swap.go(U32, x1, U32.shr(n), i, v,
               U32.is_lt(i, U32.shr(U32.shr(n)))),
             xs, i, v, hr1, hpr1)
  +ey = Equal.cong(Array<U32>, Array<U32>,
      q => Arr.Arr.fst(Array<U32>, U32,
             Array.swap.lo(U32, q,
               Array.swap.go(U32, x1, U32.shr(n), i, v,
                 U32.is_lt(i, U32.shr(U32.shr(n)))))),
      y1, y, ey1)
  +ex = Equal.cong(Array<U32> & U32, Array<U32>,
      p2 => Arr.Arr.fst(Array<U32>, U32, Array.swap.lo(U32, y, p2)),
      Array.swap.go(U32, x1, U32.shr(n), i, v,
        U32.is_lt(i, U32.shr(U32.shr(n)))),
      Array.swap.go(U32, x, U32.shr(n), i, v,
        U32.is_lt(i, U32.shr(U32.shr(n)))),
      Equal.cong(Array<U32>, Array<U32> & U32,
        z => Array.swap.go(U32, z, U32.shr(n), i, v,
               U32.is_lt(i, U32.shr(U32.shr(n)))),
        x1, x, ex1))
  CMem.CM.store_transport(1n+p, base,
    Arr.Arr.fst(Array<U32>, U32,
      Array.swap.lo(U32, y1,
        Array.swap.go(U32, x1, U32.shr(n), i, v,
          U32.is_lt(i, U32.shr(U32.shr(n)))))),
    Arr.Arr.fst(Array<U32>, U32,
      Array.swap.lo(U32, y,
        Array.swap.go(U32, x, U32.shr(n), i, v,
          U32.is_lt(i, U32.shr(U32.shr(n)))))),
    CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v),
    Equal.trans(Array<U32>,
      Arr.Arr.fst(Array<U32>, U32,
        Array.swap.lo(U32, y1,
          Array.swap.go(U32, x1, U32.shr(n), i, v,
            U32.is_lt(i, U32.shr(U32.shr(n)))))),
      Arr.Arr.fst(Array<U32>, U32,
        Array.swap.lo(U32, y,
          Array.swap.go(U32, x1, U32.shr(n), i, v,
            U32.is_lt(i, U32.shr(U32.shr(n)))))),
      Arr.Arr.fst(Array<U32>, U32,
        Array.swap.lo(U32, y,
          Array.swap.go(U32, x, U32.shr(n), i, v,
            U32.is_lt(i, U32.shr(U32.shr(n)))))),
      ey, ex),
    hp1)

# The other node case (write into the right child).  Same copy/transport
# pattern; the ghost list is rewritten from the right child's cell index to the
# parent's cell index with `eidx`.
def CW.store_swap_hi_core(+p: Nat, +base: Nat, -x: Array<U32>, -y: Array<U32>,
    +xs: +List<U32>, +n: U32, +i: U32, +ip: U32, +v: U32,
    +hx: CMem.CM.Store(p, base, x, xs),
    +hy: CMem.CM.Store(p, Nat.add(base, FT.FT.pow2(p)), y, xs),
    +hw: {Nat.is_le(Nat.add(base, FT.FT.pow2(p)),
            Nat.add(base, U32.to_nat(i))) == True{} : Bool},
    +eidx: {Nat.add(Nat.add(base, FT.FT.pow2(p)), U32.to_nat(ip))
            == Nat.add(base, U32.to_nat(i)) : Nat},
    dx: &x1: Array<U32> -> &x2: Array<U32> ->
        {x1 == x : Array<U32>} & {x2 == x1 : Array<U32>},
    dy: &y1: Array<U32> -> &y2: Array<U32> ->
        {y1 == y : Array<U32>} & {y2 == y1 : Array<U32>},
    ih: @y3: Array<U32> -> CMem.CM.Store(p, Nat.add(base, FT.FT.pow2(p)),
          y3, xs) ->
        CMem.CM.Store(p, Nat.add(base, FT.FT.pow2(p)),
          Arr.Arr.fst(Array<U32>, U32,
            Array.swap.go(U32, y3, U32.shr(n), ip, v,
              U32.is_lt(ip, U32.shr(U32.shr(n))))),
          CS.CS.set(xs, Nat.add(Nat.add(base, FT.FT.pow2(p)),
            U32.to_nat(ip)), v))) ->
  CMem.CM.Store(1n+p, base,
    Arr.Arr.fst(Array<U32>, U32,
      Array.swap.hi(U32, x,
        Array.swap.go(U32, y, U32.shr(n), ip, v,
          U32.is_lt(ip, U32.shr(U32.shr(n)))))),
    CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v)):
  (x1, d2) = dx
  (x2, pe) = d2
  (+ex1, +ex2) = pe
  (y1, e2) = dy
  (y2, qe) = e2
  (+ey1, +ey2) = qe
  +ey2y : {y2 == y : Array<U32>} =
    Equal.trans(Array<U32>, y2, y1, y, ey2, ey1)
  +hy2 = CMem.CM.store_transport(p, Nat.add(base, FT.FT.pow2(p)), y, y2, xs,
            Equal.sym(Array<U32>, y2, y, ey2y), hy)
  +hr2 = ih(y2, hy2)
  +hx1 = CMem.CM.store_transport(p, base, x, x1, xs,
            Equal.sym(Array<U32>, x1, x, ex1), hx)
  +hpl1 = CW.store_after(p, base, x1, xs, Nat.add(base, U32.to_nat(i)), v,
             hw, hx1)
  +earr = Equal.cong(Array<U32> & U32, Array<U32>,
      q => Arr.Arr.fst(Array<U32>, U32, q),
      Array.swap.go(U32, y2, U32.shr(n), ip, v, U32.is_lt(ip, U32.shr(U32.shr(n)))),
      Array.swap.go(U32, y1, U32.shr(n), ip, v, U32.is_lt(ip, U32.shr(U32.shr(n)))),
      Equal.cong(Array<U32>, Array<U32> & U32,
        z => Array.swap.go(U32, z, U32.shr(n), ip, v,
               U32.is_lt(ip, U32.shr(U32.shr(n)))),
        y2, y1, ey2))
  +hr1 = CMem.CM.store_transport(p, Nat.add(base, FT.FT.pow2(p)),
             Arr.Arr.fst(Array<U32>, U32,
               Array.swap.go(U32, y2, U32.shr(n), ip, v,
                 U32.is_lt(ip, U32.shr(U32.shr(n))))),
             Arr.Arr.fst(Array<U32>, U32,
               Array.swap.go(U32, y1, U32.shr(n), ip, v,
                 U32.is_lt(ip, U32.shr(U32.shr(n))))),
             CS.CS.set(xs, Nat.add(Nat.add(base, FT.FT.pow2(p)),
               U32.to_nat(ip)), v), earr, hr2)
  +eg = Equal.cong(Nat, +List<U32>, z => CS.CS.set(xs, z, v),
      Nat.add(Nat.add(base, FT.FT.pow2(p)), U32.to_nat(ip)),
      Nat.add(base, U32.to_nat(i)), eidx)
  +hr = CW.store_ghost(p, Nat.add(base, FT.FT.pow2(p)),
           Arr.Arr.fst(Array<U32>, U32,
             Array.swap.go(U32, y1, U32.shr(n), ip, v,
               U32.is_lt(ip, U32.shr(U32.shr(n))))),
           CS.CS.set(xs, Nat.add(Nat.add(base, FT.FT.pow2(p)),
             U32.to_nat(ip)), v),
           CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v), eg, hr1)
  +hp1 = CW.store_swap_hi(p, base, x1,
             Array.swap.go(U32, y1, U32.shr(n), ip, v,
               U32.is_lt(ip, U32.shr(U32.shr(n)))),
             xs, i, v, hpl1, hr)
  +ey = Equal.cong(Array<U32>, Array<U32>,
      q => Arr.Arr.fst(Array<U32>, U32,
             Array.swap.hi(U32, x1,
               Array.swap.go(U32, q, U32.shr(n), ip, v,
                 U32.is_lt(ip, U32.shr(U32.shr(n)))))),
      y1, y, ey1)
  +ex = Equal.cong(Array<U32>, Array<U32>,
      q => Arr.Arr.fst(Array<U32>, U32,
             Array.swap.hi(U32, q,
               Array.swap.go(U32, y, U32.shr(n), ip, v,
                 U32.is_lt(ip, U32.shr(U32.shr(n)))))),
      x1, x, ex1)
  CMem.CM.store_transport(1n+p, base,
    Arr.Arr.fst(Array<U32>, U32,
      Array.swap.hi(U32, x1,
        Array.swap.go(U32, y1, U32.shr(n), ip, v,
          U32.is_lt(ip, U32.shr(U32.shr(n)))))),
    Arr.Arr.fst(Array<U32>, U32,
      Array.swap.hi(U32, x,
        Array.swap.go(U32, y, U32.shr(n), ip, v,
          U32.is_lt(ip, U32.shr(U32.shr(n)))))),
    CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v),
    Equal.trans(Array<U32>,
      Arr.Arr.fst(Array<U32>, U32,
        Array.swap.hi(U32, x1,
          Array.swap.go(U32, y1, U32.shr(n), ip, v,
            U32.is_lt(ip, U32.shr(U32.shr(n)))))),
      Arr.Arr.fst(Array<U32>, U32,
        Array.swap.hi(U32, x1,
          Array.swap.go(U32, y, U32.shr(n), ip, v,
            U32.is_lt(ip, U32.shr(U32.shr(n)))))),
      Arr.Arr.fst(Array<U32>, U32,
        Array.swap.hi(U32, x,
          Array.swap.go(U32, y, U32.shr(n), ip, v,
            U32.is_lt(ip, U32.shr(U32.shr(n)))))),
      ey, ex),
    hp1)

# The recursive write: writing `v` at cell `base + to_nat(i)` of a subtree of
# depth `d` updates the ghost list at that cell.  Mirrors `Array.swap.go`; `n`
# is the runtime block size the caller passes down (`2^d` at the top, `shr` of
# the parent's size below), and `en` records `n == 2^d`.
def CW.store_swap_go(+d: Nat, +base: Nat, a: Array<U32>, +xs: +List<U32>,
    +n: U32, +i: U32, +v: U32, z: Bool,
    +en: {n == Arr.Arr.pow2_u32(d) : U32},
    +ez: {z == U32.is_lt(i, U32.shr(n)) : Bool},
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.Arr.u32_zero_from(d, i) == True{} : Bool},
    +hs: CMem.CM.Store(d, base, a, xs),
    +hlen: {Nat.is_le(Nat.add(base, FT.FT.pow2(d)), CS.CS.len(xs))
            == True{} : Bool}) ->
  CMem.CM.Store(d, base,
    Arr.Arr.fst(Array<U32>, U32, Array.swap.go(U32, a, n, i, v, z)),
    CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v)):
  match d:
    case 0n:
      match a:
        case ALeaf{x}:
          +ei0 : {i == 0 : U32} = Arr.Arr.u32_eq_zero(i, zi)
          +etn : {U32.to_nat(i) == 0n : Nat} =
            Equal.cong(U32, Nat, U32.to_nat, i, 0, ei0)
          +eidx : {Nat.add(base, U32.to_nat(i)) == base : Nat} =
            Equal.trans(Nat, Nat.add(base, U32.to_nat(i)), Nat.add(base, 0n),
              base,
              Equal.cong(Nat, Nat, z2 => Nat.add(base, z2), U32.to_nat(i), 0n,
                etn),
              NatProof.NatPrf.add_zero(base))
          +hs1 : {Nat.is_le(1n+base, CS.CS.len(xs)) == True{} : Bool} =
            Equal.trans(Bool, Nat.is_le(1n+base, CS.CS.len(xs)),
              Nat.is_le(Nat.add(base, 1n), CS.CS.len(xs)), True{},
              Equal.cong(Nat, Bool, z2 => Nat.is_le(z2, CS.CS.len(xs)),
                1n+base, Nat.add(base, 1n),
                Equal.sym(Nat, Nat.add(base, 1n), 1n+base,
                  NatProof.NatPrf.add_comm(base, 1n))),
              hlen)
          +hblt : {Nat.is_lt(base, CS.CS.len(xs)) == True{} : Bool} =
            CN.core_nat_lt_of_le_succ(base, CS.CS.len(xs), hs1)
          +hset : {CS.CS.nth(CS.CS.set(xs, base, v), base) == v : U32} =
            CS.CS.nth_set_same(xs, base, v, hblt)
          +eset : {CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v)
                   == CS.CS.set(xs, base, v) : +List<U32>} =
            Equal.cong(Nat, +List<U32>, z2 => CS.CS.set(xs, z2, v),
              Nat.add(base, U32.to_nat(i)), base, eidx)
          +hset2 : {CS.CS.nth(CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v),
                     base) == v : U32} =
            Equal.trans(U32,
              CS.CS.nth(CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v), base),
              CS.CS.nth(CS.CS.set(xs, base, v), base),
              v,
              Equal.cong(+List<U32>, U32, l => CS.CS.nth(l, base),
                CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v),
                CS.CS.set(xs, base, v), eset),
              hset)
          Equal.sym(U32, CS.CS.nth(CS.CS.set(xs, Nat.add(base, U32.to_nat(i)),
            v), base), v, hset2)
        case ANode{x2, y2}:
          Empty.absurd(
            CMem.CM.Store(0n, base,
              Arr.Arr.fst(Array<U32>, U32,
                Array.swap.go(U32, ANode{x2, y2}, n, i, v, z)),
              CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v)), hs)
    case 1n++p:
      match a:
        case ALeaf{x}:
          Empty.absurd(
            CMem.CM.Store(1n+p, base,
              Arr.Arr.fst(Array<U32>, U32,
                Array.swap.go(U32, ALeaf{x}, n, i, v, z)),
              CS.CS.set(xs, Nat.add(base, U32.to_nat(i)), v)), hs)
        case ANode{x, y}:
          match z:
            case True{}:
              Arr.DPair{+hx, +hy} = hs
              +plt : {Nat.is_lt(p, 32n) == True{} : Bool} =
                NatProof.Nat.is_le_lt_trans(p, 1n+p, 32n,
                  NatProof.Nat.is_le_of_lt(p, 1n+p,
                    NatProof.Nat.is_lt_succ_self(p)), hlt)
              +eshr : {U32.shr(n) == Arr.Arr.pow2_u32(p) : U32} =
                Equal.trans(U32, U32.shr(n),
                  U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p),
                  Equal.cong(U32, U32, z2 => U32.shr(z2), n,
                    Arr.Arr.pow2_u32(1n+p), en),
                  Arr.Arr.u32_shr_pow2(p, hlt))
              +ilt : {U32.is_lt(i, Arr.Arr.pow2_u32(p)) == True{} : Bool} =
                Equal.trans(Bool, U32.is_lt(i, Arr.Arr.pow2_u32(p)),
                  U32.is_lt(i, U32.shr(n)), True{},
                  Equal.cong(U32, Bool, z2 => U32.is_lt(i, z2),
                    Arr.Arr.pow2_u32(p), U32.shr(n),
                    Equal.sym(U32, U32.shr(n), Arr.Arr.pow2_u32(p), eshr)),
                  Equal.sym(Bool, True{}, U32.is_lt(i, U32.shr(n)), ez))
              +zip : {Arr.Arr.u32_zero_from(p, i) == True{} : Bool} =
                Arr.Arr.u32_zero_from_lt(p, i, zi, plt, ilt)
              +hinat : {Nat.is_lt(U32.to_nat(i), FT.FT.pow2(p))
                        == True{} : Bool} =
                FT.FT.u32_to_nat_zero_from(p, i, zip)
              +hw : {Nat.is_lt(Nat.add(base, U32.to_nat(i)),
                       Nat.add(base, FT.FT.pow2(p))) == True{} : Bool} =
                FT.FT.nat_lt_add_l(U32.to_nat(i), FT.FT.pow2(p), base, hinat)
              CW.store_swap_lo_core(p, base, x, y, xs, n, i, v, hx, hy, hw,
                Arr.Arr.dup(U32, x), Arr.Arr.dup(U32, y),
                x3 => hx3 =>
                  CW.store_swap_go(p, base, x3, xs, U32.shr(n), i, v,
                    U32.is_lt(i, U32.shr(U32.shr(n))), eshr, {==}, plt,
                    zip, hx3, CW.sub_node_l(p, base, xs, hlen)))
            case False{}:
              Arr.DPair{+hx, +hy} = hs
              +plt : {Nat.is_lt(p, 32n) == True{} : Bool} =
                NatProof.Nat.is_le_lt_trans(p, 1n+p, 32n,
                  NatProof.Nat.is_le_of_lt(p, 1n+p,
                    NatProof.Nat.is_lt_succ_self(p)), hlt)
              +eshr : {U32.shr(n) == Arr.Arr.pow2_u32(p) : U32} =
                Equal.trans(U32, U32.shr(n),
                  U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p),
                  Equal.cong(U32, U32, z2 => U32.shr(z2), n,
                    Arr.Arr.pow2_u32(1n+p), en),
                  Arr.Arr.u32_shr_pow2(p, hlt))
              +ige : {U32.is_lt(i, Arr.Arr.pow2_u32(p)) == False{} : Bool} =
                Equal.trans(Bool, U32.is_lt(i, Arr.Arr.pow2_u32(p)),
                  U32.is_lt(i, U32.shr(n)), False{},
                  Equal.cong(U32, Bool, z2 => U32.is_lt(i, z2),
                    Arr.Arr.pow2_u32(p), U32.shr(n),
                    Equal.sym(U32, U32.shr(n), Arr.Arr.pow2_u32(p), eshr)),
                  Equal.sym(Bool, False{}, U32.is_lt(i, U32.shr(n)), ez))
              +ip = U32.sub(i, U32.shr(n))
              +zip : {Arr.Arr.u32_zero_from(p, ip) == True{} : Bool} =
                Equal.trans(Bool, Arr.Arr.u32_zero_from(p, ip),
                  Arr.Arr.u32_zero_from(p, U32.sub(i, Arr.Arr.pow2_u32(p))),
                  True{},
                  Equal.cong(U32, Bool, z2 => Arr.Arr.u32_zero_from(p, z2),
                    U32.sub(i, U32.shr(n)),
                    U32.sub(i, Arr.Arr.pow2_u32(p)),
                    Equal.cong(U32, U32, z2 => U32.sub(i, z2),
                      U32.shr(n), Arr.Arr.pow2_u32(p), eshr)),
                  Arr.Arr.u32_zero_from_ge(p, i, zi, plt, ige))
              +eip : {U32.sub(i, Arr.Arr.pow2_u32(p)) == ip : U32} =
                Equal.cong(U32, U32, z2 => U32.sub(i, z2),
                  Arr.Arr.pow2_u32(p), U32.shr(n),
                  Equal.sym(U32, U32.shr(n), Arr.Arr.pow2_u32(p), eshr))
              +esub0 : {Nat.add(FT.FT.pow2(p),
                          U32.to_nat(U32.sub(i, Arr.Arr.pow2_u32(p))))
                        == U32.to_nat(i) : Nat} =
                FT.FT.u32_to_nat_sub_pow2(p, i, zi, plt, ige)
              +esub : {Nat.add(FT.FT.pow2(p), U32.to_nat(ip)) == U32.to_nat(i)
                       : Nat} =
                Equal.trans(Nat,
                  Nat.add(FT.FT.pow2(p), U32.to_nat(ip)),
                  Nat.add(FT.FT.pow2(p),
                    U32.to_nat(U32.sub(i, Arr.Arr.pow2_u32(p)))),
                  U32.to_nat(i),
                  Equal.cong(U32, Nat,
                    z2 => Nat.add(FT.FT.pow2(p), U32.to_nat(z2)),
                    ip, U32.sub(i, Arr.Arr.pow2_u32(p)),
                    Equal.sym(U32, U32.sub(i, Arr.Arr.pow2_u32(p)), ip, eip)),
                  esub0)
              +eidx : {Nat.add(Nat.add(base, FT.FT.pow2(p)), U32.to_nat(ip))
                       == Nat.add(base, U32.to_nat(i)) : Nat} =
                Equal.trans(Nat,
                  Nat.add(Nat.add(base, FT.FT.pow2(p)), U32.to_nat(ip)),
                  Nat.add(base, Nat.add(FT.FT.pow2(p), U32.to_nat(ip))),
                  Nat.add(base, U32.to_nat(i)),
                  NatProof.NatPrf.add_assoc(base, FT.FT.pow2(p),
                    U32.to_nat(ip)),
                  Equal.cong(Nat, Nat, z2 => Nat.add(base, z2),
                    Nat.add(FT.FT.pow2(p), U32.to_nat(ip)), U32.to_nat(i),
                    esub))
              +hle : {Nat.is_le(FT.FT.pow2(p), U32.to_nat(i)) == True{}
                      : Bool} =
                Equal.trans(Bool,
                  Nat.is_le(FT.FT.pow2(p), U32.to_nat(i)),
                  Nat.is_le(FT.FT.pow2(p), Nat.add(FT.FT.pow2(p),
                    U32.to_nat(ip))),
                  True{},
                  Equal.sym(Bool,
                    Nat.is_le(FT.FT.pow2(p), Nat.add(FT.FT.pow2(p),
                      U32.to_nat(ip))),
                    Nat.is_le(FT.FT.pow2(p), U32.to_nat(i)),
                    Equal.cong(Nat, Bool,
                      z2 => Nat.is_le(FT.FT.pow2(p), z2),
                      Nat.add(FT.FT.pow2(p), U32.to_nat(ip)), U32.to_nat(i),
                      esub)),
                  CW.le_add_r(FT.FT.pow2(p), U32.to_nat(ip)))
              +hw : {Nat.is_le(Nat.add(base, FT.FT.pow2(p)),
                       Nat.add(base, U32.to_nat(i))) == True{} : Bool} =
                NatProof.Nat.is_le_add_l(FT.FT.pow2(p), U32.to_nat(i), base,
                  hle)
              CW.store_swap_hi_core(p, base, x, y, xs, n, i, ip, v, hx, hy,
                hw, eidx, Arr.Arr.dup(U32, x), Arr.Arr.dup(U32, y),
                y3 => hy3 =>
                  CW.store_swap_go(p, Nat.add(base, FT.FT.pow2(p)), y3, xs,
                    U32.shr(n), ip, v,
                    U32.is_lt(ip, U32.shr(U32.shr(n))), eshr, {==}, plt,
                    zip, hy3, CW.sub_node_r(p, base, xs, hlen)))

# The machine's write: `Array.set(a, from_nat(k), v)` updates the ghost cell
# `k`.  The chain is the one `CM.store_read` uses: `Array.set` is `fst(swap)`,
# `swap` masks against the depth, and `store_swap_go` is the structural write.
def CW.store_set_body(+d: Nat, -a: Array<U32>, +xs: +List<U32>, +k: Nat,
    +v: U32, a1: Array<U32>, b1: Array<U32>, c1: Array<U32>,
    c2: Array<U32>,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hk: {Nat.is_lt(k, FT.FT.pow2(d)) == True{} : Bool},
    +hs: CMem.CM.Store(d, 0n, a, xs),
    +hlen: {Nat.is_le(Nat.add(0n, FT.FT.pow2(d)), CS.CS.len(xs))
            == True{} : Bool},
    p1: {a1 == a : Array<U32>} & {b1 == a1 : Array<U32>},
    p2: {c1 == b1 : Array<U32>} & {c2 == c1 : Array<U32>}) ->
  CMem.CM.Store(d, 0n, Array.set(U32, a, U32.from_nat(k), v),
    CS.CS.set(xs, k, v)):
  (+e1, +e2) = p1
  (+e3, +e4) = p2
  +ec2_a1 : {c2 == a1 : Array<U32>} =
    Equal.trans(Array<U32>, c2, c1, a1,
      e4, Equal.trans(Array<U32>, c1, b1, a1, e3, e2))
  +idx = U32.from_nat(k)
  +zi : {Arr.Arr.u32_zero_from(d, idx) == True{} : Bool} =
    FT.FT.u32_zero_from_from_nat(d, k, hd, hk)
  +em : {U32.and(idx, U32.sub(Arr.Arr.pow2_u32(d), 1)) == idx : U32} =
    Arr.Arr.u32_and_mask(d, idx, zi)
  +etn : {U32.to_nat(idx) == k : Nat} =
    FT.FT.u32_to_nat_from_nat(d, k, hd, hk)
  +hs_b1 = CMem.CM.store_transport(d, 0n, a, b1, xs,
             Equal.sym(Array<U32>, b1, a,
               Equal.trans(Array<U32>, b1, a1, a, e2, e1)), hs)
  +hd_b1 = CMem.CM.store_depth(d, 0n, b1, xs, hs_b1)
  +hd_c2 = Arr.Arr.depth_transport(U32, d, b1, c2,
             Equal.sym(Array<U32>, c2, b1,
               Equal.trans(Array<U32>, c2, c1, b1, e4, e3)), hd_b1)
  +eset_c2 : {Array.set(U32, c2, idx, v)
              == Arr.Arr.fst(Array<U32>, U32, Array.swap(U32, c2, idx, v))
              : Array<U32>} =
    Equal.trans(Array<U32>,
      Array.set(U32, c2, idx, v),
      Array.set(U32, c1, idx, v),
      Arr.Arr.fst(Array<U32>, U32, Array.swap(U32, c2, idx, v)),
      Equal.cong(Array<U32>, Array<U32>, x => Array.set(U32, x, idx, v),
        c2, c1, e4),
      Equal.trans(Array<U32>,
        Array.set(U32, c1, idx, v),
        Arr.Arr.fst(Array<U32>, U32, Array.swap(U32, c1, idx, v)),
        Arr.Arr.fst(Array<U32>, U32, Array.swap(U32, c2, idx, v)),
        Arr.Arr.set_eq(U32, c1, idx, v),
        Equal.cong(Array<U32>, Array<U32>,
          x => Arr.Arr.fst(Array<U32>, U32, Array.swap(U32, x, idx, v)),
          c1, c2, Equal.sym(Array<U32>, c2, c1, e4))))
  +esw : {Array.set(U32, c2, idx, v)
          == Arr.Arr.fst(Array<U32>, U32,
               Array.swap.go(U32, c2, Arr.Arr.pow2_u32(d), idx, v,
                 U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d)))))
          : Array<U32>} =
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
        Arr.Arr.swap_depth(U32, d, c2, idx, v, hd_c2),
        Equal.cong(U32, Array<U32>,
          j => Arr.Arr.fst(Array<U32>, U32,
                 Array.swap.go(U32, c2, Arr.Arr.pow2_u32(d), j, v,
                   U32.is_lt(j, U32.shr(Arr.Arr.pow2_u32(d))))),
          U32.and(idx, U32.sub(Arr.Arr.pow2_u32(d), 1)), idx, em)))
  +hs_a1 = CMem.CM.store_transport(d, 0n, a, a1, xs,
             Equal.sym(Array<U32>, a1, a, e1), hs)
  +hgo = CW.store_swap_go(d, 0n, a1, xs, Arr.Arr.pow2_u32(d), idx, v,
            U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))), {==}, {==}, hd,
            zi, hs_a1, hlen)
  +eg : {CS.CS.set(xs, Nat.add(0n, U32.to_nat(idx)), v)
         == CS.CS.set(xs, k, v) : +List<U32>} =
    Equal.cong(Nat, +List<U32>, z => CS.CS.set(xs, z, v),
      Nat.add(0n, U32.to_nat(idx)), k, etn)
  +hgo2 = CW.store_ghost(d, 0n,
             Arr.Arr.fst(Array<U32>, U32,
               Array.swap.go(U32, a1, Arr.Arr.pow2_u32(d), idx, v,
                 U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))),
             CS.CS.set(xs, Nat.add(0n, U32.to_nat(idx)), v),
             CS.CS.set(xs, k, v), eg, hgo)
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
  %e1 : CMem.CM.Store(d, 0n, Array.set(U32, _, idx, v), CS.CS.set(xs, k, v))
  %ec2_a1 : CMem.CM.Store(d, 0n, Array.set(U32, _, idx, v),
              CS.CS.set(xs, k, v))
  CMem.CM.store_transport(d, 0n,
    Arr.Arr.fst(Array<U32>, U32,
      Array.swap.go(U32, a1, Arr.Arr.pow2_u32(d), idx, v,
        U32.is_lt(idx, U32.shr(Arr.Arr.pow2_u32(d))))),
    Array.set(U32, c2, idx, v), CS.CS.set(xs, k, v), eq_a, hgo2)

def CW.store_set_dp(+d: Nat, -a: Array<U32>, +xs: +List<U32>, +k: Nat,
    +v: U32,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hk: {Nat.is_lt(k, FT.FT.pow2(d)) == True{} : Bool},
    +hs: CMem.CM.Store(d, 0n, a, xs),
    +hlen: {Nat.is_le(Nat.add(0n, FT.FT.pow2(d)), CS.CS.len(xs))
            == True{} : Bool},
    dp: &a1: Array<U32> -> &a2: Array<U32> -> &a3: Array<U32> ->
        &a4: Array<U32> ->
        ({a1 == a : Array<U32>} & {a2 == a1 : Array<U32>})
        & ({a3 == a2 : Array<U32>} & {a4 == a3 : Array<U32>})) ->
  CMem.CM.Store(d, 0n, Array.set(U32, a, U32.from_nat(k), v),
    CS.CS.set(xs, k, v)):
  (a1, r1) = dp
  (b1, r2) = r1
  (c1, r3) = r2
  (c2, px) = r3
  (p1, p2) = px
  CW.store_set_body(d, a, xs, k, v, a1, b1, c1, c2, hd, hk, hs, hlen, p1, p2)

def CW.store_set(+d: Nat, a: Array<U32>, +xs: +List<U32>, +k: Nat, +v: U32,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hk: {Nat.is_lt(k, FT.FT.pow2(d)) == True{} : Bool},
    +hs: CMem.CM.Store(d, 0n, a, xs),
    +hlen: {Nat.is_le(Nat.add(0n, FT.FT.pow2(d)), CS.CS.len(xs))
            == True{} : Bool}) ->
  CMem.CM.Store(d, 0n, Array.set(U32, a, U32.from_nat(k), v),
    CS.CS.set(xs, k, v)):
  CW.store_set_dp(d, a, xs, k, v, hd, hk, hs, hlen,
    OldCells.CC.dup4(U32, a))
