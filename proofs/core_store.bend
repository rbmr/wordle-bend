# The array-cell model for the flat-array core.
#
# `CM.Store(d, base, a, xs)` says the `2^d` cells of `a` are, in order from
# `base`, exactly the ghost list `xs`:
#
#   for every leaf at global index `base + j`, the cell's value is `nth(xs, base + j)`.
#
# The tree shape is what makes the model usable: matching a node exposes the two
# sub-arrays and their depths, so a read or a write descends structurally and
# needs one lemma per level instead of one per cell.  A dense per-cell predicate
# over a flat `Array` cannot do that, because `Arr.get_set_diff` needs the old
# array and its depth in every linear position.
#
# `xs` is global: the leaf index is never rebased, which keeps the "cells from
# `k` on are unchanged" fact expressible as an equality of ghost-list tails
# (`CS.drop`), instead of a range predicate that would need one step per cell.
import Base
import ./array.bend as Arr
import ./nat.bend as NatProof
import ./fast_tbl.bend as FT
import ./core_list.bend as CS
import ./core_nat.bend as CN

def CM.Store(+d: Nat, +base: Nat, a: Array<U32>, +xs: +List<U32>) -> Data:
  match d:
    case 0n:
      match a:
        case ALeaf{v}:
          {v == CS.CS.nth(xs, base) : U32}
        case ANode{x, y}:
          Empty
    case 1n+p:
      match a:
        case ALeaf{v}:
          Empty
        case ANode{x, y}:
          Arr.Arr.DPair<
            CM.Store(p, base, x, xs),
            CM.Store(p, Nat.add(base, FT.FT.pow2(p)), y, xs)>

def CM.store_transport(+d: Nat, +base: Nat, -a1: Array<U32>, -a2: Array<U32>,
    +xs: +List<U32>, +ea: {a1 == a2 : Array<U32>},
    +hs: CM.Store(d, base, a1, xs)) -> CM.Store(d, base, a2, xs):
  %ea : CM.Store(d, base, _, xs)
  hs

def CM.store_depth(+d: Nat, +base: Nat, a: Array<U32>, +xs: +List<U32>,
    +hs: CM.Store(d, base, a, xs)) -> Arr.Arr.Depth(U32, d, a):
  match d:
    case 0n:
      match a:
        case ALeaf{v}:
          Unit{}
        case ANode{x, y}:
          hs
    case 1n+p:
      match a:
        case ALeaf{v}:
          hs
        case ANode{x, y}:
          +hxs = Arr.Arr.dpair_l(CM.Store(p, base, x, xs),
                   CM.Store(p, Nat.add(base, FT.FT.pow2(p)), y, xs), hs)
          +hys = Arr.Arr.dpair_r(CM.Store(p, base, x, xs),
                   CM.Store(p, Nat.add(base, FT.FT.pow2(p)), y, xs), hs)
          Arr.DPair{
            CM.store_depth(p, base, x, xs, hxs),
            CM.store_depth(p, Nat.add(base, FT.FT.pow2(p)), y, xs, hys)}

# Reading cell `base + to_nat(i)` of a `Store` returns the ghost list's entry
# there and leaves the array unchanged.  The `go` lemmas mirror the array's own
# read recursion; `Arr.get_fst` gives the array half elsewhere.

def CM.nth_lo(-y: Array<U32>, r: Array<U32> & U32, +xs: +List<U32>, +k: Nat,
    +hr: {Arr.Arr.snd(Array<U32>, U32, r) == CS.CS.nth(xs, k) : U32}) ->
  {Arr.Arr.snd(Array<U32>, U32, Array.swap.lo(U32, y, r))
   == CS.CS.nth(xs, k) : U32}:
  (a2, +v) = r
  hr

def CM.nth_hi(-x: Array<U32>, r: Array<U32> & U32, +xs: +List<U32>, +k: Nat,
    +hr: {Arr.Arr.snd(Array<U32>, U32, r) == CS.CS.nth(xs, k) : U32}) ->
  {Arr.Arr.snd(Array<U32>, U32, Array.swap.hi(U32, x, r))
   == CS.CS.nth(xs, k) : U32}:
  (a2, +v) = r
  hr

def CM.store_get_go_lo(+p: Nat, +base: Nat, -x: Array<U32>, -y: Array<U32>,
    +xs: +List<U32>, +i: U32,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +hx: CM.Store(p, base, x, xs),
    d: &a1: Array<U32> -> &a2: Array<U32> ->
       {a1 == x : Array<U32>} & {a2 == a1 : Array<U32>},
    ih: @x2: Array<U32> -> CM.Store(p, base, x2, xs) ->
        {Arr.Arr.snd(Array<U32>, U32,
           Array.get.go(U32, x2, Arr.Arr.pow2_u32(p), i,
             U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))))
         == CS.CS.nth(xs, Nat.add(base, U32.to_nat(i))) : U32}) ->
  {Arr.Arr.snd(Array<U32>, U32,
     Array.get.go(U32, ANode{x, y}, Arr.Arr.pow2_u32(1n+p), i, True{}))
   == CS.CS.nth(xs, Nat.add(base, U32.to_nat(i))) : U32}:
  (x1, d2) = d
  (x2, pe) = d2
  (+ex1, +ex2) = pe
  +hx2 = CM.store_transport(p, base, x, x2, xs,
            Equal.sym(Array<U32>, x2, x,
              Equal.trans(Array<U32>, x2, x1, x, ex2, ex1)), hx)
  +h2 = ih(x2, hx2)
  +h1 : {Arr.Arr.snd(Array<U32>, U32,
           Array.get.go(U32, x1, Arr.Arr.pow2_u32(p), i,
             U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))))
         == CS.CS.nth(xs, Nat.add(base, U32.to_nat(i))) : U32} =
    Equal.trans(U32,
      Arr.Arr.snd(Array<U32>, U32,
        Array.get.go(U32, x1, Arr.Arr.pow2_u32(p), i,
          U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
      Arr.Arr.snd(Array<U32>, U32,
        Array.get.go(U32, x2, Arr.Arr.pow2_u32(p), i,
          U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
      CS.CS.nth(xs, Nat.add(base, U32.to_nat(i))),
      Equal.cong(Array<U32>, U32,
        z => Arr.Arr.snd(Array<U32>, U32,
               Array.get.go(U32, z, Arr.Arr.pow2_u32(p), i,
                 U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))))),
        x1, x2, Equal.sym(Array<U32>, x2, x1, ex2)),
      h2)
  %ex1 : {Arr.Arr.snd(Array<U32>, U32,
            Array.get.go(U32, ANode{_, y}, Arr.Arr.pow2_u32(1n+p), i, True{}))
          == CS.CS.nth(xs, Nat.add(base, U32.to_nat(i))) : U32}
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    {Arr.Arr.snd(Array<U32>, U32,
       Array.swap.lo(U32, y,
         Array.get.go(U32, x1, _, i, U32.is_lt(i, U32.shr(_)))))
     == CS.CS.nth(xs, Nat.add(base, U32.to_nat(i))) : U32}
  CM.nth_lo(y,
    Array.get.go(U32, x1, Arr.Arr.pow2_u32(p), i,
      U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p)))),
    xs, Nat.add(base, U32.to_nat(i)), h1)

def CM.store_get_go_hi(+p: Nat, +base: Nat, -x: Array<U32>, -y: Array<U32>,
    +xs: +List<U32>, +i: U32,
    +eshr: {U32.shr(Arr.Arr.pow2_u32(1n+p)) == Arr.Arr.pow2_u32(p) : U32},
    +eidx: {Nat.add(Nat.add(base, FT.FT.pow2(p)),
              U32.to_nat(U32.sub(i, Arr.Arr.pow2_u32(p))))
            == Nat.add(base, U32.to_nat(i)) : Nat},
    +hy: CM.Store(p, Nat.add(base, FT.FT.pow2(p)), y, xs),
    d: &a1: Array<U32> -> &a2: Array<U32> ->
       {a1 == y : Array<U32>} & {a2 == a1 : Array<U32>},
    ih: @y2: Array<U32> -> CM.Store(p, Nat.add(base, FT.FT.pow2(p)), y2, xs) ->
        {Arr.Arr.snd(Array<U32>, U32,
           Array.get.go(U32, y2, Arr.Arr.pow2_u32(p),
             U32.sub(i, Arr.Arr.pow2_u32(p)),
             U32.is_lt(U32.sub(i, Arr.Arr.pow2_u32(p)),
               U32.shr(Arr.Arr.pow2_u32(p)))))
         == CS.CS.nth(xs,
              Nat.add(Nat.add(base, FT.FT.pow2(p)),
                U32.to_nat(U32.sub(i, Arr.Arr.pow2_u32(p))))) : U32}) ->
  {Arr.Arr.snd(Array<U32>, U32,
     Array.get.go(U32, ANode{x, y}, Arr.Arr.pow2_u32(1n+p), i, False{}))
   == CS.CS.nth(xs, Nat.add(base, U32.to_nat(i))) : U32}:
  (y1, d2) = d
  (y2, pe) = d2
  (+ey1, +ey2) = pe
  +base2 = Nat.add(base, FT.FT.pow2(p))
  +ip = U32.sub(i, Arr.Arr.pow2_u32(p))
  +hy2 = CM.store_transport(p, base2, y, y2, xs,
            Equal.sym(Array<U32>, y2, y,
              Equal.trans(Array<U32>, y2, y1, y, ey2, ey1)), hy)
  +h2 = ih(y2, hy2)
  +h1 : {Arr.Arr.snd(Array<U32>, U32,
           Array.get.go(U32, y1, Arr.Arr.pow2_u32(p), ip,
             U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))))
         == CS.CS.nth(xs, Nat.add(base, U32.to_nat(i))) : U32} =
    Equal.trans(U32,
      Arr.Arr.snd(Array<U32>, U32,
        Array.get.go(U32, y1, Arr.Arr.pow2_u32(p), ip,
          U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
      CS.CS.nth(xs, Nat.add(base2, U32.to_nat(ip))),
      CS.CS.nth(xs, Nat.add(base, U32.to_nat(i))),
      Equal.trans(U32,
        Arr.Arr.snd(Array<U32>, U32,
          Array.get.go(U32, y1, Arr.Arr.pow2_u32(p), ip,
            U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
        Arr.Arr.snd(Array<U32>, U32,
          Array.get.go(U32, y2, Arr.Arr.pow2_u32(p), ip,
            U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
        CS.CS.nth(xs, Nat.add(base2, U32.to_nat(ip))),
        Equal.cong(Array<U32>, U32,
          z => Arr.Arr.snd(Array<U32>, U32,
                 Array.get.go(U32, z, Arr.Arr.pow2_u32(p), ip,
                   U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))))),
          y1, y2, Equal.sym(Array<U32>, y2, y1, ey2)),
        h2),
      Equal.cong(Nat, U32, x2 => CS.CS.nth(xs, x2),
        Nat.add(base2, U32.to_nat(ip)), Nat.add(base, U32.to_nat(i)), eidx))
  %ey1 : {Arr.Arr.snd(Array<U32>, U32,
            Array.get.go(U32, ANode{x, _}, Arr.Arr.pow2_u32(1n+p), i, False{}))
          == CS.CS.nth(xs, Nat.add(base, U32.to_nat(i))) : U32}
  %Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)), Arr.Arr.pow2_u32(p), eshr) :
    {Arr.Arr.snd(Array<U32>, U32,
       Array.swap.hi(U32, x,
         Array.get.go(U32, y1, _, U32.sub(i, _),
           U32.is_lt(U32.sub(i, _), U32.shr(_)))))
     == CS.CS.nth(xs, Nat.add(base, U32.to_nat(i))) : U32}
  CM.nth_hi(x,
    Array.get.go(U32, y1, Arr.Arr.pow2_u32(p), ip,
      U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p)))),
    xs, Nat.add(base, U32.to_nat(i)), h1)

def CM.store_get_go(+d: Nat, +base: Nat, a: Array<U32>, +xs: +List<U32>,
    +i: U32, z: Bool,
    +ez: {z == U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(d))) : Bool},
    +hlt: {Nat.is_lt(d, 32n) == True{} : Bool},
    +zi: {Arr.Arr.u32_zero_from(d, i) == True{} : Bool},
    +hs: CM.Store(d, base, a, xs)) ->
  {Arr.Arr.snd(Array<U32>, U32,
     Array.get.go(U32, a, Arr.Arr.pow2_u32(d), i, z))
   == CS.CS.nth(xs, Nat.add(base, U32.to_nat(i))) : U32}:
  match d:
    case 0n:
      match a:
        case ALeaf{+v}:
          +ei0 : {i == 0 : U32} = Arr.Arr.u32_eq_zero(i, zi)
          +ezero : {U32.to_nat(i) == 0n : Nat} =
            Equal.cong(U32, Nat, U32.to_nat, i, 0, ei0)
          +ebase : {Nat.add(base, U32.to_nat(i)) == base : Nat} =
            Equal.trans(Nat, Nat.add(base, U32.to_nat(i)), Nat.add(base, 0n),
              base,
              Equal.cong(Nat, Nat, x2 => Nat.add(base, x2), U32.to_nat(i), 0n,
                ezero),
              NatProof.NatPrf.add_zero(base))
          Equal.trans(U32, v, CS.CS.nth(xs, base),
            CS.CS.nth(xs, Nat.add(base, U32.to_nat(i))), hs,
            Equal.cong(Nat, U32, x2 => CS.CS.nth(xs, x2), base,
              Nat.add(base, U32.to_nat(i)), Equal.sym(Nat,
                Nat.add(base, U32.to_nat(i)), base, ebase)))
        case ANode{x2, y2}:
          Empty.absurd(
            {Arr.Arr.snd(Array<U32>, U32,
               Array.get.go(U32, ANode{x2, y2}, Arr.Arr.pow2_u32(0n), i, z))
             == CS.CS.nth(xs, Nat.add(base, U32.to_nat(i))) : U32}, hs)
    case 1n++p:
      match a:
        case ALeaf{v}:
          Empty.absurd(
            {Arr.Arr.snd(Array<U32>, U32,
               Array.get.go(U32, ALeaf{v}, Arr.Arr.pow2_u32(1n+p), i, z))
             == CS.CS.nth(xs, Nat.add(base, U32.to_nat(i))) : U32}, hs)
        case ANode{x, y}:
          match z:
            case True{}:
              +hx = Arr.Arr.dpair_l(CM.Store(p, base, x, xs),
                       CM.Store(p, Nat.add(base, FT.FT.pow2(p)), y, xs), hs)
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
                  Equal.cong(U32, Bool, x2 => U32.is_lt(i, x2),
                    Arr.Arr.pow2_u32(p), U32.shr(Arr.Arr.pow2_u32(1n+p)),
                    Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)),
                      Arr.Arr.pow2_u32(p), eshr)),
                  Equal.sym(Bool, True{},
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))), ez))
              +zip : {Arr.Arr.u32_zero_from(p, i) == True{} : Bool} =
                Arr.Arr.u32_zero_from_lt(p, i, zi, plt, ilt)
              CM.store_get_go_lo(p, base, x, y, xs, i, eshr, hx,
                Arr.Arr.dup(U32, x),
                x2 => hx2 =>
                  CM.store_get_go(p, base, x2, xs, i,
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, hx2))
            case False{}:
              +hy = Arr.Arr.dpair_r(CM.Store(p, base, x, xs),
                       CM.Store(p, Nat.add(base, FT.FT.pow2(p)), y, xs), hs)
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
                  Equal.cong(U32, Bool, x2 => U32.is_lt(i, x2),
                    Arr.Arr.pow2_u32(p), U32.shr(Arr.Arr.pow2_u32(1n+p)),
                    Equal.sym(U32, U32.shr(Arr.Arr.pow2_u32(1n+p)),
                      Arr.Arr.pow2_u32(p), eshr)),
                  Equal.sym(Bool, False{},
                    U32.is_lt(i, U32.shr(Arr.Arr.pow2_u32(1n+p))), ez))
              +ip = U32.sub(i, Arr.Arr.pow2_u32(p))
              +zip : {Arr.Arr.u32_zero_from(p, ip) == True{} : Bool} =
                Arr.Arr.u32_zero_from_ge(p, i, zi, plt, ige)
              +esub : {Nat.add(FT.FT.pow2(p), U32.to_nat(ip)) == U32.to_nat(i)
                       : Nat} =
                FT.FT.u32_to_nat_sub_pow2(p, i, zi, plt, ige)
              +eidx : {Nat.add(Nat.add(base, FT.FT.pow2(p)), U32.to_nat(ip))
                       == Nat.add(base, U32.to_nat(i)) : Nat} =
                Equal.trans(Nat,
                  Nat.add(Nat.add(base, FT.FT.pow2(p)), U32.to_nat(ip)),
                  Nat.add(base, Nat.add(FT.FT.pow2(p), U32.to_nat(ip))),
                  Nat.add(base, U32.to_nat(i)),
                  NatProof.NatPrf.add_assoc(base, FT.FT.pow2(p),
                    U32.to_nat(ip)),
                  Equal.cong(Nat, Nat, x2 => Nat.add(base, x2),
                    Nat.add(FT.FT.pow2(p), U32.to_nat(ip)), U32.to_nat(i),
                    esub))
              CM.store_get_go_hi(p, base, x, y, xs, i, eshr, eidx, hy,
                Arr.Arr.dup(U32, y),
                y2 => hy2 =>
                  CM.store_get_go(p, Nat.add(base, FT.FT.pow2(p)), y2, xs, ip,
                    U32.is_lt(ip, U32.shr(Arr.Arr.pow2_u32(p))), {==},
                    plt, zip, hy2))

# The two facts a machine read needs, in the form `Array.get` has them.  Both
# consume the array once, so they take a duplication of it: one copy carries
# the depth the read needs, the other is the array the read is about.
def CM.store_fst(+d: Nat, a: Array<U32>, +xs: +List<U32>, +k: Nat,
    +hd: {Nat.is_lt(d, 32n) == True{} : Bool},
    +hs: CM.Store(d, 0n, a, xs),
    d2: &a1: Array<U32> -> &a2: Array<U32> ->
        {a1 == a : Array<U32>} & {a2 == a1 : Array<U32>}) ->
  {Arr.Arr.fst(Array<U32>, U32, Array.get(U32, a, U32.from_nat(k)))
   == a : Array<U32>}:
  (a1, r1) = d2
  (a2, pe) = r1
  (+e1, +e2) = pe
  +hs1 = CM.store_transport(d, 0n, a, a1, xs, Equal.sym(Array<U32>, a1, a, e1), hs)
  +hd1 = CM.store_depth(d, 0n, a1, xs, hs1)
  +hd2 = Arr.Arr.depth_transport(U32, d, a1, a2,
            Equal.sym(Array<U32>, a2, a1, e2), hd1)
  +efst = Arr.Arr.get_fst(U32, d, a2, U32.from_nat(k), hd2)
  +e2a : {a2 == a : Array<U32>} =
    Equal.trans(Array<U32>, a2, a1, a, e2, e1)
  Equal.trans(Array<U32>,
    Arr.Arr.fst(Array<U32>, U32, Array.get(U32, a, U32.from_nat(k))),
    Arr.Arr.fst(Array<U32>, U32, Array.get(U32, a2, U32.from_nat(k))),
    a,
    Equal.cong(Array<U32>, Array<U32>,
      x => Arr.Arr.fst(Array<U32>, U32, Array.get(U32, x, U32.from_nat(k))),
      a, a2, Equal.sym(Array<U32>, a2, a, e2a)),
    Equal.trans(Array<U32>,
      Arr.Arr.fst(Array<U32>, U32, Array.get(U32, a2, U32.from_nat(k))),
      a2, a, efst, e2a))

# Three copies plus the pairwise equalities.  A machine read needs one copy for
# the depth, one for the `Array.get` reduction and one for the value lemma.
def CM.dup3_node(-x: Array<U32>, -y: Array<U32>,
    dl: &x1: Array<U32> -> &x2: Array<U32> -> &x3: Array<U32> ->
        ({x1 == x : Array<U32>} & {x2 == x1 : Array<U32>})
        & {x3 == x2 : Array<U32>},
    dr: &y1: Array<U32> -> &y2: Array<U32> -> &y3: Array<U32> ->
        ({y1 == y : Array<U32>} & {y2 == y1 : Array<U32>})
        & {y3 == y2 : Array<U32>}) ->
  &a1: Array<U32> -> &a2: Array<U32> -> &a3: Array<U32> ->
  ({a1 == ANode{x, y} : Array<U32>} & {a2 == a1 : Array<U32>})
  & {a3 == a2 : Array<U32>}:
  (x1, r1) = dl
  (x2, r2) = r1
  (x3, px) = r2
  ((ex1, ex2), ex3) = px
  (y1, s1) = dr
  (y2, s2) = s1
  (y3, py) = s2
  ((ey1, ey2), ey3) = py
  +e1 : {ANode{x1, y1} == ANode{x, y} : Array<U32>} =
    Equal.trans(Array<U32>, ANode{x1, y1}, ANode{x, y1}, ANode{x, y},
      Equal.cong(Array<U32>, Array<U32>, l => ANode{l, y1}, x1, x, ex1),
      Equal.cong(Array<U32>, Array<U32>, r => ANode{x, r}, y1, y, ey1))
  +e2 : {ANode{x2, y2} == ANode{x1, y1} : Array<U32>} =
    Equal.trans(Array<U32>, ANode{x2, y2}, ANode{x1, y2}, ANode{x1, y1},
      Equal.cong(Array<U32>, Array<U32>, l => ANode{l, y2}, x2, x1, ex2),
      Equal.cong(Array<U32>, Array<U32>, r => ANode{x1, r}, y2, y1, ey2))
  +e3 : {ANode{x3, y3} == ANode{x2, y2} : Array<U32>} =
    Equal.trans(Array<U32>, ANode{x3, y3}, ANode{x2, y3}, ANode{x2, y2},
      Equal.cong(Array<U32>, Array<U32>, l => ANode{l, y3}, x3, x2, ex3),
      Equal.cong(Array<U32>, Array<U32>, r => ANode{x2, r}, y3, y2, ey3))
  (ANode{x1, y1}, (ANode{x2, y2}, (ANode{x3, y3}, ((e1, e2), e3))))

def CM.dup3(a: Array<U32>) ->
  &a1: Array<U32> -> &a2: Array<U32> -> &a3: Array<U32> ->
  ({a1 == a : Array<U32>} & {a2 == a1 : Array<U32>})
  & {a3 == a2 : Array<U32>}:
  match a:
    case ALeaf{+x}:
      (ALeaf{x}, (ALeaf{x}, (ALeaf{x}, (({==}, {==}), {==}))))
    case ANode{x, y}:
      CM.dup3_node(x, y, CM.dup3(x), CM.dup3(y))
