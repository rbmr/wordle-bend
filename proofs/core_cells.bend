# Per-cell array model lemmas for the flat count kernel.
#
# `DC.Cells(i, n, a, xs)` (in `core_dcount.bend`) relates cells `i..i+n-1` of
# the flat `Array<U32>` to a ghost list.  This module proves the read and write
# laws the count machine needs, without changing the runtime layout.
import Base
import ../src/core/packed.bend as Packed
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./array.bend as Arr
import ./fast_tbl.bend as FT
import ./fast_hist5.bend as FH
import ./core_list.bend as CS
import ./core_dcount.bend as CoreDC

# `U32.from_nat` is injective on the indices below `2^dep`.  This turns
# `Nat.is_eq(a,b) == False` into `U32.is_eq(from_nat(a), from_nat(b)) == False`,
# which is what `Arr.get_set_diff` needs.
def CC.u32_from_nat_ne_go(+dep: Nat, +a: Nat, +b: Nat,
    eqb: Bool,
    +he: {eqb == U32.is_eq(U32.from_nat(a), U32.from_nat(b)) : Bool},
    +hne: {Nat.is_eq(a, b) == False{} : Bool},
    +ha: {Nat.is_lt(a, FT.FT.pow2(dep)) == True{} : Bool},
    +hb: {Nat.is_lt(b, FT.FT.pow2(dep)) == True{} : Bool},
    +hd: {Nat.is_lt(dep, 32n) == True{} : Bool}) ->
  {U32.is_eq(U32.from_nat(a), U32.from_nat(b)) == False{} : Bool}:
  match eqb:
    case False{}:
      Equal.sym(Bool, False{}, U32.is_eq(U32.from_nat(a), U32.from_nat(b)), he)
    case True{}:
      +eu : {U32.from_nat(a) == U32.from_nat(b) : U32} =
        Arr.Arr.u32_is_eq_true(U32.from_nat(a), U32.from_nat(b),
          Equal.sym(Bool, True{}, U32.is_eq(U32.from_nat(a), U32.from_nat(b)), he))
      +en : {U32.to_nat(U32.from_nat(a)) == U32.to_nat(U32.from_nat(b)) : Nat} =
        Equal.cong(U32, Nat, U32.to_nat, U32.from_nat(a), U32.from_nat(b), eu)
      +eab : {a == b : Nat} =
        Equal.trans(Nat,
          a, U32.to_nat(U32.from_nat(a)), b,
          Equal.sym(Nat, U32.to_nat(U32.from_nat(a)), a,
            FT.FT.u32_to_nat_from_nat(dep, a, hd, ha)),
          Equal.trans(Nat,
            U32.to_nat(U32.from_nat(a)), U32.to_nat(U32.from_nat(b)), b,
            en,
            FT.FT.u32_to_nat_from_nat(dep, b, hd, hb)))
      +et : {Nat.is_eq(a, b) == True{} : Bool} =
        Equal.trans(Bool,
          Nat.is_eq(a, b), Nat.is_eq(b, b), True{},
          Equal.cong(Nat, Bool, x => Nat.is_eq(x, b), a, b, eab),
          NatProof.NatPrf.is_eq_refl(b))
      Empty.absurd(
        {U32.is_eq(U32.from_nat(a), U32.from_nat(b)) == False{} : Bool},
        Logic.Proof.false_ne_true(
          Equal.trans(Bool, False{}, Nat.is_eq(a, b), True{},
            Equal.sym(Bool, Nat.is_eq(a, b), False{}, hne), et)))

def CC.u32_from_nat_ne(+dep: Nat, +a: Nat, +b: Nat,
    +hne: {Nat.is_eq(a, b) == False{} : Bool},
    +ha: {Nat.is_lt(a, FT.FT.pow2(dep)) == True{} : Bool},
    +hb: {Nat.is_lt(b, FT.FT.pow2(dep)) == True{} : Bool},
    +hd: {Nat.is_lt(dep, 32n) == True{} : Bool}) ->
  {U32.is_eq(U32.from_nat(a), U32.from_nat(b)) == False{} : Bool}:
  CC.u32_from_nat_ne_go(dep, a, b,
    U32.is_eq(U32.from_nat(a), U32.from_nat(b)), {==}, hne, ha, hb, hd)

# Reading a cell of the model: cell `i+d` (with `d < n`) holds `nth(xs, i+d)`.
def CC.cells_get(+n: Nat, +d: Nat, +i: Nat, a: Array<U32>,
    +xs: +List<U32>, hc: CoreDC.DC.Cells(i, n, a, xs),
    +hd: {Nat.is_lt(d, n) == True{} : Bool}) ->
  {Arr.Arr.snd(Array<U32>, U32, Array.get(U32, a, U32.from_nat(Nat.add(d, i))))
   == CS.CS.nth(xs, Nat.add(d, i)) : U32}:
  match n:
    case 0n:
      Empty.absurd(
        {Arr.Arr.snd(Array<U32>, U32,
           Array.get(U32, a, U32.from_nat(Nat.add(d, i))))
         == CS.CS.nth(xs, Nat.add(d, i)) : U32},
        NatProof.Nat.not_lt_zero(d, hd))
    case 1n+np:
      match d:
        case 0n:
          (hhead, _) = hc
          hhead
        case 1n+dp:
          (_, htail) = hc
          +hd2 : {Nat.is_lt(dp, np) == True{} : Bool} = hd
          +ih = CC.cells_get(np, dp, Nat.add(1n, i), a, xs, htail, hd2)
          +eidx : {Nat.add(1n+dp, i) == Nat.add(dp, Nat.add(1n, i)) : Nat} =
            Equal.sym(Nat,
              Nat.add(dp, Nat.add(1n, i)),
              Nat.add(1n+dp, i),
              NatProof.NatPrf.add_succ(dp, i))
          Equal.trans(U32,
            Arr.Arr.snd(Array<U32>, U32,
              Array.get(U32, a, U32.from_nat(Nat.add(1n+dp, i)))),
            Arr.Arr.snd(Array<U32>, U32,
              Array.get(U32, a,
                U32.from_nat(Nat.add(dp, Nat.add(1n, i))))),
            CS.CS.nth(xs, Nat.add(1n+dp, i)),
            Equal.cong(Nat, U32,
              x => Arr.Arr.snd(Array<U32>, U32,
                     Array.get(U32, a, U32.from_nat(x))),
              Nat.add(1n+dp, i), Nat.add(dp, Nat.add(1n, i)), eidx),
            Equal.trans(U32,
              Arr.Arr.snd(Array<U32>, U32,
                Array.get(U32, a,
                  U32.from_nat(Nat.add(dp, Nat.add(1n, i))))),
              CS.CS.nth(xs, Nat.add(dp, Nat.add(1n, i))),
              CS.CS.nth(xs, Nat.add(1n+dp, i)),
              ih,
              Equal.cong(Nat, U32, x => CS.CS.nth(xs, x),
                Nat.add(dp, Nat.add(1n, i)), Nat.add(1n+dp, i),
                Equal.sym(Nat, Nat.add(1n+dp, i),
                  Nat.add(dp, Nat.add(1n, i)), eidx))))


# Four copies of one array plus the pairwise equalities.  `Array<T>` is not
# `Data`, so a lemma that needs the old array in several linear positions
# (`Arr.depth_transport`, `Arr.get_set_diff`, the recursive tail) cannot reuse
# one value.  This is the same duplication shape as
# `FH.hist5_step_swap_dup4`, generalised to four copies.
def CC.dup4_node(-T: Data, -xs: Array<T>, -ys: Array<T>,
    dl: &x1: Array<T> -> &x2: Array<T> -> &x3: Array<T> -> &x4: Array<T> ->
        ({x1 == xs : Array<T>} & {x2 == x1 : Array<T>})
        & ({x3 == x2 : Array<T>} & {x4 == x3 : Array<T>}),
    dr: &y1: Array<T> -> &y2: Array<T> -> &y3: Array<T> -> &y4: Array<T> ->
        ({y1 == ys : Array<T>} & {y2 == y1 : Array<T>})
        & ({y3 == y2 : Array<T>} & {y4 == y3 : Array<T>})) ->
  &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> &a4: Array<T> ->
  ({a1 == ANode{xs, ys} : Array<T>} & {a2 == a1 : Array<T>})
  & ({a3 == a2 : Array<T>} & {a4 == a3 : Array<T>}):
  (x1, r1) = dl
  (x2, r2) = r1
  (x3, r3) = r2
  (x4, px) = r3
  ((ex1, ex2), (ex3, ex4)) = px
  (y1, s1) = dr
  (y2, s2) = s1
  (y3, s3) = s2
  (y4, py) = s3
  ((ey1, ey2), (ey3, ey4)) = py
  +e1 : {ANode{x1, y1} == ANode{xs, ys} : Array<T>} =
    Equal.trans(Array<T>, ANode{x1, y1}, ANode{xs, y1}, ANode{xs, ys},
      Equal.cong(Array<T>, Array<T>, l => ANode{l, y1}, x1, xs, ex1),
      Equal.cong(Array<T>, Array<T>, r => ANode{xs, r}, y1, ys, ey1))
  +e2 : {ANode{x2, y2} == ANode{x1, y1} : Array<T>} =
    Equal.trans(Array<T>, ANode{x2, y2}, ANode{x1, y2}, ANode{x1, y1},
      Equal.cong(Array<T>, Array<T>, l => ANode{l, y2}, x2, x1, ex2),
      Equal.cong(Array<T>, Array<T>, r => ANode{x1, r}, y2, y1, ey2))
  +e3 : {ANode{x3, y3} == ANode{x2, y2} : Array<T>} =
    Equal.trans(Array<T>, ANode{x3, y3}, ANode{x2, y3}, ANode{x2, y2},
      Equal.cong(Array<T>, Array<T>, l => ANode{l, y3}, x3, x2, ex3),
      Equal.cong(Array<T>, Array<T>, r => ANode{x2, r}, y3, y2, ey3))
  +e4 : {ANode{x4, y4} == ANode{x3, y3} : Array<T>} =
    Equal.trans(Array<T>, ANode{x4, y4}, ANode{x3, y4}, ANode{x3, y3},
      Equal.cong(Array<T>, Array<T>, l => ANode{l, y4}, x4, x3, ex4),
      Equal.cong(Array<T>, Array<T>, r => ANode{x3, r}, y4, y3, ey4))
  (ANode{x1, y1},
   (ANode{x2, y2},
    (ANode{x3, y3},
     (ANode{x4, y4}, ((e1, e2), (e3, e4))))))

def CC.dup4(-T: Data, a: Array<T>) ->
  &a1: Array<T> -> &a2: Array<T> -> &a3: Array<T> -> &a4: Array<T> ->
  ({a1 == a : Array<T>} & {a2 == a1 : Array<T>})
  & ({a3 == a2 : Array<T>} & {a4 == a3 : Array<T>}):
  match a:
    case ALeaf{+x}:
      (ALeaf{x}, (ALeaf{x}, (ALeaf{x}, (ALeaf{x},
        (({==}, {==}), ({==}, {==}))))))
    case ANode{xs, ys}:
      CC.dup4_node(T, xs, ys, CC.dup4(T, xs), CC.dup4(T, ys))
