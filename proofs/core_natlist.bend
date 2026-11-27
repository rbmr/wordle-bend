# Ghost `List<Nat>` code bookkeeping for the count machine.
#
# `CR.Count` (proofs/core_region.bend) models a count cell by membership of the
# code in a ghost `List<Nat>` (`CR.CR.mem`).  The machine's invariant also needs a
# *deduplicated* length of that list: `t = len(dedup nl)` where `nl` holds every
# processed code, duplicates kept.  `CS.dedup` is for `List<U32>` cells and
# cannot be applied to the `Nat` code list, so this file mirrors it on
# `List<Nat>` and proves the two length steps the candidate pass uses:
#
#   * `len_ndedup_add`:  adding a code at the head adds one iff it is new;
#   * `nlen_snoc`:       the touched list grows by exactly one per append.
#
# These are proof-only definitions; no runtime code uses them.
import Base
import ./core_list.bend as CS
import ./core_region.bend as CR
import ./nat.bend as NatProof

def CNL.dedup_cons(+x: Nat, b: Bool, +d: +List<Nat>) -> +List<Nat>:
  match b:
    case True{}:
      d
    case False{}:
      x <> d

def CNL.dedup(+xs: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      +d = CNL.dedup(rest)
      CNL.dedup_cons(x, CR.CR.mem(x, rest), d)

def CNL.len_dedup_cons(+x: Nat, b: Bool, +d: +List<Nat>) ->
  {CR.CR.nlen(CNL.dedup_cons(x, b, d))
   == Nat.add(CR.CR.nlen(d), U32.to_nat(Bool.to_u32(Bool.not(b)))) : Nat}:
  match b:
    case True{}:
      +ez : {Nat.add(CR.CR.nlen(d), 0n) == CR.CR.nlen(d) : Nat} =
        NatProof.NatPrf.add_zero(CR.CR.nlen(d))
      Equal.sym(Nat, Nat.add(CR.CR.nlen(d), 0n), CR.CR.nlen(d), ez)
    case False{}:
      Equal.sym(Nat, Nat.add(CR.CR.nlen(d), 1n), Nat.add(1n, CR.CR.nlen(d)),
        NatProof.NatPrf.add_comm(CR.CR.nlen(d), 1n))

# Adding a processed code at the head: the deduplicated length grows by one
# exactly when the code was not already present.  This is the counter step of
# machine phase 3 (`nl` becomes `c <> nl`, `t` grows by `1 - v`).
def CNL.len_ndedup_add(+x: Nat, +nl: +List<Nat>) ->
  {CR.CR.nlen(CNL.dedup(x <> nl))
   == Nat.add(CR.CR.nlen(CNL.dedup(nl)),
              U32.to_nat(Bool.to_u32(Bool.not(CR.CR.mem(x, nl))))) : Nat}:
  CNL.len_dedup_cons(x, CR.CR.mem(x, nl), CNL.dedup(nl))

# Membership of the appended code: `snoc` puts the code at the end, so the
# membership test that `CNL.dedup` performs is the analogue of the head test on
# the cons list.  These two lemmas are what a `len(dedup (snoc ...))` induction
# needs; see the note at the end of this file.
def CNL.mem_snoc_self(+x: Nat, +xs: +List<Nat>) ->
  {CR.CR.mem(x, CR.CR.snoc(x, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      +e : {Nat.is_eq(x, x) == True{} : Bool} = NatProof.NatPrf.is_eq_refl(x)
      +hi : {Bool.or(Nat.is_eq(x, x), False{}) == Bool.or(True{}, False{})
             : Bool} =
        Equal.cong(Bool, Bool, z => Bool.or(z, False{}),
          Nat.is_eq(x, x), True{}, e)
      Equal.trans(Bool, Bool.or(Nat.is_eq(x, x), False{}),
        Bool.or(True{}, False{}), True{}, hi, {==})
    case Con{y, rest}:
      +b = Nat.is_eq(x, y)
      +h = CNL.mem_snoc_self(x, rest)
      +hi : {Bool.or(b, CR.CR.mem(x, CR.CR.snoc(x, rest))) == Bool.or(b, True{})
             : Bool} =
        Equal.cong(Bool, Bool, z => Bool.or(b, z),
          CR.CR.mem(x, CR.CR.snoc(x, rest)), True{}, h)
      +hor : {Bool.or(b, True{}) == True{} : Bool} = CR.CR.or_true(b)
      Equal.trans(Bool, Bool.or(b, CR.CR.mem(x, CR.CR.snoc(x, rest))),
        Bool.or(b, True{}), True{}, hi, hor)

def CNL.mem_snoc_ne(+x: Nat, +c: Nat, +xs: +List<Nat>,
    +hne: {Nat.is_eq(x, c) == False{} : Bool}) ->
  {CR.CR.mem(x, CR.CR.snoc(c, xs)) == CR.CR.mem(x, xs) : Bool}:
  match xs:
    case Nil{}:
      +hi : {Bool.or(Nat.is_eq(x, c), False{})
             == Bool.or(False{}, False{}) : Bool} =
        Equal.cong(Bool, Bool, z => Bool.or(z, False{}),
          Nat.is_eq(x, c), False{}, hne)
      Equal.trans(Bool, Bool.or(Nat.is_eq(x, c), False{}),
        Bool.or(False{}, False{}), CR.CR.mem(x, Nil{}), hi, {==})
    case Con{y, rest}:
      +h = CNL.mem_snoc_ne(x, c, rest, hne)
      Equal.cong(Bool, Bool, z => Bool.or(Nat.is_eq(x, y), z),
        CR.CR.mem(x, CR.CR.snoc(c, rest)), CR.CR.mem(x, rest), h)

# Appending to the touched list grows it by exactly one cell.
def CNL.nlen_snoc(+c: Nat, +tl: +List<Nat>) ->
  {CR.CR.nlen(CR.CR.snoc(c, tl)) == Nat.add(1n, CR.CR.nlen(tl)) : Nat}:
  match tl:
    case Nil{}:
      {==}
    case Con{d, rest}:
      Equal.cong(Nat, Nat, z => Nat.add(1n, z),
        CR.CR.nlen(CR.CR.snoc(c, rest)), Nat.add(1n, CR.CR.nlen(rest)),
        CNL.nlen_snoc(c, rest))
