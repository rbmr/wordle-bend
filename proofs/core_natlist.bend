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
import ./logic.bend as Logic

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

# The counter invariant of machine phase 3 does **not** need a
# `len(dedup (snoc c tl))` lemma: the machine only appends the code to the
# touched list on a first occurrence (`mem(c, nl) = False`), so the two lists
# grow in the same step and the equality is `nlen_snoc` + `len_ndedup_add`.
# This is the append case: `len tl = len(dedup nl)` is preserved.
def CNL.touch_counter(+c: Nat, +nl: +List<Nat>, +tl: +List<Nat>,
    +ht: {CR.CR.nlen(tl) == CR.CR.nlen(CNL.dedup(nl)) : Nat},
    +hm: {CR.CR.mem(c, nl) == False{} : Bool}) ->
  {CR.CR.nlen(CR.CR.snoc(c, tl)) == CR.CR.nlen(CNL.dedup(c <> nl)) : Nat}:
  +hn : {Bool.not(CR.CR.mem(c, nl)) == True{} : Bool} =
    Equal.trans(Bool, Bool.not(CR.CR.mem(c, nl)), Bool.not(False{}), True{},
      Equal.cong(Bool, Bool, z => Bool.not(z), CR.CR.mem(c, nl), False{}, hm),
      {==})
  +hv : {U32.to_nat(Bool.to_u32(Bool.not(CR.CR.mem(c, nl)))) == 1n : Nat} =
    Equal.cong(Bool, Nat, z => U32.to_nat(Bool.to_u32(z)),
      Bool.not(CR.CR.mem(c, nl)), True{}, hn)
  +h3 : {CR.CR.nlen(CNL.dedup(c <> nl))
         == Nat.add(CR.CR.nlen(CNL.dedup(nl)), 1n) : Nat} =
    Equal.trans(Nat,
      CR.CR.nlen(CNL.dedup(c <> nl)),
      Nat.add(CR.CR.nlen(CNL.dedup(nl)),
              U32.to_nat(Bool.to_u32(Bool.not(CR.CR.mem(c, nl))))),
      Nat.add(CR.CR.nlen(CNL.dedup(nl)), 1n),
      CNL.len_ndedup_add(c, nl),
      CR.CR.add_cong_r(CR.CR.nlen(CNL.dedup(nl)),
        U32.to_nat(Bool.to_u32(Bool.not(CR.CR.mem(c, nl)))), 1n, hv))
  +h12 : {CR.CR.nlen(CR.CR.snoc(c, tl))
          == Nat.add(1n, CR.CR.nlen(CNL.dedup(nl))) : Nat} =
    Equal.trans(Nat, CR.CR.nlen(CR.CR.snoc(c, tl)),
      Nat.add(1n, CR.CR.nlen(tl)),
      Nat.add(1n, CR.CR.nlen(CNL.dedup(nl))),
      CNL.nlen_snoc(c, tl),
      CR.CR.add_cong_r(1n, CR.CR.nlen(tl), CR.CR.nlen(CNL.dedup(nl)), ht))
  Equal.trans(Nat, CR.CR.nlen(CR.CR.snoc(c, tl)),
    Nat.add(1n, CR.CR.nlen(CNL.dedup(nl))),
    CR.CR.nlen(CNL.dedup(c <> nl)),
    h12,
    Equal.trans(Nat, Nat.add(1n, CR.CR.nlen(CNL.dedup(nl))),
      Nat.add(CR.CR.nlen(CNL.dedup(nl)), 1n),
      CR.CR.nlen(CNL.dedup(c <> nl)),
      NatProof.NatPrf.add_comm(1n, CR.CR.nlen(CNL.dedup(nl))),
      Equal.sym(Nat, CR.CR.nlen(CNL.dedup(c <> nl)),
        Nat.add(CR.CR.nlen(CNL.dedup(nl)), 1n), h3)))

# The duplicate case: the code is already counted, the machine does not append
# to the touched list, and adding the duplicate to the processed list leaves
# its deduplicated length unchanged.
def CNL.dup_counter(+c: Nat, +nl: +List<Nat>,
    +hm: {CR.CR.mem(c, nl) == True{} : Bool}) ->
  {CR.CR.nlen(CNL.dedup(c <> nl)) == CR.CR.nlen(CNL.dedup(nl)) : Nat}:
  +hn : {Bool.not(CR.CR.mem(c, nl)) == False{} : Bool} =
    Equal.trans(Bool, Bool.not(CR.CR.mem(c, nl)), Bool.not(True{}), False{},
      Equal.cong(Bool, Bool, z => Bool.not(z), CR.CR.mem(c, nl), True{}, hm),
      {==})
  +hv : {U32.to_nat(Bool.to_u32(Bool.not(CR.CR.mem(c, nl)))) == 0n : Nat} =
    Equal.cong(Bool, Nat, z => U32.to_nat(Bool.to_u32(z)),
      Bool.not(CR.CR.mem(c, nl)), False{}, hn)
  +h3 : {CR.CR.nlen(CNL.dedup(c <> nl))
         == Nat.add(CR.CR.nlen(CNL.dedup(nl)), 0n) : Nat} =
    Equal.trans(Nat,
      CR.CR.nlen(CNL.dedup(c <> nl)),
      Nat.add(CR.CR.nlen(CNL.dedup(nl)),
              U32.to_nat(Bool.to_u32(Bool.not(CR.CR.mem(c, nl))))),
      Nat.add(CR.CR.nlen(CNL.dedup(nl)), 0n),
      CNL.len_ndedup_add(c, nl),
      CR.CR.add_cong_r(CR.CR.nlen(CNL.dedup(nl)),
        U32.to_nat(Bool.to_u32(Bool.not(CR.CR.mem(c, nl)))), 0n, hv))
  Equal.trans(Nat, CR.CR.nlen(CNL.dedup(c <> nl)),
    Nat.add(CR.CR.nlen(CNL.dedup(nl)), 0n),
    CR.CR.nlen(CNL.dedup(nl)),
    h3, NatProof.NatPrf.add_zero(CR.CR.nlen(CNL.dedup(nl))))

# `Nat.is_eq` is symmetric in its `False` direction too (the `True` direction
# is `NatProof.NatPrf.is_eq_sym`).  The `len_dedup_snoc` induction needs it to
# pass a `False` decision from `is_eq(c, d)` to `mem(c, d <> rest)`'s head test
# and to `mem_snoc_ne`'s head test, which are stated the other way round.
def CNL.is_eq_sym_false(a: Nat, b: Nat,
    e: {Nat.is_eq(a, b) == False{} : Bool}) ->
  {Nat.is_eq(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool},
                   Logic.Proof.true_ne_false(e))
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      CNL.is_eq_sym_false(ap, bp, e)
