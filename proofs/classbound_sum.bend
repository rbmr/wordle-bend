# Saturating sums below infinity are plain sums.
#
# The guess loop accumulates child costs with `sat_add inf`, which answers
# infinity as soon as a part is infinite. When the total stays below infinity,
# every partial sum does too, so the saturating fold is the plain sum of the
# class costs. This is what turns the numeric accumulator into the `Maybe` value
# the cover lemma compares: `OV.mv inf` of the fold is the `MAdd` of the class
# values.
#
# The proof traverses the class-cost list once and returns both facts, the plain
# sum and the `Maybe` fold, because a list of `Type`-valued proofs cannot be
# consumed twice.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./optimalvalue.bend as OV
import ./cover_maybe.bend as CoverMaybe
import ./sat.bend as Sat
import ./classbound_nat.bend as CBN

# Equality helpers for the reusable `Maybe`, whose type the parser refuses as a
# bare first argument to `Equal.sym` and `Equal.trans`.
def CU.msym(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>,
    e: {a == b : Maybe<&2, Nat>}) -> {b == a : Maybe<&2, Nat>}:
  Equal.sym(Maybe<&2, Nat>, a, b, e)

def CU.mtrans(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>, c: Maybe<&2, Nat>,
    e1: {a == b : Maybe<&2, Nat>}, e2: {b == c : Maybe<&2, Nat>}) ->
  {a == c : Maybe<&2, Nat>}:
  Equal.trans(Maybe<&2, Nat>, a, b, c, e1, e2)

# Eliminate a computed pair with a continuation.
def CU.use_pair(-R: Type, -A: Type, -B: Type, p: A & B,
    k: A -> B -> R) -> R:
  match p:
    case (a, b):
      k(a, b)

# Every cost in a list is below infinity.
def CU.AllLt(+inf: Nat, +cs: +List<Nat>) -> Type:
  match cs:
    case Nil{}:
      Unit
    case Con{c, t}:
      {Nat.is_lt(c, inf) == True{} : Bool} & CU.AllLt(inf, t)

# A part of a finite total is below infinity.
def CU.part_lt(+inf: Nat, +a: Nat, +b: Nat,
    +e: {Nat.is_lt(Nat.add(a, b), inf) == True{} : Bool}) ->
  {Nat.is_lt(b, inf) == True{} : Bool}:
  +h : {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool} =
    NatProof.Nat.is_le_add_self_l(a, b)
  NatProof.Nat.is_le_lt_trans(b, Nat.add(a, b), inf, h, e)

def CU.sum_part_lt(+inf: Nat, +acc: Nat, +cs: +List<Nat>,
    +e: {Nat.is_lt(Nat.add(acc, CBN.CB.sum(cs)), inf) == True{} : Bool}) ->
  {Nat.is_lt(CBN.CB.sum(cs), inf) == True{} : Bool}:
  CU.part_lt(inf, acc, CBN.CB.sum(cs), e)

def CU.acc_part_lt(+inf: Nat, +acc: Nat, +cs: +List<Nat>,
    +e: {Nat.is_lt(Nat.add(acc, CBN.CB.sum(cs)), inf) == True{} : Bool}) ->
  {Nat.is_lt(acc, inf) == True{} : Bool}:
  +h : {Nat.is_le(acc, Nat.add(CBN.CB.sum(cs), acc)) == True{} : Bool} =
    NatProof.Nat.is_le_add_self_l(CBN.CB.sum(cs), acc)
  +ec : {Nat.add(CBN.CB.sum(cs), acc) == Nat.add(acc, CBN.CB.sum(cs)) : Nat} =
    NatProof.NatPrf.add_comm(CBN.CB.sum(cs), acc)
  +h2 : {Nat.is_le(acc, Nat.add(acc, CBN.CB.sum(cs))) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(acc, Nat.add(CBN.CB.sum(cs), acc),
      Nat.add(acc, CBN.CB.sum(cs)), ec, h)
  NatProof.Nat.is_le_lt_trans(acc, Nat.add(acc, CBN.CB.sum(cs)), inf, h2, e)

# The `MAdd` fold of the class values.
def CU.madds(+inf: Nat, +cs: +List<Nat>) -> Maybe<&2, Nat>:
  match cs:
    case Nil{}:
      Some{0n}
    case Con{c, t}:
      CoverMaybe.Cover.MAdd(OV.OV.mv(inf, c), CU.madds(inf, t))

# One traversal: the saturating fold is the plain sum, and the `Maybe` fold is
# the `Some` of that sum.
def CU.sumL_both(+inf: Nat, +cs: +List<Nat>, +acc: Nat,
    +tot: {Nat.is_lt(Nat.add(acc, CBN.CB.sum(cs)), inf) == True{} : Bool},
    all: CU.AllLt(inf, cs)) ->
  {OV.OV.sumL(inf, cs, acc) == Nat.add(acc, CBN.CB.sum(cs)) : Nat}
  & {CU.madds(inf, cs) == Some{CBN.CB.sum(cs)} : Maybe<&2, Nat>}:
  match cs:
    case Nil{}:
      (Equal.sym(Nat, Nat.add(acc, 0n), acc, NatProof.NatPrf.add_zero(acc)), {==})
    case Con{c, t}:
      (ch, ct) = all
      +acc_lt : {Nat.is_lt(acc, inf) == True{} : Bool} =
        CU.acc_part_lt(inf, acc, c <> t, tot)
      +ec_le0 : {Nat.is_le(c, Nat.add(CBN.CB.sum(t), c)) == True{} : Bool} =
        NatProof.Nat.is_le_add_self_l(CBN.CB.sum(t), c)
      +ec_comm : {Nat.add(CBN.CB.sum(t), c) == Nat.add(c, CBN.CB.sum(t)) : Nat} =
        NatProof.NatPrf.add_comm(CBN.CB.sum(t), c)
      +ec_le : {Nat.is_le(c, Nat.add(c, CBN.CB.sum(t))) == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(c, Nat.add(CBN.CB.sum(t), c),
          Nat.add(c, CBN.CB.sum(t)), ec_comm, ec_le0)
      +ac_le : {Nat.is_le(Nat.add(acc, c),
                   Nat.add(acc, Nat.add(c, CBN.CB.sum(t)))) == True{} : Bool} =
        NatProof.Nat.is_le_add_l(c, Nat.add(c, CBN.CB.sum(t)), acc, ec_le)
      +ac_lt : {Nat.is_lt(Nat.add(acc, c), inf) == True{} : Bool} =
        NatProof.Nat.is_le_lt_trans(Nat.add(acc, c),
          Nat.add(acc, Nat.add(c, CBN.CB.sum(t))), inf, ac_le, tot)
      +ge_acc : {Nat.is_ge(acc, inf) == False{} : Bool} =
        OV.OV.ge_false_of_lt(acc, inf, acc_lt)
      +ge_c : {Nat.is_ge(c, inf) == False{} : Bool} =
        OV.OV.ge_false_of_lt(c, inf, ch)
      +ge_ac : {Nat.is_ge(Nat.add(acc, c), inf) == False{} : Bool} =
        OV.OV.ge_false_of_lt(Nat.add(acc, c), inf, ac_lt)
      +e_sat : {SolveRef.sat_add(inf, acc, c) == Nat.add(acc, c) : Nat} =
        OV.OV.sat_fin(inf, acc, c, ge_acc, ge_c)
      +tot2 : {Nat.is_lt(Nat.add(Nat.add(acc, c), CBN.CB.sum(t)), inf) == True{}
               : Bool} =
        CBN.CB.lt_eq_l(inf, Nat.add(acc, Nat.add(c, CBN.CB.sum(t))),
          Nat.add(Nat.add(acc, c), CBN.CB.sum(t)),
          Equal.sym(Nat, Nat.add(Nat.add(acc, c), CBN.CB.sum(t)),
                    Nat.add(acc, Nat.add(c, CBN.CB.sum(t))),
                    NatProof.NatPrf.add_assoc(acc, c, CBN.CB.sum(t))),
          tot)
      CU.use_pair(
        {OV.OV.sumL(inf, c <> t, acc) == Nat.add(acc, CBN.CB.sum(c <> t)) : Nat}
        & {CU.madds(inf, c <> t) == Some{CBN.CB.sum(c <> t)} : Maybe<&2, Nat>},
        {OV.OV.sumL(inf, t, Nat.add(acc, c))
         == Nat.add(Nat.add(acc, c), CBN.CB.sum(t)) : Nat},
        {CU.madds(inf, t) == Some{CBN.CB.sum(t)} : Maybe<&2, Nat>},
        CU.sumL_both(inf, t, Nat.add(acc, c), tot2, ct),
        plain_t => fold_t =>
          +e1 : {OV.OV.sumL(inf, Con{c, t}, acc)
                 == OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c)) : Nat} =
            {==}
          +e2 : {OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c))
                 == OV.OV.sumL(inf, t, Nat.add(acc, c)) : Nat} =
            Equal.cong(Nat, Nat, x => OV.OV.sumL(inf, t, x),
                       SolveRef.sat_add(inf, acc, c), Nat.add(acc, c), e_sat)
          +e3 : {Nat.add(Nat.add(acc, c), CBN.CB.sum(t))
                 == Nat.add(acc, Nat.add(c, CBN.CB.sum(t))) : Nat} =
            NatProof.NatPrf.add_assoc(acc, c, CBN.CB.sum(t))
          +plain0 : {OV.OV.sumL(inf, Con{c, t}, acc)
                     == Nat.add(Nat.add(acc, c), CBN.CB.sum(t)) : Nat} =
            Equal.trans(Nat, OV.OV.sumL(inf, Con{c, t}, acc),
              OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c)),
              Nat.add(Nat.add(acc, c), CBN.CB.sum(t)), e1,
              Equal.trans(Nat, OV.OV.sumL(inf, t, SolveRef.sat_add(inf, acc, c)),
                OV.OV.sumL(inf, t, Nat.add(acc, c)),
                Nat.add(Nat.add(acc, c), CBN.CB.sum(t)), e2, plain_t))
          +plain : {OV.OV.sumL(inf, Con{c, t}, acc)
                    == Nat.add(acc, CBN.CB.sum(Con{c, t})) : Nat} =
            Equal.trans(Nat, OV.OV.sumL(inf, Con{c, t}, acc),
              Nat.add(Nat.add(acc, c), CBN.CB.sum(t)),
              Nat.add(acc, CBN.CB.sum(Con{c, t})), plain0, e3)
          +e_mv : {OV.OV.mv(inf, c) == Some{c} : Maybe<&2, Nat>} =
            OV.OV.mv_fin(inf, c, ge_c)
          +fold1 : {CoverMaybe.Cover.MAdd(OV.OV.mv(inf, c), CU.madds(inf, t))
                    == CoverMaybe.Cover.MAdd(Some{c}, Some{CBN.CB.sum(t)})
                    : Maybe<&2, Nat>} =
            CU.mtrans(
              CoverMaybe.Cover.MAdd(OV.OV.mv(inf, c), CU.madds(inf, t)),
              CoverMaybe.Cover.MAdd(Some{c}, CU.madds(inf, t)),
              CoverMaybe.Cover.MAdd(Some{c}, Some{CBN.CB.sum(t)}),
              Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>,
                x => CoverMaybe.Cover.MAdd(x, CU.madds(inf, t)),
                OV.OV.mv(inf, c), Some{c}, e_mv),
              Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>,
                x => CoverMaybe.Cover.MAdd(Some{c}, x),
                CU.madds(inf, t), Some{CBN.CB.sum(t)}, fold_t))
          +fold : {CU.madds(inf, Con{c, t}) == Some{CBN.CB.sum(Con{c, t})}
                   : Maybe<&2, Nat>} =
            CU.mtrans(CoverMaybe.Cover.MAdd(OV.OV.mv(inf, c), CU.madds(inf, t)),
              CoverMaybe.Cover.MAdd(Some{c}, Some{CBN.CB.sum(t)}),
              Some{CBN.CB.sum(Con{c, t})}, fold1, {==})
          (plain, fold))

# The saturating fold is the plain sum when the total is below infinity.
def CU.sumL_plain(+inf: Nat, +cs: +List<Nat>, +acc: Nat,
    +tot: {Nat.is_lt(Nat.add(acc, CBN.CB.sum(cs)), inf) == True{} : Bool},
    all: CU.AllLt(inf, cs)) ->
  {OV.OV.sumL(inf, cs, acc) == Nat.add(acc, CBN.CB.sum(cs)) : Nat}:
  CU.use_pair(
    {OV.OV.sumL(inf, cs, acc) == Nat.add(acc, CBN.CB.sum(cs)) : Nat},
    {OV.OV.sumL(inf, cs, acc) == Nat.add(acc, CBN.CB.sum(cs)) : Nat},
    {CU.madds(inf, cs) == Some{CBN.CB.sum(cs)} : Maybe<&2, Nat>},
    CU.sumL_both(inf, cs, acc, tot, all),
    plain => fold => plain)

# Every finite class value folds to the sum.
def CU.madds_some(+inf: Nat, +cs: +List<Nat>, all: CU.AllLt(inf, cs)) ->
  {CU.madds(inf, cs) == Some{CBN.CB.sum(cs)} : Maybe<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case Con{c, t}:
      (ch, ct) = all
      +e_mv : {OV.OV.mv(inf, c) == Some{c} : Maybe<&2, Nat>} =
        OV.OV.mv_fin(inf, c, OV.OV.ge_false_of_lt(c, inf, ch))
      +ih : {CU.madds(inf, t) == Some{CBN.CB.sum(t)} : Maybe<&2, Nat>} =
        CU.madds_some(inf, t, ct)
      +fold1 : {CoverMaybe.Cover.MAdd(OV.OV.mv(inf, c), CU.madds(inf, t))
                == CoverMaybe.Cover.MAdd(Some{c}, Some{CBN.CB.sum(t)})
                : Maybe<&2, Nat>} =
        CU.mtrans(
          CoverMaybe.Cover.MAdd(OV.OV.mv(inf, c), CU.madds(inf, t)),
          CoverMaybe.Cover.MAdd(Some{c}, CU.madds(inf, t)),
          CoverMaybe.Cover.MAdd(Some{c}, Some{CBN.CB.sum(t)}),
          Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>,
            x => CoverMaybe.Cover.MAdd(x, CU.madds(inf, t)),
            OV.OV.mv(inf, c), Some{c}, e_mv),
          Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>,
            x => CoverMaybe.Cover.MAdd(Some{c}, x),
            CU.madds(inf, t), Some{CBN.CB.sum(t)}, ih))
      CU.mtrans(CoverMaybe.Cover.MAdd(OV.OV.mv(inf, c), CU.madds(inf, t)),
        CoverMaybe.Cover.MAdd(Some{c}, Some{CBN.CB.sum(t)}),
        Some{CBN.CB.sum(Con{c, t})}, fold1, {==})

# The value of the saturating fold is the `MAdd` of the class values.
def CU.val_sumL(+inf: Nat, +cs: +List<Nat>, +acc: Nat,
    +tot: {Nat.is_lt(Nat.add(acc, CBN.CB.sum(cs)), inf) == True{} : Bool},
    all: CU.AllLt(inf, cs)) ->
  {OV.OV.mv(inf, OV.OV.sumL(inf, cs, acc))
   == CoverMaybe.Cover.MAdd(OV.OV.mv(inf, acc), CU.madds(inf, cs))
   : Maybe<&2, Nat>}:
  CU.use_pair(
    {OV.OV.mv(inf, OV.OV.sumL(inf, cs, acc))
     == CoverMaybe.Cover.MAdd(OV.OV.mv(inf, acc), CU.madds(inf, cs))
     : Maybe<&2, Nat>},
    {OV.OV.sumL(inf, cs, acc) == Nat.add(acc, CBN.CB.sum(cs)) : Nat},
    {CU.madds(inf, cs) == Some{CBN.CB.sum(cs)} : Maybe<&2, Nat>},
    CU.sumL_both(inf, cs, acc, tot, all),
    plain => fold =>
      +acc_lt : {Nat.is_lt(acc, inf) == True{} : Bool} =
        CU.acc_part_lt(inf, acc, cs, tot)
      +sum_lt : {Nat.is_lt(CBN.CB.sum(cs), inf) == True{} : Bool} =
        CU.sum_part_lt(inf, acc, cs, tot)
      +e1 : {OV.OV.mv(inf, OV.OV.sumL(inf, cs, acc))
             == OV.OV.mv(inf, Nat.add(acc, CBN.CB.sum(cs))) : Maybe<&2, Nat>} =
        Equal.cong(Nat, Maybe<&2, Nat>, x => OV.OV.mv(inf, x),
                   OV.OV.sumL(inf, cs, acc), Nat.add(acc, CBN.CB.sum(cs)), plain)
      +ge_acc : {Nat.is_ge(acc, inf) == False{} : Bool} =
        OV.OV.ge_false_of_lt(acc, inf, acc_lt)
      +ge_sum : {Nat.is_ge(CBN.CB.sum(cs), inf) == False{} : Bool} =
        OV.OV.ge_false_of_lt(CBN.CB.sum(cs), inf, sum_lt)
      +ge_tot : {Nat.is_ge(Nat.add(acc, CBN.CB.sum(cs)), inf) == False{} : Bool} =
        OV.OV.ge_false_of_lt(Nat.add(acc, CBN.CB.sum(cs)), inf, tot)
      +e_sat : {SolveRef.sat_add(inf, acc, CBN.CB.sum(cs))
                == Nat.add(acc, CBN.CB.sum(cs)) : Nat} =
        OV.OV.sat_fin(inf, acc, CBN.CB.sum(cs), ge_acc, ge_sum)
      +e2a : {OV.OV.mv(inf, Nat.add(acc, CBN.CB.sum(cs)))
              == OV.OV.mv(inf, SolveRef.sat_add(inf, acc, CBN.CB.sum(cs)))
              : Maybe<&2, Nat>} =
        Equal.cong(Nat, Maybe<&2, Nat>, x => OV.OV.mv(inf, x),
                   Nat.add(acc, CBN.CB.sum(cs)),
                   SolveRef.sat_add(inf, acc, CBN.CB.sum(cs)), Equal.sym(Nat,
                     SolveRef.sat_add(inf, acc, CBN.CB.sum(cs)),
                     Nat.add(acc, CBN.CB.sum(cs)), e_sat))
      +e2b : {OV.OV.mv(inf, SolveRef.sat_add(inf, acc, CBN.CB.sum(cs)))
              == CoverMaybe.Cover.MAdd(OV.OV.mv(inf, acc),
                   OV.OV.mv(inf, CBN.CB.sum(cs)))
              : Maybe<&2, Nat>} =
        OV.OV.mv_add_fin(inf, acc, CBN.CB.sum(cs), ge_acc, ge_sum, ge_tot)
      +e_sum : {OV.OV.mv(inf, CBN.CB.sum(cs)) == Some{CBN.CB.sum(cs)}
                : Maybe<&2, Nat>} =
        OV.OV.mv_fin(inf, CBN.CB.sum(cs), ge_sum)
      +e3 : {CoverMaybe.Cover.MAdd(OV.OV.mv(inf, acc),
                OV.OV.mv(inf, CBN.CB.sum(cs)))
             == CoverMaybe.Cover.MAdd(OV.OV.mv(inf, acc), CU.madds(inf, cs))
             : Maybe<&2, Nat>} =
        Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>,
          x => CoverMaybe.Cover.MAdd(OV.OV.mv(inf, acc), x),
          OV.OV.mv(inf, CBN.CB.sum(cs)), CU.madds(inf, cs),
          CU.mtrans(OV.OV.mv(inf, CBN.CB.sum(cs)), Some{CBN.CB.sum(cs)},
                    CU.madds(inf, cs), e_sum,
                    CU.msym(CU.madds(inf, cs), Some{CBN.CB.sum(cs)}, fold)))
      CU.mtrans(OV.OV.mv(inf, OV.OV.sumL(inf, cs, acc)),
        OV.OV.mv(inf, Nat.add(acc, CBN.CB.sum(cs))),
        CoverMaybe.Cover.MAdd(OV.OV.mv(inf, acc), CU.madds(inf, cs)), e1,
        CU.mtrans(OV.OV.mv(inf, Nat.add(acc, CBN.CB.sum(cs))),
          OV.OV.mv(inf, SolveRef.sat_add(inf, acc, CBN.CB.sum(cs))),
          CoverMaybe.Cover.MAdd(OV.OV.mv(inf, acc), CU.madds(inf, cs)),
          e2a, CU.mtrans(
            OV.OV.mv(inf, SolveRef.sat_add(inf, acc, CBN.CB.sum(cs))),
            CoverMaybe.Cover.MAdd(OV.OV.mv(inf, acc),
              OV.OV.mv(inf, CBN.CB.sum(cs))),
            CoverMaybe.Cover.MAdd(OV.OV.mv(inf, acc), CU.madds(inf, cs)),
            e2b, e3))))

# The cost field of a finished guess is the cost of its tree. This is the
# candidate branch of `finish_guess`: the node cost is below infinity, so the
# saturating sum of the candidate count and the class-cost sum is a plain sum,
# and the class-cost sum is the node's own cost.
def CU.finish_cost(+inf: Nat, +S: +List<+List<Nat>>, +g: +List<Nat>,
    +kids: +List<Tree.Child>, +cs: +List<Nat>, +sum: Nat,
    +lt: {Nat.is_lt(SolveRef.sat_add(inf, Groups.len_words(S), sum), inf)
          == True{} : Bool},
    +sum_eq: {sum == CBN.CB.sum(cs) : Nat},
    +tree_eq: {Tree.cost(Tree.Node{g, kids}, S)
                == Nat.add(Groups.len_words(S), CBN.CB.sum(cs)) : Nat}) ->
  {SolveRef.sat_add(inf, Groups.len_words(S), sum)
   == Tree.cost(Tree.Node{g, kids}, S) : Nat}:
  +n_lt : {Nat.is_lt(Groups.len_words(S), inf) == True{} : Bool} =
    Sat.SB.sat_add_lt_l(inf, Groups.len_words(S), sum, lt)
  +s_lt : {Nat.is_lt(sum, inf) == True{} : Bool} =
    Sat.SB.sat_add_lt_r(inf, Groups.len_words(S), sum, lt)
  +e_sat : {SolveRef.sat_add(inf, Groups.len_words(S), sum)
            == Nat.add(Groups.len_words(S), sum) : Nat} =
    OV.OV.sat_fin(inf, Groups.len_words(S), sum,
      OV.OV.ge_false_of_lt(Groups.len_words(S), inf, n_lt),
      OV.OV.ge_false_of_lt(sum, inf, s_lt))
  +e1 : {Nat.add(Groups.len_words(S), sum)
         == Nat.add(Groups.len_words(S), CBN.CB.sum(cs)) : Nat} =
    Equal.cong(Nat, Nat, x => Nat.add(Groups.len_words(S), x),
               sum, CBN.CB.sum(cs), sum_eq)
  Equal.trans(Nat, SolveRef.sat_add(inf, Groups.len_words(S), sum),
    Nat.add(Groups.len_words(S), sum),
    Tree.cost(Tree.Node{g, kids}, S), e_sat,
    Equal.trans(Nat, Nat.add(Groups.len_words(S), sum),
      Nat.add(Groups.len_words(S), CBN.CB.sum(cs)),
      Tree.cost(Tree.Node{g, kids}, S), e1,
      Equal.sym(Nat, Tree.cost(Tree.Node{g, kids}, S),
                Nat.add(Groups.len_words(S), CBN.CB.sum(cs)), tree_eq)))
