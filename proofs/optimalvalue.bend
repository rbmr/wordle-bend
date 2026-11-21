# The value of a search result, as a `Maybe` cost.
#
# The optimality argument compares the search result with the oracle value of
# the `cover` lemma: the result's cost as a `Maybe Nat` (infinity is `None`) is
# the minimum over the guesses of their class sums. This module collects the
# `Maybe` arithmetic that comparison needs: the value of a result, the
# correspondence with the saturating sum, associativity of `MAdd`, and
# monotonicity of `MMin`.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./cover_maybe.bend as CoverMaybe
import ./cover.bend as Cover

# The cost of a result as a `Maybe`: `None` at or above infinity.
def OV.mv(+inf: Nat, +cost: Nat) -> Maybe<&2, Nat>:
  Feedback.Bool.case(Maybe<&2, Nat>, Nat.is_ge(cost, inf), None{}, Some{cost})

# The value of a search result.
def OV.val(+inf: Nat, best: SolveRef.Best) -> Maybe<&2, Nat>:
  match best:
    case SolveRef.Best{tree, +cost}:
      OV.mv(inf, cost)

# `is_ge` is false below infinity.
def OV.ge_false_of_lt_go(a: Nat, b: Nat, c: Cmp,
    +ec: {c == Nat.cmp(a, b) : Cmp},
    lt: {Cmp.is_lt(c) == True{} : Bool}) ->
  {Cmp.is_ge(c) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_ge(EQ{}) == False{} : Bool},
        Logic.Proof.false_ne_true(lt))
    case GT{}:
      Empty.absurd({Cmp.is_ge(GT{}) == False{} : Bool},
        Logic.Proof.false_ne_true(lt))

def OV.ge_false_of_lt(+a: Nat, +b: Nat,
    lt: {Nat.is_lt(a, b) == True{} : Bool}) ->
  {Nat.is_ge(a, b) == False{} : Bool}:
  OV.ge_false_of_lt_go(a, b, Nat.cmp(a, b), {==}, lt)

# The value at a finite cost.
def OV.mv_of_lt(+inf: Nat, +cost: Nat,
    lt: {Nat.is_lt(cost, inf) == True{} : Bool}) ->
  {OV.mv(inf, cost) == Some{cost} : Maybe<&2, Nat>}:
  Equal.cong(Bool, Maybe<&2, Nat>,
    x => Feedback.Bool.case(Maybe<&2, Nat>, x, None{}, Some{cost}),
    Nat.is_ge(cost, inf), False{}, OV.ge_false_of_lt(cost, inf, lt))

# The value at an infinite cost.
def OV.mv_of_ge(+inf: Nat, +cost: Nat,
    ge: {Nat.is_ge(cost, inf) == True{} : Bool}) ->
  {OV.mv(inf, cost) == None{} : Maybe<&2, Nat>}:
  Equal.cong(Bool, Maybe<&2, Nat>,
    x => Feedback.Bool.case(Maybe<&2, Nat>, x, None{}, Some{cost}),
    Nat.is_ge(cost, inf), True{}, ge)

# `Some` below `Some` is the numeric order.
def OV.mle_some(+x: Nat, +y: Nat,
    e: {Nat.is_le(x, y) == True{} : Bool}) ->
  CoverMaybe.Cover.MLe(Some{x}, Some{y}):
  e

# Associativity of the `Maybe` sum.
def OV.madd_assoc(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>, c: Maybe<&2, Nat>) ->
  {CoverMaybe.Cover.MAdd(CoverMaybe.Cover.MAdd(a, b), c)
   == CoverMaybe.Cover.MAdd(a, CoverMaybe.Cover.MAdd(b, c)) : Maybe<&2, Nat>}:
  match a:
    case None{}:
      {==}
    case Some{+x}:
      match b:
        case None{}:
          {==}
        case Some{+y}:
          match c:
            case None{}:
              {==}
            case Some{+z}:
              Equal.cong(Nat, Maybe<&2, Nat>, n => Some{n},
                Nat.add(Nat.add(x, y), z), Nat.add(x, Nat.add(y, z)),
                NatProof.NatPrf.add_assoc(x, y, z))

# `Some 0` is the right identity of the `Maybe` sum.
def OV.madd_zero(a: Maybe<&2, Nat>) ->
  {CoverMaybe.Cover.MAdd(a, Some{0n}) == a : Maybe<&2, Nat>}:
  match a:
    case None{}:
      {==}
    case Some{+x}:
      Equal.cong(Nat, Maybe<&2, Nat>, n => Some{n}, Nat.add(x, 0n), x,
        NatProof.NatPrf.add_zero(x))

# A finite cost has a `Some` value.
def OV.mv_fin(+inf: Nat, +cost: Nat,
    e: {Nat.is_ge(cost, inf) == False{} : Bool}) ->
  {OV.mv(inf, cost) == Some{cost} : Maybe<&2, Nat>}:
  Equal.cong(Bool, Maybe<&2, Nat>,
    x => Feedback.Bool.case(Maybe<&2, Nat>, x, None{}, Some{cost}),
    Nat.is_ge(cost, inf), False{}, e)

# Two finite numbers make a saturated sum that is their plain sum.
def OV.sat_fin(+inf: Nat, +a: Nat, +b: Nat,
    ea: {Nat.is_ge(a, inf) == False{} : Bool},
    eb: {Nat.is_ge(b, inf) == False{} : Bool}) ->
  {SolveRef.sat_add(inf, a, b) == Nat.add(a, b) : Nat}:
  +e1 : {SolveRef.sat_add(inf, a, b)
         == Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b)) : Nat} =
    Equal.cong(Bool, Nat,
      x => Feedback.Bool.case(Nat, x, inf,
        Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b))),
      Nat.is_ge(a, inf), False{}, ea)
  +e2 : {Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b))
         == Nat.add(a, b) : Nat} =
    Equal.cong(Bool, Nat, x => Feedback.Bool.case(Nat, x, inf, Nat.add(a, b)),
      Nat.is_ge(b, inf), False{}, eb)
  Equal.trans(Nat, SolveRef.sat_add(inf, a, b),
    Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b)),
    Nat.add(a, b), e1, e2)

# A saturated sum with a finite left side is finite when the right side is.
def OV.sat_inf_r(+inf: Nat, +a: Nat, +b: Nat,
    ea: {Nat.is_ge(a, inf) == False{} : Bool},
    eb: {Nat.is_ge(b, inf) == True{} : Bool}) ->
  {SolveRef.sat_add(inf, a, b) == inf : Nat}:
  +e1 : {SolveRef.sat_add(inf, a, b)
         == Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b)) : Nat} =
    Equal.cong(Bool, Nat,
      x => Feedback.Bool.case(Nat, x, inf,
        Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b))),
      Nat.is_ge(a, inf), False{}, ea)
  +e2 : {Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b)) == inf : Nat} =
    Equal.cong(Bool, Nat, x => Feedback.Bool.case(Nat, x, inf, Nat.add(a, b)),
      Nat.is_ge(b, inf), True{}, eb)
  Equal.trans(Nat, SolveRef.sat_add(inf, a, b),
    Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b)), inf, e1, e2)

# A saturated sum with an infinite left side is infinity.
def OV.sat_inf_l(+inf: Nat, +a: Nat, +b: Nat,
    ea: {Nat.is_ge(a, inf) == True{} : Bool}) ->
  {SolveRef.sat_add(inf, a, b) == inf : Nat}:
  Equal.cong(Bool, Nat,
    x => Feedback.Bool.case(Nat, x, inf,
      Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b))),
    Nat.is_ge(a, inf), True{}, ea)

# Both sides finite, and their sum too: the values add.
def OV.mv_add_fin(+inf: Nat, +a: Nat, +b: Nat,
    +ea: {Nat.is_ge(a, inf) == False{} : Bool},
    +eb: {Nat.is_ge(b, inf) == False{} : Bool},
    +es: {Nat.is_ge(Nat.add(a, b), inf) == False{} : Bool}) ->
  {OV.mv(inf, SolveRef.sat_add(inf, a, b))
   == CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b)) : Maybe<&2, Nat>}:
  +l1 : {OV.mv(inf, SolveRef.sat_add(inf, a, b)) == OV.mv(inf, Nat.add(a, b))
         : Maybe<&2, Nat>} =
    Equal.cong(Nat, Maybe<&2, Nat>, x => OV.mv(inf, x),
      SolveRef.sat_add(inf, a, b), Nat.add(a, b), OV.sat_fin(inf, a, b, ea, eb))
  +l2 : {OV.mv(inf, Nat.add(a, b)) == Some{Nat.add(a, b)} : Maybe<&2, Nat>} =
    OV.mv_fin(inf, Nat.add(a, b), es)
  +r1a : {CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b))
          == CoverMaybe.Cover.MAdd(Some{a}, OV.mv(inf, b)) : Maybe<&2, Nat>} =
    Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>,
      x => CoverMaybe.Cover.MAdd(x, OV.mv(inf, b)),
      OV.mv(inf, a), Some{a}, OV.mv_fin(inf, a, ea))
  +r1b : {CoverMaybe.Cover.MAdd(Some{a}, OV.mv(inf, b))
          == CoverMaybe.Cover.MAdd(Some{a}, Some{b}) : Maybe<&2, Nat>} =
    Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>,
      x => CoverMaybe.Cover.MAdd(Some{a}, x),
      OV.mv(inf, b), Some{b}, OV.mv_fin(inf, b, eb))
  +r2 : {CoverMaybe.Cover.MAdd(Some{a}, Some{b}) == Some{Nat.add(a, b)}
         : Maybe<&2, Nat>} = {==}
  +r1 : {CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b))
         == Some{Nat.add(a, b)} : Maybe<&2, Nat>} =
    Equal.trans(Maybe<&2, Nat>,
      CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b)),
      CoverMaybe.Cover.MAdd(Some{a}, OV.mv(inf, b)),
      Some{Nat.add(a, b)}, r1a,
      Equal.trans(Maybe<&2, Nat>,
        CoverMaybe.Cover.MAdd(Some{a}, OV.mv(inf, b)),
        CoverMaybe.Cover.MAdd(Some{a}, Some{b}), Some{Nat.add(a, b)}, r1b, r2))
  Equal.trans(Maybe<&2, Nat>,
    OV.mv(inf, SolveRef.sat_add(inf, a, b)),
    Some{Nat.add(a, b)},
    CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b)),
    Equal.trans(Maybe<&2, Nat>,
      OV.mv(inf, SolveRef.sat_add(inf, a, b)),
      OV.mv(inf, Nat.add(a, b)), Some{Nat.add(a, b)}, l1, l2),
    Equal.sym(Maybe<&2, Nat>,
      CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b)),
      Some{Nat.add(a, b)},
      Equal.trans(Maybe<&2, Nat>,
        CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b)),
        CoverMaybe.Cover.MAdd(Some{a}, Some{b}), Some{Nat.add(a, b)},
        r1, r2)))

# An infinite left side saturates to infinity.
def OV.mv_add_inf_l(+inf: Nat, +a: Nat, +b: Nat,
    +ea: {Nat.is_ge(a, inf) == True{} : Bool}) ->
  {OV.mv(inf, SolveRef.sat_add(inf, a, b))
   == CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b)) : Maybe<&2, Nat>}:
  +e1 : {OV.mv(inf, SolveRef.sat_add(inf, a, b)) == OV.mv(inf, inf) : Maybe<&2, Nat>} =
    Equal.cong(Nat, Maybe<&2, Nat>, x => OV.mv(inf, x),
      SolveRef.sat_add(inf, a, b), inf, OV.sat_inf_l(inf, a, b, ea))
  +e2 : {OV.mv(inf, inf) == None{} : Maybe<&2, Nat>} = OV.mv_of_ge(inf, inf, Nat.ge_refl(inf))
  +e3 : {OV.mv(inf, a) == None{} : Maybe<&2, Nat>} = OV.mv_of_ge(inf, a, ea)
  +e4 : {CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b)) == None{} : Maybe<&2, Nat>} =
    Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>,
      x => CoverMaybe.Cover.MAdd(x, OV.mv(inf, b)), OV.mv(inf, a), None{}, e3)
  Equal.trans(Maybe<&2, Nat>,
    OV.mv(inf, SolveRef.sat_add(inf, a, b)), None{},
    CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b)),
    Equal.trans(Maybe<&2, Nat>, OV.mv(inf, SolveRef.sat_add(inf, a, b)),
      OV.mv(inf, inf), None{}, e1, e2),
    Equal.sym(Maybe<&2, Nat>,
      CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b)), None{}, e4))

# A finite left side and an infinite right side saturate to infinity.
def OV.mv_add_inf_r(+inf: Nat, +a: Nat, +b: Nat,
    +ea: {Nat.is_ge(a, inf) == False{} : Bool},
    +eb: {Nat.is_ge(b, inf) == True{} : Bool}) ->
  {OV.mv(inf, SolveRef.sat_add(inf, a, b))
   == CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b)) : Maybe<&2, Nat>}:
  +e1 : {OV.mv(inf, SolveRef.sat_add(inf, a, b)) == OV.mv(inf, inf) : Maybe<&2, Nat>} =
    Equal.cong(Nat, Maybe<&2, Nat>, x => OV.mv(inf, x),
      SolveRef.sat_add(inf, a, b), inf, OV.sat_inf_r(inf, a, b, ea, eb))
  +e2 : {OV.mv(inf, inf) == None{} : Maybe<&2, Nat>} = OV.mv_of_ge(inf, inf, Nat.ge_refl(inf))
  +e3 : {OV.mv(inf, b) == None{} : Maybe<&2, Nat>} = OV.mv_of_ge(inf, b, eb)
  +e4a : {CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b))
          == CoverMaybe.Cover.MAdd(Some{a}, OV.mv(inf, b)) : Maybe<&2, Nat>} =
    Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>,
      x => CoverMaybe.Cover.MAdd(x, OV.mv(inf, b)),
      OV.mv(inf, a), Some{a}, OV.mv_fin(inf, a, ea))
  +e4b : {CoverMaybe.Cover.MAdd(Some{a}, OV.mv(inf, b))
          == CoverMaybe.Cover.MAdd(Some{a}, None{}) : Maybe<&2, Nat>} =
    Equal.cong(Maybe<&2, Nat>, Maybe<&2, Nat>,
      x => CoverMaybe.Cover.MAdd(Some{a}, x), OV.mv(inf, b), None{}, e3)
  +e4 : {CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b)) == None{} : Maybe<&2, Nat>} =
    Equal.trans(Maybe<&2, Nat>,
      CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b)),
      CoverMaybe.Cover.MAdd(Some{a}, OV.mv(inf, b)), None{}, e4a,
      Equal.trans(Maybe<&2, Nat>,
        CoverMaybe.Cover.MAdd(Some{a}, OV.mv(inf, b)),
        CoverMaybe.Cover.MAdd(Some{a}, None{}), None{}, e4b, {==}))
  Equal.trans(Maybe<&2, Nat>,
    OV.mv(inf, SolveRef.sat_add(inf, a, b)), None{},
    CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b)),
    Equal.trans(Maybe<&2, Nat>, OV.mv(inf, SolveRef.sat_add(inf, a, b)),
      OV.mv(inf, inf), None{}, e1, e2),
    Equal.sym(Maybe<&2, Nat>,
      CoverMaybe.Cover.MAdd(OV.mv(inf, a), OV.mv(inf, b)), None{}, e4))

# The value of a result, unfolded at its cost.
def OV.val_of(+inf: Nat, best: SolveRef.Best,
    k: Nat -> Maybe<&2, Nat> -> Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match best:
    case SolveRef.Best{tree, +cost}:
      k(cost, OV.mv(inf, cost))

# The value of a result is the value of its cost.
def OV.val_eq(+inf: Nat, best: SolveRef.Best) ->
  {OV.val(inf, best) == OV.mv(inf, Eval.Eval.cost_of(best)) : Maybe<&2, Nat>}:
  match best:
    case SolveRef.Best{tree, +cost}:
      {==}

# A `Some` value means a finite cost.
def OV.val_some_lt_go(+inf: Nat, +cost: Nat, b: Bool,
    +eb: {b == Nat.is_ge(cost, inf) : Bool}, +n: Nat,
    e: {Feedback.Bool.case(Maybe<&2, Nat>, b, None{}, Some{cost}) == Some{n}
        : Maybe<&2, Nat>}) ->
  {Nat.is_lt(cost, inf) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({Nat.is_lt(cost, inf) == True{} : Bool},
        Cover.Cover.some_ne_none(n,
          Equal.sym(Maybe<&2, Nat>, None{}, Some{n}, e)))
    case False{}:
      Sat.SB.lt_of_ge_false(cost, inf,
        Equal.sym(Bool, False{}, Nat.is_ge(cost, inf), eb))

def OV.val_some_lt(+inf: Nat, best: SolveRef.Best, +n: Nat,
    e: {OV.val(inf, best) == Some{n} : Maybe<&2, Nat>}) ->
  {Nat.is_lt(Eval.Eval.cost_of(best), inf) == True{} : Bool}:
  match best:
    case SolveRef.Best{tree, +cost}:
      OV.val_some_lt_go(inf, cost, Nat.is_ge(cost, inf), {==}, n, e)
