# Feedback equality is symmetric.
#
# `tree.lookup` tests `feedback_eq (fb) (child feedback)` while `tree.depth`
# tests `feedback_eq (child feedback) (fb)`. Proving the two scans agree needs
# symmetry, proved here from the component-wise symmetry of colour equality.
import Base
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof

# Decompose `List.all.if`.
def FbPrf.all_if_true_l(rest: Unit -> Bool, hit: Bool,
    e: {List.all.if(rest, hit) == True{} : Bool}) -> {hit == True{} : Bool}:
  match hit:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Logic.Proof.false_ne_true(e))

def FbPrf.all_if_true_r(rest: Unit -> Bool, hit: Bool,
    e: {List.all.if(rest, hit) == True{} : Bool}) ->
  {rest(Unit{}) == True{} : Bool}:
  match hit:
    case True{}:
      e
    case False{}:
      Empty.absurd({rest(Unit{}) == True{} : Bool}, Logic.Proof.false_ne_true(e))

def FbPrf.all_if_intro(rest: Unit -> Bool, hit: Bool,
    h: {hit == True{} : Bool}, t: {rest(Unit{}) == True{} : Bool}) ->
  {List.all.if(rest, hit) == True{} : Bool}:
  match hit:
    case True{}:
      t
    case False{}:
      Empty.absurd({List.all.if(rest, False{}) == True{} : Bool},
                   Logic.Proof.false_ne_true(h))

# Colour equality is symmetric.
def FbPrf.color_eq_sym(a: Feedback.Color, b: Feedback.Color,
    e: {Feedback.Color.eq(a, b) == True{} : Bool}) ->
  {Feedback.Color.eq(b, a) == True{} : Bool}:
  match a b:
    case Feedback.Gray{} Feedback.Gray{}:
      {==}
    case Feedback.Gray{} Feedback.Yellow{}:
      Empty.absurd({Feedback.Color.eq(Feedback.Yellow{}, Feedback.Gray{}) == True{} : Bool},
                   Logic.Proof.false_ne_true(e))
    case Feedback.Gray{} Feedback.Green{}:
      Empty.absurd({Feedback.Color.eq(Feedback.Green{}, Feedback.Gray{}) == True{} : Bool},
                   Logic.Proof.false_ne_true(e))
    case Feedback.Yellow{} Feedback.Gray{}:
      Empty.absurd({Feedback.Color.eq(Feedback.Gray{}, Feedback.Yellow{}) == True{} : Bool},
                   Logic.Proof.false_ne_true(e))
    case Feedback.Yellow{} Feedback.Yellow{}:
      {==}
    case Feedback.Yellow{} Feedback.Green{}:
      Empty.absurd({Feedback.Color.eq(Feedback.Green{}, Feedback.Yellow{}) == True{} : Bool},
                   Logic.Proof.false_ne_true(e))
    case Feedback.Green{} Feedback.Gray{}:
      Empty.absurd({Feedback.Color.eq(Feedback.Gray{}, Feedback.Green{}) == True{} : Bool},
                   Logic.Proof.false_ne_true(e))
    case Feedback.Green{} Feedback.Yellow{}:
      Empty.absurd({Feedback.Color.eq(Feedback.Yellow{}, Feedback.Green{}) == True{} : Bool},
                   Logic.Proof.false_ne_true(e))
    case Feedback.Green{} Feedback.Green{}:
      {==}

def FbPrf.all_pairs(+a: +List<Feedback.Color>, +b: +List<Feedback.Color>) -> Bool:
  List.all(&1, Feedback.Color & Feedback.Color, Feedback.pair_color_eq,
           List.zip(&2, Feedback.Color, &2, Feedback.Color, a, b))

def FbPrf.all_pairs_sym(+a: +List<Feedback.Color>, +b: +List<Feedback.Color>,
    +e: {FbPrf.all_pairs(a, b) == True{} : Bool}) ->
  {FbPrf.all_pairs(b, a) == True{} : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b0, +bt}:
      {==}
    case Con{+a0, +at} Nil{}:
      {==}
    case Con{+a0, +at} Con{+b0, +bt}:
      +eq_ab : {Feedback.Color.eq(a0, b0) == True{} : Bool} =
        FbPrf.all_if_true_l(u => FbPrf.all_pairs(at, bt), Feedback.Color.eq(a0, b0), e)
      +tail_ab : {FbPrf.all_pairs(at, bt) == True{} : Bool} =
        FbPrf.all_if_true_r(u => FbPrf.all_pairs(at, bt), Feedback.Color.eq(a0, b0), e)
      +eq_ba : {Feedback.Color.eq(b0, a0) == True{} : Bool} =
        FbPrf.color_eq_sym(a0, b0, eq_ab)
      +tail_ba : {FbPrf.all_pairs(bt, at) == True{} : Bool} =
        FbPrf.all_pairs_sym(at, bt, tail_ab)
      FbPrf.all_if_intro(u => FbPrf.all_pairs(bt, at), Feedback.Color.eq(b0, a0),
                         eq_ba, tail_ba)

def FeedbackProof.feedback_eq_sym(+a: +List<Feedback.Color>, +b: +List<Feedback.Color>,
    +e: {Feedback.feedback_eq(a, b) == True{} : Bool}) ->
  {Feedback.feedback_eq(b, a) == True{} : Bool}:
  +len_ab : {Nat.is_eq(List.length(&2, Feedback.Color, a), List.length(&2, Feedback.Color, b)) == True{} : Bool} =
    Logic.Proof.and_true_l(
      Nat.is_eq(List.length(&2, Feedback.Color, a), List.length(&2, Feedback.Color, b)),
      FbPrf.all_pairs(a, b), e)
  +len_ba : {Nat.is_eq(List.length(&2, Feedback.Color, b), List.length(&2, Feedback.Color, a)) == True{} : Bool} =
    NatProof.NatPrf.is_eq_sym(List.length(&2, Feedback.Color, a),
                              List.length(&2, Feedback.Color, b), len_ab)
  +all_ba : {FbPrf.all_pairs(b, a) == True{} : Bool} =
    FbPrf.all_pairs_sym(a, b,
      Logic.Proof.and_true_r(
        Nat.is_eq(List.length(&2, Feedback.Color, a), List.length(&2, Feedback.Color, b)),
        FbPrf.all_pairs(a, b), e))
  Logic.Proof.and_intro(
    Nat.is_eq(List.length(&2, Feedback.Color, b), List.length(&2, Feedback.Color, a)),
    FbPrf.all_pairs(b, a), len_ba, all_ba)

# A boolean that is not true is false.
def BoolProof.false_of_not_true(b: Bool, p: {b == True{} : Bool} -> Empty) ->
  {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, p({==}))
    case False{}:
      {==}

# The two orientations of `feedback_eq` are the same boolean, which is what
# lets `lookup` and `depth` scan a child list in lockstep.
def FbPrf.feedback_eq_sym_bool_go(+a: +List<Feedback.Color>, +b: +List<Feedback.Color>,
    x: Bool, y: Bool,
    ex: {x == Feedback.feedback_eq(a, b) : Bool},
    ey: {y == Feedback.feedback_eq(b, a) : Bool}) ->
  {x == y : Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      +p : {Feedback.feedback_eq(a, b) == True{} : Bool} =
        Equal.sym(Bool, True{}, Feedback.feedback_eq(a, b), ex)
      +q : {Feedback.feedback_eq(b, a) == True{} : Bool} =
        FeedbackProof.feedback_eq_sym(a, b, p)
      +f : {Feedback.feedback_eq(b, a) == False{} : Bool} =
        Equal.sym(Bool, False{}, Feedback.feedback_eq(b, a), ey)
      Empty.absurd({True{} == False{} : Bool},
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, Feedback.feedback_eq(b, a), False{},
                      Equal.sym(Bool, Feedback.feedback_eq(b, a), True{}, q), f)))
    case False{} True{}:
      +p : {Feedback.feedback_eq(a, b) == False{} : Bool} =
        Equal.sym(Bool, False{}, Feedback.feedback_eq(a, b), ex)
      +q : {Feedback.feedback_eq(b, a) == True{} : Bool} =
        Equal.sym(Bool, True{}, Feedback.feedback_eq(b, a), ey)
      +r : {Feedback.feedback_eq(a, b) == True{} : Bool} =
        FeedbackProof.feedback_eq_sym(b, a, q)
      Empty.absurd({False{} == True{} : Bool},
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, Feedback.feedback_eq(a, b), False{},
                      Equal.sym(Bool, Feedback.feedback_eq(a, b), True{}, r), p)))
    case False{} False{}:
      {==}

def FeedbackProof.feedback_eq_sym_bool(+a: +List<Feedback.Color>, +b: +List<Feedback.Color>) ->
  {Feedback.feedback_eq(a, b) == Feedback.feedback_eq(b, a) : Bool}:
  FbPrf.feedback_eq_sym_bool_go(a, b, Feedback.feedback_eq(a, b),
                                Feedback.feedback_eq(b, a), {==}, {==})
