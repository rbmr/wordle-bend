# The base case of the verified solver: no candidates left.
#
# With an empty candidate list, any guess in the list makes a valid tree of
# cost zero, and if the guess list is empty no valid tree exists. This is the
# `fuel = 0` step of `best`, written out with its proof so that the outcome
# type is inhabited in both of its alternatives.
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ./spec.bend as Spec
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof

# Membership in the guess list becomes a reflexivity computation.
def BaseCase.word_in_cons(+g: +List<Nat>, +rest: +List<+List<Nat>>) ->
  Tree.WordIn(g, g <> rest):
  %Equal.sym(Bool, Feedback.word_eq(g, g), True{}, FbProof.FbPrf.word_eq_refl(g)) : {
    Feedback.Bool.case(Bool, _, True{}, Tree.member_word(g, rest)) == True{} : Bool}
  {==}

# No valid tree when there are no guesses.
def BaseCase.no_valid_nil_nil(T2: Tree.Tree,
    e: Tree.Valid(T2, Nil{}, Nil{})) -> Empty:
  match T2:
    case Tree.Node{g, kids}:
      (tree_in, depths) = e
      (word_in, kids_in) = tree_in
      Logic.Proof.false_ne_true(word_in)

def BaseCase.valid_nil_cons(+g0: +List<Nat>, +rest: +List<+List<Nat>>) ->
  Tree.Valid(Tree.Node{g0, Nil{}}, g0 <> rest, Nil{}):
  ((BaseCase.word_in_cons(g0, rest), Unit{}), Unit{})

def BaseCase.optimal_nil(T: Tree.Tree, G: +List<+List<Nat>>) ->
  Spec.Optimal(T, G, Nil{}):
  T2 => v => NatProof.Nat.is_le_refl(0n)

# The outcome for an empty candidate list.
def BaseCase.outcome_nil(+G: +List<+List<Nat>>) -> Spec.Outcome(G, Nil{}):
  match G:
    case Nil{}:
      Inr{T2 => e => BaseCase.no_valid_nil_nil(T2, e)}
    case Con{g0, rest}:
      Inl{Tuple{Tree.Node{g0, Nil{}},
                (BaseCase.valid_nil_cons(g0, rest),
                 BaseCase.optimal_nil(Tree.Node{g0, Nil{}}, g0 <> rest))}}

# The search at fuel zero, given that the fuel covers the candidate count. The
# only satisfiable state is an empty candidate list.
def BaseCase.best0(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +h: {Nat.is_le(List.length(&2, +List<Nat>, S), 0n) == True{} : Bool}) ->
  Spec.Outcome(G, S):
  match S:
    case Nil{}:
      BaseCase.outcome_nil(G)
    case Con{w, t}:
      Empty.absurd(Spec.Outcome(G, Con{w, t}),
        NatProof.NatPrf.zero_ne_succ(List.length(&2, +List<Nat>, t),
          Equal.sym(Nat, 1n+List.length(&2, +List<Nat>, t), 0n,
            NatProof.Nat.eq_zero_of_le_zero(1n+List.length(&2, +List<Nat>, t), h))))
