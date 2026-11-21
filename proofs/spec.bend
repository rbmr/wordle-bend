# The proof-carrying result of the verified solver.
import Base
import ../src/tree.bend as Tree
import ./eval.bend as Eval
import ./groupsdistinct.bend as GroupsDistinct
import ./children.bend as Children

# Optimality: no valid tree for the same input costs less.
def Optimal(T: Tree.Tree, G: +List<+List<Nat>>, S: +List<+List<Nat>>) -> Type:
  @T2: Tree.Tree -> Tree.Valid(T2, G, S) ->
    {Nat.is_le(Tree.cost(T, S), Tree.cost(T2, S)) == True{} : Bool}

# Inhabited only when no valid tree exists for the input.
def NoValid(G: +List<+List<Nat>>, S: +List<+List<Nat>>) -> Type:
  @T2: Tree.Tree -> Tree.Valid(T2, G, S) -> Empty

# Either a tree with its validity and optimality proofs, or a proof that no
# valid tree exists.
def Outcome(G: +List<+List<Nat>>, S: +List<+List<Nat>>) -> Type:
  Sigma<&1, &1, Tree.Tree, T => Tree.Valid(T, G, S) & Optimal(T, G, S)>
  | NoValid(G, S)
