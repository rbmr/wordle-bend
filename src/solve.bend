# The exact solver.
#
# This is the entry point the laws talk about. It delegates to the reference
# search until the verified search replaces it.
import Base
import ./feedback.bend as Feedback
import ./tree.bend as Tree
import ./groups.bend as Groups
import ./solve_ref.bend as SolveRef

def solve(+guesses: +List<+List<Nat>>, +candidates: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  SolveRef.solve(guesses, candidates)
