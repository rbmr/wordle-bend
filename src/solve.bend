# The exact solver.
#
# This is the entry point the laws in `LAWS.bend` talk about. It delegates to
# the bound-pruned solver in `src/solve_fast.bend`, while `src/solve_ref.bend`
# stays in the tree as the exhaustive reference specification.
import Base
import ./feedback.bend as Feedback
import ./tree.bend as Tree
import ./groups.bend as Groups
import ./solve_fast.bend as SolveFast

def solve(+guesses: +List<+List<Nat>>, +candidates: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  SolveFast.solve(guesses, candidates)
