# The exact solver.
#
# This is the entry point the laws in `LAWS.bend` talk about. It is the `k = 1`
# instance of the chunked solver in `src/solve_k.bend`, which runs greedy
# upper-bound seeding and Pass-1 root bucket sorting (`src/greedy.bend`) before
# evaluating the bound-pruned search (`src/solve_fast.bend`). `src/solve_ref.bend`
# stays in the tree as the exhaustive reference specification.
import Base
import ./feedback.bend as Feedback
import ./tree.bend as Tree
import ./groups.bend as Groups
import ./solve_k.bend as SolveK

def solve(+guesses: +List<+List<Nat>>, +candidates: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  SolveK.solve_k(guesses, candidates, 1n)
