# The exact solver.
#
# This is the entry point the laws in `LAWS.bend` talk about. It is the `k = 1`
# instance of the chunked solver in `src/solve_k.bend`, which is the
# bound-pruned search with its root guess list splittable into chunks; `k = 1`
# is that search with the root loop left whole, so this is exactly the
# bound-pruned solver in `src/solve_fast.bend`. `src/solve_ref.bend` stays in
# the tree as the exhaustive reference specification.
import Base
import ./feedback.bend as Feedback
import ./tree.bend as Tree
import ./groups.bend as Groups
import ./solve_k.bend as SolveK

def solve(+guesses: +List<+List<Nat>>, +candidates: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  SolveK.solve_k(guesses, candidates, 1n)
