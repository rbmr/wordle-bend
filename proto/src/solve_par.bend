# Parallel root evaluation of the exact solver.
#
# Every guess in the guess list is evaluated independently of the accumulator:
# the reference `better` only compares a finished guess with the best result so
# far. So the root guess list can be split into halves, each half evaluated by
# the reference machine in parallel, and the per-guess results folded with
# `better` in the original order. The fold keeps the first minimal result, which
# is exactly the reference's tie-breaking, so the returned tree is the same tree
# the reference returns.
#
# The per-guess evaluation is the reference machine itself (`step` over that
# guess's schedule), so nothing inside a guess changes. Only the root guess
# list is split, down to a small grain, and the split is driven by a fuel that
# decreases so the recursion is structural.
import Base
import ./feedback.bend as Feedback
import ./tree.bend as Tree
import ./groups.bend as Groups
import ./solve_ref.bend as SolveRef

# The neutral accumulator of the reference search: no tree, at infinity.
def init_best(+inf: Nat) -> SolveRef.Best:
  SolveRef.Best{Tree.Node{Nil{}, Nil{}}, inf}

def zero_best() -> SolveRef.Best:
  SolveRef.Best{Tree.Node{Nil{}, Nil{}}, 0n}

# The schedule of one guess: its class items, or nothing when the guess is not
# usable. This is the same choice `schedule_guess` makes, with the groups and
# the boolean passed in.
def guess_schedule(+g: +List<Nat>, +groups: +List<Groups.Group>,
                   b: Bool) -> +List<SolveRef.Item>:
  Feedback.Bool.case(+List<SolveRef.Item>, b,
                     SolveRef.guess_items(g, groups), Nil{})

# The reference evaluation of one guess, starting from the neutral accumulator.
# This is the unit of parallel work.
def one(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +inf: Nat,
        +g: +List<Nat>, +groups: +List<Groups.Group>,
        b: Bool) -> SolveRef.Best:
  SolveRef.step(fuel, List.append(&2, SolveRef.Item, guess_schedule(g, groups, b),
                                  Nil{}),
                G, S, inf, Nil{}, Nil{}, 0n, init_best(inf), zero_best())

# The results of the guesses in order, evaluated one after the other.
def ones(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +inf: Nat,
         +gs: +List<+List<Nat>>) -> +List<SolveRef.Best>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{+g, +rest}:
      one(fuel, G, S, inf, g, Groups.groups_build(g, S, Nil{}),
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})))
      <> ones(fuel, G, S, inf, rest)

# Fold the per-guess results with the reference `better`: a strictly cheaper
# result replaces the accumulator, so the first minimal result wins.
def fold_results(+rs: +List<SolveRef.Best>, best: SolveRef.Best) -> SolveRef.Best:
  match rs:
    case Nil{}:
      best
    case Con{+r, +rest}:
      match r:
        case SolveRef.Best{+tree, +cost}:
          fold_results(rest, SolveRef.better(cost, tree, best))

# A leaf of the split evaluates at most this many guesses in sequence.
def grain() -> Nat:
  1n

# The per-guess results of one chunk, splitting the list in half while it is
# longer than the grain. `d` is a structural fuel for the recursion (it only
# bounds the depth, it says nothing about the result); `rem` is the list length
# above the grain, and decides whether this chunk is a leaf.
def par_results(+d: Nat, rem: Nat, +fuel: Nat, +G: +List<+List<Nat>>,
                +S: +List<+List<Nat>>, +inf: Nat,
                +gs: +List<+List<Nat>>) -> +List<SolveRef.Best>:
  match d:
    case 0n:
      ones(fuel, G, S, inf, gs)
    case 1n+p:
      match rem:
        case 0n:
          ones(fuel, G, S, inf, gs)
        case 1n+q:
          +len = Groups.len_words(gs)
          +half = Nat.div(len, 2n)
          +left = List.take(&2, +List<Nat>, gs, half)
          +right = List.drop(&2, +List<Nat>, gs, half)
          ra rb = par_results(p, Nat.sub(Groups.len_words(left), grain()), fuel, G, S, inf, left) par_results(p, Nat.sub(Groups.len_words(right), grain()), fuel, G, S, inf, right)
          List.append(&2, SolveRef.Best, ra, rb)

# The parallel solver. An empty candidate list has no class search to split and
# the reference result is immediate, so that case stays with the reference.
def solve_n(+n: Nat, +guesses: +List<+List<Nat>>,
            +candidates: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  match n:
    case 0n:
      SolveRef.solve(guesses, candidates)
    case 1n+p:
      +inf = SolveRef.inf_of(n)
      +depth = Groups.len_words(guesses)
      +above = Nat.sub(depth, grain())
      +results = par_results(depth, above, n, guesses, candidates, inf, guesses)
      SolveRef.best_to_maybe(inf, fold_results(results, init_best(inf)))

def solve(+guesses: +List<+List<Nat>>,
          +candidates: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  solve_n(Groups.len_words(candidates), guesses, candidates)
