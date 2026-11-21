# The bound-pruned solver.
#
# This module is a drop-in replacement for the reference search in
# `src/solve_ref.bend`: `solve_fast` returns the same tree as `solve`, but it
# skips a guess whose cost cannot be strictly below the best cost found so far.
#
# For a guess `g` over a candidate list `S`, the reference builds one child per
# class of the feedback partition and the node costs one per candidate plus the
# children's costs. Every candidate costs at least one, so any tree rooted at
# `g` costs at least
#
#   bound(S, g) = |S| + sum over classes of |class|
#
# The search evaluates the guesses in order and keeps the best cost. `better`
# only replaces on a strictly lower cost, so ties keep the earlier guess. A
# guess whose bound is at least the best cost so far therefore cannot change
# the result and is skipped.
#
# The schedule has the reference's shape: one `Begin` per usable guess,
# followed by that guess's class items and `End`. A skipped guess still walks
# its items, but `skip` is true, so no class is searched and `best` is left
# unchanged. Skipping therefore costs a few steps instead of a subtree search.
import Base
import ./feedback.bend as Feedback
import ./tree.bend as Tree
import ./groups.bend as Groups
import ./solve_ref.bend as SolveRef

# `Begin` carries the guess and its lower bound. `ClassItem`, `Add` and `End`
# are the reference's items.
type Item is Data:
  Begin{guess: +List<Nat>, lb: Nat}
  ClassItem{fb: +List<Feedback.Color>, words: +List<+List<Nat>>}
  Add{fb: +List<Feedback.Color>}
  End{}

# The number of candidates in a class list.
def class_words(+groups: +List<Groups.Group>) -> Nat:
  match groups:
    case Nil{}:
      0n
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          Nat.add(Groups.len_words(ws), class_words(rest))

# A lower bound on the cost of any tree rooted at a guess with these classes:
# every candidate costs at least one, and the node itself costs one per
# candidate.
def lower_bound(+n: Nat, +groups: +List<Groups.Group>) -> Nat:
  Nat.add(n, class_words(groups))

def best_cost(+best: SolveRef.Best) -> Nat:
  match best:
    case SolveRef.Best{tree, cost}:
      cost

# The guess is skipped exactly when the best cost so far is at most its bound.
def skippable(+best: SolveRef.Best, +lb: Nat) -> Bool:
  Nat.is_le(best_cost(best), lb)

def dummy_inf(+inf: Nat) -> SolveRef.Best:
  SolveRef.Best{Tree.Node{Nil{}, Nil{}}, inf}

def dummy_zero() -> SolveRef.Best:
  SolveRef.Best{Tree.Node{Nil{}, Nil{}}, 0n}

# The class items of one guess, each followed by the `Add` that consumes it.
def group_items(+groups: +List<Groups.Group>) -> +List<Item>:
  match groups:
    case Nil{}:
      Nil{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+f, +ws}:
          ClassItem{f, ws} <> (Add{f} <> group_items(rest))

# The block of one guess, followed by the rest of the schedule. The usability
# decision is a parameter so the recursive call builds the rest exactly once:
# both branches of a strict `case` would build it twice.
def schedule_guess(+g: +List<Nat>, +groups: +List<Groups.Group>, +n: Nat,
                   +rest: +List<Item>, usable: Bool) -> +List<Item>:
  match usable:
    case True{}:
      Begin{g, lower_bound(n, groups)}
      <> List.append(&2, Item, group_items(groups), End{} <> rest)
    case False{}:
      rest

def schedule_go(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +n: Nat) -> +List<Item>:
  match G:
    case Nil{}:
      Nil{}
    case Con{+g, +rest}:
      +groups = Groups.groups_build(g, S, Nil{})
      schedule_guess(g, groups, n, schedule_go(rest, S, n),
                     Groups.groups_smaller(S, groups))

# The schedule for a guess list: one block per usable guess, in G order.
def schedule(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>) -> +List<Item>:
  schedule_go(G, S, Groups.len_words(S))

# One step of the pruned search. The arguments and the fuel are the reference's;
# `skip` says whether the current block is skipped. A skipped block searches no
# class and leaves `best` unchanged.
def step(+fuel: Nat, +cs: +List<Item>, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
         +inf: Nat, +g: +List<Nat>, +kids: +List<Tree.Child>, sum: Nat,
         +best: SolveRef.Best, +pending: SolveRef.Best, skip: Bool) -> SolveRef.Best:
  match fuel:
    case 0n:
      match cs:
        case Nil{}:
          best
        case Con{item, rest}:
          match item:
            case Begin{g2, lb}:
              step(0n, rest, G, S, inf, g2, Nil{}, 0n, best, pending, False{})
            case ClassItem{fb, words}:
              dummy_inf(inf)
            case Add{fb}:
              match pending:
                case SolveRef.Best{tree, cost}:
                  step(0n, rest, G, S, inf, g,
                       Tree.Child{fb, tree} <> kids,
                       SolveRef.sat_add(inf, sum, cost), best, dummy_zero(), skip)
            case End{}:
              step(0n, rest, G, S, inf, Nil{}, Nil{}, 0n,
                   SolveRef.finish_guess(inf, g, kids, sum, Groups.len_words(S), best),
                   dummy_zero(), False{})
    case 1n+p:
      match cs:
        case Nil{}:
          best
        case Con{item, rest}:
          match item:
            case Begin{g2, lb}:
              step(fuel, rest, G, S, inf, g2, Nil{}, 0n, best, dummy_zero(),
                   skippable(best, lb))
            case ClassItem{fb, words}:
              match skip:
                case True{}:
                  step(fuel, rest, G, S, inf, g, kids, sum, best,
                       dummy_zero(), skip)
                case False{}:
                  step(fuel, rest, G, S, inf, g, kids, sum, best,
                       step(p, schedule(G, words), G, words, inf,
                            Nil{}, Nil{}, 0n, dummy_inf(inf), dummy_zero(), False{}),
                       skip)
            case Add{fb}:
              match pending:
                case SolveRef.Best{tree, cost}:
                  step(fuel, rest, G, S, inf, g,
                       Tree.Child{fb, tree} <> kids,
                       SolveRef.sat_add(inf, sum, cost), best,
                       dummy_zero(), skip)
            case End{}:
              match skip:
                case True{}:
                  step(fuel, rest, G, S, inf, Nil{}, Nil{}, 0n,
                       best, dummy_zero(), False{})
                case False{}:
                  step(fuel, rest, G, S, inf, Nil{}, Nil{}, 0n,
                       SolveRef.finish_guess(inf, g, kids, sum,
                         Groups.len_words(S), best),
                       dummy_zero(), False{})

# The pruned search on a guess list and candidate list.
def solve_fast(+guesses: +List<+List<Nat>>,
               +candidates: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  +n = Groups.len_words(candidates)
  +inf = SolveRef.inf_of(n)
  SolveRef.best_to_maybe(inf,
    step(n, schedule(guesses, candidates), guesses, candidates, inf,
         Nil{}, Nil{}, 0n, dummy_inf(inf), dummy_zero(), False{}))
