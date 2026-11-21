# The pruned solver.
#
# This module is a drop-in replacement for the reference search in
# `src/solve_ref.bend`: `solve_fast` returns the same tree as `solve`, but it
# skips guesses that cannot improve the best cost found so far.
#
# For a guess `g` over a candidate list `S`, the candidates equal to `g` end at
# the node and every other candidate falls into one feedback class. In any
# valid tree for `S` whose root is `g`, a candidate equal to `g` has depth one
# and every other candidate has depth at least two. The root of a class can
# cover only one word value, so a class of `m` candidates in which the most
# frequent word occurs `M` times costs at least `2m - M`: at most `M` of its
# candidates can be at depth one, the rest cost at least two.
#
# The node therefore costs at least
#
#   lb(S, groups) = |S| + sum over classes of (2*|class| - M(class))
#
# for every tree rooted at `g`. The search evaluates the guesses in order and
# keeps the best cost. `better` only replaces on a strictly lower cost, so ties
# keep the earlier guess; a guess whose lower bound is at least the best cost so
# far cannot change the result and is skipped.
#
# The schedule has the reference's shape: one `Begin` per usable guess,
# followed by that guess's class items and `End`. A skipped guess still walks
# its items, but `alive` is false, so no class is searched and the accumulating
# cost stays at infinity, which leaves `best` unchanged. Skipping therefore
# costs a few steps instead of a subtree search.
import Base
import ./feedback.bend as Feedback
import ./tree.bend as Tree
import ./groups.bend as Groups
import ./solve_ref.bend as SolveRef

# `Begin` carries the guess's feedback classes and the lower bound they imply.
# `ClassItem`, `Add` and `End` are the reference's items.
type Item is Data:
  Begin{guess: +List<Nat>, groups: +List<Groups.Group>, lb: Nat}
  ClassItem{fb: +List<Feedback.Color>, words: +List<+List<Nat>>}
  Add{fb: +List<Feedback.Color>}
  End{}

# The number of occurrences of w in ws.
def count_word(+w: +List<Nat>, +ws: +List<+List<Nat>>) -> Nat:
  match ws:
    case Nil{}:
      0n
    case Con{h, t}:
      Feedback.Bool.case(Nat, Feedback.word_eq(w, h),
                         1n+count_word(w, t), count_word(w, t))

# The largest multiplicity of a word in ws. Zero for the empty list.
def max_mult(+ws: +List<+List<Nat>>) -> Nat:
  match ws:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.max(count_word(h, ws), max_mult(t))

# A lower bound on the cost of any valid tree for a class: every candidate
# costs at least one, and only candidates equal to one word value can cost one,
# so the others cost at least two.
def class_lb(+ws: +List<+List<Nat>>) -> Nat:
  Nat.sub(Nat.add(Groups.len_words(ws), Groups.len_words(ws)), max_mult(ws))

# The lower bound of a node from its candidate count and class list.
def groups_lb(+n: Nat, +groups: +List<Groups.Group>) -> Nat:
  match groups:
    case Nil{}:
      n
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          Nat.add(class_lb(ws), groups_lb(n, rest))

def best_cost(+best: SolveRef.Best) -> Nat:
  match best:
    case SolveRef.Best{tree, cost}:
      cost

# The guess is skipped exactly when the best cost so far is at most the bound.
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

def guess_items(+g: +List<Nat>, +groups: +List<Groups.Group>, +lb: Nat,
                +rest: +List<Item>) -> +List<Item>:
  Begin{g, groups, lb} <> List.append(&2, Item, group_items(groups),
                                     End{} <> rest)

# The block for one guess, or just the rest when the guess is unusable. The
# decision is a parameter so the recursive call builds the rest exactly once:
# both branches of a strict `case` would build it twice.
def schedule_guess(+g: +List<Nat>, +groups: +List<Groups.Group>, +lb: Nat,
                   +rest: +List<Item>, usable: Bool) -> +List<Item>:
  match usable:
    case True{}:
      guess_items(g, groups, lb, rest)
    case False{}:
      rest

def schedule_go(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>) -> +List<Item>:
  match G:
    case Nil{}:
      Nil{}
    case Con{+g, +rest}:
      +groups = Groups.groups_build(g, S, Nil{})
      schedule_guess(g, groups, groups_lb(Groups.len_words(S), groups),
                     schedule_go(rest, S), Groups.groups_smaller(S, groups))

# The schedule for a guess list: one block per usable guess, in G order.
def schedule(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>) -> +List<Item>:
  schedule_go(G, S)

# One step of the pruned search. The arguments and the fuel are the reference's;
# `alive` says whether the current block is being evaluated or skipped.
def step(+fuel: Nat, +cs: +List<Item>, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
         +inf: Nat, +g: +List<Nat>, +kids: +List<Tree.Child>, sum: Nat,
         +best: SolveRef.Best, +pending: SolveRef.Best, alive: Bool) -> SolveRef.Best:
  match fuel:
    case 0n:
      match cs:
        case Nil{}:
          best
        case Con{item, rest}:
          match item:
            case Begin{g2, groups, lb}:
              step(0n, rest, G, S, inf, g2, Nil{}, 0n, best, pending, alive)
            case ClassItem{fb, words}:
              dummy_inf(inf)
            case Add{fb}:
              match pending:
                case SolveRef.Best{tree, cost}:
                  step(0n, rest, G, S, inf, g, Tree.Child{fb, tree} <> kids,
                       SolveRef.sat_add(inf, sum, cost), best, dummy_zero(), alive)
            case End{}:
              step(0n, rest, G, S, inf, Nil{}, Nil{}, 0n,
                   SolveRef.finish_guess(inf, g, kids, sum, Groups.len_words(S), best),
                   dummy_zero(), True{})
    case 1n+p:
      match cs:
        case Nil{}:
          best
        case Con{item, rest}:
          match item:
            case Begin{g2, groups, lb}:
              +skip = skippable(best, lb)
              step(fuel, rest, G, S, inf,
                   Bool.pick(+List<Nat>, skip, g, g2),
                   Bool.pick(+List<Tree.Child>, skip, kids, Nil{}),
                   Bool.pick(Nat, skip, sum, 0n),
                   best,
                   Bool.pick(SolveRef.Best, skip, pending, dummy_zero()),
                   Bool.pick(Bool, skip, False{}, True{}))
            case ClassItem{fb, words}:
              match alive:
                case True{}:
                  step(fuel, rest, G, S, inf, g, kids, sum, best,
                       step(p, schedule(G, words), G, words, inf,
                            Nil{}, Nil{}, 0n, dummy_inf(inf), dummy_zero(), True{}),
                       alive)
                case False{}:
                  step(fuel, rest, G, S, inf, g, kids, sum, best,
                       dummy_inf(inf), alive)
            case Add{fb}:
              match pending:
                case SolveRef.Best{tree, cost}:
                  step(fuel, rest, G, S, inf, g, Tree.Child{fb, tree} <> kids,
                       SolveRef.sat_add(inf, sum, cost), best, dummy_zero(), alive)
            case End{}:
              step(fuel, rest, G, S, inf, Nil{}, Nil{}, 0n,
                   SolveRef.finish_guess(inf, g, kids, sum, Groups.len_words(S), best),
                   dummy_zero(), True{})

def solve_fast(+guesses: +List<+List<Nat>>,
               +candidates: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  +n = Groups.len_words(candidates)
  +inf = SolveRef.inf_of(n)
  SolveRef.best_to_maybe(inf,
    step(n, schedule(guesses, candidates), guesses, candidates, inf,
         Nil{}, Nil{}, 0n, dummy_inf(inf), dummy_zero(), True{}))
