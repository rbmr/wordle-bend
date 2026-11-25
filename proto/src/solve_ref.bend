# The exact reference solver.
#
# For a candidate list S and a guess list G, the tree for one guess g is:
#
#   Node(g, kids)
#
# where the candidates equal to g end at that node (each contributes depth 1),
# and every other candidate is partitioned by feedback(g, .) into one child per
# distinct feedback. A guess is only usable when every such class is strictly
# smaller than S; without that the search would not terminate and the tree
# would not make progress on the class.
#
# The minimal-cost tree over all guesses wins, with ties going to the guess
# that appears first in G. The empty candidate list gives Node(g0, []) for the
# first guess g0 (cost 0), or None when G is empty.
#
# The implementation is deliberately simple rather than fast. The recursion
# is fused into one def, `step`, driven by a flat per-node schedule (a list of
# Begin / ClassItem / Add / End items). `step` shrinks the schedule on every
# step and only descends into a class's own search with `fuel - 1`. That is why
# `fuel = length(S)` suffices: every class is strictly shorter than S, so a
# child search always has at least `length(class)` fuel left.
import Base
import ./feedback.bend as Feedback
import ./tree.bend as Tree
import ./groups.bend as Groups

# The schedule for one candidate list. Begin resets the guess being evaluated,
# each ClassItem is followed by the Add that consumes its child result, and End
# finishes the guess and compares it with the best so far.
type Item is Data:
  Begin{guess: +List<Nat>}
  ClassItem{fb: +List<Feedback.Color>, words: +List<+List<Nat>>}
  Add{fb: +List<Feedback.Color>}
  End{}

# A search result: the tree and its cost. A cost of infinity means no tree.
type Best is Data:
  Best{tree: Tree.Tree, cost: Nat}

def group_items(+groups: +List<Groups.Group>) -> +List<Item>:
  match groups:
    case Nil{}:
      Nil{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+f, ws}:
          ClassItem{f, ws} <> (Add{f} <> group_items(rest))

def guess_items(+g: +List<Nat>, +groups: +List<Groups.Group>) -> +List<Item>:
  Begin{g} <> List.append(&2, Item, group_items(groups), End{} <> Nil{})

def schedule_guess(+g: +List<Nat>, +S: +List<+List<Nat>>) -> +List<Item>:
  +groups = Groups.groups_build(g, S, Nil{})
  Feedback.Bool.case(+List<Item>, Groups.groups_smaller(S, groups), guess_items(g, groups), Nil{})

# The flat schedule for every guess in G, in G order.
def mk_schedule(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>) -> +List<Item>:
  match G:
    case Nil{}:
      Nil{}
    case Con{+g, +rest}:
      List.append(&2, Item, schedule_guess(g, S), mk_schedule(rest, S))

# Saturating addition: a missing child (infinity) makes the whole guess unusable.
def sat_add(+inf: Nat, +a: Nat, +b: Nat) -> Nat:
  Feedback.Bool.case(Nat, Nat.is_ge(a, inf), inf,
                      Feedback.Bool.case(Nat, Nat.is_ge(b, inf), inf, Nat.add(a, b)))

def rev_kids(+kids: +List<Tree.Child>, +acc: +List<Tree.Child>) -> +List<Tree.Child>:
  match kids:
    case Nil{}:
      acc
    case Con{+h, +rest}:
      rev_kids(rest, h <> acc)

def better(+candCost: Nat, +candTree: Tree.Tree, best: Best) -> Best:
  match best:
    case Best{+tree, +cost}:
      Feedback.Bool.case(Best, Nat.is_lt(candCost, cost),
                          Best{candTree, candCost}, Best{tree, cost})

def finish_guess(+inf: Nat, +g: +List<Nat>, +kids: +List<Tree.Child>, +sum: Nat, +n: Nat,
                 best: Best) -> Best:
  cost : Nat = sat_add(inf, n, sum)
  tree : Tree.Tree = Tree.Node{g, rev_kids(kids, Nil{})}
  better(cost, tree, best)

def inf_of(+n: Nat) -> Nat:
  Nat.add(Nat.mul(n, n), 1n)

def best_to_maybe(inf: Nat, best: Best) -> Maybe<Tree.Tree>:
  match best:
    case Best{tree, cost}:
      Feedback.Bool.case(Maybe<Tree.Tree>, Nat.is_ge(cost, inf), None{}, Some{tree})

# One step of the search. `fuel` bounds the class depth; `cs` is the remaining
# schedule for the current candidate list S. Every call either shortens `cs`
# or descends with a smaller `fuel`.
def step(+fuel: Nat, +cs: +List<Item>, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
         +inf: Nat, +g: +List<Nat>, +kids: +List<Tree.Child>, sum: Nat,
         best: Best, pending: Best) -> Best:
  match fuel:
    case 0n:
      match cs:
        case Nil{}:
          best
        case Con{item, rest}:
          match item:
            case Begin{g2}:
              step(0n, rest, G, S, inf, g2, Nil{}, 0n, best, pending)
            case ClassItem{fb, words}:
              Best{Tree.Node{Nil{}, Nil{}}, inf}
            case Add{fb}:
              match pending:
                case Best{tree, cost}:
                  step(0n, rest, G, S, inf, g,
                       Tree.Child{fb, tree} <> kids, sat_add(inf, sum, cost),
                       best, Best{Tree.Node{Nil{}, Nil{}}, 0n})
            case End{}:
              step(0n, rest, G, S, inf, Nil{}, Nil{}, 0n,
                   finish_guess(inf, g, kids, sum, Groups.len_words(S), best),
                   Best{Tree.Node{Nil{}, Nil{}}, 0n})
    case 1n+p:
      match cs:
        case Nil{}:
          best
        case Con{item, rest}:
          match item:
            case Begin{g2}:
              step(fuel, rest, G, S, inf, g2, Nil{}, 0n, best, pending)
            case ClassItem{fb, words}:
              step(fuel, rest, G, S, inf, g, kids, sum, best,
                   step(p, mk_schedule(G, words), G, words, inf, Nil{}, Nil{}, 0n,
                        Best{Tree.Node{Nil{}, Nil{}}, inf}, Best{Tree.Node{Nil{}, Nil{}}, 0n}))
            case Add{fb}:
              match pending:
                case Best{tree, cost}:
                  step(fuel, rest, G, S, inf, g,
                       Tree.Child{fb, tree} <> kids, sat_add(inf, sum, cost),
                       best, Best{Tree.Node{Nil{}, Nil{}}, 0n})
            case End{}:
              step(fuel, rest, G, S, inf, Nil{}, Nil{}, 0n,
                   finish_guess(inf, g, kids, sum, Groups.len_words(S), best),
                   Best{Tree.Node{Nil{}, Nil{}}, 0n})

def solve(+guesses: +List<+List<Nat>>, +candidates: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  +n = Groups.len_words(candidates)
  +inf = inf_of(n)
  +schedule = mk_schedule(guesses, candidates)
  best_to_maybe(inf, step(n, schedule, guesses, candidates, inf, Nil{}, Nil{}, 0n,
                           Best{Tree.Node{Nil{}, Nil{}}, inf}, Best{Tree.Node{Nil{}, Nil{}}, 0n}))
