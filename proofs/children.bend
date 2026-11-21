# The child list a guess's groups produce.
#
# `Eval.Eval.items` accumulates children by prepending, so its final `kids` is the
# reverse of the group order, and `finish_guess` reverses it again. This module
# names the children in group order (`children`), proves that the accumulator is
# its reverse (`items_kids`), and that reversing twice is the identity. That is
# the bridge from the group facts to `Valid (Node g kids)`.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./eval.bend as Eval

def CH.kids_of(ks: Eval.KS) -> +List<Tree.Child>:
  match ks:
    case Eval.KS{+kids, sum}:
      kids

# The child contributed by one group: its feedback and the search result for
# the class.
def CH.kid(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>, +inf: Nat) -> Tree.Child:
  Tree.Child{fb,
    Eval.Eval.tree_of(SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
      Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()))}

def CH.children(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +groups: +List<Groups.Group>, +inf: Nat) -> +List<Tree.Child>:
  match groups:
    case Nil{}:
      Nil{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+fb, +ws}:
          CH.kid(p, G, S, fb, ws, inf) <> CH.children(p, G, S, rest, inf)

# Reversing an append.
def CH.rev_kids_append(xs: +List<Tree.Child>, ys: +List<Tree.Child>,
    acc: +List<Tree.Child>) ->
  {SolveRef.rev_kids(List.append(&2, Tree.Child, xs, ys), acc)
   == SolveRef.rev_kids(ys, SolveRef.rev_kids(xs, acc))
   : +List<Tree.Child>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      CH.rev_kids_append(t, ys, h <> acc)

# Reversing twice is the identity, with an accumulator.
def CH.rev_rev_acc(xs: +List<Tree.Child>, acc: +List<Tree.Child>) ->
  {SolveRef.rev_kids(SolveRef.rev_kids(xs, acc), Nil{})
   == SolveRef.rev_kids(acc, xs)
   : +List<Tree.Child>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      CH.rev_rev_acc(t, h <> acc)

def CH.rev_rev(xs: +List<Tree.Child>) ->
  {SolveRef.rev_kids(SolveRef.rev_kids(xs, Nil{}), Nil{}) == xs
   : +List<Tree.Child>}:
  CH.rev_rev_acc(xs, Nil{})

# Branch of `items_kids` for one group. The child search is a parameter, so the
# proof can match it once and then use the induction hypothesis on the rest.
def CH.with_kid_items_kids(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +fb: +List<Feedback.Color>,
    +rest: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat, +inf: Nat,
    +pending: SolveRef.Best,
    k: @k2: +List<Tree.Child> -> @s2: Nat ->
       {CH.kids_of(Eval.Eval.items(p, G, S, g, rest, k2, s2, inf))
        == SolveRef.rev_kids(CH.children(p, G, S, rest, inf), k2)
        : +List<Tree.Child>}) ->
  {CH.kids_of(Eval.Eval.with_kid(fb, kids, sum, inf, pending,
      k2 => s2 => Eval.Eval.items(p, G, S, g, rest, k2, s2, inf)))
   == SolveRef.rev_kids(
        Tree.Child{fb, Eval.Eval.tree_of(pending)}
        <> CH.children(p, G, S, rest, inf), kids)
   : +List<Tree.Child>}:
  match pending:
    case SolveRef.Best{tree, cost}:
      k(Tree.Child{fb, tree} <> kids, SolveRef.sat_add(inf, sum, cost))

# The accumulated children are the reverse of the group-order children.
def CH.items_kids(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +groups: +List<Groups.Group>, +kids: +List<Tree.Child>,
    +sum: Nat, +inf: Nat) ->
  {CH.kids_of(Eval.Eval.items(p, G, S, g, groups, kids, sum, inf))
   == SolveRef.rev_kids(CH.children(p, G, S, groups, inf), kids)
   : +List<Tree.Child>}:
  match groups:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+fb, +ws}:
          CH.with_kid_items_kids(p, G, S, g, fb, rest, kids, sum, inf,
            SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
              Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()),
            k2 => s2 => CH.items_kids(p, G, S, g, rest, k2, s2, inf))
