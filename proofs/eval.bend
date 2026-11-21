# A specification evaluator for the fused reference search.
#
# `src/solve_ref.bend` runs one def, `step`, over a flat schedule. This module
# gives that schedule a recursive meaning: `items` folds over a guess's
# feedback groups (calling the child search at the smaller fuel), `block`
# closes one guess, and `guesses` folds over the guess list. `items_step`,
# `guess_step`, `schedule_step`, `guesses_step` and `guesses_zero` prove that
# the state machine is exactly that fold. The equalities are pure computation
# lemmas; they do not assume anything about the child searches, so the same
# fold is then used to state the validity and optimality invariants.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback

type KS is Data:
  KS{kids: +List<Tree.Child>, sum: Nat}

def Eval.tree_of(b: SolveRef.Best) -> Tree.Tree:
  match b:
    case SolveRef.Best{+tree, cost}:
      tree

def Eval.cost_of(b: SolveRef.Best) -> Nat:
  match b:
    case SolveRef.Best{tree, +cost}:
      cost

def Eval.dummy_inf(+inf: Nat) -> SolveRef.Best:
  SolveRef.Best{Tree.Node{Nil{}, Nil{}}, inf}

def Eval.dummy_zero() -> SolveRef.Best:
  SolveRef.Best{Tree.Node{Nil{}, Nil{}}, 0n}

def Eval.with_kid(+fb: +List<Feedback.Color>, +kids: +List<Tree.Child>, +sum: Nat,
    +inf: Nat, pending: SolveRef.Best,
    k: +List<Tree.Child> -> Nat -> KS) -> KS:
  match pending:
    case SolveRef.Best{+tree, +cost}:
      k(Tree.Child{fb, tree} <> kids, SolveRef.sat_add(inf, sum, cost))

def Eval.items(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +g: +List<Nat>,
    +groups: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat, +inf: Nat) -> KS:
  match groups:
    case Nil{}:
      KS{kids, sum}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+fb, +ws}:
          Eval.with_kid(fb, kids, sum, inf,
            SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
                          Nil{}, Nil{}, 0n,
                          Eval.dummy_inf(inf), Eval.dummy_zero()),
            k2 => s2 => Eval.items(p, G, S, g, rest, k2, s2, inf))

def Eval.resume(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, ks: KS,
    +rest: +List<SolveRef.Item>, best: SolveRef.Best) -> SolveRef.Best:
  match ks:
    case KS{+kids, +sum}:
      SolveRef.step(fuel, rest, G, S, inf, Nil{}, Nil{}, 0n,
                    SolveRef.finish_guess(inf, g, kids, sum, Groups.len_words(S), best),
                    Eval.dummy_zero())

# Stepping an Add item equals the state update.
def Eval.add_go(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +fb: +List<Feedback.Color>,
    +rest: +List<SolveRef.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    best: SolveRef.Best, pending: SolveRef.Best) -> SolveRef.Best:
  match pending:
    case SolveRef.Best{+tree, +cost}:
      SolveRef.step(fuel, rest, G, S, inf, g, Tree.Child{fb, tree} <> kids,
                    SolveRef.sat_add(inf, sum, cost), best, Eval.dummy_zero())

def Eval.add_step(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +fb: +List<Feedback.Color>,
    +rest: +List<SolveRef.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    best: SolveRef.Best, pending: SolveRef.Best) ->
  {SolveRef.step(fuel, SolveRef.Add{fb} <> rest, G, S, inf, g, kids, sum, best, pending)
   == Eval.add_go(fuel, G, S, inf, g, fb, rest, kids, sum, best, pending)
   : SolveRef.Best}:
  match fuel:
    case 0n:
      match pending:
        case SolveRef.Best{tree, cost}:
          {==}
    case 1n+p:
      match pending:
        case SolveRef.Best{tree, cost}:
          {==}

# Stepping a ClassItem item calls the child's search.
def Eval.class_step(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +fb: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +rest: +List<SolveRef.Item>,
    +kids: +List<Tree.Child>, +sum: Nat, best: SolveRef.Best, pending: SolveRef.Best) ->
  {SolveRef.step(1n+p, SolveRef.ClassItem{fb, ws} <> rest, G, S, inf, g, kids, sum, best, pending)
   == SolveRef.step(1n+p, rest, G, S, inf, g, kids, sum, best,
        SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
          Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()))
   : SolveRef.Best}:
  {==}


def Eval.with_kid_eq(+fb: +List<Feedback.Color>, +kids: +List<Tree.Child>, +sum: Nat,
    +inf: Nat, +pending: SolveRef.Best,
    k: +List<Tree.Child> -> Nat -> KS) ->
  {Eval.with_kid(fb, kids, sum, inf, pending, k)
   == k(Tree.Child{fb, Eval.tree_of(pending)} <> kids,
        SolveRef.sat_add(inf, sum, Eval.cost_of(pending)))
   : KS}:
  match pending:
    case SolveRef.Best{tree, cost}:
      {==}

def Eval.add_go_eq(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +fb: +List<Feedback.Color>,
    +rest: +List<SolveRef.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +pending: SolveRef.Best) ->
  {Eval.add_go(fuel, G, S, inf, g, fb, rest, kids, sum, best, pending)
   == SolveRef.step(fuel, rest, G, S, inf, g,
        Tree.Child{fb, Eval.tree_of(pending)} <> kids,
        SolveRef.sat_add(inf, sum, Eval.cost_of(pending)), best, Eval.dummy_zero())
   : SolveRef.Best}:
  match pending:
    case SolveRef.Best{tree, cost}:
      {==}

# Stepping a group list (followed by End) equals finishing the spec fold.
def Eval.items_step(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +groups: +List<Groups.Group>, +kids: +List<Tree.Child>,
    +sum: Nat, +inf: Nat, +rest: +List<SolveRef.Item>, +best: SolveRef.Best,
    +pending: SolveRef.Best) ->
  {SolveRef.step(1n+p,
      List.append(&2, SolveRef.Item, SolveRef.group_items(groups),
        SolveRef.End{} <> rest),
      G, S, inf, g, kids, sum, best, pending)
   == Eval.resume(1n+p, G, S, inf, g,
        Eval.items(p, G, S, g, groups, kids, sum, inf), rest, best)
   : SolveRef.Best}:
  match groups:
    case Nil{}:
      {==}
    case Con{gp, restg}:
      match gp:
        case Groups.Group{+fb, +ws}:
          %Equal.sym(SolveRef.Best,
              SolveRef.step(1n+p, SolveRef.ClassItem{fb, ws} <> (SolveRef.Add{fb} <> (List.append(&2, SolveRef.Item,
                SolveRef.group_items(restg), SolveRef.End{} <> rest))), G, S, inf, g, kids, sum, best, pending),
              SolveRef.step(1n+p, SolveRef.Add{fb} <> (List.append(&2, SolveRef.Item,
                SolveRef.group_items(restg), SolveRef.End{} <> rest)), G, S, inf, g, kids, sum, best,
                SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
                  Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero())),
              Eval.class_step(p, G, S, inf, g, fb, ws,
              SolveRef.Add{fb} <> (List.append(&2, SolveRef.Item,
                SolveRef.group_items(restg), SolveRef.End{} <> rest)),
              kids, sum, best, pending)) : {
            _ == Eval.resume(1n+p, G, S, inf, g,
                   Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                              kids, sum, inf),
                   rest, best)
            : SolveRef.Best}
          %Equal.sym(SolveRef.Best,
              SolveRef.step(1n+p, SolveRef.Add{fb} <> List.append(&2, SolveRef.Item, SolveRef.group_items(restg),
                SolveRef.End{} <> rest), G, S, inf, g, kids, sum, best,
              SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
                Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero())),
              Eval.add_go(1n+p, G, S, inf, g, fb,
              List.append(&2, SolveRef.Item, SolveRef.group_items(restg),
                SolveRef.End{} <> rest),
              kids, sum, best,
              SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
                Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero())),
              Eval.add_step(1n+p, G, S, inf, g, fb,
              List.append(&2, SolveRef.Item, SolveRef.group_items(restg),
                SolveRef.End{} <> rest),
              kids, sum, best,
              SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
                Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()))) : {
            _ == Eval.resume(1n+p, G, S, inf, g,
                   Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
                              kids, sum, inf),
                   rest, best)
            : SolveRef.Best}
          %Equal.sym(SolveRef.Best,
              Eval.add_go(1n+p, G, S, inf, g, fb,
                List.append(&2, SolveRef.Item, SolveRef.group_items(restg),
                  SolveRef.End{} <> rest), kids, sum, best,
                SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
                  Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero())),
              SolveRef.step(1n+p,
                List.append(&2, SolveRef.Item, SolveRef.group_items(restg),
                  SolveRef.End{} <> rest), G, S, inf, g,
                Tree.Child{fb, Eval.tree_of(SolveRef.step(p, SolveRef.mk_schedule(G, ws),
                  G, ws, inf, Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()))} <> kids,
                SolveRef.sat_add(inf, sum, Eval.cost_of(SolveRef.step(p, SolveRef.mk_schedule(G, ws),
                  G, ws, inf, Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()))),
                best, Eval.dummy_zero()),
              Eval.add_go_eq(1n+p, G, S, inf, g, fb,
                List.append(&2, SolveRef.Item, SolveRef.group_items(restg),
                  SolveRef.End{} <> rest), kids, sum, best,
                SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
                  Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()))) : {
            _ == Eval.resume(1n+p, G, S, inf, g,
                   Eval.with_kid(fb, kids, sum, inf,
                     SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
                       Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()),
                     k2 => s2 => Eval.items(p, G, S, g, restg, k2, s2, inf)),
                   rest, best)
            : SolveRef.Best}
          Equal.trans(SolveRef.Best,
            SolveRef.step(1n+p,
              List.append(&2, SolveRef.Item, SolveRef.group_items(restg),
                SolveRef.End{} <> rest), G, S, inf, g,
              Tree.Child{fb, Eval.tree_of(SolveRef.step(p, SolveRef.mk_schedule(G, ws),
                G, ws, inf, Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()))} <> kids,
              SolveRef.sat_add(inf, sum, Eval.cost_of(SolveRef.step(p, SolveRef.mk_schedule(G, ws),
                G, ws, inf, Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()))),
              best, Eval.dummy_zero()),
            Eval.resume(1n+p, G, S, inf, g,
              Eval.items(p, G, S, g, restg,
                Tree.Child{fb, Eval.tree_of(SolveRef.step(p, SolveRef.mk_schedule(G, ws),
                  G, ws, inf, Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()))} <> kids,
                SolveRef.sat_add(inf, sum, Eval.cost_of(SolveRef.step(p, SolveRef.mk_schedule(G, ws),
                  G, ws, inf, Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()))),
                inf),
              rest, best),
            Eval.resume(1n+p, G, S, inf, g,
              Eval.with_kid(fb, kids, sum, inf,
                SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
                  Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()),
                k2 => s2 => Eval.items(p, G, S, g, restg, k2, s2, inf)),
              rest, best),
            Eval.items_step(p, G, S, g, restg,
              Tree.Child{fb, Eval.tree_of(
                SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
                  Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()))} <> kids,
              SolveRef.sat_add(inf, sum, Eval.cost_of(
                SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
                  Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()))),
              inf, rest, best, Eval.dummy_zero()),
            Equal.sym(SolveRef.Best,
              Eval.resume(1n+p, G, S, inf, g,
                Eval.with_kid(fb, kids, sum, inf,
                  SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
                    Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()),
                  k2 => s2 => Eval.items(p, G, S, g, restg, k2, s2, inf)),
                rest, best),
              Eval.resume(1n+p, G, S, inf, g,
                Eval.items(p, G, S, g, restg,
                  Tree.Child{fb, Eval.tree_of(SolveRef.step(p, SolveRef.mk_schedule(G, ws),
                    G, ws, inf, Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()))} <> kids,
                  SolveRef.sat_add(inf, sum, Eval.cost_of(SolveRef.step(p, SolveRef.mk_schedule(G, ws),
                    G, ws, inf, Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()))),
                  inf),
                rest, best),
              Equal.cong(KS, SolveRef.Best,
                ks => Eval.resume(1n+p, G, S, inf, g, ks, rest, best),
                Eval.with_kid(fb, kids, sum, inf,
                  SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
                    Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()),
                  k2 => s2 => Eval.items(p, G, S, g, restg, k2, s2, inf)),
                Eval.items(p, G, S, g, restg,
                  Tree.Child{fb, Eval.tree_of(SolveRef.step(p, SolveRef.mk_schedule(G, ws),
                    G, ws, inf, Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()))} <> kids,
                  SolveRef.sat_add(inf, sum, Eval.cost_of(SolveRef.step(p, SolveRef.mk_schedule(G, ws),
                    G, ws, inf, Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()))),
                  inf),
                Eval.with_kid_eq(fb, kids, sum, inf,
                  SolveRef.step(p, SolveRef.mk_schedule(G, ws), G, ws, inf,
                    Nil{}, Nil{}, 0n, Eval.dummy_inf(inf), Eval.dummy_zero()),
                  k2 => s2 => Eval.items(p, G, S, g, restg, k2, s2, inf)))))


def Eval.finish_ks(+inf: Nat, +g: +List<Nat>, +S: +List<+List<Nat>>, ks: KS,
    best: SolveRef.Best) -> SolveRef.Best:
  match ks:
    case KS{+kids, +sum}:
      SolveRef.finish_guess(inf, g, kids, sum, Groups.len_words(S), best)

def Eval.block(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +g: +List<Nat>,
    +inf: Nat, +groups: +List<Groups.Group>, +best: SolveRef.Best) -> SolveRef.Best:
  Eval.finish_ks(inf, g, S, Eval.items(p, G, S, g, groups, Nil{}, 0n, inf), best)



def Eval.resume_eq(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +ks: KS, +rest: +List<SolveRef.Item>,
    +best: SolveRef.Best) ->
  {Eval.resume(fuel, G, S, inf, g, ks, rest, best)
   == SolveRef.step(fuel, rest, G, S, inf, Nil{}, Nil{}, 0n,
        Eval.finish_ks(inf, g, S, ks, best), Eval.dummy_zero())
   : SolveRef.Best}:
  match ks:
    case KS{kids, sum}:
      {==}

def Eval.append_assoc_item(xs: +List<SolveRef.Item>, ys: +List<SolveRef.Item>,
    zs: +List<SolveRef.Item>) ->
  {List.append(&2, SolveRef.Item, List.append(&2, SolveRef.Item, xs, ys), zs)
   == List.append(&2, SolveRef.Item, xs, List.append(&2, SolveRef.Item, ys, zs))
   : +List<SolveRef.Item>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(+List<SolveRef.Item>, +List<SolveRef.Item>, l => h <> l,
        List.append(&2, SolveRef.Item, List.append(&2, SolveRef.Item, t, ys), zs),
        List.append(&2, SolveRef.Item, t, List.append(&2, SolveRef.Item, ys, zs)),
        Eval.append_assoc_item(t, ys, zs))

def Eval.guess_step(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +groups: +List<Groups.Group>, +inf: Nat,
    +rest: +List<SolveRef.Item>, +best: SolveRef.Best, +pending: SolveRef.Best) ->
  {SolveRef.step(1n+p,
      List.append(&2, SolveRef.Item, SolveRef.guess_items(g, groups), rest),
      G, S, inf, Nil{}, Nil{}, 0n, best, pending)
   == SolveRef.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n,
        Eval.block(p, G, S, g, inf, groups, best), Eval.dummy_zero())
   : SolveRef.Best}:
  Equal.trans(SolveRef.Best,
    SolveRef.step(1n+p,
      List.append(&2, SolveRef.Item,
        List.append(&2, SolveRef.Item, SolveRef.group_items(groups), [SolveRef.End{}]), rest),
      G, S, inf, g, Nil{}, 0n, best, pending),
    SolveRef.step(1n+p,
      List.append(&2, SolveRef.Item, SolveRef.group_items(groups),
        SolveRef.End{} <> rest),
      G, S, inf, g, Nil{}, 0n, best, pending),
    SolveRef.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n,
      Eval.finish_ks(inf, g, S, Eval.items(p, G, S, g, groups, Nil{}, 0n, inf), best),
      Eval.dummy_zero()),
    Equal.cong(+List<SolveRef.Item>, SolveRef.Best,
      cs => SolveRef.step(1n+p, cs, G, S, inf, g, Nil{}, 0n, best, pending),
      List.append(&2, SolveRef.Item,
        List.append(&2, SolveRef.Item, SolveRef.group_items(groups), [SolveRef.End{}]), rest),
      List.append(&2, SolveRef.Item, SolveRef.group_items(groups), SolveRef.End{} <> rest),
      Eval.append_assoc_item(SolveRef.group_items(groups), [SolveRef.End{}], rest)),
    Equal.trans(SolveRef.Best,
      SolveRef.step(1n+p,
        List.append(&2, SolveRef.Item, SolveRef.group_items(groups),
          SolveRef.End{} <> rest),
        G, S, inf, g, Nil{}, 0n, best, pending),
      Eval.resume(1n+p, G, S, inf, g,
        Eval.items(p, G, S, g, groups, Nil{}, 0n, inf), rest, best),
      SolveRef.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n,
        Eval.finish_ks(inf, g, S,
          Eval.items(p, G, S, g, groups, Nil{}, 0n, inf), best),
        Eval.dummy_zero()),
      Eval.items_step(p, G, S, g, groups, Nil{}, 0n, inf, rest, best, pending),
      Eval.resume_eq(1n+p, G, S, inf, g,
        Eval.items(p, G, S, g, groups, Nil{}, 0n, inf), rest, best)))

def Eval.schedule_guess_bool(+g: +List<Nat>, +groups: +List<Groups.Group>,
    b: Bool) -> +List<SolveRef.Item>:
  Feedback.Bool.case(+List<SolveRef.Item>, b, SolveRef.guess_items(g, groups), Nil{})

def Eval.guess_bool(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +groups: +List<Groups.Group>, +inf: Nat, b: Bool,
    +best: SolveRef.Best) -> SolveRef.Best:
  Feedback.Bool.case(SolveRef.Best, b, Eval.block(p, G, S, g, inf, groups, best), best)

# Stepping one guess in the schedule equals the spec guess followed by the rest.
def Eval.schedule_step(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +groups: +List<Groups.Group>, +inf: Nat, b: Bool,
    +rest: +List<SolveRef.Item>, +best: SolveRef.Best) ->
  {SolveRef.step(1n+p,
      List.append(&2, SolveRef.Item,
        Eval.schedule_guess_bool(g, groups, b), rest),
      G, S, inf, Nil{}, Nil{}, 0n, best, Eval.dummy_zero())
   == SolveRef.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n,
        Eval.guess_bool(p, G, S, g, groups, inf, b, best), Eval.dummy_zero())
   : SolveRef.Best}:
  match b:
    case True{}:
      Eval.guess_step(p, G, S, g, groups, inf, rest, best, Eval.dummy_zero())
    case False{}:
      {==}

def Eval.guess(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +best: SolveRef.Best) -> SolveRef.Best:
  Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf,
    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), best)

def Eval.guesses(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +gs: +List<+List<Nat>>, +best: SolveRef.Best) -> SolveRef.Best:
  match fuel:
    case 0n:
      match gs:
        case Nil{}:
          best
        case Con{g, rest}:
          Eval.guesses(0n, G, S, inf, rest,
            SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(S), best))
    case 1n+p:
      match gs:
        case Nil{}:
          best
        case Con{g, rest}:
          Eval.guesses(1n+p, G, S, inf, rest, Eval.guess(p, G, S, g, inf, best))

# Stepping the schedule at positive fuel equals the spec fold over guesses.
def Eval.guesses_step(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +gs: +List<+List<Nat>>, +best: SolveRef.Best) ->
  {SolveRef.step(1n+p, SolveRef.mk_schedule(gs, S), G, S, inf,
      Nil{}, Nil{}, 0n, best, Eval.dummy_zero())
   == Eval.guesses(1n+p, G, S, inf, gs, best)
   : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{g, rest}:
      Equal.trans(SolveRef.Best,
        SolveRef.step(1n+p, SolveRef.mk_schedule(g <> rest, S), G, S, inf,
          Nil{}, Nil{}, 0n, best, Eval.dummy_zero()),
        SolveRef.step(1n+p, SolveRef.mk_schedule(rest, S), G, S, inf,
          Nil{}, Nil{}, 0n, Eval.guess(p, G, S, g, inf, best), Eval.dummy_zero()),
        Eval.guesses(1n+p, G, S, inf, g <> rest, best),
        Eval.schedule_step(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf,
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
          SolveRef.mk_schedule(rest, S), best),
        Eval.guesses_step(p, G, S, inf, rest, Eval.guess(p, G, S, g, inf, best)))

def Eval.zero_guess_step(+G: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +rest: +List<SolveRef.Item>, +best: SolveRef.Best) ->
  {SolveRef.step(0n, List.append(&2, SolveRef.Item, SolveRef.guess_items(g, Nil{}), rest),
      G, Nil{}, inf, Nil{}, Nil{}, 0n, best, Eval.dummy_zero())
   == SolveRef.step(0n, rest, G, Nil{}, inf, Nil{}, Nil{}, 0n,
        SolveRef.finish_guess(inf, g, Nil{}, 0n, 0n, best), Eval.dummy_zero())
   : SolveRef.Best}:
  {==}

def Eval.guesses_zero(+G: +List<+List<Nat>>, +inf: Nat,
    +gs: +List<+List<Nat>>, +best: SolveRef.Best) ->
  {SolveRef.step(0n, SolveRef.mk_schedule(gs, Nil{}), G, Nil{}, inf,
      Nil{}, Nil{}, 0n, best, Eval.dummy_zero())
   == Eval.guesses(0n, G, Nil{}, inf, gs, best)
   : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{g, rest}:
      Equal.trans(SolveRef.Best,
        SolveRef.step(0n, SolveRef.mk_schedule(g <> rest, Nil{}), G, Nil{}, inf,
          Nil{}, Nil{}, 0n, best, Eval.dummy_zero()),
        SolveRef.step(0n, SolveRef.mk_schedule(rest, Nil{}), G, Nil{}, inf,
          Nil{}, Nil{}, 0n,
          SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(Nil{}), best),
          Eval.dummy_zero()),
        Eval.guesses(0n, G, Nil{}, inf, g <> rest, best),
        Eval.zero_guess_step(G, inf, g, SolveRef.mk_schedule(rest, Nil{}), best),
        Eval.guesses_zero(G, inf, rest,
          SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(Nil{}), best)))
