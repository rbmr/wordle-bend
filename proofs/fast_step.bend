# Computation lemmas for the pruned search machine.
#
# `src/solve_fast.bend` runs one state machine driven by a flat schedule. This
# module proves the small equations that let the equality proof walk that
# schedule: one step per item kind, the block of one guess (its class items and
# `End`) in both the skipped and the searched case, and the class fold
# `FS.items` that mirrors `Eval.items` with the pruned child search.
import Base
import ../src/solve_fast.bend as SolveFast
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./eval.bend as Eval
import ./nat.bend as NatProof
import ./sat.bend as Sat

# The pruned search from its canonical start state.
def FS.run_at(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>) -> SolveRef.Best:
  SolveFast.step(fuel, SolveFast.schedule(G, S), G, S, inf,
    Nil{}, Nil{}, 0n, SolveFast.dummy_inf(inf), SolveFast.dummy_zero(), False{})

# The reference search from its canonical start state (the term `solve` runs).
def FS.ref_run_at(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>) -> SolveRef.Best:
  SolveRef.step(fuel, SolveRef.mk_schedule(G, S), G, S, inf,
    Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())

# The class fold of one guess, with the pruned child search. It is `Eval.items`
# with the reference child search replaced by the pruned machine at `p`.
def FS.items(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +g: +List<Nat>,
    +groups: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat, +inf: Nat) -> Eval.KS:
  match groups:
    case Nil{}:
      Eval.KS{kids, sum}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+fb, +ws}:
          Eval.Eval.with_kid(fb, kids, sum, inf,
            FS.run_at(p, inf, G, ws),
            k2 => s2 => FS.items(p, G, S, g, rest, k2, s2, inf))

# An empty schedule returns the accumulator.
def FS.nil_step(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +pending: SolveRef.Best, +skip: Bool) ->
  {SolveFast.step(fuel, Nil{}, G, S, inf, g, kids, sum, best, pending, skip)
   == best : SolveRef.Best}:
  match fuel:
    case 0n:
      {==}
    case 1n+p:
      {==}

# The state after `Begin`: the guess and the accumulator are reset, the skip
# decision becomes the new mode.
def FS.after_begin(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g2: +List<Nat>, +rest: +List<SolveFast.Item>,
    +best: SolveRef.Best, skip: Bool) -> SolveRef.Best:
  SolveFast.step(fuel, rest, G, S, inf, g2, Nil{}, 0n, best,
    SolveFast.dummy_zero(), skip)

# `Begin` at zero fuel starts a searched block.
def FS.begin_zero(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +inf: Nat,
    +g: +List<Nat>, +g2: +List<Nat>, +lb: Nat, +kids: +List<Tree.Child>,
    +sum: Nat, +best: SolveRef.Best, +pending: SolveRef.Best, +skip: Bool,
    +rest: +List<SolveFast.Item>) ->
  {SolveFast.step(0n, SolveFast.Begin{g2, lb} <> rest, G, S, inf, g, kids, sum,
      best, pending, skip)
   == SolveFast.step(0n, rest, G, S, inf, g2, Nil{}, 0n, best, pending, False{})
   : SolveRef.Best}:
  {==}

# `Begin` at positive fuel decides by the bound.
def FS.begin_succ(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +g2: +List<Nat>, +lb: Nat,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    +pending: SolveRef.Best, +skip: Bool, +rest: +List<SolveFast.Item>, b: Bool,
    +eb: {b == SolveFast.skippable(best, lb) : Bool}) ->
  {SolveFast.step(1n+p, SolveFast.Begin{g2, lb} <> rest, G, S, inf, g, kids, sum,
      best, pending, skip)
   == FS.after_begin(1n+p, G, S, inf, g2, rest, best, b)
   : SolveRef.Best}:
  Equal.trans(SolveRef.Best,
    SolveFast.step(1n+p, SolveFast.Begin{g2, lb} <> rest, G, S, inf, g, kids,
      sum, best, pending, skip),
    FS.after_begin(1n+p, G, S, inf, g2, rest, best,
      SolveFast.skippable(best, lb)),
    FS.after_begin(1n+p, G, S, inf, g2, rest, best, b),
    {==},
    Equal.cong(Bool, SolveRef.Best,
      sk => FS.after_begin(1n+p, G, S, inf, g2, rest, best, sk),
      SolveFast.skippable(best, lb), b,
      Equal.sym(Bool, b, SolveFast.skippable(best, lb), eb)))

# The state after a class item, in both modes.
def FS.after_class(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +ws: +List<+List<Nat>>,
    +rest: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, skip: Bool) -> SolveRef.Best:
  match skip:
    case True{}:
      SolveFast.step(1n+p, rest, G, S, inf, g, kids, sum, best,
        SolveFast.dummy_zero(), True{})
    case False{}:
      SolveFast.step(1n+p, rest, G, S, inf, g, kids, sum, best,
        FS.run_at(p, inf, G, ws), False{})

def FS.class_step(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +fb: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +rest: +List<SolveFast.Item>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    +skip: Bool) ->
  {SolveFast.step(1n+p, SolveFast.ClassItem{fb, ws} <> rest, G, S, inf, g, kids,
      sum, best, SolveFast.dummy_zero(), skip)
   == FS.after_class(p, G, S, inf, g, ws, rest, kids, sum, best, skip)
   : SolveRef.Best}:
  match skip:
    case True{}:
      {==}
    case False{}:
      {==}

# A class item at zero fuel becomes the infinite pending result.
def FS.class_zero(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +inf: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +rest: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +pending: SolveRef.Best, +skip: Bool) ->
  {SolveFast.step(0n, SolveFast.ClassItem{fb, ws} <> rest, G, S, inf, g, kids,
      sum, best, pending, skip)
   == SolveFast.dummy_inf(inf) : SolveRef.Best}:
  {==}

# `Add` consumes the pending child result.
def FS.add_go(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +fb: +List<Feedback.Color>,
    +rest: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +skip: Bool, pending: SolveRef.Best) -> SolveRef.Best:
  match pending:
    case SolveRef.Best{+tree, +cost}:
      SolveFast.step(fuel, rest, G, S, inf, g, Tree.Child{fb, tree} <> kids,
        SolveRef.sat_add(inf, sum, cost), best, SolveFast.dummy_zero(), skip)

def FS.add_step(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +fb: +List<Feedback.Color>,
    +rest: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +skip: Bool, +pending: SolveRef.Best) ->
  {SolveFast.step(fuel, SolveFast.Add{fb} <> rest, G, S, inf, g, kids, sum,
      best, pending, skip)
   == FS.add_go(fuel, G, S, inf, g, fb, rest, kids, sum, best, skip, pending)
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

# The `Add` unfolded: the pending result is read with `tree_of` and `cost_of`
# so the equation does not have to match the neutral child result.
def FS.add_go_eq(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +fb: +List<Feedback.Color>,
    +rest: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +skip: Bool, +pending: SolveRef.Best) ->
  {FS.add_go(fuel, G, S, inf, g, fb, rest, kids, sum, best, skip, pending)
   == SolveFast.step(fuel, rest, G, S, inf, g,
        Tree.Child{fb, Eval.Eval.tree_of(pending)} <> kids,
        SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(pending)), best,
        SolveFast.dummy_zero(), skip)
   : SolveRef.Best}:
  match pending:
    case SolveRef.Best{tree, cost}:
      {==}

# The state after `End`, in both modes. It always starts a fresh mode.
def FS.after_end(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +rest: +List<SolveFast.Item>, skip: Bool) -> SolveRef.Best:
  match skip:
    case True{}:
      SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
        SolveFast.dummy_zero(), False{})
    case False{}:
      SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n,
        SolveRef.finish_guess(inf, g, kids, sum, Groups.len_words(S), best),
        SolveFast.dummy_zero(), False{})

def FS.end_step(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +pending: SolveRef.Best, +rest: +List<SolveFast.Item>,
    +skip: Bool) ->
  {SolveFast.step(1n+p, SolveFast.End{} <> rest, G, S, inf, g, kids, sum, best,
      pending, skip)
   == FS.after_end(p, G, S, inf, g, kids, sum, best, rest, skip)
   : SolveRef.Best}:
  match skip:
    case True{}:
      {==}
    case False{}:
      {==}

# `End` at zero fuel closes the guess with no class searched.
def FS.end_zero(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +inf: Nat,
    +g: +List<Nat>, +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    +pending: SolveRef.Best, +skip: Bool, +rest: +List<SolveFast.Item>) ->
  {SolveFast.step(0n, SolveFast.End{} <> rest, G, S, inf, g, kids, sum, best,
      pending, skip)
   == SolveFast.step(0n, rest, G, S, inf, Nil{}, Nil{}, 0n,
        SolveRef.finish_guess(inf, g, kids, sum, Groups.len_words(S), best),
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  {==}

# The class fold's first step.
def FS.items_cons(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +rest: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat, +inf: Nat) ->
  {FS.items(p, G, S, g, Groups.Group{fb, ws} <> rest, kids, sum, inf)
   == Eval.Eval.with_kid(fb, kids, sum, inf, FS.run_at(p, inf, G, ws),
        k2 => s2 => FS.items(p, G, S, g, rest, k2, s2, inf))
   : Eval.KS}:
  {==}

# The state a live block's items lead to: the finished guess handed to `rest`.
def FS.resume(+fuel: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, ks: Eval.KS, +rest: +List<SolveFast.Item>,
    best: SolveRef.Best) -> SolveRef.Best:
  match ks:
    case Eval.KS{+kids, +sum}:
      SolveFast.step(fuel, rest, G, S, inf, Nil{}, Nil{}, 0n,
        SolveRef.finish_guess(inf, g, kids, sum, Groups.len_words(S), best),
        SolveFast.dummy_zero(), False{})

# The outcome of one guess's block, in both modes.
def FS.block_out(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +groups: +List<Groups.Group>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    +rest: +List<SolveFast.Item>, skip: Bool) -> SolveRef.Best:
  match skip:
    case True{}:
      SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
        SolveFast.dummy_zero(), False{})
    case False{}:
      FS.resume(1n+p, G, S, inf, g,
        FS.items(p, G, S, g, groups, kids, sum, inf), rest, best)

# A skipped block searches no class and leaves the best result alone.
def FS.block_dead(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +groups: +List<Groups.Group>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    +rest: +List<SolveFast.Item>) ->
  {SolveFast.step(1n+p,
      List.append(&2, SolveFast.Item, SolveFast.group_items(groups),
        SolveFast.End{} <> rest),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{})
   == SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  match groups:
    case Nil{}:
      FS.end_step(p, G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(),
        rest, True{})
    case Con{dgp, drest}:
      match dgp:
        case Groups.Group{+dfb, +dws}:
          +dinner : +List<SolveFast.Item> =
            List.append(&2, SolveFast.Item, SolveFast.group_items(drest),
              SolveFast.End{} <> rest)
          +dkids : +List<Tree.Child> =
            Tree.Child{dfb, Eval.Eval.tree_of(SolveFast.dummy_zero())} <> kids
          +dsum : Nat =
            SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(SolveFast.dummy_zero()))
          +dlhs1 : SolveRef.Best =
            SolveFast.step(1n+p, SolveFast.ClassItem{dfb, dws}
                <> (SolveFast.Add{dfb} <> dinner),
              G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{})
          +dlhs2 : SolveRef.Best =
            SolveFast.step(1n+p, SolveFast.Add{dfb} <> dinner, G, S, inf, g,
              kids, sum, best, SolveFast.dummy_zero(), True{})
          +dlhs3 : SolveRef.Best =
            FS.add_go(1n+p, G, S, inf, g, dfb, dinner, kids, sum, best,
              True{}, SolveFast.dummy_zero())
          +dlhs4 : SolveRef.Best =
            SolveFast.step(1n+p, dinner, G, S, inf, g, dkids, dsum, best,
              SolveFast.dummy_zero(), True{})
          +drhs : SolveRef.Best =
            SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
              SolveFast.dummy_zero(), False{})
          +de12 : {dlhs1 == dlhs2 : SolveRef.Best} =
            FS.class_step(p, G, S, inf, g, dfb, dws,
              SolveFast.Add{dfb} <> dinner, kids, sum, best, True{})
          +de23 : {dlhs2 == dlhs3 : SolveRef.Best} =
            FS.add_step(1n+p, G, S, inf, g, dfb, dinner, kids, sum, best,
              True{}, SolveFast.dummy_zero())
          +de34 : {dlhs3 == dlhs4 : SolveRef.Best} =
            FS.add_go_eq(1n+p, G, S, inf, g, dfb, dinner, kids, sum, best,
              True{}, SolveFast.dummy_zero())
          +de4t : {dlhs4 == drhs : SolveRef.Best} =
            FS.block_dead(p, G, S, inf, g, drest, dkids, dsum, best, rest)
          Equal.trans(SolveRef.Best,
            SolveFast.step(1n+p,
              List.append(&2, SolveFast.Item,
                SolveFast.group_items(Groups.Group{dfb, dws} <> drest),
                SolveFast.End{} <> rest),
              G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{}),
            dlhs1,
            SolveFast.step(1n+p, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
              SolveFast.dummy_zero(), False{}),
            {==},
            Equal.trans(SolveRef.Best, dlhs1, dlhs2, drhs,
              de12,
              Equal.trans(SolveRef.Best, dlhs2, dlhs3, drhs,
                de23,
                Equal.trans(SolveRef.Best, dlhs3, dlhs4, drhs, de34, de4t))))

# A live block: the class items and `End` continue with the finished class fold.
def FS.block_live(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +groups: +List<Groups.Group>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    +rest: +List<SolveFast.Item>) ->
  {SolveFast.step(1n+p,
      List.append(&2, SolveFast.Item, SolveFast.group_items(groups),
        SolveFast.End{} <> rest),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{})
   == FS.resume(1n+p, G, S, inf, g,
        FS.items(p, G, S, g, groups, kids, sum, inf), rest, best)
   : SolveRef.Best}:
  match groups:
    case Nil{}:
      FS.end_step(p, G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(),
        rest, False{})
    case Con{gp, restg}:
      match gp:
        case Groups.Group{+fb, +ws}:
          +inner : +List<SolveFast.Item> =
            List.append(&2, SolveFast.Item, SolveFast.group_items(restg),
              SolveFast.End{} <> rest)
          +search : SolveRef.Best = FS.run_at(p, inf, G, ws)
          +kids2 : +List<Tree.Child> =
            Tree.Child{fb, Eval.Eval.tree_of(search)} <> kids
          +sum2 : Nat = SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search))
          +lhs1 : SolveRef.Best =
            SolveFast.step(1n+p,
              SolveFast.ClassItem{fb, ws} <> (SolveFast.Add{fb} <> inner),
              G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{})
          +lhs2 : SolveRef.Best =
            SolveFast.step(1n+p, SolveFast.Add{fb} <> inner, G, S, inf, g,
              kids, sum, best, search, False{})
          +lhs3 : SolveRef.Best =
            FS.add_go(1n+p, G, S, inf, g, fb, inner, kids, sum, best, False{}, search)
          +lhs4 : SolveRef.Best =
            SolveFast.step(1n+p, inner, G, S, inf, g, kids2, sum2, best,
              SolveFast.dummy_zero(), False{})
          +rhs : SolveRef.Best =
            FS.resume(1n+p, G, S, inf, g,
              FS.items(p, G, S, g, Groups.Group{fb, ws} <> restg, kids, sum, inf),
              rest, best)
          +e12 : {lhs1 == lhs2 : SolveRef.Best} =
            FS.class_step(p, G, S, inf, g, fb, ws,
              SolveFast.Add{fb} <> inner, kids, sum, best, False{})
          +e23 : {lhs2 == lhs3 : SolveRef.Best} =
            FS.add_step(1n+p, G, S, inf, g, fb, inner, kids, sum, best, False{},
              search)
          +e34 : {lhs3 == lhs4 : SolveRef.Best} =
            FS.add_go_eq(1n+p, G, S, inf, g, fb, inner, kids, sum, best,
              False{}, search)
          +e4t : {lhs4 == FS.resume(1n+p, G, S, inf, g,
                     FS.items(p, G, S, g, restg, kids2, sum2, inf), rest, best)
                  : SolveRef.Best} =
            FS.block_live(p, G, S, inf, g, restg, kids2, sum2, best, rest)
          +wk : {FS.items(p, G, S, g, Groups.Group{fb, ws} <> restg, kids, sum, inf)
                 == FS.items(p, G, S, g, restg, kids2, sum2, inf) : Eval.KS} =
            Equal.trans(Eval.KS,
              FS.items(p, G, S, g, Groups.Group{fb, ws} <> restg, kids, sum, inf),
              Eval.Eval.with_kid(fb, kids, sum, inf, search,
                k2 => s2 => FS.items(p, G, S, g, restg, k2, s2, inf)),
              FS.items(p, G, S, g, restg, kids2, sum2, inf),
              FS.items_cons(p, G, S, g, fb, ws, restg, kids, sum, inf),
              Eval.Eval.with_kid_eq(fb, kids, sum, inf, search,
                k2 => s2 => FS.items(p, G, S, g, restg, k2, s2, inf)))
          +et : {FS.resume(1n+p, G, S, inf, g,
                     FS.items(p, G, S, g, restg, kids2, sum2, inf), rest, best)
                  == rhs : SolveRef.Best} =
            Equal.cong(Eval.KS, SolveRef.Best,
              ks => FS.resume(1n+p, G, S, inf, g, ks, rest, best),
              FS.items(p, G, S, g, restg, kids2, sum2, inf),
              FS.items(p, G, S, g, Groups.Group{fb, ws} <> restg, kids, sum, inf),
              Equal.sym(Eval.KS, FS.items(p, G, S, g,
                Groups.Group{fb, ws} <> restg, kids, sum, inf),
                FS.items(p, G, S, g, restg, kids2, sum2, inf), wk))
          Equal.trans(SolveRef.Best,
            SolveFast.step(1n+p,
              List.append(&2, SolveFast.Item,
                SolveFast.group_items(Groups.Group{fb, ws} <> restg),
                SolveFast.End{} <> rest),
              G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{}),
            lhs1, rhs, {==},
            Equal.trans(SolveRef.Best, lhs1, lhs2, rhs, e12,
              Equal.trans(SolveRef.Best, lhs2, lhs3, rhs, e23,
                Equal.trans(SolveRef.Best, lhs3, lhs4, rhs, e34,
                  Equal.trans(SolveRef.Best, lhs4,
                    FS.resume(1n+p, G, S, inf, g,
                      FS.items(p, G, S, g, restg, kids2, sum2, inf), rest, best),
                    rhs, e4t, et)))))

# A block: the class items and `End` continue in the mode the block started in.
def FS.block(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +g: +List<Nat>, +groups: +List<Groups.Group>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    +rest: +List<SolveFast.Item>, +skip: Bool) ->
  {SolveFast.step(1n+p,
      List.append(&2, SolveFast.Item, SolveFast.group_items(groups),
        SolveFast.End{} <> rest),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), skip)
   == FS.block_out(p, G, S, inf, g, groups, kids, sum, best, rest, skip)
   : SolveRef.Best}:
  match skip:
    case True{}:
      FS.block_dead(p, G, S, inf, g, groups, kids, sum, best, rest)
    case False{}:
      FS.block_live(p, G, S, inf, g, groups, kids, sum, best, rest)
