# Computation lemmas for the pruned search machine.
#
# `src/solve_fast.bend` runs one state machine driven by a remaining guess list
# `gs` and a current guess schedule `cs`. This module proves the small
# equations that let the equality proof walk that schedule: popping the next
# guess when `cs` is empty, one step per item kind, and the dead-tail lemmas
# when a guess or remaining class suffix is skipped.
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
  SolveFast.step(fuel, G, Nil{}, G, S, inf,
    Nil{}, Nil{}, 0n, SolveFast.dummy_inf(inf), SolveFast.dummy_zero(), False{})

# The reference search from its canonical start state (the term `solve` runs).
def FS.ref_run_at(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>) -> SolveRef.Best:
  SolveRef.step(fuel, SolveRef.mk_schedule(G, S), G, S, inf,
    Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())

# Popping the next guess at positive fuel when `cs` is empty.
def FS.pop_guess_succ(+p: Nat, +g2: +List<Nat>, +grest: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +inf: Nat,
    +g: +List<Nat>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +pending: SolveRef.Best, +skip: Bool,
    pre_skip: Bool,
    +ep: {pre_skip == SolveFast.skippable(best,
            SolveFast.pre_lb(Groups.len_words(S), g2, S)) : Bool}) ->
  {SolveFast.step(1n+p, g2 <> grest, Nil{}, G, S, inf, g, kids, sum,
      best, pending, skip)
   == SolveFast.step(1n+p, grest,
        SolveFast.guess_items_go(g2, S, Groups.len_words(S), pre_skip),
        G, S, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  Equal.cong(Bool, SolveRef.Best,
    ps => SolveFast.step(1n+p, grest,
            SolveFast.guess_items_go(g2, S, Groups.len_words(S), ps),
            G, S, inf, Nil{}, Nil{}, 0n, best,
            SolveFast.dummy_zero(), False{}),
    SolveFast.skippable(best, SolveFast.pre_lb(Groups.len_words(S), g2, S)),
    pre_skip,
    Equal.sym(Bool, pre_skip,
      SolveFast.skippable(best,
        SolveFast.pre_lb(Groups.len_words(S), g2, S)), ep))

# The state after `Begin`: the guess and the accumulator are reset, the skip
# decision becomes the new mode.
def FS.after_begin(+fuel: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g2: +List<Nat>,
    +rest: +List<SolveFast.Item>, +best: SolveRef.Best,
    skip: Bool) -> SolveRef.Best:
  SolveFast.step(fuel, gs, rest, G, S, inf, g2, Nil{}, 0n, best,
    SolveFast.dummy_zero(), skip)

def FS.begin_open(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>, +g2: +List<Nat>,
    +lb: Nat, +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    +pending: SolveRef.Best, +skip: Bool, +rest: +List<SolveFast.Item>) ->
  {SolveFast.step(1n+p, gs, SolveFast.Begin{g2, lb} <> rest, G, S, inf, g,
      kids, sum, best, pending, skip)
   == FS.after_begin(1n+p, gs, G, S, inf, g2, rest, best,
        SolveFast.skippable(best, lb))
   : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{gh, gt}:
      {==}

# `Begin` at positive fuel decides by the bound.
def FS.begin_succ(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>, +g2: +List<Nat>,
    +lb: Nat, +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    +pending: SolveRef.Best, +skip: Bool, +rest: +List<SolveFast.Item>,
    b: Bool, +eb: {b == SolveFast.skippable(best, lb) : Bool}) ->
  {SolveFast.step(1n+p, gs, SolveFast.Begin{g2, lb} <> rest, G, S, inf, g,
      kids, sum, best, pending, skip)
   == FS.after_begin(1n+p, gs, G, S, inf, g2, rest, best, b)
   : SolveRef.Best}:
  Equal.trans(SolveRef.Best,
    SolveFast.step(1n+p, gs, SolveFast.Begin{g2, lb} <> rest, G, S, inf, g,
      kids, sum, best, pending, skip),
    FS.after_begin(1n+p, gs, G, S, inf, g2, rest, best,
      SolveFast.skippable(best, lb)),
    FS.after_begin(1n+p, gs, G, S, inf, g2, rest, best, b),
    FS.begin_open(p, gs, G, S, inf, g, g2, lb, kids, sum, best, pending, skip,
      rest),
    Equal.cong(Bool, SolveRef.Best,
      sk => FS.after_begin(1n+p, gs, G, S, inf, g2, rest, best, sk),
      SolveFast.skippable(best, lb), b,
      Equal.sym(Bool, b, SolveFast.skippable(best, lb), eb)))

# `Check` in a skipped block stays in `skip = True{}`.
def FS.check_dead(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>, +rem_lb: Nat,
    +rest: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +pending: SolveRef.Best) ->
  {SolveFast.step(1n+p, gs, SolveFast.Check{rem_lb} <> rest, G, S, inf, g,
      kids, sum, best, pending, True{})
   == SolveFast.step(1n+p, gs, rest, G, S, inf, g, kids, sum, best,
        SolveFast.dummy_zero(), True{})
   : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{gh, gt}:
      {==}

def FS.check_open(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>, +rem_lb: Nat,
    +rest: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +pending: SolveRef.Best) ->
  {SolveFast.step(1n+p, gs, SolveFast.Check{rem_lb} <> rest, G, S, inf, g,
      kids, sum, best, pending, False{})
   == SolveFast.step(1n+p, gs, rest, G, S, inf, g, kids, sum, best,
        SolveFast.dummy_zero(),
        SolveFast.skippable(best, Nat.add(sum, rem_lb)))
   : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{gh, gt}:
      {==}

# `Check` in a live block updates `skip` from `sum + rem_lb`.
def FS.check_live(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>, +rem_lb: Nat,
    +rest: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +pending: SolveRef.Best, b: Bool,
    +eb: {b == SolveFast.skippable(best, Nat.add(sum, rem_lb)) : Bool}) ->
  {SolveFast.step(1n+p, gs, SolveFast.Check{rem_lb} <> rest, G, S, inf, g,
      kids, sum, best, pending, False{})
   == SolveFast.step(1n+p, gs, rest, G, S, inf, g, kids, sum, best,
        SolveFast.dummy_zero(), b)
   : SolveRef.Best}:
  Equal.trans(SolveRef.Best,
    SolveFast.step(1n+p, gs, SolveFast.Check{rem_lb} <> rest, G, S, inf, g,
      kids, sum, best, pending, False{}),
    SolveFast.step(1n+p, gs, rest, G, S, inf, g, kids, sum, best,
      SolveFast.dummy_zero(),
      SolveFast.skippable(best, Nat.add(sum, rem_lb))),
    SolveFast.step(1n+p, gs, rest, G, S, inf, g, kids, sum, best,
      SolveFast.dummy_zero(), b),
    FS.check_open(p, gs, G, S, inf, g, rem_lb, rest, kids, sum, best, pending),
    Equal.cong(Bool, SolveRef.Best,
      sk => SolveFast.step(1n+p, gs, rest, G, S, inf, g, kids, sum, best,
              SolveFast.dummy_zero(), sk),
      SolveFast.skippable(best, Nat.add(sum, rem_lb)), b,
      Equal.sym(Bool, b, SolveFast.skippable(best, Nat.add(sum, rem_lb)), eb)))

# The state after a class item, in both modes.
def FS.after_class(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>, +ws: +List<+List<Nat>>,
    +rest: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, skip: Bool) -> SolveRef.Best:
  match skip:
    case True{}:
      SolveFast.step(1n+p, gs, rest, G, S, inf, g, kids, sum, best,
        SolveFast.dummy_zero(), True{})
    case False{}:
      SolveFast.step(1n+p, gs, rest, G, S, inf, g, kids, sum, best,
        FS.run_at(p, inf, G, ws), False{})

def FS.class_step(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +rest: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +skip: Bool) ->
  {SolveFast.step(1n+p, gs, SolveFast.ClassItem{fb, ws} <> rest, G, S, inf, g,
      kids, sum, best, SolveFast.dummy_zero(), skip)
   == FS.after_class(p, gs, G, S, inf, g, ws, rest, kids, sum, best, skip)
   : SolveRef.Best}:
  match gs:
    case Nil{}:
      match skip:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{gh, gt}:
      match skip:
        case True{}:
          {==}
        case False{}:
          {==}

# `Add` consumes the pending child result.
def FS.add_go(+fuel: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +rest: +List<SolveFast.Item>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best, +skip: Bool,
    pending: SolveRef.Best) -> SolveRef.Best:
  match pending:
    case SolveRef.Best{+tree, +cost}:
      SolveFast.step(fuel, gs, rest, G, S, inf, g,
        Tree.Child{fb, tree} <> kids,
        SolveRef.sat_add(inf, sum, cost), best, SolveFast.dummy_zero(), skip)

def FS.add_step(+fuel: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +rest: +List<SolveFast.Item>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best, +skip: Bool,
    +pending: SolveRef.Best) ->
  {SolveFast.step(fuel, gs, SolveFast.Add{fb} <> rest, G, S, inf, g, kids, sum,
      best, pending, skip)
   == FS.add_go(fuel, gs, G, S, inf, g, fb, rest, kids, sum, best, skip,
        pending)
   : SolveRef.Best}:
  match fuel:
    case 0n:
      match gs:
        case Nil{}:
          match pending:
            case SolveRef.Best{tree, cost}:
              {==}
        case Con{gh, gt}:
          match pending:
            case SolveRef.Best{tree, cost}:
              {==}
    case 1n+p:
      match gs:
        case Nil{}:
          match pending:
            case SolveRef.Best{tree, cost}:
              {==}
        case Con{gh, gt}:
          match pending:
            case SolveRef.Best{tree, cost}:
              {==}

def FS.add_go_eq(+fuel: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +rest: +List<SolveFast.Item>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best, +skip: Bool,
    +pending: SolveRef.Best) ->
  {FS.add_go(fuel, gs, G, S, inf, g, fb, rest, kids, sum, best, skip, pending)
   == SolveFast.step(fuel, gs, rest, G, S, inf, g,
        Tree.Child{fb, Eval.Eval.tree_of(pending)} <> kids,
        SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(pending)), best,
        SolveFast.dummy_zero(), skip)
   : SolveRef.Best}:
  match pending:
    case SolveRef.Best{tree, cost}:
      {==}

# The state after `End`, in both modes. It always starts a fresh mode.
def FS.after_end(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    +rest: +List<SolveFast.Item>, skip: Bool) -> SolveRef.Best:
  match skip:
    case True{}:
      SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
        SolveFast.dummy_zero(), False{})
    case False{}:
      SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
        SolveRef.finish_guess(inf, g, kids, sum, Groups.len_words(S), best),
        SolveFast.dummy_zero(), False{})

def FS.end_step(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    +pending: SolveRef.Best, +rest: +List<SolveFast.Item>, +skip: Bool) ->
  {SolveFast.step(1n+p, gs, SolveFast.End{} <> rest, G, S, inf, g, kids, sum,
      best, pending, skip)
   == FS.after_end(p, gs, G, S, inf, g, kids, sum, best, rest, skip)
   : SolveRef.Best}:
  match gs:
    case Nil{}:
      match skip:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{gh, gt}:
      match skip:
        case True{}:
          {==}
        case False{}:
          {==}

# A skipped `ClassItem` followed by `Add` updates the dead accumulator and
# stays in `skip = True{}`.
def FS.class_add_dead(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +dfb: +List<Feedback.Color>, +dws: +List<+List<Nat>>,
    +dinner: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best) ->
  {SolveFast.step(1n+p, gs,
      SolveFast.ClassItem{dfb, dws} <> (SolveFast.Add{dfb} <> dinner),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{})
   == SolveFast.step(1n+p, gs, dinner, G, S, inf, g,
        Tree.Child{dfb, Eval.Eval.tree_of(SolveFast.dummy_zero())} <> kids,
        SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(SolveFast.dummy_zero())),
        best, SolveFast.dummy_zero(), True{})
   : SolveRef.Best}:
  +dkids : +List<Tree.Child> =
    Tree.Child{dfb, Eval.Eval.tree_of(SolveFast.dummy_zero())} <> kids
  +dsum : Nat =
    SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(SolveFast.dummy_zero()))
  +dlhs1 : SolveRef.Best =
    SolveFast.step(1n+p, gs,
      SolveFast.ClassItem{dfb, dws} <> (SolveFast.Add{dfb} <> dinner),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{})
  +dlhs2 : SolveRef.Best =
    SolveFast.step(1n+p, gs, SolveFast.Add{dfb} <> dinner, G, S, inf, g,
      kids, sum, best, SolveFast.dummy_zero(), True{})
  +dlhs3 : SolveRef.Best =
    FS.add_go(1n+p, gs, G, S, inf, g, dfb, dinner, kids, sum, best,
      True{}, SolveFast.dummy_zero())
  +dlhs4 : SolveRef.Best =
    SolveFast.step(1n+p, gs, dinner, G, S, inf, g, dkids, dsum, best,
      SolveFast.dummy_zero(), True{})
  +de12 : {dlhs1 == dlhs2 : SolveRef.Best} =
    FS.class_step(p, gs, G, S, inf, g, dfb, dws,
      SolveFast.Add{dfb} <> dinner, kids, sum, best, True{})
  +de23 : {dlhs2 == dlhs3 : SolveRef.Best} =
    FS.add_step(1n+p, gs, G, S, inf, g, dfb, dinner, kids, sum, best,
      True{}, SolveFast.dummy_zero())
  +de34 : {dlhs3 == dlhs4 : SolveRef.Best} =
    FS.add_go_eq(1n+p, gs, G, S, inf, g, dfb, dinner, kids, sum, best,
      True{}, SolveFast.dummy_zero())
  Equal.trans(SolveRef.Best, dlhs1, dlhs2, dlhs4,
    de12,
    Equal.trans(SolveRef.Best, dlhs2, dlhs3, dlhs4, de23, de34))

# A live `ClassItem` followed by `Add` searches the class at fuel `p`, adds the
# child and continues in `skip = False{}`.
def FS.class_add_live(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +inner: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best) ->
  {SolveFast.step(1n+p, gs,
      SolveFast.ClassItem{fb, ws} <> (SolveFast.Add{fb} <> inner),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{})
   == SolveFast.step(1n+p, gs, inner, G, S, inf, g,
        Tree.Child{fb, Eval.Eval.tree_of(FS.run_at(p, inf, G, ws))} <> kids,
        SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(FS.run_at(p, inf, G, ws))),
        best, SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  +search : SolveRef.Best = FS.run_at(p, inf, G, ws)
  +kids2 : +List<Tree.Child> =
    Tree.Child{fb, Eval.Eval.tree_of(search)} <> kids
  +sum2 : Nat = SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search))
  +lhs1 : SolveRef.Best =
    SolveFast.step(1n+p, gs,
      SolveFast.ClassItem{fb, ws} <> (SolveFast.Add{fb} <> inner),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{})
  +lhs2 : SolveRef.Best =
    SolveFast.step(1n+p, gs, SolveFast.Add{fb} <> inner, G, S, inf, g,
      kids, sum, best, search, False{})
  +lhs3 : SolveRef.Best =
    FS.add_go(1n+p, gs, G, S, inf, g, fb, inner, kids, sum, best, False{},
      search)
  +lhs4 : SolveRef.Best =
    SolveFast.step(1n+p, gs, inner, G, S, inf, g, kids2, sum2, best,
      SolveFast.dummy_zero(), False{})
  +e12 : {lhs1 == lhs2 : SolveRef.Best} =
    FS.class_step(p, gs, G, S, inf, g, fb, ws,
      SolveFast.Add{fb} <> inner, kids, sum, best, False{})
  +e23 : {lhs2 == lhs3 : SolveRef.Best} =
    FS.add_step(1n+p, gs, G, S, inf, g, fb, inner, kids, sum, best, False{},
      search)
  +e34 : {lhs3 == lhs4 : SolveRef.Best} =
    FS.add_go_eq(1n+p, gs, G, S, inf, g, fb, inner, kids, sum, best,
      False{}, search)
  Equal.trans(SolveRef.Best, lhs1, lhs2, lhs4, e12,
    Equal.trans(SolveRef.Best, lhs2, lhs3, lhs4, e23, e34))

# A skipped `OneItem` leaves `kids` and `sum` unchanged and stays in
# `skip = True{}`.
def FS.one_dead(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +dfb: +List<Feedback.Color>, +dw: +List<Nat>,
    +dinner: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best) ->
  {SolveFast.step(1n+p, gs, SolveFast.OneItem{dfb, dw} <> dinner,
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{})
   == SolveFast.step(1n+p, gs, dinner, G, S, inf, g, kids, sum, best,
        SolveFast.dummy_zero(), True{})
   : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{gh, gt}:
      {==}

# A live `OneItem` adds the leaf `Tree.Node{w, Nil{}}` of cost 1 directly.
def FS.one_live(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +w: +List<Nat>,
    +inner: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best) ->
  {SolveFast.step(1n+p, gs, SolveFast.OneItem{fb, w} <> inner,
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{})
   == SolveFast.step(1n+p, gs, inner, G, S, inf, g,
        Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
        SolveRef.sat_add(inf, sum, 1n), best,
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{gh, gt}:
      {==}

def FS.block_dead_check(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +n: Nat, +inf: Nat, +g: +List<Nat>,
    +dfb: +List<Feedback.Color>, +dws: +List<+List<Nat>>,
    +drest: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +rest: +List<SolveFast.Item>,
    rec: {SolveFast.step(1n+p, gs,
            List.append(&2, SolveFast.Item, SolveFast.group_items(n, drest),
              SolveFast.End{} <> rest),
            G, S, inf, g,
            Tree.Child{dfb, Eval.Eval.tree_of(SolveFast.dummy_zero())} <> kids,
            SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(SolveFast.dummy_zero())),
            best, SolveFast.dummy_zero(), True{})
          == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
               SolveFast.dummy_zero(), False{})
          : SolveRef.Best}) ->
  {SolveFast.step(1n+p, gs,
      SolveFast.Check{SolveFast.lower_bound(n,
        Groups.Group{dfb, dws} <> drest)}
        <> (SolveFast.ClassItem{dfb, dws}
            <> (SolveFast.Add{dfb}
                <> List.append(&2, SolveFast.Item,
                     SolveFast.group_items(n, drest),
                     SolveFast.End{} <> rest))),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{})
   == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  +rem_lb : Nat =
    SolveFast.lower_bound(n, Groups.Group{dfb, dws} <> drest)
  +dinner : +List<SolveFast.Item> =
    List.append(&2, SolveFast.Item, SolveFast.group_items(n, drest),
      SolveFast.End{} <> rest)
  +dkids : +List<Tree.Child> =
    Tree.Child{dfb, Eval.Eval.tree_of(SolveFast.dummy_zero())} <> kids
  +dsum : Nat =
    SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(SolveFast.dummy_zero()))
  +drhs : SolveRef.Best =
    SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
      SolveFast.dummy_zero(), False{})
  +e0 : {SolveFast.step(1n+p, gs,
           SolveFast.Check{rem_lb}
             <> (SolveFast.ClassItem{dfb, dws}
                 <> (SolveFast.Add{dfb} <> dinner)),
           G, S, inf, g, kids, sum, best,
           SolveFast.dummy_zero(), True{})
         == SolveFast.step(1n+p, gs,
              SolveFast.ClassItem{dfb, dws}
                <> (SolveFast.Add{dfb} <> dinner),
              G, S, inf, g, kids, sum, best,
              SolveFast.dummy_zero(), True{})
         : SolveRef.Best} =
    FS.check_dead(p, gs, G, S, inf, g, rem_lb,
      SolveFast.ClassItem{dfb, dws} <> (SolveFast.Add{dfb} <> dinner),
      kids, sum, best, SolveFast.dummy_zero())
  Equal.trans(SolveRef.Best,
    SolveFast.step(1n+p, gs,
      SolveFast.Check{rem_lb}
        <> (SolveFast.ClassItem{dfb, dws}
            <> (SolveFast.Add{dfb} <> dinner)),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{}),
    SolveFast.step(1n+p, gs,
      SolveFast.ClassItem{dfb, dws} <> (SolveFast.Add{dfb} <> dinner),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{}),
    drhs,
    e0,
    Equal.trans(SolveRef.Best,
      SolveFast.step(1n+p, gs,
        SolveFast.ClassItem{dfb, dws}
          <> (SolveFast.Add{dfb} <> dinner),
        G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{}),
      SolveFast.step(1n+p, gs, dinner, G, S, inf, g, dkids, dsum, best,
        SolveFast.dummy_zero(), True{}),
      drhs,
      FS.class_add_dead(p, gs, G, S, inf, g, dfb, dws, dinner, kids,
        sum, best),
      rec))

# A skipped block searches no class and leaves the best result alone.
def FS.block_dead(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +n: Nat, +inf: Nat, +g: +List<Nat>,
    +groups: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +rest: +List<SolveFast.Item>) ->
  {SolveFast.step(1n+p, gs,
      List.append(&2, SolveFast.Item, SolveFast.group_items(n, groups),
        SolveFast.End{} <> rest),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{})
   == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  match groups:
    case Nil{}:
      FS.end_step(p, gs, G, S, inf, g, kids, sum, best,
        SolveFast.dummy_zero(), rest, True{})
    case Con{dgp, drest}:
      match dgp:
        case Groups.Group{+dfb, +dws}:
          match dws:
            case Nil{}:
              +dkids : +List<Tree.Child> =
                Tree.Child{dfb, Eval.Eval.tree_of(SolveFast.dummy_zero())} <> kids
              +dsum : Nat =
                SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(SolveFast.dummy_zero()))
              FS.block_dead_check(p, gs, G, S, n, inf, g, dfb, Nil{}, drest,
                kids, sum, best, rest,
                FS.block_dead(p, gs, G, S, n, inf, g, drest, dkids, dsum, best,
                  rest))
            case Con{+dw, +dwt}:
              match dwt:
                case Nil{}:
                  +dinner : +List<SolveFast.Item> =
                    List.append(&2, SolveFast.Item,
                      SolveFast.group_items(n, drest),
                      SolveFast.End{} <> rest)
                  Equal.trans(SolveRef.Best,
                    SolveFast.step(1n+p, gs,
                      SolveFast.OneItem{dfb, dw} <> dinner,
                      G, S, inf, g, kids, sum, best,
                      SolveFast.dummy_zero(), True{}),
                    SolveFast.step(1n+p, gs, dinner, G, S, inf, g, kids, sum,
                      best, SolveFast.dummy_zero(), True{}),
                    SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
                      best, SolveFast.dummy_zero(), False{}),
                    FS.one_dead(p, gs, G, S, inf, g, dfb, dw, dinner, kids,
                      sum, best),
                    FS.block_dead(p, gs, G, S, n, inf, g, drest, kids, sum,
                      best, rest))
                case Con{+dw2, +dwt2}:
                  +dws2 : +List<+List<Nat>> = dw <> (dw2 <> dwt2)
                  +dkids : +List<Tree.Child> =
                    Tree.Child{dfb, Eval.Eval.tree_of(SolveFast.dummy_zero())} <> kids
                  +dsum : Nat =
                    SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(SolveFast.dummy_zero()))
                  FS.block_dead_check(p, gs, G, S, n, inf, g, dfb, dws2, drest,
                    kids, sum, best, rest,
                    FS.block_dead(p, gs, G, S, n, inf, g, drest, dkids, dsum,
                      best, rest))

# A skipped class tail (`ClassItem`, `Add`, and the remaining groups) leaves
# `best` unchanged.
def FS.tail_dead(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +n: Nat, +inf: Nat, +g: +List<Nat>,
    +dfb: +List<Feedback.Color>, +dws: +List<+List<Nat>>,
    +drest: +List<Groups.Group>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +rest: +List<SolveFast.Item>) ->
  {SolveFast.step(1n+p, gs,
      SolveFast.ClassItem{dfb, dws}
        <> (SolveFast.Add{dfb}
            <> List.append(&2, SolveFast.Item, SolveFast.group_items(n, drest),
                 SolveFast.End{} <> rest)),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{})
   == SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
        SolveFast.dummy_zero(), False{})
   : SolveRef.Best}:
  +dinner : +List<SolveFast.Item> =
    List.append(&2, SolveFast.Item, SolveFast.group_items(n, drest),
      SolveFast.End{} <> rest)
  +dkids : +List<Tree.Child> =
    Tree.Child{dfb, Eval.Eval.tree_of(SolveFast.dummy_zero())} <> kids
  +dsum : Nat =
    SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(SolveFast.dummy_zero()))
  +drhs : SolveRef.Best =
    SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n, best,
      SolveFast.dummy_zero(), False{})
  Equal.trans(SolveRef.Best,
    SolveFast.step(1n+p, gs,
      SolveFast.ClassItem{dfb, dws} <> (SolveFast.Add{dfb} <> dinner),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{}),
    SolveFast.step(1n+p, gs, dinner, G, S, inf, g, dkids, dsum, best,
      SolveFast.dummy_zero(), True{}),
    drhs,
    FS.class_add_dead(p, gs, G, S, inf, g, dfb, dws, dinner, kids, sum, best),
    FS.block_dead(p, gs, G, S, n, inf, g, drest, dkids, dsum, best, rest))
