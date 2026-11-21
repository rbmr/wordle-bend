# Computation lemmas for the pruned search machine.
#
# `src/solve_fast.bend` runs one state machine driven by a remaining guess list
# `gs` and a current guess schedule `cs`. This module proves the small
# equations that let the equality proof walk that schedule: popping the next
# guess when `cs` is empty, one step per item kind (including recursive child
# searches started from an arbitrary cutoff accumulator `best0`), and the
# dead-tail lemma when a guess or remaining class suffix is skipped.
import Base
import ../src/solve_fast.bend as SolveFast
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./eval.bend as Eval
import ./nat.bend as NatProof
import ./sat.bend as Sat

# The pruned search from an arbitrary starting accumulator `best0`.
def FS.run_from(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +best0: SolveRef.Best) -> SolveRef.Best:
  SolveFast.step(fuel, G, Nil{}, G, S, inf,
    Nil{}, Nil{}, 0n, best0, SolveFast.dummy_zero(), False{})

# The pruned search from its canonical start state.
def FS.run_at(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>) -> SolveRef.Best:
  FS.run_from(fuel, inf, G, S, SolveFast.dummy_inf(inf))

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

# The child cutoff for a live class item with remaining lower bound `tail_lb`.
def FS.child_cutoff(+best: SolveRef.Best, +sum: Nat, +tail_lb: Nat) -> Nat:
  Nat.sub(SolveFast.best_cost(best), Nat.add(sum, tail_lb))

# The state after a class item, in both modes.
def FS.after_class(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>, +ws: +List<+List<Nat>>,
    +tail_lb: Nat, +rest: +List<SolveFast.Item>, +kids: +List<Tree.Child>,
    +sum: Nat, +best: SolveRef.Best, skip: Bool) -> SolveRef.Best:
  match skip:
    case True{}:
      SolveFast.step(1n+p, gs, rest, G, S, inf, g, kids, sum, best,
        SolveFast.dummy_zero(), True{})
    case False{}:
      SolveFast.step(1n+p, gs, rest, G, S, inf, g, kids, sum, best,
        FS.run_from(p, inf, G, ws,
          SolveFast.dummy_inf(FS.child_cutoff(best, sum, tail_lb))),
        False{})

def FS.class_step(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>, +tail_lb: Nat,
    +rest: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +skip: Bool) ->
  {SolveFast.step(1n+p, gs, SolveFast.ClassItem{fb, ws, tail_lb} <> rest,
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), skip)
   == FS.after_class(p, gs, G, S, inf, g, ws, tail_lb, rest, kids, sum, best,
        skip)
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

# `Add` in a skipped block ignores `pending` and keeps `skip = True{}`.
def FS.add_dead(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +tail_lb: Nat, +rest: +List<SolveFast.Item>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    +pending: SolveRef.Best) ->
  {SolveFast.step(1n+p, gs, SolveFast.Add{fb, tail_lb} <> rest, G, S, inf, g,
      kids, sum, best, pending, True{})
   == SolveFast.step(1n+p, gs, rest, G, S, inf, g, kids, sum, best,
        SolveFast.dummy_zero(), True{})
   : SolveRef.Best}:
  match gs:
    case Nil{}:
      match pending:
        case SolveRef.Best{tree, cost}:
          {==}
    case Con{gh, gt}:
      match pending:
        case SolveRef.Best{tree, cost}:
          {==}

# `Add` in a live block consumes `pending` and updates `skip` from
# `sum2 + tail_lb`.
def FS.add_live_go(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +tail_lb: Nat, +rest: +List<SolveFast.Item>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    pending: SolveRef.Best) -> SolveRef.Best:
  match pending:
    case SolveRef.Best{+tree, +cost}:
      +sum2 : Nat = SolveRef.sat_add(inf, sum, cost)
      SolveFast.step(1n+p, gs, rest, G, S, inf, g,
        Tree.Child{fb, tree} <> kids, sum2, best, SolveFast.dummy_zero(),
        SolveFast.skippable(best, Nat.add(sum2, tail_lb)))

def FS.add_live_step(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +tail_lb: Nat, +rest: +List<SolveFast.Item>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    +pending: SolveRef.Best) ->
  {SolveFast.step(1n+p, gs, SolveFast.Add{fb, tail_lb} <> rest, G, S, inf, g,
      kids, sum, best, pending, False{})
   == FS.add_live_go(p, gs, G, S, inf, g, fb, tail_lb, rest, kids, sum, best,
        pending)
   : SolveRef.Best}:
  match gs:
    case Nil{}:
      match pending:
        case SolveRef.Best{tree, cost}:
          {==}
    case Con{gh, gt}:
      match pending:
        case SolveRef.Best{tree, cost}:
          {==}

def FS.add_live_go_eq(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +tail_lb: Nat, +rest: +List<SolveFast.Item>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    +pending: SolveRef.Best) ->
  {FS.add_live_go(p, gs, G, S, inf, g, fb, tail_lb, rest, kids, sum, best,
      pending)
   == SolveFast.step(1n+p, gs, rest, G, S, inf, g,
        Tree.Child{fb, Eval.Eval.tree_of(pending)} <> kids,
        SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(pending)), best,
        SolveFast.dummy_zero(),
        SolveFast.skippable(best,
          Nat.add(SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(pending)),
            tail_lb)))
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

# A skipped `ClassItem` followed by `Add` leaves `kids` and `sum` unchanged
# and stays in `skip = True{}`.
def FS.class_add_dead(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +dfb: +List<Feedback.Color>, +dws: +List<+List<Nat>>, +dtlb: Nat,
    +dinner: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best) ->
  {SolveFast.step(1n+p, gs,
      SolveFast.ClassItem{dfb, dws, dtlb}
        <> (SolveFast.Add{dfb, dtlb} <> dinner),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{})
   == SolveFast.step(1n+p, gs, dinner, G, S, inf, g, kids, sum, best,
        SolveFast.dummy_zero(), True{})
   : SolveRef.Best}:
  Equal.trans(SolveRef.Best,
    SolveFast.step(1n+p, gs,
      SolveFast.ClassItem{dfb, dws, dtlb}
        <> (SolveFast.Add{dfb, dtlb} <> dinner),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{}),
    SolveFast.step(1n+p, gs, SolveFast.Add{dfb, dtlb} <> dinner, G, S, inf, g,
      kids, sum, best, SolveFast.dummy_zero(), True{}),
    SolveFast.step(1n+p, gs, dinner, G, S, inf, g, kids, sum, best,
      SolveFast.dummy_zero(), True{}),
    FS.class_step(p, gs, G, S, inf, g, dfb, dws, dtlb,
      SolveFast.Add{dfb, dtlb} <> dinner, kids, sum, best, True{}),
    FS.add_dead(p, gs, G, S, inf, g, dfb, dtlb, dinner, kids, sum, best,
      SolveFast.dummy_zero()))

# A live `ClassItem` followed by `Add` searches the class at fuel `p` with the
# tight cutoff accumulator, adds the child and updates `skip` from `sum2 + tail_lb`.
def FS.class_add_live(+p: Nat, +gs: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +g: +List<Nat>,
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>, +tail_lb: Nat,
    +inner: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best) ->
  {SolveFast.step(1n+p, gs,
      SolveFast.ClassItem{fb, ws, tail_lb}
        <> (SolveFast.Add{fb, tail_lb} <> inner),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{})
   == SolveFast.step(1n+p, gs, inner, G, S, inf, g,
        Tree.Child{fb, Eval.Eval.tree_of(
          FS.run_from(p, inf, G, ws,
            SolveFast.dummy_inf(FS.child_cutoff(best, sum, tail_lb))))} <> kids,
        SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(
          FS.run_from(p, inf, G, ws,
            SolveFast.dummy_inf(FS.child_cutoff(best, sum, tail_lb))))),
        best, SolveFast.dummy_zero(),
        SolveFast.skippable(best,
          Nat.add(
            SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(
              FS.run_from(p, inf, G, ws,
                SolveFast.dummy_inf(FS.child_cutoff(best, sum, tail_lb))))),
            tail_lb)))
   : SolveRef.Best}:
  +search : SolveRef.Best =
    FS.run_from(p, inf, G, ws,
      SolveFast.dummy_inf(FS.child_cutoff(best, sum, tail_lb)))
  +kids2 : +List<Tree.Child> =
    Tree.Child{fb, Eval.Eval.tree_of(search)} <> kids
  +sum2 : Nat = SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(search))
  +sk2 : Bool = SolveFast.skippable(best, Nat.add(sum2, tail_lb))
  +lhs1 : SolveRef.Best =
    SolveFast.step(1n+p, gs,
      SolveFast.ClassItem{fb, ws, tail_lb}
        <> (SolveFast.Add{fb, tail_lb} <> inner),
      G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), False{})
  +lhs2 : SolveRef.Best =
    SolveFast.step(1n+p, gs, SolveFast.Add{fb, tail_lb} <> inner, G, S, inf, g,
      kids, sum, best, search, False{})
  +lhs3 : SolveRef.Best =
    FS.add_live_go(p, gs, G, S, inf, g, fb, tail_lb, inner, kids, sum, best,
      search)
  +lhs4 : SolveRef.Best =
    SolveFast.step(1n+p, gs, inner, G, S, inf, g, kids2, sum2, best,
      SolveFast.dummy_zero(), sk2)
  +e12 : {lhs1 == lhs2 : SolveRef.Best} =
    FS.class_step(p, gs, G, S, inf, g, fb, ws, tail_lb,
      SolveFast.Add{fb, tail_lb} <> inner, kids, sum, best, False{})
  +e23 : {lhs2 == lhs3 : SolveRef.Best} =
    FS.add_live_step(p, gs, G, S, inf, g, fb, tail_lb, inner, kids, sum, best,
      search)
  +e34 : {lhs3 == lhs4 : SolveRef.Best} =
    FS.add_live_go_eq(p, gs, G, S, inf, g, fb, tail_lb, inner, kids, sum, best,
      search)
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
              +dtlb : Nat = SolveFast.lower_bound(n, drest)
              +dinner : +List<SolveFast.Item> =
                List.append(&2, SolveFast.Item,
                  SolveFast.group_items(n, drest),
                  SolveFast.End{} <> rest)
              Equal.trans(SolveRef.Best,
                SolveFast.step(1n+p, gs,
                  SolveFast.ClassItem{dfb, Nil{}, dtlb}
                    <> (SolveFast.Add{dfb, dtlb} <> dinner),
                  G, S, inf, g, kids, sum, best, SolveFast.dummy_zero(), True{}),
                SolveFast.step(1n+p, gs, dinner, G, S, inf, g, kids, sum,
                  best, SolveFast.dummy_zero(), True{}),
                SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
                  best, SolveFast.dummy_zero(), False{}),
                FS.class_add_dead(p, gs, G, S, inf, g, dfb, Nil{}, dtlb,
                  dinner, kids, sum, best),
                FS.block_dead(p, gs, G, S, n, inf, g, drest, kids, sum,
                  best, rest))
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
                  +dtlb : Nat = SolveFast.lower_bound(n, drest)
                  +dinner : +List<SolveFast.Item> =
                    List.append(&2, SolveFast.Item,
                      SolveFast.group_items(n, drest),
                      SolveFast.End{} <> rest)
                  Equal.trans(SolveRef.Best,
                    SolveFast.step(1n+p, gs,
                      SolveFast.ClassItem{dfb, dws2, dtlb}
                        <> (SolveFast.Add{dfb, dtlb} <> dinner),
                      G, S, inf, g, kids, sum, best,
                      SolveFast.dummy_zero(), True{}),
                    SolveFast.step(1n+p, gs, dinner, G, S, inf, g, kids, sum,
                      best, SolveFast.dummy_zero(), True{}),
                    SolveFast.step(1n+p, gs, rest, G, S, inf, Nil{}, Nil{}, 0n,
                      best, SolveFast.dummy_zero(), False{}),
                    FS.class_add_dead(p, gs, G, S, inf, g, dfb, dws2, dtlb,
                      dinner, kids, sum, best),
                    FS.block_dead(p, gs, G, S, n, inf, g, drest, kids, sum,
                      best, rest))
