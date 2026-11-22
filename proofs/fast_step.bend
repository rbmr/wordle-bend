# Computation lemmas for the pruned search machine (`src/solve_fast.bend`).
#
# `SolveFast.step` runs one state machine driven by a staged guess queue
# `gs: GList`, a single-step unpack phase `phase`, a current guess schedule
# `cs`, and a root-allocated `Buf5` threaded linearly through `StepRes`.
# This module proves the single-step computation equations that `proofs/fast_opt.bend`
# uses to walk schedules: popping the next guess, crossing `GThen`, exiting on
# `done`, unpacking `GuessRes`, stepping `Begin`/`ClassItem`/`OneItem`/`TwoItem`/
# `DoneItem`/`Add`/`End`, and skipping dead blocks (`FS.items_dead`).
import Base
import ../src/solve_fast.bend as SolveFast
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./eval.bend as Eval
import ./nat.bend as NatProof
import ./sat.bend as Sat
import ./logic.bend as Logic

# The pruned child search from an arbitrary starting accumulator `best0` and
# threaded buffer `buf0`.
def FS.run_child_from(+fuel: Nat, +inf: Nat, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +nodup: Bool, +best0: SolveRef.Best,
    buf0: SolveFast.Buf5) -> SolveFast.StepRes:
  +n : Nat = Groups.len_words(SolveFast.cwords_words(S))
  +fl : Nat = SolveFast.init_floor(n)
  SolveFast.step(fuel, SolveFast.child_glist(nodup, S, n, best0, gG),
    0n, Nil{}, gG, S, n, nodup, fl, inf,
    Nil{}, Nil{}, 0n, best0, SolveFast.dummy_step_zero(), False{},
    SolveFast.is_floor_hit(nodup, fl, best0),
    SolveFast.GuessRes{Nil{}, buf0})

# The pruned root search from an arbitrary starting accumulator `best0` and
# threaded buffer `buf0`.
def FS.run_root_from(+fuel: Nat, +inf: Nat, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +nodup: Bool, +best0: SolveRef.Best,
    buf0: SolveFast.Buf5) -> SolveFast.StepRes:
  +n : Nat = Groups.len_words(SolveFast.cwords_words(S))
  +fl : Nat = SolveFast.init_floor(n)
  SolveFast.step(fuel, gG, 0n, Nil{}, gG, S, n, nodup, fl, inf,
    Nil{}, Nil{}, 0n, best0, SolveFast.dummy_step_zero(), False{},
    SolveFast.is_floor_hit(nodup, fl, best0),
    SolveFast.GuessRes{Nil{}, buf0})

# The reference search from its canonical start state (the term `solve_ref` runs).
def FS.ref_run_at(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>) -> SolveRef.Best:
  SolveRef.step(fuel, SolveRef.mk_schedule(G, S), G, S, inf,
    Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())

# Early node exit when `done == True{}` and `cs == Nil{}`.
def FS.done_exit(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +best: SolveRef.Best, -gres: SolveFast.GuessRes) ->
  {SolveFast.step(1n+p, gs, 0n, Nil{}, gG, S, n, nodup, floor, inf,
     Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, True{}, gres)
   == SolveFast.StepRes{best, SolveFast.gres_buf(gres)} : SolveFast.StepRes}:
  match gs:
    case SolveFast.GEnd{}:
      {==}
    case SolveFast.GThen{grest}:
      {==}
    case SolveFast.GTry{row2, g2, grest}:
      {==}

# Exiting at `GEnd{}` with `cs == Nil{}` regardless of `done`.
def FS.gend_exit(+p: Nat, +gG: SolveFast.GList, +S: +List<SolveFast.CWord>,
    +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat, +best: SolveRef.Best,
    +done: Bool, -gres: SolveFast.GuessRes) ->
  {SolveFast.step(1n+p, SolveFast.GEnd{}, 0n, Nil{}, gG, S, n, nodup, floor, inf,
     Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, done, gres)
   == SolveFast.StepRes{best, SolveFast.gres_buf(gres)} : SolveFast.StepRes}:
  {==}

# Crossing `GThen` raises the early-exit floor to `2*n` and preserves `gres`.
def FS.gthen_step(+p: Nat, +grest: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +best: SolveRef.Best, -gres: SolveFast.GuessRes) ->
  {SolveFast.step(1n+p, SolveFast.GThen{grest}, 0n, Nil{}, gG, S, n, nodup,
     floor, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
     False{}, gres)
   == SolveFast.step(1n+p, grest, 0n, Nil{}, gG, S, n, nodup, Nat.add(n, n),
        inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nodup, Nat.add(n, n), best), gres)
   : SolveFast.StepRes}:
  {==}

# Popping the next guess at positive fuel when `cs` is empty and `done = False{}`.
def FS.pop_guess_succ(+p: Nat, +row2: U32, +g2: +List<Nat>,
    +grest: SolveFast.GList, +gG: SolveFast.GList, +S: +List<SolveFast.CWord>,
    +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat, +best: SolveRef.Best,
    -buf: SolveFast.Buf5) ->
  {SolveFast.step(1n+p, SolveFast.GTry{row2, g2, grest}, 0n, Nil{}, gG, S, n,
     nodup, floor, inf, Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(),
     False{}, False{}, SolveFast.GuessRes{Nil{}, buf})
   == SolveFast.step(1n+p, grest, 1n, Nil{}, gG, S, n, nodup, floor, inf,
        Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, False{},
        SolveFast.guess_items_buf(nodup, row2, g2, S, n, floor, best, buf))
   : SolveFast.StepRes}:
  {==}

# Unpacking a `GuessRes{items, buf2}` on `phase = 1n` into `cs = items`.
def FS.unpack_gres_succ(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +best: SolveRef.Best, +items: +List<SolveFast.Item>,
    -buf2: SolveFast.Buf5) ->
  {SolveFast.step(1n+p, gs, 1n, Nil{}, gG, S, n, nodup, floor, inf,
     Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, False{},
     SolveFast.GuessRes{items, buf2})
   == SolveFast.step(1n+p, gs, 0n, items, gG, S, n, nodup, floor, inf,
        Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, False{},
        SolveFast.GuessRes{Nil{}, buf2})
   : SolveFast.StepRes}:
  match gs:
    case SolveFast.GEnd{}:
      {==}
    case SolveFast.GThen{gt}:
      {==}
    case SolveFast.GTry{rh, gh, gt}:
      {==}

# `Begin` at positive fuel resets the guess and class accumulator.
def FS.begin_succ(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +g2: +List<Nat>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, -pending: SolveFast.StepRes, +skip: Bool, +done: Bool,
    +rest: +List<SolveFast.Item>, -gres: SolveFast.GuessRes) ->
  {SolveFast.step(1n+p, gs, 0n, SolveFast.Begin{g2} <> rest, gG, S, n, nodup,
     floor, inf, g, kids, sum, best, pending, skip, done, gres)
   == SolveFast.step(1n+p, gs, 0n, rest, gG, S, n, nodup, floor, inf, g2,
        Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, False{}, gres)
   : SolveFast.StepRes}:
  match gs:
    case SolveFast.GEnd{}:
      {==}
    case SolveFast.GThen{gt}:
      {==}
    case SolveFast.GTry{rh, gh, gt}:
      {==}

# The child cutoff for a live class item with remaining lower bound `tail_lb`.
def FS.child_cutoff(+best: SolveRef.Best, +sum: Nat, +tail_lb: Nat) -> Nat:
  Nat.sub(SolveFast.best_cost(best), Nat.add(sum, tail_lb))

# A skipped `ClassItem` leaves `kids`, `sum`, and `gres` unchanged.
def FS.class_dead(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +ws: +List<SolveFast.CWord>,
    +wlen: Nat, +tail_lb: Nat, +rest: +List<SolveFast.Item>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    -gres: SolveFast.GuessRes) ->
  {SolveFast.step(1n+p, gs, 0n,
      SolveFast.ClassItem{fb, ws, wlen, tail_lb} <> rest,
      gG, S, n, nodup, floor, inf, g, kids, sum, best,
      SolveFast.dummy_step_zero(), True{}, False{}, gres)
   == SolveFast.step(1n+p, gs, 0n, rest, gG, S, n, nodup, floor, inf, g, kids,
        sum, best, SolveFast.dummy_step_zero(), True{}, False{}, gres)
   : SolveFast.StepRes}:
  match gs:
    case SolveFast.GEnd{}:
      {==}
    case SolveFast.GThen{gt}:
      {==}
    case SolveFast.GTry{rh, gh, gt}:
      {==}

# A live `ClassItem` passes `buf` into the child search and stores its `StepRes`
# in `pending`.
def FS.class_live(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +ws: +List<SolveFast.CWord>,
    +wlen: Nat, +tail_lb: Nat, +rest: +List<SolveFast.Item>,
    +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    +old_items: +List<SolveFast.Item>, -buf: SolveFast.Buf5) ->
  {SolveFast.step(1n+p, gs, 0n,
      SolveFast.ClassItem{fb, ws, wlen, tail_lb} <> rest,
      gG, S, n, nodup, floor, inf, g, kids, sum, best,
      SolveFast.dummy_step_zero(), False{}, False{},
      SolveFast.GuessRes{old_items, buf})
   == SolveFast.step(1n+p, gs, 0n, rest, gG, S, n, nodup, floor, inf, g, kids,
        sum, best,
        SolveFast.step(p,
          SolveFast.child_glist(nodup, ws, wlen,
            SolveFast.dummy_inf(FS.child_cutoff(best, sum, tail_lb)), gG),
          0n, Nil{}, gG, ws, wlen, nodup, SolveFast.init_floor(wlen), inf,
          Nil{}, Nil{}, 0n,
          SolveFast.dummy_inf(FS.child_cutoff(best, sum, tail_lb)),
          SolveFast.dummy_step_zero(), False{},
          SolveFast.is_floor_hit(nodup, SolveFast.init_floor(wlen),
            SolveFast.dummy_inf(FS.child_cutoff(best, sum, tail_lb))),
          SolveFast.GuessRes{Nil{}, buf}),
        False{}, False{}, SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}})
   : SolveFast.StepRes}:
  match gs:
    case SolveFast.GEnd{}:
      {==}
    case SolveFast.GThen{gt}:
      {==}
    case SolveFast.GTry{rh, gh, gt}:
      {==}

# `Add` in a skipped block ignores `pending` and keeps `skip = True{}` and `gres`.
def FS.add_dead(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +tail_lb: Nat,
    +rest: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +pbest: SolveRef.Best, -pbuf: SolveFast.Buf5,
    -gres: SolveFast.GuessRes) ->
  {SolveFast.step(1n+p, gs, 0n, SolveFast.Add{fb, tail_lb} <> rest, gG, S, n,
      nodup, floor, inf, g, kids, sum, best, SolveFast.StepRes{pbest, pbuf},
      True{}, False{}, gres)
   == SolveFast.step(1n+p, gs, 0n, rest, gG, S, n, nodup, floor, inf, g, kids,
        sum, best, SolveFast.dummy_step_zero(), True{}, False{}, gres)
   : SolveFast.StepRes}:
  match gs:
    case SolveFast.GEnd{}:
      match pbest:
        case SolveRef.Best{tree, cost}:
          {==}
    case SolveFast.GThen{gt}:
      match pbest:
        case SolveRef.Best{tree, cost}:
          {==}
    case SolveFast.GTry{rh, gh, gt}:
      match pbest:
        case SolveRef.Best{tree, cost}:
          {==}

# `Add` in a live block consumes `pending` (`StepRes{pbest, pbuf}`), updates
# `skip` from `sum2 + tail_lb`, and restores `pbuf` into `gres`.
def FS.after_child_res(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +tail_lb: Nat,
    +rest: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, pending: SolveFast.StepRes) -> SolveFast.StepRes:
  match pending:
    case SolveFast.StepRes{pbest, pbuf}:
      match pbest:
        case SolveRef.Best{+tree, +cost}:
          +sum2 : Nat = SolveRef.sat_add(inf, sum, cost)
          SolveFast.step(1n+p, gs, 0n, rest, gG, S, n, nodup, floor, inf, g,
            Tree.Child{fb, tree} <> kids, sum2, best,
            SolveFast.dummy_step_zero(),
            SolveFast.skippable(best, Nat.add(sum2, tail_lb)),
            False{}, SolveFast.GuessRes{Nil{}, pbuf})

def FS.add_live_step(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +tail_lb: Nat,
    +rest: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, pending: SolveFast.StepRes,
    -gres: SolveFast.GuessRes) ->
  {SolveFast.step(1n+p, gs, 0n, SolveFast.Add{fb, tail_lb} <> rest, gG, S, n,
      nodup, floor, inf, g, kids, sum, best, pending, False{}, False{}, gres)
   == FS.after_child_res(p, gs, gG, S, n, nodup, floor, inf, g, fb, tail_lb,
        rest, kids, sum, best, pending)
   : SolveFast.StepRes}:
  match gs:
    case SolveFast.GEnd{}:
      match pending:
        case SolveFast.StepRes{pbest, pbuf}:
          match pbest:
            case SolveRef.Best{tree, cost}:
              {==}
    case SolveFast.GThen{gt}:
      match pending:
        case SolveFast.StepRes{pbest, pbuf}:
          match pbest:
            case SolveRef.Best{tree, cost}:
              {==}
    case SolveFast.GTry{rh, gh, gt}:
      match pending:
        case SolveFast.StepRes{pbest, pbuf}:
          match pbest:
            case SolveRef.Best{tree, cost}:
              {==}

def FS.after_child_res_eq(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +tail_lb: Nat,
    +rest: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, +pbest: SolveRef.Best, -pbuf: SolveFast.Buf5) ->
  {FS.after_child_res(p, gs, gG, S, n, nodup, floor, inf, g, fb, tail_lb, rest,
      kids, sum, best, SolveFast.StepRes{pbest, pbuf})
   == SolveFast.step(1n+p, gs, 0n, rest, gG, S, n, nodup, floor, inf, g,
        Tree.Child{fb, Eval.Eval.tree_of(pbest)} <> kids,
        SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(pbest)), best,
        SolveFast.dummy_step_zero(),
        SolveFast.skippable(best,
          Nat.add(SolveRef.sat_add(inf, sum, Eval.Eval.cost_of(pbest)),
            tail_lb)),
        False{}, SolveFast.GuessRes{Nil{}, pbuf})
   : SolveFast.StepRes}:
  match pbest:
    case SolveRef.Best{tree, cost}:
      {==}

# Combined live `ClassItem` + `Add` step.
def FS.class_add_live(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +ws: +List<SolveFast.CWord>,
    +tail_lb: Nat, +inner: +List<SolveFast.Item>, +kids: +List<Tree.Child>,
    +sum: Nat, +best: SolveRef.Best, buf: SolveFast.Buf5) ->
  {SolveFast.step(1n+p, gs, 0n,
      SolveFast.ClassItem{fb, ws, Groups.len_words(SolveFast.cwords_words(ws)),
        tail_lb}
        <> (SolveFast.Add{fb, tail_lb} <> inner),
      gG, S, n, nodup, floor, inf, g, kids, sum, best,
      SolveFast.dummy_step_zero(), False{}, False{},
      SolveFast.GuessRes{Nil{}, buf})
   == FS.after_child_res(p, gs, gG, S, n, nodup, floor, inf, g, fb, tail_lb,
        inner, kids, sum, best,
        FS.run_child_from(p, inf, gG, ws, nodup,
          SolveFast.dummy_inf(FS.child_cutoff(best, sum, tail_lb)), buf))
   : SolveFast.StepRes}:
  +wlen : Nat = Groups.len_words(SolveFast.cwords_words(ws))
  Equal.trans(SolveFast.StepRes,
    SolveFast.step(1n+p, gs, 0n,
      SolveFast.ClassItem{fb, ws, wlen, tail_lb}
        <> (SolveFast.Add{fb, tail_lb} <> inner),
      gG, S, n, nodup, floor, inf, g, kids, sum, best,
      SolveFast.dummy_step_zero(), False{}, False{},
      SolveFast.GuessRes{Nil{}, buf}),
    SolveFast.step(1n+p, gs, 0n, SolveFast.Add{fb, tail_lb} <> inner, gG, S, n,
      nodup, floor, inf, g, kids, sum, best,
      FS.run_child_from(p, inf, gG, ws, nodup,
        SolveFast.dummy_inf(FS.child_cutoff(best, sum, tail_lb)), buf),
      False{}, False{}, SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}}),
    FS.after_child_res(p, gs, gG, S, n, nodup, floor, inf, g, fb, tail_lb,
      inner, kids, sum, best,
      FS.run_child_from(p, inf, gG, ws, nodup,
        SolveFast.dummy_inf(FS.child_cutoff(best, sum, tail_lb)), buf)),
    FS.class_live(p, gs, gG, S, n, nodup, floor, inf, g, fb, ws, wlen, tail_lb,
      SolveFast.Add{fb, tail_lb} <> inner, kids, sum, best, Nil{}, buf),
    FS.add_live_step(p, gs, gG, S, n, nodup, floor, inf, g, fb, tail_lb, inner,
      kids, sum, best,
      FS.run_child_from(p, inf, gG, ws, nodup,
        SolveFast.dummy_inf(FS.child_cutoff(best, sum, tail_lb)), buf),
      SolveFast.GuessRes{Nil{}, SolveFast.NoBuf{}}))

# The state after `End`, in both modes.
def FS.after_end(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    +rest: +List<SolveFast.Item>, skip: Bool, gres: SolveFast.GuessRes) ->
  SolveFast.StepRes:
  match skip:
    case True{}:
      SolveFast.step(1n+p, gs, 0n, rest, gG, S, n, nodup, floor, inf, Nil{},
        Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, False{}, gres)
    case False{}:
      +best2 : SolveRef.Best = SolveRef.finish_guess(inf, g, kids, sum, n, best)
      SolveFast.step(1n+p, gs, 0n, rest, gG, S, n, nodup, floor, inf, Nil{},
        Nil{}, 0n, best2, SolveFast.dummy_step_zero(), False{},
        SolveFast.is_floor_hit(nodup, floor, best2), gres)

def FS.end_step(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +kids: +List<Tree.Child>, +sum: Nat, +best: SolveRef.Best,
    -pending: SolveFast.StepRes, +rest: +List<SolveFast.Item>, +skip: Bool,
    -gres: SolveFast.GuessRes) ->
  {SolveFast.step(1n+p, gs, 0n, SolveFast.End{} <> rest, gG, S, n, nodup,
      floor, inf, g, kids, sum, best, pending, skip, False{}, gres)
   == FS.after_end(p, gs, gG, S, n, nodup, floor, inf, g, kids, sum, best, rest,
        skip, gres)
   : SolveFast.StepRes}:
  match gs:
    case SolveFast.GEnd{}:
      match skip:
        case True{}:
          {==}
        case False{}:
          {==}
    case SolveFast.GThen{gt}:
      match skip:
        case True{}:
          {==}
        case False{}:
          {==}
    case SolveFast.GTry{rh, gh, gt}:
      match skip:
        case True{}:
          {==}
        case False{}:
          {==}

# `OneItem`, `TwoItem`, and `DoneItem` in skipped and live modes.
def FS.one_dead(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +dfb: +List<Feedback.Color>, +dw: +List<Nat>,
    +dinner: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, -gres: SolveFast.GuessRes) ->
  {SolveFast.step(1n+p, gs, 0n, SolveFast.OneItem{dfb, dw} <> dinner,
      gG, S, n, nodup, floor, inf, g, kids, sum, best,
      SolveFast.dummy_step_zero(), True{}, False{}, gres)
   == SolveFast.step(1n+p, gs, 0n, dinner, gG, S, n, nodup, floor, inf, g, kids,
        sum, best, SolveFast.dummy_step_zero(), True{}, False{}, gres)
   : SolveFast.StepRes}:
  match gs:
    case SolveFast.GEnd{}:
      {==}
    case SolveFast.GThen{gt}:
      {==}
    case SolveFast.GTry{rh, gh, gt}:
      {==}

def FS.one_live(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +w: +List<Nat>,
    +inner: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, -gres: SolveFast.GuessRes) ->
  {SolveFast.step(1n+p, gs, 0n, SolveFast.OneItem{fb, w} <> inner,
      gG, S, n, nodup, floor, inf, g, kids, sum, best,
      SolveFast.dummy_step_zero(), False{}, False{}, gres)
   == SolveFast.step(1n+p, gs, 0n, inner, gG, S, n, nodup, floor, inf, g,
        Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
        SolveRef.sat_add(inf, sum, 1n), best,
        SolveFast.dummy_step_zero(), False{}, False{}, gres)
   : SolveFast.StepRes}:
  match gs:
    case SolveFast.GEnd{}:
      {==}
    case SolveFast.GThen{gt}:
      {==}
    case SolveFast.GTry{rh, gh, gt}:
      {==}

def FS.two_dead(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +dfb: +List<Feedback.Color>, +dw1: +List<Nat>,
    +dw2: +List<Nat>, +dinner: +List<SolveFast.Item>, +kids: +List<Tree.Child>,
    +sum: Nat, +best: SolveRef.Best, -gres: SolveFast.GuessRes) ->
  {SolveFast.step(1n+p, gs, 0n, SolveFast.TwoItem{dfb, dw1, dw2} <> dinner,
      gG, S, n, nodup, floor, inf, g, kids, sum, best,
      SolveFast.dummy_step_zero(), True{}, False{}, gres)
   == SolveFast.step(1n+p, gs, 0n, dinner, gG, S, n, nodup, floor, inf, g, kids,
        sum, best, SolveFast.dummy_step_zero(), True{}, False{}, gres)
   : SolveFast.StepRes}:
  match gs:
    case SolveFast.GEnd{}:
      {==}
    case SolveFast.GThen{gt}:
      {==}
    case SolveFast.GTry{rh, gh, gt}:
      {==}

def FS.two_live(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +w1: +List<Nat>,
    +w2: +List<Nat>, +inner: +List<SolveFast.Item>, +kids: +List<Tree.Child>,
    +sum: Nat, +best: SolveRef.Best, -gres: SolveFast.GuessRes) ->
  {SolveFast.step(1n+p, gs, 0n, SolveFast.TwoItem{fb, w1, w2} <> inner,
      gG, S, n, nodup, floor, inf, g, kids, sum, best,
      SolveFast.dummy_step_zero(), False{}, False{}, gres)
   == SolveFast.step(1n+p, gs, 0n, inner, gG, S, n, nodup, floor, inf, g,
        Tree.Child{fb, SolveFast.two_tree(w1, w2)} <> kids,
        SolveRef.sat_add(inf, sum, 3n), best,
        SolveFast.dummy_step_zero(), False{}, False{}, gres)
   : SolveFast.StepRes}:
  match gs:
    case SolveFast.GEnd{}:
      {==}
    case SolveFast.GThen{gt}:
      {==}
    case SolveFast.GTry{rh, gh, gt}:
      {==}

def FS.done_dead(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +dfb: +List<Feedback.Color>, +dtree: Tree.Tree, +dcost: Nat,
    +dinner: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, -gres: SolveFast.GuessRes) ->
  {SolveFast.step(1n+p, gs, 0n, SolveFast.DoneItem{dfb, dtree, dcost} <> dinner,
      gG, S, n, nodup, floor, inf, g, kids, sum, best,
      SolveFast.dummy_step_zero(), True{}, False{}, gres)
   == SolveFast.step(1n+p, gs, 0n, dinner, gG, S, n, nodup, floor, inf, g, kids,
        sum, best, SolveFast.dummy_step_zero(), True{}, False{}, gres)
   : SolveFast.StepRes}:
  match gs:
    case SolveFast.GEnd{}:
      {==}
    case SolveFast.GThen{gt}:
      {==}
    case SolveFast.GTry{rh, gh, gt}:
      {==}

def FS.done_live(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +tree: Tree.Tree, +cost: Nat,
    +inner: +List<SolveFast.Item>, +kids: +List<Tree.Child>, +sum: Nat,
    +best: SolveRef.Best, -gres: SolveFast.GuessRes) ->
  {SolveFast.step(1n+p, gs, 0n, SolveFast.DoneItem{fb, tree, cost} <> inner,
      gG, S, n, nodup, floor, inf, g, kids, sum, best,
      SolveFast.dummy_step_zero(), False{}, False{}, gres)
   == SolveFast.step(1n+p, gs, 0n, inner, gG, S, n, nodup, floor, inf, g,
        Tree.Child{fb, tree} <> kids,
        SolveRef.sat_add(inf, sum, cost), best,
        SolveFast.dummy_step_zero(), False{}, False{}, gres)
   : SolveFast.StepRes}:
  match gs:
    case SolveFast.GEnd{}:
      {==}
    case SolveFast.GThen{gt}:
      {==}
    case SolveFast.GTry{rh, gh, gt}:
      {==}

# Generic skipped-block lemma: any list of body items (`ClassItem`, `Add`,
# `OneItem`, `TwoItem`, `DoneItem`) followed by `End{} <> rest` is skipped
# cleanly with `best` and `gres` preserved.
def FS.dead_body_b(+items: +List<SolveFast.Item>) -> Bool:
  match items:
    case Nil{}:
      True{}
    case Con{it, t}:
      match it:
        case SolveFast.Begin{g}:
          False{}
        case SolveFast.ClassItem{fb, ws, wlen, tlb}:
          FS.dead_body_b(t)
        case SolveFast.OneItem{fb, w}:
          FS.dead_body_b(t)
        case SolveFast.TwoItem{fb, w1, w2}:
          FS.dead_body_b(t)
        case SolveFast.DoneItem{fb, tr, c}:
          FS.dead_body_b(t)
        case SolveFast.Add{fb, tlb}:
          FS.dead_body_b(t)
        case SolveFast.End{}:
          False{}

def FS.items_dead(+p: Nat, +gs: SolveFast.GList, +gG: SolveFast.GList,
    +S: +List<SolveFast.CWord>, +n: Nat, +nodup: Bool, +floor: Nat, +inf: Nat,
    +g: +List<Nat>, +body: +List<SolveFast.Item>, +kids: +List<Tree.Child>,
    +sum: Nat, +best: SolveRef.Best, +rest: +List<SolveFast.Item>,
    +hb: {FS.dead_body_b(body) == True{} : Bool},
    -gres: SolveFast.GuessRes) ->
  {SolveFast.step(1n+p, gs, 0n,
      List.append(&2, SolveFast.Item, body, SolveFast.End{} <> rest),
      gG, S, n, nodup, floor, inf, g, kids, sum, best,
      SolveFast.dummy_step_zero(), True{}, False{}, gres)
   == SolveFast.step(1n+p, gs, 0n, rest, gG, S, n, nodup, floor, inf, Nil{},
        Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{}, False{}, gres)
   : SolveFast.StepRes}:
  match body:
    case Nil{}:
      FS.end_step(p, gs, gG, S, n, nodup, floor, inf, g, kids, sum, best,
        SolveFast.dummy_step_zero(), rest, True{}, gres)
    case Con{it, t}:
      match it:
        case SolveFast.Begin{g2}:
          Empty.absurd(
            {SolveFast.step(1n+p, gs, 0n,
                SolveFast.Begin{g2}
                <> List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
                gG, S, n, nodup, floor, inf, g, kids, sum, best,
                SolveFast.dummy_step_zero(), True{}, False{}, gres)
             == SolveFast.step(1n+p, gs, 0n, rest, gG, S, n, nodup, floor, inf,
                  Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
                  False{}, gres) : SolveFast.StepRes},
            Logic.Proof.false_ne_true(hb))
        case SolveFast.ClassItem{+fb, +ws, +wlen, +tlb}:
          Equal.trans(SolveFast.StepRes,
            SolveFast.step(1n+p, gs, 0n,
              SolveFast.ClassItem{fb, ws, wlen, tlb}
              <> List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
              gG, S, n, nodup, floor, inf, g, kids, sum, best,
              SolveFast.dummy_step_zero(), True{}, False{}, gres),
            SolveFast.step(1n+p, gs, 0n,
              List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
              gG, S, n, nodup, floor, inf, g, kids, sum, best,
              SolveFast.dummy_step_zero(), True{}, False{}, gres),
            SolveFast.step(1n+p, gs, 0n, rest, gG, S, n, nodup, floor, inf,
              Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
              False{}, gres),
            FS.class_dead(p, gs, gG, S, n, nodup, floor, inf, g, fb, ws, wlen,
              tlb, List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
              kids, sum, best, gres),
            FS.items_dead(p, gs, gG, S, n, nodup, floor, inf, g, t, kids, sum,
              best, rest, hb, gres))
        case SolveFast.OneItem{+fb, +w}:
          Equal.trans(SolveFast.StepRes,
            SolveFast.step(1n+p, gs, 0n,
              SolveFast.OneItem{fb, w}
              <> List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
              gG, S, n, nodup, floor, inf, g, kids, sum, best,
              SolveFast.dummy_step_zero(), True{}, False{}, gres),
            SolveFast.step(1n+p, gs, 0n,
              List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
              gG, S, n, nodup, floor, inf, g, kids, sum, best,
              SolveFast.dummy_step_zero(), True{}, False{}, gres),
            SolveFast.step(1n+p, gs, 0n, rest, gG, S, n, nodup, floor, inf,
              Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
              False{}, gres),
            FS.one_dead(p, gs, gG, S, n, nodup, floor, inf, g, fb, w,
              List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
              kids, sum, best, gres),
            FS.items_dead(p, gs, gG, S, n, nodup, floor, inf, g, t, kids, sum,
              best, rest, hb, gres))
        case SolveFast.TwoItem{+fb, +w1, +w2}:
          Equal.trans(SolveFast.StepRes,
            SolveFast.step(1n+p, gs, 0n,
              SolveFast.TwoItem{fb, w1, w2}
              <> List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
              gG, S, n, nodup, floor, inf, g, kids, sum, best,
              SolveFast.dummy_step_zero(), True{}, False{}, gres),
            SolveFast.step(1n+p, gs, 0n,
              List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
              gG, S, n, nodup, floor, inf, g, kids, sum, best,
              SolveFast.dummy_step_zero(), True{}, False{}, gres),
            SolveFast.step(1n+p, gs, 0n, rest, gG, S, n, nodup, floor, inf,
              Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
              False{}, gres),
            FS.two_dead(p, gs, gG, S, n, nodup, floor, inf, g, fb, w1, w2,
              List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
              kids, sum, best, gres),
            FS.items_dead(p, gs, gG, S, n, nodup, floor, inf, g, t, kids, sum,
              best, rest, hb, gres))
        case SolveFast.DoneItem{+fb, +tr, +c}:
          Equal.trans(SolveFast.StepRes,
            SolveFast.step(1n+p, gs, 0n,
              SolveFast.DoneItem{fb, tr, c}
              <> List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
              gG, S, n, nodup, floor, inf, g, kids, sum, best,
              SolveFast.dummy_step_zero(), True{}, False{}, gres),
            SolveFast.step(1n+p, gs, 0n,
              List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
              gG, S, n, nodup, floor, inf, g, kids, sum, best,
              SolveFast.dummy_step_zero(), True{}, False{}, gres),
            SolveFast.step(1n+p, gs, 0n, rest, gG, S, n, nodup, floor, inf,
              Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
              False{}, gres),
            FS.done_dead(p, gs, gG, S, n, nodup, floor, inf, g, fb, tr, c,
              List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
              kids, sum, best, gres),
            FS.items_dead(p, gs, gG, S, n, nodup, floor, inf, g, t, kids, sum,
              best, rest, hb, gres))
        case SolveFast.Add{+fb, +tlb}:
          Equal.trans(SolveFast.StepRes,
            SolveFast.step(1n+p, gs, 0n,
              SolveFast.Add{fb, tlb}
              <> List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
              gG, S, n, nodup, floor, inf, g, kids, sum, best,
              SolveFast.dummy_step_zero(), True{}, False{}, gres),
            SolveFast.step(1n+p, gs, 0n,
              List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
              gG, S, n, nodup, floor, inf, g, kids, sum, best,
              SolveFast.dummy_step_zero(), True{}, False{}, gres),
            SolveFast.step(1n+p, gs, 0n, rest, gG, S, n, nodup, floor, inf,
              Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
              False{}, gres),
            FS.add_dead(p, gs, gG, S, n, nodup, floor, inf, g, fb, tlb,
              List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
              kids, sum, best, SolveFast.dummy_zero(), SolveFast.NoBuf{}, gres),
            FS.items_dead(p, gs, gG, S, n, nodup, floor, inf, g, t, kids, sum,
              best, rest, hb, gres))
        case SolveFast.End{}:
          Empty.absurd(
            {SolveFast.step(1n+p, gs, 0n,
                SolveFast.End{}
                <> List.append(&2, SolveFast.Item, t, SolveFast.End{} <> rest),
                gG, S, n, nodup, floor, inf, g, kids, sum, best,
                SolveFast.dummy_step_zero(), True{}, False{}, gres)
             == SolveFast.step(1n+p, gs, 0n, rest, gG, S, n, nodup, floor, inf,
                  Nil{}, Nil{}, 0n, best, SolveFast.dummy_step_zero(), False{},
                  False{}, gres) : SolveFast.StepRes},
            Logic.Proof.false_ne_true(hb))

def FS.dead_body_group_items_two(nodup: Bool, +n: Nat,
    +fb: +List<Feedback.Color>, +w: +List<Nat>, +w2: +List<Nat>,
    +rest: +List<Groups.Group>, +tail: +List<SolveFast.Item>,
    +ht: {FS.dead_body_b(tail) == True{} : Bool}) ->
  {FS.dead_body_b(SolveFast.group_items_two(nodup, n, fb, w, w2, rest, tail))
   == True{} : Bool}:
  match nodup:
    case True{}:
      ht
    case False{}:
      ht

def FS.dead_body_group_items(+nodup: Bool, +n: Nat,
    +groups: +List<Groups.Group>) ->
  {FS.dead_body_b(SolveFast.group_items(nodup, n, groups)) == True{} : Bool}:
  match groups:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+fb, +ws}:
          match ws:
            case Nil{}:
              FS.dead_body_group_items(nodup, n, rest)
            case Con{+w, +wt}:
              match wt:
                case Nil{}:
                  FS.dead_body_group_items(nodup, n, rest)
                case Con{+w2, +wt2}:
                  match wt2:
                    case Nil{}:
                      FS.dead_body_group_items_two(nodup, n, fb, w, w2, rest,
                        SolveFast.group_items(nodup, n, rest),
                        FS.dead_body_group_items(nodup, n, rest))
                    case Con{+w3, +wt3}:
                      FS.dead_body_group_items(nodup, n, rest)
