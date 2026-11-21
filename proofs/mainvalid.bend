# Validity of the fused search at every fuel.
#
# `step` returns a `Best` whose cost is either at least infinity or a valid
# tree. The proof is an induction on the fuel. At fuel `1+p` one guess is
# evaluated by the specification fold `Eval.guess` at fuel `p`; the fold over
# the guess list then keeps the invariant. The classes of a guess are searched
# at `p`, so the induction has to hand every class of every guess its own
# result: a single recursive call returns the conjunction over all of them,
# and the per-guess conjunctions are read off by splitting that conjunction.
#
# This module proves the guess step (`guess_ok`), the fuel recursion (`flat`)
# and finally `solve_valid`.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./bestok.bend as BO
import ./children.bend as CH
import ./groupsmeasure.bend as GM
import ./solvevalid.bend as SV

# The class obligations of one guess, only when the guess is usable. An
# unusable guess contributes no class to the schedule, so it needs none.
def MV.OksIf(b: Bool, +p: Nat, +G: +List<+List<Nat>>, +inf: Nat,
    +groups: +List<Groups.Group>) -> Type:
  match b:
    case True{}:
      SV.SV.Oks(p, G, inf, groups)
    case False{}:
      Unit

# `better` keeps the invariant when the candidate is at least infinity.
def MV.better_ge_go(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    +tree: Tree.Tree, +cost: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    b: Bool, +eb: {b == Nat.is_lt(candCost, cost) : Bool},
    ge: {Nat.is_ge(candCost, inf) == True{} : Bool},
    ok: BO.BO.BestOK(inf, SolveRef.Best{tree, cost}, G, S)) ->
  BO.BO.BestOK(inf,
    Feedback.Bool.case(SolveRef.Best, b,
      SolveRef.Best{candTree, candCost}, SolveRef.Best{tree, cost}), G, S):
  match b:
    case True{}:
      Inl{ge}
    case False{}:
      ok

def MV.better_ge_ok(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    best: SolveRef.Best, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    ge: {Nat.is_ge(candCost, inf) == True{} : Bool},
    ok: BO.BO.BestOK(inf, best, G, S)) ->
  BO.BO.BestOK(inf, SolveRef.better(candCost, candTree, best), G, S):
  match best:
    case SolveRef.Best{tree, +cost}:
      MV.better_ge_go(inf, candCost, candTree, tree, cost, G, S,
        Nat.is_lt(candCost, cost), {==}, ge, ok)

# The finished guess at a group fold: the node cost decides whether the
# candidate can be used at all.
def MV.finish_ge_case(+inf: Nat, +p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +kids: +List<Tree.Child>, +sum: Nat,
    best: SolveRef.Best, b: Bool,
    +eb: {b == Nat.is_ge(SolveRef.sat_add(inf, Groups.len_words(S), sum), inf) : Bool},
    +eks: {Eval.KS{kids, sum}
          == Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)
          : Eval.KS},
    wg: Tree.WordIn(g, G),
    oks: SV.SV.Oks(p, G, inf, Groups.groups_build(g, S, Nil{})),
    ok: BO.BO.BestOK(inf, best, G, S)) ->
  BO.BO.BestOK(inf,
    SolveRef.better(SolveRef.sat_add(inf, Groups.len_words(S), sum),
      Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, best), G, S):
  match b:
    case True{}:
      MV.better_ge_ok(inf,
        SolveRef.sat_add(inf, Groups.len_words(S), sum),
        Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, best, G, S,
        Equal.sym(Bool, True{},
          Nat.is_ge(SolveRef.sat_add(inf, Groups.len_words(S), sum), inf), eb),
        ok)
    case False{}:
      +lt : {Nat.is_lt(SolveRef.sat_add(inf, Groups.len_words(S), sum), inf) == True{}
             : Bool} =
        Sat.SB.lt_of_ge_false(SolveRef.sat_add(inf, Groups.len_words(S), sum), inf,
          Equal.sym(Bool, False{},
            Nat.is_ge(SolveRef.sat_add(inf, Groups.len_words(S), sum), inf), eb))
      +eSum : {sum == Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g,
                 Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)) : Nat} =
        Equal.cong(Eval.KS, Nat, Sat.SB.ks_sum, Eval.KS{kids, sum},
          Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf),
          eks)
      +eKids : {kids == SolveRef.rev_kids(
                  CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf), Nil{})
                : +List<Tree.Child>} =
        Equal.trans(+List<Tree.Child>, kids,
          CH.CH.kids_of(Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
          SolveRef.rev_kids(CH.CH.children(p, G, S,
            Groups.groups_build(g, S, Nil{}), inf), Nil{}),
          Equal.cong(Eval.KS, +List<Tree.Child>, CH.CH.kids_of, Eval.KS{kids, sum},
            Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf),
            eks),
          CH.CH.items_kids(p, G, S, g, Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf))
      vc : Tree.Valid(Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, G, S) =
        SV.SV.end_valid(p, G, S, g, inf, kids, sum, lt, oks, eSum, eKids, wg)
      BO.BO.better_ok(inf, SolveRef.sat_add(inf, Groups.len_words(S), sum),
        Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, best, G, S, vc, ok)

# The group fold of one guess leaves the invariant intact.
def MV.finish_go(+inf: Nat, +p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, ks: Eval.KS, best: SolveRef.Best,
    b: Bool,
    +eb: {b == Nat.is_ge(SolveRef.sat_add(inf, Groups.len_words(S),
             Sat.SB.ks_sum(ks)), inf) : Bool},
    +eks: {ks == Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)
           : Eval.KS},
    wg: Tree.WordIn(g, G),
    oks: SV.SV.Oks(p, G, inf, Groups.groups_build(g, S, Nil{})),
    ok: BO.BO.BestOK(inf, best, G, S)) ->
  BO.BO.BestOK(inf, Eval.Eval.finish_ks(inf, g, S, ks, best), G, S):
  match ks:
    case Eval.KS{kids, sum}:
      MV.finish_ge_case(inf, p, G, S, g, kids, sum, best, b, eb, eks, wg, oks, ok)

# The usable-guess branch: `Eval.block` is the group fold.
def MV.guess_ok_go(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, best: SolveRef.Best, b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    wg: Tree.WordIn(g, G),
    oks: MV.OksIf(b, p, G, inf, Groups.groups_build(g, S, Nil{})),
    ok: BO.BO.BestOK(inf, best, G, S)) ->
  BO.BO.BestOK(inf,
    Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf, b, best),
    G, S):
  match b:
    case True{}:
      MV.finish_go(inf, p, G, S, g,
        Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf),
        best,
        Nat.is_ge(SolveRef.sat_add(inf, Groups.len_words(S),
          Sat.SB.ks_sum(Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf))), inf),
        {==}, {==}, wg, oks, ok)
    case False{}:
      ok

# The guess step preserves the invariant.
def MV.guess_ok(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, best: SolveRef.Best,
    b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    wg: Tree.WordIn(g, G),
    oks: MV.OksIf(b, p, G, inf, Groups.groups_build(g, S, Nil{})),
    ok: BO.BO.BestOK(inf, best, G, S)) ->
  BO.BO.BestOK(inf,
    Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf, b, best),
    G, S):
  MV.guess_ok_go(p, G, S, g, inf, best, b, eb, wg, oks, ok)

# The proof obligation for one candidate list at a given fuel.
def MV.Job(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>) -> Type:
  BO.BO.BestOK(inf, SolveRef.step(fuel, SolveRef.mk_schedule(G, S), G, S, inf,
    Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()), G, S)

# The conjunction of the obligations over a list of candidate lists.
def MV.Flat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    jobs: +List<+List<+List<Nat>>>) -> Type:
  match jobs:
    case Nil{}:
      Unit
    case Con{S, t}:
      MV.Job(fuel, inf, G, S) & MV.Flat(fuel, inf, G, t)

# The class lists of one group list, in order.
def MV.next_groups(+groups: +List<Groups.Group>) -> +List<+List<+List<Nat>>>:
  match groups:
    case Nil{}:
      Nil{}
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          ws <> MV.next_groups(t)

# The class lists of one guess, only when the guess is usable.
def MV.classes_b(b: Bool, +groups: +List<Groups.Group>) -> +List<+List<+List<Nat>>>:
  match b:
    case True{}:
      MV.next_groups(groups)
    case False{}:
      Nil{}

def MV.classes(+g: +List<Nat>, +S: +List<+List<Nat>>) -> +List<+List<+List<Nat>>>:
  MV.classes_b(Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
    Groups.groups_build(g, S, Nil{}))

# The class lists of a guess list, in order.
def MV.next_guess(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>)
    -> +List<+List<+List<Nat>>>:
  match G:
    case Nil{}:
      Nil{}
    case Con{g, t}:
      List.append(&2, +List<+List<Nat>>, MV.classes(g, S), MV.next_guess(t, S))

# The classes of every job, in order.
def MV.next_jobs(+G: +List<+List<Nat>>, +jobs: +List<+List<+List<Nat>>>)
    -> +List<+List<+List<Nat>>>:
  match jobs:
    case Nil{}:
      Nil{}
    case Con{S, t}:
      List.append(&2, +List<+List<Nat>>, MV.next_guess(G, S), MV.next_jobs(G, t))

# Eliminate a pair with a continuation, so a computed pair is destructured once.
def MV.use_pair(-R: Type, -A: Type, -B: Type, p: A & B,
    k: A -> B -> R) -> R:
  match p:
    case (a, b):
      k(a, b)

# Split the conjunction at an append.
def MV.flat_append(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +xs: +List<+List<+List<Nat>>>, +ys: +List<+List<+List<Nat>>>,
    f: MV.Flat(fuel, inf, G, List.append(&2, +List<+List<Nat>>, xs, ys))) ->
  MV.Flat(fuel, inf, G, xs) & MV.Flat(fuel, inf, G, ys):
  match xs:
    case Nil{}:
      Tuple{Unit{}, f}
    case Con{S, t}:
      (j, fr) = f
      MV.use_pair(MV.Flat(fuel, inf, G, S <> t) & MV.Flat(fuel, inf, G, ys),
        MV.Flat(fuel, inf, G, t), MV.Flat(fuel, inf, G, ys),
        MV.flat_append(fuel, inf, G, t, ys, fr),
        ft => fys => Tuple{Tuple{j, ft}, fys})

# The class obligations of one group list, read off the conjunction.
def MV.oks_of_flat(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>,
    f: MV.Flat(p, inf, G, MV.next_groups(groups))) -> SV.SV.Oks(p, G, inf, groups):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, t}:
      match gp:
        case Groups.Group{fb, ws}:
          (j, fr) = f
          (j, MV.oks_of_flat(p, inf, G, t, fr))

# The class obligations of a guess, when it is usable.
def MV.oks_if(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +groups: +List<Groups.Group>, b: Bool,
    f: MV.Flat(p, inf, G, MV.classes_b(b, groups))) ->
  MV.OksIf(b, p, G, inf, groups):
  match b:
    case True{}:
      MV.oks_of_flat(p, inf, G, groups, f)
    case False{}:
      Unit{}

# The per-guess class obligations of a guess list.
def MV.ByGs(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    gs: +List<+List<Nat>>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{g, t}:
      MV.OksIf(Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), p, G, inf,
        Groups.groups_build(g, S, Nil{}))
      & MV.ByGs(p, inf, G, S, t)

def MV.by_gs(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +gs: +List<+List<Nat>>,
    f: MV.Flat(p, inf, G, MV.next_guess(gs, S))) -> MV.ByGs(p, inf, G, S, gs):
  match gs:
    case Nil{}:
      Unit{}
    case Con{g, t}:
      MV.use_pair(MV.ByGs(p, inf, G, S, g <> t),
        MV.Flat(p, inf, G, MV.classes(g, S)),
        MV.Flat(p, inf, G, MV.next_guess(t, S)),
        MV.flat_append(p, inf, G, MV.classes(g, S), MV.next_guess(t, S), f),
        fg => ft =>
          Tuple{MV.oks_if(p, inf, G, Groups.groups_build(g, S, Nil{}),
             Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), fg),
           MV.by_gs(p, inf, G, S, t, ft)})

# The guess fold: every guess keeps the invariant.
def MV.guesses_fold(+inf: Nat, +p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>, +best: SolveRef.Best,
    f: MV.ByGs(p, inf, G, S, gs),
    every: BO.BO.EveryIn(gs, G),
    ok: BO.BO.BestOK(inf, best, G, S)) ->
  BO.BO.BestOK(inf, Eval.Eval.guesses(1n+p, G, S, inf, gs, best), G, S):
  match gs:
    case Nil{}:
      ok
    case Con{g, t}:
      (oks, ft) = f
      (wg, every2) = every
      MV.guesses_fold(inf, p, G, S, t, Eval.Eval.guess(p, G, S, g, inf, best), ft, every2,
        MV.guess_ok(p, G, S, g, inf, best,
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==}, wg, oks, ok))

# One step of the fuel: the machine fold is the specification fold.
def MV.step_to_fold(+inf: Nat, +p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>,
    f: MV.ByGs(p, inf, G, S, G)) -> MV.Job(1n+p, inf, G, S):
  %Equal.sym(SolveRef.Best,
      SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()),
      Eval.Eval.guesses(1n+p, G, S, inf, G, Eval.Eval.dummy_inf(inf)),
      Eval.Eval.guesses_step(p, G, S, inf, G, Eval.Eval.dummy_inf(inf)))
    : BO.BO.BestOK(inf, _, G, S)
  MV.guesses_fold(inf, p, G, S, G, Eval.Eval.dummy_inf(inf), f,
    BO.BO.every_in_self(G), BO.BO.base_ok(inf, G, S))

# Every job of a list gets its obligation from the conjunction at the classes.
def MV.flat_step(+inf: Nat, +p: Nat, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>,
    f: MV.Flat(p, inf, G, MV.next_jobs(G, jobs))) -> MV.Flat(1n+p, inf, G, jobs):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{S, t}:
      MV.use_pair(MV.Flat(1n+p, inf, G, S <> t),
        MV.Flat(p, inf, G, MV.next_guess(G, S)),
        MV.Flat(p, inf, G, MV.next_jobs(G, t)),
        MV.flat_append(p, inf, G, MV.next_guess(G, S), MV.next_jobs(G, t), f),
        fS => ft =>
          Tuple{MV.step_to_fold(inf, p, G, S, MV.by_gs(p, inf, G, S, G, fS)),
           MV.flat_step(inf, p, G, t, ft)})

# The length bounds of the jobs at a level: every candidate list is at most
# the fuel.
def MV.Bounds(+fuel: Nat, jobs: +List<+List<+List<Nat>>>) -> Type:
  match jobs:
    case Nil{}:
      Unit
    case Con{S, t}:
      {Nat.is_le(Groups.len_words(S), fuel) == True{} : Bool} & MV.Bounds(fuel, t)

# The class bounds of one group list, from the guess list's bound.
def MV.group_bounds(+p: Nat, +S: +List<+List<Nat>>, +groups: +List<Groups.Group>,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    sm: GM.GM.GroupsSmaller(S, groups)) -> MV.Bounds(p, MV.next_groups(groups)):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          (lt, sm2) = sm
          (NatProof.Nat.le_fuel(Groups.len_words(ws), Groups.len_words(S), p, lt, ele),
           MV.group_bounds(p, S, t, ele, sm2))

# The class bounds of one guess, when it is usable.
def MV.guess_bounds(+p: Nat, +S: +List<+List<Nat>>, +groups: +List<Groups.Group>,
    b: Bool, +eb: {b == Groups.groups_smaller(S, groups) : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool}) ->
  MV.Bounds(p, MV.classes_b(b, groups)):
  match b:
    case True{}:
      MV.group_bounds(p, S, groups, ele,
        GM.GM.groups_smaller_sound(S, groups,
          Equal.sym(Bool, True{}, Groups.groups_smaller(S, groups), eb)))
    case False{}:
      Unit{}

# Build the bounds of an append from its two halves.
def MV.bounds_append_build(+fuel: Nat, +xs: +List<+List<+List<Nat>>>,
    +ys: +List<+List<+List<Nat>>>, fx: MV.Bounds(fuel, xs),
    fy: MV.Bounds(fuel, ys)) ->
  MV.Bounds(fuel, List.append(&2, +List<+List<Nat>>, xs, ys)):
  match xs:
    case Nil{}:
      fy
    case Con{S, t}:
      (b, ft) = fx
      (b, MV.bounds_append_build(fuel, t, ys, ft, fy))

# The bounds of a guess list's classes.
def MV.any_bounds(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool}) ->
  MV.Bounds(p, MV.next_guess(G, S)):
  match G:
    case Nil{}:
      Unit{}
    case Con{g, t}:
      MV.bounds_append_build(p, MV.classes(g, S), MV.next_guess(t, S),
        MV.guess_bounds(p, S, Groups.groups_build(g, S, Nil{}),
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==}, ele),
        MV.any_bounds(p, t, S, ele))

# The bounds of the next level, from the bounds of this one.
def MV.next_bounds(+p: Nat, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.Bounds(1n+p, jobs)) -> MV.Bounds(p, MV.next_jobs(G, jobs)):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{S, t}:
      (ble, bt) = bounds
      MV.bounds_append_build(p, MV.next_guess(G, S), MV.next_jobs(G, t),
        MV.any_bounds(p, G, S, ble), MV.next_bounds(p, G, t, bt))

# A list of no length is empty.
def MV.nil_of_len_zero(+S: +List<+List<Nat>>,
    e: {Groups.len_words(S) == 0n : Nat}) -> {S == Nil{} : +List<+List<Nat>>}:
  match S:
    case Nil{}:
      {==}
    case Con{w, t}:
      Empty.absurd({w <> t == Nil{} : +List<+List<Nat>>},
        NatProof.NatPrf.zero_ne_succ(Groups.len_words(t),
          Equal.sym(Nat, 1n+Groups.len_words(t), 0n, e)))

# A job obligation, moved to an equal candidate list.
def MV.job_transport(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S1: +List<+List<Nat>>, +S2: +List<+List<Nat>>,
    e: {S1 == S2 : +List<+List<Nat>>}, j: MV.Job(fuel, inf, G, S1)) ->
  MV.Job(fuel, inf, G, S2):
  %e : MV.Job(fuel, inf, G, _)
  j

# The empty candidate list at zero fuel.
def MV.job_nil(+inf: Nat, +G: +List<+List<Nat>>) -> MV.Job(0n, inf, G, Nil{}):
  %Equal.sym(SolveRef.Best,
      SolveRef.step(0n, SolveRef.mk_schedule(G, Nil{}), G, Nil{}, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()),
      Eval.Eval.guesses(0n, G, Nil{}, inf, G, Eval.Eval.dummy_inf(inf)),
      Eval.Eval.guesses_zero(G, inf, G, Eval.Eval.dummy_inf(inf)))
    : BO.BO.BestOK(inf, _, G, Nil{})
  BO.BO.guesses_zero_ok(G, inf, G, Eval.Eval.dummy_inf(inf),
    BO.BO.every_in_self(G), BO.BO.base_ok(inf, G, Nil{}))

# A zero-length candidate list is empty, so its obligation is the base case.
def MV.job_zero(+inf: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    le: {Nat.is_le(Groups.len_words(S), 0n) == True{} : Bool}) ->
  MV.Job(0n, inf, G, S):
  +eS : {S == Nil{} : +List<+List<Nat>>} =
    MV.nil_of_len_zero(S, NatProof.Nat.eq_zero_of_le_zero(Groups.len_words(S), le))
  MV.job_transport(0n, inf, G, Nil{}, S, Equal.sym(+List<+List<Nat>>, S, Nil{}, eS), MV.job_nil(inf, G))

# Zero fuel: every job is empty.
def MV.flat_zero(+inf: Nat, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.Bounds(0n, jobs)) -> MV.Flat(0n, inf, G, jobs):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{S, t}:
      (ble, bt) = bounds
      Tuple{MV.job_zero(inf, G, S, ble), MV.flat_zero(inf, G, t, bt)}

# The fuel induction. One recursive call per level hands every class of every
# job its obligation at the smaller fuel.
def MV.flat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.Bounds(fuel, jobs)) -> MV.Flat(fuel, inf, G, jobs):
  match fuel:
    case 0n:
      MV.flat_zero(inf, G, jobs, bounds)
    case 1n+p:
      MV.flat_step(inf, p, G, jobs,
        MV.flat(p, inf, G, MV.next_jobs(G, jobs), MV.next_bounds(p, G, jobs, bounds)))

# The obligation for the top-level candidate list.
def MV.main_ok(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>,
    le: {Nat.is_le(Groups.len_words(S), fuel) == True{} : Bool}) ->
  MV.Job(fuel, inf, G, S):
  MV.use_pair(MV.Job(fuel, inf, G, S), MV.Job(fuel, inf, G, S), Unit,
    MV.flat(fuel, inf, G, S <> Nil{}, Tuple{le, Unit{}}),
    j => u => j)
