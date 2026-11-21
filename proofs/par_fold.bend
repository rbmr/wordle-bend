# The parallel root fold is the reference fold.
#
# `ones` evaluates every guess from the neutral accumulator; `fold_results`
# replays those results with `better`. The replay lemma of `par_elt.bend` turns
# each replay step into the guess's own step, which is exactly the reference
# fold `Eval.guesses`. `par_results` only changes the order the guesses are
# evaluated in, and the split lemma shows its list of results is the same list;
# so the whole parallel solver reaches the reference's best result, and the
# solver entry point returns the same tree.
import Base
import ../src/feedback.bend as Feedback
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/solve_ref.bend as SolveRef
import ../src/solve_par.bend as SolvePar
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval
import ./par_list.bend as ParList
import ./par_elt.bend as ParElt

# Folding a result cons is replaying its head on the folded tail.
def ParFold.fold_unfold(+r: SolveRef.Best, +rest: +List<SolveRef.Best>,
    best: SolveRef.Best) ->
  {SolvePar.fold_results(r <> rest, best)
   == SolvePar.fold_results(rest, ParElt.ParElt.apply(r, best)) : SolveRef.Best}:
  match r:
    case SolveRef.Best{+tree, +cost}:
      {==}

# Folding the sequential per-guess results is the reference guess fold.
def ParFold.fold_eq(+p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +gs: +List<+List<Nat>>,
    +acc: SolveRef.Best,
    +h: {Nat.is_le(Eval.Eval.cost_of(acc), inf) == True{} : Bool}) ->
  {SolvePar.fold_results(SolvePar.ones(1n+p, G, S, inf, gs), acc)
   == Eval.Eval.guesses(1n+p, G, S, inf, gs, acc) : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      +one_g : SolveRef.Best =
        SolvePar.one(1n+p, G, S, inf, g, Groups.groups_build(g, S, Nil{}),
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})))
      +step1 : {SolvePar.fold_results(
                  SolvePar.ones(1n+p, G, S, inf, g <> rest), acc)
                == SolvePar.fold_results(SolvePar.ones(1n+p, G, S, inf, rest),
                     ParElt.ParElt.apply(one_g, acc)) : SolveRef.Best} =
        ParFold.fold_unfold(one_g, SolvePar.ones(1n+p, G, S, inf, rest), acc)
      +bound : {Nat.is_le(Eval.Eval.cost_of(ParElt.ParElt.apply(one_g, acc)), inf)
                == True{} : Bool} =
        NatProof.Nat.is_le_trans(Eval.Eval.cost_of(ParElt.ParElt.apply(one_g, acc)),
          Eval.Eval.cost_of(acc), inf, ParElt.ParElt.apply_cost_le(one_g, acc), h)
      +step2 : {SolvePar.fold_results(SolvePar.ones(1n+p, G, S, inf, rest),
                   ParElt.ParElt.apply(one_g, acc))
                == Eval.Eval.guesses(1n+p, G, S, inf, rest,
                     ParElt.ParElt.apply(one_g, acc)) : SolveRef.Best} =
        ParFold.fold_eq(p, G, S, inf, rest, ParElt.ParElt.apply(one_g, acc), bound)
      +gee : {ParElt.ParElt.apply(one_g, acc)
              == Eval.Eval.guess(p, G, S, g, inf, acc) : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          ParElt.ParElt.apply(one_g, acc),
          ParElt.ParElt.apply(Eval.Eval.guess(p, G, S, g, inf,
                         SolvePar.init_best(inf)), acc),
          Eval.Eval.guess(p, G, S, g, inf, acc),
          Equal.cong(SolveRef.Best, SolveRef.Best, r => ParElt.ParElt.apply(r, acc),
            one_g, Eval.Eval.guess(p, G, S, g, inf, SolvePar.init_best(inf)),
            ParElt.ParElt.one_eq(p, G, S, inf, g, Groups.groups_build(g, S, Nil{}),
              Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})))),
          ParElt.ParElt.guess_apply(p, G, S, g, inf, acc, h))
      +step3 : {Eval.Eval.guesses(1n+p, G, S, inf, rest, ParElt.ParElt.apply(one_g, acc))
                == Eval.Eval.guesses(1n+p, G, S, inf, rest,
                     Eval.Eval.guess(p, G, S, g, inf, acc)) : SolveRef.Best} =
        Equal.cong(SolveRef.Best, SolveRef.Best,
          x => Eval.Eval.guesses(1n+p, G, S, inf, rest, x),
          ParElt.ParElt.apply(one_g, acc), Eval.Eval.guess(p, G, S, g, inf, acc), gee)
      Equal.trans(SolveRef.Best,
        SolvePar.fold_results(SolvePar.ones(1n+p, G, S, inf, g <> rest), acc),
        SolvePar.fold_results(SolvePar.ones(1n+p, G, S, inf, rest),
          ParElt.ParElt.apply(one_g, acc)),
        Eval.Eval.guesses(1n+p, G, S, inf, rest,
          Eval.Eval.guess(p, G, S, g, inf, acc)),
        step1, Equal.trans(SolveRef.Best,
          SolvePar.fold_results(SolvePar.ones(1n+p, G, S, inf, rest),
            ParElt.ParElt.apply(one_g, acc)),
          Eval.Eval.guesses(1n+p, G, S, inf, rest, ParElt.ParElt.apply(one_g, acc)),
          Eval.Eval.guesses(1n+p, G, S, inf, rest,
            Eval.Eval.guess(p, G, S, g, inf, acc)),
          step2, step3))

# Splitting and evaluating in halves keeps the per-guess result list.
def ParFold.par_results_eq(+d: Nat, +rem: Nat, +fuel: Nat,
    +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +inf: Nat,
    +gs: +List<+List<Nat>>) ->
  {SolvePar.par_results(d, rem, fuel, G, S, inf, gs)
   == SolvePar.ones(fuel, G, S, inf, gs) : +List<SolveRef.Best>}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      match rem:
        case 0n:
          {==}
        case 1n+q:
          +len : Nat = Groups.len_words(gs)
          +half : Nat = Nat.div(len, 2n)
          +left : +List<+List<Nat>> = List.take(&2, +List<Nat>, gs, half)
          +right : +List<+List<Nat>> = List.drop(&2, +List<Nat>, gs, half)
          +ihl : {SolvePar.par_results(p, Nat.sub(Groups.len_words(left), SolvePar.grain()),
                     fuel, G, S, inf, left)
                  == SolvePar.ones(fuel, G, S, inf, left)
                  : +List<SolveRef.Best>} =
            ParFold.par_results_eq(p, Nat.sub(Groups.len_words(left), SolvePar.grain()),
              fuel, G, S, inf, left)
          +ihr : {SolvePar.par_results(p, Nat.sub(Groups.len_words(right), SolvePar.grain()),
                     fuel, G, S, inf, right)
                  == SolvePar.ones(fuel, G, S, inf, right)
                  : +List<SolveRef.Best>} =
            ParFold.par_results_eq(p, Nat.sub(Groups.len_words(right), SolvePar.grain()),
              fuel, G, S, inf, right)
          +e1 : {List.append(&2, SolveRef.Best,
                     SolvePar.par_results(p, Nat.sub(Groups.len_words(left),
                       SolvePar.grain()), fuel, G, S, inf, left),
                     SolvePar.par_results(p, Nat.sub(Groups.len_words(right),
                       SolvePar.grain()), fuel, G, S, inf, right))
                  == List.append(&2, SolveRef.Best,
                     SolvePar.ones(fuel, G, S, inf, left),
                     SolvePar.par_results(p, Nat.sub(Groups.len_words(right),
                       SolvePar.grain()), fuel, G, S, inf, right))
                  : +List<SolveRef.Best>} =
            Equal.cong(+List<SolveRef.Best>, +List<SolveRef.Best>,
              l => List.append(&2, SolveRef.Best, l,
                     SolvePar.par_results(p, Nat.sub(Groups.len_words(right),
                       SolvePar.grain()), fuel, G, S, inf, right)),
              SolvePar.par_results(p, Nat.sub(Groups.len_words(left),
                SolvePar.grain()), fuel, G, S, inf, left),
              SolvePar.ones(fuel, G, S, inf, left), ihl)
          +e2 : {List.append(&2, SolveRef.Best,
                     SolvePar.ones(fuel, G, S, inf, left),
                     SolvePar.par_results(p, Nat.sub(Groups.len_words(right),
                       SolvePar.grain()), fuel, G, S, inf, right))
                  == List.append(&2, SolveRef.Best,
                     SolvePar.ones(fuel, G, S, inf, left),
                     SolvePar.ones(fuel, G, S, inf, right))
                  : +List<SolveRef.Best>} =
            Equal.cong(+List<SolveRef.Best>, +List<SolveRef.Best>,
              l => List.append(&2, SolveRef.Best,
                     SolvePar.ones(fuel, G, S, inf, left), l),
              SolvePar.par_results(p, Nat.sub(Groups.len_words(right),
                SolvePar.grain()), fuel, G, S, inf, right),
              SolvePar.ones(fuel, G, S, inf, right), ihr)
          +e3 : {List.append(&2, SolveRef.Best,
                     SolvePar.ones(fuel, G, S, inf, left),
                     SolvePar.ones(fuel, G, S, inf, right))
                  == SolvePar.ones(fuel, G, S, inf,
                       List.append(&2, +List<Nat>, left, right))
                  : +List<SolveRef.Best>} =
            Equal.sym(+List<SolveRef.Best>,
              SolvePar.ones(fuel, G, S, inf, List.append(&2, +List<Nat>, left, right)),
              List.append(&2, SolveRef.Best, SolvePar.ones(fuel, G, S, inf, left),
                          SolvePar.ones(fuel, G, S, inf, right)),
              ParList.ParList.ones_concat(fuel, G, S, inf, left, right))
          +e4 : {SolvePar.ones(fuel, G, S, inf,
                     List.append(&2, +List<Nat>, left, right))
                  == SolvePar.ones(fuel, G, S, inf, gs)
                  : +List<SolveRef.Best>} =
            Equal.cong(+List<+List<Nat>>, +List<SolveRef.Best>,
              xs => SolvePar.ones(fuel, G, S, inf, xs),
              List.append(&2, +List<Nat>, left, right), gs,
              ParList.ParList.take_drop(gs, half))
          Equal.trans(+List<SolveRef.Best>,
            List.append(&2, SolveRef.Best,
              SolvePar.par_results(p, Nat.sub(Groups.len_words(left),
                SolvePar.grain()), fuel, G, S, inf, left),
              SolvePar.par_results(p, Nat.sub(Groups.len_words(right),
                SolvePar.grain()), fuel, G, S, inf, right)),
            SolvePar.ones(fuel, G, S, inf, gs),
            SolvePar.ones(fuel, G, S, inf, gs),
            Equal.trans(+List<SolveRef.Best>,
              List.append(&2, SolveRef.Best,
                SolvePar.par_results(p, Nat.sub(Groups.len_words(left),
                  SolvePar.grain()), fuel, G, S, inf, left),
                SolvePar.par_results(p, Nat.sub(Groups.len_words(right),
                  SolvePar.grain()), fuel, G, S, inf, right)),
              List.append(&2, SolveRef.Best,
                SolvePar.ones(fuel, G, S, inf, left),
                SolvePar.ones(fuel, G, S, inf, right)),
              SolvePar.ones(fuel, G, S, inf, gs),
              Equal.trans(+List<SolveRef.Best>,
                List.append(&2, SolveRef.Best,
                  SolvePar.par_results(p, Nat.sub(Groups.len_words(left),
                    SolvePar.grain()), fuel, G, S, inf, left),
                  SolvePar.par_results(p, Nat.sub(Groups.len_words(right),
                    SolvePar.grain()), fuel, G, S, inf, right)),
                List.append(&2, SolveRef.Best,
                  SolvePar.ones(fuel, G, S, inf, left),
                  SolvePar.par_results(p, Nat.sub(Groups.len_words(right),
                    SolvePar.grain()), fuel, G, S, inf, right)),
                List.append(&2, SolveRef.Best,
                  SolvePar.ones(fuel, G, S, inf, left),
                  SolvePar.ones(fuel, G, S, inf, right)),
                e1, e2),
              Equal.trans(+List<SolveRef.Best>,
                List.append(&2, SolveRef.Best,
                  SolvePar.ones(fuel, G, S, inf, left),
                  SolvePar.ones(fuel, G, S, inf, right)),
                SolvePar.ones(fuel, G, S, inf,
                  List.append(&2, +List<Nat>, left, right)),
                SolvePar.ones(fuel, G, S, inf, gs),
                e3, e4)),
            {==})

# The reference search at a given candidate count, with the same initial
# state. This names the term `SolveRef.solve` computes, so the candidate count
# can be replaced by the matched number in the proof without touching the
# search itself.
def ParFold.ref_best(+n: Nat, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  SolveRef.best_to_maybe(SolveRef.inf_of(n),
    SolveRef.step(n, SolveRef.mk_schedule(G, C), G, C, SolveRef.inf_of(n),
      Nil{}, Nil{}, 0n, SolvePar.init_best(SolveRef.inf_of(n)),
      SolvePar.zero_best()))

# `SolveRef.solve` is that search at the candidate count.
def ParFold.unfold_ref(+n: Nat, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, e: {n == Groups.len_words(C) : Nat}) ->
  {SolveRef.solve(G, C) == ParFold.ref_best(n, G, C) : Maybe<Tree.Tree>}:
  Equal.trans(Maybe<Tree.Tree>, SolveRef.solve(G, C),
    ParFold.ref_best(Groups.len_words(C), G, C),
    ParFold.ref_best(n, G, C), {==},
    Equal.cong(Nat, Maybe<Tree.Tree>, m => ParFold.ref_best(m, G, C),
      Groups.len_words(C), n, Equal.sym(Nat, n, Groups.len_words(C), e)))

# The parallel solver at a positive candidate count reaches the reference
# search at the same count.
def ParFold.solve_n_eq(+n: Nat, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, e: {n == Groups.len_words(C) : Nat}) ->
  {SolvePar.solve_n(n, G, C) == ParFold.ref_best(n, G, C) : Maybe<Tree.Tree>}:
  match n:
    case 0n:
      Equal.trans(Maybe<Tree.Tree>, SolvePar.solve_n(0n, G, C),
        SolveRef.solve(G, C), ParFold.ref_best(0n, G, C), {==},
        ParFold.unfold_ref(0n, G, C, e))
    case 1n+p:
      +inf : Nat = SolveRef.inf_of(1n+p)
      +depth : Nat = Groups.len_words(G)
      +above : Nat = Nat.sub(depth, SolvePar.grain())
      +results : +List<SolveRef.Best> =
        SolvePar.par_results(depth, above, 1n+p, G, C, inf, G)
      +bound : {Nat.is_le(Eval.Eval.cost_of(SolvePar.init_best(inf)), inf)
                == True{} : Bool} =
        NatProof.Nat.is_le_refl(inf)
      +best_eq : {SolvePar.fold_results(results, SolvePar.init_best(inf))
                  == SolveRef.step(1n+p, SolveRef.mk_schedule(G, C), G, C, inf,
                       Nil{}, Nil{}, 0n, SolvePar.init_best(inf),
                       SolvePar.zero_best()) : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          SolvePar.fold_results(results, SolvePar.init_best(inf)),
          Eval.Eval.guesses(1n+p, G, C, inf, G, SolvePar.init_best(inf)),
          SolveRef.step(1n+p, SolveRef.mk_schedule(G, C), G, C, inf,
            Nil{}, Nil{}, 0n, SolvePar.init_best(inf), SolvePar.zero_best()),
          Equal.trans(SolveRef.Best,
            SolvePar.fold_results(results, SolvePar.init_best(inf)),
            SolvePar.fold_results(SolvePar.ones(1n+p, G, C, inf, G),
              SolvePar.init_best(inf)),
            Eval.Eval.guesses(1n+p, G, C, inf, G, SolvePar.init_best(inf)),
            Equal.cong(+List<SolveRef.Best>, SolveRef.Best,
              rs => SolvePar.fold_results(rs, SolvePar.init_best(inf)),
              SolvePar.par_results(depth, above, 1n+p, G, C, inf, G),
              SolvePar.ones(1n+p, G, C, inf, G),
              ParFold.par_results_eq(depth, above, 1n+p, G, C, inf, G)),
            ParFold.fold_eq(p, G, C, inf, G, SolvePar.init_best(inf), bound)),
          Equal.sym(SolveRef.Best,
            SolveRef.step(1n+p, SolveRef.mk_schedule(G, C), G, C, inf,
              Nil{}, Nil{}, 0n, SolvePar.init_best(inf), SolvePar.zero_best()),
            Eval.Eval.guesses(1n+p, G, C, inf, G, SolvePar.init_best(inf)),
            Eval.Eval.guesses_step(p, G, C, inf, G, SolvePar.init_best(inf))))
      Equal.cong(SolveRef.Best, Maybe<Tree.Tree>,
        best => SolveRef.best_to_maybe(inf, best),
        SolvePar.fold_results(results, SolvePar.init_best(inf)),
        SolveRef.step(1n+p, SolveRef.mk_schedule(G, C), G, C, inf,
          Nil{}, Nil{}, 0n, SolvePar.init_best(inf), SolvePar.zero_best()),
        best_eq)

def ParFold.solve_eq(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>) ->
  {SolvePar.solve(G, C) == SolveRef.solve(G, C) : Maybe<Tree.Tree>}:
  Equal.trans(Maybe<Tree.Tree>, SolvePar.solve(G, C),
    ParFold.ref_best(Groups.len_words(C), G, C), SolveRef.solve(G, C),
    ParFold.solve_n_eq(Groups.len_words(C), G, C, {==}),
    Equal.sym(Maybe<Tree.Tree>, SolveRef.solve(G, C),
      ParFold.ref_best(Groups.len_words(C), G, C),
      ParFold.unfold_ref(Groups.len_words(C), G, C, {==})))
