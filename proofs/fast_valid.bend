# Direct validity, cost, leaf/two-item, and floor-soundness lemmas for the
# bound-pruned solver (`src/solve_fast.bend`).
#
# Rather than proving tree-for-tree equality with `SolveRef.solve`, the direct
# proof tracks a `Data`-valued boolean validity+cost invariant (`FV.best_ok_b`)
# and proves that `SolveFast` always produces a result whose cost is at most
# the reference search's cost. This module collects all pure boolean validity,
# finished-node reconstruction, `OneItem`/`TwoItem` bounds, monotonicity, and
# `2*|S|` / `2*|S| - 1` floor-soundness lemmas used by `proofs/fast_opt.bend`.
import Base
import ../src/solve_fast.bend as SolveFast
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./groups.bend as Grp
import ./groupsdistinct.bend as GD
import ./nodevalid.bend as NV
import ./depthgroups.bend as DG
import ./solvevalid.bend as SV
import ./nodecost.bend as NodeCost
import ./groupcost.bend as GC
import ./classbound_nat.bend as CBN
import ./classbound_kids.bend as CBK
import ./optimalvalue.bend as OV
import ./optfold.bend as Fold
import ./optguess.bend as OQGuess
import ./optcost.bend as OC
import ./mainvalid.bend as MV
import ./fast_step.bend as FS
import ./fast_better.bend as FB
import ./fast_groups.bend as FG
import ./fast_lb.bend as FLB
import ./fast_cutoff.bend as FC
import ./fast_one.bend as FO
import ./fast_nodup.bend as FN

# ---------------------------------------------------------------------------
# Small Bool, Nat, and saturating-addition helpers
# ---------------------------------------------------------------------------

def FV.bool_or_r(+a: Bool, +b: Bool, +eb: {b == True{} : Bool}) ->
  {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      eb

def FV.ge_of_le_go(a: Nat, b: Nat,
    +h: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Nat.is_ge(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_ge(0n, 1n+ap) == True{} : Bool},
        Logic.Proof.false_ne_true(h))
    case 1n+ap 1n+bp:
      FV.ge_of_le_go(ap, bp, h)

def FV.ge_of_le(+a: Nat, +b: Nat,
    +h: {Nat.is_le(a, b) == True{} : Bool}) ->
  {Nat.is_ge(b, a) == True{} : Bool}:
  FV.ge_of_le_go(a, b, h)

def FV.le_sat_add_of_lt_inf_go(+inf: Nat, +a1: Nat, +a2: Nat, +b1: Nat, +b2: Nat,
    +ha: {Nat.is_le(a1, a2) == True{} : Bool},
    +hb: {Nat.is_le(b1, b2) == True{} : Bool},
    +hlt: {Nat.is_lt(Nat.add(a1, b1), inf) == True{} : Bool},
    ga: Bool, gb: Bool) ->
  {Nat.is_le(Nat.add(a1, b1),
     Feedback.Bool.case(Nat, ga, inf,
       Feedback.Bool.case(Nat, gb, inf, Nat.add(a2, b2)))) == True{} : Bool}:
  match ga:
    case True{}:
      NatProof.Nat.is_le_of_lt(Nat.add(a1, b1), inf, hlt)
    case False{}:
      match gb:
        case True{}:
          NatProof.Nat.is_le_of_lt(Nat.add(a1, b1), inf, hlt)
        case False{}:
          CBN.CB.is_le_add(a1, a2, b1, b2, ha, hb)

def FV.le_sat_add_of_lt_inf(+inf: Nat, +a1: Nat, +a2: Nat, +b1: Nat, +b2: Nat,
    +ha: {Nat.is_le(a1, a2) == True{} : Bool},
    +hb: {Nat.is_le(b1, b2) == True{} : Bool},
    +hlt: {Nat.is_lt(Nat.add(a1, b1), inf) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(a1, b1), SolveRef.sat_add(inf, a2, b2)) == True{} : Bool}:
  FV.le_sat_add_of_lt_inf_go(inf, a1, a2, b1, b2, ha, hb, hlt,
    Nat.is_ge(a2, inf), Nat.is_ge(b2, inf))

def FV.le_better_of_le_both_go(+x: Nat, +cc: Nat, +ct: Tree.Tree,
    +tb: Tree.Tree, +cb: Nat, b: Bool,
    +h1: {Nat.is_le(x, cc) == True{} : Bool},
    +h2: {Nat.is_le(x, cb) == True{} : Bool}) ->
  {Nat.is_le(x,
     Eval.Eval.cost_of(Feedback.Bool.case(SolveRef.Best, b,
       SolveRef.Best{ct, cc}, SolveRef.Best{tb, cb}))) == True{} : Bool}:
  match b:
    case True{}:
      h1
    case False{}:
      h2

def FV.le_better_of_le_both(+x: Nat, +cc: Nat, +ct: Tree.Tree,
    best: SolveRef.Best,
    +h1: {Nat.is_le(x, cc) == True{} : Bool},
    +h2: {Nat.is_le(x, Eval.Eval.cost_of(best)) == True{} : Bool}) ->
  {Nat.is_le(x, Eval.Eval.cost_of(SolveRef.better(cc, ct, best)))
   == True{} : Bool}:
  match best:
    case SolveRef.Best{+tb, +cb}:
      FV.le_better_of_le_both_go(x, cc, ct, tb, cb, Nat.is_lt(cc, cb), h1, h2)

def FV.better_mono(+cc: Nat, +ct: Tree.Tree, +b1: SolveRef.Best,
    +b2: SolveRef.Best,
    +hle: {Nat.is_le(Eval.Eval.cost_of(b1), Eval.Eval.cost_of(b2))
           == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(SolveRef.better(cc, ct, b1)),
             Eval.Eval.cost_of(SolveRef.better(cc, ct, b2)))
   == True{} : Bool}:
  FV.le_better_of_le_both(
    Eval.Eval.cost_of(SolveRef.better(cc, ct, b1)), cc, ct, b2,
    Fold.OQ.better_le_cand(cc, ct, b1),
    NatProof.Nat.is_le_trans(
      Eval.Eval.cost_of(SolveRef.better(cc, ct, b1)),
      Eval.Eval.cost_of(b1), Eval.Eval.cost_of(b2),
      Fold.OQ.better_le_best(cc, ct, b1), hle))

def FV.eval_guess_mono_bool(+p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +groups: +List<Groups.Group>,
    +inf: Nat, usable: Bool, +b1: SolveRef.Best, +b2: SolveRef.Best,
    +hle: {Nat.is_le(Eval.Eval.cost_of(b1), Eval.Eval.cost_of(b2))
           == True{} : Bool}) ->
  {Nat.is_le(
     Eval.Eval.cost_of(Eval.Eval.guess_bool(p, G, S, g, groups, inf, usable, b1)),
     Eval.Eval.cost_of(Eval.Eval.guess_bool(p, G, S, g, groups, inf, usable, b2)))
   == True{} : Bool}:
  match usable:
    case False{}:
      hle
    case True{}:
      +ks : Eval.KS = Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)
      +cc : Nat = Fold.OQ.ks_cost(inf, S, ks)
      +ct : Tree.Tree = Fold.OQ.ks_tree(g, ks)
      +e1 : {Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf, groups, b1))
             == Eval.Eval.cost_of(SolveRef.better(cc, ct, b1)) : Nat} =
        Fold.OQ.block_cost_eq(inf, g, S, ks, b1)
      +e2 : {Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf, groups, b2))
             == Eval.Eval.cost_of(SolveRef.better(cc, ct, b2)) : Nat} =
        Fold.OQ.block_cost_eq(inf, g, S, ks, b2)
      Fold.OQ.le_cong_l(
        Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf, groups, b1)),
        Eval.Eval.cost_of(SolveRef.better(cc, ct, b1)),
        Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf, groups, b2)),
        e1,
        Fold.OQ.le_cong_r(
          Eval.Eval.cost_of(SolveRef.better(cc, ct, b1)),
          Eval.Eval.cost_of(SolveRef.better(cc, ct, b2)),
          Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf, groups, b2)),
          Equal.sym(Nat,
            Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf, groups, b2)),
            Eval.Eval.cost_of(SolveRef.better(cc, ct, b2)), e2),
          FV.better_mono(cc, ct, b1, b2, hle)))

def FV.eval_guesses_mono(+p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +gs: +List<+List<Nat>>,
    +b1: SolveRef.Best, +b2: SolveRef.Best,
    +hle: {Nat.is_le(Eval.Eval.cost_of(b1), Eval.Eval.cost_of(b2))
           == True{} : Bool}) ->
  {Nat.is_le(
     Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, gs, b1)),
     Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, gs, b2)))
   == True{} : Bool}:
  match gs:
    case Nil{}:
      hle
    case Con{+g, +t}:
      +groups : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
      FV.eval_guesses_mono(p, G, S, inf, t,
        Eval.Eval.guess(p, G, S, g, inf, b1),
        Eval.Eval.guess(p, G, S, g, inf, b2),
        FV.eval_guess_mono_bool(p, G, S, g, groups, inf,
          Groups.groups_smaller(S, groups), b1, b2, hle))

def FV.better_best_le_l(a: SolveRef.Best, b: SolveRef.Best) ->
  {Nat.is_le(Eval.Eval.cost_of(FC.FC.better_best(a, b)),
             Eval.Eval.cost_of(a)) == True{} : Bool}:
  match a:
    case SolveRef.Best{+ta, +ca}:
      Fold.OQ.better_le_cand(ca, ta, b)

def FV.better_best_le_r(a: SolveRef.Best, b: SolveRef.Best) ->
  {Nat.is_le(Eval.Eval.cost_of(FC.FC.better_best(a, b)),
             Eval.Eval.cost_of(b)) == True{} : Bool}:
  match a:
    case SolveRef.Best{+ta, +ca}:
      Fold.OQ.better_le_best(ca, ta, b)

def FV.eval_guesses_le_from_inf(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>, +b0: SolveRef.Best,
    +hb0: {Nat.is_le(Eval.Eval.cost_of(b0), inf) == True{} : Bool}) ->
  {Nat.is_le(
     Eval.Eval.cost_of(Eval.Eval.guesses(fuel, G, S, inf, gs, b0)),
     Eval.Eval.cost_of(Eval.Eval.guesses(fuel, G, S, inf, gs,
       Eval.Eval.dummy_inf(inf)))) == True{} : Bool}:
  +e1 : {Eval.Eval.guesses(fuel, G, S, inf, gs, b0)
         == Eval.Eval.guesses(fuel, G, S, inf, gs,
              FC.FC.better_best(Eval.Eval.dummy_inf(inf), b0))
         : SolveRef.Best} =
    Equal.cong(SolveRef.Best, SolveRef.Best,
      a => Eval.Eval.guesses(fuel, G, S, inf, gs, a),
      b0, FC.FC.better_best(Eval.Eval.dummy_inf(inf), b0),
      Equal.sym(SolveRef.Best,
        FC.FC.better_best(Eval.Eval.dummy_inf(inf), b0), b0,
        FC.FC.better_dummy_inf(inf, b0, hb0)))
  +e2 : {Eval.Eval.guesses(fuel, G, S, inf, gs, b0)
         == FC.FC.better_best(
              Eval.Eval.guesses(fuel, G, S, inf, gs, Eval.Eval.dummy_inf(inf)),
              b0) : SolveRef.Best} =
    Equal.trans(SolveRef.Best,
      Eval.Eval.guesses(fuel, G, S, inf, gs, b0),
      Eval.Eval.guesses(fuel, G, S, inf, gs,
        FC.FC.better_best(Eval.Eval.dummy_inf(inf), b0)),
      FC.FC.better_best(
        Eval.Eval.guesses(fuel, G, S, inf, gs, Eval.Eval.dummy_inf(inf)), b0),
      e1, FC.FC.eval_guesses_better(fuel, G, S, inf, gs,
            Eval.Eval.dummy_inf(inf), b0))
  Fold.OQ.le_cong_l(
    Eval.Eval.cost_of(Eval.Eval.guesses(fuel, G, S, inf, gs, b0)),
    Eval.Eval.cost_of(FC.FC.better_best(
      Eval.Eval.guesses(fuel, G, S, inf, gs, Eval.Eval.dummy_inf(inf)), b0)),
    Eval.Eval.cost_of(
      Eval.Eval.guesses(fuel, G, S, inf, gs, Eval.Eval.dummy_inf(inf))),
    Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
      Eval.Eval.guesses(fuel, G, S, inf, gs, b0),
      FC.FC.better_best(
        Eval.Eval.guesses(fuel, G, S, inf, gs, Eval.Eval.dummy_inf(inf)), b0),
      e2),
    FV.better_best_le_l(
      Eval.Eval.guesses(fuel, G, S, inf, gs, Eval.Eval.dummy_inf(inf)), b0))

# Every list of words is a subset of itself.
def FV.all_in_ref_cons_r(+xs: +List<+List<Nat>>, +h: +List<Nat>,
    +G: +List<+List<Nat>>,
    +ai: {FO.FO.all_in_ref(xs, G) == True{} : Bool}) ->
  {FO.FO.all_in_ref(xs, h <> G) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      FO.FO.bool_and_intro(Tree.member_word(w, h <> G),
        FO.FO.all_in_ref(t, h <> G),
        FN.FN.member_cons_r(w, h, G, FO.FO.all_in_head(w, t, G, ai)),
        FV.all_in_ref_cons_r(t, h, G, FO.FO.all_in_tail(w, t, G, ai)))

def FV.member_head(+w: +List<Nat>, +t: +List<+List<Nat>>) ->
  {Tree.member_word(w, w <> t) == True{} : Bool}:
  Equal.cong(Bool, Bool,
    b => Feedback.Bool.case(Bool, b, True{}, Tree.member_word(w, t)),
    Feedback.word_eq(w, w), True{}, FbProof.FbPrf.word_eq_refl(w))

def FV.all_in_ref_self(+G: +List<+List<Nat>>) ->
  {FO.FO.all_in_ref(G, G) == True{} : Bool}:
  match G:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      FO.FO.bool_and_intro(Tree.member_word(h, h <> t),
        FO.FO.all_in_ref(t, h <> t),
        FV.member_head(h, t),
        FV.all_in_ref_cons_r(t, h, t, FV.all_in_ref_self(t)))

# `Fold.ks_cost` of `Eval.items` ignores the accumulated child list.
def FV.ks_cost_unfold(+inf: Nat, +S: +List<+List<Nat>>, ks: Eval.KS) ->
  {Fold.OQ.ks_cost(inf, S, ks)
   == SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(ks)) : Nat}:
  match ks:
    case Eval.KS{kids, sum}:
      {==}

def FV.ks_cost_items_kids_irrel(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +groups: +List<Groups.Group>,
    +k1: +List<Tree.Child>, +k2: +List<Tree.Child>, +sum: Nat) ->
  {Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, groups, k1, sum, inf))
   == Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, groups, k2, sum, inf))
   : Nat}:
  +ks1 : Eval.KS = Eval.Eval.items(p, G, S, g, groups, k1, sum, inf)
  +ks2 : Eval.KS = Eval.Eval.items(p, G, S, g, groups, k2, sum, inf)
  +cs : +List<Nat> = Sat.SB.child_costs(p, G, groups, inf)
  +es : {Sat.SB.ks_sum(ks1) == Sat.SB.ks_sum(ks2) : Nat} =
    Equal.trans(Nat, Sat.SB.ks_sum(ks1), OV.OV.sumL(inf, cs, sum),
      Sat.SB.ks_sum(ks2),
      OV.OV.sum_fold(p, G, S, g, groups, k1, sum, inf),
      Equal.sym(Nat, Sat.SB.ks_sum(ks2), OV.OV.sumL(inf, cs, sum),
        OV.OV.sum_fold(p, G, S, g, groups, k2, sum, inf)))
  Equal.trans(Nat,
    Fold.OQ.ks_cost(inf, S, ks1),
    SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(ks1)),
    Fold.OQ.ks_cost(inf, S, ks2),
    FV.ks_cost_unfold(inf, S, ks1),
    Equal.trans(Nat,
      SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(ks1)),
      SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(ks2)),
      Fold.OQ.ks_cost(inf, S, ks2),
      Equal.cong(Nat, Nat, x => SolveRef.sat_add(inf, Groups.len_words(S), x),
        Sat.SB.ks_sum(ks1), Sat.SB.ks_sum(ks2), es),
      Equal.sym(Nat, Fold.OQ.ks_cost(inf, S, ks2),
        SolveRef.sat_add(inf, Groups.len_words(S), Sat.SB.ks_sum(ks2)),
        FV.ks_cost_unfold(inf, S, ks2))))

def FV.ks_cost_items_step(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +fb: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +restg: +List<Groups.Group>, +sum_ref: Nat) ->
  {Fold.OQ.ks_cost(inf, S,
     Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
       Nil{}, sum_ref, inf))
   == Fold.OQ.ks_cost(inf, S,
        Eval.Eval.items(p, G, S, g, restg, Nil{},
          SolveRef.sat_add(inf, sum_ref,
            Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws))), inf))
   : Nat}:
  +ref_c : SolveRef.Best = FS.FS.ref_run_at(p, inf, G, ws)
  +kr : +List<Tree.Child> = Tree.Child{fb, Eval.Eval.tree_of(ref_c)} <> Nil{}
  +sr : Nat = SolveRef.sat_add(inf, sum_ref, Eval.Eval.cost_of(ref_c))
  +e1 : {Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
           Nil{}, sum_ref, inf)
         == Eval.Eval.items(p, G, S, g, restg, kr, sr, inf) : Eval.KS} =
    Eval.Eval.with_kid_eq(fb, Nil{}, sum_ref, inf, ref_c,
      ka => sa => Eval.Eval.items(p, G, S, g, restg, ka, sa, inf))
  Equal.trans(Nat,
    Fold.OQ.ks_cost(inf, S,
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
        Nil{}, sum_ref, inf)),
    Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, restg, kr, sr, inf)),
    Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g, restg, Nil{}, sr, inf)),
    Equal.cong(Eval.KS, Nat, ks => Fold.OQ.ks_cost(inf, S, ks),
      Eval.Eval.items(p, G, S, g, Groups.Group{fb, ws} <> restg,
        Nil{}, sum_ref, inf),
      Eval.Eval.items(p, G, S, g, restg, kr, sr, inf), e1),
    FV.ks_cost_items_kids_irrel(p, inf, G, S, g, restg, kr, Nil{}, sr))

# ---------------------------------------------------------------------------
# Boolean validity (`FV.valid_b`) and reflection to `Tree.Valid`
# ---------------------------------------------------------------------------

def FV.kids_in_b(kids: +List<Tree.Child>, +G: +List<+List<Nat>>) -> Bool:
  match kids:
    case Nil{}:
      True{}
    case Con{ch, rest}:
      match ch:
        case Tree.Child{fb, c}:
          match c:
            case Tree.Node{g, ckids}:
              Bool.and(
                Bool.and(Tree.member_word(g, G), FV.kids_in_b(ckids, G)),
                FV.kids_in_b(rest, G))

def FV.tree_in_b(t: Tree.Tree, +G: +List<+List<Nat>>) -> Bool:
  match t:
    case Tree.Node{g, kids}:
      Bool.and(Tree.member_word(g, G), FV.kids_in_b(kids, G))

def FV.kids_in_cons(+fb: +List<Feedback.Color>, c: Tree.Tree,
    +rest: +List<Tree.Child>, +G: +List<+List<Nat>>) ->
  {FV.kids_in_b(Tree.Child{fb, c} <> rest, G)
   == Bool.and(FV.tree_in_b(c, G), FV.kids_in_b(rest, G)) : Bool}:
  match c:
    case Tree.Node{g, ckids}:
      {==}

def FV.all_have_depth_b(+t: Tree.Tree, S: +List<+List<Nat>>) -> Bool:
  match S:
    case Nil{}:
      True{}
    case Con{w, rest}:
      Bool.and(Maybe.is_some(&1, Nat, Tree.depth(t, w)),
               FV.all_have_depth_b(t, rest))

def FV.valid_b(+t: Tree.Tree, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>) -> Bool:
  Bool.and(FV.tree_in_b(t, G), FV.all_have_depth_b(t, S))

def FV.kids_in_of_b(+kids: +List<Tree.Child>, +G: +List<+List<Nat>>,
    +h: {FV.kids_in_b(kids, G) == True{} : Bool}) -> Tree.KidsIn(kids, G):
  match kids:
    case Nil{}:
      Unit{}
    case Con{ch, rest}:
      match ch:
        case Tree.Child{+fb, c}:
          match c:
            case Tree.Node{+g, +ckids}:
              +hc : {Bool.and(Tree.member_word(g, G), FV.kids_in_b(ckids, G))
                     == True{} : Bool} =
                Logic.Proof.and_true_l(
                  Bool.and(Tree.member_word(g, G), FV.kids_in_b(ckids, G)),
                  FV.kids_in_b(rest, G), h)
              +hr : {FV.kids_in_b(rest, G) == True{} : Bool} =
                Logic.Proof.and_true_r(
                  Bool.and(Tree.member_word(g, G), FV.kids_in_b(ckids, G)),
                  FV.kids_in_b(rest, G), h)
              ((Logic.Proof.and_true_l(Tree.member_word(g, G),
                  FV.kids_in_b(ckids, G), hc),
                FV.kids_in_of_b(ckids, G,
                  Logic.Proof.and_true_r(Tree.member_word(g, G),
                    FV.kids_in_b(ckids, G), hc))),
               FV.kids_in_of_b(rest, G, hr))

def FV.tree_in_of_b(+t: Tree.Tree, +G: +List<+List<Nat>>,
    +h: {FV.tree_in_b(t, G) == True{} : Bool}) -> Tree.TreeIn(t, G):
  match t:
    case Tree.Node{+g, +kids}:
      (Logic.Proof.and_true_l(Tree.member_word(g, G), FV.kids_in_b(kids, G), h),
       FV.kids_in_of_b(kids, G,
         Logic.Proof.and_true_r(Tree.member_word(g, G), FV.kids_in_b(kids, G), h)))

def FV.all_have_depth_of_b(+t: Tree.Tree, +S: +List<+List<Nat>>,
    +h: {FV.all_have_depth_b(t, S) == True{} : Bool}) -> Tree.AllHaveDepth(t, S):
  match S:
    case Nil{}:
      Unit{}
    case Con{+w, +rest}:
      (Logic.Proof.and_true_l(Maybe.is_some(&1, Nat, Tree.depth(t, w)),
         FV.all_have_depth_b(t, rest), h),
       FV.all_have_depth_of_b(t, rest,
         Logic.Proof.and_true_r(Maybe.is_some(&1, Nat, Tree.depth(t, w)),
           FV.all_have_depth_b(t, rest), h)))

def FV.valid_of_b(+t: Tree.Tree, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +hv: {FV.valid_b(t, G, S) == True{} : Bool}) ->
  Tree.Valid(t, G, S):
  (FV.tree_in_of_b(t, G,
     Logic.Proof.and_true_l(FV.tree_in_b(t, G), FV.all_have_depth_b(t, S), hv)),
   FV.all_have_depth_of_b(t, S,
     Logic.Proof.and_true_r(FV.tree_in_b(t, G), FV.all_have_depth_b(t, S), hv)))

# ---------------------------------------------------------------------------
# Boolean accumulator invariant `FV.best_ok_b`
# ---------------------------------------------------------------------------

def FV.best_ok_b(+limit: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    best: SolveRef.Best) -> Bool:
  match best:
    case SolveRef.Best{+tree, +cost}:
      Bool.or(Nat.is_ge(cost, limit),
        Bool.and(FV.valid_b(tree, G, S),
                 Nat.is_le(Tree.cost(tree, S), cost)))

def FV.best_ok_init(+limit: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    best: SolveRef.Best,
    +hge: {Nat.is_ge(Eval.Eval.cost_of(best), limit) == True{} : Bool}) ->
  {FV.best_ok_b(limit, G, S, best) == True{} : Bool}:
  match best:
    case SolveRef.Best{+tree, +cost}:
      Equal.cong(Bool, Bool,
        b => Bool.or(b,
               Bool.and(FV.valid_b(tree, G, S),
                        Nat.is_le(Tree.cost(tree, S), cost))),
        Nat.is_ge(cost, limit), True{}, hge)

def FV.best_ok_extract(+limit: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, best: SolveRef.Best,
    +hok: {FV.best_ok_b(limit, G, S, best) == True{} : Bool},
    +hlt: {Nat.is_lt(Eval.Eval.cost_of(best), limit) == True{} : Bool}) ->
  {Bool.and(FV.valid_b(Eval.Eval.tree_of(best), G, S),
            Nat.is_le(Tree.cost(Eval.Eval.tree_of(best), S),
                      Eval.Eval.cost_of(best))) == True{} : Bool}:
  match best:
    case SolveRef.Best{+tree, +cost}:
      +hgf : {Nat.is_ge(cost, limit) == False{} : Bool} =
        OV.OV.ge_false_of_lt(cost, limit, hlt)
      Equal.trans(Bool,
        Bool.and(FV.valid_b(tree, G, S), Nat.is_le(Tree.cost(tree, S), cost)),
        Bool.or(Nat.is_ge(cost, limit),
          Bool.and(FV.valid_b(tree, G, S), Nat.is_le(Tree.cost(tree, S), cost))),
        True{},
        Equal.cong(Bool, Bool,
          b => Bool.or(b,
                 Bool.and(FV.valid_b(tree, G, S),
                          Nat.is_le(Tree.cost(tree, S), cost))),
          False{}, Nat.is_ge(cost, limit),
          Equal.sym(Bool, Nat.is_ge(cost, limit), False{}, hgf)),
        hok)

def FV.best_ok_better_go(+limit: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +candCost: Nat, +candTree: Tree.Tree,
    +tree: Tree.Tree, +cost: Nat, b: Bool,
    +hv: {FV.valid_b(candTree, G, S) == True{} : Bool},
    +hc: {Nat.is_le(Tree.cost(candTree, S), candCost) == True{} : Bool},
    +hok: {FV.best_ok_b(limit, G, S, SolveRef.Best{tree, cost})
           == True{} : Bool}) ->
  {FV.best_ok_b(limit, G, S,
     Feedback.Bool.case(SolveRef.Best, b,
       SolveRef.Best{candTree, candCost}, SolveRef.Best{tree, cost}))
   == True{} : Bool}:
  match b:
    case True{}:
      FV.bool_or_r(Nat.is_ge(candCost, limit),
        Bool.and(FV.valid_b(candTree, G, S),
                 Nat.is_le(Tree.cost(candTree, S), candCost)),
        FO.FO.bool_and_intro(FV.valid_b(candTree, G, S),
          Nat.is_le(Tree.cost(candTree, S), candCost), hv, hc))
    case False{}:
      hok

def FV.best_ok_better(+limit: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +candCost: Nat, +candTree: Tree.Tree,
    best: SolveRef.Best,
    +hv: {FV.valid_b(candTree, G, S) == True{} : Bool},
    +hc: {Nat.is_le(Tree.cost(candTree, S), candCost) == True{} : Bool},
    +hok: {FV.best_ok_b(limit, G, S, best) == True{} : Bool}) ->
  {FV.best_ok_b(limit, G, S, SolveRef.better(candCost, candTree, best))
   == True{} : Bool}:
  match best:
    case SolveRef.Best{+tree, +cost}:
      FV.best_ok_better_go(limit, G, S, candCost, candTree, tree, cost,
        Nat.is_lt(candCost, cost), hv, hc, hok)

# ---------------------------------------------------------------------------
# Singleton (`OneItem`) and two-candidate (`TwoItem`) validity, cost, bounds
# ---------------------------------------------------------------------------

def FV.depth_self(+w: +List<Nat>, +kids: +List<Tree.Child>) ->
  {Tree.depth(Tree.Node{w, kids}, w) == Some{1n} : Maybe<Nat>}:
  Equal.cong(Bool, Maybe<Nat>,
    b => Feedback.Bool.case(Maybe<Nat>, b, Some{1n},
           Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(w, w), w))),
    Feedback.word_eq(w, w), True{}, FbProof.FbPrf.word_eq_refl(w))

def FV.depth_eq_word(+g: +List<Nat>, +w: +List<Nat>, +kids: +List<Tree.Child>,
    +heq: {Feedback.word_eq(g, w) == True{} : Bool}) ->
  {Tree.depth(Tree.Node{g, kids}, w) == Some{1n} : Maybe<Nat>}:
  Equal.cong(Bool, Maybe<Nat>,
    b => Feedback.Bool.case(Maybe<Nat>, b, Some{1n},
           Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w))),
    Feedback.word_eq(g, w), True{}, heq)

def FV.one_tree_valid_b(+w: +List<Nat>, +G: +List<+List<Nat>>,
    +win: {Tree.member_word(w, G) == True{} : Bool}) ->
  {FV.valid_b(Tree.Node{w, Nil{}}, G, w <> Nil{}) == True{} : Bool}:
  +hti : {FV.tree_in_b(Tree.Node{w, Nil{}}, G) == True{} : Bool} =
    FO.FO.bool_and_intro(Tree.member_word(w, G), True{}, win, {==})
  +hd : {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{w, Nil{}}, w))
         == True{} : Bool} =
    Equal.cong(Maybe<Nat>, Bool, m => Maybe.is_some(&1, Nat, m),
      Tree.depth(Tree.Node{w, Nil{}}, w), Some{1n}, FV.depth_self(w, Nil{}))
  FO.FO.bool_and_intro(FV.tree_in_b(Tree.Node{w, Nil{}}, G),
    FV.all_have_depth_b(Tree.Node{w, Nil{}}, w <> Nil{}),
    hti, FO.FO.bool_and_intro(
      Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{w, Nil{}}, w)), True{},
      hd, {==}))

def FV.one_tree_cost(+w: +List<Nat>) ->
  {Tree.cost(Tree.Node{w, Nil{}}, w <> Nil{}) == 1n : Nat}:
  Equal.cong(Maybe<Nat>, Nat,
    m => Nat.add(Maybe.default(&1, Nat, m, 0n), 0n),
    Tree.depth(Tree.Node{w, Nil{}}, w), Some{1n}, FV.depth_self(w, Nil{}))

def FV.two_same_valid_b(+w1: +List<Nat>, +w2: +List<Nat>, +G: +List<+List<Nat>>,
    +w1in: {Tree.member_word(w1, G) == True{} : Bool},
    +heq: {Feedback.word_eq(w1, w2) == True{} : Bool}) ->
  {FV.valid_b(Tree.Node{w1, Nil{}}, G, w1 <> (w2 <> Nil{})) == True{} : Bool}:
  +hti : {FV.tree_in_b(Tree.Node{w1, Nil{}}, G) == True{} : Bool} =
    FO.FO.bool_and_intro(Tree.member_word(w1, G), True{}, w1in, {==})
  +hd1 : {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{w1, Nil{}}, w1))
          == True{} : Bool} =
    Equal.cong(Maybe<Nat>, Bool, m => Maybe.is_some(&1, Nat, m),
      Tree.depth(Tree.Node{w1, Nil{}}, w1), Some{1n}, FV.depth_self(w1, Nil{}))
  +hd2 : {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{w1, Nil{}}, w2))
          == True{} : Bool} =
    Equal.cong(Maybe<Nat>, Bool, m => Maybe.is_some(&1, Nat, m),
      Tree.depth(Tree.Node{w1, Nil{}}, w2), Some{1n},
      FV.depth_eq_word(w1, w2, Nil{}, heq))
  FO.FO.bool_and_intro(FV.tree_in_b(Tree.Node{w1, Nil{}}, G),
    FV.all_have_depth_b(Tree.Node{w1, Nil{}}, w1 <> (w2 <> Nil{})),
    hti,
    FO.FO.bool_and_intro(
      Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{w1, Nil{}}, w1)),
      Bool.and(Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{w1, Nil{}}, w2)), True{}),
      hd1,
      FO.FO.bool_and_intro(
        Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{w1, Nil{}}, w2)), True{},
        hd2, {==})))

def FV.two_same_cost(+w1: +List<Nat>, +w2: +List<Nat>,
    +heq: {Feedback.word_eq(w1, w2) == True{} : Bool}) ->
  {Tree.cost(Tree.Node{w1, Nil{}}, w1 <> (w2 <> Nil{})) == 2n : Nat}:
  +e1 : {Maybe.default(&1, Nat, Tree.depth(Tree.Node{w1, Nil{}}, w1), 0n)
         == 1n : Nat} =
    Equal.cong(Maybe<Nat>, Nat, m => Maybe.default(&1, Nat, m, 0n),
      Tree.depth(Tree.Node{w1, Nil{}}, w1), Some{1n}, FV.depth_self(w1, Nil{}))
  +e2 : {Maybe.default(&1, Nat, Tree.depth(Tree.Node{w1, Nil{}}, w2), 0n)
         == 1n : Nat} =
    Equal.cong(Maybe<Nat>, Nat, m => Maybe.default(&1, Nat, m, 0n),
      Tree.depth(Tree.Node{w1, Nil{}}, w2), Some{1n},
      FV.depth_eq_word(w1, w2, Nil{}, heq))
  Equal.trans(Nat,
    Nat.add(Maybe.default(&1, Nat, Tree.depth(Tree.Node{w1, Nil{}}, w1), 0n),
      Nat.add(Maybe.default(&1, Nat, Tree.depth(Tree.Node{w1, Nil{}}, w2), 0n), 0n)),
    Nat.add(1n,
      Nat.add(Maybe.default(&1, Nat, Tree.depth(Tree.Node{w1, Nil{}}, w2), 0n), 0n)),
    2n,
    Equal.cong(Nat, Nat,
      x => Nat.add(x,
             Nat.add(Maybe.default(&1, Nat, Tree.depth(Tree.Node{w1, Nil{}}, w2), 0n), 0n)),
      Maybe.default(&1, Nat, Tree.depth(Tree.Node{w1, Nil{}}, w1), 0n), 1n, e1),
    Equal.cong(Nat, Nat, y => Nat.add(1n, Nat.add(y, 0n)),
      Maybe.default(&1, Nat, Tree.depth(Tree.Node{w1, Nil{}}, w2), 0n), 1n, e2))

def FV.bool_case_id_false(b: Bool,
    +e: {Feedback.Bool.case(Bool, b, True{}, False{}) == False{} : Bool}) ->
  {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Logic.Proof.true_ne_false(e))

def FV.word_eq_false_of_no_dup_two(+w1: +List<Nat>, +w2: +List<Nat>,
    +nd: {FN.FN.no_dup_ref(w1 <> (w2 <> Nil{})) == True{} : Bool}) ->
  {Feedback.word_eq(w1, w2) == False{} : Bool}:
  +nm : {Tree.member_word(w1, w2 <> Nil{}) == False{} : Bool} =
    FN.FN.false_of_not_true(Tree.member_word(w1, w2 <> Nil{}),
      Logic.Proof.and_true_l(Bool.not(Tree.member_word(w1, w2 <> Nil{})),
        FN.FN.no_dup_ref(w2 <> Nil{}), nd))
  FV.bool_case_id_false(Feedback.word_eq(w1, w2), nm)

def FV.no_dup_two_of_word_eq_false(+w1: +List<Nat>, +w2: +List<Nat>,
    +hne: {Feedback.word_eq(w1, w2) == False{} : Bool}) ->
  {FN.FN.no_dup_ref(w1 <> (w2 <> Nil{})) == True{} : Bool}:
  +nm : {Tree.member_word(w1, w2 <> Nil{}) == False{} : Bool} =
    Equal.cong(Bool, Bool,
      b => Feedback.Bool.case(Bool, b, True{}, False{}),
      Feedback.word_eq(w1, w2), False{}, hne)
  FO.FO.bool_and_intro(Bool.not(Tree.member_word(w1, w2 <> Nil{})),
    FN.FN.no_dup_ref(w2 <> Nil{}),
    FN.FN.not_true_of_false(Tree.member_word(w1, w2 <> Nil{}), nm), {==})

def FV.two_tree_depth_w2(+w1: +List<Nat>, +w2: +List<Nat>,
    +hne: {Feedback.word_eq(w1, w2) == False{} : Bool}) ->
  {Tree.depth(SolveFast.two_tree(w1, w2), w2) == Some{2n} : Maybe<Nat>}:
  +fb_f : +List<Feedback.Color> = SolveFast.feedback_fast(w1, w2)
  +fb_r : +List<Feedback.Color> = Feedback.feedback(w1, w2)
  +kids : +List<Tree.Child> = Tree.Child{fb_f, Tree.Node{w2, Nil{}}} <> Nil{}
  +efb_eq : {Feedback.feedback_eq(fb_f, fb_r) == True{} : Bool} =
    Equal.trans(Bool, Feedback.feedback_eq(fb_f, fb_r),
      Feedback.feedback_eq(fb_r, fb_r), True{},
      Equal.cong(+List<Feedback.Color>, Bool,
        x => Feedback.feedback_eq(x, fb_r), fb_f, fb_r,
        FG.FG.feedback_eq(w1, w2)),
      FbProof.FbPrf.feedback_eq_refl(fb_r))
  +e_go : {Tree.depth.go(kids, fb_r, w2)
           == Tree.depth(Tree.Node{w2, Nil{}}, w2) : Maybe<Nat>} =
    NV.NV.depth_go_head_at(w2, fb_r, fb_f, Tree.Node{w2, Nil{}}, Nil{}, efb_eq)
  +e_d2 : {Tree.depth.go(kids, fb_r, w2) == Some{1n} : Maybe<Nat>} =
    Equal.trans(Maybe<Nat>, Tree.depth.go(kids, fb_r, w2),
      Tree.depth(Tree.Node{w2, Nil{}}, w2), Some{1n},
      e_go, FV.depth_self(w2, Nil{}))
  Equal.trans(Maybe<Nat>,
    Tree.depth(Tree.Node{w1, kids}, w2),
    Tree.depth.bump(Tree.depth.go(kids, fb_r, w2)),
    Some{2n},
    Equal.cong(Bool, Maybe<Nat>,
      b => Feedback.Bool.case(Maybe<Nat>, b, Some{1n},
             Tree.depth.bump(Tree.depth.go(kids, fb_r, w2))),
      Feedback.word_eq(w1, w2), False{}, hne),
    Equal.cong(Maybe<Nat>, Maybe<Nat>, Tree.depth.bump,
      Tree.depth.go(kids, fb_r, w2), Some{1n}, e_d2))

def FV.two_tree_valid_b(+w1: +List<Nat>, +w2: +List<Nat>, +G: +List<+List<Nat>>,
    +w1in: {Tree.member_word(w1, G) == True{} : Bool},
    +w2in: {Tree.member_word(w2, G) == True{} : Bool},
    +hne: {Feedback.word_eq(w1, w2) == False{} : Bool}) ->
  {FV.valid_b(SolveFast.two_tree(w1, w2), G, w1 <> (w2 <> Nil{}))
   == True{} : Bool}:
  +t : Tree.Tree = SolveFast.two_tree(w1, w2)
  +fb_f : +List<Feedback.Color> = SolveFast.feedback_fast(w1, w2)
  +hti2 : {FV.tree_in_b(Tree.Node{w2, Nil{}}, G) == True{} : Bool} =
    FO.FO.bool_and_intro(Tree.member_word(w2, G), True{}, w2in, {==})
  +hki : {FV.kids_in_b(Tree.Child{fb_f, Tree.Node{w2, Nil{}}} <> Nil{}, G)
          == True{} : Bool} =
    FO.FO.bool_and_intro(FV.tree_in_b(Tree.Node{w2, Nil{}}, G), True{},
      hti2, {==})
  +hti : {FV.tree_in_b(t, G) == True{} : Bool} =
    FO.FO.bool_and_intro(Tree.member_word(w1, G),
      FV.kids_in_b(Tree.Child{fb_f, Tree.Node{w2, Nil{}}} <> Nil{}, G),
      w1in, hki)
  +hd1 : {Maybe.is_some(&1, Nat, Tree.depth(t, w1)) == True{} : Bool} =
    Equal.cong(Maybe<Nat>, Bool, m => Maybe.is_some(&1, Nat, m),
      Tree.depth(t, w1), Some{1n},
      FV.depth_self(w1, Tree.Child{fb_f, Tree.Node{w2, Nil{}}} <> Nil{}))
  +hd2 : {Maybe.is_some(&1, Nat, Tree.depth(t, w2)) == True{} : Bool} =
    Equal.cong(Maybe<Nat>, Bool, m => Maybe.is_some(&1, Nat, m),
      Tree.depth(t, w2), Some{2n}, FV.two_tree_depth_w2(w1, w2, hne))
  FO.FO.bool_and_intro(FV.tree_in_b(t, G),
    FV.all_have_depth_b(t, w1 <> (w2 <> Nil{})),
    hti,
    FO.FO.bool_and_intro(Maybe.is_some(&1, Nat, Tree.depth(t, w1)),
      Bool.and(Maybe.is_some(&1, Nat, Tree.depth(t, w2)), True{}),
      hd1,
      FO.FO.bool_and_intro(Maybe.is_some(&1, Nat, Tree.depth(t, w2)), True{},
        hd2, {==})))

def FV.two_tree_cost(+w1: +List<Nat>, +w2: +List<Nat>,
    +hne: {Feedback.word_eq(w1, w2) == False{} : Bool}) ->
  {Tree.cost(SolveFast.two_tree(w1, w2), w1 <> (w2 <> Nil{})) == 3n : Nat}:
  +t : Tree.Tree = SolveFast.two_tree(w1, w2)
  +fb_f : +List<Feedback.Color> = SolveFast.feedback_fast(w1, w2)
  +e1 : {Maybe.default(&1, Nat, Tree.depth(t, w1), 0n) == 1n : Nat} =
    Equal.cong(Maybe<Nat>, Nat, m => Maybe.default(&1, Nat, m, 0n),
      Tree.depth(t, w1), Some{1n},
      FV.depth_self(w1, Tree.Child{fb_f, Tree.Node{w2, Nil{}}} <> Nil{}))
  +e2 : {Maybe.default(&1, Nat, Tree.depth(t, w2), 0n) == 2n : Nat} =
    Equal.cong(Maybe<Nat>, Nat, m => Maybe.default(&1, Nat, m, 0n),
      Tree.depth(t, w2), Some{2n}, FV.two_tree_depth_w2(w1, w2, hne))
  Equal.trans(Nat,
    Nat.add(Maybe.default(&1, Nat, Tree.depth(t, w1), 0n),
      Nat.add(Maybe.default(&1, Nat, Tree.depth(t, w2), 0n), 0n)),
    Nat.add(1n, Nat.add(Maybe.default(&1, Nat, Tree.depth(t, w2), 0n), 0n)),
    3n,
    Equal.cong(Nat, Nat,
      x => Nat.add(x, Nat.add(Maybe.default(&1, Nat, Tree.depth(t, w2), 0n), 0n)),
      Maybe.default(&1, Nat, Tree.depth(t, w1), 0n), 1n, e1),
    Equal.cong(Nat, Nat, y => Nat.add(1n, Nat.add(y, 0n)),
      Maybe.default(&1, Nat, Tree.depth(t, w2), 0n), 2n, e2))

def FV.three_le_ref_two_go(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +w1: +List<Nat>, +w2: +List<Nat>,
    +ble: {Nat.is_le(2n, p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(w1 <> (w2 <> Nil{})) == True{} : Bool},
    b: Bool,
    +eb: {b == Nat.is_lt(Eval.Eval.cost_of(
            FS.FS.ref_run_at(p, inf, G, w1 <> (w2 <> Nil{}))), inf) : Bool}) ->
  {Nat.is_le(3n, Eval.Eval.cost_of(
     FS.FS.ref_run_at(p, inf, G, w1 <> (w2 <> Nil{})))) == True{} : Bool}:
  match b:
    case True{}:
      +ws2 : +List<+List<Nat>> = w1 <> (w2 <> Nil{})
      +rc : Nat = Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws2))
      +hlt : {Nat.is_lt(rc, inf) == True{} : Bool} =
        Equal.sym(Bool, True{}, Nat.is_lt(rc, inf), eb)
      +le_clb : {Nat.is_le(SolveFast.class_lb(ws2), rc) == True{} : Bool} =
        FLB.FS.child_size_le(p, inf, G, ws2, ble, hz, hlt)
      Fold.OQ.le_cong_l(3n, SolveFast.class_lb(ws2), rc,
        FN.FN.class_lb_nodup_eq(ws2, nd), le_clb)
    case False{}:
      +ws2 : +List<+List<Nat>> = w1 <> (w2 <> Nil{})
      +rc : Nat = Eval.Eval.cost_of(FS.FS.ref_run_at(p, inf, G, ws2))
      +hge : {Nat.is_le(inf, rc) == True{} : Bool} =
        FC.FC.le_of_lt_false(rc, inf,
          Equal.sym(Bool, False{}, Nat.is_lt(rc, inf), eb))
      NatProof.Nat.is_le_trans(3n, inf, rc,
        NatProof.Nat.is_le_of_lt(3n, inf, h3), hge)

def FV.three_le_ref_two(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +w1: +List<Nat>, +w2: +List<Nat>,
    +ble: {Nat.is_le(2n, p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h3: {Nat.is_lt(3n, inf) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(w1 <> (w2 <> Nil{})) == True{} : Bool}) ->
  {Nat.is_le(3n, Eval.Eval.cost_of(
     FS.FS.ref_run_at(p, inf, G, w1 <> (w2 <> Nil{})))) == True{} : Bool}:
  FV.three_le_ref_two_go(p, inf, G, w1, w2, ble, hz, h3, nd,
    Nat.is_lt(Eval.Eval.cost_of(
      FS.FS.ref_run_at(p, inf, G, w1 <> (w2 <> Nil{}))), inf), {==})

# Preserving the liveness invariant across `OneItem` (+1) and `TwoItem` (+3).
def FV.sat_add_k_eq(+inf: Nat, +sum: Nat, +k: Nat, +tail: Nat, +B: Nat,
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +alive: {Nat.is_lt(Nat.add(sum, Nat.add(k, tail)), B) == True{} : Bool}) ->
  {SolveRef.sat_add(inf, sum, k) == Nat.add(sum, k) : Nat}:
  +hlt : {Nat.is_lt(Nat.add(Nat.add(sum, k), tail), B) == True{} : Bool} =
    CBN.CB.lt_eq_l(B, Nat.add(sum, Nat.add(k, tail)),
      Nat.add(Nat.add(sum, k), tail),
      Equal.sym(Nat, Nat.add(Nat.add(sum, k), tail),
        Nat.add(sum, Nat.add(k, tail)), NatProof.NatPrf.add_assoc(sum, k, tail)),
      alive)
  FC.FC.sat_add_lt_eq(inf, sum, k, tail, B, hB, hlt)

def FV.sat_add_1_eq(+inf: Nat, +sum: Nat, +tail: Nat, +B: Nat,
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +alive: {Nat.is_lt(Nat.add(sum, Nat.add(1n, tail)), B) == True{} : Bool}) ->
  {SolveRef.sat_add(inf, sum, 1n) == Nat.add(sum, 1n) : Nat}:
  FV.sat_add_k_eq(inf, sum, 1n, tail, B, hB, alive)

def FV.sat_add_3_eq(+inf: Nat, +sum: Nat, +tail: Nat, +B: Nat,
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +alive: {Nat.is_lt(Nat.add(sum, Nat.add(3n, tail)), B) == True{} : Bool}) ->
  {SolveRef.sat_add(inf, sum, 3n) == Nat.add(sum, 3n) : Nat}:
  FV.sat_add_k_eq(inf, sum, 3n, tail, B, hB, alive)

def FV.alive_two(+inf: Nat, +sum: Nat, +tail: Nat, +B: Nat,
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +alive: {Nat.is_lt(Nat.add(sum, Nat.add(3n, tail)), B) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(SolveRef.sat_add(inf, sum, 3n), tail), B)
   == True{} : Bool}:
  +hlt : {Nat.is_lt(Nat.add(Nat.add(sum, 3n), tail), B) == True{} : Bool} =
    CBN.CB.lt_eq_l(B, Nat.add(sum, Nat.add(3n, tail)),
      Nat.add(Nat.add(sum, 3n), tail),
      Equal.sym(Nat, Nat.add(Nat.add(sum, 3n), tail),
        Nat.add(sum, Nat.add(3n, tail)), NatProof.NatPrf.add_assoc(sum, 3n, tail)),
      alive)
  +esat : {SolveRef.sat_add(inf, sum, 3n) == Nat.add(sum, 3n) : Nat} =
    FC.FC.sat_add_lt_eq(inf, sum, 3n, tail, B, hB, hlt)
  CBN.CB.lt_eq_l(B, Nat.add(Nat.add(sum, 3n), tail),
    Nat.add(SolveRef.sat_add(inf, sum, 3n), tail),
    Equal.cong(Nat, Nat, x => Nat.add(x, tail),
      Nat.add(sum, 3n), SolveRef.sat_add(inf, sum, 3n),
      Equal.sym(Nat, SolveRef.sat_add(inf, sum, 3n), Nat.add(sum, 3n), esat)),
    hlt)

# ---------------------------------------------------------------------------
# Finished node reconstruction: validity and cost from matched children
# ---------------------------------------------------------------------------

def FV.rev_groups(+gs: +List<Groups.Group>,
    +acc: +List<Groups.Group>) -> +List<Groups.Group>:
  match gs:
    case Nil{}:
      acc
    case Con{gp, t}:
      FV.rev_groups(t, gp <> acc)

def FV.kids_match_b(+G: +List<+List<Nat>>, +gs: +List<Groups.Group>,
    +ks: +List<Tree.Child>) -> Bool:
  match gs:
    case Nil{}:
      match ks:
        case Nil{}:
          True{}
        case Con{_, _}:
          False{}
    case Con{gp, gt}:
      match gp:
        case Groups.Group{fg, ws}:
          match ks:
            case Nil{}:
              False{}
            case Con{ch, kt}:
              match ch:
                case Tree.Child{fk, t}:
                  Bool.and(Feedback.feedback_eq(fg, fk),
                    Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, gt, kt)))

def FV.kids_cost_sum(+gs: +List<Groups.Group>, +ks: +List<Tree.Child>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case Con{gp, gt}:
      match gp:
        case Groups.Group{fg, ws}:
          match ks:
            case Nil{}:
              0n
            case Con{ch, kt}:
              match ch:
                case Tree.Child{fk, t}:
                  Nat.add(Tree.cost(t, ws), FV.kids_cost_sum(gt, kt))

def FV.rev_kids_match_ok(+G: +List<+List<Nat>>, +d: +List<Groups.Group>,
    +k: +List<Tree.Child>, +gf: +List<Groups.Group>, +kf: +List<Tree.Child>,
    +hd: {FV.kids_match_b(G, d, k) == True{} : Bool},
    +hf: {FV.kids_match_b(G, gf, kf) == True{} : Bool}) ->
  {FV.kids_match_b(G, FV.rev_groups(d, gf), SolveRef.rev_kids(k, kf))
   == True{} : Bool}:
  match d:
    case Nil{}:
      match k:
        case Nil{}:
          hf
        case Con{_, _}:
          Empty.absurd(
            {FV.kids_match_b(G, gf, SolveRef.rev_kids(k, kf)) == True{} : Bool},
            Logic.Proof.false_ne_true(hd))
    case Con{gp, dt}:
      match gp:
        case Groups.Group{+fg, +ws}:
          match k:
            case Nil{}:
              Empty.absurd(
                {FV.kids_match_b(G, FV.rev_groups(Groups.Group{fg, ws} <> dt, gf), kf)
                 == True{} : Bool},
                Logic.Proof.false_ne_true(hd))
            case Con{ch, kt}:
              match ch:
                case Tree.Child{+fk, +t}:
                  +hfb : {Feedback.feedback_eq(fg, fk) == True{} : Bool} =
                    Logic.Proof.and_true_l(Feedback.feedback_eq(fg, fk),
                      Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, dt, kt)), hd)
                  +hr : {Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, dt, kt))
                         == True{} : Bool} =
                    Logic.Proof.and_true_r(Feedback.feedback_eq(fg, fk),
                      Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, dt, kt)), hd)
                  +hv : {FV.valid_b(t, G, ws) == True{} : Bool} =
                    Logic.Proof.and_true_l(FV.valid_b(t, G, ws),
                      FV.kids_match_b(G, dt, kt), hr)
                  +hdt : {FV.kids_match_b(G, dt, kt) == True{} : Bool} =
                    Logic.Proof.and_true_r(FV.valid_b(t, G, ws),
                      FV.kids_match_b(G, dt, kt), hr)
                  FV.rev_kids_match_ok(G, dt, kt,
                    Groups.Group{fg, ws} <> gf, Tree.Child{fk, t} <> kf, hdt,
                    FO.FO.bool_and_intro(Feedback.feedback_eq(fg, fk),
                      Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, gf, kf)),
                      hfb,
                      FO.FO.bool_and_intro(FV.valid_b(t, G, ws),
                        FV.kids_match_b(G, gf, kf), hv, hf)))

def FV.rev_kids_cost_sum_eq(+G: +List<+List<Nat>>, +d: +List<Groups.Group>,
    +k: +List<Tree.Child>, +gf: +List<Groups.Group>, +kf: +List<Tree.Child>,
    +hd: {FV.kids_match_b(G, d, k) == True{} : Bool}) ->
  {FV.kids_cost_sum(FV.rev_groups(d, gf), SolveRef.rev_kids(k, kf))
   == Nat.add(FV.kids_cost_sum(d, k), FV.kids_cost_sum(gf, kf)) : Nat}:
  match d:
    case Nil{}:
      match k:
        case Nil{}:
          {==}
        case Con{_, _}:
          Empty.absurd(
            {FV.kids_cost_sum(gf, SolveRef.rev_kids(k, kf))
             == Nat.add(0n, FV.kids_cost_sum(gf, kf)) : Nat},
            Logic.Proof.false_ne_true(hd))
    case Con{gp, dt}:
      match gp:
        case Groups.Group{+fg, +ws}:
          match k:
            case Nil{}:
              Empty.absurd(
                {FV.kids_cost_sum(FV.rev_groups(Groups.Group{fg, ws} <> dt, gf), kf)
                 == Nat.add(0n, FV.kids_cost_sum(gf, kf)) : Nat},
                Logic.Proof.false_ne_true(hd))
            case Con{ch, kt}:
              match ch:
                case Tree.Child{+fk, +t}:
                  +hr : {Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, dt, kt))
                         == True{} : Bool} =
                    Logic.Proof.and_true_r(Feedback.feedback_eq(fg, fk),
                      Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, dt, kt)), hd)
                  +hdt : {FV.kids_match_b(G, dt, kt) == True{} : Bool} =
                    Logic.Proof.and_true_r(FV.valid_b(t, G, ws),
                      FV.kids_match_b(G, dt, kt), hr)
                  +c : Nat = Tree.cost(t, ws)
                  +sd : Nat = FV.kids_cost_sum(dt, kt)
                  +sf : Nat = FV.kids_cost_sum(gf, kf)
                  +ih : {FV.kids_cost_sum(FV.rev_groups(dt, Groups.Group{fg, ws} <> gf),
                           SolveRef.rev_kids(kt, Tree.Child{fk, t} <> kf))
                         == Nat.add(sd, Nat.add(c, sf)) : Nat} =
                    FV.rev_kids_cost_sum_eq(G, dt, kt,
                      Groups.Group{fg, ws} <> gf, Tree.Child{fk, t} <> kf, hdt)
                  Equal.trans(Nat,
                    FV.kids_cost_sum(FV.rev_groups(dt, Groups.Group{fg, ws} <> gf),
                      SolveRef.rev_kids(kt, Tree.Child{fk, t} <> kf)),
                    Nat.add(sd, Nat.add(c, sf)),
                    Nat.add(Nat.add(c, sd), sf),
                    ih,
                    Equal.trans(Nat,
                      Nat.add(sd, Nat.add(c, sf)),
                      Nat.add(c, Nat.add(sd, sf)),
                      Nat.add(Nat.add(c, sd), sf),
                      FLB.FS.add_swap_l(sd, c, sf),
                      Equal.sym(Nat, Nat.add(Nat.add(c, sd), sf),
                        Nat.add(c, Nat.add(sd, sf)),
                        NatProof.NatPrf.add_assoc(c, sd, sf))))

def FV.kids_in_of_match(+G: +List<+List<Nat>>, +gs: +List<Groups.Group>,
    +ks: +List<Tree.Child>,
    +hm: {FV.kids_match_b(G, gs, ks) == True{} : Bool}) ->
  {FV.kids_in_b(ks, G) == True{} : Bool}:
  match gs:
    case Nil{}:
      match ks:
        case Nil{}:
          {==}
        case Con{_, _}:
          Empty.absurd({FV.kids_in_b(ks, G) == True{} : Bool},
            Logic.Proof.false_ne_true(hm))
    case Con{gp, gt}:
      match gp:
        case Groups.Group{+fg, +ws}:
          match ks:
            case Nil{}:
              {==}
            case Con{ch, kt}:
              match ch:
                case Tree.Child{+fk, +t}:
                  +hr : {Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, gt, kt))
                         == True{} : Bool} =
                    Logic.Proof.and_true_r(Feedback.feedback_eq(fg, fk),
                      Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, gt, kt)), hm)
                  +hv : {FV.valid_b(t, G, ws) == True{} : Bool} =
                    Logic.Proof.and_true_l(FV.valid_b(t, G, ws),
                      FV.kids_match_b(G, gt, kt), hr)
                  +hgt : {FV.kids_match_b(G, gt, kt) == True{} : Bool} =
                    Logic.Proof.and_true_r(FV.valid_b(t, G, ws),
                      FV.kids_match_b(G, gt, kt), hr)
                  +hti : {FV.tree_in_b(t, G) == True{} : Bool} =
                    Logic.Proof.and_true_l(FV.tree_in_b(t, G),
                      FV.all_have_depth_b(t, ws), hv)
                  Equal.trans(Bool,
                    FV.kids_in_b(Tree.Child{fk, t} <> kt, G),
                    Bool.and(FV.tree_in_b(t, G), FV.kids_in_b(kt, G)),
                    True{},
                    FV.kids_in_cons(fk, t, kt, G),
                    FO.FO.bool_and_intro(FV.tree_in_b(t, G), FV.kids_in_b(kt, G),
                      hti, FV.kids_in_of_match(G, gt, kt, hgt)))

def FV.depth_of_in_words(+t: Tree.Tree, +ws: +List<+List<Nat>>, +w: +List<Nat>,
    +hd: {FV.all_have_depth_b(t, ws) == True{} : Bool},
    iw: Grp.Grp.InWords(w, ws)) ->
  {Maybe.is_some(&1, Nat, Tree.depth(t, w)) == True{} : Bool}:
  match ws:
    case Nil{}:
      Empty.absurd(
        {Maybe.is_some(&1, Nat, Tree.depth(t, w)) == True{} : Bool}, iw)
    case Con{+h, +r}:
      match iw:
        case Inl{ewh}:
          +dh : {Maybe.is_some(&1, Nat, Tree.depth(t, h)) == True{} : Bool} =
            Logic.Proof.and_true_l(Maybe.is_some(&1, Nat, Tree.depth(t, h)),
              FV.all_have_depth_b(t, r), hd)
          %Equal.sym(+List<Nat>, w, h, ewh) :
            {Maybe.is_some(&1, Nat, Tree.depth(t, _)) == True{} : Bool}
          dh
        case Inr{iwr}:
          +dr : {FV.all_have_depth_b(t, r) == True{} : Bool} =
            Logic.Proof.and_true_r(Maybe.is_some(&1, Nat, Tree.depth(t, h)),
              FV.all_have_depth_b(t, r), hd)
          FV.depth_of_in_words(t, r, w, dr, iwr)

def FV.allne_false_of_in_groups_fb(+f: +List<Feedback.Color>,
    +fb: +List<Feedback.Color>, +gs: +List<Groups.Group>, +w: +List<Nat>,
    +hne: {CBK.CBK.allNe(f, gs) == True{} : Bool},
    m: NV.NV.InGroupsFb(w, fb, gs)) ->
  {Feedback.feedback_eq(f, fb) == False{} : Bool}:
  match gs:
    case Nil{}:
      match m:
    case Con{gp, gt}:
      match gp:
        case Groups.Group{+f2, +ws}:
          match m:
            case Inl{pin}:
              (iw, efb) = pin
              +h1 : {Bool.not(Feedback.feedback_eq(f, f2)) == True{} : Bool} =
                Logic.Proof.and_true_l(Bool.not(Feedback.feedback_eq(f, f2)),
                  CBK.CBK.allNe(f, gt), hne)
              +eff2 : {Feedback.feedback_eq(f, f2) == False{} : Bool} =
                CBK.CBK.not_true(Feedback.feedback_eq(f, f2), h1)
              Equal.trans(Bool,
                Feedback.feedback_eq(f, fb),
                Feedback.feedback_eq(f, f2),
                False{},
                Equal.cong(+List<Feedback.Color>, Bool,
                  x => Feedback.feedback_eq(f, x), fb, f2,
                  FbProof.FbPrf.feedback_eq_true(fb, f2, efb)),
                eff2)
            case Inr{mt}:
              +h2 : {CBK.CBK.allNe(f, gt) == True{} : Bool} =
                Logic.Proof.and_true_r(Bool.not(Feedback.feedback_eq(f, f2)),
                  CBK.CBK.allNe(f, gt), hne)
              FV.allne_false_of_in_groups_fb(f, fb, gt, w, h2, mt)

def FV.depth_go_of_match_inr(+G: +List<+List<Nat>>, +fg: +List<Feedback.Color>,
    +fk: +List<Feedback.Color>, +t: Tree.Tree, +gt: +List<Groups.Group>,
    +kt: +List<Tree.Child>, +w: +List<Nat>, +fb: +List<Feedback.Color>,
    +hne: {CBK.CBK.allNe(fg, gt) == True{} : Bool},
    +efgfk: {fg == fk : +List<Feedback.Color>},
    b: Bool, +eb: {b == Feedback.feedback_eq(fg, fb) : Bool},
    mt: NV.NV.InGroupsFb(w, fb, gt),
    rec: NV.NV.InGroupsFb(w, fb, gt) ->
      {Maybe.is_some(&1, Nat, Tree.depth.go(kt, fb, w)) == True{} : Bool}) ->
  {Maybe.is_some(&1, Nat, Tree.depth.go(Tree.Child{fk, t} <> kt, fb, w))
   == True{} : Bool}:
  match b:
    case True{}:
      +efalse : {Feedback.feedback_eq(fg, fb) == False{} : Bool} =
        FV.allne_false_of_in_groups_fb(fg, fb, gt, w, hne, mt)
      Empty.absurd(
        {Maybe.is_some(&1, Nat, Tree.depth.go(Tree.Child{fk, t} <> kt, fb, w))
         == True{} : Bool},
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, Feedback.feedback_eq(fg, fb), False{},
            eb, efalse)))
    case False{}:
      +efgfb : {Feedback.feedback_eq(fg, fb) == False{} : Bool} =
        Equal.sym(Bool, False{}, Feedback.feedback_eq(fg, fb), eb)
      +efkfb : {Feedback.feedback_eq(fk, fb) == False{} : Bool} =
        Equal.trans(Bool,
          Feedback.feedback_eq(fk, fb),
          Feedback.feedback_eq(fg, fb),
          False{},
          Equal.cong(+List<Feedback.Color>, Bool,
            x => Feedback.feedback_eq(x, fb), fk, fg,
            Equal.sym(+List<Feedback.Color>, fg, fk, efgfk)),
          efgfb)
      +eskip : {Tree.depth.go(Tree.Child{fk, t} <> kt, fb, w)
                == Tree.depth.go(kt, fb, w) : Maybe<Nat>} =
        NV.NV.depth_go_skip(w, fb, fk, t, kt, efkfb)
      Equal.trans(Bool,
        Maybe.is_some(&1, Nat,
          Tree.depth.go(Tree.Child{fk, t} <> kt, fb, w)),
        Maybe.is_some(&1, Nat, Tree.depth.go(kt, fb, w)),
        True{},
        Equal.cong(Maybe<Nat>, Bool, x => Maybe.is_some(&1, Nat, x),
          Tree.depth.go(Tree.Child{fk, t} <> kt, fb, w),
          Tree.depth.go(kt, fb, w), eskip),
        rec(mt))

def FV.depth_go_of_match(+G: +List<+List<Nat>>, +gs: +List<Groups.Group>,
    +ks: +List<Tree.Child>, +w: +List<Nat>, +fb: +List<Feedback.Color>,
    +hdist: {CBK.CBK.distinctB(gs) == True{} : Bool},
    +hm: {FV.kids_match_b(G, gs, ks) == True{} : Bool},
    m: NV.NV.InGroupsFb(w, fb, gs)) ->
  {Maybe.is_some(&1, Nat, Tree.depth.go(ks, fb, w)) == True{} : Bool}:
  match gs:
    case Nil{}:
      match m:
    case Con{gp, gt}:
      match gp:
        case Groups.Group{+fg, +ws}:
          match ks:
            case Nil{}:
              Empty.absurd(
                {Maybe.is_some(&1, Nat, Tree.depth.go(Nil{}, fb, w)) == True{} : Bool},
                Logic.Proof.false_ne_true(hm))
            case Con{ch, kt}:
              match ch:
                case Tree.Child{+fk, +t}:
                  match m:
                    case Inl{pin}:
                      (iw, efbfg) = pin
                      +hfb : {Feedback.feedback_eq(fg, fk) == True{} : Bool} =
                        Logic.Proof.and_true_l(Feedback.feedback_eq(fg, fk),
                          Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, gt, kt)), hm)
                      +hr : {Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, gt, kt))
                             == True{} : Bool} =
                        Logic.Proof.and_true_r(Feedback.feedback_eq(fg, fk),
                          Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, gt, kt)), hm)
                      +hv : {FV.valid_b(t, G, ws) == True{} : Bool} =
                        Logic.Proof.and_true_l(FV.valid_b(t, G, ws),
                          FV.kids_match_b(G, gt, kt), hr)
                      +efgfk : {fg == fk : +List<Feedback.Color>} =
                        FbProof.FbPrf.feedback_eq_true(fg, fk, hfb)
                      +efkfb : {Feedback.feedback_eq(fk, fb) == True{} : Bool} =
                        Equal.trans(Bool,
                          Feedback.feedback_eq(fk, fb),
                          Feedback.feedback_eq(fg, fb),
                          True{},
                          Equal.cong(+List<Feedback.Color>, Bool,
                            x => Feedback.feedback_eq(x, fb), fk, fg,
                            Equal.sym(+List<Feedback.Color>, fg, fk, efgfk)),
                          FbProof.FeedbackProof.feedback_eq_sym(fb, fg, efbfg))
                      +ehead : {Tree.depth.go(Tree.Child{fk, t} <> kt, fb, w)
                                == Tree.depth(t, w) : Maybe<Nat>} =
                        NV.NV.depth_go_head_at(w, fb, fk, t, kt, efkfb)
                      +ahd : {FV.all_have_depth_b(t, ws) == True{} : Bool} =
                        Logic.Proof.and_true_r(FV.tree_in_b(t, G),
                          FV.all_have_depth_b(t, ws), hv)
                      Equal.trans(Bool,
                        Maybe.is_some(&1, Nat,
                          Tree.depth.go(Tree.Child{fk, t} <> kt, fb, w)),
                        Maybe.is_some(&1, Nat, Tree.depth(t, w)),
                        True{},
                        Equal.cong(Maybe<Nat>, Bool, x => Maybe.is_some(&1, Nat, x),
                          Tree.depth.go(Tree.Child{fk, t} <> kt, fb, w),
                          Tree.depth(t, w), ehead),
                        FV.depth_of_in_words(t, ws, w, ahd, iw))
                    case Inr{mt}:
                      +hne : {CBK.CBK.allNe(fg, gt) == True{} : Bool} =
                        Logic.Proof.and_true_l(CBK.CBK.allNe(fg, gt),
                          CBK.CBK.distinctB(gt), hdist)
                      +hdt : {CBK.CBK.distinctB(gt) == True{} : Bool} =
                        Logic.Proof.and_true_r(CBK.CBK.allNe(fg, gt),
                          CBK.CBK.distinctB(gt), hdist)
                      +hfb : {Feedback.feedback_eq(fg, fk) == True{} : Bool} =
                        Logic.Proof.and_true_l(Feedback.feedback_eq(fg, fk),
                          Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, gt, kt)), hm)
                      +hr : {Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, gt, kt))
                             == True{} : Bool} =
                        Logic.Proof.and_true_r(Feedback.feedback_eq(fg, fk),
                          Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, gt, kt)), hm)
                      +hmt : {FV.kids_match_b(G, gt, kt) == True{} : Bool} =
                        Logic.Proof.and_true_r(FV.valid_b(t, G, ws),
                          FV.kids_match_b(G, gt, kt), hr)
                      +efgfk : {fg == fk : +List<Feedback.Color>} =
                        FbProof.FbPrf.feedback_eq_true(fg, fk, hfb)
                      FV.depth_go_of_match_inr(G, fg, fk, t, gt, kt, w, fb,
                        hne, efgfk, Feedback.feedback_eq(fg, fb), {==}, mt,
                        mt2 => FV.depth_go_of_match(G, gt, kt, w, fb, hdt, hmt, mt2))

def FV.word_depth_of_match_go(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +rkids: +List<Tree.Child>, +w: +List<Nat>,
    iw: Grp.Grp.InWords(w, S),
    +hm: {FV.kids_match_b(G, Groups.groups_build(g, S, Nil{}), rkids)
          == True{} : Bool},
    b: Bool, +eb: {b == Feedback.word_eq(g, w) : Bool}) ->
  {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, rkids}, w))
   == True{} : Bool}:
  match b:
    case True{}:
      Equal.cong(Maybe<Nat>, Bool, m => Maybe.is_some(&1, Nat, m),
        Tree.depth(Tree.Node{g, rkids}, w), Some{1n},
        FV.depth_eq_word(g, w, rkids,
          Equal.sym(Bool, True{}, Feedback.word_eq(g, w), eb)))
    case False{}:
      +hne : {Feedback.word_eq(g, w) == False{} : Bool} =
        Equal.sym(Bool, False{}, Feedback.word_eq(g, w), eb)
      +hgo : {Maybe.is_some(&1, Nat,
                Tree.depth.go(rkids, Feedback.feedback(g, w), w))
              == True{} : Bool} =
        FV.depth_go_of_match(G, Groups.groups_build(g, S, Nil{}), rkids, w,
          Feedback.feedback(g, w), CBK.CBK.distinctB_build(g, S), hm,
          NV.NV.groups_build_contains_fb(g, S, w, iw, hne, Nil{}))
      DG.DG.node_depth_bool(g, rkids, w, Feedback.word_eq(g, w), {==}, hgo)

def FV.all_have_depth_of_match_go(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +rkids: +List<Tree.Child>, +rem: +List<+List<Nat>>,
    +wpre: +List<+List<Nat>>,
    +eS: {S == List.append(&2, +List<Nat>, wpre, rem) : +List<+List<Nat>>},
    +hm: {FV.kids_match_b(G, Groups.groups_build(g, S, Nil{}), rkids)
          == True{} : Bool}) ->
  {FV.all_have_depth_b(Tree.Node{g, rkids}, rem) == True{} : Bool}:
  match rem:
    case Nil{}:
      {==}
    case Con{+w, +wt}:
      iw : Grp.Grp.InWords(w, S) =
        SV.SV.in_words_transport(
          List.append(&2, +List<Nat>, wpre, w <> wt), S,
          Equal.sym(+List<+List<Nat>>, S,
            List.append(&2, +List<Nat>, wpre, w <> wt), eS),
          w, SV.SV.in_words_at(wpre, w, wt))
      +eS2 : {S == List.append(&2, +List<Nat>,
                     List.append(&2, +List<Nat>, wpre, w <> Nil{}), wt)
              : +List<+List<Nat>>} =
        Equal.trans(+List<+List<Nat>>, S,
          List.append(&2, +List<Nat>, wpre, w <> wt),
          List.append(&2, +List<Nat>,
            List.append(&2, +List<Nat>, wpre, w <> Nil{}), wt),
          eS, SV.SV.append_singleton(wpre, w, wt))
      FO.FO.bool_and_intro(
        Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, rkids}, w)),
        FV.all_have_depth_b(Tree.Node{g, rkids}, wt),
        FV.word_depth_of_match_go(G, S, g, rkids, w, iw, hm,
          Feedback.word_eq(g, w), {==}),
        FV.all_have_depth_of_match_go(G, S, g, rkids, wt,
          List.append(&2, +List<Nat>, wpre, w <> Nil{}), eS2, hm))

def FV.total_eq_kids_cost_sum(+G: +List<+List<Nat>>, +gs: +List<Groups.Group>,
    +ks: +List<Tree.Child>,
    +hdist: {CBK.CBK.distinctB(gs) == True{} : Bool},
    +hm: {FV.kids_match_b(G, gs, ks) == True{} : Bool}) ->
  {GC.GC.Total(ks, gs) == FV.kids_cost_sum(gs, ks) : Nat}:
  match gs:
    case Nil{}:
      match ks:
        case Nil{}:
          {==}
        case Con{_, _}:
          Empty.absurd({0n == 0n : Nat}, Logic.Proof.false_ne_true(hm))
    case Con{gp, gt}:
      match gp:
        case Groups.Group{+fg, +ws}:
          match ks:
            case Nil{}:
              Empty.absurd(
                {GC.GC.Total(Nil{}, Groups.Group{fg, ws} <> gt) == 0n : Nat},
                Logic.Proof.false_ne_true(hm))
            case Con{ch, kt}:
              match ch:
                case Tree.Child{+fk, +t}:
                  +hne : {CBK.CBK.allNe(fg, gt) == True{} : Bool} =
                    Logic.Proof.and_true_l(CBK.CBK.allNe(fg, gt),
                      CBK.CBK.distinctB(gt), hdist)
                  +hdt : {CBK.CBK.distinctB(gt) == True{} : Bool} =
                    Logic.Proof.and_true_r(CBK.CBK.allNe(fg, gt),
                      CBK.CBK.distinctB(gt), hdist)
                  +hfb : {Feedback.feedback_eq(fg, fk) == True{} : Bool} =
                    Logic.Proof.and_true_l(Feedback.feedback_eq(fg, fk),
                      Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, gt, kt)), hm)
                  +hr : {Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, gt, kt))
                         == True{} : Bool} =
                    Logic.Proof.and_true_r(Feedback.feedback_eq(fg, fk),
                      Bool.and(FV.valid_b(t, G, ws), FV.kids_match_b(G, gt, kt)), hm)
                  +hmt : {FV.kids_match_b(G, gt, kt) == True{} : Bool} =
                    Logic.Proof.and_true_r(FV.valid_b(t, G, ws),
                      FV.kids_match_b(G, gt, kt), hr)
                  +efgfk : {fg == fk : +List<Feedback.Color>} =
                    FbProof.FbPrf.feedback_eq_true(fg, fk, hfb)
                  +k0 : +List<Tree.Child> = Tree.Child{fg, t} <> kt
                  +ek : {Tree.Child{fk, t} <> kt == k0 : +List<Tree.Child>} =
                    Equal.cong(+List<Feedback.Color>, +List<Tree.Child>,
                      x => Tree.Child{x, t} <> kt, fk, fg,
                      Equal.sym(+List<Feedback.Color>, fg, fk, efgfk))
                  +e_head : {GC.GC.GroupCost(k0, Groups.Group{fg, ws})
                             == Tree.cost(t, ws) : Nat} =
                    Equal.cong(Maybe<Tree.Tree>, Nat,
                      m => GC.GC.group_cost_of(k0, ws, m),
                      Tree.lookup(fg, k0), Some{t},
                      CBK.CBK.lookup_head(fg, t, kt))
                  +e_tail : {GC.GC.Total(k0, gt) == GC.GC.Total(kt, gt) : Nat} =
                    CBK.CBK.total_lk_eqs(k0, kt, gt,
                      CBK.CBK.skip_eqs(fg, t, kt, gt, hne))
                  +ih : {GC.GC.Total(kt, gt) == FV.kids_cost_sum(gt, kt) : Nat} =
                    FV.total_eq_kids_cost_sum(G, gt, kt, hdt, hmt)
                  +e_k0 : {GC.GC.Total(k0, Groups.Group{fg, ws} <> gt)
                           == Nat.add(Tree.cost(t, ws), FV.kids_cost_sum(gt, kt))
                           : Nat} =
                    Equal.trans(Nat,
                      Nat.add(GC.GC.GroupCost(k0, Groups.Group{fg, ws}),
                        GC.GC.Total(k0, gt)),
                      Nat.add(Tree.cost(t, ws), GC.GC.Total(k0, gt)),
                      Nat.add(Tree.cost(t, ws), FV.kids_cost_sum(gt, kt)),
                      Equal.cong(Nat, Nat, x => Nat.add(x, GC.GC.Total(k0, gt)),
                        GC.GC.GroupCost(k0, Groups.Group{fg, ws}),
                        Tree.cost(t, ws), e_head),
                      Equal.cong(Nat, Nat, x => Nat.add(Tree.cost(t, ws), x),
                        GC.GC.Total(k0, gt), FV.kids_cost_sum(gt, kt),
                        Equal.trans(Nat, GC.GC.Total(k0, gt), GC.GC.Total(kt, gt),
                          FV.kids_cost_sum(gt, kt), e_tail, ih)))
                  Equal.trans(Nat,
                    GC.GC.Total(Tree.Child{fk, t} <> kt, Groups.Group{fg, ws} <> gt),
                    GC.GC.Total(k0, Groups.Group{fg, ws} <> gt),
                    Nat.add(Tree.cost(t, ws), FV.kids_cost_sum(gt, kt)),
                    Equal.cong(+List<Tree.Child>, Nat,
                      l => GC.GC.Total(l, Groups.Group{fg, ws} <> gt),
                      Tree.Child{fk, t} <> kt, k0, ek),
                    e_k0)

def FV.end_node_ok(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +done_rev: +List<Groups.Group>, +kids: +List<Tree.Child>,
    +sum: Nat,
    +wg: {Tree.member_word(g, G) == True{} : Bool},
    +esplit: {FV.rev_groups(done_rev, Nil{})
              == Groups.groups_build(g, S, Nil{}) : +List<Groups.Group>},
    +hm: {FV.kids_match_b(G, done_rev, kids) == True{} : Bool},
    +hcs: {Nat.is_le(FV.kids_cost_sum(done_rev, kids), sum) == True{} : Bool}) ->
  {Bool.and(
     FV.valid_b(Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, G, S),
     Nat.is_le(Tree.cost(Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, S),
       Nat.add(Groups.len_words(S), sum))) == True{} : Bool}:
  +full : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
  +rkids : +List<Tree.Child> = SolveRef.rev_kids(kids, Nil{})
  +hm_rev : {FV.kids_match_b(G, FV.rev_groups(done_rev, Nil{}), rkids)
             == True{} : Bool} =
    FV.rev_kids_match_ok(G, done_rev, kids, Nil{}, Nil{}, hm, {==})
  +hm_full : {FV.kids_match_b(G, full, rkids) == True{} : Bool} =
    Equal.trans(Bool,
      FV.kids_match_b(G, full, rkids),
      FV.kids_match_b(G, FV.rev_groups(done_rev, Nil{}), rkids),
      True{},
      Equal.cong(+List<Groups.Group>, Bool,
        gs => FV.kids_match_b(G, gs, rkids),
        full, FV.rev_groups(done_rev, Nil{}),
        Equal.sym(+List<Groups.Group>,
          FV.rev_groups(done_rev, Nil{}), full, esplit)),
      hm_rev)
  +hvalid : {FV.valid_b(Tree.Node{g, rkids}, G, S) == True{} : Bool} =
    FO.FO.bool_and_intro(FV.tree_in_b(Tree.Node{g, rkids}, G),
      FV.all_have_depth_b(Tree.Node{g, rkids}, S),
      FO.FO.bool_and_intro(Tree.member_word(g, G), FV.kids_in_b(rkids, G),
        wg, FV.kids_in_of_match(G, full, rkids, hm_full)),
      FV.all_have_depth_of_match_go(G, S, g, rkids, S, Nil{}, {==}, hm_full))
  +ecs_rev : {FV.kids_cost_sum(FV.rev_groups(done_rev, Nil{}), rkids)
              == FV.kids_cost_sum(done_rev, kids) : Nat} =
    Equal.trans(Nat,
      FV.kids_cost_sum(FV.rev_groups(done_rev, Nil{}), rkids),
      Nat.add(FV.kids_cost_sum(done_rev, kids), 0n),
      FV.kids_cost_sum(done_rev, kids),
      FV.rev_kids_cost_sum_eq(G, done_rev, kids, Nil{}, Nil{}, hm),
      NatProof.NatPrf.add_zero(FV.kids_cost_sum(done_rev, kids)))
  +ecs_full : {FV.kids_cost_sum(full, rkids)
               == FV.kids_cost_sum(done_rev, kids) : Nat} =
    Equal.trans(Nat,
      FV.kids_cost_sum(full, rkids),
      FV.kids_cost_sum(FV.rev_groups(done_rev, Nil{}), rkids),
      FV.kids_cost_sum(done_rev, kids),
      Equal.cong(+List<Groups.Group>, Nat, gs => FV.kids_cost_sum(gs, rkids),
        full, FV.rev_groups(done_rev, Nil{}),
        Equal.sym(+List<Groups.Group>,
          FV.rev_groups(done_rev, Nil{}), full, esplit)),
      ecs_rev)
  +ekid_eq : {NodeCost.NodeCost.kid_sum(g, rkids, S)
              == FV.kids_cost_sum(done_rev, kids) : Nat} =
    Equal.trans(Nat,
      NodeCost.NodeCost.kid_sum(g, rkids, S),
      GC.GC.Total(rkids, full),
      FV.kids_cost_sum(done_rev, kids),
      Equal.sym(Nat, GC.GC.Total(rkids, full),
        NodeCost.NodeCost.kid_sum(g, rkids, S),
        GC.GC.groups_build_total(g, rkids, S)),
      Equal.trans(Nat,
        GC.GC.Total(rkids, full),
        FV.kids_cost_sum(full, rkids),
        FV.kids_cost_sum(done_rev, kids),
        FV.total_eq_kids_cost_sum(G, full, rkids,
          CBK.CBK.distinctB_build(g, S), hm_full),
        ecs_full))
  +hkid_le : {Nat.is_le(NodeCost.NodeCost.kid_sum(g, rkids, S), sum)
              == True{} : Bool} =
    Fold.OQ.le_cong_l(NodeCost.NodeCost.kid_sum(g, rkids, S),
      FV.kids_cost_sum(done_rev, kids), sum, ekid_eq, hcs)
  +hcost : {Nat.is_le(Tree.cost(Tree.Node{g, rkids}, S),
              Nat.add(Groups.len_words(S), sum)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(
      Tree.cost(Tree.Node{g, rkids}, S),
      Nat.add(Groups.len_words(S), NodeCost.NodeCost.kid_sum(g, rkids, S)),
      Nat.add(Groups.len_words(S), sum),
      OC.OC.cost_node_le(g, rkids, S),
      NatProof.Nat.is_le_add_l(NodeCost.NodeCost.kid_sum(g, rkids, S),
        sum, Groups.len_words(S), hkid_le))
  FO.FO.bool_and_intro(FV.valid_b(Tree.Node{g, rkids}, G, S),
    Nat.is_le(Tree.cost(Tree.Node{g, rkids}, S),
      Nat.add(Groups.len_words(S), sum)),
    hvalid, hcost)

# ---------------------------------------------------------------------------
# Floor soundness: `2*n - 1` (`FloorInit`) and `2*n` after `S` (`FloorAfterS`)
# ---------------------------------------------------------------------------

def FV.after_s_guess_skip_in_us(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +best: SolveRef.Best,
    +mem: {Tree.member_word(g, S) == True{} : Bool},
    +h_after_s: {Nat.is_le(Eval.Eval.cost_of(best),
                   Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                     Eval.Eval.dummy_inf(inf)))) == True{} : Bool},
    us: Bool,
    +eus: {us == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           : Bool}) ->
  {Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf,
     us, best) == best : SolveRef.Best}:
  match us:
    case False{}:
      {==}
    case True{}:
      +hus : {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
              == True{} : Bool} =
        Equal.sym(Bool, True{},
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), eus)
      +grp : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
      +ks : Eval.KS = Eval.Eval.items(p, G, S, g, grp, Nil{}, 0n, inf)
      +hs_le_cand : {Nat.is_le(
                       Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                         Eval.Eval.dummy_inf(inf))),
                       Fold.OQ.ks_cost(inf, S, ks)) == True{} : Bool} =
        OQGuess.OQ.guesses_le_cand(p, G, S, inf, S, g,
          Eval.Eval.dummy_inf(inf), mem, hus)
      Equal.trans(SolveRef.Best,
        Eval.Eval.block(p, G, S, g, inf, grp, best),
        SolveRef.better(Fold.OQ.ks_cost(inf, S, ks), Fold.OQ.ks_tree(g, ks), best),
        best,
        Fold.OQ.block_eq(inf, g, S, ks, best),
        FB.FS.keep(Fold.OQ.ks_cost(inf, S, ks), Fold.OQ.ks_tree(g, ks), best,
          Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
            Eval.Eval.dummy_inf(inf))),
          h_after_s, hs_le_cand))

def FV.after_s_guess_skip(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +best: SolveRef.Best,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +h2n: {Nat.is_le(Eval.Eval.cost_of(best),
             Nat.add(Groups.len_words(S), Groups.len_words(S)))
           == True{} : Bool},
    +h_after_s: {Nat.is_le(Eval.Eval.cost_of(best),
                   Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                     Eval.Eval.dummy_inf(inf)))) == True{} : Bool},
    in_s: Bool, +ein: {in_s == Tree.member_word(g, S) : Bool}) ->
  {Eval.Eval.guess(p, G, S, g, inf, best) == best : SolveRef.Best}:
  match in_s:
    case True{}:
      FV.after_s_guess_skip_in_us(p, inf, G, S, g, best,
        Equal.sym(Bool, True{}, Tree.member_word(g, S), ein),
        h_after_s,
        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==})
    case False{}:
      +n : Nat = Groups.len_words(S)
      +nm : {Tree.member_word(g, S) == False{} : Bool} =
        Equal.sym(Bool, False{}, Tree.member_word(g, S), ein)
      +hle : {Nat.is_le(Eval.Eval.cost_of(best), SolveFast.pre_lb(n, g, S))
              == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(Eval.Eval.cost_of(best), Nat.add(n, n),
          SolveFast.pre_lb(n, g, S),
          Equal.sym(Nat, SolveFast.pre_lb(n, g, S), Nat.add(n, n),
            FN.FN.pre_lb_of_not_member(g, S, nm)),
          h2n)
      FLB.FS.pre_guess_skip_eq(p, inf, G, S, g, best, ele, hz, hbest, hle)

def FV.after_s_guesses_skip(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>, +best: SolveRef.Best,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +h2n: {Nat.is_le(Eval.Eval.cost_of(best),
             Nat.add(Groups.len_words(S), Groups.len_words(S)))
           == True{} : Bool},
    +h_after_s: {Nat.is_le(Eval.Eval.cost_of(best),
                   Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                     Eval.Eval.dummy_inf(inf)))) == True{} : Bool}) ->
  {Eval.Eval.guesses(1n+p, G, S, inf, gs, best) == best : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      +eg : {Eval.Eval.guess(p, G, S, g, inf, best) == best : SolveRef.Best} =
        FV.after_s_guess_skip(p, inf, G, S, g, best, ele, hz, hbest, h2n,
          h_after_s, Tree.member_word(g, S), {==})
      Equal.trans(SolveRef.Best,
        Eval.Eval.guesses(1n+p, G, S, inf, t,
          Eval.Eval.guess(p, G, S, g, inf, best)),
        Eval.Eval.guesses(1n+p, G, S, inf, t, best),
        best,
        Equal.cong(SolveRef.Best, SolveRef.Best,
          b => Eval.Eval.guesses(1n+p, G, S, inf, t, b),
          Eval.Eval.guess(p, G, S, g, inf, best), best, eg),
        FV.after_s_guesses_skip(p, inf, G, S, t, best, ele, hz, hbest, h2n,
          h_after_s))

def FV.le_ref_of_guesses_fixed(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +best: SolveRef.Best,
    +ele: {Nat.is_le(Groups.len_words(S), fuel) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +efix: {Eval.Eval.guesses(fuel, G, S, inf, G, best) == best
            : SolveRef.Best}) ->
  {Nat.is_le(Eval.Eval.cost_of(best),
             Eval.Eval.cost_of(FS.FS.ref_run_at(fuel, inf, G, S)))
   == True{} : Bool}:
  +eb : {best == FC.FC.better_best(FS.FS.ref_run_at(fuel, inf, G, S), best)
         : SolveRef.Best} =
    Equal.trans(SolveRef.Best,
      best,
      Eval.Eval.guesses(fuel, G, S, inf, G, best),
      FC.FC.better_best(FS.FS.ref_run_at(fuel, inf, G, S), best),
      Equal.sym(SolveRef.Best,
        Eval.Eval.guesses(fuel, G, S, inf, G, best), best, efix),
      FC.FC.eval_guesses_from(fuel, inf, G, S, best, ele, hbest))
  Fold.OQ.le_cong_l(Eval.Eval.cost_of(best),
    Eval.Eval.cost_of(FC.FC.better_best(FS.FS.ref_run_at(fuel, inf, G, S), best)),
    Eval.Eval.cost_of(FS.FS.ref_run_at(fuel, inf, G, S)),
    Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of, best,
      FC.FC.better_best(FS.FS.ref_run_at(fuel, inf, G, S), best), eb),
    FV.better_best_le_l(FS.FS.ref_run_at(fuel, inf, G, S), best))

def FV.after_s_floor_le(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +best: SolveRef.Best,
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +h2n: {Nat.is_le(Eval.Eval.cost_of(best),
             Nat.add(Groups.len_words(S), Groups.len_words(S)))
           == True{} : Bool},
    +h_after_s: {Nat.is_le(Eval.Eval.cost_of(best),
                   Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, S,
                     Eval.Eval.dummy_inf(inf)))) == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(best),
             Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)))
   == True{} : Bool}:
  FV.le_ref_of_guesses_fixed(1n+p, inf, G, S, best, ele, hbest,
    FV.after_s_guesses_skip(p, inf, G, S, G, best, ele, hz, hbest, h2n,
      h_after_s))

def FV.floor_init_le_ref(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +best: SolveRef.Best,
    +nd: {FN.FN.no_dup_ref(S) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hfl: {Nat.is_le(Eval.Eval.cost_of(best),
             SolveFast.init_floor(Groups.len_words(S))) == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(best),
             Eval.Eval.cost_of(FS.FS.ref_run_at(1n+p, inf, G, S)))
   == True{} : Bool}:
  FV.le_ref_of_guesses_fixed(1n+p, inf, G, S, best, ele, hbest,
    FN.FN.guesses_floor_skip(p, inf, G, S, G, best, nd, ele, hz, hbest, hfl))
