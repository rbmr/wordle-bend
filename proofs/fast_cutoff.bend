# Recursive child cutoff soundness for the bound-pruned solver.
#
# When searching a feedback class `ws` inside a live guess whose remaining
# classes plus `|S|` have lower bound `tail_lb`, the child search starts from
# `dummy_inf(cutoff)` where `cutoff = best_cost(best) - (sum + tail_lb)`.
# Because `SolveRef.better` is associative with exact tie-breaking, starting
# `Eval.guesses` from `best0` (with `cost_of(best0) <= inf`) equals
# `better_best(ref_run_at(...), best0)`:
#
# - if the true child cost is strictly below `cutoff`, the child search returns
#   the exact reference child `ref_c` and the parent guess stays alive;
# - if the true child cost is at least `cutoff`, the child search returns
#   `dummy_inf(cutoff)`, `Add` sets `skip = True{}` to prune the rest of the
#   guess, and the reference guess cost is at least `best_cost(best)` so the
#   reference accumulator is also unchanged.
import Base
import ../src/solve_fast.bend as SolveFast
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval
import ./optfold.bend as Fold
import ./classbound_nat.bend as CBN
import ./optimalvalue.bend as OV
import ./mainvalid.bend as MV
import ./fast_step.bend as FS

# Compare two `Best` values keeping the strictly cheaper one, preferring `b`
# on ties (matching `SolveRef.better`).
def FC.better_best(a: SolveRef.Best, b: SolveRef.Best) -> SolveRef.Best:
  match a:
    case SolveRef.Best{ta, ca}:
      SolveRef.better(ca, ta, b)

# Order conversion helpers by induction on `a` and `b`.
def FC.lt_of_le_false(a: Nat, b: Nat,
    +e: {Nat.is_le(a, b) == False{} : Bool}) ->
  {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n _:
      Empty.absurd({Nat.is_lt(b, 0n) == True{} : Bool},
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, Nat.is_le(0n, b), False{},
            Equal.sym(Bool, Nat.is_le(0n, b), True{},
              NatProof.Nat.is_le_zero_l(b)), e)))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      FC.lt_of_le_false(ap, bp, e)

def FC.le_false_of_lt(a: Nat, b: Nat,
    +e: {Nat.is_lt(b, a) == True{} : Bool}) ->
  {Nat.is_le(a, b) == False{} : Bool}:
  match a b:
    case 0n _:
      Empty.absurd({Nat.is_le(0n, b) == False{} : Bool},
        NatProof.Nat.not_lt_zero(b, e))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      FC.le_false_of_lt(ap, bp, e)

def FC.le_of_lt_false(a: Nat, b: Nat,
    +e: {Nat.is_lt(a, b) == False{} : Bool}) ->
  {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.is_le(1n+bp, 0n) == True{} : Bool},
        Logic.Proof.true_ne_false(e))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      FC.le_of_lt_false(ap, bp, e)

def FC.lt_false_of_le(a: Nat, b: Nat,
    +e: {Nat.is_le(b, a) == True{} : Bool}) ->
  {Nat.is_lt(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.is_lt(0n, 1n+bp) == False{} : Bool},
        Logic.Proof.false_ne_true(e))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      FC.lt_false_of_le(ap, bp, e)

def FC.lt_trans(+a: Nat, +b: Nat, +c: Nat,
    +ab: {Nat.is_lt(a, b) == True{} : Bool},
    +bc: {Nat.is_lt(b, c) == True{} : Bool}) ->
  {Nat.is_lt(a, c) == True{} : Bool}:
  NatProof.Nat.is_lt_le_trans(a, b, c, ab, NatProof.Nat.is_le_of_lt(b, c, bc))

# Associativity of `SolveRef.better` with exact tie-breaking.
def FC.better_assoc_go(+c: Nat, +t: Tree.Tree, +ta: Tree.Tree, +ca: Nat,
    +tb: Tree.Tree, +cb: Nat,
    b_ab: Bool, +e_ab: {b_ab == Nat.is_lt(ca, cb) : Bool},
    b_ca: Bool, +e_ca: {b_ca == Nat.is_lt(c, ca) : Bool}) ->
  {SolveRef.better(c, t,
     Feedback.Bool.case(SolveRef.Best, b_ab,
       SolveRef.Best{ta, ca}, SolveRef.Best{tb, cb}))
   == FC.better_best(
        Feedback.Bool.case(SolveRef.Best, b_ca,
          SolveRef.Best{t, c}, SolveRef.Best{ta, ca}),
        SolveRef.Best{tb, cb})
   : SolveRef.Best}:
  match b_ab:
    case True{}:
      match b_ca:
        case True{}:
          +lt_ca : {Nat.is_lt(c, ca) == True{} : Bool} =
            Equal.sym(Bool, True{}, Nat.is_lt(c, ca), e_ca)
          +lt_ab : {Nat.is_lt(ca, cb) == True{} : Bool} =
            Equal.sym(Bool, True{}, Nat.is_lt(ca, cb), e_ab)
          +lt_cb : {Nat.is_lt(c, cb) == True{} : Bool} =
            FC.lt_trans(c, ca, cb, lt_ca, lt_ab)
          +lhs : {SolveRef.better(c, t, SolveRef.Best{ta, ca})
                  == SolveRef.Best{t, c} : SolveRef.Best} =
            Equal.cong(Bool, SolveRef.Best,
              b => Feedback.Bool.case(SolveRef.Best, b,
                     SolveRef.Best{t, c}, SolveRef.Best{ta, ca}),
              Nat.is_lt(c, ca), True{}, lt_ca)
          +rhs : {SolveRef.better(c, t, SolveRef.Best{tb, cb})
                  == SolveRef.Best{t, c} : SolveRef.Best} =
            Equal.cong(Bool, SolveRef.Best,
              b => Feedback.Bool.case(SolveRef.Best, b,
                     SolveRef.Best{t, c}, SolveRef.Best{tb, cb}),
              Nat.is_lt(c, cb), True{}, lt_cb)
          Equal.trans(SolveRef.Best,
            SolveRef.better(c, t, SolveRef.Best{ta, ca}),
            SolveRef.Best{t, c},
            SolveRef.better(c, t, SolveRef.Best{tb, cb}),
            lhs,
            Equal.sym(SolveRef.Best,
              SolveRef.better(c, t, SolveRef.Best{tb, cb}),
              SolveRef.Best{t, c}, rhs))
        case False{}:
          +f_ca : {Nat.is_lt(c, ca) == False{} : Bool} =
            Equal.sym(Bool, False{}, Nat.is_lt(c, ca), e_ca)
          +lt_ab : {Nat.is_lt(ca, cb) == True{} : Bool} =
            Equal.sym(Bool, True{}, Nat.is_lt(ca, cb), e_ab)
          +lhs : {SolveRef.better(c, t, SolveRef.Best{ta, ca})
                  == SolveRef.Best{ta, ca} : SolveRef.Best} =
            Equal.cong(Bool, SolveRef.Best,
              b => Feedback.Bool.case(SolveRef.Best, b,
                     SolveRef.Best{t, c}, SolveRef.Best{ta, ca}),
              Nat.is_lt(c, ca), False{}, f_ca)
          +rhs : {SolveRef.better(ca, ta, SolveRef.Best{tb, cb})
                  == SolveRef.Best{ta, ca} : SolveRef.Best} =
            Equal.cong(Bool, SolveRef.Best,
              b => Feedback.Bool.case(SolveRef.Best, b,
                     SolveRef.Best{ta, ca}, SolveRef.Best{tb, cb}),
              Nat.is_lt(ca, cb), True{}, lt_ab)
          Equal.trans(SolveRef.Best,
            SolveRef.better(c, t, SolveRef.Best{ta, ca}),
            SolveRef.Best{ta, ca},
            SolveRef.better(ca, ta, SolveRef.Best{tb, cb}),
            lhs,
            Equal.sym(SolveRef.Best,
              SolveRef.better(ca, ta, SolveRef.Best{tb, cb}),
              SolveRef.Best{ta, ca}, rhs))
    case False{}:
      match b_ca:
        case True{}:
          {==}
        case False{}:
          +le_ac : {Nat.is_le(ca, c) == True{} : Bool} =
            FC.le_of_lt_false(c, ca,
              Equal.sym(Bool, False{}, Nat.is_lt(c, ca), e_ca))
          +le_ba : {Nat.is_le(cb, ca) == True{} : Bool} =
            FC.le_of_lt_false(ca, cb,
              Equal.sym(Bool, False{}, Nat.is_lt(ca, cb), e_ab))
          +le_bc : {Nat.is_le(cb, c) == True{} : Bool} =
            NatProof.Nat.is_le_trans(cb, ca, c, le_ba, le_ac)
          +f_cb : {Nat.is_lt(c, cb) == False{} : Bool} =
            FC.lt_false_of_le(c, cb, le_bc)
          +f_ab : {Nat.is_lt(ca, cb) == False{} : Bool} =
            Equal.sym(Bool, False{}, Nat.is_lt(ca, cb), e_ab)
          +lhs : {SolveRef.better(c, t, SolveRef.Best{tb, cb})
                  == SolveRef.Best{tb, cb} : SolveRef.Best} =
            Equal.cong(Bool, SolveRef.Best,
              b => Feedback.Bool.case(SolveRef.Best, b,
                     SolveRef.Best{t, c}, SolveRef.Best{tb, cb}),
              Nat.is_lt(c, cb), False{}, f_cb)
          +rhs : {SolveRef.better(ca, ta, SolveRef.Best{tb, cb})
                  == SolveRef.Best{tb, cb} : SolveRef.Best} =
            Equal.cong(Bool, SolveRef.Best,
              b => Feedback.Bool.case(SolveRef.Best, b,
                     SolveRef.Best{ta, ca}, SolveRef.Best{tb, cb}),
              Nat.is_lt(ca, cb), False{}, f_ab)
          Equal.trans(SolveRef.Best,
            SolveRef.better(c, t, SolveRef.Best{tb, cb}),
            SolveRef.Best{tb, cb},
            SolveRef.better(ca, ta, SolveRef.Best{tb, cb}),
            lhs,
            Equal.sym(SolveRef.Best,
              SolveRef.better(ca, ta, SolveRef.Best{tb, cb}),
              SolveRef.Best{tb, cb}, rhs))

def FC.better_assoc(+c: Nat, +t: Tree.Tree, a: SolveRef.Best,
    b: SolveRef.Best) ->
  {SolveRef.better(c, t, FC.better_best(a, b))
   == FC.better_best(SolveRef.better(c, t, a), b) : SolveRef.Best}:
  match a:
    case SolveRef.Best{+ta, +ca}:
      match b:
        case SolveRef.Best{+tb, +cb}:
          FC.better_assoc_go(c, t, ta, ca, tb, cb,
            Nat.is_lt(ca, cb), {==},
            Nat.is_lt(c, ca), {==})

# `dummy_inf(inf)` is a left identity for `FC.better_best` on any `b` with
# `cost_of(b) <= inf`.
def FC.better_dummy_inf(+inf: Nat, b: SolveRef.Best,
    +hb: {Nat.is_le(Eval.Eval.cost_of(b), inf) == True{} : Bool}) ->
  {FC.better_best(Eval.Eval.dummy_inf(inf), b) == b : SolveRef.Best}:
  match b:
    case SolveRef.Best{+tb, +cb}:
      +f : {Nat.is_lt(inf, cb) == False{} : Bool} =
        FC.lt_false_of_le(inf, cb, hb)
      Equal.cong(Bool, SolveRef.Best,
        x => Feedback.Bool.case(SolveRef.Best, x,
               SolveRef.Best{Tree.Node{Nil{}, Nil{}}, inf},
               SolveRef.Best{tb, cb}),
        Nat.is_lt(inf, cb), False{}, f)

# `FC.better_best` selects `a` when `cost_of(a) < cost_of(b)` and `b` otherwise.
def FC.better_best_lt(a: SolveRef.Best, b: SolveRef.Best,
    +lt: {Nat.is_lt(Eval.Eval.cost_of(a), Eval.Eval.cost_of(b))
          == True{} : Bool}) ->
  {FC.better_best(a, b) == a : SolveRef.Best}:
  match a:
    case SolveRef.Best{+ta, +ca}:
      match b:
        case SolveRef.Best{+tb, +cb}:
          Equal.cong(Bool, SolveRef.Best,
            x => Feedback.Bool.case(SolveRef.Best, x,
                   SolveRef.Best{ta, ca}, SolveRef.Best{tb, cb}),
            Nat.is_lt(ca, cb), True{}, lt)

def FC.better_best_ge(a: SolveRef.Best, b: SolveRef.Best,
    +ge: {Nat.is_lt(Eval.Eval.cost_of(a), Eval.Eval.cost_of(b))
          == False{} : Bool}) ->
  {FC.better_best(a, b) == b : SolveRef.Best}:
  match a:
    case SolveRef.Best{+ta, +ca}:
      match b:
        case SolveRef.Best{+tb, +cb}:
          Equal.cong(Bool, SolveRef.Best,
            x => Feedback.Bool.case(SolveRef.Best, x,
                   SolveRef.Best{ta, ca}, SolveRef.Best{tb, cb}),
            Nat.is_lt(ca, cb), False{}, ge)

# One positive-fuel guess step commutes with `FC.better_best(_, b0)`.
def FC.eval_guess_better_bool(+p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +groups: +List<Groups.Group>,
    +inf: Nat, usable: Bool, +acc: SolveRef.Best, +b0: SolveRef.Best) ->
  {Eval.Eval.guess_bool(p, G, S, g, groups, inf, usable,
     FC.better_best(acc, b0))
   == FC.better_best(Eval.Eval.guess_bool(p, G, S, g, groups, inf, usable, acc),
        b0)
   : SolveRef.Best}:
  match usable:
    case False{}:
      {==}
    case True{}:
      +items : Eval.KS = Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)
      +cc : Nat = Fold.OQ.ks_cost(inf, S, items)
      +ct : Tree.Tree = Fold.OQ.ks_tree(g, items)
      +e1 : {Eval.Eval.block(p, G, S, g, inf, groups, FC.better_best(acc, b0))
             == SolveRef.better(cc, ct, FC.better_best(acc, b0))
             : SolveRef.Best} =
        Fold.OQ.block_eq(inf, g, S, items, FC.better_best(acc, b0))
      +e2 : {SolveRef.better(cc, ct, FC.better_best(acc, b0))
             == FC.better_best(SolveRef.better(cc, ct, acc), b0)
             : SolveRef.Best} =
        FC.better_assoc(cc, ct, acc, b0)
      +e3 : {FC.better_best(SolveRef.better(cc, ct, acc), b0)
             == FC.better_best(Eval.Eval.block(p, G, S, g, inf, groups, acc), b0)
             : SolveRef.Best} =
        Equal.cong(SolveRef.Best, SolveRef.Best,
          r => FC.better_best(r, b0),
          SolveRef.better(cc, ct, acc),
          Eval.Eval.block(p, G, S, g, inf, groups, acc),
          Equal.sym(SolveRef.Best,
            Eval.Eval.block(p, G, S, g, inf, groups, acc),
            SolveRef.better(cc, ct, acc),
            Fold.OQ.block_eq(inf, g, S, items, acc)))
      Equal.trans(SolveRef.Best,
        Eval.Eval.block(p, G, S, g, inf, groups, FC.better_best(acc, b0)),
        FC.better_best(SolveRef.better(cc, ct, acc), b0),
        FC.better_best(Eval.Eval.block(p, G, S, g, inf, groups, acc), b0),
        Equal.trans(SolveRef.Best,
          Eval.Eval.block(p, G, S, g, inf, groups, FC.better_best(acc, b0)),
          SolveRef.better(cc, ct, FC.better_best(acc, b0)),
          FC.better_best(SolveRef.better(cc, ct, acc), b0),
          e1, e2),
        e3)

def FC.eval_guesses_better(+fuel: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +gs: +List<+List<Nat>>,
    +acc: SolveRef.Best, +b0: SolveRef.Best) ->
  {Eval.Eval.guesses(fuel, G, S, inf, gs, FC.better_best(acc, b0))
   == FC.better_best(Eval.Eval.guesses(fuel, G, S, inf, gs, acc), b0)
   : SolveRef.Best}:
  match fuel:
    case 0n:
      match gs:
        case Nil{}:
          {==}
        case Con{+g, +t}:
          +c0 : Nat = SolveRef.sat_add(inf, Groups.len_words(S), 0n)
          +t0 : Tree.Tree = Tree.Node{g, Nil{}}
          +step1 : {SolveRef.finish_guess(inf, g, Nil{}, 0n,
                      Groups.len_words(S), FC.better_best(acc, b0))
                    == FC.better_best(
                         SolveRef.finish_guess(inf, g, Nil{}, 0n,
                           Groups.len_words(S), acc),
                         b0)
                    : SolveRef.Best} =
            FC.better_assoc(c0, t0, acc, b0)
          Equal.trans(SolveRef.Best,
            Eval.Eval.guesses(0n, G, S, inf, t,
              SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(S),
                FC.better_best(acc, b0))),
            Eval.Eval.guesses(0n, G, S, inf, t,
              FC.better_best(
                SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(S),
                  acc),
                b0)),
            FC.better_best(Eval.Eval.guesses(0n, G, S, inf, g <> t, acc), b0),
            Equal.cong(SolveRef.Best, SolveRef.Best,
              a => Eval.Eval.guesses(0n, G, S, inf, t, a),
              SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(S),
                FC.better_best(acc, b0)),
              FC.better_best(
                SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(S),
                  acc),
                b0),
              step1),
            FC.eval_guesses_better(0n, G, S, inf, t,
              SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(S), acc),
              b0))
    case 1n+p:
      match gs:
        case Nil{}:
          {==}
        case Con{+g, +t}:
          +groups : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
          +step1 : {Eval.Eval.guess(p, G, S, g, inf, FC.better_best(acc, b0))
                    == FC.better_best(Eval.Eval.guess(p, G, S, g, inf, acc), b0)
                    : SolveRef.Best} =
            FC.eval_guess_better_bool(p, G, S, g, groups, inf,
              Groups.groups_smaller(S, groups), acc, b0)
          Equal.trans(SolveRef.Best,
            Eval.Eval.guesses(1n+p, G, S, inf, t,
              Eval.Eval.guess(p, G, S, g, inf, FC.better_best(acc, b0))),
            Eval.Eval.guesses(1n+p, G, S, inf, t,
              FC.better_best(Eval.Eval.guess(p, G, S, g, inf, acc), b0)),
            FC.better_best(Eval.Eval.guesses(1n+p, G, S, inf, g <> t, acc), b0),
            Equal.cong(SolveRef.Best, SolveRef.Best,
              a => Eval.Eval.guesses(1n+p, G, S, inf, t, a),
              Eval.Eval.guess(p, G, S, g, inf, FC.better_best(acc, b0)),
              FC.better_best(Eval.Eval.guess(p, G, S, g, inf, acc), b0),
              step1),
            FC.eval_guesses_better(1n+p, G, S, inf, t,
              Eval.Eval.guess(p, G, S, g, inf, acc), b0))

# Running `Eval.guesses` from `b0` (with `cost_of(b0) <= inf`) equals
# `FC.better_best(FS.ref_run_at(fuel, inf, G, S), b0)` whenever `|S| <= fuel`.
def FC.ref_run_guesses_eq(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>,
    +le: {Nat.is_le(Groups.len_words(S), fuel) == True{} : Bool}) ->
  {Eval.Eval.guesses(fuel, G, S, inf, G, Eval.Eval.dummy_inf(inf))
   == FS.FS.ref_run_at(fuel, inf, G, S) : SolveRef.Best}:
  match fuel:
    case 0n:
      +eS : {S == Nil{} : +List<+List<Nat>>} =
        MV.MV.nil_of_len_zero(S,
          NatProof.Nat.eq_zero_of_le_zero(Groups.len_words(S), le))
      %Equal.sym(+List<+List<Nat>>, S, Nil{}, eS) : {
        Eval.Eval.guesses(0n, G, _, inf, G, Eval.Eval.dummy_inf(inf))
        == FS.FS.ref_run_at(0n, inf, G, _) : SolveRef.Best}
      Equal.sym(SolveRef.Best,
        FS.FS.ref_run_at(0n, inf, G, Nil{}),
        Eval.Eval.guesses(0n, G, Nil{}, inf, G, Eval.Eval.dummy_inf(inf)),
        Eval.Eval.guesses_zero(G, inf, G, Eval.Eval.dummy_inf(inf)))
    case 1n+p:
      Equal.sym(SolveRef.Best,
        FS.FS.ref_run_at(1n+p, inf, G, S),
        Eval.Eval.guesses(1n+p, G, S, inf, G, Eval.Eval.dummy_inf(inf)),
        Eval.Eval.guesses_step(p, G, S, inf, G, Eval.Eval.dummy_inf(inf)))

def FC.eval_guesses_from(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +b0: SolveRef.Best,
    +le: {Nat.is_le(Groups.len_words(S), fuel) == True{} : Bool},
    +hb0: {Nat.is_le(Eval.Eval.cost_of(b0), inf) == True{} : Bool}) ->
  {Eval.Eval.guesses(fuel, G, S, inf, G, b0)
   == FC.better_best(FS.FS.ref_run_at(fuel, inf, G, S), b0) : SolveRef.Best}:
  +e1 : {Eval.Eval.guesses(fuel, G, S, inf, G, b0)
         == Eval.Eval.guesses(fuel, G, S, inf, G,
              FC.better_best(Eval.Eval.dummy_inf(inf), b0))
         : SolveRef.Best} =
    Equal.cong(SolveRef.Best, SolveRef.Best,
      a => Eval.Eval.guesses(fuel, G, S, inf, G, a),
      b0, FC.better_best(Eval.Eval.dummy_inf(inf), b0),
      Equal.sym(SolveRef.Best,
        FC.better_best(Eval.Eval.dummy_inf(inf), b0), b0,
        FC.better_dummy_inf(inf, b0, hb0)))
  +e2 : {Eval.Eval.guesses(fuel, G, S, inf, G,
           FC.better_best(Eval.Eval.dummy_inf(inf), b0))
         == FC.better_best(
              Eval.Eval.guesses(fuel, G, S, inf, G, Eval.Eval.dummy_inf(inf)),
              b0)
         : SolveRef.Best} =
    FC.eval_guesses_better(fuel, G, S, inf, G, Eval.Eval.dummy_inf(inf), b0)
  +e3 : {FC.better_best(
           Eval.Eval.guesses(fuel, G, S, inf, G, Eval.Eval.dummy_inf(inf)), b0)
         == FC.better_best(FS.FS.ref_run_at(fuel, inf, G, S), b0)
         : SolveRef.Best} =
    Equal.cong(SolveRef.Best, SolveRef.Best,
      r => FC.better_best(r, b0),
      Eval.Eval.guesses(fuel, G, S, inf, G, Eval.Eval.dummy_inf(inf)),
      FS.FS.ref_run_at(fuel, inf, G, S),
      FC.ref_run_guesses_eq(fuel, inf, G, S, le))
  Equal.trans(SolveRef.Best,
    Eval.Eval.guesses(fuel, G, S, inf, G, b0),
    FC.better_best(
      Eval.Eval.guesses(fuel, G, S, inf, G, Eval.Eval.dummy_inf(inf)), b0),
    FC.better_best(FS.FS.ref_run_at(fuel, inf, G, S), b0),
    Equal.trans(SolveRef.Best,
      Eval.Eval.guesses(fuel, G, S, inf, G, b0),
      Eval.Eval.guesses(fuel, G, S, inf, G,
        FC.better_best(Eval.Eval.dummy_inf(inf), b0)),
      FC.better_best(
        Eval.Eval.guesses(fuel, G, S, inf, G, Eval.Eval.dummy_inf(inf)), b0),
      e1, e2),
    e3)

# Subtraction arithmetic for the cutoff budget.
def FC.sub_le_self(+a: Nat, +b: Nat) ->
  {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n++ap:
      match b:
        case 0n:
          NatProof.Nat.is_le_refl(1n+ap)
        case 1n++bp:
          NatProof.Nat.is_le_trans(Nat.sub(ap, bp), ap, 1n+ap,
            FC.sub_le_self(ap, bp),
            NatProof.Nat.is_le_of_lt(ap, 1n+ap,
              NatProof.Nat.is_lt_succ_self(ap)))

def FC.add_sub_of_le(+a: Nat, +b: Nat,
    +le: {Nat.is_le(b, a) == True{} : Bool}) ->
  {Nat.add(b, Nat.sub(a, b)) == a : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+ap 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({Nat.add(1n+bp, Nat.sub(0n, 1n+bp)) == 0n : Nat},
        Logic.Proof.false_ne_true(le))
    case 1n++ap 1n++bp:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(bp, Nat.sub(ap, bp)), ap,
        FC.add_sub_of_le(ap, bp, le))

def FC.lt_add_l(a: Nat, +b: Nat, +c: Nat,
    +lt: {Nat.is_lt(b, c) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(a, b), Nat.add(a, c)) == True{} : Bool}:
  match a:
    case 0n:
      lt
    case 1n+ap:
      FC.lt_add_l(ap, b, c, lt)

# `a + b < B <= inf` implies `sat_add(inf, a, b) == a + b`.
def FC.sat_add_lt_eq(+inf: Nat, +a: Nat, +b: Nat, +tail: Nat, +B: Nat,
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +hlt: {Nat.is_lt(Nat.add(Nat.add(a, b), tail), B) == True{} : Bool}) ->
  {SolveRef.sat_add(inf, a, b) == Nat.add(a, b) : Nat}:
  +ab_le : {Nat.is_le(Nat.add(a, b), Nat.add(Nat.add(a, b), tail))
            == True{} : Bool} =
    CBN.CB.is_le_add_self_r(Nat.add(a, b), tail)
  +a_le : {Nat.is_le(a, Nat.add(Nat.add(a, b), tail)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(a, Nat.add(a, b), Nat.add(Nat.add(a, b), tail),
      CBN.CB.is_le_add_self_r(a, b), ab_le)
  +b_le_ab : {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(b, Nat.add(b, a), Nat.add(a, b),
      NatProof.NatPrf.add_comm(b, a), CBN.CB.is_le_add_self_r(b, a))
  +b_le : {Nat.is_le(b, Nat.add(Nat.add(a, b), tail)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(b, Nat.add(a, b), Nat.add(Nat.add(a, b), tail),
      b_le_ab, ab_le)
  +a_lt : {Nat.is_lt(a, inf) == True{} : Bool} =
    NatProof.Nat.is_lt_le_trans(a, B, inf,
      NatProof.Nat.is_le_lt_trans(a, Nat.add(Nat.add(a, b), tail), B,
        a_le, hlt),
      hB)
  +b_lt : {Nat.is_lt(b, inf) == True{} : Bool} =
    NatProof.Nat.is_lt_le_trans(b, B, inf,
      NatProof.Nat.is_le_lt_trans(b, Nat.add(Nat.add(a, b), tail), B,
        b_le, hlt),
      hB)
  OV.OV.sat_fin(inf, a, b,
    OV.OV.ge_false_of_lt(a, inf, a_lt),
    OV.OV.ge_false_of_lt(b, inf, b_lt))

# If `B <= inf` and `B <= (a + b) + tail`, then `B <= sat_add(inf, a, b) + tail`.
def FC.le_sat_add_r_go(+inf: Nat, +a: Nat, +b: Nat, +tail: Nat, +B: Nat,
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +hle: {Nat.is_le(B, Nat.add(Nat.add(a, b), tail)) == True{} : Bool},
    ga: Bool, +ea: {ga == Nat.is_ge(a, inf) : Bool},
    gb: Bool, +eb: {gb == Nat.is_ge(b, inf) : Bool}) ->
  {Nat.is_le(B,
     Nat.add(
       Feedback.Bool.case(Nat, ga, inf,
         Feedback.Bool.case(Nat, gb, inf, Nat.add(a, b))),
       tail)) == True{} : Bool}:
  match ga:
    case True{}:
      NatProof.Nat.is_le_trans(B, inf, Nat.add(inf, tail), hB,
        CBN.CB.is_le_add_self_r(inf, tail))
    case False{}:
      match gb:
        case True{}:
          NatProof.Nat.is_le_trans(B, inf, Nat.add(inf, tail), hB,
            CBN.CB.is_le_add_self_r(inf, tail))
        case False{}:
          hle

def FC.le_sat_add_r(+inf: Nat, +a: Nat, +b: Nat, +tail: Nat, +B: Nat,
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +hle: {Nat.is_le(B, Nat.add(Nat.add(a, b), tail)) == True{} : Bool}) ->
  {Nat.is_le(B, Nat.add(SolveRef.sat_add(inf, a, b), tail)) == True{} : Bool}:
  FC.le_sat_add_r_go(inf, a, b, tail, B, hB, hle,
    Nat.is_ge(a, inf), {==}, Nat.is_ge(b, inf), {==})

# Preserving the liveness invariant across a `OneItem` step.
def FC.alive_one(+inf: Nat, +sum: Nat, +tail: Nat, +B: Nat,
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +alive: {Nat.is_lt(Nat.add(sum, Nat.add(1n, tail)), B) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(SolveRef.sat_add(inf, sum, 1n), tail), B)
   == True{} : Bool}:
  +eassoc : {Nat.add(Nat.add(sum, 1n), tail) == Nat.add(sum, Nat.add(1n, tail))
             : Nat} =
    NatProof.NatPrf.add_assoc(sum, 1n, tail)
  +hlt : {Nat.is_lt(Nat.add(Nat.add(sum, 1n), tail), B) == True{} : Bool} =
    CBN.CB.lt_eq_l(B, Nat.add(sum, Nat.add(1n, tail)),
      Nat.add(Nat.add(sum, 1n), tail),
      Equal.sym(Nat, Nat.add(Nat.add(sum, 1n), tail),
        Nat.add(sum, Nat.add(1n, tail)), eassoc),
      alive)
  +esat : {SolveRef.sat_add(inf, sum, 1n) == Nat.add(sum, 1n) : Nat} =
    FC.sat_add_lt_eq(inf, sum, 1n, tail, B, hB, hlt)
  CBN.CB.lt_eq_l(B, Nat.add(Nat.add(sum, 1n), tail),
    Nat.add(SolveRef.sat_add(inf, sum, 1n), tail),
    Equal.cong(Nat, Nat, x => Nat.add(x, tail),
      Nat.add(sum, 1n), SolveRef.sat_add(inf, sum, 1n),
      Equal.sym(Nat, SolveRef.sat_add(inf, sum, 1n), Nat.add(sum, 1n), esat)),
    hlt)

# From `sum + (clb + tail) < B` extract `sum + tail <= B`.
def FC.sum_tail_le(+sum: Nat, +clb: Nat, +tail: Nat, +B: Nat,
    +alive: {Nat.is_lt(Nat.add(sum, Nat.add(clb, tail)), B)
             == True{} : Bool}) ->
  {Nat.is_le(Nat.add(sum, tail), B) == True{} : Bool}:
  +t_le : {Nat.is_le(tail, Nat.add(clb, tail)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(tail, Nat.add(tail, clb), Nat.add(clb, tail),
      NatProof.NatPrf.add_comm(tail, clb), CBN.CB.is_le_add_self_r(tail, clb))
  +st_le : {Nat.is_le(Nat.add(sum, tail), Nat.add(sum, Nat.add(clb, tail)))
            == True{} : Bool} =
    NatProof.Nat.is_le_add_l(tail, Nat.add(clb, tail), sum, t_le)
  NatProof.Nat.is_le_of_lt(Nat.add(sum, tail), B,
    NatProof.Nat.is_le_lt_trans(Nat.add(sum, tail),
      Nat.add(sum, Nat.add(clb, tail)), B, st_le, alive))

# Regroup `(sum + c) + tail == (sum + tail) + c`.
def FC.regroup_sum(+sum: Nat, +c: Nat, +tail: Nat) ->
  {Nat.add(Nat.add(sum, c), tail) == Nat.add(Nat.add(sum, tail), c) : Nat}:
  Equal.trans(Nat,
    Nat.add(Nat.add(sum, c), tail),
    Nat.add(sum, Nat.add(c, tail)),
    Nat.add(Nat.add(sum, tail), c),
    NatProof.NatPrf.add_assoc(sum, c, tail),
    Equal.trans(Nat,
      Nat.add(sum, Nat.add(c, tail)),
      Nat.add(sum, Nat.add(tail, c)),
      Nat.add(Nat.add(sum, tail), c),
      Equal.cong(Nat, Nat, x => Nat.add(sum, x),
        Nat.add(c, tail), Nat.add(tail, c),
        NatProof.NatPrf.add_comm(c, tail)),
      Equal.sym(Nat,
        Nat.add(Nat.add(sum, tail), c),
        Nat.add(sum, Nat.add(tail, c)),
        NatProof.NatPrf.add_assoc(sum, tail, c))))

# When `c < B - (sum + tail)` (with `sum + tail <= B <= inf`), the updated sum
# does not saturate and stays strictly below `B`: `sat_add(inf, sum, c) + tail < B`.
def FC.alive_cut_lt(+inf: Nat, +sum: Nat, +c: Nat, +tail: Nat, +B: Nat,
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +st_le: {Nat.is_le(Nat.add(sum, tail), B) == True{} : Bool},
    +hlt: {Nat.is_lt(c, Nat.sub(B, Nat.add(sum, tail))) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(SolveRef.sat_add(inf, sum, c), tail), B)
   == True{} : Bool}:
  +cut : Nat = Nat.sub(B, Nat.add(sum, tail))
  +lt1 : {Nat.is_lt(Nat.add(Nat.add(sum, tail), c),
            Nat.add(Nat.add(sum, tail), cut)) == True{} : Bool} =
    FC.lt_add_l(Nat.add(sum, tail), c, cut, hlt)
  +eqB : {Nat.add(Nat.add(sum, tail), cut) == B : Nat} =
    FC.add_sub_of_le(B, Nat.add(sum, tail), st_le)
  +lt2 : {Nat.is_lt(Nat.add(Nat.add(sum, tail), c), B) == True{} : Bool} =
    Equal.trans(Bool,
      Nat.is_lt(Nat.add(Nat.add(sum, tail), c), B),
      Nat.is_lt(Nat.add(Nat.add(sum, tail), c),
        Nat.add(Nat.add(sum, tail), cut)),
      True{},
      Equal.cong(Nat, Bool,
        x => Nat.is_lt(Nat.add(Nat.add(sum, tail), c), x),
        B, Nat.add(Nat.add(sum, tail), cut),
        Equal.sym(Nat, Nat.add(Nat.add(sum, tail), cut), B, eqB)),
      lt1)
  +lt3 : {Nat.is_lt(Nat.add(Nat.add(sum, c), tail), B) == True{} : Bool} =
    CBN.CB.lt_eq_l(B, Nat.add(Nat.add(sum, tail), c),
      Nat.add(Nat.add(sum, c), tail),
      Equal.sym(Nat, Nat.add(Nat.add(sum, c), tail),
        Nat.add(Nat.add(sum, tail), c), FC.regroup_sum(sum, c, tail)),
      lt2)
  +esat : {SolveRef.sat_add(inf, sum, c) == Nat.add(sum, c) : Nat} =
    FC.sat_add_lt_eq(inf, sum, c, tail, B, hB, lt3)
  CBN.CB.lt_eq_l(B, Nat.add(Nat.add(sum, c), tail),
    Nat.add(SolveRef.sat_add(inf, sum, c), tail),
    Equal.cong(Nat, Nat, x => Nat.add(x, tail),
      Nat.add(sum, c), SolveRef.sat_add(inf, sum, c),
      Equal.sym(Nat, SolveRef.sat_add(inf, sum, c), Nat.add(sum, c), esat)),
    lt3)

# When `B - (sum + tail) <= c` (with `sum + tail <= B <= inf`), the updated
# sum plus `tail` reaches at least `B`: `B <= sat_add(inf, sum, c) + tail`.
def FC.dead_cut_ge(+inf: Nat, +sum: Nat, +c: Nat, +tail: Nat, +B: Nat,
    +hB: {Nat.is_le(B, inf) == True{} : Bool},
    +st_le: {Nat.is_le(Nat.add(sum, tail), B) == True{} : Bool},
    +hge: {Nat.is_le(Nat.sub(B, Nat.add(sum, tail)), c) == True{} : Bool}) ->
  {Nat.is_le(B, Nat.add(SolveRef.sat_add(inf, sum, c), tail))
   == True{} : Bool}:
  +cut : Nat = Nat.sub(B, Nat.add(sum, tail))
  +le1 : {Nat.is_le(Nat.add(Nat.add(sum, tail), cut),
            Nat.add(Nat.add(sum, tail), c)) == True{} : Bool} =
    NatProof.Nat.is_le_add_l(cut, c, Nat.add(sum, tail), hge)
  +eqB : {Nat.add(Nat.add(sum, tail), cut) == B : Nat} =
    FC.add_sub_of_le(B, Nat.add(sum, tail), st_le)
  +le2 : {Nat.is_le(B, Nat.add(Nat.add(sum, tail), c)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_l(Nat.add(Nat.add(sum, tail), c),
      Nat.add(Nat.add(sum, tail), cut), B, eqB, le1)
  +le3 : {Nat.is_le(B, Nat.add(Nat.add(sum, c), tail)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(B, Nat.add(Nat.add(sum, tail), c),
      Nat.add(Nat.add(sum, c), tail),
      Equal.sym(Nat, Nat.add(Nat.add(sum, c), tail),
        Nat.add(Nat.add(sum, tail), c), FC.regroup_sum(sum, c, tail)),
      le2)
  FC.le_sat_add_r(inf, sum, c, tail, B, hB, le3)
