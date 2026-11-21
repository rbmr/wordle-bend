# The guess fold reaches the cost of the guess that a valid tree uses.
#
# A valid tree's root guess is one of the guesses the solver folds over. The
# fold only lowers its cost, so the fold's result is at most the candidate cost
# of that guess. This module carries that argument down the guess list.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./eval.bend as Eval
import ./sat.bend as Sat
import ./cover.bend as Cover
import ./cover_list.bend as CoverList
import ./cover_oracle.bend as Cora
import ./optsum.bend as Sums
import ./optfold.bend as Fold

# A usable guess costs at most its own candidate.
def OQ.guess_le_cand_go(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +best: SolveRef.Best, b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    +us: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{}
          : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guess_bool(p, G, S, g,
      Groups.groups_build(g, S, Nil{}), inf, b, best)),
      Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
        Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf))) == True{} : Bool}:
  match b:
    case True{}:
      +ceq : {Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf,
                Groups.groups_build(g, S, Nil{}), best))
              == Eval.Eval.cost_of(SolveRef.better(
                   Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                     Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
                   Fold.OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
                     Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
                   best)) : Nat} =
        Equal.trans(Nat,
          Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf,
            Groups.groups_build(g, S, Nil{}), best)),
          Eval.Eval.cost_of(Eval.Eval.finish_ks(inf, g, S,
            Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}),
              Nil{}, 0n, inf), best)),
          Eval.Eval.cost_of(SolveRef.better(
            Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
              Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
            Fold.OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
              Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), best)),
          Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
            Eval.Eval.block(p, G, S, g, inf,
              Groups.groups_build(g, S, Nil{}), best),
            Eval.Eval.finish_ks(inf, g, S,
              Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}),
                Nil{}, 0n, inf), best),
            Fold.OQ.block_unfold(p, G, S, g, Groups.groups_build(g, S, Nil{}),
              inf, best)),
          Fold.OQ.block_cost_eq(inf, g, S,
            Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}),
              Nil{}, 0n, inf), best))
      +le : {Nat.is_le(Eval.Eval.cost_of(SolveRef.better(
                 Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                   Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
                 Fold.OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
                   Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
                 best)),
               Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                 Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)))
             == True{} : Bool} =
        Fold.OQ.better_le_cand(
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
          Fold.OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), best)
      +cl : {Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf,
                Groups.groups_build(g, S, Nil{}), best))
              == Eval.Eval.cost_of(Eval.Eval.guess_bool(p, G, S, g,
                   Groups.groups_build(g, S, Nil{}), inf, b, best)) : Nat} =
        Equal.cong(SolveRef.Best, Nat, Eval.Eval.cost_of,
          Eval.Eval.block(p, G, S, g, inf, Groups.groups_build(g, S, Nil{}),
            best),
          Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}),
            inf, b, best),
          Equal.sym(SolveRef.Best,
            Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}),
              inf, b, best),
            Eval.Eval.block(p, G, S, g, inf, Groups.groups_build(g, S, Nil{}),
              best), {==}))
      +mid : {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf,
                 Groups.groups_build(g, S, Nil{}), best)),
                 Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                   Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)))
               == True{} : Bool} =
        Fold.OQ.le_cong_l(
          Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf,
            Groups.groups_build(g, S, Nil{}), best)),
          Eval.Eval.cost_of(SolveRef.better(
            Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
              Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
            Fold.OQ.ks_tree(g, Eval.Eval.items(p, G, S, g,
              Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), best)),
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), ceq, le)
      Fold.OQ.le_cong_l(
        Eval.Eval.cost_of(Eval.Eval.guess_bool(p, G, S, g,
          Groups.groups_build(g, S, Nil{}), inf, b, best)),
        Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf,
          Groups.groups_build(g, S, Nil{}), best)),
        Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
          Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
        Equal.sym(Nat,
          Eval.Eval.cost_of(Eval.Eval.block(p, G, S, g, inf,
            Groups.groups_build(g, S, Nil{}), best)),
          Eval.Eval.cost_of(Eval.Eval.guess_bool(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), inf, b, best)), cl),
        mid)
    case False{}:
      +ne : {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
             == False{} : Bool} =
        Equal.sym(Bool, False{},
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), eb)
      +contra : {True{} == False{} : Bool} =
        Equal.trans(Bool, True{},
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), False{},
          Equal.sym(Bool,
            Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
            True{}, us), ne)
      Empty.absurd(
        {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guess_bool(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), inf, b, best)),
            Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
              Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf))) == True{}
         : Bool},
        Logic.Proof.true_ne_false(contra))

def OQ.guess_le_cand(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +best: SolveRef.Best,
    +us: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{}
         : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, g, inf, best)),
      Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
        Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf))) == True{} : Bool}:
  OQ.guess_le_cand_go(p, G, S, g, inf, best,
    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==}, us)

# The head branch of the membership argument. The tail's recursive call is a
# continuation, so the def is not self-referential.
def OQ.mem_head(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +h: +List<Nat>, +t: +List<+List<Nat>>, +g: +List<Nat>, +inf: Nat,
    +best: SolveRef.Best,
    +mem: {Tree.member_word(g, h <> t) == True{} : Bool},
    +us: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{}
         : Bool},
    b: Bool, +eb: {b == Feedback.word_eq(g, h) : Bool},
    k: {Tree.member_word(g, t) == True{} : Bool}
       -> {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, t,
             Eval.Eval.guess(p, G, S, h, inf, best))),
             Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
               Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)))
           == True{} : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, h <> t, best)),
      Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
        Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf))) == True{} : Bool}:
  match b:
    case True{}:
      +egh : {g == h : +List<Nat>} =
        CoverList.Cover.word_eq_true(g, h,
          Equal.sym(Bool, True{}, Feedback.word_eq(g, h), eb))
      +egrp : {Groups.groups_build(g, S, Nil{})
               == Groups.groups_build(h, S, Nil{}) : +List<Groups.Group>} =
        Equal.cong(+List<Nat>, +List<Groups.Group>,
          x => Groups.groups_build(x, S, Nil{}), g, h, egh)
      +ush : {Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{}))
              == True{} : Bool} =
        Equal.trans(Bool,
          Groups.groups_smaller(S, Groups.groups_build(h, S, Nil{})),
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), True{},
          Equal.cong(+List<Groups.Group>, Bool,
            z => Groups.groups_smaller(S, z),
            Groups.groups_build(h, S, Nil{}), Groups.groups_build(g, S, Nil{}),
            Equal.sym(+List<Groups.Group>, Groups.groups_build(g, S, Nil{}),
              Groups.groups_build(h, S, Nil{}), egrp)),
          us)
      +le_g : {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, h, inf, best)),
                 Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, h,
                   Groups.groups_build(h, S, Nil{}), Nil{}, 0n, inf)))
               == True{} : Bool} =
        OQ.guess_le_cand(p, G, S, h, inf, best, ush)
      +ceq1 : {Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, h,
                  Groups.groups_build(h, S, Nil{}), Nil{}, 0n, inf))
                == Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, h,
                  Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)) : Nat} =
        Equal.cong(+List<Groups.Group>, Nat,
          z => Fold.OQ.ks_cost(inf, S,
            Eval.Eval.items(p, G, S, h, z, Nil{}, 0n, inf)),
          Groups.groups_build(h, S, Nil{}), Groups.groups_build(g, S, Nil{}),
          Equal.sym(+List<Groups.Group>, Groups.groups_build(g, S, Nil{}),
            Groups.groups_build(h, S, Nil{}), egrp))
      +ceq2 : {Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, h,
                  Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf))
                == Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                  Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)) : Nat} =
        Equal.cong(+List<Nat>, Nat,
          x => Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, x,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), h, g,
          Equal.sym(+List<Nat>, g, h, egh))
      +ceq : {Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, h,
                 Groups.groups_build(h, S, Nil{}), Nil{}, 0n, inf))
              == Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                   Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)) : Nat} =
        Equal.trans(Nat,
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, h,
            Groups.groups_build(h, S, Nil{}), Nil{}, 0n, inf)),
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, h,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), ceq1, ceq2)
      +le_g2 : {Nat.is_le(
                  Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, h, inf, best)),
                  Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
                    Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)))
                == True{} : Bool} =
        Fold.OQ.le_cong_r(
          Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, h, inf, best)),
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, h,
            Groups.groups_build(h, S, Nil{}), Nil{}, 0n, inf)),
          Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
            Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)), ceq, le_g)
      NatProof.Nat.is_le_trans(
        Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, h <> t, best)),
        Eval.Eval.cost_of(Eval.Eval.guess(p, G, S, h, inf, best)),
        Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
          Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf)),
        Fold.OQ.guesses_cost_le_acc(p, G, S, inf, t,
          Eval.Eval.guess(p, G, S, h, inf, best)),
        le_g2)
    case False{}:
      +mt : {Tree.member_word(g, t) == True{} : Bool} =
        Cora.Cover.member_tail(g, h, t, b, eb, {==}, mem)
      k(mt)

# The guess fold is at most the candidate cost of any usable guess it contains.
def OQ.guesses_le_cand(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +gs: +List<+List<Nat>>, +g: +List<Nat>, +best: SolveRef.Best,
    +mem: {Tree.member_word(g, gs) == True{} : Bool},
    +us: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{}
         : Bool}) ->
  {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, gs, best)),
      Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
        Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf))) == True{} : Bool}:
  match gs:
    case Nil{}:
      Empty.absurd(
        {Nat.is_le(Eval.Eval.cost_of(Eval.Eval.guesses(1n+p, G, S, inf, Nil{}, best)),
            Fold.OQ.ks_cost(inf, S, Eval.Eval.items(p, G, S, g,
              Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf))) == True{}
         : Bool},
        Logic.Proof.false_ne_true(mem))
    case Con{h, t}:
      OQ.mem_head(p, G, S, h, t, g, inf, best, mem, us,
        Feedback.word_eq(g, h), {==},
        mt => OQ.guesses_le_cand(p, G, S, inf, t, g,
          Eval.Eval.guess(p, G, S, h, inf, best), mt, us))
