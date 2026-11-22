# Duplicate-free invariants, `2*n - 1` node floor exit, and O(1)-prepend
# `FGroup` equivalence for the bound-pruned solver.
#
# When `no_dup_fast(C)` is true at the root, every feedback class is a
# subsequence of its parent (`cover_groups.bend`) and stays duplicate-free:
# - every non-empty class has `max_mult(ws) = 1`, so `class_lb(ws) = 2*|ws| - 1`
#   in O(1) using the cached length in `FGroup`;
# - `pre_lb(|S|, g, S)` equals `2*|S|` when `g` is not in `S` and `2*|S| - 1`
#   when `g` is in `S`, so reaching `best_cost(best) <= 2*|S| - 1` leaves
#   `Eval.guesses` unchanged on all remaining guesses;
# - `fgroups_build_fast` accumulates reversed classes with cached lengths whose
#   reversals equal `Groups.groups_build`, and `fgroups_smaller`, `fgroups_lb`,
#   and `fgroup_items_build` match the reference predicates and bounds.
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
import ./mainvalid.bend as MV
import ./classbound_nat.bend as CBN
import ./lb_twice.bend as LBProof2
import ./cover_list.bend as CoverList
import ./cover_groups.bend as CoverGroups
import ./fast_groups.bend as FG
import ./fast_lb.bend as FLB
import ./fast_one.bend as FO

# Reference duplicate-free predicate on a candidate list.
def FN.no_dup_ref(+S: +List<+List<Nat>>) -> Bool:
  match S:
    case Nil{}:
      True{}
    case Con{w, t}:
      Bool.and(Bool.not(Tree.member_word(w, t)), FN.no_dup_ref(t))

def FN.nodup_ok(+nodup: Bool, +S: +List<+List<Nat>>) -> Bool:
  match nodup:
    case True{}:
      FN.no_dup_ref(S)
    case False{}:
      True{}

# `no_dup_go` agrees with `FN.no_dup_ref`.
def FN.no_dup_go_eq(+S: +List<+List<Nat>>, dup: Bool,
    +ed: {dup == SolveFast.next_dup(S) : Bool}) ->
  {SolveFast.no_dup_go(S, dup) == FN.no_dup_ref(S) : Bool}:
  match S:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      match dup:
        case True{}:
          +ew : {True{} == Tree.member_word(w, t) : Bool} =
            Equal.trans(Bool, True{},
              SolveFast.member_word_fast(w, t), Tree.member_word(w, t),
              ed, FO.FO.member_word_fast_eq(w, t))
          Equal.cong(Bool, Bool,
            b => Bool.and(Bool.not(b), FN.no_dup_ref(t)),
            True{}, Tree.member_word(w, t), ew)
        case False{}:
          +ew : {False{} == Tree.member_word(w, t) : Bool} =
            Equal.trans(Bool, False{},
              SolveFast.member_word_fast(w, t), Tree.member_word(w, t),
              ed, FO.FO.member_word_fast_eq(w, t))
          +e1 : {SolveFast.no_dup_go(t, SolveFast.next_dup(t))
                 == FN.no_dup_ref(t) : Bool} =
            FN.no_dup_go_eq(t, SolveFast.next_dup(t), {==})
          +e2 : {FN.no_dup_ref(t)
                 == Bool.and(Bool.not(Tree.member_word(w, t)),
                      FN.no_dup_ref(t)) : Bool} =
            Equal.cong(Bool, Bool,
              b => Bool.and(Bool.not(b), FN.no_dup_ref(t)),
              False{}, Tree.member_word(w, t), ew)
          Equal.trans(Bool,
            SolveFast.no_dup_go(t, SolveFast.next_dup(t)),
            FN.no_dup_ref(t),
            FN.no_dup_ref(w <> t),
            e1, e2)

def FN.no_dup_fast_eq(+S: +List<+List<Nat>>) ->
  {SolveFast.no_dup_fast(S) == FN.no_dup_ref(S) : Bool}:
  FN.no_dup_go_eq(S, SolveFast.next_dup(S), {==})

# `Bool.not(b) == True{}` implies `b == False{}` and vice versa.
def FN.false_of_not_true(b: Bool, +e: {Bool.not(b) == True{} : Bool}) ->
  {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Logic.Proof.false_ne_true(e))

def FN.not_true_of_false(b: Bool, +e: {b == False{} : Bool}) ->
  {Bool.not(b) == True{} : Bool}:
  Equal.cong(Bool, Bool, Bool.not, b, False{}, e)

# Subsequence monotonicity of `Tree.member_word` (contrapositive: non-membership
# passes down to subsequences).
def FN.member_cons_r_go(+w: +List<Nat>, +y: +List<Nat>, +r: +List<+List<Nat>>,
    +mr: {Tree.member_word(w, r) == True{} : Bool}, b: Bool) ->
  {Feedback.Bool.case(Bool, b, True{}, Tree.member_word(w, r))
   == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      mr

def FN.member_cons_r(+w: +List<Nat>, +y: +List<Nat>, +r: +List<+List<Nat>>,
    +mr: {Tree.member_word(w, r) == True{} : Bool}) ->
  {Tree.member_word(w, y <> r) == True{} : Bool}:
  FN.member_cons_r_go(w, y, r, mr, Feedback.word_eq(w, y))

def FN.member_of_subseq_step(+w: +List<Nat>, +h: +List<Nat>,
    +t: +List<+List<Nat>>, +y: +List<Nat>, +r: +List<+List<Nat>>,
    +ehy: {h == y : +List<Nat>},
    b: Bool, +eb: {b == Feedback.word_eq(w, h) : Bool},
    +mw: {Tree.member_word(w, h <> t) == True{} : Bool},
    rec: {Tree.member_word(w, t) == True{} : Bool} ->
         {Tree.member_word(w, r) == True{} : Bool}) ->
  {Tree.member_word(w, y <> r) == True{} : Bool}:
  match b:
    case True{}:
      +ewy : {Feedback.word_eq(w, y) == True{} : Bool} =
        Equal.trans(Bool, Feedback.word_eq(w, y), Feedback.word_eq(w, h), True{},
          Equal.cong(+List<Nat>, Bool, x => Feedback.word_eq(w, x), y, h,
            Equal.sym(+List<Nat>, h, y, ehy)),
          Equal.sym(Bool, True{}, Feedback.word_eq(w, h), eb))
      Equal.cong(Bool, Bool,
        x => Feedback.Bool.case(Bool, x, True{}, Tree.member_word(w, r)),
        Feedback.word_eq(w, y), True{}, ewy)
    case False{}:
      +mt : {Tree.member_word(w, t) == True{} : Bool} =
        Equal.trans(Bool, Tree.member_word(w, t), Tree.member_word(w, h <> t),
          True{},
          Equal.cong(Bool, Bool,
            x => Feedback.Bool.case(Bool, x, True{}, Tree.member_word(w, t)),
            False{}, Feedback.word_eq(w, h), eb),
          mw)
      FN.member_cons_r(w, y, r, rec(mt))

def FN.member_of_subseq(+w: +List<Nat>, +ws: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, sub: CoverList.Cover.Subseq(ws, S),
    +mw: {Tree.member_word(w, ws) == True{} : Bool}) ->
  {Tree.member_word(w, S) == True{} : Bool}:
  match ws S:
    case Nil{} _:
      Empty.absurd({Tree.member_word(w, S) == True{} : Bool},
        Logic.Proof.false_ne_true(mw))
    case Con{h, t} Nil{}:
      match sub:
    case Con{+h, +t} Con{+y, +r}:
      match sub:
        case Inl{q}:
          (+e, sub_t) = q
          FN.member_of_subseq_step(w, h, t, y, r, e,
            Feedback.word_eq(w, h), {==}, mw,
            mt => FN.member_of_subseq(w, t, r, sub_t, mt))
        case Inr{sub_r}:
          FN.member_cons_r(w, y, r,
            FN.member_of_subseq(w, h <> t, r, sub_r, mw))

def FN.not_member_of_subseq_go(+w: +List<Nat>, +ws: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, sub: CoverList.Cover.Subseq(ws, S),
    +nm: {Tree.member_word(w, S) == False{} : Bool},
    b: Bool, +eb: {b == Tree.member_word(w, ws) : Bool}) ->
  {Tree.member_word(w, ws) == False{} : Bool}:
  match b:
    case False{}:
      Equal.sym(Bool, False{}, Tree.member_word(w, ws), eb)
    case True{}:
      +mw : {Tree.member_word(w, ws) == True{} : Bool} =
        Equal.sym(Bool, True{}, Tree.member_word(w, ws), eb)
      +ms : {Tree.member_word(w, S) == True{} : Bool} =
        FN.member_of_subseq(w, ws, S, sub, mw)
      Empty.absurd({Tree.member_word(w, ws) == False{} : Bool},
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, Tree.member_word(w, S), False{},
            Equal.sym(Bool, Tree.member_word(w, S), True{}, ms), nm)))

def FN.not_member_of_subseq(+w: +List<Nat>, +ws: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, sub: CoverList.Cover.Subseq(ws, S),
    +nm: {Tree.member_word(w, S) == False{} : Bool}) ->
  {Tree.member_word(w, ws) == False{} : Bool}:
  FN.not_member_of_subseq_go(w, ws, S, sub, nm, Tree.member_word(w, ws), {==})

# Copy a `Cover.Subseq` witness (each `Inl` holds a list equality, which is
# `Data`).
def FN.subseq_copy(+ws: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    sub: CoverList.Cover.Subseq(ws, S)) ->
  CoverList.Cover.Subseq(ws, S) & CoverList.Cover.Subseq(ws, S):
  match ws S:
    case Nil{} _:
      Tuple{Unit{}, Unit{}}
    case Con{h, t} Nil{}:
      match sub:
    case Con{+h, +t} Con{+y, +r}:
      match sub:
        case Inl{q}:
          (+e, sub_t) = q
          MV.MV.use_pair(
            CoverList.Cover.Subseq(h <> t, y <> r)
            & CoverList.Cover.Subseq(h <> t, y <> r),
            CoverList.Cover.Subseq(t, r), CoverList.Cover.Subseq(t, r),
            FN.subseq_copy(t, r, sub_t),
            s1 => s2 => Tuple{Inl{Tuple{e, s1}}, Inl{Tuple{e, s2}}})
        case Inr{sub_r}:
          MV.MV.use_pair(
            CoverList.Cover.Subseq(h <> t, y <> r)
            & CoverList.Cover.Subseq(h <> t, y <> r),
            CoverList.Cover.Subseq(h <> t, r), CoverList.Cover.Subseq(h <> t, r),
            FN.subseq_copy(h <> t, r, sub_r),
            s1 => s2 => Tuple{Inr{s1}, Inr{s2}})

# Subsequences of a duplicate-free list stay duplicate-free.
def FN.no_dup_of_subseq(+ws: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    sub: CoverList.Cover.Subseq(ws, S),
    +nd: {FN.no_dup_ref(S) == True{} : Bool}) ->
  {FN.no_dup_ref(ws) == True{} : Bool}:
  match ws S:
    case Nil{} _:
      {==}
    case Con{h, t} Nil{}:
      match sub:
    case Con{+h, +t} Con{+y, +r}:
      match sub:
        case Inl{q}:
          (+e, sub_t) = q
          +nmy : {Tree.member_word(y, r) == False{} : Bool} =
            FN.false_of_not_true(Tree.member_word(y, r),
              Logic.Proof.and_true_l(Bool.not(Tree.member_word(y, r)),
                FN.no_dup_ref(r), nd))
          +ndr : {FN.no_dup_ref(r) == True{} : Bool} =
            Logic.Proof.and_true_r(Bool.not(Tree.member_word(y, r)),
              FN.no_dup_ref(r), nd)
          +nmh_r : {Tree.member_word(h, r) == False{} : Bool} =
            Equal.trans(Bool, Tree.member_word(h, r), Tree.member_word(y, r),
              False{},
              Equal.cong(+List<Nat>, Bool, x => Tree.member_word(x, r), h, y, e),
              nmy)
          MV.MV.use_pair(
            {FN.no_dup_ref(h <> t) == True{} : Bool},
            CoverList.Cover.Subseq(t, r), CoverList.Cover.Subseq(t, r),
            FN.subseq_copy(t, r, sub_t),
            s1 => s2 =>
              FO.FO.bool_and_intro(Bool.not(Tree.member_word(h, t)),
                FN.no_dup_ref(t),
                FN.not_true_of_false(Tree.member_word(h, t),
                  FN.not_member_of_subseq(h, t, r, s1, nmh_r)),
                FN.no_dup_of_subseq(t, r, s2, ndr)))
        case Inr{sub_r}:
          +ndr : {FN.no_dup_ref(r) == True{} : Bool} =
            Logic.Proof.and_true_r(Bool.not(Tree.member_word(y, r)),
              FN.no_dup_ref(r), nd)
          FN.no_dup_of_subseq(h <> t, r, sub_r, ndr)

def FN.nodup_ok_of_subseq(+nodup: Bool, +ws: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, sub: CoverList.Cover.Subseq(ws, S),
    +nd: {FN.nodup_ok(nodup, S) == True{} : Bool}) ->
  {FN.nodup_ok(nodup, ws) == True{} : Bool}:
  match nodup:
    case True{}:
      FN.no_dup_of_subseq(ws, S, sub, nd)
    case False{}:
      {==}

# Job-level preservation of `FN.nodup_ok` through `MV.next_jobs`.
def FN.nodup_ok_jobs(+nodup: Bool, +jobs: +List<+List<+List<Nat>>>) -> Bool:
  match jobs:
    case Nil{}:
      True{}
    case Con{S, t}:
      Bool.and(FN.nodup_ok(nodup, S), FN.nodup_ok_jobs(nodup, t))

def FN.nodup_ok_jobs_append(+nodup: Bool, +xs: +List<+List<+List<Nat>>>,
    +ys: +List<+List<+List<Nat>>>,
    +ax: {FN.nodup_ok_jobs(nodup, xs) == True{} : Bool},
    +ay: {FN.nodup_ok_jobs(nodup, ys) == True{} : Bool}) ->
  {FN.nodup_ok_jobs(nodup, List.append(&2, +List<+List<Nat>>, xs, ys))
   == True{} : Bool}:
  match xs:
    case Nil{}:
      ay
    case Con{+S, +t}:
      +ah : {FN.nodup_ok(nodup, S) == True{} : Bool} =
        Logic.Proof.and_true_l(FN.nodup_ok(nodup, S),
          FN.nodup_ok_jobs(nodup, t), ax)
      +at : {FN.nodup_ok_jobs(nodup, t) == True{} : Bool} =
        Logic.Proof.and_true_r(FN.nodup_ok(nodup, S),
          FN.nodup_ok_jobs(nodup, t), ax)
      FO.FO.bool_and_intro(FN.nodup_ok(nodup, S),
        FN.nodup_ok_jobs(nodup, List.append(&2, +List<+List<Nat>>, t, ys)),
        ah, FN.nodup_ok_jobs_append(nodup, t, ys, at, ay))

def FN.nodup_ok_next_groups(+nodup: Bool, +groups: +List<Groups.Group>,
    +S: +List<+List<Nat>>,
    allsub: CoverGroups.Cover.AllSubseq(groups, S),
    +nd: {FN.nodup_ok(nodup, S) == True{} : Bool}) ->
  {FN.nodup_ok_jobs(nodup, MV.MV.next_groups(groups)) == True{} : Bool}:
  match groups:
    case Nil{}:
      {==}
    case Con{+gp, +rest}:
      match gp:
        case Groups.Group{+fb, +ws}:
          (sub, subt) = allsub
          FO.FO.bool_and_intro(FN.nodup_ok(nodup, ws),
            FN.nodup_ok_jobs(nodup, MV.MV.next_groups(rest)),
            FN.nodup_ok_of_subseq(nodup, ws, S, sub, nd),
            FN.nodup_ok_next_groups(nodup, rest, S, subt, nd))

def FN.nodup_ok_classes_b(+nodup: Bool, b: Bool, +groups: +List<Groups.Group>,
    +S: +List<+List<Nat>>,
    allsub: CoverGroups.Cover.AllSubseq(groups, S),
    +nd: {FN.nodup_ok(nodup, S) == True{} : Bool}) ->
  {FN.nodup_ok_jobs(nodup, MV.MV.classes_b(b, groups)) == True{} : Bool}:
  match b:
    case True{}:
      FN.nodup_ok_next_groups(nodup, groups, S, allsub, nd)
    case False{}:
      {==}

def FN.nodup_ok_next_guess(+nodup: Bool, +gs: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +nd: {FN.nodup_ok(nodup, S) == True{} : Bool}) ->
  {FN.nodup_ok_jobs(nodup, MV.MV.next_guess(gs, S)) == True{} : Bool}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      +groups : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
      FN.nodup_ok_jobs_append(nodup, MV.MV.classes(g, S),
        MV.MV.next_guess(t, S),
        FN.nodup_ok_classes_b(nodup, Groups.groups_smaller(S, groups),
          groups, S, CoverGroups.Cover.all_subseq_nil(g, S), nd),
        FN.nodup_ok_next_guess(nodup, t, S, nd))

def FN.nodup_ok_next_jobs(+nodup: Bool, +G: +List<+List<Nat>>,
    +jobs: +List<+List<+List<Nat>>>,
    +aj: {FN.nodup_ok_jobs(nodup, jobs) == True{} : Bool}) ->
  {FN.nodup_ok_jobs(nodup, MV.MV.next_jobs(G, jobs)) == True{} : Bool}:
  match jobs:
    case Nil{}:
      {==}
    case Con{+S, +t}:
      +nd : {FN.nodup_ok(nodup, S) == True{} : Bool} =
        Logic.Proof.and_true_l(FN.nodup_ok(nodup, S),
          FN.nodup_ok_jobs(nodup, t), aj)
      +at : {FN.nodup_ok_jobs(nodup, t) == True{} : Bool} =
        Logic.Proof.and_true_r(FN.nodup_ok(nodup, S),
          FN.nodup_ok_jobs(nodup, t), aj)
      FN.nodup_ok_jobs_append(nodup, MV.MV.next_guess(G, S),
        MV.MV.next_jobs(G, t),
        FN.nodup_ok_next_guess(nodup, G, S, nd),
        FN.nodup_ok_next_jobs(nodup, G, t, at))

# Multiplicity, `class_lb`, and `pre_lb` consequences of `FN.no_dup_ref`.
def FN.mult_zero_step(+g: +List<Nat>, +h: +List<Nat>, +t: +List<+List<Nat>>,
    b: Bool, +eb: {b == Feedback.word_eq(g, h) : Bool},
    +nm: {Tree.member_word(g, h <> t) == False{} : Bool},
    rec: {Tree.member_word(g, t) == False{} : Bool} ->
         {LBProof2.LB.mult(g, t) == 0n : Nat}) ->
  {LBProof2.LB.mult(g, h <> t) == 0n : Nat}:
  match b:
    case True{}:
      +et : {Tree.member_word(g, h <> t) == True{} : Bool} =
        Equal.cong(Bool, Bool,
          x => Feedback.Bool.case(Bool, x, True{}, Tree.member_word(g, t)),
          Feedback.word_eq(g, h), True{},
          Equal.sym(Bool, True{}, Feedback.word_eq(g, h), eb))
      Empty.absurd({LBProof2.LB.mult(g, h <> t) == 0n : Nat},
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, Tree.member_word(g, h <> t), False{},
            Equal.sym(Bool, Tree.member_word(g, h <> t), True{}, et), nm)))
    case False{}:
      +nmt : {Tree.member_word(g, t) == False{} : Bool} =
        Equal.trans(Bool, Tree.member_word(g, t), Tree.member_word(g, h <> t),
          False{},
          Equal.cong(Bool, Bool,
            x => Feedback.Bool.case(Bool, x, True{}, Tree.member_word(g, t)),
            False{}, Feedback.word_eq(g, h), eb),
          nm)
      +eh0 : {LBProof2.LB.hit(g, h) == 0n : Nat} =
        Equal.cong(Bool, Nat, LBProof2.LB.hit_bool,
          Feedback.word_eq(g, h), False{},
          Equal.sym(Bool, False{}, Feedback.word_eq(g, h), eb))
      Equal.trans(Nat,
        Nat.add(LBProof2.LB.hit(g, h), LBProof2.LB.mult(g, t)),
        LBProof2.LB.mult(g, t),
        0n,
        Equal.cong(Nat, Nat, x => Nat.add(x, LBProof2.LB.mult(g, t)),
          LBProof2.LB.hit(g, h), 0n, eh0),
        rec(nmt))

def FN.mult_zero_of_not_member(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +nm: {Tree.member_word(g, S) == False{} : Bool}) ->
  {LBProof2.LB.mult(g, S) == 0n : Nat}:
  match S:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      FN.mult_zero_step(g, h, t, Feedback.word_eq(g, h), {==}, nm,
        nmt => FN.mult_zero_of_not_member(g, t, nmt))

def FN.head_mult_one_of_no_dup(+w: +List<Nat>, +t: +List<+List<Nat>>,
    +nd: {FN.no_dup_ref(w <> t) == True{} : Bool}) ->
  {LBProof2.LB.mult(w, w <> t) == 1n : Nat}:
  +nmw : {Tree.member_word(w, t) == False{} : Bool} =
    FN.false_of_not_true(Tree.member_word(w, t),
      Logic.Proof.and_true_l(Bool.not(Tree.member_word(w, t)),
        FN.no_dup_ref(t), nd))
  +hith : {LBProof2.LB.hit(w, w) == 1n : Nat} =
    Equal.cong(Bool, Nat, LBProof2.LB.hit_bool,
      Feedback.word_eq(w, w), True{}, FbProof.FbPrf.word_eq_refl(w))
  +mt0 : {LBProof2.LB.mult(w, t) == 0n : Nat} =
    FN.mult_zero_of_not_member(w, t, nmw)
  Equal.trans(Nat,
    Nat.add(LBProof2.LB.hit(w, w), LBProof2.LB.mult(w, t)),
    Nat.add(1n, LBProof2.LB.mult(w, t)),
    1n,
    Equal.cong(Nat, Nat, x => Nat.add(x, LBProof2.LB.mult(w, t)),
      LBProof2.LB.hit(w, w), 1n, hith),
    Equal.cong(Nat, Nat, x => Nat.add(1n, x),
      LBProof2.LB.mult(w, t), 0n, mt0))

def FN.max_mult_one_of_no_dup(+t: +List<+List<Nat>>, +w: +List<Nat>,
    +nd: {FN.no_dup_ref(w <> t) == True{} : Bool}) ->
  {LBProof2.LB.maxMult(w <> t) == 1n : Nat}:
  match t:
    case Nil{}:
      Equal.cong(Nat, Nat, x => Nat.max(x, 0n),
        LBProof2.LB.mult(w, w <> Nil{}), 1n,
        FN.head_mult_one_of_no_dup(w, Nil{}, nd))
    case Con{+w2, +t2}:
      +ndt : {FN.no_dup_ref(w2 <> t2) == True{} : Bool} =
        Logic.Proof.and_true_r(Bool.not(Tree.member_word(w, w2 <> t2)),
          FN.no_dup_ref(w2 <> t2), nd)
      +m1 : {LBProof2.LB.mult(w, w <> (w2 <> t2)) == 1n : Nat} =
        FN.head_mult_one_of_no_dup(w, w2 <> t2, nd)
      +ih : {LBProof2.LB.maxMult(w2 <> t2) == 1n : Nat} =
        FN.max_mult_one_of_no_dup(t2, w2, ndt)
      FLB.FS.max_cong(LBProof2.LB.mult(w, w <> (w2 <> t2)), 1n,
        LBProof2.LB.maxMult(w2 <> t2), 1n, m1, ih)

# For any duplicate-free list `ws`, `2 * |ws| - 1 == class_lb(ws)`.
def FN.class_lb_nodup_eq(+ws: +List<+List<Nat>>,
    +nd: {FN.no_dup_ref(ws) == True{} : Bool}) ->
  {Nat.sub(Nat.add(Groups.len_words(ws), Groups.len_words(ws)), 1n)
   == SolveFast.class_lb(ws) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      +m : Nat = Groups.len_words(w <> t)
      +mm : {SolveFast.max_mult(w <> t) == 1n : Nat} =
        Equal.trans(Nat,
          SolveFast.max_mult(w <> t), LBProof2.LB.maxMult(w <> t), 1n,
          FLB.FS.max_mult_eq(w <> t),
          FN.max_mult_one_of_no_dup(t, w, nd))
      Equal.cong(Nat, Nat, x => Nat.sub(Nat.add(m, m), x),
        1n, SolveFast.max_mult(w <> t),
        Equal.sym(Nat, SolveFast.max_mult(w <> t), 1n, mm))

def FN.class_lb_fast_eq(+nodup: Bool, +len: Nat, +ws: +List<+List<Nat>>,
    +elen: {len == Groups.len_words(ws) : Nat},
    +nd: {FN.nodup_ok(nodup, ws) == True{} : Bool}) ->
  {SolveFast.class_lb_fast(nodup, len, ws) == SolveFast.class_lb(ws) : Nat}:
  match nodup:
    case False{}:
      {==}
    case True{}:
      Equal.trans(Nat,
        Nat.sub(Nat.add(len, len), 1n),
        Nat.sub(Nat.add(Groups.len_words(ws), Groups.len_words(ws)), 1n),
        SolveFast.class_lb(ws),
        Equal.cong(Nat, Nat, x => Nat.sub(Nat.add(x, x), 1n),
          len, Groups.len_words(ws), elen),
        FN.class_lb_nodup_eq(ws, nd))

# `keep_fast(g, S)` on a duplicate-free list `S`: equals `|S|` when `g` is
# absent, and `1 + keep_fast(g, S) == |S|` when `g` is present.
def FN.keep_of_not_member_step(+g: +List<Nat>, +w: +List<Nat>,
    +t: +List<+List<Nat>>, b: Bool, +eb: {b == Feedback.word_eq(g, w) : Bool},
    +nm: {Tree.member_word(g, w <> t) == False{} : Bool},
    rec: {Tree.member_word(g, t) == False{} : Bool} ->
         {SolveFast.keep_fast(g, t) == Groups.len_words(t) : Nat}) ->
  {SolveFast.keep_fast(g, w <> t) == Groups.len_words(w <> t) : Nat}:
  match b:
    case True{}:
      +et : {Tree.member_word(g, w <> t) == True{} : Bool} =
        Equal.cong(Bool, Bool,
          x => Feedback.Bool.case(Bool, x, True{}, Tree.member_word(g, t)),
          Feedback.word_eq(g, w), True{},
          Equal.sym(Bool, True{}, Feedback.word_eq(g, w), eb))
      Empty.absurd(
        {SolveFast.keep_fast(g, w <> t) == Groups.len_words(w <> t) : Nat},
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, Tree.member_word(g, w <> t), False{},
            Equal.sym(Bool, Tree.member_word(g, w <> t), True{}, et), nm)))
    case False{}:
      +nmt : {Tree.member_word(g, t) == False{} : Bool} =
        Equal.trans(Bool, Tree.member_word(g, t), Tree.member_word(g, w <> t),
          False{},
          Equal.cong(Bool, Bool,
            x => Feedback.Bool.case(Bool, x, True{}, Tree.member_word(g, t)),
            False{}, Feedback.word_eq(g, w), eb),
          nm)
      +ewf : {SolveFast.word_eq_fast(g, w) == False{} : Bool} =
        Equal.trans(Bool, SolveFast.word_eq_fast(g, w),
          Feedback.word_eq(g, w), False{},
          FG.FG.word_eq_fast_eq(g, w),
          Equal.sym(Bool, False{}, Feedback.word_eq(g, w), eb))
      Equal.trans(Nat,
        SolveFast.keep_step(SolveFast.keep_fast(g, t),
          SolveFast.word_eq_fast(g, w)),
        Nat.add(1n, SolveFast.keep_fast(g, t)),
        Nat.add(1n, Groups.len_words(t)),
        Equal.cong(Bool, Nat,
          x => SolveFast.keep_step(SolveFast.keep_fast(g, t), x),
          SolveFast.word_eq_fast(g, w), False{}, ewf),
        Equal.cong(Nat, Nat, x => Nat.add(1n, x),
          SolveFast.keep_fast(g, t), Groups.len_words(t), rec(nmt)))

def FN.keep_of_not_member(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +nm: {Tree.member_word(g, S) == False{} : Bool}) ->
  {SolveFast.keep_fast(g, S) == Groups.len_words(S) : Nat}:
  match S:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      FN.keep_of_not_member_step(g, w, t, Feedback.word_eq(g, w), {==}, nm,
        nmt => FN.keep_of_not_member(g, t, nmt))

def FN.keep_of_member_step(+g: +List<Nat>, +w: +List<Nat>,
    +t: +List<+List<Nat>>, b: Bool, +eb: {b == Feedback.word_eq(g, w) : Bool},
    +nd: {FN.no_dup_ref(w <> t) == True{} : Bool},
    +mw: {Tree.member_word(g, w <> t) == True{} : Bool},
    rec: {FN.no_dup_ref(t) == True{} : Bool} ->
         {Tree.member_word(g, t) == True{} : Bool} ->
         {Nat.add(1n, SolveFast.keep_fast(g, t)) == Groups.len_words(t)
          : Nat}) ->
  {Nat.add(1n, SolveFast.keep_fast(g, w <> t)) == Groups.len_words(w <> t)
   : Nat}:
  match b:
    case True{}:
      +nmw : {Tree.member_word(w, t) == False{} : Bool} =
        FN.false_of_not_true(Tree.member_word(w, t),
          Logic.Proof.and_true_l(Bool.not(Tree.member_word(w, t)),
            FN.no_dup_ref(t), nd))
      +egw : {g == w : +List<Nat>} =
        CoverList.Cover.word_eq_true(g, w,
          Equal.sym(Bool, True{}, Feedback.word_eq(g, w), eb))
      +nmg : {Tree.member_word(g, t) == False{} : Bool} =
        Equal.trans(Bool, Tree.member_word(g, t), Tree.member_word(w, t),
          False{},
          Equal.cong(+List<Nat>, Bool, x => Tree.member_word(x, t), g, w, egw),
          nmw)
      +ewt : {SolveFast.word_eq_fast(g, w) == True{} : Bool} =
        Equal.trans(Bool, SolveFast.word_eq_fast(g, w),
          Feedback.word_eq(g, w), True{},
          FG.FG.word_eq_fast_eq(g, w),
          Equal.sym(Bool, True{}, Feedback.word_eq(g, w), eb))
      +ekt : {SolveFast.keep_fast(g, t) == Groups.len_words(t) : Nat} =
        FN.keep_of_not_member(g, t, nmg)
      Equal.trans(Nat,
        Nat.add(1n, SolveFast.keep_step(SolveFast.keep_fast(g, t),
          SolveFast.word_eq_fast(g, w))),
        Nat.add(1n, SolveFast.keep_fast(g, t)),
        Nat.add(1n, Groups.len_words(t)),
        Equal.cong(Bool, Nat,
          x => Nat.add(1n, SolveFast.keep_step(SolveFast.keep_fast(g, t), x)),
          SolveFast.word_eq_fast(g, w), True{}, ewt),
        Equal.cong(Nat, Nat, x => Nat.add(1n, x),
          SolveFast.keep_fast(g, t), Groups.len_words(t), ekt))
    case False{}:
      +ndt : {FN.no_dup_ref(t) == True{} : Bool} =
        Logic.Proof.and_true_r(Bool.not(Tree.member_word(w, t)),
          FN.no_dup_ref(t), nd)
      +mwt : {Tree.member_word(g, t) == True{} : Bool} =
        Equal.trans(Bool, Tree.member_word(g, t), Tree.member_word(g, w <> t),
          True{},
          Equal.cong(Bool, Bool,
            x => Feedback.Bool.case(Bool, x, True{}, Tree.member_word(g, t)),
            False{}, Feedback.word_eq(g, w), eb),
          mw)
      +ewf : {SolveFast.word_eq_fast(g, w) == False{} : Bool} =
        Equal.trans(Bool, SolveFast.word_eq_fast(g, w),
          Feedback.word_eq(g, w), False{},
          FG.FG.word_eq_fast_eq(g, w),
          Equal.sym(Bool, False{}, Feedback.word_eq(g, w), eb))
      Equal.trans(Nat,
        Nat.add(1n, SolveFast.keep_step(SolveFast.keep_fast(g, t),
          SolveFast.word_eq_fast(g, w))),
        Nat.add(1n, Nat.add(1n, SolveFast.keep_fast(g, t))),
        Nat.add(1n, Groups.len_words(t)),
        Equal.cong(Bool, Nat,
          x => Nat.add(1n, SolveFast.keep_step(SolveFast.keep_fast(g, t), x)),
          SolveFast.word_eq_fast(g, w), False{}, ewf),
        Equal.cong(Nat, Nat, x => Nat.add(1n, x),
          Nat.add(1n, SolveFast.keep_fast(g, t)), Groups.len_words(t),
          rec(ndt, mwt)))

def FN.keep_of_member(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +nd: {FN.no_dup_ref(S) == True{} : Bool},
    +mw: {Tree.member_word(g, S) == True{} : Bool}) ->
  {Nat.add(1n, SolveFast.keep_fast(g, S)) == Groups.len_words(S) : Nat}:
  match S:
    case Nil{}:
      Empty.absurd({1n == 0n : Nat}, Logic.Proof.false_ne_true(mw))
    case Con{+w, +t}:
      FN.keep_of_member_step(g, w, t, Feedback.word_eq(g, w), {==}, nd, mw,
        ndt => mwt => FN.keep_of_member(g, t, ndt, mwt))

# `|S| <= 1 + keep_fast(g, S)` on any duplicate-free candidate list `S`.
def FN.len_le_succ_keep_go(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +nd: {FN.no_dup_ref(S) == True{} : Bool},
    b: Bool, +eb: {b == Tree.member_word(g, S) : Bool}) ->
  {Nat.is_le(Groups.len_words(S), Nat.add(1n, SolveFast.keep_fast(g, S)))
   == True{} : Bool}:
  match b:
    case True{}:
      +mw : {Tree.member_word(g, S) == True{} : Bool} =
        Equal.sym(Bool, True{}, Tree.member_word(g, S), eb)
      +ek : {Nat.add(1n, SolveFast.keep_fast(g, S)) == Groups.len_words(S) : Nat} =
        FN.keep_of_member(g, S, nd, mw)
      NatProof.Nat.is_le_eq_r(Groups.len_words(S), Groups.len_words(S),
        Nat.add(1n, SolveFast.keep_fast(g, S)),
        Equal.sym(Nat, Nat.add(1n, SolveFast.keep_fast(g, S)),
          Groups.len_words(S), ek),
        NatProof.Nat.is_le_refl(Groups.len_words(S)))
    case False{}:
      +nm : {Tree.member_word(g, S) == False{} : Bool} =
        Equal.sym(Bool, False{}, Tree.member_word(g, S), eb)
      +ek : {SolveFast.keep_fast(g, S) == Groups.len_words(S) : Nat} =
        FN.keep_of_not_member(g, S, nm)
      NatProof.Nat.is_le_eq_r(Groups.len_words(S),
        Nat.add(1n, Groups.len_words(S)),
        Nat.add(1n, SolveFast.keep_fast(g, S)),
        Equal.cong(Nat, Nat, x => Nat.add(1n, x),
          Groups.len_words(S), SolveFast.keep_fast(g, S),
          Equal.sym(Nat, SolveFast.keep_fast(g, S), Groups.len_words(S), ek)),
        NatProof.Nat.is_le_of_lt(Groups.len_words(S),
          Nat.add(1n, Groups.len_words(S)),
          NatProof.Nat.is_lt_succ_self(Groups.len_words(S))))

def FN.len_le_succ_keep(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +nd: {FN.no_dup_ref(S) == True{} : Bool}) ->
  {Nat.is_le(Groups.len_words(S), Nat.add(1n, SolveFast.keep_fast(g, S)))
   == True{} : Bool}:
  FN.len_le_succ_keep_go(g, S, nd, Tree.member_word(g, S), {==})

# `pre_lb(|S|, g, S) == 2 * |S|` when `g` is not in `S`.
def FN.pre_lb_of_not_member(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +nm: {Tree.member_word(g, S) == False{} : Bool}) ->
  {SolveFast.pre_lb(Groups.len_words(S), g, S)
   == Nat.add(Groups.len_words(S), Groups.len_words(S)) : Nat}:
  Equal.cong(Nat, Nat, x => Nat.add(Groups.len_words(S), x),
    SolveFast.keep_fast(g, S), Groups.len_words(S),
    FN.keep_of_not_member(g, S, nm))

# `2 * |S| - 1 <= pre_lb(|S|, g, S)` for every guess `g` on duplicate-free `S`.
def FN.sub_one_le(a: Nat) -> {Nat.is_le(Nat.sub(a, 1n), a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      match p:
        case 0n:
          {==}
        case 1n++q:
          NatProof.Nat.is_le_of_lt(1n+q, 1n+(1n+q),
            NatProof.Nat.is_lt_succ_self(1n+q))

def FN.floor_le_pre_lb_go(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +nd: {FN.no_dup_ref(S) == True{} : Bool},
    b: Bool, +eb: {b == Tree.member_word(g, S) : Bool}) ->
  {Nat.is_le(
     Nat.sub(Nat.add(Groups.len_words(S), Groups.len_words(S)), 1n),
     SolveFast.pre_lb(Groups.len_words(S), g, S)) == True{} : Bool}:
  match b:
    case False{}:
      +n : Nat = Groups.len_words(S)
      +nm : {Tree.member_word(g, S) == False{} : Bool} =
        Equal.sym(Bool, False{}, Tree.member_word(g, S), eb)
      NatProof.Nat.is_le_eq_r(Nat.sub(Nat.add(n, n), 1n),
        Nat.add(n, n), SolveFast.pre_lb(n, g, S),
        Equal.sym(Nat, SolveFast.pre_lb(n, g, S), Nat.add(n, n),
          FN.pre_lb_of_not_member(g, S, nm)),
        FN.sub_one_le(Nat.add(n, n)))
    case True{}:
      +n : Nat = Groups.len_words(S)
      +k : Nat = SolveFast.keep_fast(g, S)
      +mw : {Tree.member_word(g, S) == True{} : Bool} =
        Equal.sym(Bool, True{}, Tree.member_word(g, S), eb)
      +ek : {Nat.add(1n, k) == n : Nat} = FN.keep_of_member(g, S, nd, mw)
      +e1 : {Nat.add(n, n) == Nat.add(1n, Nat.add(n, k)) : Nat} =
        Equal.trans(Nat,
          Nat.add(n, n),
          Nat.add(n, Nat.add(1n, k)),
          Nat.add(1n, Nat.add(n, k)),
          Equal.cong(Nat, Nat, x => Nat.add(n, x), n, Nat.add(1n, k),
            Equal.sym(Nat, Nat.add(1n, k), n, ek)),
          NatProof.NatPrf.add_succ(n, k))
      +esub : {Nat.sub(Nat.add(n, n), 1n) == Nat.add(n, k) : Nat} =
        Equal.trans(Nat,
          Nat.sub(Nat.add(n, n), 1n),
          Nat.sub(Nat.add(1n, Nat.add(n, k)), 1n),
          Nat.add(n, k),
          Equal.cong(Nat, Nat, x => Nat.sub(x, 1n),
            Nat.add(n, n), Nat.add(1n, Nat.add(n, k)), e1),
          FLB.FS.sub_zero(Nat.add(n, k)))
      NatProof.Nat.is_le_eq_l(SolveFast.pre_lb(n, g, S),
        Nat.add(n, k), Nat.sub(Nat.add(n, n), 1n),
        Equal.sym(Nat, Nat.sub(Nat.add(n, n), 1n), Nat.add(n, k), esub),
        NatProof.Nat.is_le_refl(Nat.add(n, k)))

def FN.floor_le_pre_lb(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +nd: {FN.no_dup_ref(S) == True{} : Bool}) ->
  {Nat.is_le(
     Nat.sub(Nat.add(Groups.len_words(S), Groups.len_words(S)), 1n),
     SolveFast.pre_lb(Groups.len_words(S), g, S)) == True{} : Bool}:
  FN.floor_le_pre_lb_go(g, S, nd, Tree.member_word(g, S), {==})

# Once `best_cost(best) <= 2*|S| - 1` on a duplicate-free candidate list `S`,
# no remaining guess in `gs` can strictly improve `best`.
def FN.guesses_floor_skip(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>, +best: SolveRef.Best,
    +nd: {FN.no_dup_ref(S) == True{} : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hfl: {Nat.is_le(Eval.Eval.cost_of(best),
             Nat.sub(Nat.add(Groups.len_words(S), Groups.len_words(S)), 1n))
           == True{} : Bool}) ->
  {Eval.Eval.guesses(1n+p, G, S, inf, gs, best) == best : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      +le : {Nat.is_le(Eval.Eval.cost_of(best),
               SolveFast.pre_lb(Groups.len_words(S), g, S))
             == True{} : Bool} =
        NatProof.Nat.is_le_trans(Eval.Eval.cost_of(best),
          Nat.sub(Nat.add(Groups.len_words(S), Groups.len_words(S)), 1n),
          SolveFast.pre_lb(Groups.len_words(S), g, S),
          hfl, FN.floor_le_pre_lb(g, S, nd))
      +geq : {Eval.Eval.guess(p, G, S, g, inf, best) == best : SolveRef.Best} =
        FLB.FS.pre_guess_skip_eq(p, inf, G, S, g, best, ele, hz, hbest, le)
      Equal.trans(SolveRef.Best,
        Eval.Eval.guesses(1n+p, G, S, inf, t,
          Eval.Eval.guess(p, G, S, g, inf, best)),
        Eval.Eval.guesses(1n+p, G, S, inf, t, best),
        best,
        Equal.cong(SolveRef.Best, SolveRef.Best,
          b => Eval.Eval.guesses(1n+p, G, S, inf, t, b),
          Eval.Eval.guess(p, G, S, g, inf, best), best, geq),
        FN.guesses_floor_skip(p, inf, G, S, t, best, nd, ele, hz, hbest, hfl))

# `rev_words` algebra and `FGroup` -> `Groups.Group` correspondence.
def FN.list_append_nil(+xs: +List<+List<Nat>>) ->
  {List.append(&2, +List<Nat>, xs, Nil{}) == xs : +List<+List<Nat>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>, l => h <> l,
        List.append(&2, +List<Nat>, t, Nil{}), t, FN.list_append_nil(t))

def FN.list_append_assoc(+xs: +List<+List<Nat>>, +ys: +List<+List<Nat>>,
    +zs: +List<+List<Nat>>) ->
  {List.append(&2, +List<Nat>, List.append(&2, +List<Nat>, xs, ys), zs)
   == List.append(&2, +List<Nat>, xs, List.append(&2, +List<Nat>, ys, zs))
   : +List<+List<Nat>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>, l => h <> l,
        List.append(&2, +List<Nat>, List.append(&2, +List<Nat>, t, ys), zs),
        List.append(&2, +List<Nat>, t, List.append(&2, +List<Nat>, ys, zs)),
        FN.list_append_assoc(t, ys, zs))

def FN.rev_words_acc(+xs: +List<+List<Nat>>, +acc: +List<+List<Nat>>) ->
  {SolveFast.rev_words(xs, acc)
   == List.append(&2, +List<Nat>, SolveFast.rev_words(xs, Nil{}), acc)
   : +List<+List<Nat>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +e1 : {SolveFast.rev_words(t, h <> acc)
             == List.append(&2, +List<Nat>, SolveFast.rev_words(t, Nil{}),
                  h <> acc) : +List<+List<Nat>>} =
        FN.rev_words_acc(t, h <> acc)
      +e2 : {SolveFast.rev_words(t, h <> Nil{})
             == List.append(&2, +List<Nat>, SolveFast.rev_words(t, Nil{}),
                  h <> Nil{}) : +List<+List<Nat>>} =
        FN.rev_words_acc(t, h <> Nil{})
      +e3 : {List.append(&2, +List<Nat>,
               List.append(&2, +List<Nat>, SolveFast.rev_words(t, Nil{}),
                 h <> Nil{}), acc)
             == List.append(&2, +List<Nat>, SolveFast.rev_words(t, Nil{}),
                  h <> acc) : +List<+List<Nat>>} =
        FN.list_append_assoc(SolveFast.rev_words(t, Nil{}), h <> Nil{}, acc)
      +e4 : {List.append(&2, +List<Nat>, SolveFast.rev_words(t, h <> Nil{}),
               acc)
             == List.append(&2, +List<Nat>,
                  List.append(&2, +List<Nat>, SolveFast.rev_words(t, Nil{}),
                    h <> Nil{}), acc) : +List<+List<Nat>>} =
        Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
          l => List.append(&2, +List<Nat>, l, acc),
          SolveFast.rev_words(t, h <> Nil{}),
          List.append(&2, +List<Nat>, SolveFast.rev_words(t, Nil{}), h <> Nil{}),
          e2)
      Equal.trans(+List<+List<Nat>>,
        SolveFast.rev_words(t, h <> acc),
        List.append(&2, +List<Nat>, SolveFast.rev_words(t, Nil{}), h <> acc),
        List.append(&2, +List<Nat>, SolveFast.rev_words(t, h <> Nil{}), acc),
        e1,
        Equal.sym(+List<+List<Nat>>,
          List.append(&2, +List<Nat>, SolveFast.rev_words(t, h <> Nil{}), acc),
          List.append(&2, +List<Nat>, SolveFast.rev_words(t, Nil{}), h <> acc),
          Equal.trans(+List<+List<Nat>>,
            List.append(&2, +List<Nat>, SolveFast.rev_words(t, h <> Nil{}), acc),
            List.append(&2, +List<Nat>,
              List.append(&2, +List<Nat>, SolveFast.rev_words(t, Nil{}),
                h <> Nil{}), acc),
            List.append(&2, +List<Nat>, SolveFast.rev_words(t, Nil{}), h <> acc),
            e4, e3)))

def FN.len_rev_words(+xs: +List<+List<Nat>>, +acc: +List<+List<Nat>>) ->
  {Groups.len_words(SolveFast.rev_words(xs, acc))
   == Nat.add(Groups.len_words(xs), Groups.len_words(acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat,
        Groups.len_words(SolveFast.rev_words(t, h <> acc)),
        Nat.add(Groups.len_words(t), Nat.add(1n, Groups.len_words(acc))),
        Nat.add(1n, Nat.add(Groups.len_words(t), Groups.len_words(acc))),
        FN.len_rev_words(t, h <> acc),
        NatProof.NatPrf.add_succ(Groups.len_words(t), Groups.len_words(acc)))

def FN.len_rev_nil(+xs: +List<+List<Nat>>) ->
  {Groups.len_words(SolveFast.rev_words(xs, Nil{}))
   == Groups.len_words(xs) : Nat}:
  Equal.trans(Nat,
    Groups.len_words(SolveFast.rev_words(xs, Nil{})),
    Nat.add(Groups.len_words(xs), 0n),
    Groups.len_words(xs),
    FN.len_rev_words(xs, Nil{}),
    NatProof.NatPrf.add_zero(Groups.len_words(xs)))

# Convert `FGroup`s back to reference `Groups.Group`s.
def FN.fgroups_to_groups(+fgroups: +List<SolveFast.FGroup>) ->
  +List<Groups.Group>:
  match fgroups:
    case Nil{}:
      Nil{}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{f, len, rws}:
          Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
          <> FN.fgroups_to_groups(rest)

# Cached-length invariant on `FGroup`s.
def FN.fgroups_lens_ok(+fgroups: +List<SolveFast.FGroup>) -> Bool:
  match fgroups:
    case Nil{}:
      True{}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{f, len, rws}:
          Bool.and(Nat.is_eq(len, Groups.len_words(rws)),
            FN.fgroups_lens_ok(rest))

def FN.fgroup_add_go_eq(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +fgroups: +List<SolveFast.FGroup>, hit: Bool,
    +eh: {hit == SolveFast.next_fgroup_hit(fb, fgroups) : Bool}) ->
  {FN.fgroups_to_groups(SolveFast.fgroup_add_go(w, fb, fgroups, hit))
   == Groups.group_add(w, fb, FN.fgroups_to_groups(fgroups))
   : +List<Groups.Group>}:
  match fgroups:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          match hit:
            case True{}:
              +eh_ref : {True{} == Feedback.feedback_eq(fb, f) : Bool} =
                Equal.trans(Bool, True{},
                  SolveFast.feedback_eq_fast(fb, f),
                  Feedback.feedback_eq(fb, f),
                  eh, FG.FG.feedback_eq_fast_eq(fb, f))
              +erw : {SolveFast.rev_words(w <> rws, Nil{})
                      == List.append(&2, +List<Nat>,
                           SolveFast.rev_words(rws, Nil{}), [w])
                      : +List<+List<Nat>>} =
                FN.rev_words_acc(rws, [w])
              +e1 : {Groups.Group{f, SolveFast.rev_words(w <> rws, Nil{})}
                     <> FN.fgroups_to_groups(rest)
                     == Groups.Group{f,
                          List.append(&2, +List<Nat>,
                            SolveFast.rev_words(rws, Nil{}), [w])}
                        <> FN.fgroups_to_groups(rest)
                     : +List<Groups.Group>} =
                Equal.cong(+List<+List<Nat>>, +List<Groups.Group>,
                  ws => Groups.Group{f, ws} <> FN.fgroups_to_groups(rest),
                  SolveFast.rev_words(w <> rws, Nil{}),
                  List.append(&2, +List<Nat>,
                    SolveFast.rev_words(rws, Nil{}), [w]),
                  erw)
              +e2 : {Groups.Group{f,
                       List.append(&2, +List<Nat>,
                         SolveFast.rev_words(rws, Nil{}), [w])}
                     <> FN.fgroups_to_groups(rest)
                     == Groups.group_add(w, fb,
                          Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
                          <> FN.fgroups_to_groups(rest))
                     : +List<Groups.Group>} =
                Equal.cong(Bool, +List<Groups.Group>,
                  b => Feedback.Bool.case(+List<Groups.Group>, b,
                         Groups.Group{f,
                           List.append(&2, +List<Nat>,
                             SolveFast.rev_words(rws, Nil{}), [w])}
                         <> FN.fgroups_to_groups(rest),
                         Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
                         <> Groups.group_add(w, fb,
                              FN.fgroups_to_groups(rest))),
                  True{}, Feedback.feedback_eq(fb, f), eh_ref)
              Equal.trans(+List<Groups.Group>,
                Groups.Group{f, SolveFast.rev_words(w <> rws, Nil{})}
                <> FN.fgroups_to_groups(rest),
                Groups.Group{f,
                  List.append(&2, +List<Nat>,
                    SolveFast.rev_words(rws, Nil{}), [w])}
                <> FN.fgroups_to_groups(rest),
                Groups.group_add(w, fb,
                  Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
                  <> FN.fgroups_to_groups(rest)),
                e1, e2)
            case False{}:
              +eh_ref : {False{} == Feedback.feedback_eq(fb, f) : Bool} =
                Equal.trans(Bool, False{},
                  SolveFast.feedback_eq_fast(fb, f),
                  Feedback.feedback_eq(fb, f),
                  eh, FG.FG.feedback_eq_fast_eq(fb, f))
              +e1 : {Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
                     <> FN.fgroups_to_groups(
                          SolveFast.fgroup_add_go(w, fb, rest,
                            SolveFast.next_fgroup_hit(fb, rest)))
                     == Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
                        <> Groups.group_add(w, fb, FN.fgroups_to_groups(rest))
                     : +List<Groups.Group>} =
                Equal.cong(+List<Groups.Group>, +List<Groups.Group>,
                  l => Groups.Group{f, SolveFast.rev_words(rws, Nil{})} <> l,
                  FN.fgroups_to_groups(
                    SolveFast.fgroup_add_go(w, fb, rest,
                      SolveFast.next_fgroup_hit(fb, rest))),
                  Groups.group_add(w, fb, FN.fgroups_to_groups(rest)),
                  FN.fgroup_add_go_eq(w, fb, rest,
                    SolveFast.next_fgroup_hit(fb, rest), {==}))
              +e2 : {Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
                     <> Groups.group_add(w, fb, FN.fgroups_to_groups(rest))
                     == Groups.group_add(w, fb,
                          Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
                          <> FN.fgroups_to_groups(rest))
                     : +List<Groups.Group>} =
                Equal.cong(Bool, +List<Groups.Group>,
                  b => Feedback.Bool.case(+List<Groups.Group>, b,
                         Groups.Group{f,
                           List.append(&2, +List<Nat>,
                             SolveFast.rev_words(rws, Nil{}), [w])}
                         <> FN.fgroups_to_groups(rest),
                         Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
                         <> Groups.group_add(w, fb,
                              FN.fgroups_to_groups(rest))),
                  False{}, Feedback.feedback_eq(fb, f), eh_ref)
              Equal.trans(+List<Groups.Group>,
                Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
                <> FN.fgroups_to_groups(
                     SolveFast.fgroup_add_go(w, fb, rest,
                       SolveFast.next_fgroup_hit(fb, rest))),
                Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
                <> Groups.group_add(w, fb, FN.fgroups_to_groups(rest)),
                Groups.group_add(w, fb,
                  Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
                  <> FN.fgroups_to_groups(rest)),
                e1, e2)

def FN.fgroup_add_eq(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +fgroups: +List<SolveFast.FGroup>) ->
  {FN.fgroups_to_groups(SolveFast.fgroup_add_fast(w, fb, fgroups))
   == Groups.group_add(w, fb, FN.fgroups_to_groups(fgroups))
   : +List<Groups.Group>}:
  FN.fgroup_add_go_eq(w, fb, fgroups,
    SolveFast.next_fgroup_hit(fb, fgroups), {==})

def FN.fgroup_add_feedback_eq(+g: +List<Nat>, +w: +List<Nat>,
    +acc: +List<SolveFast.FGroup>) ->
  {FN.fgroups_to_groups(
     SolveFast.fgroup_add_fast(w, SolveFast.feedback_fast(g, w), acc))
   == Groups.group_add(w, Feedback.feedback(g, w), FN.fgroups_to_groups(acc))
   : +List<Groups.Group>}:
  Equal.trans(+List<Groups.Group>,
    FN.fgroups_to_groups(
      SolveFast.fgroup_add_fast(w, SolveFast.feedback_fast(g, w), acc)),
    FN.fgroups_to_groups(
      SolveFast.fgroup_add_fast(w, Feedback.feedback(g, w), acc)),
    Groups.group_add(w, Feedback.feedback(g, w), FN.fgroups_to_groups(acc)),
    Equal.cong(+List<Feedback.Color>, +List<Groups.Group>,
      fb => FN.fgroups_to_groups(SolveFast.fgroup_add_fast(w, fb, acc)),
      SolveFast.feedback_fast(g, w), Feedback.feedback(g, w),
      FG.FG.feedback_eq(g, w)),
    FN.fgroup_add_eq(w, Feedback.feedback(g, w), acc))

def FN.fgroups_step_eq(+g: +List<Nat>, +w: +List<Nat>,
    +rest: +List<+List<Nat>>, +acc: +List<SolveFast.FGroup>, same: Bool) ->
  {Groups.groups_build(g, rest,
     FN.fgroups_to_groups(SolveFast.fgroups_next_acc(g, w, acc, same)))
   == Feedback.Bool.case(+List<Groups.Group>, same,
        Groups.groups_build(g, rest, FN.fgroups_to_groups(acc)),
        Groups.groups_build(g, rest,
          Groups.group_add(w, Feedback.feedback(g, w),
            FN.fgroups_to_groups(acc))))
   : +List<Groups.Group>}:
  match same:
    case True{}:
      {==}
    case False{}:
      Equal.cong(+List<Groups.Group>, +List<Groups.Group>,
        a => Groups.groups_build(g, rest, a),
        FN.fgroups_to_groups(
          SolveFast.fgroup_add_fast(w, SolveFast.feedback_fast(g, w), acc)),
        Groups.group_add(w, Feedback.feedback(g, w), FN.fgroups_to_groups(acc)),
        FN.fgroup_add_feedback_eq(g, w, acc))

def FN.fgroups_build_eq(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +acc: +List<SolveFast.FGroup>) ->
  {FN.fgroups_to_groups(SolveFast.fgroups_build_fast(g, S, acc))
   == Groups.groups_build(g, S, FN.fgroups_to_groups(acc))
   : +List<Groups.Group>}:
  match S:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      +ew : {Groups.groups_build(g, rest,
               FN.fgroups_to_groups(
                 SolveFast.fgroups_next_acc(g, w, acc,
                   SolveFast.word_eq_fast(g, w))))
             == Groups.groups_build(g, rest,
                  FN.fgroups_to_groups(
                    SolveFast.fgroups_next_acc(g, w, acc,
                      Feedback.word_eq(g, w))))
             : +List<Groups.Group>} =
        Equal.cong(Bool, +List<Groups.Group>,
          b => Groups.groups_build(g, rest,
                 FN.fgroups_to_groups(
                   SolveFast.fgroups_next_acc(g, w, acc, b))),
          SolveFast.word_eq_fast(g, w), Feedback.word_eq(g, w),
          FG.FG.word_eq_fast_eq(g, w))
      Equal.trans(+List<Groups.Group>,
        FN.fgroups_to_groups(
          SolveFast.fgroups_build_fast(g, rest,
            SolveFast.fgroups_next_acc(g, w, acc,
              SolveFast.word_eq_fast(g, w)))),
        Groups.groups_build(g, rest,
          FN.fgroups_to_groups(
            SolveFast.fgroups_next_acc(g, w, acc, Feedback.word_eq(g, w)))),
        Groups.groups_build(g, w <> rest, FN.fgroups_to_groups(acc)),
        Equal.trans(+List<Groups.Group>,
          FN.fgroups_to_groups(
            SolveFast.fgroups_build_fast(g, rest,
              SolveFast.fgroups_next_acc(g, w, acc,
                SolveFast.word_eq_fast(g, w)))),
          Groups.groups_build(g, rest,
            FN.fgroups_to_groups(
              SolveFast.fgroups_next_acc(g, w, acc,
                SolveFast.word_eq_fast(g, w)))),
          Groups.groups_build(g, rest,
            FN.fgroups_to_groups(
              SolveFast.fgroups_next_acc(g, w, acc, Feedback.word_eq(g, w)))),
          FN.fgroups_build_eq(g, rest,
            SolveFast.fgroups_next_acc(g, w, acc,
              SolveFast.word_eq_fast(g, w))),
          ew),
        FN.fgroups_step_eq(g, w, rest, acc, Feedback.word_eq(g, w)))

# Cached-length invariant preservation.
def FN.fgroup_add_lens_ok(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +fgroups: +List<SolveFast.FGroup>, hit: Bool,
    +lok: {FN.fgroups_lens_ok(fgroups) == True{} : Bool}) ->
  {FN.fgroups_lens_ok(SolveFast.fgroup_add_go(w, fb, fgroups, hit))
   == True{} : Bool}:
  match fgroups:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          match hit:
            case True{}:
              +lh : {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool} =
                Logic.Proof.and_true_l(Nat.is_eq(len, Groups.len_words(rws)),
                  FN.fgroups_lens_ok(rest), lok)
              +lt : {FN.fgroups_lens_ok(rest) == True{} : Bool} =
                Logic.Proof.and_true_r(Nat.is_eq(len, Groups.len_words(rws)),
                  FN.fgroups_lens_ok(rest), lok)
              FO.FO.bool_and_intro(
                Nat.is_eq(Nat.add(1n, len), Nat.add(1n, Groups.len_words(rws))),
                FN.fgroups_lens_ok(rest), lh, lt)
            case False{}:
              +lh : {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool} =
                Logic.Proof.and_true_l(Nat.is_eq(len, Groups.len_words(rws)),
                  FN.fgroups_lens_ok(rest), lok)
              +lt : {FN.fgroups_lens_ok(rest) == True{} : Bool} =
                Logic.Proof.and_true_r(Nat.is_eq(len, Groups.len_words(rws)),
                  FN.fgroups_lens_ok(rest), lok)
              FO.FO.bool_and_intro(
                Nat.is_eq(len, Groups.len_words(rws)),
                FN.fgroups_lens_ok(
                  SolveFast.fgroup_add_go(w, fb, rest,
                    SolveFast.next_fgroup_hit(fb, rest))),
                lh,
                FN.fgroup_add_lens_ok(w, fb, rest,
                  SolveFast.next_fgroup_hit(fb, rest), lt))

def FN.fgroups_next_lens_ok(+g: +List<Nat>, +w: +List<Nat>,
    +acc: +List<SolveFast.FGroup>, same: Bool,
    +lok: {FN.fgroups_lens_ok(acc) == True{} : Bool}) ->
  {FN.fgroups_lens_ok(SolveFast.fgroups_next_acc(g, w, acc, same))
   == True{} : Bool}:
  match same:
    case True{}:
      lok
    case False{}:
      FN.fgroup_add_lens_ok(w, SolveFast.feedback_fast(g, w), acc,
        SolveFast.next_fgroup_hit(SolveFast.feedback_fast(g, w), acc), lok)

def FN.fgroups_build_lens_ok(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +acc: +List<SolveFast.FGroup>,
    +lok: {FN.fgroups_lens_ok(acc) == True{} : Bool}) ->
  {FN.fgroups_lens_ok(SolveFast.fgroups_build_fast(g, S, acc))
   == True{} : Bool}:
  match S:
    case Nil{}:
      lok
    case Con{+w, +rest}:
      FN.fgroups_build_lens_ok(g, rest,
        SolveFast.fgroups_next_acc(g, w, acc, SolveFast.word_eq_fast(g, w)),
        FN.fgroups_next_lens_ok(g, w, acc, SolveFast.word_eq_fast(g, w), lok))

# `fgroups_smaller` agrees with `Groups.groups_smaller` on `fgroups_to_groups`.
def FN.fgroups_smaller_go_eq(+S: +List<+List<Nat>>,
    +fgroups: +List<SolveFast.FGroup>, ok: Bool,
    +eok: {ok == SolveFast.next_fgroup_lt(Groups.len_words(S), fgroups) : Bool},
    +lok: {FN.fgroups_lens_ok(fgroups) == True{} : Bool}) ->
  {SolveFast.fgroups_smaller_go(Groups.len_words(S), fgroups, ok)
   == Groups.groups_smaller(S, FN.fgroups_to_groups(fgroups)) : Bool}:
  match fgroups:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          match ok:
            case True{}:
              +n : Nat = Groups.len_words(S)
              +lh : {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool} =
                Logic.Proof.and_true_l(Nat.is_eq(len, Groups.len_words(rws)),
                  FN.fgroups_lens_ok(rest), lok)
              +lt : {FN.fgroups_lens_ok(rest) == True{} : Bool} =
                Logic.Proof.and_true_r(Nat.is_eq(len, Groups.len_words(rws)),
                  FN.fgroups_lens_ok(rest), lok)
              +elen : {len == Groups.len_words(SolveFast.rev_words(rws, Nil{}))
                       : Nat} =
                Equal.trans(Nat, len, Groups.len_words(rws),
                  Groups.len_words(SolveFast.rev_words(rws, Nil{})),
                  NatProof.NatPrf.is_eq_true(len, Groups.len_words(rws), lh),
                  Equal.sym(Nat,
                    Groups.len_words(SolveFast.rev_words(rws, Nil{})),
                    Groups.len_words(rws), FN.len_rev_nil(rws)))
              +eh : {True{} == Nat.is_lt(
                       Groups.len_words(SolveFast.rev_words(rws, Nil{})), n)
                     : Bool} =
                Equal.trans(Bool, True{}, Nat.is_lt(len, n),
                  Nat.is_lt(Groups.len_words(SolveFast.rev_words(rws, Nil{})), n),
                  eok,
                  Equal.cong(Nat, Bool, x => Nat.is_lt(x, n),
                    len, Groups.len_words(SolveFast.rev_words(rws, Nil{})),
                    elen))
              +er : {SolveFast.fgroups_smaller_go(n, rest,
                       SolveFast.next_fgroup_lt(n, rest))
                     == Groups.groups_smaller(S, FN.fgroups_to_groups(rest))
                     : Bool} =
                FN.fgroups_smaller_go_eq(S, rest,
                  SolveFast.next_fgroup_lt(n, rest), {==}, lt)
              Equal.trans(Bool,
                SolveFast.fgroups_smaller_go(n, rest,
                  SolveFast.next_fgroup_lt(n, rest)),
                Groups.groups_smaller(S, FN.fgroups_to_groups(rest)),
                Groups.groups_smaller(S,
                  Groups.Group{f, SolveFast.rev_words(rws, Nil{})}
                  <> FN.fgroups_to_groups(rest)),
                er,
                Equal.cong(Bool, Bool,
                  b => Bool.and(b,
                         Groups.groups_smaller(S, FN.fgroups_to_groups(rest))),
                  True{},
                  Nat.is_lt(Groups.len_words(SolveFast.rev_words(rws, Nil{})), n),
                  eh))
            case False{}:
              +n : Nat = Groups.len_words(S)
              +lh : {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool} =
                Logic.Proof.and_true_l(Nat.is_eq(len, Groups.len_words(rws)),
                  FN.fgroups_lens_ok(rest), lok)
              +elen : {len == Groups.len_words(SolveFast.rev_words(rws, Nil{}))
                       : Nat} =
                Equal.trans(Nat, len, Groups.len_words(rws),
                  Groups.len_words(SolveFast.rev_words(rws, Nil{})),
                  NatProof.NatPrf.is_eq_true(len, Groups.len_words(rws), lh),
                  Equal.sym(Nat,
                    Groups.len_words(SolveFast.rev_words(rws, Nil{})),
                    Groups.len_words(rws), FN.len_rev_nil(rws)))
              +eh : {False{} == Nat.is_lt(
                       Groups.len_words(SolveFast.rev_words(rws, Nil{})), n)
                     : Bool} =
                Equal.trans(Bool, False{}, Nat.is_lt(len, n),
                  Nat.is_lt(Groups.len_words(SolveFast.rev_words(rws, Nil{})), n),
                  eok,
                  Equal.cong(Nat, Bool, x => Nat.is_lt(x, n),
                    len, Groups.len_words(SolveFast.rev_words(rws, Nil{})),
                    elen))
              Equal.cong(Bool, Bool,
                b => Bool.and(b,
                       Groups.groups_smaller(S, FN.fgroups_to_groups(rest))),
                False{},
                Nat.is_lt(Groups.len_words(SolveFast.rev_words(rws, Nil{})), n),
                eh)

def FN.fgroups_smaller_eq(+S: +List<+List<Nat>>,
    +fgroups: +List<SolveFast.FGroup>,
    +lok: {FN.fgroups_lens_ok(fgroups) == True{} : Bool}) ->
  {SolveFast.fgroups_smaller(Groups.len_words(S), fgroups)
   == Groups.groups_smaller(S, FN.fgroups_to_groups(fgroups)) : Bool}:
  FN.fgroups_smaller_go_eq(S, fgroups,
    SolveFast.next_fgroup_lt(Groups.len_words(S), fgroups), {==}, lok)

# `fgroups_lb` agrees with `SolveFast.lower_bound` on `fgroups_to_groups`.
def FN.fgroups_lb_nodup_eq(+fgroups: +List<SolveFast.FGroup>, +acc: Nat,
    +lok: {FN.fgroups_lens_ok(fgroups) == True{} : Bool},
    +ng: {FN.nodup_ok_jobs(True{},
            MV.MV.next_groups(FN.fgroups_to_groups(fgroups))) == True{} : Bool}) ->
  {SolveFast.fgroups_lb_nodup(fgroups, acc)
   == Nat.add(acc, SolveFast.class_words(FN.fgroups_to_groups(fgroups))) : Nat}:
  match fgroups:
    case Nil{}:
      Equal.sym(Nat, Nat.add(acc, 0n), acc, NatProof.NatPrf.add_zero(acc))
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          +ws : +List<+List<Nat>> = SolveFast.rev_words(rws, Nil{})
          +lh : {Nat.is_eq(len, Groups.len_words(rws)) == True{} : Bool} =
            Logic.Proof.and_true_l(Nat.is_eq(len, Groups.len_words(rws)),
              FN.fgroups_lens_ok(rest), lok)
          +lt : {FN.fgroups_lens_ok(rest) == True{} : Bool} =
            Logic.Proof.and_true_r(Nat.is_eq(len, Groups.len_words(rws)),
              FN.fgroups_lens_ok(rest), lok)
          +nh : {FN.no_dup_ref(ws) == True{} : Bool} =
            Logic.Proof.and_true_l(FN.no_dup_ref(ws),
              FN.nodup_ok_jobs(True{},
                MV.MV.next_groups(FN.fgroups_to_groups(rest))), ng)
          +nt : {FN.nodup_ok_jobs(True{},
                   MV.MV.next_groups(FN.fgroups_to_groups(rest)))
                 == True{} : Bool} =
            Logic.Proof.and_true_r(FN.no_dup_ref(ws),
              FN.nodup_ok_jobs(True{},
                MV.MV.next_groups(FN.fgroups_to_groups(rest))), ng)
          +elen : {len == Groups.len_words(ws) : Nat} =
            Equal.trans(Nat, len, Groups.len_words(rws), Groups.len_words(ws),
              NatProof.NatPrf.is_eq_true(len, Groups.len_words(rws), lh),
              Equal.sym(Nat, Groups.len_words(ws), Groups.len_words(rws),
                FN.len_rev_nil(rws)))
          +clb : Nat = Nat.sub(Nat.add(len, len), 1n)
          +eclb : {clb == SolveFast.class_lb(ws) : Nat} =
            FN.class_lb_fast_eq(True{}, len, ws, elen, nh)
          +ih : {SolveFast.fgroups_lb_nodup(rest, Nat.add(acc, clb))
                 == Nat.add(Nat.add(acc, clb),
                      SolveFast.class_words(FN.fgroups_to_groups(rest))) : Nat} =
            FN.fgroups_lb_nodup_eq(rest, Nat.add(acc, clb), lt, nt)
          Equal.trans(Nat,
            SolveFast.fgroups_lb_nodup(rest, Nat.add(acc, clb)),
            Nat.add(acc,
              Nat.add(clb, SolveFast.class_words(FN.fgroups_to_groups(rest)))),
            Nat.add(acc,
              Nat.add(SolveFast.class_lb(ws),
                SolveFast.class_words(FN.fgroups_to_groups(rest)))),
            Equal.trans(Nat,
              SolveFast.fgroups_lb_nodup(rest, Nat.add(acc, clb)),
              Nat.add(Nat.add(acc, clb),
                SolveFast.class_words(FN.fgroups_to_groups(rest))),
              Nat.add(acc,
                Nat.add(clb,
                  SolveFast.class_words(FN.fgroups_to_groups(rest)))),
              ih,
              NatProof.NatPrf.add_assoc(acc, clb,
                SolveFast.class_words(FN.fgroups_to_groups(rest)))),
            Equal.cong(Nat, Nat,
              x => Nat.add(acc,
                     Nat.add(x,
                       SolveFast.class_words(FN.fgroups_to_groups(rest)))),
              clb, SolveFast.class_lb(ws), eclb))

def FN.fgroups_lb_dup_eq(+fgroups: +List<SolveFast.FGroup>, +acc: Nat) ->
  {SolveFast.fgroups_lb_dup(fgroups, acc)
   == Nat.add(acc, SolveFast.class_words(FN.fgroups_to_groups(fgroups))) : Nat}:
  match fgroups:
    case Nil{}:
      Equal.sym(Nat, Nat.add(acc, 0n), acc, NatProof.NatPrf.add_zero(acc))
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          +ws : +List<+List<Nat>> = SolveFast.rev_words(rws, Nil{})
          +clb : Nat = SolveFast.class_lb(ws)
          Equal.trans(Nat,
            SolveFast.fgroups_lb_dup(rest, Nat.add(acc, clb)),
            Nat.add(Nat.add(acc, clb),
              SolveFast.class_words(FN.fgroups_to_groups(rest))),
            Nat.add(acc,
              Nat.add(clb, SolveFast.class_words(FN.fgroups_to_groups(rest)))),
            FN.fgroups_lb_dup_eq(rest, Nat.add(acc, clb)),
            NatProof.NatPrf.add_assoc(acc, clb,
              SolveFast.class_words(FN.fgroups_to_groups(rest))))

def FN.fgroups_lb_eq(+nodup: Bool, +n: Nat, +fgroups: +List<SolveFast.FGroup>,
    +lok: {FN.fgroups_lens_ok(fgroups) == True{} : Bool},
    +ng: {FN.nodup_ok_jobs(nodup,
            MV.MV.next_groups(FN.fgroups_to_groups(fgroups))) == True{} : Bool}) ->
  {SolveFast.fgroups_lb(nodup, n, fgroups)
   == SolveFast.lower_bound(n, FN.fgroups_to_groups(fgroups)) : Nat}:
  match nodup:
    case True{}:
      +groups : +List<Groups.Group> = FN.fgroups_to_groups(fgroups)
      Equal.trans(Nat,
        SolveFast.fgroups_lb_nodup(fgroups, n),
        Nat.add(n, SolveFast.class_words(groups)),
        SolveFast.lower_bound(n, groups),
        FN.fgroups_lb_nodup_eq(fgroups, n, lok, ng),
        Equal.sym(Nat, SolveFast.lower_bound(n, groups),
          Nat.add(n, SolveFast.class_words(groups)),
          FLB.FS.lower_bound_eq(n, groups)))
    case False{}:
      +groups : +List<Groups.Group> = FN.fgroups_to_groups(fgroups)
      Equal.trans(Nat,
        SolveFast.fgroups_lb_dup(fgroups, n),
        Nat.add(n, SolveFast.class_words(groups)),
        SolveFast.lower_bound(n, groups),
        FN.fgroups_lb_dup_eq(fgroups, n),
        Equal.sym(Nat, SolveFast.lower_bound(n, groups),
          Nat.add(n, SolveFast.class_words(groups)),
          FLB.FS.lower_bound_eq(n, groups)))

# `rev_words(wt3, [w3, w2, w])` has at least three elements, so `group_items`
# takes the `ClassItem` + `Add` branch.
def FN.group_items_ge3_eq(+nodup: Bool, +n: Nat, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +rest: +List<Groups.Group>,
    +k: Nat, +ek: {Groups.len_words(ws) == Nat.add(3n, k) : Nat}) ->
  {SolveFast.group_items(nodup, n, Groups.Group{f, ws} <> rest)
   == SolveFast.ClassItem{f, ws, Groups.len_words(ws),
        SolveFast.lower_bound(n, rest)}
      <> (SolveFast.Add{f, SolveFast.lower_bound(n, rest)}
          <> SolveFast.group_items(nodup, n, rest))
   : +List<SolveFast.Item>}:
  match ws:
    case Nil{}:
      Empty.absurd(
        {SolveFast.group_items(nodup, n, Groups.Group{f, Nil{}} <> rest)
         == SolveFast.ClassItem{f, Nil{}, 0n, SolveFast.lower_bound(n, rest)}
            <> (SolveFast.Add{f, SolveFast.lower_bound(n, rest)}
                <> SolveFast.group_items(nodup, n, rest))
         : +List<SolveFast.Item>},
        NatProof.NatPrf.zero_ne_succ(Nat.add(2n, k), ek))
    case Con{+w, +wt}:
      match wt:
        case Nil{}:
          +e0 : {0n == Nat.add(2n, k) : Nat} =
            NatProof.NatPrf.pred_succ(0n, Nat.add(2n, k), ek)
          Empty.absurd(
            {SolveFast.group_items(nodup, n, Groups.Group{f, w <> Nil{}} <> rest)
             == SolveFast.ClassItem{f, w <> Nil{}, 1n,
                  SolveFast.lower_bound(n, rest)}
                <> (SolveFast.Add{f, SolveFast.lower_bound(n, rest)}
                    <> SolveFast.group_items(nodup, n, rest))
             : +List<SolveFast.Item>},
            NatProof.NatPrf.zero_ne_succ(Nat.add(1n, k), e0))
        case Con{+w2, +wt2}:
          match wt2:
            case Nil{}:
              +e0 : {1n == Nat.add(2n, k) : Nat} =
                NatProof.NatPrf.pred_succ(1n, Nat.add(2n, k), ek)
              +e1 : {0n == Nat.add(1n, k) : Nat} =
                NatProof.NatPrf.pred_succ(0n, Nat.add(1n, k), e0)
              +ws2 : +List<+List<Nat>> = w <> (w2 <> Nil{})
              Empty.absurd(
                {SolveFast.group_items(nodup, n, Groups.Group{f, ws2} <> rest)
                 == SolveFast.ClassItem{f, ws2, 2n,
                      SolveFast.lower_bound(n, rest)}
                    <> (SolveFast.Add{f, SolveFast.lower_bound(n, rest)}
                        <> SolveFast.group_items(nodup, n, rest))
                 : +List<SolveFast.Item>},
                NatProof.NatPrf.zero_ne_succ(k, e1))
            case Con{+w3, +wt3}:
              {==}

def FN.fgroup_items_two_eq(nodup: Bool, +n: Nat, +f: +List<Feedback.Color>,
    +len: Nat, +w: +List<Nat>, +w2: +List<Nat>, +rg: +List<Groups.Group>,
    +tail: +List<SolveFast.Item>,
    +ib: SolveFast.ItemsBound,
    +eib: {ib == SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                   List.append(&2, SolveFast.Item,
                     SolveFast.group_items(nodup, n, rg), tail)}
           : SolveFast.ItemsBound},
    +elen: {len == 2n : Nat},
    +nh: {FN.nodup_ok(nodup, w2 <> (w <> Nil{})) == True{} : Bool}) ->
  {SolveFast.fgroup_items_two(nodup, f, len, w, w2, ib)
   == SolveFast.ItemsBound{
        SolveFast.lower_bound(n,
          Groups.Group{f, w2 <> (w <> Nil{})} <> rg),
        List.append(&2, SolveFast.Item,
          SolveFast.group_items(nodup, n,
            Groups.Group{f, w2 <> (w <> Nil{})} <> rg), tail)}
   : SolveFast.ItemsBound}:
  match nodup:
    case True{}:
      +ws2 : +List<+List<Nat>> = w2 <> (w <> Nil{})
      +eclb : {3n == SolveFast.class_lb(ws2) : Nat} =
        FN.class_lb_nodup_eq(ws2, nh)
      +e1 : {SolveFast.group_items_two_step(f, w2, w, ib)
             == SolveFast.ItemsBound{
                  Nat.add(3n, SolveFast.lower_bound(n, rg)),
                  SolveFast.TwoItem{f, w2, w}
                  <> List.append(&2, SolveFast.Item,
                       SolveFast.group_items(True{}, n, rg), tail)}
             : SolveFast.ItemsBound} =
        Equal.cong(SolveFast.ItemsBound, SolveFast.ItemsBound,
          x => SolveFast.group_items_two_step(f, w2, w, x),
          ib,
          SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
            List.append(&2, SolveFast.Item,
              SolveFast.group_items(True{}, n, rg), tail)},
          eib)
      +e2 : {SolveFast.ItemsBound{
               Nat.add(3n, SolveFast.lower_bound(n, rg)),
               SolveFast.TwoItem{f, w2, w}
               <> List.append(&2, SolveFast.Item,
                    SolveFast.group_items(True{}, n, rg), tail)}
             == SolveFast.ItemsBound{
                  Nat.add(SolveFast.class_lb(ws2), SolveFast.lower_bound(n, rg)),
                  SolveFast.TwoItem{f, w2, w}
                  <> List.append(&2, SolveFast.Item,
                       SolveFast.group_items(True{}, n, rg), tail)}
             : SolveFast.ItemsBound} =
        Equal.cong(Nat, SolveFast.ItemsBound,
          c => SolveFast.ItemsBound{
                 Nat.add(c, SolveFast.lower_bound(n, rg)),
                 SolveFast.TwoItem{f, w2, w}
                 <> List.append(&2, SolveFast.Item,
                      SolveFast.group_items(True{}, n, rg), tail)},
          3n, SolveFast.class_lb(ws2), eclb)
      Equal.trans(SolveFast.ItemsBound,
        SolveFast.group_items_two_step(f, w2, w, ib),
        SolveFast.ItemsBound{
          Nat.add(3n, SolveFast.lower_bound(n, rg)),
          SolveFast.TwoItem{f, w2, w}
          <> List.append(&2, SolveFast.Item,
               SolveFast.group_items(True{}, n, rg), tail)},
        SolveFast.ItemsBound{
          SolveFast.lower_bound(n, Groups.Group{f, ws2} <> rg),
          List.append(&2, SolveFast.Item,
            SolveFast.group_items(True{}, n, Groups.Group{f, ws2} <> rg), tail)},
        e1, e2)
    case False{}:
      +ws2 : +List<+List<Nat>> = w2 <> (w <> Nil{})
      +e1 : {SolveFast.group_items_step(f, ws2, len, SolveFast.class_lb(ws2), ib)
             == SolveFast.group_items_step(f, ws2, len, SolveFast.class_lb(ws2),
                  SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                    List.append(&2, SolveFast.Item,
                      SolveFast.group_items(False{}, n, rg), tail)})
             : SolveFast.ItemsBound} =
        Equal.cong(SolveFast.ItemsBound, SolveFast.ItemsBound,
          x => SolveFast.group_items_step(f, ws2, len, SolveFast.class_lb(ws2), x),
          ib,
          SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
            List.append(&2, SolveFast.Item,
              SolveFast.group_items(False{}, n, rg), tail)},
          eib)
      +e2 : {SolveFast.group_items_step(f, ws2, len, SolveFast.class_lb(ws2),
               SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                 List.append(&2, SolveFast.Item,
                   SolveFast.group_items(False{}, n, rg), tail)})
             == SolveFast.group_items_step(f, ws2, 2n, SolveFast.class_lb(ws2),
                  SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                    List.append(&2, SolveFast.Item,
                      SolveFast.group_items(False{}, n, rg), tail)})
             : SolveFast.ItemsBound} =
        Equal.cong(Nat, SolveFast.ItemsBound,
          l => SolveFast.group_items_step(f, ws2, l, SolveFast.class_lb(ws2),
                 SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                   List.append(&2, SolveFast.Item,
                     SolveFast.group_items(False{}, n, rg), tail)}),
          len, 2n, elen)
      Equal.trans(SolveFast.ItemsBound,
        SolveFast.group_items_step(f, ws2, len, SolveFast.class_lb(ws2), ib),
        SolveFast.group_items_step(f, ws2, len, SolveFast.class_lb(ws2),
          SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
            List.append(&2, SolveFast.Item,
              SolveFast.group_items(False{}, n, rg), tail)}),
        SolveFast.group_items_step(f, ws2, 2n, SolveFast.class_lb(ws2),
          SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
            List.append(&2, SolveFast.Item,
              SolveFast.group_items(False{}, n, rg), tail)}),
        e1, e2)

# `fgroup_items_build` matches `lower_bound` and `group_items` on
# `fgroups_to_groups`.
def FN.fgroup_items_build_eq(+nodup: Bool, +n: Nat,
    +fgroups: +List<SolveFast.FGroup>, +tail: +List<SolveFast.Item>,
    +lok: {FN.fgroups_lens_ok(fgroups) == True{} : Bool},
    +ng: {FN.nodup_ok_jobs(nodup,
            MV.MV.next_groups(FN.fgroups_to_groups(fgroups))) == True{} : Bool}) ->
  {SolveFast.fgroup_items_build(nodup, n, fgroups, tail)
   == SolveFast.ItemsBound{
        SolveFast.lower_bound(n, FN.fgroups_to_groups(fgroups)),
        List.append(&2, SolveFast.Item,
          SolveFast.group_items(nodup, n, FN.fgroups_to_groups(fgroups)), tail)}
   : SolveFast.ItemsBound}:
  match fgroups:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{+f, +len, +rws}:
          match rws:
            case Nil{}:
              +lt : {FN.fgroups_lens_ok(rest) == True{} : Bool} =
                Logic.Proof.and_true_r(Nat.is_eq(len, 0n),
                  FN.fgroups_lens_ok(rest), lok)
              +nt : {FN.nodup_ok_jobs(nodup,
                       MV.MV.next_groups(FN.fgroups_to_groups(rest)))
                     == True{} : Bool} =
                Logic.Proof.and_true_r(FN.nodup_ok(nodup, Nil{}),
                  FN.nodup_ok_jobs(nodup,
                    MV.MV.next_groups(FN.fgroups_to_groups(rest))), ng)
              +rg : +List<Groups.Group> = FN.fgroups_to_groups(rest)
              Equal.cong(SolveFast.ItemsBound, SolveFast.ItemsBound,
                ib => SolveFast.group_items_step(f, Nil{}, 0n, 0n, ib),
                SolveFast.fgroup_items_build(nodup, n, rest, tail),
                SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                  List.append(&2, SolveFast.Item,
                    SolveFast.group_items(nodup, n, rg), tail)},
                FN.fgroup_items_build_eq(nodup, n, rest, tail, lt, nt))
            case Con{+w, +wt}:
              match wt:
                case Nil{}:
                  +lt : {FN.fgroups_lens_ok(rest) == True{} : Bool} =
                    Logic.Proof.and_true_r(Nat.is_eq(len, 1n),
                      FN.fgroups_lens_ok(rest), lok)
                  +nt : {FN.nodup_ok_jobs(nodup,
                           MV.MV.next_groups(FN.fgroups_to_groups(rest)))
                         == True{} : Bool} =
                    Logic.Proof.and_true_r(FN.nodup_ok(nodup, w <> Nil{}),
                      FN.nodup_ok_jobs(nodup,
                        MV.MV.next_groups(FN.fgroups_to_groups(rest))), ng)
                  +rg : +List<Groups.Group> = FN.fgroups_to_groups(rest)
                  Equal.cong(SolveFast.ItemsBound, SolveFast.ItemsBound,
                    ib => SolveFast.group_items_one_step(f, w, ib),
                    SolveFast.fgroup_items_build(nodup, n, rest, tail),
                    SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                      List.append(&2, SolveFast.Item,
                        SolveFast.group_items(nodup, n, rg), tail)},
                    FN.fgroup_items_build_eq(nodup, n, rest, tail, lt, nt))
                case Con{+w2, +wt2}:
                  match wt2:
                    case Nil{}:
                      +ws2 : +List<+List<Nat>> = w2 <> (w <> Nil{})
                      +lh : {Nat.is_eq(len, 2n) == True{} : Bool} =
                        Logic.Proof.and_true_l(Nat.is_eq(len, 2n),
                          FN.fgroups_lens_ok(rest), lok)
                      +lt : {FN.fgroups_lens_ok(rest) == True{} : Bool} =
                        Logic.Proof.and_true_r(Nat.is_eq(len, 2n),
                          FN.fgroups_lens_ok(rest), lok)
                      +nh : {FN.nodup_ok(nodup, ws2) == True{} : Bool} =
                        Logic.Proof.and_true_l(FN.nodup_ok(nodup, ws2),
                          FN.nodup_ok_jobs(nodup,
                            MV.MV.next_groups(FN.fgroups_to_groups(rest))), ng)
                      +nt : {FN.nodup_ok_jobs(nodup,
                               MV.MV.next_groups(FN.fgroups_to_groups(rest)))
                             == True{} : Bool} =
                        Logic.Proof.and_true_r(FN.nodup_ok(nodup, ws2),
                          FN.nodup_ok_jobs(nodup,
                            MV.MV.next_groups(FN.fgroups_to_groups(rest))), ng)
                      +elen : {len == 2n : Nat} =
                        NatProof.NatPrf.is_eq_true(len, 2n, lh)
                      +rg : +List<Groups.Group> = FN.fgroups_to_groups(rest)
                      +ih : {SolveFast.fgroup_items_build(nodup, n, rest, tail)
                             == SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                                  List.append(&2, SolveFast.Item,
                                    SolveFast.group_items(nodup, n, rg), tail)}
                             : SolveFast.ItemsBound} =
                        FN.fgroup_items_build_eq(nodup, n, rest, tail, lt, nt)
                      FN.fgroup_items_two_eq(nodup, n, f, len, w, w2, rg, tail,
                        SolveFast.fgroup_items_build(nodup, n, rest, tail),
                        ih, elen, nh)
                    case Con{+w3, +wt3}:
                      +rws3 : +List<+List<Nat>> = w <> (w2 <> (w3 <> wt3))
                      +ws3 : +List<+List<Nat>> =
                        SolveFast.rev_words(wt3, w3 <> (w2 <> (w <> Nil{})))
                      +lh : {Nat.is_eq(len, Groups.len_words(rws3))
                             == True{} : Bool} =
                        Logic.Proof.and_true_l(
                          Nat.is_eq(len, Groups.len_words(rws3)),
                          FN.fgroups_lens_ok(rest), lok)
                      +lt : {FN.fgroups_lens_ok(rest) == True{} : Bool} =
                        Logic.Proof.and_true_r(
                          Nat.is_eq(len, Groups.len_words(rws3)),
                          FN.fgroups_lens_ok(rest), lok)
                      +nh : {FN.nodup_ok(nodup, ws3) == True{} : Bool} =
                        Logic.Proof.and_true_l(FN.nodup_ok(nodup, ws3),
                          FN.nodup_ok_jobs(nodup,
                            MV.MV.next_groups(FN.fgroups_to_groups(rest))), ng)
                      +nt : {FN.nodup_ok_jobs(nodup,
                               MV.MV.next_groups(FN.fgroups_to_groups(rest)))
                             == True{} : Bool} =
                        Logic.Proof.and_true_r(FN.nodup_ok(nodup, ws3),
                          FN.nodup_ok_jobs(nodup,
                            MV.MV.next_groups(FN.fgroups_to_groups(rest))), ng)
                      +elen : {len == Groups.len_words(ws3) : Nat} =
                        Equal.trans(Nat, len, Groups.len_words(rws3),
                          Groups.len_words(ws3),
                          NatProof.NatPrf.is_eq_true(len, Groups.len_words(rws3),
                            lh),
                          Equal.sym(Nat, Groups.len_words(ws3),
                            Groups.len_words(rws3), FN.len_rev_nil(rws3)))
                      +rg : +List<Groups.Group> = FN.fgroups_to_groups(rest)
                      +ih : {SolveFast.fgroup_items_build(nodup, n, rest, tail)
                             == SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                                  List.append(&2, SolveFast.Item,
                                    SolveFast.group_items(nodup, n, rg), tail)}
                             : SolveFast.ItemsBound} =
                        FN.fgroup_items_build_eq(nodup, n, rest, tail, lt, nt)
                      +eclb : {SolveFast.class_lb_fast(nodup, len, ws3)
                               == SolveFast.class_lb(ws3) : Nat} =
                        FN.class_lb_fast_eq(nodup, len, ws3, elen, nh)
                      +e1 : {SolveFast.group_items_step(f, ws3, len,
                               SolveFast.class_lb_fast(nodup, len, ws3),
                               SolveFast.fgroup_items_build(nodup, n, rest, tail))
                             == SolveFast.group_items_step(f, ws3, len,
                                  SolveFast.class_lb_fast(nodup, len, ws3),
                                  SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                                    List.append(&2, SolveFast.Item,
                                      SolveFast.group_items(nodup, n, rg), tail)})
                             : SolveFast.ItemsBound} =
                        Equal.cong(SolveFast.ItemsBound, SolveFast.ItemsBound,
                          ib => SolveFast.group_items_step(f, ws3, len,
                                  SolveFast.class_lb_fast(nodup, len, ws3), ib),
                          SolveFast.fgroup_items_build(nodup, n, rest, tail),
                          SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                            List.append(&2, SolveFast.Item,
                              SolveFast.group_items(nodup, n, rg), tail)},
                          ih)
                      +e2 : {SolveFast.group_items_step(f, ws3, len,
                               SolveFast.class_lb_fast(nodup, len, ws3),
                               SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                                 List.append(&2, SolveFast.Item,
                                   SolveFast.group_items(nodup, n, rg), tail)})
                             == SolveFast.group_items_step(f, ws3,
                                  Groups.len_words(ws3), SolveFast.class_lb(ws3),
                                  SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                                    List.append(&2, SolveFast.Item,
                                      SolveFast.group_items(nodup, n, rg), tail)})
                             : SolveFast.ItemsBound} =
                        Equal.trans(SolveFast.ItemsBound,
                          SolveFast.group_items_step(f, ws3, len,
                            SolveFast.class_lb_fast(nodup, len, ws3),
                            SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                              List.append(&2, SolveFast.Item,
                                SolveFast.group_items(nodup, n, rg), tail)}),
                          SolveFast.group_items_step(f, ws3, Groups.len_words(ws3),
                            SolveFast.class_lb_fast(nodup, len, ws3),
                            SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                              List.append(&2, SolveFast.Item,
                                SolveFast.group_items(nodup, n, rg), tail)}),
                          SolveFast.group_items_step(f, ws3, Groups.len_words(ws3),
                            SolveFast.class_lb(ws3),
                            SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                              List.append(&2, SolveFast.Item,
                                SolveFast.group_items(nodup, n, rg), tail)}),
                          Equal.cong(Nat, SolveFast.ItemsBound,
                            l => SolveFast.group_items_step(f, ws3, l,
                                   SolveFast.class_lb_fast(nodup, len, ws3),
                                   SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                                     List.append(&2, SolveFast.Item,
                                       SolveFast.group_items(nodup, n, rg), tail)}),
                            len, Groups.len_words(ws3), elen),
                          Equal.cong(Nat, SolveFast.ItemsBound,
                            c => SolveFast.group_items_step(f, ws3,
                                   Groups.len_words(ws3), c,
                                   SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                                     List.append(&2, SolveFast.Item,
                                       SolveFast.group_items(nodup, n, rg), tail)}),
                            SolveFast.class_lb_fast(nodup, len, ws3),
                            SolveFast.class_lb(ws3), eclb))
                      +ek : {Groups.len_words(ws3)
                             == Nat.add(3n, Groups.len_words(wt3)) : Nat} =
                        FN.len_rev_nil(rws3)
                      +egi : {SolveFast.group_items(nodup, n, Groups.Group{f, ws3} <> rg)
                              == SolveFast.ClassItem{f, ws3, Groups.len_words(ws3),
                                   SolveFast.lower_bound(n, rg)}
                                 <> (SolveFast.Add{f, SolveFast.lower_bound(n, rg)}
                                     <> SolveFast.group_items(nodup, n, rg))
                              : +List<SolveFast.Item>} =
                        FN.group_items_ge3_eq(nodup, n, f, ws3, rg,
                          Groups.len_words(wt3), ek)
                      +e3 : {SolveFast.ItemsBound{
                               SolveFast.lower_bound(n, Groups.Group{f, ws3} <> rg),
                               SolveFast.ClassItem{f, ws3, Groups.len_words(ws3),
                                 SolveFast.lower_bound(n, rg)}
                               <> (SolveFast.Add{f, SolveFast.lower_bound(n, rg)}
                                   <> List.append(&2, SolveFast.Item,
                                        SolveFast.group_items(nodup, n, rg), tail))}
                             == SolveFast.ItemsBound{
                                  SolveFast.lower_bound(n,
                                    Groups.Group{f, ws3} <> rg),
                                  List.append(&2, SolveFast.Item,
                                    SolveFast.group_items(nodup, n,
                                      Groups.Group{f, ws3} <> rg), tail)}
                             : SolveFast.ItemsBound} =
                        Equal.cong(+List<SolveFast.Item>, SolveFast.ItemsBound,
                          its => SolveFast.ItemsBound{
                                   SolveFast.lower_bound(n,
                                     Groups.Group{f, ws3} <> rg),
                                   List.append(&2, SolveFast.Item, its, tail)},
                          SolveFast.ClassItem{f, ws3, Groups.len_words(ws3),
                            SolveFast.lower_bound(n, rg)}
                          <> (SolveFast.Add{f, SolveFast.lower_bound(n, rg)}
                              <> SolveFast.group_items(nodup, n, rg)),
                          SolveFast.group_items(nodup, n, Groups.Group{f, ws3} <> rg),
                          Equal.sym(+List<SolveFast.Item>,
                            SolveFast.group_items(nodup, n, Groups.Group{f, ws3} <> rg),
                            SolveFast.ClassItem{f, ws3, Groups.len_words(ws3),
                              SolveFast.lower_bound(n, rg)}
                            <> (SolveFast.Add{f, SolveFast.lower_bound(n, rg)}
                                <> SolveFast.group_items(nodup, n, rg)),
                            egi))
                      Equal.trans(SolveFast.ItemsBound,
                        SolveFast.group_items_step(f, ws3, len,
                          SolveFast.class_lb_fast(nodup, len, ws3),
                          SolveFast.fgroup_items_build(nodup, n, rest, tail)),
                        SolveFast.group_items_step(f, ws3, Groups.len_words(ws3),
                          SolveFast.class_lb(ws3),
                          SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                            List.append(&2, SolveFast.Item,
                              SolveFast.group_items(nodup, n, rg), tail)}),
                        SolveFast.ItemsBound{
                          SolveFast.lower_bound(n, Groups.Group{f, ws3} <> rg),
                          List.append(&2, SolveFast.Item,
                            SolveFast.group_items(nodup, n, Groups.Group{f, ws3} <> rg),
                            tail)},
                        Equal.trans(SolveFast.ItemsBound,
                          SolveFast.group_items_step(f, ws3, len,
                            SolveFast.class_lb_fast(nodup, len, ws3),
                            SolveFast.fgroup_items_build(nodup, n, rest, tail)),
                          SolveFast.group_items_step(f, ws3, len,
                            SolveFast.class_lb_fast(nodup, len, ws3),
                            SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                              List.append(&2, SolveFast.Item,
                                SolveFast.group_items(nodup, n, rg), tail)}),
                          SolveFast.group_items_step(f, ws3, Groups.len_words(ws3),
                            SolveFast.class_lb(ws3),
                            SolveFast.ItemsBound{SolveFast.lower_bound(n, rg),
                              List.append(&2, SolveFast.Item,
                                SolveFast.group_items(nodup, n, rg), tail)}),
                          e1, e2),
                        e3)
