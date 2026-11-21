# O(1) singleton leaf resolution and root candidate-membership check.
#
# A valid decision tree over `(G, C)` must reach every candidate in `C` using
# only guesses from `G`, so every candidate in `C` must occur in `G`. If
# `all_in_fast(C, G)` is false, no valid tree exists and `SolveRef.solve(G, C)`
# is `None{}`. If `all_in_fast(C, G)` is true, every candidate class `S` built
# by `groups_build` is a subsequence of its parent (`cover_groups.bend`) and
# therefore also has every word in `G`. For any singleton class `[w]` with
# `w in G`, positive fuel `p >= 1` and `1 < inf`, the reference search
# `FS.ref_run_at(p, inf, G, [w])` equals `SolveRef.Best{Tree.Node{w, Nil{}}, 1n}`.
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
import ./optfold.bend as Fold
import ./optimalvalue.bend as OV
import ./mainvalid.bend as MV
import ./lb_twice.bend as LBProof2
import ./cover_list.bend as CoverList
import ./cover_groups.bend as CoverGroups
import ./fast_step.bend as FStep
import ./fast_groups.bend as FG
import ./fast_better.bend as FB

# Reference conjunction checking that every word of `S` occurs in `G`.
def FO.all_in_ref(+S: +List<+List<Nat>>, +G: +List<+List<Nat>>) -> Bool:
  match S:
    case Nil{}:
      True{}
    case Con{w, t}:
      Bool.and(Tree.member_word(w, G), FO.all_in_ref(t, G))

def FO.AllIn(+S: +List<+List<Nat>>, +G: +List<+List<Nat>>) -> Type:
  {FO.all_in_ref(S, G) == True{} : Bool}

# `member_word_go` agrees with `Tree.member_word`.
def FO.member_word_go_eq(+w: +List<Nat>, +gs: +List<+List<Nat>>, hit: Bool,
    +eh: {hit == SolveFast.next_word_hit(w, gs) : Bool}) ->
  {SolveFast.member_word_go(w, gs, hit) == Tree.member_word(w, gs) : Bool}:
  match gs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      match hit:
        case True{}:
          +eh_ref : {True{} == Feedback.word_eq(w, h) : Bool} =
            Equal.trans(Bool, True{},
              SolveFast.word_eq_fast(w, h), Feedback.word_eq(w, h),
              eh, FG.FG.word_eq_fast_eq(w, h))
          Equal.cong(Bool, Bool,
            b => Feedback.Bool.case(Bool, b, True{}, Tree.member_word(w, t)),
            True{}, Feedback.word_eq(w, h), eh_ref)
        case False{}:
          +eh_ref : {False{} == Feedback.word_eq(w, h) : Bool} =
            Equal.trans(Bool, False{},
              SolveFast.word_eq_fast(w, h), Feedback.word_eq(w, h),
              eh, FG.FG.word_eq_fast_eq(w, h))
          +e1 : {SolveFast.member_word_go(w, t, SolveFast.next_word_hit(w, t))
                 == Tree.member_word(w, t) : Bool} =
            FO.member_word_go_eq(w, t, SolveFast.next_word_hit(w, t), {==})
          +e2 : {Tree.member_word(w, t)
                 == Feedback.Bool.case(Bool, Feedback.word_eq(w, h), True{},
                      Tree.member_word(w, t)) : Bool} =
            Equal.cong(Bool, Bool,
              b => Feedback.Bool.case(Bool, b, True{}, Tree.member_word(w, t)),
              False{}, Feedback.word_eq(w, h), eh_ref)
          Equal.trans(Bool,
            SolveFast.member_word_go(w, t, SolveFast.next_word_hit(w, t)),
            Tree.member_word(w, t),
            Tree.member_word(w, h <> t),
            e1, e2)

def FO.member_word_fast_eq(+w: +List<Nat>, +gs: +List<+List<Nat>>) ->
  {SolveFast.member_word_fast(w, gs) == Tree.member_word(w, gs) : Bool}:
  FO.member_word_go_eq(w, gs, SolveFast.next_word_hit(w, gs), {==})

# `all_in_go` agrees with `FO.all_in_ref`.
def FO.all_in_go_eq(+S: +List<+List<Nat>>, +G: +List<+List<Nat>>, ok: Bool,
    +eok: {ok == SolveFast.next_in(S, G) : Bool}) ->
  {SolveFast.all_in_go(S, G, ok) == FO.all_in_ref(S, G) : Bool}:
  match S:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      match ok:
        case True{}:
          +ew : {True{} == Tree.member_word(w, G) : Bool} =
            Equal.trans(Bool, True{},
              SolveFast.member_word_fast(w, G), Tree.member_word(w, G),
              eok, FO.member_word_fast_eq(w, G))
          +e1 : {SolveFast.all_in_go(t, G, SolveFast.next_in(t, G))
                 == FO.all_in_ref(t, G) : Bool} =
            FO.all_in_go_eq(t, G, SolveFast.next_in(t, G), {==})
          +e2 : {FO.all_in_ref(t, G)
                 == Bool.and(Tree.member_word(w, G), FO.all_in_ref(t, G))
                 : Bool} =
            Equal.cong(Bool, Bool, b => Bool.and(b, FO.all_in_ref(t, G)),
              True{}, Tree.member_word(w, G), ew)
          Equal.trans(Bool,
            SolveFast.all_in_go(t, G, SolveFast.next_in(t, G)),
            FO.all_in_ref(t, G),
            FO.all_in_ref(w <> t, G),
            e1, e2)
        case False{}:
          +ew : {False{} == Tree.member_word(w, G) : Bool} =
            Equal.trans(Bool, False{},
              SolveFast.member_word_fast(w, G), Tree.member_word(w, G),
              eok, FO.member_word_fast_eq(w, G))
          Equal.cong(Bool, Bool, b => Bool.and(b, FO.all_in_ref(t, G)),
            False{}, Tree.member_word(w, G), ew)

def FO.all_in_fast_eq(+S: +List<+List<Nat>>, +G: +List<+List<Nat>>) ->
  {SolveFast.all_in_fast(S, G) == FO.all_in_ref(S, G) : Bool}:
  FO.all_in_go_eq(S, G, SolveFast.next_in(S, G), {==})

# Symmetry of `Feedback.word_eq` for false results.
def FO.word_eq_sym_false_go(+w: +List<Nat>, +g: +List<Nat>,
    +e: {Feedback.word_eq(w, g) == False{} : Bool}, b: Bool,
    +eb: {b == Feedback.word_eq(g, w) : Bool}) ->
  {Feedback.word_eq(g, w) == False{} : Bool}:
  match b:
    case False{}:
      Equal.sym(Bool, False{}, Feedback.word_eq(g, w), eb)
    case True{}:
      +egw : {Feedback.word_eq(g, w) == True{} : Bool} =
        Equal.sym(Bool, True{}, Feedback.word_eq(g, w), eb)
      +eq : {g == w : +List<Nat>} = CoverList.Cover.word_eq_true(g, w, egw)
      +ewg : {Feedback.word_eq(w, g) == True{} : Bool} =
        Equal.trans(Bool, Feedback.word_eq(w, g), Feedback.word_eq(w, w),
          True{},
          Equal.cong(+List<Nat>, Bool, x => Feedback.word_eq(w, x), g, w, eq),
          FbProof.FbPrf.word_eq_refl(w))
      Empty.absurd({Feedback.word_eq(g, w) == False{} : Bool},
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, Feedback.word_eq(w, g), False{},
            Equal.sym(Bool, Feedback.word_eq(w, g), True{}, ewg), e)))

def FO.word_eq_sym_false(+w: +List<Nat>, +g: +List<Nat>,
    +e: {Feedback.word_eq(w, g) == False{} : Bool}) ->
  {Feedback.word_eq(g, w) == False{} : Bool}:
  FO.word_eq_sym_false_go(w, g, e, Feedback.word_eq(g, w), {==})

# Strip `Tree.depth.bump` from a `Maybe.is_some` hypothesis.
def FO.is_some_of_bump(m: Maybe<Nat>,
    +s: {Maybe.is_some(&1, Nat, Tree.depth.bump(m)) == True{} : Bool}) ->
  {Maybe.is_some(&1, Nat, m) == True{} : Bool}:
  Equal.trans(Bool,
    Maybe.is_some(&1, Nat, m),
    Maybe.is_some(&1, Nat, Tree.depth.bump(m)),
    True{},
    Equal.sym(Bool,
      Maybe.is_some(&1, Nat, Tree.depth.bump(m)),
      Maybe.is_some(&1, Nat, m),
      LBProof2.LB.is_some_bump(m)),
    s)

# One step of extracting `Tree.WordIn(a, G)` from `Tree.depth.go`.
def FO.word_in_of_depth_step(+G: +List<+List<Nat>>, +a: +List<Nat>,
    +g: +List<Nat>, +f: +List<Feedback.Color>, +fb: +List<Feedback.Color>,
    +ckids: +List<Tree.Child>, +rest: +List<Tree.Child>,
    bfb: Bool, +ebfb: {bfb == Feedback.feedback_eq(f, fb) : Bool},
    bw: Bool, +ebw: {bw == Feedback.word_eq(g, a) : Bool},
    wg: Tree.WordIn(g, G),
    k1: {Maybe.is_some(&1, Nat, Tree.depth.go(ckids, Feedback.feedback(g, a), a))
         == True{} : Bool} -> Tree.WordIn(a, G),
    k2: {Maybe.is_some(&1, Nat, Tree.depth.go(rest, fb, a)) == True{} : Bool}
        -> Tree.WordIn(a, G),
    +sd: {Maybe.is_some(&1, Nat,
            Feedback.Bool.case(Maybe<Nat>, bfb,
              Feedback.Bool.case(Maybe<Nat>, bw, Some{1n},
                Tree.depth.bump(Tree.depth.go(ckids, Feedback.feedback(g, a), a))),
              Tree.depth.go(rest, fb, a))) == True{} : Bool}) ->
  Tree.WordIn(a, G):
  match bfb:
    case True{}:
      match bw:
        case True{}:
          +eg : {g == a : +List<Nat>} =
            CoverList.Cover.word_eq_true(g, a,
              Equal.sym(Bool, True{}, Feedback.word_eq(g, a), ebw))
          %eg : Tree.WordIn(_, G)
          wg
        case False{}:
          k1(FO.is_some_of_bump(
               Tree.depth.go(ckids, Feedback.feedback(g, a), a), sd))
    case False{}:
      k2(sd)

# If `Tree.depth.go` reaches `a` inside a tree whose guesses are in `G`, then
# `a` itself is in `G`.
def FO.word_in_of_depth_go(+kids: +List<Tree.Child>, +G: +List<+List<Nat>>,
    +fb: +List<Feedback.Color>, +a: +List<Nat>,
    ki: Tree.KidsIn(kids, G),
    +sd: {Maybe.is_some(&1, Nat, Tree.depth.go(kids, fb, a)) == True{} : Bool}) ->
  Tree.WordIn(a, G):
  match kids:
    case Nil{}:
      Empty.absurd(Tree.WordIn(a, G), Logic.Proof.false_ne_true(sd))
    case Con{+c, +rest}:
      match c:
        case Tree.Child{+f, +child}:
          match child:
            case Tree.Node{+g, +ckids}:
              (ti_c, ki_r) = ki
              (wg, ki_c) = ti_c
              FO.word_in_of_depth_step(G, a, g, f, fb, ckids, rest,
                Feedback.feedback_eq(f, fb), {==},
                Feedback.word_eq(g, a), {==}, wg,
                s1 => FO.word_in_of_depth_go(ckids, G, Feedback.feedback(g, a),
                        a, ki_c, s1),
                s2 => FO.word_in_of_depth_go(rest, G, fb, a, ki_r, s2),
                sd)

def FO.word_in_of_depth_node(+G: +List<+List<Nat>>, +a: +List<Nat>,
    +g: +List<Nat>, +kids: +List<Tree.Child>,
    bw: Bool, +ebw: {bw == Feedback.word_eq(g, a) : Bool},
    wg: Tree.WordIn(g, G), ki: Tree.KidsIn(kids, G),
    +sd: {Maybe.is_some(&1, Nat,
            Feedback.Bool.case(Maybe<Nat>, bw, Some{1n},
              Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, a), a))))
          == True{} : Bool}) ->
  Tree.WordIn(a, G):
  match bw:
    case True{}:
      +eg : {g == a : +List<Nat>} =
        CoverList.Cover.word_eq_true(g, a,
          Equal.sym(Bool, True{}, Feedback.word_eq(g, a), ebw))
      %eg : Tree.WordIn(_, G)
      wg
    case False{}:
      FO.word_in_of_depth_go(kids, G, Feedback.feedback(g, a), a, ki,
        FO.is_some_of_bump(Tree.depth.go(kids, Feedback.feedback(g, a), a), sd))

# Any candidate reached by a tree with guesses in `G` belongs to `G`.
def FO.word_in_of_depth(+T: Tree.Tree, +G: +List<+List<Nat>>, +a: +List<Nat>,
    ti: Tree.TreeIn(T, G),
    +sd: {Maybe.is_some(&1, Nat, Tree.depth(T, a)) == True{} : Bool}) ->
  Tree.WordIn(a, G):
  match T:
    case Tree.Node{+g, +kids}:
      (wg, ki) = ti
      FO.word_in_of_depth_node(G, a, g, kids,
        Feedback.word_eq(g, a), {==}, wg, ki, sd)

# If `all_in_ref(C, G)` is false, no tree is valid for `(G, C)`.
def FO.no_valid_step(+G: +List<+List<Nat>>, +h: +List<Nat>,
    +t: +List<+List<Nat>>, +T: Tree.Tree,
    ti: Tree.TreeIn(T, G),
    +sh: {Maybe.is_some(&1, Nat, Tree.depth(T, h)) == True{} : Bool},
    st: Tree.AllHaveDepth(T, t),
    b: Bool, +eb: {b == Tree.member_word(h, G) : Bool},
    +ef: {Bool.and(Tree.member_word(h, G), FO.all_in_ref(t, G))
          == False{} : Bool},
    rec: Tree.TreeIn(T, G) -> Tree.AllHaveDepth(T, t) ->
         {FO.all_in_ref(t, G) == False{} : Bool} -> Empty) ->
  Empty:
  match b:
    case False{}:
      +hm : {Tree.member_word(h, G) == False{} : Bool} =
        Equal.sym(Bool, False{}, Tree.member_word(h, G), eb)
      +wt : {Tree.member_word(h, G) == True{} : Bool} =
        FO.word_in_of_depth(T, G, h, ti, sh)
      Logic.Proof.true_ne_false(
        Equal.trans(Bool, True{}, Tree.member_word(h, G), False{},
          Equal.sym(Bool, Tree.member_word(h, G), True{}, wt), hm))
    case True{}:
      +ef_t : {FO.all_in_ref(t, G) == False{} : Bool} =
        Equal.trans(Bool,
          FO.all_in_ref(t, G),
          Bool.and(Tree.member_word(h, G), FO.all_in_ref(t, G)),
          False{},
          Equal.cong(Bool, Bool, x => Bool.and(x, FO.all_in_ref(t, G)),
            True{}, Tree.member_word(h, G), eb),
          ef)
      rec(ti, st, ef_t)

def FO.no_valid_of_all_in_false(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +T: Tree.Tree, ti: Tree.TreeIn(T, G), ahd: Tree.AllHaveDepth(T, C),
    +ef: {FO.all_in_ref(C, G) == False{} : Bool}) -> Empty:
  match C:
    case Nil{}:
      Logic.Proof.true_ne_false(ef)
    case Con{+h, +t}:
      (+sh, st) = ahd
      FO.no_valid_step(G, h, t, T, ti, sh, st,
        Tree.member_word(h, G), {==}, ef,
        ti2 => st2 => ef2 => FO.no_valid_of_all_in_false(G, t, T, ti2, st2, ef2))

def FO.no_valid_of_valid(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    +T: Tree.Tree, v: Tree.Valid(T, G, C),
    +ef: {FO.all_in_ref(C, G) == False{} : Bool}) -> Empty:
  (ti, ahd) = v
  FO.no_valid_of_all_in_false(G, C, T, ti, ahd, ef)

def FO.none_of_solve_valid(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
    m: Maybe<Tree.Tree>, +em: {SolveRef.solve(G, C) == m : Maybe<Tree.Tree>},
    +ef: {FO.all_in_ref(C, G) == False{} : Bool}) ->
  {None{} == m : Maybe<Tree.Tree>}:
  match m:
    case None{}:
      {==}
    case Some{+T}:
      Empty.absurd({None{} == Some{T} : Maybe<Tree.Tree>},
        FO.no_valid_of_valid(G, C, T, MV.MV.solve_valid(G, C, T, em), ef))

# When `all_in_ref(C, G)` is false, `SolveRef.solve(G, C)` returns `None{}`.
def FO.solve_ref_none_of_all_in_false(+G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>,
    +ef: {FO.all_in_ref(C, G) == False{} : Bool}) ->
  {None{} == SolveRef.solve(G, C) : Maybe<Tree.Tree>}:
  FO.none_of_solve_valid(G, C, SolveRef.solve(G, C), {==}, ef)

# `FO.all_in_ref` helpers and preservation through `groups_build` and `next_jobs`.
def FO.all_in_head(+w: +List<Nat>, +t: +List<+List<Nat>>,
    +G: +List<+List<Nat>>,
    +ai: {FO.all_in_ref(w <> t, G) == True{} : Bool}) ->
  {Tree.member_word(w, G) == True{} : Bool}:
  Logic.Proof.and_true_l(Tree.member_word(w, G), FO.all_in_ref(t, G), ai)

def FO.all_in_tail(+w: +List<Nat>, +t: +List<+List<Nat>>,
    +G: +List<+List<Nat>>,
    +ai: {FO.all_in_ref(w <> t, G) == True{} : Bool}) ->
  {FO.all_in_ref(t, G) == True{} : Bool}:
  Logic.Proof.and_true_r(Tree.member_word(w, G), FO.all_in_ref(t, G), ai)

def FO.bool_and_intro(a: Bool, b: Bool,
    +ea: {a == True{} : Bool}, +eb: {b == True{} : Bool}) ->
  {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool},
        Logic.Proof.false_ne_true(ea))

def FO.all_in_of_subseq(+ws: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, sub: CoverList.Cover.Subseq(ws, S),
    +ai: {FO.all_in_ref(S, G) == True{} : Bool}) ->
  {FO.all_in_ref(ws, G) == True{} : Bool}:
  match ws S:
    case Nil{} _:
      {==}
    case Con{h, t} Nil{}:
      match sub:
    case Con{+h, +t} Con{+y, +r}:
      match sub:
        case Inl{q}:
          (+e, sub_t) = q
          +wy : {Tree.member_word(y, G) == True{} : Bool} =
            FO.all_in_head(y, r, G, ai)
          +wh : {Tree.member_word(h, G) == True{} : Bool} =
            Equal.trans(Bool, Tree.member_word(h, G), Tree.member_word(y, G),
              True{},
              Equal.cong(+List<Nat>, Bool, x => Tree.member_word(x, G), h, y, e),
              wy)
          +ait : {FO.all_in_ref(t, G) == True{} : Bool} =
            FO.all_in_of_subseq(t, r, G, sub_t, FO.all_in_tail(y, r, G, ai))
          FO.bool_and_intro(Tree.member_word(h, G), FO.all_in_ref(t, G),
            wh, ait)
        case Inr{sub_r}:
          FO.all_in_of_subseq(h <> t, r, G, sub_r, FO.all_in_tail(y, r, G, ai))

# Every job in a job list has all candidates in `G` (represented as a `Bool`
# equality so it is `Data` and copies freely).
def FO.all_in_jobs_b(+jobs: +List<+List<+List<Nat>>>,
    +G: +List<+List<Nat>>) -> Bool:
  match jobs:
    case Nil{}:
      True{}
    case Con{S, t}:
      Bool.and(FO.all_in_ref(S, G), FO.all_in_jobs_b(t, G))

def FO.all_in_jobs_append(+xs: +List<+List<+List<Nat>>>,
    +ys: +List<+List<+List<Nat>>>, +G: +List<+List<Nat>>,
    +ax: {FO.all_in_jobs_b(xs, G) == True{} : Bool},
    +ay: {FO.all_in_jobs_b(ys, G) == True{} : Bool}) ->
  {FO.all_in_jobs_b(List.append(&2, +List<+List<Nat>>, xs, ys), G)
   == True{} : Bool}:
  match xs:
    case Nil{}:
      ay
    case Con{+S, +t}:
      +ah : {FO.all_in_ref(S, G) == True{} : Bool} =
        Logic.Proof.and_true_l(FO.all_in_ref(S, G), FO.all_in_jobs_b(t, G), ax)
      +at : {FO.all_in_jobs_b(t, G) == True{} : Bool} =
        Logic.Proof.and_true_r(FO.all_in_ref(S, G), FO.all_in_jobs_b(t, G), ax)
      FO.bool_and_intro(FO.all_in_ref(S, G),
        FO.all_in_jobs_b(List.append(&2, +List<+List<Nat>>, t, ys), G),
        ah, FO.all_in_jobs_append(t, ys, G, at, ay))

def FO.all_in_next_groups(+groups: +List<Groups.Group>,
    +S: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    allsub: CoverGroups.Cover.AllSubseq(groups, S),
    +ai: {FO.all_in_ref(S, G) == True{} : Bool}) ->
  {FO.all_in_jobs_b(MV.MV.next_groups(groups), G) == True{} : Bool}:
  match groups:
    case Nil{}:
      {==}
    case Con{+gp, +rest}:
      match gp:
        case Groups.Group{+fb, +ws}:
          (sub, subt) = allsub
          FO.bool_and_intro(FO.all_in_ref(ws, G),
            FO.all_in_jobs_b(MV.MV.next_groups(rest), G),
            FO.all_in_of_subseq(ws, S, G, sub, ai),
            FO.all_in_next_groups(rest, S, G, subt, ai))

def FO.all_in_classes_b(b: Bool, +groups: +List<Groups.Group>,
    +S: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    allsub: CoverGroups.Cover.AllSubseq(groups, S),
    +ai: {FO.all_in_ref(S, G) == True{} : Bool}) ->
  {FO.all_in_jobs_b(MV.MV.classes_b(b, groups), G) == True{} : Bool}:
  match b:
    case True{}:
      FO.all_in_next_groups(groups, S, G, allsub, ai)
    case False{}:
      {==}

def FO.all_in_next_guess(+gs: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +G: +List<+List<Nat>>, +ai: {FO.all_in_ref(S, G) == True{} : Bool}) ->
  {FO.all_in_jobs_b(MV.MV.next_guess(gs, S), G) == True{} : Bool}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      +groups : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
      FO.all_in_jobs_append(MV.MV.classes(g, S), MV.MV.next_guess(t, S), G,
        FO.all_in_classes_b(Groups.groups_smaller(S, groups), groups, S, G,
          CoverGroups.Cover.all_subseq_nil(g, S), ai),
        FO.all_in_next_guess(t, S, G, ai))

def FO.all_in_next_jobs(+G: +List<+List<Nat>>, +jobs: +List<+List<+List<Nat>>>,
    +aj: {FO.all_in_jobs_b(jobs, G) == True{} : Bool}) ->
  {FO.all_in_jobs_b(MV.MV.next_jobs(G, jobs), G) == True{} : Bool}:
  match jobs:
    case Nil{}:
      {==}
    case Con{+S, +t}:
      +ai : {FO.all_in_ref(S, G) == True{} : Bool} =
        Logic.Proof.and_true_l(FO.all_in_ref(S, G), FO.all_in_jobs_b(t, G), aj)
      +at : {FO.all_in_jobs_b(t, G) == True{} : Bool} =
        Logic.Proof.and_true_r(FO.all_in_ref(S, G), FO.all_in_jobs_b(t, G), aj)
      FO.all_in_jobs_append(MV.MV.next_guess(G, S), MV.MV.next_jobs(G, t), G,
        FO.all_in_next_guess(G, S, G, ai),
        FO.all_in_next_jobs(G, t, at))

# Evaluating one guess on a singleton candidate list `[w]`.
def FO.eval_guess_one(+p: Nat, +G: +List<+List<Nat>>, +w: +List<Nat>,
    +g: +List<Nat>, +inf: Nat, +best: SolveRef.Best, same: Bool) ->
  {Eval.Eval.guess_bool(p, G, w <> Nil{}, g,
     Feedback.Bool.case(+List<Groups.Group>, same, Nil{},
       Groups.Group{Feedback.feedback(g, w), w <> Nil{}} <> Nil{}),
     inf,
     Groups.groups_smaller(w <> Nil{},
       Feedback.Bool.case(+List<Groups.Group>, same, Nil{},
         Groups.Group{Feedback.feedback(g, w), w <> Nil{}} <> Nil{})),
     best)
   == Feedback.Bool.case(SolveRef.Best, same,
        SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, best),
        best)
   : SolveRef.Best}:
  match same:
    case True{}:
      {==}
    case False{}:
      {==}

# When `1 < inf`, `sat_add(inf, 1n, 0n) = 1n`.
def FO.sat_add_one_zero(+inf: Nat, +h1: {Nat.is_lt(1n, inf) == True{} : Bool}) ->
  {SolveRef.sat_add(inf, 1n, 0n) == 1n : Nat}:
  +hz : {Nat.is_lt(0n, inf) == True{} : Bool} =
    NatProof.Nat.is_le_lt_trans(0n, 1n, inf, {==}, h1)
  OV.OV.sat_fin(inf, 1n, 0n,
    OV.OV.ge_false_of_lt(1n, inf, h1),
    OV.OV.ge_false_of_lt(0n, inf, hz))

# Finishing guess `w` on `[w]` from `dummy_inf(inf)` yields `Best{Node{w, []}, 1}`.
def FO.finish_one_eq(+inf: Nat, +w: +List<Nat>,
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool}) ->
  {SolveRef.finish_guess(inf, w, Nil{}, 0n, 1n, Eval.Eval.dummy_inf(inf))
   == SolveRef.Best{Tree.Node{w, Nil{}}, 1n} : SolveRef.Best}:
  +s1 : {SolveRef.sat_add(inf, 1n, 0n) == 1n : Nat} =
    FO.sat_add_one_zero(inf, h1)
  +e1 : {SolveRef.better(SolveRef.sat_add(inf, 1n, 0n), Tree.Node{w, Nil{}},
           Eval.Eval.dummy_inf(inf))
         == SolveRef.better(1n, Tree.Node{w, Nil{}}, Eval.Eval.dummy_inf(inf))
         : SolveRef.Best} =
    Equal.cong(Nat, SolveRef.Best,
      c => SolveRef.better(c, Tree.Node{w, Nil{}}, Eval.Eval.dummy_inf(inf)),
      SolveRef.sat_add(inf, 1n, 0n), 1n, s1)
  +e2 : {SolveRef.better(1n, Tree.Node{w, Nil{}}, Eval.Eval.dummy_inf(inf))
         == SolveRef.Best{Tree.Node{w, Nil{}}, 1n} : SolveRef.Best} =
    Equal.cong(Bool, SolveRef.Best,
      b => Feedback.Bool.case(SolveRef.Best, b,
             SolveRef.Best{Tree.Node{w, Nil{}}, 1n},
             Eval.Eval.dummy_inf(inf)),
      Nat.is_lt(1n, inf), True{}, h1)
  Equal.trans(SolveRef.Best,
    SolveRef.finish_guess(inf, w, Nil{}, 0n, 1n, Eval.Eval.dummy_inf(inf)),
    SolveRef.better(1n, Tree.Node{w, Nil{}}, Eval.Eval.dummy_inf(inf)),
    SolveRef.Best{Tree.Node{w, Nil{}}, 1n},
    e1, e2)

# Once `best` already has cost 1, any further guess on `[w]` keeps `best`.
def FO.guess_one_keep_case(+g: +List<Nat>, +w: +List<Nat>, +inf: Nat,
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool}, same: Bool) ->
  {Feedback.Bool.case(SolveRef.Best, same,
     SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n,
       SolveRef.Best{Tree.Node{w, Nil{}}, 1n}),
     SolveRef.Best{Tree.Node{w, Nil{}}, 1n})
   == SolveRef.Best{Tree.Node{w, Nil{}}, 1n} : SolveRef.Best}:
  match same:
    case False{}:
      {==}
    case True{}:
      +s1 : {SolveRef.sat_add(inf, 1n, 0n) == 1n : Nat} =
        FO.sat_add_one_zero(inf, h1)
      Equal.cong(Nat, SolveRef.Best,
        c => SolveRef.better(c, Tree.Node{g, Nil{}},
               SolveRef.Best{Tree.Node{w, Nil{}}, 1n}),
        SolveRef.sat_add(inf, 1n, 0n), 1n, s1)

def FO.guesses_one_keep(+p: Nat, +G: +List<+List<Nat>>, +w: +List<Nat>,
    +inf: Nat, +gs: +List<+List<Nat>>,
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool}) ->
  {Eval.Eval.guesses(1n+p, G, w <> Nil{}, inf, gs,
     SolveRef.Best{Tree.Node{w, Nil{}}, 1n})
   == SolveRef.Best{Tree.Node{w, Nil{}}, 1n} : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      +b1 : SolveRef.Best = SolveRef.Best{Tree.Node{w, Nil{}}, 1n}
      +eg : {Eval.Eval.guess(p, G, w <> Nil{}, g, inf, b1) == b1
             : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          Eval.Eval.guess(p, G, w <> Nil{}, g, inf, b1),
          Feedback.Bool.case(SolveRef.Best, Feedback.word_eq(g, w),
            SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, b1), b1),
          b1,
          FO.eval_guess_one(p, G, w, g, inf, b1, Feedback.word_eq(g, w)),
          FO.guess_one_keep_case(g, w, inf, h1, Feedback.word_eq(g, w)))
      Equal.trans(SolveRef.Best,
        Eval.Eval.guesses(1n+p, G, w <> Nil{}, inf, rest,
          Eval.Eval.guess(p, G, w <> Nil{}, g, inf, b1)),
        Eval.Eval.guesses(1n+p, G, w <> Nil{}, inf, rest, b1),
        b1,
        Equal.cong(SolveRef.Best, SolveRef.Best,
          b => Eval.Eval.guesses(1n+p, G, w <> Nil{}, inf, rest, b),
          Eval.Eval.guess(p, G, w <> Nil{}, g, inf, b1), b1, eg),
        FO.guesses_one_keep(p, G, w, inf, rest, h1))

# Folding guesses over `[w]` when `w` is in `gs` always returns
# `Best{Node{w, []}, 1}`.
def FO.guesses_one_mem_step(+p: Nat, +G: +List<+List<Nat>>, +w: +List<Nat>,
    +inf: Nat, +g: +List<Nat>, +rest: +List<+List<Nat>>,
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    same: Bool, +es: {same == Feedback.word_eq(w, g) : Bool},
    +mem: {Tree.member_word(w, g <> rest) == True{} : Bool},
    rec: {Tree.member_word(w, rest) == True{} : Bool} ->
         {SolveRef.Best{Tree.Node{w, Nil{}}, 1n}
          == Eval.Eval.guesses(1n+p, G, w <> Nil{}, inf, rest,
               Eval.Eval.dummy_inf(inf)) : SolveRef.Best}) ->
  {SolveRef.Best{Tree.Node{w, Nil{}}, 1n}
   == Eval.Eval.guesses(1n+p, G, w <> Nil{}, inf, g <> rest,
        Eval.Eval.dummy_inf(inf)) : SolveRef.Best}:
  match same:
    case True{}:
      +ewg : {Feedback.word_eq(w, g) == True{} : Bool} =
        Equal.sym(Bool, True{}, Feedback.word_eq(w, g), es)
      +eq : {w == g : +List<Nat>} = CoverList.Cover.word_eq_true(w, g, ewg)
      +egw : {Feedback.word_eq(g, w) == True{} : Bool} =
        Equal.trans(Bool, Feedback.word_eq(g, w), Feedback.word_eq(w, w),
          True{},
          Equal.cong(+List<Nat>, Bool, x => Feedback.word_eq(x, w),
            g, w, Equal.sym(+List<Nat>, w, g, eq)),
          FbProof.FbPrf.word_eq_refl(w))
      +d : SolveRef.Best = Eval.Eval.dummy_inf(inf)
      +b1 : SolveRef.Best = SolveRef.Best{Tree.Node{w, Nil{}}, 1n}
      +e1 : {Eval.Eval.guess(p, G, w <> Nil{}, g, inf, d)
             == SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, d)
             : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          Eval.Eval.guess(p, G, w <> Nil{}, g, inf, d),
          Feedback.Bool.case(SolveRef.Best, Feedback.word_eq(g, w),
            SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, d), d),
          SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, d),
          FO.eval_guess_one(p, G, w, g, inf, d, Feedback.word_eq(g, w)),
          Equal.cong(Bool, SolveRef.Best,
            b => Feedback.Bool.case(SolveRef.Best, b,
                   SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, d), d),
            Feedback.word_eq(g, w), True{}, egw))
      +e2 : {SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, d) == b1
             : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, d),
          SolveRef.finish_guess(inf, w, Nil{}, 0n, 1n, d),
          b1,
          Equal.cong(+List<Nat>, SolveRef.Best,
            x => SolveRef.finish_guess(inf, x, Nil{}, 0n, 1n, d),
            g, w, Equal.sym(+List<Nat>, w, g, eq)),
          FO.finish_one_eq(inf, w, h1))
      +eg : {Eval.Eval.guess(p, G, w <> Nil{}, g, inf, d) == b1
             : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          Eval.Eval.guess(p, G, w <> Nil{}, g, inf, d),
          SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, d),
          b1, e1, e2)
      +er : {Eval.Eval.guesses(1n+p, G, w <> Nil{}, inf, g <> rest, d) == b1
             : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          Eval.Eval.guesses(1n+p, G, w <> Nil{}, inf, rest,
            Eval.Eval.guess(p, G, w <> Nil{}, g, inf, d)),
          Eval.Eval.guesses(1n+p, G, w <> Nil{}, inf, rest, b1),
          b1,
          Equal.cong(SolveRef.Best, SolveRef.Best,
            b => Eval.Eval.guesses(1n+p, G, w <> Nil{}, inf, rest, b),
            Eval.Eval.guess(p, G, w <> Nil{}, g, inf, d), b1, eg),
          FO.guesses_one_keep(p, G, w, inf, rest, h1))
      Equal.sym(SolveRef.Best,
        Eval.Eval.guesses(1n+p, G, w <> Nil{}, inf, g <> rest, d), b1, er)
    case False{}:
      +ewg : {Feedback.word_eq(w, g) == False{} : Bool} =
        Equal.sym(Bool, False{}, Feedback.word_eq(w, g), es)
      +egw : {Feedback.word_eq(g, w) == False{} : Bool} =
        FO.word_eq_sym_false(w, g, ewg)
      +mt : {Tree.member_word(w, rest) == True{} : Bool} =
        Equal.trans(Bool,
          Tree.member_word(w, rest),
          Tree.member_word(w, g <> rest),
          True{},
          Equal.cong(Bool, Bool,
            b => Feedback.Bool.case(Bool, b, True{}, Tree.member_word(w, rest)),
            False{}, Feedback.word_eq(w, g), es),
          mem)
      +d : SolveRef.Best = Eval.Eval.dummy_inf(inf)
      +b1 : SolveRef.Best = SolveRef.Best{Tree.Node{w, Nil{}}, 1n}
      +eg : {Eval.Eval.guess(p, G, w <> Nil{}, g, inf, d) == d
             : SolveRef.Best} =
        Equal.trans(SolveRef.Best,
          Eval.Eval.guess(p, G, w <> Nil{}, g, inf, d),
          Feedback.Bool.case(SolveRef.Best, Feedback.word_eq(g, w),
            SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, d), d),
          d,
          FO.eval_guess_one(p, G, w, g, inf, d, Feedback.word_eq(g, w)),
          Equal.cong(Bool, SolveRef.Best,
            b => Feedback.Bool.case(SolveRef.Best, b,
                   SolveRef.finish_guess(inf, g, Nil{}, 0n, 1n, d), d),
            Feedback.word_eq(g, w), False{}, egw))
      Equal.trans(SolveRef.Best,
        b1,
        Eval.Eval.guesses(1n+p, G, w <> Nil{}, inf, rest, d),
        Eval.Eval.guesses(1n+p, G, w <> Nil{}, inf, rest,
          Eval.Eval.guess(p, G, w <> Nil{}, g, inf, d)),
        rec(mt),
        Equal.cong(SolveRef.Best, SolveRef.Best,
          b => Eval.Eval.guesses(1n+p, G, w <> Nil{}, inf, rest, b),
          d, Eval.Eval.guess(p, G, w <> Nil{}, g, inf, d),
          Equal.sym(SolveRef.Best,
            Eval.Eval.guess(p, G, w <> Nil{}, g, inf, d), d, eg)))

def FO.guesses_one_mem(+p: Nat, +G: +List<+List<Nat>>, +w: +List<Nat>,
    +inf: Nat, +gs: +List<+List<Nat>>,
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +mem: {Tree.member_word(w, gs) == True{} : Bool}) ->
  {SolveRef.Best{Tree.Node{w, Nil{}}, 1n}
   == Eval.Eval.guesses(1n+p, G, w <> Nil{}, inf, gs,
        Eval.Eval.dummy_inf(inf)) : SolveRef.Best}:
  match gs:
    case Nil{}:
      Empty.absurd(
        {SolveRef.Best{Tree.Node{w, Nil{}}, 1n}
         == Eval.Eval.guesses(1n+p, G, w <> Nil{}, inf, Nil{},
              Eval.Eval.dummy_inf(inf)) : SolveRef.Best},
        Logic.Proof.false_ne_true(mem))
    case Con{+g, +rest}:
      FO.guesses_one_mem_step(p, G, w, inf, g, rest, h1,
        Feedback.word_eq(w, g), {==}, mem,
        mt => FO.guesses_one_mem(p, G, w, inf, rest, h1, mt))

# For any singleton class `[w]` with `w in G`, `1 <= p` and `1 < inf`, the
# reference search returns `Best{Node{w, []}, 1}`.
def FO.ref_run_one_eq(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +w: +List<Nat>,
    +ble: {Nat.is_le(1n, p) == True{} : Bool},
    +h1: {Nat.is_lt(1n, inf) == True{} : Bool},
    +win: {Tree.member_word(w, G) == True{} : Bool}) ->
  {SolveRef.Best{Tree.Node{w, Nil{}}, 1n}
   == FStep.FS.ref_run_at(p, inf, G, w <> Nil{}) : SolveRef.Best}:
  match p:
    case 0n:
      Empty.absurd(
        {SolveRef.Best{Tree.Node{w, Nil{}}, 1n}
         == FStep.FS.ref_run_at(0n, inf, G, w <> Nil{}) : SolveRef.Best},
        Logic.Proof.false_ne_true(ble))
    case 1n+p2:
      Equal.trans(SolveRef.Best,
        SolveRef.Best{Tree.Node{w, Nil{}}, 1n},
        Eval.Eval.guesses(1n+p2, G, w <> Nil{}, inf, G,
          Eval.Eval.dummy_inf(inf)),
        FStep.FS.ref_run_at(1n+p2, inf, G, w <> Nil{}),
        FO.guesses_one_mem(p2, G, w, inf, G, h1, win),
        Equal.sym(SolveRef.Best,
          FStep.FS.ref_run_at(1n+p2, inf, G, w <> Nil{}),
          Eval.Eval.guesses(1n+p2, G, w <> Nil{}, inf, G,
            Eval.Eval.dummy_inf(inf)),
          Eval.Eval.guesses_step(p2, G, w <> Nil{}, inf, G,
            Eval.Eval.dummy_inf(inf))))

# For any list of at least two candidates, `1 < inf_of(|C|)`.
def FO.one_lt_inf_ge2(+w: +List<Nat>, +w2: +List<Nat>,
    +t2: +List<+List<Nat>>) ->
  {Nat.is_lt(1n, SolveRef.inf_of(Groups.len_words(w <> (w2 <> t2))))
   == True{} : Bool}:
  {==}
