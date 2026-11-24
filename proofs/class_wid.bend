# Obligation B: the canonical reference tree is bounded by the class branching
# factor.
#
# `class_k_start` returns a `k` that bounds the number of distinct feedback
# codes any guess of the guess list produces on the class. This module proves
# that the reference search's tree over that class is `Wid t k` for any such
# `k`: at every node the children are the non-empty feedback groups of the
# node's guess on the node's class, the number of children is the number of
# distinct codes of that guess on that class (`CH.children`), a child class is a
# subsequence of its parent (`Cover.all_subseq_nil`), so every node's count is
# at most the root class's `CK.prefmax`, which `k` bounds.
#
# The proof is a fuel induction over the reference evaluation, in the shape of
# `mainvalid.bend`'s validity proof, but carrying `k` itself: the recursive
# calls hand every class of every guess its own `Wid` at the same `k`, so no
# monotonicity of `Wid` in `k` is needed.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ../src/solve_fast.bend as SolveFast
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./eval.bend as Eval
import ./children.bend as CH
import ./cover.bend as Cover
import ./cover_groups.bend as CG
import ./cover_list.bend as CoverList
import ./fast_step.bend as FStep
import ./fast_tbl.bend as FT
import ./fast_cutoff.bend as FCut
import ./bestok.bend as BO
import ./class_k.bend as CK
import ./class_sub.bend as CS
import ./fast_nodup.bend as FN
import ./lb_capacity.bend as CapProof
import ./lb_twice.bend as Twice
import ./lb_capacity_sound.bend as LBProof8
import ./mainvalid.bend as MV

# ---------------------------------------------------------------------------
# `CK.prefmax` bounds the count of every guess of the list
# ---------------------------------------------------------------------------

# The count of the `i`-th guess is at most the prefmax of the first `i + 1`.
def WK.nth_pref(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>, +i: Nat) ->
  {Nat.is_le(CK.CK.count(FT.FT.nth_word(G, i), ws),
             CK.CK.prefmax(G, ws, Nat.add(1n, i))) == True{} : Bool}:
  match i:
    case 0n:
      CK.CK.le_max_l(CK.CK.count(FT.FT.nth_word(G, 0n), ws),
        CK.CK.prefmax(G, ws, 0n))
    case 1n+p:
      CK.CK.le_max_l(CK.CK.count(FT.FT.nth_word(G, 1n+p), ws),
        CK.CK.prefmax(G, ws, 1n+p))

# The prefmax of a tail is at most the prefmax of the list with one more guess.
def WK.prefmax_tail(+h: +List<Nat>, +t: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +i: Nat) ->
  {Nat.is_le(CK.CK.prefmax(t, ws, i), CK.CK.prefmax(h <> t, ws, Nat.add(1n, i)))
   == True{} : Bool}:
  match i:
    case 0n:
      NatProof.Nat.is_le_zero_l(CK.CK.prefmax(h <> t, ws, 1n))
    case 1n+p:
      CK.CK.max_le(CK.CK.count(FT.FT.nth_word(t, p), ws), CK.CK.prefmax(t, ws, p),
        CK.CK.prefmax(h <> t, ws, Nat.add(1n, 1n+p)),
        CK.CK.le_max_l(CK.CK.count(FT.FT.nth_word(t, p), ws),
          CK.CK.prefmax(h <> t, ws, 1n+p)),
        NatProof.Nat.is_le_trans(CK.CK.prefmax(t, ws, p),
          CK.CK.prefmax(h <> t, ws, 1n+p),
          CK.CK.prefmax(h <> t, ws, Nat.add(1n, 1n+p)),
          WK.prefmax_tail(h, t, ws, p),
          CK.CK.prefmax_mono(h <> t, ws, 1n+p)))

# The prefmax of a prefix is at most the prefmax of the whole list.
def WK.prefmax_le_len(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>, +i: Nat,
    +le: {Nat.is_le(i, CK.CK.len(G)) == True{} : Bool}) ->
  {Nat.is_le(CK.CK.prefmax(G, ws, i), CK.CK.prefmax(G, ws, CK.CK.len(G)))
   == True{} : Bool}:
  +fuel : Nat = Nat.sub(CK.CK.len(G), i)
  +e : {Nat.add(i, fuel) == CK.CK.len(G) : Nat} =
    FCut.FC.add_sub_of_le(CK.CK.len(G), i, le)
  NatProof.Nat.is_le_eq_r(CK.CK.prefmax(G, ws, i),
    CK.CK.prefmax(G, ws, Nat.add(i, fuel)),
    CK.CK.prefmax(G, ws, CK.CK.len(G)),
    Equal.cong(Nat, Nat, x => CK.CK.prefmax(G, ws, x),
      Nat.add(i, fuel), CK.CK.len(G), e),
    CK.CK.prefmax_le_add(G, ws, i, fuel))

# One cons step of the membership bound, with the word test as a parameter.
def WK.count_mem_step(+h: +List<Nat>, +t: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +g: +List<Nat>, b: Bool,
    +eb: {b == Feedback.word_eq(g, h) : Bool},
    wg: {Feedback.Bool.case(Bool, b, True{}, Tree.member_word(g, t))
         == True{} : Bool},
    rec: {Tree.member_word(g, t) == True{} : Bool} ->
         {Nat.is_le(CK.CK.count(g, ws),
            CK.CK.prefmax(t, ws, CK.CK.len(t))) == True{} : Bool}) ->
  {Nat.is_le(CK.CK.count(g, ws),
             CK.CK.prefmax(h <> t, ws, CK.CK.len(h <> t))) == True{} : Bool}:
  match b:
    case True{}:
      +G : +List<+List<Nat>> = h <> t
      +h1len : {Nat.is_le(1n, CK.CK.len(G)) == True{} : Bool} =
        NatProof.Nat.is_le_succ(0n, CK.CK.len(t),
          NatProof.Nat.is_le_zero_l(CK.CK.len(t)))
      +eg : {g == h : +List<Nat>} =
        CoverList.Cover.word_eq_true(g, h,
          Equal.sym(Bool, True{}, Feedback.word_eq(g, h), eb))
      +ec : {CK.CK.count(g, ws) == CK.CK.count(h, ws) : Nat} =
        Equal.cong(+List<Nat>, Nat, w => CK.CK.count(w, ws), g, h, eg)
      NatProof.Nat.is_le_eq_l(CK.CK.prefmax(G, ws, CK.CK.len(G)),
        CK.CK.count(h, ws), CK.CK.count(g, ws),
        Equal.sym(Nat, CK.CK.count(g, ws), CK.CK.count(h, ws), ec),
        NatProof.Nat.is_le_trans(CK.CK.count(h, ws), CK.CK.prefmax(G, ws, 1n),
          CK.CK.prefmax(G, ws, CK.CK.len(G)),
          CK.CK.le_max_l(CK.CK.count(FT.FT.nth_word(G, 0n), ws),
            CK.CK.prefmax(G, ws, 0n)),
          WK.prefmax_le_len(G, ws, 1n, h1len)))
    case False{}:
      +G : +List<+List<Nat>> = h <> t
      NatProof.Nat.is_le_trans(CK.CK.count(g, ws),
        CK.CK.prefmax(t, ws, CK.CK.len(t)),
        CK.CK.prefmax(G, ws, CK.CK.len(G)),
        rec(wg),
        WK.prefmax_tail(h, t, ws, CK.CK.len(t)))

# The count of a guess of the list is at most the class's prefmax.
def WK.count_mem(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +g: +List<Nat>, wg: Tree.WordIn(g, G)) ->
  {Nat.is_le(CK.CK.count(g, ws), CK.CK.prefmax(G, ws, CK.CK.len(G)))
   == True{} : Bool}:
  match G:
    case Nil{}:
      Empty.absurd(
        {Nat.is_le(CK.CK.count(g, ws), CK.CK.prefmax(Nil{}, ws, CK.CK.len(Nil{})))
         == True{} : Bool}, Logic.Proof.false_ne_true(wg))
    case Con{h, t}:
      WK.count_mem_step(h, t, ws, g, Feedback.word_eq(g, h), {==}, wg,
        mw => WK.count_mem(t, ws, g, mw))

# ---------------------------------------------------------------------------
# Child lists: transport, reversals
# ---------------------------------------------------------------------------

def WK.wid_transport(+t1: Tree.Tree, +t2: Tree.Tree, +k: Nat,
    +e: {t1 == t2 : Tree.Tree}, w: LBProof8.LBS.Wid(t1, k)) ->
  LBProof8.LBS.Wid(t2, k):
  %e : LBProof8.LBS.Wid(_, k)
  w

def WK.widkids_transport(+xs: +List<Tree.Child>, +ys: +List<Tree.Child>,
    +k: Nat, +e: {xs == ys : List<&2, Tree.Child>},
    w: LBProof8.LBS.WidKids(xs, k)) ->
  LBProof8.LBS.WidKids(ys, k):
  %e : LBProof8.LBS.WidKids(_, k)
  w

# A reversed child list keeps the widness of every child.
def WK.widkids_rev(+xs: +List<Tree.Child>, +acc: +List<Tree.Child>, +k: Nat,
    w: LBProof8.LBS.WidKids(xs, k),
    wa: LBProof8.LBS.WidKids(acc, k)) ->
  LBProof8.LBS.WidKids(SolveRef.rev_kids(xs, acc), k):
  match xs:
    case Nil{}:
      wa
    case Con{c, rest}:
      match c:
        case Tree.Child{f, t}:
          (wh, wr) = w
          WK.widkids_rev(rest, Tree.Child{f, t} <> acc, k, wr, (wh, wa))

# ---------------------------------------------------------------------------
# The invariants
# ---------------------------------------------------------------------------

# The tree of one job at a given fuel has at most `k` children at every node.
def WK.WJob(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +k: Nat) -> Type:
  LBProof8.LBS.Wid(Eval.Eval.tree_of(FStep.FS.ref_run_at(fuel, inf, G, S)), k)

# The conjunction of the obligations over a list of candidate lists.
def WK.WFlat(fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>, +k: Nat,
    +jobs: +List<+List<+List<Nat>>>) -> Type:
  match jobs:
    case Nil{}:
      Unit
    case Con{S, t}:
      WK.WJob(fuel, inf, G, S, k) & WK.WFlat(fuel, inf, G, k, t)

# The obligations of the classes of one group list.
def WK.WOks(+p: Nat, +G: +List<+List<Nat>>, +inf: Nat, +k: Nat,
    +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          WK.WJob(p, inf, G, ws, k) & WK.WOks(p, G, inf, k, rest)

def WK.WOksIf(b: Bool, +p: Nat, +G: +List<+List<Nat>>, +inf: Nat, +k: Nat,
    +groups: +List<Groups.Group>) -> Type:
  match b:
    case True{}:
      WK.WOks(p, G, inf, k, groups)
    case False{}:
      Unit

# The per-guess class obligations of a guess list.
def WK.WByGs(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +inf: Nat,
    +k: Nat, gs: +List<+List<Nat>>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{g, t}:
      WK.WOksIf(Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), p, G,
        inf, k, Groups.groups_build(g, S, Nil{}))
      & WK.WByGs(p, G, S, inf, k, t)

# The prefmax of every job is at most `k`.
def WK.Prefs(+G: +List<+List<Nat>>, +k: Nat,
    jobs: +List<+List<+List<Nat>>>) -> Type:
  match jobs:
    case Nil{}:
      Unit
    case Con{S, t}:
      {Nat.is_le(CK.CK.prefmax(G, S, CK.CK.len(G)), k) == True{} : Bool}
      & WK.Prefs(G, k, t)

# The prefmax of every class of a group list is at most `k`.
def WK.GPrefs(+G: +List<+List<Nat>>, +k: Nat,
    +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          {Nat.is_le(CK.CK.prefmax(G, ws, CK.CK.len(G)), k) == True{} : Bool}
          & WK.GPrefs(G, k, rest)

# ---------------------------------------------------------------------------
# The node step
# ---------------------------------------------------------------------------

# `better` keeps widness when both candidates are wide enough.
def WK.better_wid(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    +tree: Tree.Tree, +cost: Nat, +k: Nat, b: Bool,
    +eb: {b == Nat.is_lt(candCost, cost) : Bool},
    wc: LBProof8.LBS.Wid(candTree, k),
    wb: LBProof8.LBS.Wid(tree, k)) ->
  LBProof8.LBS.Wid(Eval.Eval.tree_of(Feedback.Bool.case(SolveRef.Best, b,
    SolveRef.Best{candTree, candCost}, SolveRef.Best{tree, cost})), k):
  match b:
    case True{}:
      wc
    case False{}:
      wb

def WK.better_wid_best(+inf: Nat, +candCost: Nat, +candTree: Tree.Tree,
    best: SolveRef.Best, +k: Nat,
    wc: LBProof8.LBS.Wid(candTree, k),
    wb: LBProof8.LBS.Wid(Eval.Eval.tree_of(best), k)) ->
  LBProof8.LBS.Wid(Eval.Eval.tree_of(SolveRef.better(candCost, candTree, best)), k):
  match best:
    case SolveRef.Best{tree, +cost}:
      WK.better_wid(inf, candCost, candTree, tree, cost, k,
        Nat.is_lt(candCost, cost), {==}, wc, wb)

# Finishing a guess keeps widness: the node's children are the reversed
# accumulator, whose length the caller bounds.
def WK.finish_wid(+inf: Nat, +g: +List<Nat>, +kids: +List<Tree.Child>,
    +sum: Nat, +n: Nat, best: SolveRef.Best, +k: Nat,
    wk: LBProof8.LBS.WidKids(kids, k),
    wlen: {Nat.is_le(List.length(&2, Tree.Child, SolveRef.rev_kids(kids, Nil{})),
                     k) == True{} : Bool},
    wb: LBProof8.LBS.Wid(Eval.Eval.tree_of(best), k)) ->
  LBProof8.LBS.Wid(Eval.Eval.tree_of(
    SolveRef.finish_guess(inf, g, kids, sum, n, best)), k):
  WK.better_wid_best(inf, SolveRef.sat_add(inf, n, sum),
    Tree.Node{g, SolveRef.rev_kids(kids, Nil{})}, best, k,
    (wlen, WK.widkids_rev(kids, Nil{}, k, wk, Unit{})), wb)

def WK.dummy_wid(inf: Nat, +k: Nat) ->
  LBProof8.LBS.Wid(Eval.Eval.tree_of(Eval.Eval.dummy_inf(inf)), k):
  (NatProof.Nat.is_le_zero_l(k), Unit{})

# The children of a group list are wide, given their jobs.
def WK.children_wid(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +groups: +List<Groups.Group>, +inf: Nat, +k: Nat,
    woks: WK.WOks(p, G, inf, k, groups)) ->
  LBProof8.LBS.WidKids(CH.CH.children(p, G, S, groups, inf), k):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          (wh, wr) = woks
          (wh, WK.children_wid(p, G, S, rest, inf, k, wr))

# The children a guess accumulates are wide.
def WK.items_wid(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +groups: +List<Groups.Group>, +inf: Nat, +k: Nat,
    woks: WK.WOks(p, G, inf, k, groups)) ->
  LBProof8.LBS.WidKids(
    CH.CH.kids_of(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)), k):
  +e : {SolveRef.rev_kids(CH.CH.children(p, G, S, groups, inf), Nil{})
        == CH.CH.kids_of(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf))
        : +List<Tree.Child>} =
    Equal.sym(+List<Tree.Child>,
      CH.CH.kids_of(Eval.Eval.items(p, G, S, g, groups, Nil{}, 0n, inf)),
      SolveRef.rev_kids(CH.CH.children(p, G, S, groups, inf), Nil{}),
      CH.CH.items_kids(p, G, S, g, groups, Nil{}, 0n, inf))
  %e : LBProof8.LBS.WidKids(_, k)
  WK.widkids_rev(CH.CH.children(p, G, S, groups, inf), Nil{}, k,
    WK.children_wid(p, G, S, groups, inf, k, woks), Unit{})

# The zero-fuel fold over the guess list keeps widness: every guess finishes an
# empty child list, whose node has no children.
def WK.guesses_zero_wid(+G: +List<+List<Nat>>, +inf: Nat, +k: Nat,
    +gs: +List<+List<Nat>>, +best: SolveRef.Best,
    every: BO.BO.EveryIn(gs, G),
    wb: LBProof8.LBS.Wid(Eval.Eval.tree_of(best), k)) ->
  LBProof8.LBS.Wid(Eval.Eval.tree_of(
    Eval.Eval.guesses(0n, G, Nil{}, inf, gs, best)), k):
  match gs:
    case Nil{}:
      wb
    case Con{g, rest}:
      (wg, every2) = every
      WK.guesses_zero_wid(G, inf, k, rest,
        SolveRef.finish_guess(inf, g, Nil{}, 0n, Groups.len_words(Nil{}), best),
        every2,
        WK.finish_wid(inf, g, Nil{}, 0n, Groups.len_words(Nil{}), best, k,
          Unit{}, NatProof.Nat.is_le_zero_l(k), wb))

# The empty candidate list at zero fuel.
def WK.job_nil(+inf: Nat, +G: +List<+List<Nat>>, +k: Nat) ->
  WK.WJob(0n, inf, G, Nil{}, k):
  +eb : {SolveRef.step(0n, SolveRef.mk_schedule(G, Nil{}), G, Nil{}, inf,
          Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())
         == Eval.Eval.guesses(0n, G, Nil{}, inf, G, Eval.Eval.dummy_inf(inf))
         : SolveRef.Best} =
    Eval.Eval.guesses_zero(G, inf, G, Eval.Eval.dummy_inf(inf))
  +et : {Eval.Eval.tree_of(Eval.Eval.guesses(0n, G, Nil{}, inf, G,
            Eval.Eval.dummy_inf(inf)))
         == Eval.Eval.tree_of(SolveRef.step(0n, SolveRef.mk_schedule(G, Nil{}), G,
            Nil{}, inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf),
            Eval.Eval.dummy_zero())) : Tree.Tree} =
    Equal.cong(SolveRef.Best, Tree.Tree, Eval.Eval.tree_of,
      Eval.Eval.guesses(0n, G, Nil{}, inf, G, Eval.Eval.dummy_inf(inf)),
      SolveRef.step(0n, SolveRef.mk_schedule(G, Nil{}), G, Nil{}, inf, Nil{}, Nil{},
        0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()),
      Equal.sym(SolveRef.Best,
        SolveRef.step(0n, SolveRef.mk_schedule(G, Nil{}), G, Nil{}, inf, Nil{}, Nil{},
          0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()),
        Eval.Eval.guesses(0n, G, Nil{}, inf, G, Eval.Eval.dummy_inf(inf)), eb))
  %et : LBProof8.LBS.Wid(_, k)
  WK.guesses_zero_wid(G, inf, k, G, Eval.Eval.dummy_inf(inf),
    BO.BO.every_in_self(G), WK.dummy_wid(inf, k))

# ---------------------------------------------------------------------------
# The prefmax of the classes from the prefmax of the class
# ---------------------------------------------------------------------------

# A class of a group list has prefmax at most the group list's class.
def WK.gprefs_go(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +groups: +List<Groups.Group>, +k: Nat,
    +hS: {Nat.is_le(CK.CK.prefmax(G, S, CK.CK.len(G)), k) == True{} : Bool},
    all: CG.Cover.AllSubseq(groups, S)) -> WK.GPrefs(G, k, groups):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          (sub, all2) = all
          (NatProof.Nat.is_le_trans(CK.CK.prefmax(G, ws, CK.CK.len(G)),
             CK.CK.prefmax(G, S, CK.CK.len(G)), k,
             CS.CS.prefmax_sub(G, ws, S, CK.CK.len(G), sub), hS),
           WK.gprefs_go(G, S, rest, k, hS, all2))

def WK.prefs_append(+G: +List<+List<Nat>>, +k: Nat,
    xs: +List<+List<+List<Nat>>>, ys: +List<+List<+List<Nat>>>,
    px: WK.Prefs(G, k, xs), py: WK.Prefs(G, k, ys)) ->
  WK.Prefs(G, k, List.append(&2, +List<+List<Nat>>, xs, ys)):
  match xs:
    case Nil{}:
      py
    case Con{h, t}:
      (ph, pt) = px
      (ph, WK.prefs_append(G, k, t, ys, pt, py))

def WK.gprefs_flat(+G: +List<+List<Nat>>, +k: Nat,
    +groups: +List<Groups.Group>, gp: WK.GPrefs(G, k, groups)) ->
  WK.Prefs(G, k, MV.MV.next_groups(groups)):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp0, rest}:
      match gp0:
        case Groups.Group{fb, ws}:
          (ph, pt) = gp
          WK.prefs_append(G, k, ws <> Nil{}, MV.MV.next_groups(rest),
            (ph, Unit{}), WK.gprefs_flat(G, k, rest, pt))

def WK.classes_prefs(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +k: Nat,
    +hS: {Nat.is_le(CK.CK.prefmax(G, S, CK.CK.len(G)), k) == True{} : Bool},
    b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool}) ->
  WK.Prefs(G, k, MV.MV.classes_b(b, Groups.groups_build(g, S, Nil{}))):
  match b:
    case True{}:
      WK.gprefs_flat(G, k, Groups.groups_build(g, S, Nil{}),
        WK.gprefs_go(G, S, Groups.groups_build(g, S, Nil{}), k, hS,
          CG.Cover.all_subseq_nil(g, S)))
    case False{}:
      Unit{}

def WK.any_prefs(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +k: Nat,
    +hS: {Nat.is_le(CK.CK.prefmax(G, S, CK.CK.len(G)), k) == True{} : Bool},
    +gs: +List<+List<Nat>>) -> WK.Prefs(G, k, MV.MV.next_guess(gs, S)):
  match gs:
    case Nil{}:
      Unit{}
    case Con{g, t}:
      WK.prefs_append(G, k, MV.MV.classes(g, S), MV.MV.next_guess(t, S),
        WK.classes_prefs(G, S, g, k, hS,
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==}),
        WK.any_prefs(G, S, k, hS, t))

def WK.next_prefs(+G: +List<+List<Nat>>, +k: Nat,
    +jobs: +List<+List<+List<Nat>>>, prefs: WK.Prefs(G, k, jobs)) ->
  WK.Prefs(G, k, MV.MV.next_jobs(G, jobs)):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{S, t}:
      (ph, pt) = prefs
      WK.prefs_append(G, k, MV.MV.next_guess(G, S), MV.MV.next_jobs(G, t),
        WK.any_prefs(G, S, k, ph, G), WK.next_prefs(G, k, t, pt))

# ---------------------------------------------------------------------------
# One guess
# ---------------------------------------------------------------------------

# Finishing one guess keeps widness: the children are wide and their count is
# at most `k`, so the node is.
def WK.block_wid(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +best: SolveRef.Best, +k: Nat, ks: Eval.KS,
    +eks: {ks == Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}),
             Nil{}, 0n, inf) : Eval.KS},
    wg: Tree.WordIn(g, G),
    +hpref: {Nat.is_le(CK.CK.prefmax(G, S, CK.CK.len(G)), k) == True{} : Bool},
    woks: WK.WOks(p, G, inf, k, Groups.groups_build(g, S, Nil{})),
    wb: LBProof8.LBS.Wid(Eval.Eval.tree_of(best), k)) ->
  LBProof8.LBS.Wid(Eval.Eval.tree_of(Eval.Eval.finish_ks(inf, g, S, ks, best)), k):
  match ks:
    case Eval.KS{+kids, +sum}:
      +lit : Eval.KS = Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}),
                           Nil{}, 0n, inf)
      +ekids : {kids == CH.CH.kids_of(lit) : List<&2, Tree.Child>} =
        Equal.cong(Eval.KS, +List<Tree.Child>, CH.CH.kids_of,
          Eval.KS{kids, sum}, lit, eks)
      wki : LBProof8.LBS.WidKids(CH.CH.kids_of(lit), k) =
        WK.items_wid(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf, k, woks)
      wkids : LBProof8.LBS.WidKids(kids, k) =
        WK.widkids_transport(CH.CH.kids_of(lit), kids, k,
          Equal.sym(+List<Tree.Child>, kids, CH.CH.kids_of(lit), ekids), wki)
      +ek2 : {SolveRef.rev_kids(kids, Nil{})
              == SolveRef.rev_kids(CH.CH.kids_of(lit), Nil{})
              : List<&2, Tree.Child>} =
        Equal.cong(+List<Tree.Child>, +List<Tree.Child>,
          l => SolveRef.rev_kids(l, Nil{}), kids, CH.CH.kids_of(lit), ekids)
      +ek3 : {SolveRef.rev_kids(CH.CH.kids_of(lit), Nil{})
              == CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf)
              : List<&2, Tree.Child>} =
        Equal.trans(+List<Tree.Child>,
          SolveRef.rev_kids(CH.CH.kids_of(lit), Nil{}),
          SolveRef.rev_kids(
            SolveRef.rev_kids(CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf),
              Nil{}), Nil{}),
          CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf),
          Equal.cong(+List<Tree.Child>, +List<Tree.Child>,
            l => SolveRef.rev_kids(l, Nil{}),
            CH.CH.kids_of(lit),
            SolveRef.rev_kids(CH.CH.children(p, G, S,
              Groups.groups_build(g, S, Nil{}), inf), Nil{}),
            CH.CH.items_kids(p, G, S, g, Groups.groups_build(g, S, Nil{}),
              Nil{}, 0n, inf)),
          CH.CH.rev_rev(CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf)))
      +ekids_children : {SolveRef.rev_kids(kids, Nil{})
                         == CH.CH.children(p, G, S,
                              Groups.groups_build(g, S, Nil{}), inf)
                         : List<&2, Tree.Child>} =
        Equal.trans(+List<Tree.Child>, SolveRef.rev_kids(kids, Nil{}),
          SolveRef.rev_kids(CH.CH.kids_of(lit), Nil{}),
          CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf), ek2, ek3)
      +hcnt : {Nat.is_le(CK.CK.count(g, S), k) == True{} : Bool} =
        NatProof.Nat.is_le_trans(CK.CK.count(g, S),
          CK.CK.prefmax(G, S, CK.CK.len(G)), k,
          WK.count_mem(G, S, g, wg), hpref)
      +hclen : {Nat.is_le(
                  List.length(&2, Tree.Child,
                    CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf)), k)
                == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(k, CK.CK.count(g, S),
          List.length(&2, Tree.Child,
            CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf)),
          Equal.sym(Nat,
            List.length(&2, Tree.Child,
              CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf)),
            CK.CK.count(g, S), CS.CS.len_children_build(p, G, S, g, inf)),
          hcnt)
      +wlen : {Nat.is_le(
                 List.length(&2, Tree.Child, SolveRef.rev_kids(kids, Nil{})), k)
               == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(k,
          List.length(&2, Tree.Child,
            CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf)),
          List.length(&2, Tree.Child, SolveRef.rev_kids(kids, Nil{})),
          Equal.cong(+List<Tree.Child>, Nat,
            l => List.length(&2, Tree.Child, l),
            CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf),
            SolveRef.rev_kids(kids, Nil{}),
            Equal.sym(+List<Tree.Child>, SolveRef.rev_kids(kids, Nil{}),
              CH.CH.children(p, G, S, Groups.groups_build(g, S, Nil{}), inf),
              ekids_children)),
          hclen)
      WK.finish_wid(inf, g, kids, sum, Groups.len_words(S), best, k,
        wkids, wlen, wb)

# The usable-guess branch keeps widness; the unusable one leaves the state.
def WK.guess_ok_go(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +best: SolveRef.Best, +k: Nat, b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    wg: Tree.WordIn(g, G),
    +hpref: {Nat.is_le(CK.CK.prefmax(G, S, CK.CK.len(G)), k) == True{} : Bool},
    oks: WK.WOksIf(b, p, G, inf, k, Groups.groups_build(g, S, Nil{})),
    wb: LBProof8.LBS.Wid(Eval.Eval.tree_of(best), k)) ->
  LBProof8.LBS.Wid(Eval.Eval.tree_of(
    Eval.Eval.guess_bool(p, G, S, g, Groups.groups_build(g, S, Nil{}), inf, b, best)), k):
  match b:
    case True{}:
      WK.block_wid(p, G, S, g, inf, best, k,
        Eval.Eval.items(p, G, S, g, Groups.groups_build(g, S, Nil{}), Nil{}, 0n, inf),
        {==}, wg, hpref, oks, wb)
    case False{}:
      wb

def WK.guess_ok(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +inf: Nat, +best: SolveRef.Best, +k: Nat,
    +eb: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
          == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    wg: Tree.WordIn(g, G),
    +hpref: {Nat.is_le(CK.CK.prefmax(G, S, CK.CK.len(G)), k) == True{} : Bool},
    oks: WK.WOksIf(Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
           p, G, inf, k, Groups.groups_build(g, S, Nil{})),
    wb: LBProof8.LBS.Wid(Eval.Eval.tree_of(best), k)) ->
  LBProof8.LBS.Wid(Eval.Eval.tree_of(Eval.Eval.guess(p, G, S, g, inf, best)), k):
  WK.guess_ok_go(p, G, S, g, inf, best, k,
    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), eb, wg, hpref, oks, wb)

# The guess fold: every guess keeps widness.
def WK.guesses_fold(+inf: Nat, +p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +gs: +List<+List<Nat>>, +best: SolveRef.Best, +k: Nat,
    +hpref: {Nat.is_le(CK.CK.prefmax(G, S, CK.CK.len(G)), k) == True{} : Bool},
    f: WK.WByGs(p, G, S, inf, k, gs),
    every: BO.BO.EveryIn(gs, G),
    wb: LBProof8.LBS.Wid(Eval.Eval.tree_of(best), k)) ->
  LBProof8.LBS.Wid(Eval.Eval.tree_of(
    Eval.Eval.guesses(1n+p, G, S, inf, gs, best)), k):
  match gs:
    case Nil{}:
      wb
    case Con{g, t}:
      (oks, ft) = f
      (wg, every2) = every
      WK.guesses_fold(inf, p, G, S, t, Eval.Eval.guess(p, G, S, g, inf, best), k,
        hpref, ft, every2,
        WK.guess_ok(p, G, S, g, inf, best, k, {==}, wg, hpref, oks, wb))

# One step of the fuel: the machine fold is the specification fold.
def WK.step_to_fold(+inf: Nat, +p: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +k: Nat,
    +hpref: {Nat.is_le(CK.CK.prefmax(G, S, CK.CK.len(G)), k) == True{} : Bool},
    f: WK.WByGs(p, G, S, inf, k, G)) -> WK.WJob(1n+p, inf, G, S, k):
  +eb : {SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S, inf, Nil{}, Nil{}, 0n,
          Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero())
         == Eval.Eval.guesses(1n+p, G, S, inf, G, Eval.Eval.dummy_inf(inf))
         : SolveRef.Best} =
    Eval.Eval.guesses_step(p, G, S, inf, G, Eval.Eval.dummy_inf(inf))
  +et : {Eval.Eval.tree_of(Eval.Eval.guesses(1n+p, G, S, inf, G,
            Eval.Eval.dummy_inf(inf)))
         == Eval.Eval.tree_of(SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S,
            inf, Nil{}, Nil{}, 0n, Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()))
         : Tree.Tree} =
    Equal.cong(SolveRef.Best, Tree.Tree, Eval.Eval.tree_of,
      Eval.Eval.guesses(1n+p, G, S, inf, G, Eval.Eval.dummy_inf(inf)),
      SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S, inf, Nil{}, Nil{}, 0n,
        Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()),
      Equal.sym(SolveRef.Best,
        SolveRef.step(1n+p, SolveRef.mk_schedule(G, S), G, S, inf, Nil{}, Nil{}, 0n,
          Eval.Eval.dummy_inf(inf), Eval.Eval.dummy_zero()),
        Eval.Eval.guesses(1n+p, G, S, inf, G, Eval.Eval.dummy_inf(inf)), eb))
  %et : LBProof8.LBS.Wid(_, k)
  WK.guesses_fold(inf, p, G, S, G, Eval.Eval.dummy_inf(inf), k, hpref, f,
    BO.BO.every_in_self(G), WK.dummy_wid(inf, k))

# ---------------------------------------------------------------------------
# The class obligations, read off the conjunction at the next level
# ---------------------------------------------------------------------------

# Split the conjunction at an append.
def WK.flat_append(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>, +k: Nat,
    +xs: +List<+List<+List<Nat>>>, +ys: +List<+List<+List<Nat>>>,
    f: WK.WFlat(fuel, inf, G, k, List.append(&2, +List<+List<Nat>>, xs, ys))) ->
  WK.WFlat(fuel, inf, G, k, xs) & WK.WFlat(fuel, inf, G, k, ys):
  match xs:
    case Nil{}:
      Tuple{Unit{}, f}
    case Con{S, t}:
      (j, fr) = f
      MV.MV.use_pair(WK.WFlat(fuel, inf, G, k, S <> t) & WK.WFlat(fuel, inf, G, k, ys),
        WK.WFlat(fuel, inf, G, k, t), WK.WFlat(fuel, inf, G, k, ys),
        WK.flat_append(fuel, inf, G, k, t, ys, fr),
        ft => fys => Tuple{Tuple{j, ft}, fys})

def WK.oks_of_flat(+p: Nat, +G: +List<+List<Nat>>, +inf: Nat, +k: Nat,
    +groups: +List<Groups.Group>,
    f: WK.WFlat(p, inf, G, k, MV.MV.next_groups(groups))) ->
  WK.WOks(p, G, inf, k, groups):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          (j, fr) = f
          (j, WK.oks_of_flat(p, G, inf, k, rest, fr))

def WK.oks_if(+p: Nat, +G: +List<+List<Nat>>, +inf: Nat, +k: Nat,
    +groups: +List<Groups.Group>, b: Bool,
    f: WK.WFlat(p, inf, G, k, MV.MV.classes_b(b, groups))) ->
  WK.WOksIf(b, p, G, inf, k, groups):
  match b:
    case True{}:
      WK.oks_of_flat(p, G, inf, k, groups, f)
    case False{}:
      Unit{}

def WK.by_gs(+p: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +inf: Nat, +k: Nat, +gs: +List<+List<Nat>>,
    f: WK.WFlat(p, inf, G, k, MV.MV.next_guess(gs, S))) ->
  WK.WByGs(p, G, S, inf, k, gs):
  match gs:
    case Nil{}:
      Unit{}
    case Con{g, t}:
      MV.MV.use_pair(WK.WByGs(p, G, S, inf, k, g <> t),
        WK.WFlat(p, inf, G, k, MV.MV.classes(g, S)),
        WK.WFlat(p, inf, G, k, MV.MV.next_guess(t, S)),
        WK.flat_append(p, inf, G, k, MV.MV.classes(g, S), MV.MV.next_guess(t, S), f),
        fg => ft =>
          Tuple{WK.oks_if(p, G, inf, k, Groups.groups_build(g, S, Nil{}),
                  Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), fg),
                WK.by_gs(p, G, S, inf, k, t, ft)})

# ---------------------------------------------------------------------------
# Plan-1 style flatness: one step and the fuel induction
# ---------------------------------------------------------------------------

def WK.flat_step(+inf: Nat, +p: Nat, +G: +List<+List<Nat>>, +k: Nat,
    +jobs: +List<+List<+List<Nat>>>,
    prefs: WK.Prefs(G, k, jobs),
    f: WK.WFlat(p, inf, G, k, MV.MV.next_jobs(G, jobs))) ->
  WK.WFlat(1n+p, inf, G, k, jobs):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{S, t}:
      (hpref, pt) = prefs
      MV.MV.use_pair(WK.WFlat(1n+p, inf, G, k, S <> t),
        WK.WFlat(p, inf, G, k, MV.MV.next_guess(G, S)),
        WK.WFlat(p, inf, G, k, MV.MV.next_jobs(G, t)),
        WK.flat_append(p, inf, G, k, MV.MV.next_guess(G, S), MV.MV.next_jobs(G, t), f),
        fS => ft =>
          Tuple{WK.step_to_fold(inf, p, G, S, k, hpref,
                  WK.by_gs(p, G, S, inf, k, G, fS)),
                WK.flat_step(inf, p, G, k, t, pt, ft)})

# A zero-length job is the empty candidate list, whose tree has one node.
def WK.job_zero(+inf: Nat, +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +k: Nat,
    le: {Nat.is_le(Groups.len_words(S), 0n) == True{} : Bool}) ->
  WK.WJob(0n, inf, G, S, k):
  +eS : {S == Nil{} : +List<+List<Nat>>} =
    MV.MV.nil_of_len_zero(S, NatProof.Nat.eq_zero_of_le_zero(Groups.len_words(S), le))
  +e : {FStep.FS.ref_run_at(0n, inf, G, S) == FStep.FS.ref_run_at(0n, inf, G, Nil{})
        : SolveRef.Best} =
    Equal.cong(+List<+List<Nat>>, SolveRef.Best,
      s => FStep.FS.ref_run_at(0n, inf, G, s), S, Nil{}, eS)
  +et : {Eval.Eval.tree_of(FStep.FS.ref_run_at(0n, inf, G, S))
         == Eval.Eval.tree_of(FStep.FS.ref_run_at(0n, inf, G, Nil{})) : Tree.Tree} =
    Equal.cong(SolveRef.Best, Tree.Tree, Eval.Eval.tree_of,
      FStep.FS.ref_run_at(0n, inf, G, S), FStep.FS.ref_run_at(0n, inf, G, Nil{}), e)
  WK.wid_transport(Eval.Eval.tree_of(FStep.FS.ref_run_at(0n, inf, G, Nil{})),
    Eval.Eval.tree_of(FStep.FS.ref_run_at(0n, inf, G, S)), k,
    Equal.sym(Tree.Tree,
      Eval.Eval.tree_of(FStep.FS.ref_run_at(0n, inf, G, S)),
      Eval.Eval.tree_of(FStep.FS.ref_run_at(0n, inf, G, Nil{})), et),
    WK.job_nil(inf, G, k))

def WK.flat_zero(+inf: Nat, +G: +List<+List<Nat>>, +k: Nat,
    +jobs: +List<+List<+List<Nat>>>, bounds: MV.MV.Bounds(0n, jobs)) ->
  WK.WFlat(0n, inf, G, k, jobs):
  match jobs:
    case Nil{}:
      Unit{}
    case Con{S, t}:
      (ble, bt) = bounds
      (WK.job_zero(inf, G, S, k, ble), WK.flat_zero(inf, G, k, t, bt))

# The prefmax hypothesis of every job can be used twice.
def WK.prefs_dup(+G: +List<+List<Nat>>, +k: Nat,
    jobs: +List<+List<+List<Nat>>>, prefs: WK.Prefs(G, k, jobs)) ->
  WK.Prefs(G, k, jobs) & WK.Prefs(G, k, jobs):
  match jobs:
    case Nil{}:
      (Unit{}, Unit{})
    case Con{S, t}:
      (ph, pt) = prefs
      +ph2 : {Nat.is_le(CK.CK.prefmax(G, S, CK.CK.len(G)), k) == True{} : Bool} = ph
      MV.MV.use_pair(WK.Prefs(G, k, jobs) & WK.Prefs(G, k, jobs),
        WK.Prefs(G, k, t), WK.Prefs(G, k, t),
        WK.prefs_dup(G, k, t, pt),
        p1 => p2 => ((ph2, p1), (ph2, p2)))

# The fuel induction. One recursive call per level hands every class of every
# job its obligation at the smaller fuel.
def WK.flat(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>, +k: Nat,
    +jobs: +List<+List<+List<Nat>>>,
    bounds: MV.MV.Bounds(fuel, jobs),
    prefs: WK.Prefs(G, k, jobs)) -> WK.WFlat(fuel, inf, G, k, jobs):
  match fuel:
    case 0n:
      WK.flat_zero(inf, G, k, jobs, bounds)
    case 1n+p:
      MV.MV.use_pair(WK.WFlat(1n+p, inf, G, k, jobs),
        WK.Prefs(G, k, jobs), WK.Prefs(G, k, jobs),
        WK.prefs_dup(G, k, jobs, prefs),
        p1 => p2 =>
          WK.flat_step(inf, p, G, k, jobs, p1,
            WK.flat(p, inf, G, k, MV.MV.next_jobs(G, jobs),
              MV.MV.next_bounds(p, G, jobs, bounds),
              WK.next_prefs(G, k, jobs, p2))))

# ---------------------------------------------------------------------------
# The tree of a class
# ---------------------------------------------------------------------------

# The obligation for the top-level candidate list.
def WK.main_wid(+fuel: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +k: Nat,
    +hpref: {Nat.is_le(CK.CK.prefmax(G, C, CK.CK.len(G)), k) == True{} : Bool},
    le: {Nat.is_le(Groups.len_words(C), fuel) == True{} : Bool}) ->
  WK.WJob(fuel, inf, G, C, k):
  MV.MV.use_pair(WK.WJob(fuel, inf, G, C, k), WK.WJob(fuel, inf, G, C, k), Unit,
    WK.flat(fuel, inf, G, k, C <> Nil{}, Tuple{le, Unit{}}, Tuple{hpref, Unit{}}),
    j => u => j)

# The reference tree over a class is as wide as `k` whenever `k` bounds the
# class's prefmax.
def WK.ref_wid(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +C: +List<+List<Nat>>, +k: Nat,
    +hpref: {Nat.is_le(CK.CK.prefmax(G, C, CK.CK.len(G)), k) == True{} : Bool},
    le: {Nat.is_le(Groups.len_words(C), p) == True{} : Bool}) ->
  LBProof8.LBS.Wid(Eval.Eval.tree_of(FStep.FS.ref_run_at(p, inf, G, C)), k):
  WK.main_wid(p, inf, G, C, k, hpref, le)

# ---------------------------------------------------------------------------
# The capacity bound on a class
# ---------------------------------------------------------------------------

# A duplicate-free class has largest multiplicity one.
def WK.mult_le_one(+ws: +List<+List<Nat>>,
    +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool}) ->
  {Nat.is_le(Twice.LB.maxMult(ws), 1n) == True{} : Bool}:
  match ws:
    case Nil{}:
      NatProof.Nat.is_le_zero_l(1n)
    case Con{w, t}:
      NatProof.Nat.is_le_eq_l(1n, 1n, Twice.LB.maxMult(w <> t),
        Equal.sym(Nat, Twice.LB.maxMult(w <> t), 1n,
          FN.FN.max_mult_one_of_no_dup(t, w, hnd)),
        NatProof.Nat.is_le_refl(1n))

# The capacity bound is a lower bound on the reference tree of a class.
def WK.class_cap(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +k: Nat,
    +hpref: {Nat.is_le(CK.CK.prefmax(G, ws, CK.CK.len(G)), k) == True{} : Bool},
    le: {Nat.is_le(Groups.len_words(ws), p) == True{} : Bool},
    +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool},
    v: Tree.Valid(Eval.Eval.tree_of(FStep.FS.ref_run_at(p, inf, G, ws)), G, ws)) ->
  {Nat.is_le(CapProof.LB.capbound(Groups.len_words(ws), k),
     Tree.cost(Eval.Eval.tree_of(FStep.FS.ref_run_at(p, inf, G, ws)), ws))
   == True{} : Bool}:
  LBProof8.LB.capbound_sound(Eval.Eval.tree_of(FStep.FS.ref_run_at(p, inf, G, ws)),
    G, ws, k, WK.ref_wid(p, inf, G, ws, k, hpref, le), v,
    WK.mult_le_one(ws, hnd))
