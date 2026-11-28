# Soundness of sibling-level depth-two lookahead lower bounds.
#
# For a candidate subset `ws` and guess list `G`, `LB2.all_usable_ge(G, ws, lb)`
# states that every usable guess `g` in `G` has depth-two lower bound
# `SolveFast.lower_bound(|ws|, Groups.groups_build(g, ws, Nil{})) >= lb`.
#
# Main theorems:
# - `LB2.valid_tree_cost_ge`: any valid tree `T` for `(G, ws)` satisfies
#   `lb <= Tree.cost(T, ws)` whenever `LB2.all_usable_ge(G, ws, lb) == True{}`.
# - `LB2.child_lb_le_ref`: any `clb` accepted by `LB2.clb_ok_b(G, nodup, ws, clb)`
#   sits at or below the finite reference child search cost.
# - `LB2.all_usable_ge_of_le_floor` and `LB2.all_usable_ge_of_le_2n`: floor
#   early-exit soundness for `SolveFast.scan_lb2_step`.
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
import ./bestok.bend as BO
import ./solvevalid.bend as SV
import ./mainvalid.bend as MV
import ./classbound.bend as CBProof
import ./classbound_nat.bend as CBN
import ./optcost.bend as OC
import ./optfold.bend as Fold
import ./optind.bend as Ind
import ./groupcost.bend as GC
import ./nodecost.bend as NodeCost
import ./cover.bend as Cover
import ./cover_oracle.bend as Cora
import ./cover_kids.bend as Ckids
import ./cover_list.bend as Clist
import ./cover_groups.bend as Cgrp
import ./fast_step.bend as FStep
import ./fast_lb.bend as FLB
import ./fast_nodup.bend as FN

# Every usable guess `g` in `gs` has `lb <= lower_bound(|ws|, groups_build(g, ws))`.
def LB2.all_usable_ge(+gs: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +lb: Nat) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case Con{g, rest}:
      Bool.and(
        Feedback.Bool.case(Bool,
          Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})),
          Nat.is_le(lb, SolveFast.lower_bound(Groups.len_words(ws),
                          Groups.groups_build(g, ws, Nil{}))),
          True{}),
        LB2.all_usable_ge(rest, ws, lb))

# Soundness predicate for a per-class lower bound `clb`: either bounded by the
# depth-two multiplicity bound `class_lb(ws)`, or (under `nodup`) bounded by
# `all_usable_ge(G, ws, clb)` from a depth-two lookahead scan.
def LB2.clb_ok_b(+G: +List<+List<Nat>>, +nodup: Bool,
    +ws: +List<+List<Nat>>, +clb: Nat) -> Bool:
  Bool.or(
    Nat.is_le(clb, SolveFast.class_lb(ws)),
    Bool.and(nodup, LB2.all_usable_ge(G, ws, clb)))

def LB2.bool_and_intro(a: Bool, b: Bool, +ha: {a == True{} : Bool},
    +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(a, b), Bool.and(True{}, b), True{},
    Equal.cong(Bool, Bool, x => Bool.and(x, b), a, True{}, ha), hb)

def LB2.bool_or_l(a: Bool, b: Bool, +ha: {a == True{} : Bool}) ->
  {Bool.or(a, b) == True{} : Bool}:
  Equal.cong(Bool, Bool, x => Bool.or(x, b), a, True{}, ha)

def LB2.bool_or_r(a: Bool, b: Bool, +hb: {b == True{} : Bool}) ->
  {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def LB2.clb_ok_of_le_class_lb(+G: +List<+List<Nat>>, +nodup: Bool,
    +ws: +List<+List<Nat>>, +clb: Nat,
    +hle: {Nat.is_le(clb, SolveFast.class_lb(ws)) == True{} : Bool}) ->
  {LB2.clb_ok_b(G, nodup, ws, clb) == True{} : Bool}:
  LB2.bool_or_l(Nat.is_le(clb, SolveFast.class_lb(ws)),
    Bool.and(nodup, LB2.all_usable_ge(G, ws, clb)), hle)

def LB2.clb_ok_of_all_usable(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +clb: Nat, +hall: {LB2.all_usable_ge(G, ws, clb) == True{} : Bool}) ->
  {LB2.clb_ok_b(G, True{}, ws, clb) == True{} : Bool}:
  LB2.bool_or_r(Nat.is_le(clb, SolveFast.class_lb(ws)),
    LB2.all_usable_ge(G, ws, clb), hall)

# Monotonicity of `all_usable_ge` when `lb` decreases.
def LB2.usable_case_mono(us: Bool, +lb1: Nat, +lb2: Nat, +v: Nat,
    +hle: {Nat.is_le(lb2, lb1) == True{} : Bool},
    +h1: {Feedback.Bool.case(Bool, us, Nat.is_le(lb1, v), True{}) == True{} : Bool}) ->
  {Feedback.Bool.case(Bool, us, Nat.is_le(lb2, v), True{}) == True{} : Bool}:
  match us:
    case True{}:
      NatProof.Nat.is_le_trans(lb2, lb1, v, hle, h1)
    case False{}:
      {==}

def LB2.all_usable_ge_mono(+gs: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +lb1: Nat, +lb2: Nat,
    +hle: {Nat.is_le(lb2, lb1) == True{} : Bool},
    +h1: {LB2.all_usable_ge(gs, ws, lb1) == True{} : Bool}) ->
  {LB2.all_usable_ge(gs, ws, lb2) == True{} : Bool}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      +us = Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
      +v = SolveFast.lower_bound(Groups.len_words(ws),
             Groups.groups_build(g, ws, Nil{}))
      +hh = Logic.Proof.and_true_l(
              Feedback.Bool.case(Bool, us, Nat.is_le(lb1, v), True{}),
              LB2.all_usable_ge(rest, ws, lb1), h1)
      +ht = Logic.Proof.and_true_r(
              Feedback.Bool.case(Bool, us, Nat.is_le(lb1, v), True{}),
              LB2.all_usable_ge(rest, ws, lb1), h1)
      LB2.bool_and_intro(
        Feedback.Bool.case(Bool, us, Nat.is_le(lb2, v), True{}),
        LB2.all_usable_ge(rest, ws, lb2),
        LB2.usable_case_mono(us, lb1, lb2, v, hle, hh),
        LB2.all_usable_ge_mono(rest, ws, lb1, lb2, hle, ht))

def LB2.all_usable_ge_append(+xs: +List<+List<Nat>>, +ys: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +lb: Nat,
    +hx: {LB2.all_usable_ge(xs, ws, lb) == True{} : Bool},
    +hy: {LB2.all_usable_ge(ys, ws, lb) == True{} : Bool}) ->
  {LB2.all_usable_ge(List.append(&2, +List<Nat>, xs, ys), ws, lb)
   == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+g, +rest}:
      +us = Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
      +v = SolveFast.lower_bound(Groups.len_words(ws),
             Groups.groups_build(g, ws, Nil{}))
      +hh = Logic.Proof.and_true_l(
              Feedback.Bool.case(Bool, us, Nat.is_le(lb, v), True{}),
              LB2.all_usable_ge(rest, ws, lb), hx)
      +ht = Logic.Proof.and_true_r(
              Feedback.Bool.case(Bool, us, Nat.is_le(lb, v), True{}),
              LB2.all_usable_ge(rest, ws, lb), hx)
      LB2.bool_and_intro(
        Feedback.Bool.case(Bool, us, Nat.is_le(lb, v), True{}),
        LB2.all_usable_ge(List.append(&2, +List<Nat>, rest, ys), ws, lb),
        hh, LB2.all_usable_ge_append(rest, ys, ws, lb, ht, hy))

# Look up one usable guess `g` inside `all_usable_ge(gs, ws, lb)`.
def LB2.all_usable_ge_at_go(+h: +List<Nat>, +t: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +lb: Nat, +g: +List<Nat>,
    b: Bool, +eb: {b == Feedback.word_eq(g, h) : Bool},
    +mem: {Tree.member_word(g, h <> t) == True{} : Bool},
    +hall: {LB2.all_usable_ge(h <> t, ws, lb) == True{} : Bool},
    +hus: {Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
           == True{} : Bool},
    ih: {Tree.member_word(g, t) == True{} : Bool} ->
        {LB2.all_usable_ge(t, ws, lb) == True{} : Bool} ->
        {Nat.is_le(lb, SolveFast.lower_bound(Groups.len_words(ws),
                         Groups.groups_build(g, ws, Nil{}))) == True{} : Bool}) ->
  {Nat.is_le(lb, SolveFast.lower_bound(Groups.len_words(ws),
                   Groups.groups_build(g, ws, Nil{}))) == True{} : Bool}:
  match b:
    case True{}:
      +egh : {g == h : +List<Nat>} =
        Clist.Cover.word_eq_true(g, h,
          Equal.sym(Bool, True{}, Feedback.word_eq(g, h), eb))
      +egrp : {Groups.groups_build(g, ws, Nil{})
               == Groups.groups_build(h, ws, Nil{}) : +List<Groups.Group>} =
        Equal.cong(+List<Nat>, +List<Groups.Group>,
          x => Groups.groups_build(x, ws, Nil{}), g, h, egh)
      +ush : {Groups.groups_smaller(ws, Groups.groups_build(h, ws, Nil{}))
              == True{} : Bool} =
        Equal.trans(Bool,
          Groups.groups_smaller(ws, Groups.groups_build(h, ws, Nil{})),
          Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})), True{},
          Equal.cong(+List<Groups.Group>, Bool, z => Groups.groups_smaller(ws, z),
            Groups.groups_build(h, ws, Nil{}), Groups.groups_build(g, ws, Nil{}),
            Equal.sym(+List<Groups.Group>, Groups.groups_build(g, ws, Nil{}),
              Groups.groups_build(h, ws, Nil{}), egrp)), hus)
      +vh = SolveFast.lower_bound(Groups.len_words(ws),
              Groups.groups_build(h, ws, Nil{}))
      +vg = SolveFast.lower_bound(Groups.len_words(ws),
              Groups.groups_build(g, ws, Nil{}))
      +hh = Logic.Proof.and_true_l(
              Feedback.Bool.case(Bool,
                Groups.groups_smaller(ws, Groups.groups_build(h, ws, Nil{})),
                Nat.is_le(lb, vh), True{}),
              LB2.all_usable_ge(t, ws, lb), hall)
      +hleh : {Nat.is_le(lb, vh) == True{} : Bool} =
        Equal.trans(Bool, Nat.is_le(lb, vh),
          Feedback.Bool.case(Bool,
            Groups.groups_smaller(ws, Groups.groups_build(h, ws, Nil{})),
            Nat.is_le(lb, vh), True{}), True{},
          Equal.sym(Bool,
            Feedback.Bool.case(Bool,
              Groups.groups_smaller(ws, Groups.groups_build(h, ws, Nil{})),
              Nat.is_le(lb, vh), True{}),
            Nat.is_le(lb, vh),
            Equal.cong(Bool, Bool,
              u => Feedback.Bool.case(Bool, u, Nat.is_le(lb, vh), True{}),
              Groups.groups_smaller(ws, Groups.groups_build(h, ws, Nil{})),
              True{}, ush)), hh)
      NatProof.Nat.is_le_eq_r(lb, vh, vg,
        Equal.cong(+List<Groups.Group>, Nat,
          z => SolveFast.lower_bound(Groups.len_words(ws), z),
          Groups.groups_build(h, ws, Nil{}), Groups.groups_build(g, ws, Nil{}),
          Equal.sym(+List<Groups.Group>, Groups.groups_build(g, ws, Nil{}),
            Groups.groups_build(h, ws, Nil{}), egrp)), hleh)
    case False{}:
      +vh = SolveFast.lower_bound(Groups.len_words(ws),
              Groups.groups_build(h, ws, Nil{}))
      +ht = Logic.Proof.and_true_r(
              Feedback.Bool.case(Bool,
                Groups.groups_smaller(ws, Groups.groups_build(h, ws, Nil{})),
                Nat.is_le(lb, vh), True{}),
              LB2.all_usable_ge(t, ws, lb), hall)
      +mt : {Tree.member_word(g, t) == True{} : Bool} =
        Cora.Cover.member_tail(g, h, t, b, eb, {==}, mem)
      ih(mt, ht)

def LB2.all_usable_ge_at(+gs: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +lb: Nat, +g: +List<Nat>,
    +mem: {Tree.member_word(g, gs) == True{} : Bool},
    +hall: {LB2.all_usable_ge(gs, ws, lb) == True{} : Bool},
    +hus: {Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
           == True{} : Bool}) ->
  {Nat.is_le(lb, SolveFast.lower_bound(Groups.len_words(ws),
                   Groups.groups_build(g, ws, Nil{}))) == True{} : Bool}:
  match gs:
    case Nil{}:
      Empty.absurd(
        {Nat.is_le(lb, SolveFast.lower_bound(Groups.len_words(ws),
                         Groups.groups_build(g, ws, Nil{}))) == True{} : Bool},
        Logic.Proof.false_ne_true(mem))
    case Con{+h, +t}:
      LB2.all_usable_ge_at_go(h, t, ws, lb, g, Feedback.word_eq(g, h), {==},
        mem, hall, hus,
        +mt => +ht => LB2.all_usable_ge_at(t, ws, lb, g, mt, ht, hus))

# ---------------------------------------------------------------------------
# Valid-tree lower bound: `all_usable_ge(G, ws, lb) -> lb <= Tree.cost(T, ws)`
# ---------------------------------------------------------------------------

def LB2.class_words_le_total(+G: +List<+List<Nat>>, +kids: +List<Tree.Child>,
    +groups: +List<Groups.Group>,
    gk: Cora.Cover.GroupKids(G, kids, groups)) ->
  {Nat.is_le(SolveFast.class_words(groups), GC.GC.Total(kids, groups))
   == True{} : Bool}:
  match groups:
    case Nil{}:
      NatProof.Nat.is_le_refl(0n)
    case Con{gp, +rest}:
      match gp:
        case Groups.Group{+fb, +ws}:
          (kh, kt) = gk
          match kh:
            case Tuple{+T, kp}:
              (e_look, valid) = kp
              +le1 : {Nat.is_le(SolveFast.class_lb(ws), Tree.cost(T, ws))
                      == True{} : Bool} =
                FLB.FS.valid_cost_ge_class_lb(T, G, ws, valid)
              +egc : {GC.GC.GroupCost(kids, Groups.Group{fb, ws})
                      == Tree.cost(T, ws) : Nat} =
                Cover.Cover.group_cost_some(kids, fb, ws, T, e_look)
              +le_hd : {Nat.is_le(SolveFast.class_lb(ws),
                          GC.GC.GroupCost(kids, Groups.Group{fb, ws}))
                        == True{} : Bool} =
                Fold.OQ.le_cong_r(SolveFast.class_lb(ws), Tree.cost(T, ws),
                  GC.GC.GroupCost(kids, Groups.Group{fb, ws}),
                  Equal.sym(Nat, GC.GC.GroupCost(kids, Groups.Group{fb, ws}),
                    Tree.cost(T, ws), egc), le1)
              +le_tl = LB2.class_words_le_total(G, kids, rest, kt)
              CBN.CB.is_le_add(SolveFast.class_lb(ws),
                GC.GC.GroupCost(kids, Groups.Group{fb, ws}),
                SolveFast.class_words(rest), GC.GC.Total(kids, rest),
                le_hd, le_tl)

def LB2.node_lb_le_cost(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +g: +List<Nat>, +kids: +List<Tree.Child>,
    kidsin: Tree.KidsIn(kids, G),
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, ws)) ->
  {Nat.is_le(
     SolveFast.lower_bound(Groups.len_words(ws),
       Groups.groups_build(g, ws, Nil{})),
     Tree.cost(Tree.Node{g, kids}, ws)) == True{} : Bool}:
  +n : Nat = Groups.len_words(ws)
  +gb : +List<Groups.Group> = Groups.groups_build(g, ws, Nil{})
  Cover.Cover.depths_agd(
    {Nat.is_le(SolveFast.lower_bound(n, gb),
       Tree.cost(Tree.Node{g, kids}, ws)) == True{} : Bool},
    g, kids, ws, Nil{}, depths, Unit{},
    ok => d2 =>
      +neokb : {Ckids.Cover.all_ne(gb) == True{} : Bool} =
        Ckids.Cover.groups_build_ne(g, ws, Nil{}, {==})
      +kb : {Ckids.Cover.kids_in_b(kids, G) == True{} : Bool} =
        Ckids.Cover.kids_in_to_b(kids, G, kidsin)
      Ckids.Cover.groupkids_from(
        {Nat.is_le(SolveFast.lower_bound(n, gb),
           Tree.cost(Tree.Node{g, kids}, ws)) == True{} : Bool},
        G, g, kids, gb, kb, neokb, ok,
        gk =>
          +hcw = LB2.class_words_le_total(G, kids, gb, gk)
          +hkid : {Nat.is_le(SolveFast.class_words(gb),
                     NodeCost.NodeCost.kid_sum(g, kids, ws)) == True{} : Bool} =
            Fold.OQ.le_cong_r(SolveFast.class_words(gb), GC.GC.Total(kids, gb),
              NodeCost.NodeCost.kid_sum(g, kids, ws),
              GC.GC.groups_build_total(g, kids, ws), hcw)
          +hadd : {Nat.is_le(Nat.add(n, SolveFast.class_words(gb)),
                     Nat.add(n, NodeCost.NodeCost.kid_sum(g, kids, ws)))
                   == True{} : Bool} =
            NatProof.Nat.is_le_add_l(SolveFast.class_words(gb),
              NodeCost.NodeCost.kid_sum(g, kids, ws), n, hkid)
          +cn : {Tree.cost(Tree.Node{g, kids}, ws)
                 == Nat.add(n, NodeCost.NodeCost.kid_sum(g, kids, ws)) : Nat} =
            Equal.trans(Nat, Tree.cost(Tree.Node{g, kids}, ws),
              Nat.add(List.length(&2, +List<Nat>, ws),
                NodeCost.NodeCost.kid_sum(g, kids, ws)),
              Nat.add(n, NodeCost.NodeCost.kid_sum(g, kids, ws)),
              NodeCost.NodeCost.cost_node(g, kids, ws, d2), {==})
          Fold.OQ.le_cong_l(SolveFast.lower_bound(n, gb),
            Nat.add(n, SolveFast.class_words(gb)),
            Tree.cost(Tree.Node{g, kids}, ws),
            FLB.FS.lower_bound_eq(n, gb),
            Fold.OQ.le_cong_r(Nat.add(n, SolveFast.class_words(gb)),
              Nat.add(n, NodeCost.NodeCost.kid_sum(g, kids, ws)),
              Tree.cost(Tree.Node{g, kids}, ws),
              Equal.sym(Nat, Tree.cost(Tree.Node{g, kids}, ws),
                Nat.add(n, NodeCost.NodeCost.kid_sum(g, kids, ws)), cn),
              hadd))))

def LB2.KidBound(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>, +lb: Nat,
    +T: Tree.Tree) -> Type:
  Tree.Valid(T, G, ws) -> {Nat.is_le(lb, Tree.cost(T, ws)) == True{} : Bool}

def LB2.AllKidBound(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>, +lb: Nat,
    +kids: +List<Tree.Child>) -> Type:
  match kids:
    case Nil{}:
      Unit
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          LB2.KidBound(G, ws, lb, child) & LB2.AllKidBound(G, ws, lb, rest)

def LB2.pick_kid_head(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>, +lb: Nat,
    +fb: +List<Feedback.Color>, +f: +List<Feedback.Color>, +child: Tree.Tree,
    +rest: +List<Tree.Child>, head: LB2.KidBound(G, ws, lb, child),
    +T: Tree.Tree,
    +e: {Tree.lookup(fb, Tree.Child{f, child} <> rest)
         == Some{T} : Maybe<&1, Tree.Tree>},
    b: Bool, +eb: {b == Feedback.feedback_eq(fb, f) : Bool},
    k: {Tree.lookup(fb, rest) == Some{T} : Maybe<&1, Tree.Tree>} ->
       LB2.KidBound(G, ws, lb, T)) ->
  LB2.KidBound(G, ws, lb, T):
  match b:
    case True{}:
      +es : {Some{child} == Some{T} : Maybe<&1, Tree.Tree>} =
        Equal.trans(Maybe<&1, Tree.Tree>, Some{child},
          Tree.lookup(fb, Tree.Child{f, child} <> rest), Some{T},
          Equal.cong(Bool, Maybe<&1, Tree.Tree>,
            x => Feedback.Bool.case(Maybe<&1, Tree.Tree>, x, Some{child},
                   Tree.lookup(fb, rest)),
            True{}, Feedback.feedback_eq(fb, f), eb), e)
      +ect : {child == T : Tree.Tree} =
        Equal.cong(Maybe<&1, Tree.Tree>, Tree.Tree,
          m => Maybe.default(&1, Tree.Tree, m, child),
          Some{child}, Some{T}, es)
      %ect : LB2.KidBound(G, ws, lb, _)
      head
    case False{}:
      +er : {Tree.lookup(fb, rest) == Some{T} : Maybe<&1, Tree.Tree>} =
        Equal.trans(Maybe<&1, Tree.Tree>, Tree.lookup(fb, rest),
          Tree.lookup(fb, Tree.Child{f, child} <> rest), Some{T},
          Equal.cong(Bool, Maybe<&1, Tree.Tree>,
            x => Feedback.Bool.case(Maybe<&1, Tree.Tree>, x, Some{child},
                   Tree.lookup(fb, rest)),
            False{}, Feedback.feedback_eq(fb, f), eb), e)
      k(er)

def LB2.maybe_tree_disc(m: Maybe<&1, Tree.Tree>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{_}:
      Empty

def LB2.none_ne_some_tree(+T: Tree.Tree,
    +e: {None{} == Some{T} : Maybe<&1, Tree.Tree>}) -> Empty:
  %e : LB2.maybe_tree_disc(_)
  Unit{}

def LB2.pick_kid(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>, +lb: Nat,
    +fb: +List<Feedback.Color>, +kids: +List<Tree.Child>,
    all: LB2.AllKidBound(G, ws, lb, kids), +T: Tree.Tree,
    +e: {Tree.lookup(fb, kids) == Some{T} : Maybe<&1, Tree.Tree>}) ->
  LB2.KidBound(G, ws, lb, T):
  match kids:
    case Nil{}:
      Empty.absurd(LB2.KidBound(G, ws, lb, T), LB2.none_ne_some_tree(T, e))
    case Con{c, +rest}:
      match c:
        case Tree.Child{+f, +child}:
          (head, tail) = all
          LB2.pick_kid_head(G, ws, lb, fb, f, child, rest, head, T, e,
            Feedback.feedback_eq(fb, f), {==},
            +e2 => LB2.pick_kid(G, ws, lb, fb, rest, tail, T, e2))

def LB2.valid_node_ge_unusable(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +lb: Nat, +g: +List<Nat>, +kids: +List<Tree.Child>,
    res: Ind.OQ.KidRes(G, ws, g, kids),
    all: LB2.AllKidBound(G, ws, lb, kids)) ->
  {Nat.is_le(lb, Tree.cost(Tree.Node{g, kids}, ws)) == True{} : Bool}:
  match res:
    case Tuple{+T2, r}:
      (valid_ws, r2) = r
      (le2, r3) = r2
      (fb2, el2) = r3
      +hle = LB2.pick_kid(G, ws, lb, fb2, kids, all, T2, el2)(valid_ws)
      NatProof.Nat.is_le_trans(lb, Tree.cost(T2, ws),
        Tree.cost(Tree.Node{g, kids}, ws), hle, le2)

def LB2.valid_node_ge_go(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>,
    +lb: Nat, +g: +List<Nat>, +kids: +List<Tree.Child>,
    +hall: {LB2.all_usable_ge(G, ws, lb) == True{} : Bool},
    v: Tree.Valid(Tree.Node{g, kids}, G, ws),
    b: Bool,
    +eb: {b == Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
          : Bool},
    all: LB2.AllKidBound(G, ws, lb, kids)) ->
  {Nat.is_le(lb, Tree.cost(Tree.Node{g, kids}, ws)) == True{} : Bool}:
  ((wg, kidsin), depths) = v
  match b:
    case True{}:
      +hus : {Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
              == True{} : Bool} =
        Equal.sym(Bool, True{},
          Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})), eb)
      +h1 = LB2.all_usable_ge_at(G, ws, lb, g, wg, hall, hus)
      +h2 = LB2.node_lb_le_cost(G, ws, g, kids, kidsin, depths)
      NatProof.Nat.is_le_trans(lb,
        SolveFast.lower_bound(Groups.len_words(ws),
          Groups.groups_build(g, ws, Nil{})),
        Tree.cost(Tree.Node{g, kids}, ws), h1, h2)
    case False{}:
      +ef : {Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
             == False{} : Bool} =
        Equal.sym(Bool, False{},
          Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})), eb)
      LB2.valid_node_ge_unusable(G, ws, lb, g, kids,
        Ind.OQ.unusable_kid(G, ws, g, kids, Groups.groups_build(g, ws, Nil{}),
          {==}, depths, kidsin, ef), all)

def LB2.all_kid_bounds(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>, +lb: Nat,
    +hall: {LB2.all_usable_ge(G, ws, lb) == True{} : Bool},
    +kids: +List<Tree.Child>) -> LB2.AllKidBound(G, ws, lb, kids):
  match kids:
    case Nil{}:
      Unit{}
    case Con{c, +rest}:
      match c:
        case Tree.Child{f, child}:
          match child:
            case Tree.Node{+g, +ckids}:
              (v => LB2.valid_node_ge_go(G, ws, lb, g, ckids, hall, v,
                      Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})),
                      {==}, LB2.all_kid_bounds(G, ws, lb, hall, ckids)),
               LB2.all_kid_bounds(G, ws, lb, hall, rest))

def LB2.valid_tree_cost_ge(T: Tree.Tree, +G: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +lb: Nat,
    +hall: {LB2.all_usable_ge(G, ws, lb) == True{} : Bool},
    v: Tree.Valid(T, G, ws)) ->
  {Nat.is_le(lb, Tree.cost(T, ws)) == True{} : Bool}:
  match T:
    case Tree.Node{+g, +kids}:
      LB2.valid_node_ge_go(G, ws, lb, g, kids, hall, v,
        Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})), {==},
        LB2.all_kid_bounds(G, ws, lb, hall, kids))

# Any `clb` with `clb_ok_b(G, nodup, ws, clb) == True{}` sits at or below the
# finite reference child search cost.
def LB2.child_lb_le_ref_go(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +nodup: Bool, +ws: +List<+List<Nat>>, +clb: Nat,
    +ble: {Nat.is_le(Groups.len_words(ws), p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +clt: {Nat.is_lt(Sat.SB.child_cost(p, G, ws, inf), inf) == True{} : Bool},
    le_c: Bool, +elec: {le_c == Nat.is_le(clb, SolveFast.class_lb(ws)) : Bool},
    +hok: {LB2.clb_ok_b(G, nodup, ws, clb) == True{} : Bool}) ->
  {Nat.is_le(clb, Sat.SB.child_cost(p, G, ws, inf)) == True{} : Bool}:
  match le_c:
    case True{}:
      +h1 : {Nat.is_le(clb, SolveFast.class_lb(ws)) == True{} : Bool} =
        Equal.sym(Bool, True{}, Nat.is_le(clb, SolveFast.class_lb(ws)), elec)
      NatProof.Nat.is_le_trans(clb, SolveFast.class_lb(ws),
        Sat.SB.child_cost(p, G, ws, inf), h1,
        FLB.FS.child_size_le(p, inf, G, ws, ble, hz, clt))
    case False{}:
      +hr : {Bool.and(nodup, LB2.all_usable_ge(G, ws, clb)) == True{} : Bool} =
        Equal.trans(Bool, Bool.and(nodup, LB2.all_usable_ge(G, ws, clb)),
          LB2.clb_ok_b(G, nodup, ws, clb), True{},
          Equal.cong(Bool, Bool,
            x => Bool.or(x, Bool.and(nodup, LB2.all_usable_ge(G, ws, clb))),
            False{}, Nat.is_le(clb, SolveFast.class_lb(ws)), elec), hok)
      +hall = Logic.Proof.and_true_r(nodup, LB2.all_usable_ge(G, ws, clb), hr)
      +cr : SolveRef.Best = FStep.FS.ref_run_at(p, inf, G, ws)
      ok : BO.BO.BestOK(inf, cr, G, ws) = MV.MV.main_ok(p, inf, G, ws, ble)
      v : Tree.Valid(Eval.Eval.tree_of(cr), G, ws) =
        SV.SV.valid_of_ok_lt(inf, cr, G, ws, clt, ok)
      +le1 = LB2.valid_tree_cost_ge(Eval.Eval.tree_of(cr), G, ws, clb, hall, v)
      cok : OC.OC.CJob(p, inf, G, ws) = FLB.FS.child_cost_ok(p, inf, G, ws, ble, hz)
      +le2 : {Nat.is_le(Tree.cost(Eval.Eval.tree_of(cr), ws),
                Sat.SB.child_cost(p, G, ws, inf)) == True{} : Bool} =
        cok(clt)
      NatProof.Nat.is_le_trans(clb, Tree.cost(Eval.Eval.tree_of(cr), ws),
        Sat.SB.child_cost(p, G, ws, inf), le1, le2)

def LB2.child_lb_le_ref(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +nodup: Bool, +ws: +List<+List<Nat>>, +clb: Nat,
    +ble: {Nat.is_le(Groups.len_words(ws), p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +clt: {Nat.is_lt(Sat.SB.child_cost(p, G, ws, inf), inf) == True{} : Bool},
    +hok: {LB2.clb_ok_b(G, nodup, ws, clb) == True{} : Bool}) ->
  {Nat.is_le(clb, Sat.SB.child_cost(p, G, ws, inf)) == True{} : Bool}:
  LB2.child_lb_le_ref_go(p, inf, G, nodup, ws, clb, ble, hz, clt,
    Nat.is_le(clb, SolveFast.class_lb(ws)), {==}, hok)

# ---------------------------------------------------------------------------
# Floor bounds: `init_floor(|ws|) <= lower_bound` and `2*|ws| <= lower_bound`
# ---------------------------------------------------------------------------

def LB2.len_le_class_lb_nodup(+ws: +List<+List<Nat>>,
    +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool}) ->
  {Nat.is_le(Groups.len_words(ws), SolveFast.class_lb(ws)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      +k : Nat = Groups.len_words(t)
      +eclb : {Nat.sub(Nat.add(1n+k, 1n+k), 1n) == SolveFast.class_lb(w <> t)
               : Nat} =
        FN.FN.class_lb_nodup_eq(w <> t, hnd)
      +esub : {Nat.sub(Nat.add(1n+k, 1n+k), 1n) == Nat.add(k, 1n+k) : Nat} =
        FLB.FS.sub_zero(Nat.add(k, 1n+k))
      +hle : {Nat.is_le(1n+k, Nat.add(k, 1n+k)) == True{} : Bool} =
        Fold.OQ.le_cong_r(1n+k, Nat.add(1n+k, k), Nat.add(k, 1n+k),
          NatProof.NatPrf.add_comm(1n+k, k),
          CBN.CB.is_le_add_self_r(1n+k, k))
      Fold.OQ.le_cong_r(1n+k, Nat.sub(Nat.add(1n+k, 1n+k), 1n),
        SolveFast.class_lb(w <> t), eclb,
        Fold.OQ.le_cong_r(1n+k, Nat.add(k, 1n+k),
          Nat.sub(Nat.add(1n+k, 1n+k), 1n),
          Equal.sym(Nat, Nat.sub(Nat.add(1n+k, 1n+k), 1n), Nat.add(k, 1n+k),
            esub), hle))

def LB2.sizes_le_class_words(+groups: +List<Groups.Group>,
    +hng: {FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(groups))
           == True{} : Bool}) ->
  {Nat.is_le(CBN.CB.sum(CBProof.CB.sizes(groups)),
             SolveFast.class_words(groups)) == True{} : Bool}:
  match groups:
    case Nil{}:
      {==}
    case Con{gp, +rest}:
      match gp:
        case Groups.Group{fb, +ws}:
          +hnd = Logic.Proof.and_true_l(FN.FN.no_dup_ref(ws),
                   FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(rest)), hng)
          +hrest = Logic.Proof.and_true_r(FN.FN.no_dup_ref(ws),
                     FN.FN.nodup_ok_jobs(True{}, MV.MV.next_groups(rest)), hng)
          CBN.CB.is_le_add(Groups.len_words(ws), SolveFast.class_lb(ws),
            CBN.CB.sum(CBProof.CB.sizes(rest)), SolveFast.class_words(rest),
            LB2.len_le_class_lb_nodup(ws, hnd),
            LB2.sizes_le_class_words(rest, hrest))

def LB2.pre_lb_le_lower_bound(+g: +List<Nat>, +ws: +List<+List<Nat>>,
    +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool}) ->
  {Nat.is_le(SolveFast.pre_lb(Groups.len_words(ws), g, ws),
             SolveFast.lower_bound(Groups.len_words(ws),
               Groups.groups_build(g, ws, Nil{}))) == True{} : Bool}:
  +n : Nat = Groups.len_words(ws)
  +gb = Groups.groups_build(g, ws, Nil{})
  +hng = FN.FN.nodup_ok_next_groups(True{}, gb, ws,
           Cgrp.Cover.all_subseq_nil(g, ws), hnd)
  +hsum = LB2.sizes_le_class_words(gb, hng)
  +hadd = NatProof.Nat.is_le_add_l(CBN.CB.sum(CBProof.CB.sizes(gb)),
            SolveFast.class_words(gb), n, hsum)
  Fold.OQ.le_cong_l(SolveFast.pre_lb(n, g, ws),
    Nat.add(n, CBN.CB.sum(CBProof.CB.sizes(gb))),
    SolveFast.lower_bound(n, gb),
    FLB.FS.pre_lb_partition_eq(g, ws),
    Fold.OQ.le_cong_r(Nat.add(n, CBN.CB.sum(CBProof.CB.sizes(gb))),
      Nat.add(n, SolveFast.class_words(gb)), SolveFast.lower_bound(n, gb),
      Equal.sym(Nat, SolveFast.lower_bound(n, gb),
        Nat.add(n, SolveFast.class_words(gb)),
        FLB.FS.lower_bound_eq(n, gb)), hadd))

def LB2.init_floor_le_lower_bound(+g: +List<Nat>, +ws: +List<+List<Nat>>,
    +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool}) ->
  {Nat.is_le(SolveFast.init_floor(Groups.len_words(ws)),
             SolveFast.lower_bound(Groups.len_words(ws),
               Groups.groups_build(g, ws, Nil{}))) == True{} : Bool}:
  NatProof.Nat.is_le_trans(
    SolveFast.init_floor(Groups.len_words(ws)),
    SolveFast.pre_lb(Groups.len_words(ws), g, ws),
    SolveFast.lower_bound(Groups.len_words(ws),
      Groups.groups_build(g, ws, Nil{})),
    FN.FN.floor_le_pre_lb(g, ws, hnd),
    LB2.pre_lb_le_lower_bound(g, ws, hnd))

def LB2.two_n_le_lower_bound(+g: +List<Nat>, +ws: +List<+List<Nat>>,
    +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool},
    +hnm: {Tree.member_word(g, ws) == False{} : Bool}) ->
  {Nat.is_le(Nat.add(Groups.len_words(ws), Groups.len_words(ws)),
             SolveFast.lower_bound(Groups.len_words(ws),
               Groups.groups_build(g, ws, Nil{}))) == True{} : Bool}:
  +n : Nat = Groups.len_words(ws)
  Fold.OQ.le_cong_l(Nat.add(n, n), SolveFast.pre_lb(n, g, ws),
    SolveFast.lower_bound(n, Groups.groups_build(g, ws, Nil{})),
    Equal.sym(Nat, SolveFast.pre_lb(n, g, ws), Nat.add(n, n),
      FN.FN.pre_lb_of_not_member(g, ws, hnm)),
    LB2.pre_lb_le_lower_bound(g, ws, hnd))

def LB2.usable_case_of_le(us: Bool, +lb: Nat, +v: Nat,
    +hle: {Nat.is_le(lb, v) == True{} : Bool}) ->
  {Feedback.Bool.case(Bool, us, Nat.is_le(lb, v), True{}) == True{} : Bool}:
  match us:
    case True{}:
      hle
    case False{}:
      {==}

def LB2.all_usable_ge_of_le_floor(+gs: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +lb: Nat,
    +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool},
    +hle: {Nat.is_le(lb, SolveFast.init_floor(Groups.len_words(ws)))
           == True{} : Bool}) ->
  {LB2.all_usable_ge(gs, ws, lb) == True{} : Bool}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      +us = Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
      +v = SolveFast.lower_bound(Groups.len_words(ws),
             Groups.groups_build(g, ws, Nil{}))
      +h1 = NatProof.Nat.is_le_trans(lb,
              SolveFast.init_floor(Groups.len_words(ws)), v, hle,
              LB2.init_floor_le_lower_bound(g, ws, hnd))
      LB2.bool_and_intro(
        Feedback.Bool.case(Bool, us, Nat.is_le(lb, v), True{}),
        LB2.all_usable_ge(rest, ws, lb),
        LB2.usable_case_of_le(us, lb, v, h1),
        LB2.all_usable_ge_of_le_floor(rest, ws, lb, hnd, hle))

def LB2.usable_case_of_2n_or_mem(+g: +List<Nat>, +ws: +List<+List<Nat>>,
    +lb: Nat, +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool},
    +hws: {LB2.all_usable_ge(ws, ws, lb) == True{} : Bool},
    +hle2n: {Nat.is_le(lb, Nat.add(Groups.len_words(ws), Groups.len_words(ws)))
             == True{} : Bool},
    mem: Bool, +emem: {mem == Tree.member_word(g, ws) : Bool},
    us: Bool,
    +eus: {us == Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
           : Bool}) ->
  {Feedback.Bool.case(Bool, us,
     Nat.is_le(lb, SolveFast.lower_bound(Groups.len_words(ws),
                     Groups.groups_build(g, ws, Nil{}))),
     True{}) == True{} : Bool}:
  match mem us:
    case _ False{}:
      {==}
    case True{} True{}:
      +hus : {Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
              == True{} : Bool} =
        Equal.sym(Bool, True{},
          Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{})), eus)
      +hmem : {Tree.member_word(g, ws) == True{} : Bool} =
        Equal.sym(Bool, True{}, Tree.member_word(g, ws), emem)
      LB2.all_usable_ge_at(ws, ws, lb, g, hmem, hws, hus)
    case False{} True{}:
      +hnm : {Tree.member_word(g, ws) == False{} : Bool} =
        Equal.sym(Bool, False{}, Tree.member_word(g, ws), emem)
      NatProof.Nat.is_le_trans(lb,
        Nat.add(Groups.len_words(ws), Groups.len_words(ws)),
        SolveFast.lower_bound(Groups.len_words(ws),
          Groups.groups_build(g, ws, Nil{})),
        hle2n, LB2.two_n_le_lower_bound(g, ws, hnd, hnm))

def LB2.all_usable_ge_of_le_2n(+gs: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +lb: Nat,
    +hnd: {FN.FN.no_dup_ref(ws) == True{} : Bool},
    +hws: {LB2.all_usable_ge(ws, ws, lb) == True{} : Bool},
    +hle2n: {Nat.is_le(lb, Nat.add(Groups.len_words(ws), Groups.len_words(ws)))
             == True{} : Bool}) ->
  {LB2.all_usable_ge(gs, ws, lb) == True{} : Bool}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      +us = Groups.groups_smaller(ws, Groups.groups_build(g, ws, Nil{}))
      +v = SolveFast.lower_bound(Groups.len_words(ws),
             Groups.groups_build(g, ws, Nil{}))
      LB2.bool_and_intro(
        Feedback.Bool.case(Bool, us, Nat.is_le(lb, v), True{}),
        LB2.all_usable_ge(rest, ws, lb),
        LB2.usable_case_of_2n_or_mem(g, ws, lb, hnd, hws, hle2n,
          Tree.member_word(g, ws), {==}, us, {==}),
        LB2.all_usable_ge_of_le_2n(rest, ws, lb, hnd, hws, hle2n))
