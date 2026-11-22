# Exact O(1) resolution of duplicate-free 3-word classes (`solve_three_tbl`).
#
# Proves:
# - `FT3.solve_three_tbl_ok`: given a valid feedback table `tbl`, valid
#   duplicate-free `CWord`s `cw1, cw2, cw3`, `SolveFast.solve_three_tbl`
#   preserves `tbl` unchanged and produces a tree and cost (`5n` or `6n`)
#   satisfying `FT3.done_three_ok_b`.
# - `FT3.done_three_le_ref`: any `(tree, cost)` satisfying `FT3.done_three_ok_b`
#   on a duplicate-free 3-word class `[w1, w2, w3]` has `cost <= ref_cost`
#   at any fuel `p >= 3` with `6 < inf`.
import Base
import ../src/feedback.bend as Feedback
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/solve_ref.bend as SolveRef
import ../src/solve_fast.bend as SolveFast
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./cover_list.bend as CoverList
import ./array.bend as Arr
import ./eval.bend as Eval
import ./nodevalid.bend as NV
import ./fast_step.bend as FS
import ./fast_one.bend as FO
import ./fast_nodup.bend as FN
import ./fast_lb.bend as FLB
import ./fast_valid.bend as FV
import ./fast_tbl.bend as FT

# ---------------------------------------------------------------------------
# Section 1: Pure `Bool` specification `FT3.done_three_ok_b` and `FT3.ThreeSpec`
# ---------------------------------------------------------------------------

def FT3.done_three_ok_b(+G: +List<+List<Nat>>,
    +w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    +tree: Tree.Tree, +cost: Nat) -> Bool:
  +ws3 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> Nil{}))
  Bool.and(FV.FV.valid_b(tree, G, ws3),
    Bool.and(Nat.is_le(Tree.cost(tree, ws3), cost),
      Bool.or(Nat.is_eq(cost, 5n),
        Bool.and(Nat.is_eq(cost, 6n),
          Bool.and(
            Feedback.feedback_eq(Feedback.feedback(w1, w2),
              Feedback.feedback(w1, w3)),
            Bool.and(
              Feedback.feedback_eq(Feedback.feedback(w2, w1),
                Feedback.feedback(w2, w3)),
              Feedback.feedback_eq(Feedback.feedback(w3, w1),
                Feedback.feedback(w3, w2))))))))

def FT3.ThreeSpec(+G: +List<+List<Nat>>,
    +w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    -tbl: Array<U32>, tr: SolveFast.ThreeRes) -> Data:
  match tr:
    case SolveFast.ThreeRes{tree, cost, tbl2}:
      Arr.Arr.DPair<
        {tbl2 == tbl : Array<U32>},
        {FT3.done_three_ok_b(G, w1, w2, w3, tree, cost) == True{} : Bool}>

def FT3.three_spec_transport_tbl(+G: +List<+List<Nat>>,
    +w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    -t1: Array<U32>, -t2: Array<U32>, -tr: SolveFast.ThreeRes,
    +et: {t1 == t2 : Array<U32>},
    +h: FT3.ThreeSpec(G, w1, w2, w3, t1, tr)) ->
  FT3.ThreeSpec(G, w1, w2, w3, t2, tr):
  %et : FT3.ThreeSpec(G, w1, w2, w3, _, tr)
  h

def FT3.done_three_valid_b(+G: +List<+List<Nat>>,
    +w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    +tree: Tree.Tree, +cost: Nat,
    +h: {FT3.done_three_ok_b(G, w1, w2, w3, tree, cost) == True{} : Bool}) ->
  {FV.FV.valid_b(tree, G, w1 <> (w2 <> (w3 <> Nil{}))) == True{} : Bool}:
  +ws3 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> Nil{}))
  Logic.Proof.and_true_l(FV.FV.valid_b(tree, G, ws3),
    Bool.and(Nat.is_le(Tree.cost(tree, ws3), cost),
      Bool.or(Nat.is_eq(cost, 5n),
        Bool.and(Nat.is_eq(cost, 6n),
          Bool.and(
            Feedback.feedback_eq(Feedback.feedback(w1, w2),
              Feedback.feedback(w1, w3)),
            Bool.and(
              Feedback.feedback_eq(Feedback.feedback(w2, w1),
                Feedback.feedback(w2, w3)),
              Feedback.feedback_eq(Feedback.feedback(w3, w1),
                Feedback.feedback(w3, w2))))))), h)

def FT3.done_three_cost_le(+G: +List<+List<Nat>>,
    +w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    +tree: Tree.Tree, +cost: Nat,
    +h: {FT3.done_three_ok_b(G, w1, w2, w3, tree, cost) == True{} : Bool}) ->
  {Nat.is_le(Tree.cost(tree, w1 <> (w2 <> (w3 <> Nil{}))), cost)
   == True{} : Bool}:
  +ws3 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> Nil{}))
  +r = Logic.Proof.and_true_r(FV.FV.valid_b(tree, G, ws3),
         Bool.and(Nat.is_le(Tree.cost(tree, ws3), cost),
           Bool.or(Nat.is_eq(cost, 5n),
             Bool.and(Nat.is_eq(cost, 6n),
               Bool.and(
                 Feedback.feedback_eq(Feedback.feedback(w1, w2),
                   Feedback.feedback(w1, w3)),
                 Bool.and(
                   Feedback.feedback_eq(Feedback.feedback(w2, w1),
                     Feedback.feedback(w2, w3)),
                   Feedback.feedback_eq(Feedback.feedback(w3, w1),
                     Feedback.feedback(w3, w2))))))), h)
  Logic.Proof.and_true_l(Nat.is_le(Tree.cost(tree, ws3), cost),
    Bool.or(Nat.is_eq(cost, 5n),
      Bool.and(Nat.is_eq(cost, 6n),
        Bool.and(
          Feedback.feedback_eq(Feedback.feedback(w1, w2),
            Feedback.feedback(w1, w3)),
          Bool.and(
            Feedback.feedback_eq(Feedback.feedback(w2, w1),
              Feedback.feedback(w2, w3)),
            Feedback.feedback_eq(Feedback.feedback(w3, w1),
              Feedback.feedback(w3, w2)))))), r)

# ---------------------------------------------------------------------------
# Section 2: Pairwise inequality extraction from `no_dup_ref([w1, w2, w3])`
# ---------------------------------------------------------------------------

def FT3.bool_case_false_l(a: Bool, +b: Bool,
    +e: {Feedback.Bool.case(Bool, a, True{}, b) == False{} : Bool}) ->
  {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Logic.Proof.true_ne_false(e))

def FT3.bool_case_false_r(a: Bool, +b: Bool,
    +e: {Feedback.Bool.case(Bool, a, True{}, b) == False{} : Bool}) ->
  {b == False{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      Empty.absurd({b == False{} : Bool}, Logic.Proof.true_ne_false(e))

def FT3.nd3_ne12(+w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    +nd: {FN.FN.no_dup_ref(w1 <> (w2 <> (w3 <> Nil{}))) == True{} : Bool}) ->
  {Feedback.word_eq(w1, w2) == False{} : Bool}:
  +nm = FN.FN.false_of_not_true(Tree.member_word(w1, w2 <> (w3 <> Nil{})),
          Logic.Proof.and_true_l(
            Bool.not(Tree.member_word(w1, w2 <> (w3 <> Nil{}))),
            FN.FN.no_dup_ref(w2 <> (w3 <> Nil{})), nd))
  FT3.bool_case_false_l(Feedback.word_eq(w1, w2),
    Tree.member_word(w1, w3 <> Nil{}), nm)

def FT3.nd3_ne13(+w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    +nd: {FN.FN.no_dup_ref(w1 <> (w2 <> (w3 <> Nil{}))) == True{} : Bool}) ->
  {Feedback.word_eq(w1, w3) == False{} : Bool}:
  +nm = FN.FN.false_of_not_true(Tree.member_word(w1, w2 <> (w3 <> Nil{})),
          Logic.Proof.and_true_l(
            Bool.not(Tree.member_word(w1, w2 <> (w3 <> Nil{}))),
            FN.FN.no_dup_ref(w2 <> (w3 <> Nil{})), nd))
  +nm3 = FT3.bool_case_false_r(Feedback.word_eq(w1, w2),
           Tree.member_word(w1, w3 <> Nil{}), nm)
  FV.FV.bool_case_id_false(Feedback.word_eq(w1, w3), nm3)

def FT3.nd3_ne23(+w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    +nd: {FN.FN.no_dup_ref(w1 <> (w2 <> (w3 <> Nil{}))) == True{} : Bool}) ->
  {Feedback.word_eq(w2, w3) == False{} : Bool}:
  +nd23 = Logic.Proof.and_true_r(
            Bool.not(Tree.member_word(w1, w2 <> (w3 <> Nil{}))),
            FN.FN.no_dup_ref(w2 <> (w3 <> Nil{})), nd)
  FV.FV.word_eq_false_of_no_dup_two(w2, w3, nd23)

# ---------------------------------------------------------------------------
# Section 3: Validity and exact cost for `three_tree_sep` and `three_tree_6`
# ---------------------------------------------------------------------------

def FT3.tree_valid_cost_3(+G: +List<+List<Nat>>, +t: Tree.Tree,
    +w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    +d1: Nat, +d2: Nat, +d3: Nat,
    +hti: {FV.FV.tree_in_b(t, G) == True{} : Bool},
    +ed1: {Tree.depth(t, w1) == Some{d1} : Maybe<Nat>},
    +ed2: {Tree.depth(t, w2) == Some{d2} : Maybe<Nat>},
    +ed3: {Tree.depth(t, w3) == Some{d3} : Maybe<Nat>}) ->
  Arr.Arr.DPair<
    {FV.FV.valid_b(t, G, w1 <> (w2 <> (w3 <> Nil{}))) == True{} : Bool},
    {Tree.cost(t, w1 <> (w2 <> (w3 <> Nil{})))
     == Nat.add(d1, Nat.add(d2, Nat.add(d3, 0n))) : Nat}>:
  +ws3 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> Nil{}))
  +hs1 : {Maybe.is_some(&1, Nat, Tree.depth(t, w1)) == True{} : Bool} =
    Equal.cong(Maybe<Nat>, Bool, m => Maybe.is_some(&1, Nat, m),
      Tree.depth(t, w1), Some{d1}, ed1)
  +hs2 : {Maybe.is_some(&1, Nat, Tree.depth(t, w2)) == True{} : Bool} =
    Equal.cong(Maybe<Nat>, Bool, m => Maybe.is_some(&1, Nat, m),
      Tree.depth(t, w2), Some{d2}, ed2)
  +hs3 : {Maybe.is_some(&1, Nat, Tree.depth(t, w3)) == True{} : Bool} =
    Equal.cong(Maybe<Nat>, Bool, m => Maybe.is_some(&1, Nat, m),
      Tree.depth(t, w3), Some{d3}, ed3)
  +hv : {FV.FV.valid_b(t, G, ws3) == True{} : Bool} =
    FO.FO.bool_and_intro(FV.FV.tree_in_b(t, G), FV.FV.all_have_depth_b(t, ws3),
      hti,
      FO.FO.bool_and_intro(Maybe.is_some(&1, Nat, Tree.depth(t, w1)),
        FV.FV.all_have_depth_b(t, w2 <> (w3 <> Nil{})), hs1,
        FO.FO.bool_and_intro(Maybe.is_some(&1, Nat, Tree.depth(t, w2)),
          FV.FV.all_have_depth_b(t, w3 <> Nil{}), hs2,
          FO.FO.bool_and_intro(Maybe.is_some(&1, Nat, Tree.depth(t, w3)),
            True{}, hs3, {==}))))
  +e1 : {Maybe.default(&1, Nat, Tree.depth(t, w1), 0n) == d1 : Nat} =
    Equal.cong(Maybe<Nat>, Nat, m => Maybe.default(&1, Nat, m, 0n),
      Tree.depth(t, w1), Some{d1}, ed1)
  +e2 : {Maybe.default(&1, Nat, Tree.depth(t, w2), 0n) == d2 : Nat} =
    Equal.cong(Maybe<Nat>, Nat, m => Maybe.default(&1, Nat, m, 0n),
      Tree.depth(t, w2), Some{d2}, ed2)
  +e3 : {Maybe.default(&1, Nat, Tree.depth(t, w3), 0n) == d3 : Nat} =
    Equal.cong(Maybe<Nat>, Nat, m => Maybe.default(&1, Nat, m, 0n),
      Tree.depth(t, w3), Some{d3}, ed3)
  +ec : {Tree.cost(t, ws3) == Nat.add(d1, Nat.add(d2, Nat.add(d3, 0n))) : Nat} =
    Equal.trans(Nat,
      Tree.cost(t, ws3),
      Nat.add(d1,
        Nat.add(Maybe.default(&1, Nat, Tree.depth(t, w2), 0n),
          Nat.add(Maybe.default(&1, Nat, Tree.depth(t, w3), 0n), 0n))),
      Nat.add(d1, Nat.add(d2, Nat.add(d3, 0n))),
      Equal.cong(Nat, Nat,
        x => Nat.add(x,
               Nat.add(Maybe.default(&1, Nat, Tree.depth(t, w2), 0n),
                 Nat.add(Maybe.default(&1, Nat, Tree.depth(t, w3), 0n), 0n))),
        Maybe.default(&1, Nat, Tree.depth(t, w1), 0n), d1, e1),
      Equal.trans(Nat,
        Nat.add(d1,
          Nat.add(Maybe.default(&1, Nat, Tree.depth(t, w2), 0n),
            Nat.add(Maybe.default(&1, Nat, Tree.depth(t, w3), 0n), 0n))),
        Nat.add(d1,
          Nat.add(d2,
            Nat.add(Maybe.default(&1, Nat, Tree.depth(t, w3), 0n), 0n))),
        Nat.add(d1, Nat.add(d2, Nat.add(d3, 0n))),
        Equal.cong(Nat, Nat,
          y => Nat.add(d1,
                 Nat.add(y,
                   Nat.add(Maybe.default(&1, Nat, Tree.depth(t, w3), 0n), 0n))),
          Maybe.default(&1, Nat, Tree.depth(t, w2), 0n), d2, e2),
        Equal.cong(Nat, Nat, z => Nat.add(d1, Nat.add(d2, Nat.add(z, 0n))),
          Maybe.default(&1, Nat, Tree.depth(t, w3), 0n), d3, e3)))
  Arr.DPair{hv, ec}

def FT3.three_tree_sep_in(+G: +List<+List<Nat>>,
    +g: +List<Nat>, +c1: U32, +wa: +List<Nat>, +c2: U32, +wb: +List<Nat>,
    +hg: {Tree.member_word(g, G) == True{} : Bool},
    +ha: {Tree.member_word(wa, G) == True{} : Bool},
    +hb: {Tree.member_word(wb, G) == True{} : Bool}) ->
  {FV.FV.tree_in_b(SolveFast.three_tree_sep(g, c1, wa, c2, wb), G)
   == True{} : Bool}:
  +ta : {FV.FV.tree_in_b(Tree.Node{wa, Nil{}}, G) == True{} : Bool} =
    FO.FO.bool_and_intro(Tree.member_word(wa, G), True{}, ha, {==})
  +tb : {FV.FV.tree_in_b(Tree.Node{wb, Nil{}}, G) == True{} : Bool} =
    FO.FO.bool_and_intro(Tree.member_word(wb, G), True{}, hb, {==})
  +k2 : {FV.FV.kids_in_b(
           Tree.Child{SolveFast.decode_fb5(c2), Tree.Node{wb, Nil{}}} <> Nil{}, G)
         == True{} : Bool} =
    FO.FO.bool_and_intro(FV.FV.tree_in_b(Tree.Node{wb, Nil{}}, G), True{},
      tb, {==})
  +k1 : {FV.FV.kids_in_b(
           Tree.Child{SolveFast.decode_fb5(c1), Tree.Node{wa, Nil{}}}
           <> (Tree.Child{SolveFast.decode_fb5(c2), Tree.Node{wb, Nil{}}} <> Nil{}),
           G) == True{} : Bool} =
    FO.FO.bool_and_intro(FV.FV.tree_in_b(Tree.Node{wa, Nil{}}, G),
      FV.FV.kids_in_b(
        Tree.Child{SolveFast.decode_fb5(c2), Tree.Node{wb, Nil{}}} <> Nil{}, G),
      ta, k2)
  FO.FO.bool_and_intro(Tree.member_word(g, G),
    FV.FV.kids_in_b(
      Tree.Child{SolveFast.decode_fb5(c1), Tree.Node{wa, Nil{}}}
      <> (Tree.Child{SolveFast.decode_fb5(c2), Tree.Node{wb, Nil{}}} <> Nil{}), G),
    hg, k1)

def FT3.three_tree_sep_depth_a(+g: +List<Nat>, +c1: U32, +wa: +List<Nat>,
    +c2: U32, +wb: +List<Nat>,
    +ec1: {c1 == FT.FT.fb_code_words(g, wa) : U32},
    +hg5: {SolveFast.is_len5(g) == True{} : Bool},
    +ha5: {SolveFast.is_len5(wa) == True{} : Bool},
    +hne: {Feedback.word_eq(g, wa) == False{} : Bool}) ->
  {Tree.depth(SolveFast.three_tree_sep(g, c1, wa, c2, wb), wa)
   == Some{2n} : Maybe<Nat>}:
  +fb1 = Feedback.feedback(g, wa)
  +dc1 = SolveFast.decode_fb5(c1)
  +kids : +List<Tree.Child> =
    Tree.Child{dc1, Tree.Node{wa, Nil{}}}
    <> (Tree.Child{SolveFast.decode_fb5(c2), Tree.Node{wb, Nil{}}} <> Nil{})
  +edec : {dc1 == fb1 : +List<Feedback.Color>} =
    Equal.trans(+List<Feedback.Color>, dc1,
      SolveFast.decode_fb5(FT.FT.fb_code_words(g, wa)), fb1,
      Equal.cong(U32, +List<Feedback.Color>, u => SolveFast.decode_fb5(u),
        c1, FT.FT.fb_code_words(g, wa), ec1),
      FT.FT.decode_fb_code(g, wa, hg5, ha5))
  +efbeq : {Feedback.feedback_eq(dc1, fb1) == True{} : Bool} =
    Equal.trans(Bool, Feedback.feedback_eq(dc1, fb1),
      Feedback.feedback_eq(fb1, fb1), True{},
      Equal.cong(+List<Feedback.Color>, Bool,
        x => Feedback.feedback_eq(x, fb1), dc1, fb1, edec),
      FbProof.FbPrf.feedback_eq_refl(fb1))
  +ego : {Tree.depth.go(kids, fb1, wa) == Some{1n} : Maybe<Nat>} =
    Equal.trans(Maybe<Nat>, Tree.depth.go(kids, fb1, wa),
      Tree.depth(Tree.Node{wa, Nil{}}, wa), Some{1n},
      NV.NV.depth_go_head_at(wa, fb1, dc1, Tree.Node{wa, Nil{}},
        Tree.Child{SolveFast.decode_fb5(c2), Tree.Node{wb, Nil{}}} <> Nil{},
        efbeq),
      FV.FV.depth_self(wa, Nil{}))
  Equal.trans(Maybe<Nat>,
    Tree.depth(Tree.Node{g, kids}, wa),
    Tree.depth.bump(Tree.depth.go(kids, fb1, wa)),
    Some{2n},
    Equal.cong(Bool, Maybe<Nat>,
      b => Feedback.Bool.case(Maybe<Nat>, b, Some{1n},
             Tree.depth.bump(Tree.depth.go(kids, fb1, wa))),
      Feedback.word_eq(g, wa), False{}, hne),
    Equal.cong(Maybe<Nat>, Maybe<Nat>, Tree.depth.bump,
      Tree.depth.go(kids, fb1, wa), Some{1n}, ego))

def FT3.three_tree_sep_depth_b(+g: +List<Nat>, +c1: U32, +wa: +List<Nat>,
    +c2: U32, +wb: +List<Nat>,
    +ec1: {c1 == FT.FT.fb_code_words(g, wa) : U32},
    +ec2: {c2 == FT.FT.fb_code_words(g, wb) : U32},
    +hg5: {SolveFast.is_len5(g) == True{} : Bool},
    +ha5: {SolveFast.is_len5(wa) == True{} : Bool},
    +hb5: {SolveFast.is_len5(wb) == True{} : Bool},
    +hne: {Feedback.word_eq(g, wb) == False{} : Bool},
    +hdiff: {U32.is_eq(c1, c2) == False{} : Bool}) ->
  {Tree.depth(SolveFast.three_tree_sep(g, c1, wa, c2, wb), wb)
   == Some{2n} : Maybe<Nat>}:
  +fb1 = Feedback.feedback(g, wa)
  +fb2 = Feedback.feedback(g, wb)
  +dc1 = SolveFast.decode_fb5(c1)
  +dc2 = SolveFast.decode_fb5(c2)
  +k2 : +List<Tree.Child> = Tree.Child{dc2, Tree.Node{wb, Nil{}}} <> Nil{}
  +kids : +List<Tree.Child> = Tree.Child{dc1, Tree.Node{wa, Nil{}}} <> k2
  +edec1 : {dc1 == fb1 : +List<Feedback.Color>} =
    Equal.trans(+List<Feedback.Color>, dc1,
      SolveFast.decode_fb5(FT.FT.fb_code_words(g, wa)), fb1,
      Equal.cong(U32, +List<Feedback.Color>, u => SolveFast.decode_fb5(u),
        c1, FT.FT.fb_code_words(g, wa), ec1),
      FT.FT.decode_fb_code(g, wa, hg5, ha5))
  +edec2 : {dc2 == fb2 : +List<Feedback.Color>} =
    Equal.trans(+List<Feedback.Color>, dc2,
      SolveFast.decode_fb5(FT.FT.fb_code_words(g, wb)), fb2,
      Equal.cong(U32, +List<Feedback.Color>, u => SolveFast.decode_fb5(u),
        c2, FT.FT.fb_code_words(g, wb), ec2),
      FT.FT.decode_fb_code(g, wb, hg5, hb5))
  +efb12 : {Feedback.feedback_eq(fb1, fb2) == False{} : Bool} =
    Equal.trans(Bool,
      Feedback.feedback_eq(fb1, fb2),
      U32.is_eq(FT.FT.fb_code_words(g, wa), FT.FT.fb_code_words(g, wb)),
      False{},
      Equal.sym(Bool,
        U32.is_eq(FT.FT.fb_code_words(g, wa), FT.FT.fb_code_words(g, wb)),
        Feedback.feedback_eq(fb1, fb2),
        FT.FT.fb_code_eq_iff(g, wa, g, wb, hg5, ha5, hg5, hb5)),
      Equal.trans(Bool,
        U32.is_eq(FT.FT.fb_code_words(g, wa), FT.FT.fb_code_words(g, wb)),
        U32.is_eq(c1, c2), False{},
        Equal.trans(Bool,
          U32.is_eq(FT.FT.fb_code_words(g, wa), FT.FT.fb_code_words(g, wb)),
          U32.is_eq(c1, FT.FT.fb_code_words(g, wb)),
          U32.is_eq(c1, c2),
          Equal.cong(U32, Bool,
            u => U32.is_eq(u, FT.FT.fb_code_words(g, wb)),
            FT.FT.fb_code_words(g, wa), c1,
            Equal.sym(U32, c1, FT.FT.fb_code_words(g, wa), ec1)),
          Equal.cong(U32, Bool, u => U32.is_eq(c1, u),
            FT.FT.fb_code_words(g, wb), c2,
            Equal.sym(U32, c2, FT.FT.fb_code_words(g, wb), ec2))),
        hdiff))
  +eskip_b : {Feedback.feedback_eq(dc1, fb2) == False{} : Bool} =
    Equal.trans(Bool, Feedback.feedback_eq(dc1, fb2),
      Feedback.feedback_eq(fb1, fb2), False{},
      Equal.cong(+List<Feedback.Color>, Bool,
        x => Feedback.feedback_eq(x, fb2), dc1, fb1, edec1),
      efb12)
  +efbeq2 : {Feedback.feedback_eq(dc2, fb2) == True{} : Bool} =
    Equal.trans(Bool, Feedback.feedback_eq(dc2, fb2),
      Feedback.feedback_eq(fb2, fb2), True{},
      Equal.cong(+List<Feedback.Color>, Bool,
        x => Feedback.feedback_eq(x, fb2), dc2, fb2, edec2),
      FbProof.FbPrf.feedback_eq_refl(fb2))
  +ego : {Tree.depth.go(kids, fb2, wb) == Some{1n} : Maybe<Nat>} =
    Equal.trans(Maybe<Nat>,
      Tree.depth.go(kids, fb2, wb),
      Tree.depth.go(k2, fb2, wb),
      Some{1n},
      NV.NV.depth_go_skip(wb, fb2, dc1, Tree.Node{wa, Nil{}}, k2, eskip_b),
      Equal.trans(Maybe<Nat>,
        Tree.depth.go(k2, fb2, wb),
        Tree.depth(Tree.Node{wb, Nil{}}, wb),
        Some{1n},
        NV.NV.depth_go_head_at(wb, fb2, dc2, Tree.Node{wb, Nil{}}, Nil{}, efbeq2),
        FV.FV.depth_self(wb, Nil{})))
  Equal.trans(Maybe<Nat>,
    Tree.depth(Tree.Node{g, kids}, wb),
    Tree.depth.bump(Tree.depth.go(kids, fb2, wb)),
    Some{2n},
    Equal.cong(Bool, Maybe<Nat>,
      b => Feedback.Bool.case(Maybe<Nat>, b, Some{1n},
             Tree.depth.bump(Tree.depth.go(kids, fb2, wb))),
      Feedback.word_eq(g, wb), False{}, hne),
    Equal.cong(Maybe<Nat>, Maybe<Nat>, Tree.depth.bump,
      Tree.depth.go(kids, fb2, wb), Some{1n}, ego))

def FT3.done_three_5_intro(+G: +List<+List<Nat>>,
    +w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    +t: Tree.Tree,
    +hv: {FV.FV.valid_b(t, G, w1 <> (w2 <> (w3 <> Nil{}))) == True{} : Bool},
    +ec: {Tree.cost(t, w1 <> (w2 <> (w3 <> Nil{}))) == 5n : Nat}) ->
  {FT3.done_three_ok_b(G, w1, w2, w3, t, 5n) == True{} : Bool}:
  +ws3 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> Nil{}))
  +hle : {Nat.is_le(Tree.cost(t, ws3), 5n) == True{} : Bool} =
    Equal.cong(Nat, Bool, x => Nat.is_le(x, 5n), Tree.cost(t, ws3), 5n, ec)
  FO.FO.bool_and_intro(FV.FV.valid_b(t, G, ws3),
    Bool.and(Nat.is_le(Tree.cost(t, ws3), 5n), True{}),
    hv, FO.FO.bool_and_intro(Nat.is_le(Tree.cost(t, ws3), 5n), True{}, hle, {==}))

def FT3.three_tree_6_ok(+G: +List<+List<Nat>>,
    +w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    +c12: U32, +c23: U32,
    +h1: {Tree.member_word(w1, G) == True{} : Bool},
    +h2: {Tree.member_word(w2, G) == True{} : Bool},
    +h3: {Tree.member_word(w3, G) == True{} : Bool},
    +h15: {SolveFast.is_len5(w1) == True{} : Bool},
    +h25: {SolveFast.is_len5(w2) == True{} : Bool},
    +h35: {SolveFast.is_len5(w3) == True{} : Bool},
    +ec12: {c12 == FT.FT.fb_code_words(w1, w2) : U32},
    +ec23: {c23 == FT.FT.fb_code_words(w2, w3) : U32},
    +hne12: {Feedback.word_eq(w1, w2) == False{} : Bool},
    +hne13: {Feedback.word_eq(w1, w3) == False{} : Bool},
    +hne23: {Feedback.word_eq(w2, w3) == False{} : Bool},
    +efb1: {Feedback.feedback_eq(Feedback.feedback(w1, w2),
              Feedback.feedback(w1, w3)) == True{} : Bool},
    +efb2: {Feedback.feedback_eq(Feedback.feedback(w2, w1),
              Feedback.feedback(w2, w3)) == True{} : Bool},
    +efb3: {Feedback.feedback_eq(Feedback.feedback(w3, w1),
              Feedback.feedback(w3, w2)) == True{} : Bool}) ->
  {FT3.done_three_ok_b(G, w1, w2, w3,
     SolveFast.three_tree_6(w1, c12, w2, c23, w3), 6n) == True{} : Bool}:
  +dc12 = SolveFast.decode_fb5(c12)
  +dc23 = SolveFast.decode_fb5(c23)
  +sub2 : Tree.Tree = Tree.Node{w2, Tree.Child{dc23, Tree.Node{w3, Nil{}}} <> Nil{}}
  +kids1 : +List<Tree.Child> = Tree.Child{dc12, sub2} <> Nil{}
  +t = SolveFast.three_tree_6(w1, c12, w2, c23, w3)
  +ws3 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> Nil{}))
  +hti3 : {FV.FV.tree_in_b(Tree.Node{w3, Nil{}}, G) == True{} : Bool} =
    FO.FO.bool_and_intro(Tree.member_word(w3, G), True{}, h3, {==})
  +hti2 : {FV.FV.tree_in_b(sub2, G) == True{} : Bool} =
    FO.FO.bool_and_intro(Tree.member_word(w2, G),
      FV.FV.kids_in_b(Tree.Child{dc23, Tree.Node{w3, Nil{}}} <> Nil{}, G),
      h2, FO.FO.bool_and_intro(FV.FV.tree_in_b(Tree.Node{w3, Nil{}}, G),
            True{}, hti3, {==}))
  +hti : {FV.FV.tree_in_b(t, G) == True{} : Bool} =
    FO.FO.bool_and_intro(Tree.member_word(w1, G),
      FV.FV.kids_in_b(kids1, G),
      h1, FO.FO.bool_and_intro(FV.FV.tree_in_b(sub2, G), True{}, hti2, {==}))
  +edec12 : {dc12 == Feedback.feedback(w1, w2) : +List<Feedback.Color>} =
    Equal.trans(+List<Feedback.Color>, dc12,
      SolveFast.decode_fb5(FT.FT.fb_code_words(w1, w2)),
      Feedback.feedback(w1, w2),
      Equal.cong(U32, +List<Feedback.Color>, u => SolveFast.decode_fb5(u),
        c12, FT.FT.fb_code_words(w1, w2), ec12),
      FT.FT.decode_fb_code(w1, w2, h15, h25))
  +edec23 : {dc23 == Feedback.feedback(w2, w3) : +List<Feedback.Color>} =
    Equal.trans(+List<Feedback.Color>, dc23,
      SolveFast.decode_fb5(FT.FT.fb_code_words(w2, w3)),
      Feedback.feedback(w2, w3),
      Equal.cong(U32, +List<Feedback.Color>, u => SolveFast.decode_fb5(u),
        c23, FT.FT.fb_code_words(w2, w3), ec23),
      FT.FT.decode_fb_code(w2, w3, h25, h35))
  +ed1 : {Tree.depth(t, w1) == Some{1n} : Maybe<Nat>} =
    FV.FV.depth_self(w1, kids1)
  +ef12 : {Feedback.feedback_eq(dc12, Feedback.feedback(w1, w2)) == True{} : Bool} =
    Equal.trans(Bool, Feedback.feedback_eq(dc12, Feedback.feedback(w1, w2)),
      Feedback.feedback_eq(Feedback.feedback(w1, w2), Feedback.feedback(w1, w2)),
      True{},
      Equal.cong(+List<Feedback.Color>, Bool,
        x => Feedback.feedback_eq(x, Feedback.feedback(w1, w2)),
        dc12, Feedback.feedback(w1, w2), edec12),
      FbProof.FbPrf.feedback_eq_refl(Feedback.feedback(w1, w2)))
  +ego2 : {Tree.depth.go(kids1, Feedback.feedback(w1, w2), w2)
           == Some{1n} : Maybe<Nat>} =
    Equal.trans(Maybe<Nat>,
      Tree.depth.go(kids1, Feedback.feedback(w1, w2), w2),
      Tree.depth(sub2, w2), Some{1n},
      NV.NV.depth_go_head_at(w2, Feedback.feedback(w1, w2), dc12, sub2, Nil{},
        ef12),
      FV.FV.depth_self(w2, Tree.Child{dc23, Tree.Node{w3, Nil{}}} <> Nil{}))
  +ed2 : {Tree.depth(t, w2) == Some{2n} : Maybe<Nat>} =
    Equal.trans(Maybe<Nat>,
      Tree.depth(t, w2),
      Tree.depth.bump(Tree.depth.go(kids1, Feedback.feedback(w1, w2), w2)),
      Some{2n},
      Equal.cong(Bool, Maybe<Nat>,
        b => Feedback.Bool.case(Maybe<Nat>, b, Some{1n},
               Tree.depth.bump(Tree.depth.go(kids1, Feedback.feedback(w1, w2), w2))),
        Feedback.word_eq(w1, w2), False{}, hne12),
      Equal.cong(Maybe<Nat>, Maybe<Nat>, Tree.depth.bump,
        Tree.depth.go(kids1, Feedback.feedback(w1, w2), w2), Some{1n}, ego2))
  +ef23 : {Feedback.feedback_eq(dc23, Feedback.feedback(w2, w3)) == True{} : Bool} =
    Equal.trans(Bool, Feedback.feedback_eq(dc23, Feedback.feedback(w2, w3)),
      Feedback.feedback_eq(Feedback.feedback(w2, w3), Feedback.feedback(w2, w3)),
      True{},
      Equal.cong(+List<Feedback.Color>, Bool,
        x => Feedback.feedback_eq(x, Feedback.feedback(w2, w3)),
        dc23, Feedback.feedback(w2, w3), edec23),
      FbProof.FbPrf.feedback_eq_refl(Feedback.feedback(w2, w3)))
  +ego3_in : {Tree.depth.go(Tree.Child{dc23, Tree.Node{w3, Nil{}}} <> Nil{},
                Feedback.feedback(w2, w3), w3) == Some{1n} : Maybe<Nat>} =
    Equal.trans(Maybe<Nat>,
      Tree.depth.go(Tree.Child{dc23, Tree.Node{w3, Nil{}}} <> Nil{},
        Feedback.feedback(w2, w3), w3),
      Tree.depth(Tree.Node{w3, Nil{}}, w3), Some{1n},
      NV.NV.depth_go_head_at(w3, Feedback.feedback(w2, w3), dc23,
        Tree.Node{w3, Nil{}}, Nil{}, ef23),
      FV.FV.depth_self(w3, Nil{}))
  +ed3_sub : {Tree.depth(sub2, w3) == Some{2n} : Maybe<Nat>} =
    Equal.trans(Maybe<Nat>,
      Tree.depth(sub2, w3),
      Tree.depth.bump(Tree.depth.go(
        Tree.Child{dc23, Tree.Node{w3, Nil{}}} <> Nil{},
        Feedback.feedback(w2, w3), w3)),
      Some{2n},
      Equal.cong(Bool, Maybe<Nat>,
        b => Feedback.Bool.case(Maybe<Nat>, b, Some{1n},
               Tree.depth.bump(Tree.depth.go(
                 Tree.Child{dc23, Tree.Node{w3, Nil{}}} <> Nil{},
                 Feedback.feedback(w2, w3), w3))),
        Feedback.word_eq(w2, w3), False{}, hne23),
      Equal.cong(Maybe<Nat>, Maybe<Nat>, Tree.depth.bump,
        Tree.depth.go(Tree.Child{dc23, Tree.Node{w3, Nil{}}} <> Nil{},
          Feedback.feedback(w2, w3), w3), Some{1n}, ego3_in))
  +ef13 : {Feedback.feedback_eq(dc12, Feedback.feedback(w1, w3)) == True{} : Bool} =
    Equal.trans(Bool, Feedback.feedback_eq(dc12, Feedback.feedback(w1, w3)),
      Feedback.feedback_eq(Feedback.feedback(w1, w2), Feedback.feedback(w1, w3)),
      True{},
      Equal.cong(+List<Feedback.Color>, Bool,
        x => Feedback.feedback_eq(x, Feedback.feedback(w1, w3)),
        dc12, Feedback.feedback(w1, w2), edec12),
      efb1)
  +ego3 : {Tree.depth.go(kids1, Feedback.feedback(w1, w3), w3)
           == Some{2n} : Maybe<Nat>} =
    Equal.trans(Maybe<Nat>,
      Tree.depth.go(kids1, Feedback.feedback(w1, w3), w3),
      Tree.depth(sub2, w3), Some{2n},
      NV.NV.depth_go_head_at(w3, Feedback.feedback(w1, w3), dc12, sub2, Nil{},
        ef13),
      ed3_sub)
  +ed3 : {Tree.depth(t, w3) == Some{3n} : Maybe<Nat>} =
    Equal.trans(Maybe<Nat>,
      Tree.depth(t, w3),
      Tree.depth.bump(Tree.depth.go(kids1, Feedback.feedback(w1, w3), w3)),
      Some{3n},
      Equal.cong(Bool, Maybe<Nat>,
        b => Feedback.Bool.case(Maybe<Nat>, b, Some{1n},
               Tree.depth.bump(Tree.depth.go(kids1, Feedback.feedback(w1, w3), w3))),
        Feedback.word_eq(w1, w3), False{}, hne13),
      Equal.cong(Maybe<Nat>, Maybe<Nat>, Tree.depth.bump,
        Tree.depth.go(kids1, Feedback.feedback(w1, w3), w3), Some{2n}, ego3))
  +vc = FT3.tree_valid_cost_3(G, t, w1, w2, w3, 1n, 2n, 3n, hti, ed1, ed2, ed3)
  +hv = Arr.Arr.dpair_l({FV.FV.valid_b(t, G, ws3) == True{} : Bool},
          {Tree.cost(t, ws3) == 6n : Nat}, vc)
  +ec = Arr.Arr.dpair_r({FV.FV.valid_b(t, G, ws3) == True{} : Bool},
          {Tree.cost(t, ws3) == 6n : Nat}, vc)
  +hle : {Nat.is_le(Tree.cost(t, ws3), 6n) == True{} : Bool} =
    Equal.cong(Nat, Bool, x => Nat.is_le(x, 6n), Tree.cost(t, ws3), 6n, ec)
  +heqs : {Bool.and(
             Feedback.feedback_eq(Feedback.feedback(w1, w2),
               Feedback.feedback(w1, w3)),
             Bool.and(
               Feedback.feedback_eq(Feedback.feedback(w2, w1),
                 Feedback.feedback(w2, w3)),
               Feedback.feedback_eq(Feedback.feedback(w3, w1),
                 Feedback.feedback(w3, w2)))) == True{} : Bool} =
    FO.FO.bool_and_intro(
      Feedback.feedback_eq(Feedback.feedback(w1, w2), Feedback.feedback(w1, w3)),
      Bool.and(
        Feedback.feedback_eq(Feedback.feedback(w2, w1), Feedback.feedback(w2, w3)),
        Feedback.feedback_eq(Feedback.feedback(w3, w1), Feedback.feedback(w3, w2))),
      efb1,
      FO.FO.bool_and_intro(
        Feedback.feedback_eq(Feedback.feedback(w2, w1), Feedback.feedback(w2, w3)),
        Feedback.feedback_eq(Feedback.feedback(w3, w1), Feedback.feedback(w3, w2)),
        efb2, efb3))
  FO.FO.bool_and_intro(FV.FV.valid_b(t, G, ws3),
    Bool.and(Nat.is_le(Tree.cost(t, ws3), 6n),
      Bool.and(
        Feedback.feedback_eq(Feedback.feedback(w1, w2), Feedback.feedback(w1, w3)),
        Bool.and(
          Feedback.feedback_eq(Feedback.feedback(w2, w1), Feedback.feedback(w2, w3)),
          Feedback.feedback_eq(Feedback.feedback(w3, w1), Feedback.feedback(w3, w2))))),
    hv,
    FO.FO.bool_and_intro(Nat.is_le(Tree.cost(t, ws3), 6n),
      Bool.and(
        Feedback.feedback_eq(Feedback.feedback(w1, w2), Feedback.feedback(w1, w3)),
        Bool.and(
          Feedback.feedback_eq(Feedback.feedback(w2, w1), Feedback.feedback(w2, w3)),
          Feedback.feedback_eq(Feedback.feedback(w3, w1), Feedback.feedback(w3, w2)))),
      hle, heqs))

# ---------------------------------------------------------------------------
# Section 4: `FT3.solve_three_tbl_ok` (table-lookup proof)
# ---------------------------------------------------------------------------

def FT3.fb_eq_of_u32_eq(+g: +List<Nat>, +wa: +List<Nat>, +wb: +List<Nat>,
    +ca: U32, +cb: U32,
    +hg5: {SolveFast.is_len5(g) == True{} : Bool},
    +ha5: {SolveFast.is_len5(wa) == True{} : Bool},
    +hb5: {SolveFast.is_len5(wb) == True{} : Bool},
    +eca: {ca == FT.FT.fb_code_words(g, wa) : U32},
    +ecb: {cb == FT.FT.fb_code_words(g, wb) : U32},
    +heq: {U32.is_eq(ca, cb) == True{} : Bool}) ->
  {Feedback.feedback_eq(Feedback.feedback(g, wa), Feedback.feedback(g, wb))
   == True{} : Bool}:
  Equal.trans(Bool,
    Feedback.feedback_eq(Feedback.feedback(g, wa), Feedback.feedback(g, wb)),
    U32.is_eq(FT.FT.fb_code_words(g, wa), FT.FT.fb_code_words(g, wb)),
    True{},
    Equal.sym(Bool,
      U32.is_eq(FT.FT.fb_code_words(g, wa), FT.FT.fb_code_words(g, wb)),
      Feedback.feedback_eq(Feedback.feedback(g, wa), Feedback.feedback(g, wb)),
      FT.FT.fb_code_eq_iff(g, wa, g, wb, hg5, ha5, hg5, hb5)),
    Equal.trans(Bool,
      U32.is_eq(FT.FT.fb_code_words(g, wa), FT.FT.fb_code_words(g, wb)),
      U32.is_eq(ca, cb), True{},
      Equal.trans(Bool,
        U32.is_eq(FT.FT.fb_code_words(g, wa), FT.FT.fb_code_words(g, wb)),
        U32.is_eq(ca, FT.FT.fb_code_words(g, wb)),
        U32.is_eq(ca, cb),
        Equal.cong(U32, Bool,
          u => U32.is_eq(u, FT.FT.fb_code_words(g, wb)),
          FT.FT.fb_code_words(g, wa), ca,
          Equal.sym(U32, ca, FT.FT.fb_code_words(g, wa), eca)),
        Equal.cong(U32, Bool, u => U32.is_eq(ca, u),
          FT.FT.fb_code_words(g, wb), cb,
          Equal.sym(U32, cb, FT.FT.fb_code_words(g, wb), ecb))),
      heq))

def FT3.three_s3_cmp_ok(+G: +List<+List<Nat>>,
    +w1: +List<Nat>, +c12: U32, +w2: +List<Nat>, +c23: U32,
    +w3: +List<Nat>, +c31: U32, +c32: U32,
    same: Bool, tbl: Array<U32>,
    +esame: {same == U32.is_eq(c31, c32) : Bool},
    +h1: {Tree.member_word(w1, G) == True{} : Bool},
    +h2: {Tree.member_word(w2, G) == True{} : Bool},
    +h3: {Tree.member_word(w3, G) == True{} : Bool},
    +h15: {SolveFast.is_len5(w1) == True{} : Bool},
    +h25: {SolveFast.is_len5(w2) == True{} : Bool},
    +h35: {SolveFast.is_len5(w3) == True{} : Bool},
    +ec12: {c12 == FT.FT.fb_code_words(w1, w2) : U32},
    +ec23: {c23 == FT.FT.fb_code_words(w2, w3) : U32},
    +ec31: {c31 == FT.FT.fb_code_words(w3, w1) : U32},
    +ec32: {c32 == FT.FT.fb_code_words(w3, w2) : U32},
    +hne12: {Feedback.word_eq(w1, w2) == False{} : Bool},
    +hne13: {Feedback.word_eq(w1, w3) == False{} : Bool},
    +hne23: {Feedback.word_eq(w2, w3) == False{} : Bool},
    +efb1: {Feedback.feedback_eq(Feedback.feedback(w1, w2),
              Feedback.feedback(w1, w3)) == True{} : Bool},
    +efb2: {Feedback.feedback_eq(Feedback.feedback(w2, w1),
              Feedback.feedback(w2, w3)) == True{} : Bool}) ->
  FT3.ThreeSpec(G, w1, w2, w3, tbl,
    SolveFast.three_s3_cmp(w1, c12, w2, c23, w3, c31, c32, same, tbl)):
  match same:
    case False{}:
      +hdiff : {U32.is_eq(c31, c32) == False{} : Bool} =
        Equal.sym(Bool, False{}, U32.is_eq(c31, c32), esame)
      +t = SolveFast.three_tree_sep(w3, c31, w1, c32, w2)
      +hti = FT3.three_tree_sep_in(G, w3, c31, w1, c32, w2, h3, h1, h2)
      +ed1 = FT3.three_tree_sep_depth_a(w3, c31, w1, c32, w2, ec31, h35, h15,
               FO.FO.word_eq_sym_false(w1, w3, hne13))
      +ed2 = FT3.three_tree_sep_depth_b(w3, c31, w1, c32, w2, ec31, ec32,
               h35, h15, h25, FO.FO.word_eq_sym_false(w2, w3, hne23), hdiff)
      +ed3 = FV.FV.depth_self(w3,
               Tree.Child{SolveFast.decode_fb5(c31), Tree.Node{w1, Nil{}}}
               <> (Tree.Child{SolveFast.decode_fb5(c32), Tree.Node{w2, Nil{}}} <> Nil{}))
      +vc = FT3.tree_valid_cost_3(G, t, w1, w2, w3, 2n, 2n, 1n, hti, ed1, ed2, ed3)
      +hv = Arr.Arr.dpair_l(
              {FV.FV.valid_b(t, G, w1 <> (w2 <> (w3 <> Nil{}))) == True{} : Bool},
              {Tree.cost(t, w1 <> (w2 <> (w3 <> Nil{}))) == 5n : Nat}, vc)
      +ec = Arr.Arr.dpair_r(
              {FV.FV.valid_b(t, G, w1 <> (w2 <> (w3 <> Nil{}))) == True{} : Bool},
              {Tree.cost(t, w1 <> (w2 <> (w3 <> Nil{}))) == 5n : Nat}, vc)
      Arr.DPair{{==}, FT3.done_three_5_intro(G, w1, w2, w3, t, hv, ec)}
    case True{}:
      +heq : {U32.is_eq(c31, c32) == True{} : Bool} =
        Equal.sym(Bool, True{}, U32.is_eq(c31, c32), esame)
      +efb3 = FT3.fb_eq_of_u32_eq(w3, w1, w2, c31, c32, h35, h15, h25,
                ec31, ec32, heq)
      Arr.DPair{{==},
        FT3.three_tree_6_ok(G, w1, w2, w3, c12, c23, h1, h2, h3, h15, h25, h35,
          ec12, ec23, hne12, hne13, hne23, efb1, efb2, efb3)}

def FT3.three_s2_cmp_ok(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    +ci1: U32, +w1: +List<Nat>, +c12: U32,
    +ci2: U32, +w2: +List<Nat>, +c21: U32, +c23: U32,
    +gr3: U32, +w3: +List<Nat>,
    same: Bool, tbl: Array<U32>,
    +esame: {same == U32.is_eq(c21, c23) : Bool},
    +htbl: FT.FT.TblOk(G, C, n, tbl),
    +hcol1: {FT.FT.has_col_go(C, ci1, w1, 0n) == True{} : Bool},
    +hcol2: {FT.FT.has_col_go(C, ci2, w2, 0n) == True{} : Bool},
    +hrow3: {FT.FT.gentry_ok_b(G, n, gr3, w3) == True{} : Bool},
    +h1: {Tree.member_word(w1, G) == True{} : Bool},
    +h2: {Tree.member_word(w2, G) == True{} : Bool},
    +h3: {Tree.member_word(w3, G) == True{} : Bool},
    +h15: {SolveFast.is_len5(w1) == True{} : Bool},
    +h25: {SolveFast.is_len5(w2) == True{} : Bool},
    +h35: {SolveFast.is_len5(w3) == True{} : Bool},
    +ec12: {c12 == FT.FT.fb_code_words(w1, w2) : U32},
    +ec21: {c21 == FT.FT.fb_code_words(w2, w1) : U32},
    +ec23: {c23 == FT.FT.fb_code_words(w2, w3) : U32},
    +hne12: {Feedback.word_eq(w1, w2) == False{} : Bool},
    +hne13: {Feedback.word_eq(w1, w3) == False{} : Bool},
    +hne23: {Feedback.word_eq(w2, w3) == False{} : Bool},
    +efb1: {Feedback.feedback_eq(Feedback.feedback(w1, w2),
              Feedback.feedback(w1, w3)) == True{} : Bool}) ->
  FT3.ThreeSpec(G, w1, w2, w3, tbl,
    SolveFast.three_s2_cmp(ci1, w1, c12, ci2, w2, c21, c23, gr3, w3, same, tbl)):
  match same:
    case False{}:
      +hdiff : {U32.is_eq(c21, c23) == False{} : Bool} =
        Equal.sym(Bool, False{}, U32.is_eq(c21, c23), esame)
      +t = SolveFast.three_tree_sep(w2, c21, w1, c23, w3)
      +hti = FT3.three_tree_sep_in(G, w2, c21, w1, c23, w3, h2, h1, h3)
      +ed1 = FT3.three_tree_sep_depth_a(w2, c21, w1, c23, w3, ec21, h25, h15,
               FO.FO.word_eq_sym_false(w1, w2, hne12))
      +ed2 = FV.FV.depth_self(w2,
               Tree.Child{SolveFast.decode_fb5(c21), Tree.Node{w1, Nil{}}}
               <> (Tree.Child{SolveFast.decode_fb5(c23), Tree.Node{w3, Nil{}}} <> Nil{}))
      +ed3 = FT3.three_tree_sep_depth_b(w2, c21, w1, c23, w3, ec21, ec23,
               h25, h15, h35, hne23, hdiff)
      +vc = FT3.tree_valid_cost_3(G, t, w1, w2, w3, 2n, 1n, 2n, hti, ed1, ed2, ed3)
      +hv = Arr.Arr.dpair_l(
              {FV.FV.valid_b(t, G, w1 <> (w2 <> (w3 <> Nil{}))) == True{} : Bool},
              {Tree.cost(t, w1 <> (w2 <> (w3 <> Nil{}))) == 5n : Nat}, vc)
      +ec = Arr.Arr.dpair_r(
              {FV.FV.valid_b(t, G, w1 <> (w2 <> (w3 <> Nil{}))) == True{} : Bool},
              {Tree.cost(t, w1 <> (w2 <> (w3 <> Nil{}))) == 5n : Nat}, vc)
      Arr.DPair{{==}, FT3.done_three_5_intro(G, w1, w2, w3, t, hv, ec)}
    case True{}:
      +heq : {U32.is_eq(c21, c23) == True{} : Bool} =
        Equal.sym(Bool, True{}, U32.is_eq(c21, c23), esame)
      +efb2 = FT3.fb_eq_of_u32_eq(w2, w1, w3, c21, c23, h25, h15, h35,
                ec21, ec23, heq)
      FT.FT.tbl_get_use(
        r => FT3.ThreeSpec(G, w1, w2, w3, tbl,
               SolveFast.three_s3_a(w1, c12, ci2, w2, c23, gr3, w3, r)),
        G, C, n, gr3, w3, ci1, w1, tbl, htbl, hrow3, hcol1,
        t1 => +c31 => +et1 => +htbl1 => +ec31 => +hg35 => +hw15 =>
          FT.FT.tbl_get_use(
            r2 => FT3.ThreeSpec(G, w1, w2, w3, tbl,
                    SolveFast.three_s3_b(w1, c12, w2, c23, w3, c31, r2)),
            G, C, n, gr3, w3, ci2, w2, t1, htbl1, hrow3, hcol2,
            t2 => +c32 => +et2 => +htbl2 => +ec32 => +hg35b => +hw25 =>
              FT3.three_spec_transport_tbl(G, w1, w2, w3, t2, tbl,
                SolveFast.three_s3_cmp(w1, c12, w2, c23, w3, c31, c32,
                  U32.is_eq(c31, c32), t2),
                Equal.trans(Array<U32>, t2, t1, tbl, et2, et1),
                FT3.three_s3_cmp_ok(G, w1, c12, w2, c23, w3, c31, c32,
                  U32.is_eq(c31, c32), t2, {==}, h1, h2, h3, h15, h25, h35,
                  ec12, ec23, ec31, ec32, hne12, hne13, hne23, efb1, efb2))))

def FT3.three_s1_cmp_ok(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    +ci1: U32, +w1: +List<Nat>, +c12: U32, +c13: U32,
    +ci2: U32, +gr2: U32, +w2: +List<Nat>,
    +ci3: U32, +gr3: U32, +w3: +List<Nat>,
    same: Bool, tbl: Array<U32>,
    +esame: {same == U32.is_eq(c12, c13) : Bool},
    +htbl: FT.FT.TblOk(G, C, n, tbl),
    +hcol1: {FT.FT.has_col_go(C, ci1, w1, 0n) == True{} : Bool},
    +hcol2: {FT.FT.has_col_go(C, ci2, w2, 0n) == True{} : Bool},
    +hcol3: {FT.FT.has_col_go(C, ci3, w3, 0n) == True{} : Bool},
    +hrow2: {FT.FT.gentry_ok_b(G, n, gr2, w2) == True{} : Bool},
    +hrow3: {FT.FT.gentry_ok_b(G, n, gr3, w3) == True{} : Bool},
    +h1: {Tree.member_word(w1, G) == True{} : Bool},
    +h2: {Tree.member_word(w2, G) == True{} : Bool},
    +h3: {Tree.member_word(w3, G) == True{} : Bool},
    +h15: {SolveFast.is_len5(w1) == True{} : Bool},
    +h25: {SolveFast.is_len5(w2) == True{} : Bool},
    +h35: {SolveFast.is_len5(w3) == True{} : Bool},
    +ec12: {c12 == FT.FT.fb_code_words(w1, w2) : U32},
    +ec13: {c13 == FT.FT.fb_code_words(w1, w3) : U32},
    +hne12: {Feedback.word_eq(w1, w2) == False{} : Bool},
    +hne13: {Feedback.word_eq(w1, w3) == False{} : Bool},
    +hne23: {Feedback.word_eq(w2, w3) == False{} : Bool}) ->
  FT3.ThreeSpec(G, w1, w2, w3, tbl,
    SolveFast.three_s1_cmp(ci1, w1, c12, c13, ci2, gr2, w2, ci3, gr3, w3,
      same, tbl)):
  match same:
    case False{}:
      +hdiff : {U32.is_eq(c12, c13) == False{} : Bool} =
        Equal.sym(Bool, False{}, U32.is_eq(c12, c13), esame)
      +t = SolveFast.three_tree_sep(w1, c12, w2, c13, w3)
      +hti = FT3.three_tree_sep_in(G, w1, c12, w2, c13, w3, h1, h2, h3)
      +ed1 = FV.FV.depth_self(w1,
               Tree.Child{SolveFast.decode_fb5(c12), Tree.Node{w2, Nil{}}}
               <> (Tree.Child{SolveFast.decode_fb5(c13), Tree.Node{w3, Nil{}}} <> Nil{}))
      +ed2 = FT3.three_tree_sep_depth_a(w1, c12, w2, c13, w3, ec12, h15, h25,
               hne12)
      +ed3 = FT3.three_tree_sep_depth_b(w1, c12, w2, c13, w3, ec12, ec13,
               h15, h25, h35, hne13, hdiff)
      +vc = FT3.tree_valid_cost_3(G, t, w1, w2, w3, 1n, 2n, 2n, hti, ed1, ed2, ed3)
      +hv = Arr.Arr.dpair_l(
              {FV.FV.valid_b(t, G, w1 <> (w2 <> (w3 <> Nil{}))) == True{} : Bool},
              {Tree.cost(t, w1 <> (w2 <> (w3 <> Nil{}))) == 5n : Nat}, vc)
      +ec = Arr.Arr.dpair_r(
              {FV.FV.valid_b(t, G, w1 <> (w2 <> (w3 <> Nil{}))) == True{} : Bool},
              {Tree.cost(t, w1 <> (w2 <> (w3 <> Nil{}))) == 5n : Nat}, vc)
      Arr.DPair{{==}, FT3.done_three_5_intro(G, w1, w2, w3, t, hv, ec)}
    case True{}:
      +heq : {U32.is_eq(c12, c13) == True{} : Bool} =
        Equal.sym(Bool, True{}, U32.is_eq(c12, c13), esame)
      +efb1 = FT3.fb_eq_of_u32_eq(w1, w2, w3, c12, c13, h15, h25, h35,
                ec12, ec13, heq)
      FT.FT.tbl_get_use(
        r => FT3.ThreeSpec(G, w1, w2, w3, tbl,
               SolveFast.three_s2_a(ci1, w1, c12, ci2, gr2, w2, ci3, gr3, w3, r)),
        G, C, n, gr2, w2, ci1, w1, tbl, htbl, hrow2, hcol1,
        t1 => +c21 => +et1 => +htbl1 => +ec21 => +hg25 => +hw15 =>
          FT.FT.tbl_get_use(
            r2 => FT3.ThreeSpec(G, w1, w2, w3, tbl,
                    SolveFast.three_s2_b(ci1, w1, c12, ci2, w2, c21, gr3, w3, r2)),
            G, C, n, gr2, w2, ci3, w3, t1, htbl1, hrow2, hcol3,
            t2 => +c23 => +et2 => +htbl2 => +ec23 => +hg25b => +hw35 =>
              FT3.three_spec_transport_tbl(G, w1, w2, w3, t2, tbl,
                SolveFast.three_s2_cmp(ci1, w1, c12, ci2, w2, c21, c23, gr3, w3,
                  U32.is_eq(c21, c23), t2),
                Equal.trans(Array<U32>, t2, t1, tbl, et2, et1),
                FT3.three_s2_cmp_ok(G, C, n, ci1, w1, c12, ci2, w2, c21, c23,
                  gr3, w3, U32.is_eq(c21, c23), t2, {==}, htbl2,
                  hcol1, hcol2, hrow3, h1, h2, h3, h15, h25, h35,
                  ec12, ec21, ec23, hne12, hne13, hne23, efb1))))

def FT3.solve_three_tbl_ok(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +n: Nat,
    +cw1: SolveFast.CWord, +cw2: SolveFast.CWord, +cw3: SolveFast.CWord,
    tbl: Array<U32>,
    +htbl: FT.FT.TblOk(G, C, n, tbl),
    +hcw1: {FT.FT.cword_ok_b(G, C, n, cw1) == True{} : Bool},
    +hcw2: {FT.FT.cword_ok_b(G, C, n, cw2) == True{} : Bool},
    +hcw3: {FT.FT.cword_ok_b(G, C, n, cw3) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(
            SolveFast.cword_w(cw1)
            <> (SolveFast.cword_w(cw2) <> (SolveFast.cword_w(cw3) <> Nil{})))
          == True{} : Bool}) ->
  FT3.ThreeSpec(G, SolveFast.cword_w(cw1), SolveFast.cword_w(cw2),
    SolveFast.cword_w(cw3), tbl,
    SolveFast.solve_three_tbl(cw1, cw2, cw3, tbl)):
  match cw1 cw2 cw3:
    case SolveFast.CWord{+ci1, +gr1, +w1} SolveFast.CWord{+ci2, +gr2, +w2} SolveFast.CWord{+ci3, +gr3, +w3}:
      +hcol1 = Logic.Proof.and_true_l(FT.FT.has_col_go(C, ci1, w1, 0n),
                 FT.FT.gentry_ok_b(G, n, gr1, w1), hcw1)
      +hrow1 = Logic.Proof.and_true_r(FT.FT.has_col_go(C, ci1, w1, 0n),
                 FT.FT.gentry_ok_b(G, n, gr1, w1), hcw1)
      +hcol2 = Logic.Proof.and_true_l(FT.FT.has_col_go(C, ci2, w2, 0n),
                 FT.FT.gentry_ok_b(G, n, gr2, w2), hcw2)
      +hrow2 = Logic.Proof.and_true_r(FT.FT.has_col_go(C, ci2, w2, 0n),
                 FT.FT.gentry_ok_b(G, n, gr2, w2), hcw2)
      +hcol3 = Logic.Proof.and_true_l(FT.FT.has_col_go(C, ci3, w3, 0n),
                 FT.FT.gentry_ok_b(G, n, gr3, w3), hcw3)
      +hrow3 = Logic.Proof.and_true_r(FT.FT.has_col_go(C, ci3, w3, 0n),
                 FT.FT.gentry_ok_b(G, n, gr3, w3), hcw3)
      +h1 = FT.FT.member_of_gentry_ok(G, n, gr1, w1, hrow1)
      +h2 = FT.FT.member_of_gentry_ok(G, n, gr2, w2, hrow2)
      +h3 = FT.FT.member_of_gentry_ok(G, n, gr3, w3, hrow3)
      +hne12 = FT3.nd3_ne12(w1, w2, w3, nd)
      +hne13 = FT3.nd3_ne13(w1, w2, w3, nd)
      +hne23 = FT3.nd3_ne23(w1, w2, w3, nd)
      FT.FT.tbl_get_use(
        r => FT3.ThreeSpec(G, w1, w2, w3, tbl,
               SolveFast.three_s1_a(ci1, gr1, w1, ci2, gr2, w2, ci3, gr3, w3, r)),
        G, C, n, gr1, w1, ci2, w2, tbl, htbl, hrow1, hcol2,
        t1 => +c12 => +et1 => +htbl1 => +ec12 => +h15 => +h25 =>
          FT.FT.tbl_get_use(
            r2 => FT3.ThreeSpec(G, w1, w2, w3, tbl,
                    SolveFast.three_s1_b(ci1, w1, c12, ci2, gr2, w2, ci3, gr3, w3, r2)),
            G, C, n, gr1, w1, ci3, w3, t1, htbl1, hrow1, hcol3,
            t2 => +c13 => +et2 => +htbl2 => +ec13 => +h15b => +h35 =>
              FT3.three_spec_transport_tbl(G, w1, w2, w3, t2, tbl,
                SolveFast.three_s1_cmp(ci1, w1, c12, c13, ci2, gr2, w2,
                  ci3, gr3, w3, U32.is_eq(c12, c13), t2),
                Equal.trans(Array<U32>, t2, t1, tbl, et2, et1),
                FT3.three_s1_cmp_ok(G, C, n, ci1, w1, c12, c13, ci2, gr2, w2,
                  ci3, gr3, w3, U32.is_eq(c12, c13), t2, {==}, htbl2,
                  hcol1, hcol2, hcol3, hrow2, hrow3, h1, h2, h3,
                  h15, h25, h35, ec12, ec13, hne12, hne13, hne23))))

# ---------------------------------------------------------------------------
# Section 5: Optimality `FT3.done_three_le_ref` (both `5n` and `6n`)
# ---------------------------------------------------------------------------

def FT3.groups_build_3_w1(+w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    +hne12: {Feedback.word_eq(w1, w2) == False{} : Bool},
    +hne13: {Feedback.word_eq(w1, w3) == False{} : Bool},
    +efb1: {Feedback.feedback_eq(Feedback.feedback(w1, w2),
              Feedback.feedback(w1, w3)) == True{} : Bool}) ->
  {Groups.groups_build(w1, w1 <> (w2 <> (w3 <> Nil{})), Nil{})
   == Groups.Group{Feedback.feedback(w1, w2), w2 <> (w3 <> Nil{})} <> Nil{}
   : +List<Groups.Group>}:
  +s1 : {Groups.groups_build(w1, w1 <> (w2 <> (w3 <> Nil{})), Nil{})
         == Groups.groups_build(w1, w2 <> (w3 <> Nil{}), Nil{})
         : +List<Groups.Group>} =
    Equal.cong(Bool, +List<Groups.Group>,
      b => Feedback.Bool.case(+List<Groups.Group>, b,
             Groups.groups_build(w1, w2 <> (w3 <> Nil{}), Nil{}),
             Groups.groups_build(w1, w2 <> (w3 <> Nil{}),
               Groups.group_add(w1, Feedback.feedback(w1, w1), Nil{}))),
      Feedback.word_eq(w1, w1), True{}, FbProof.FbPrf.word_eq_refl(w1))
  +g1 : +List<Groups.Group> =
    Groups.Group{Feedback.feedback(w1, w2), w2 <> Nil{}} <> Nil{}
  +s2 : {Groups.groups_build(w1, w2 <> (w3 <> Nil{}), Nil{})
         == Groups.groups_build(w1, w3 <> Nil{}, g1) : +List<Groups.Group>} =
    Equal.cong(Bool, +List<Groups.Group>,
      b => Feedback.Bool.case(+List<Groups.Group>, b,
             Groups.groups_build(w1, w3 <> Nil{}, Nil{}),
             Groups.groups_build(w1, w3 <> Nil{}, g1)),
      Feedback.word_eq(w1, w2), False{}, hne12)
  +efsym : {Feedback.feedback_eq(Feedback.feedback(w1, w3),
              Feedback.feedback(w1, w2)) == True{} : Bool} =
    FbProof.FeedbackProof.feedback_eq_sym(Feedback.feedback(w1, w2),
      Feedback.feedback(w1, w3), efb1)
  +s3 : {Groups.groups_build(w1, w3 <> Nil{}, g1)
         == Groups.group_add(w3, Feedback.feedback(w1, w3), g1)
         : +List<Groups.Group>} =
    Equal.cong(Bool, +List<Groups.Group>,
      b => Feedback.Bool.case(+List<Groups.Group>, b, g1,
             Groups.group_add(w3, Feedback.feedback(w1, w3), g1)),
      Feedback.word_eq(w1, w3), False{}, hne13)
  +s4 : {Groups.group_add(w3, Feedback.feedback(w1, w3), g1)
         == Groups.Group{Feedback.feedback(w1, w2), w2 <> (w3 <> Nil{})} <> Nil{}
         : +List<Groups.Group>} =
    Equal.cong(Bool, +List<Groups.Group>,
      b => Feedback.Bool.case(+List<Groups.Group>, b,
             Groups.Group{Feedback.feedback(w1, w2), w2 <> (w3 <> Nil{})} <> Nil{},
             Groups.Group{Feedback.feedback(w1, w2), w2 <> Nil{}}
             <> (Groups.Group{Feedback.feedback(w1, w3), w3 <> Nil{}} <> Nil{})),
      Feedback.feedback_eq(Feedback.feedback(w1, w3), Feedback.feedback(w1, w2)),
      True{}, efsym)
  Equal.trans(+List<Groups.Group>,
    Groups.groups_build(w1, w1 <> (w2 <> (w3 <> Nil{})), Nil{}),
    Groups.groups_build(w1, w3 <> Nil{}, g1),
    Groups.Group{Feedback.feedback(w1, w2), w2 <> (w3 <> Nil{})} <> Nil{},
    Equal.trans(+List<Groups.Group>,
      Groups.groups_build(w1, w1 <> (w2 <> (w3 <> Nil{})), Nil{}),
      Groups.groups_build(w1, w2 <> (w3 <> Nil{}), Nil{}),
      Groups.groups_build(w1, w3 <> Nil{}, g1), s1, s2),
    Equal.trans(+List<Groups.Group>,
      Groups.groups_build(w1, w3 <> Nil{}, g1),
      Groups.group_add(w3, Feedback.feedback(w1, w3), g1),
      Groups.Group{Feedback.feedback(w1, w2), w2 <> (w3 <> Nil{})} <> Nil{},
      s3, s4))

def FT3.groups_build_3_w2(+w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    +hne21: {Feedback.word_eq(w2, w1) == False{} : Bool},
    +hne23: {Feedback.word_eq(w2, w3) == False{} : Bool},
    +efb2: {Feedback.feedback_eq(Feedback.feedback(w2, w1),
              Feedback.feedback(w2, w3)) == True{} : Bool}) ->
  {Groups.groups_build(w2, w1 <> (w2 <> (w3 <> Nil{})), Nil{})
   == Groups.Group{Feedback.feedback(w2, w1), w1 <> (w3 <> Nil{})} <> Nil{}
   : +List<Groups.Group>}:
  +g1 : +List<Groups.Group> =
    Groups.Group{Feedback.feedback(w2, w1), w1 <> Nil{}} <> Nil{}
  +s1 : {Groups.groups_build(w2, w1 <> (w2 <> (w3 <> Nil{})), Nil{})
         == Groups.groups_build(w2, w2 <> (w3 <> Nil{}), g1)
         : +List<Groups.Group>} =
    Equal.cong(Bool, +List<Groups.Group>,
      b => Feedback.Bool.case(+List<Groups.Group>, b,
             Groups.groups_build(w2, w2 <> (w3 <> Nil{}), Nil{}),
             Groups.groups_build(w2, w2 <> (w3 <> Nil{}), g1)),
      Feedback.word_eq(w2, w1), False{}, hne21)
  +s2 : {Groups.groups_build(w2, w2 <> (w3 <> Nil{}), g1)
         == Groups.groups_build(w2, w3 <> Nil{}, g1)
         : +List<Groups.Group>} =
    Equal.cong(Bool, +List<Groups.Group>,
      b => Feedback.Bool.case(+List<Groups.Group>, b,
             Groups.groups_build(w2, w3 <> Nil{}, g1),
             Groups.groups_build(w2, w3 <> Nil{},
               Groups.group_add(w2, Feedback.feedback(w2, w2), g1))),
      Feedback.word_eq(w2, w2), True{}, FbProof.FbPrf.word_eq_refl(w2))
  +efsym : {Feedback.feedback_eq(Feedback.feedback(w2, w3),
              Feedback.feedback(w2, w1)) == True{} : Bool} =
    FbProof.FeedbackProof.feedback_eq_sym(Feedback.feedback(w2, w1),
      Feedback.feedback(w2, w3), efb2)
  +s3 : {Groups.groups_build(w2, w3 <> Nil{}, g1)
         == Groups.group_add(w3, Feedback.feedback(w2, w3), g1)
         : +List<Groups.Group>} =
    Equal.cong(Bool, +List<Groups.Group>,
      b => Feedback.Bool.case(+List<Groups.Group>, b, g1,
             Groups.group_add(w3, Feedback.feedback(w2, w3), g1)),
      Feedback.word_eq(w2, w3), False{}, hne23)
  +s4 : {Groups.group_add(w3, Feedback.feedback(w2, w3), g1)
         == Groups.Group{Feedback.feedback(w2, w1), w1 <> (w3 <> Nil{})} <> Nil{}
         : +List<Groups.Group>} =
    Equal.cong(Bool, +List<Groups.Group>,
      b => Feedback.Bool.case(+List<Groups.Group>, b,
             Groups.Group{Feedback.feedback(w2, w1), w1 <> (w3 <> Nil{})} <> Nil{},
             Groups.Group{Feedback.feedback(w2, w1), w1 <> Nil{}}
             <> (Groups.Group{Feedback.feedback(w2, w3), w3 <> Nil{}} <> Nil{})),
      Feedback.feedback_eq(Feedback.feedback(w2, w3), Feedback.feedback(w2, w1)),
      True{}, efsym)
  Equal.trans(+List<Groups.Group>,
    Groups.groups_build(w2, w1 <> (w2 <> (w3 <> Nil{})), Nil{}),
    Groups.groups_build(w2, w3 <> Nil{}, g1),
    Groups.Group{Feedback.feedback(w2, w1), w1 <> (w3 <> Nil{})} <> Nil{},
    Equal.trans(+List<Groups.Group>,
      Groups.groups_build(w2, w1 <> (w2 <> (w3 <> Nil{})), Nil{}),
      Groups.groups_build(w2, w2 <> (w3 <> Nil{}), g1),
      Groups.groups_build(w2, w3 <> Nil{}, g1), s1, s2),
    Equal.trans(+List<Groups.Group>,
      Groups.groups_build(w2, w3 <> Nil{}, g1),
      Groups.group_add(w3, Feedback.feedback(w2, w3), g1),
      Groups.Group{Feedback.feedback(w2, w1), w1 <> (w3 <> Nil{})} <> Nil{},
      s3, s4))

def FT3.groups_build_3_w3(+w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    +hne31: {Feedback.word_eq(w3, w1) == False{} : Bool},
    +hne32: {Feedback.word_eq(w3, w2) == False{} : Bool},
    +efb3: {Feedback.feedback_eq(Feedback.feedback(w3, w1),
              Feedback.feedback(w3, w2)) == True{} : Bool}) ->
  {Groups.groups_build(w3, w1 <> (w2 <> (w3 <> Nil{})), Nil{})
   == Groups.Group{Feedback.feedback(w3, w1), w1 <> (w2 <> Nil{})} <> Nil{}
   : +List<Groups.Group>}:
  +g1 : +List<Groups.Group> =
    Groups.Group{Feedback.feedback(w3, w1), w1 <> Nil{}} <> Nil{}
  +g2 : +List<Groups.Group> =
    Groups.Group{Feedback.feedback(w3, w1), w1 <> (w2 <> Nil{})} <> Nil{}
  +s1 : {Groups.groups_build(w3, w1 <> (w2 <> (w3 <> Nil{})), Nil{})
         == Groups.groups_build(w3, w2 <> (w3 <> Nil{}), g1)
         : +List<Groups.Group>} =
    Equal.cong(Bool, +List<Groups.Group>,
      b => Feedback.Bool.case(+List<Groups.Group>, b,
             Groups.groups_build(w3, w2 <> (w3 <> Nil{}), Nil{}),
             Groups.groups_build(w3, w2 <> (w3 <> Nil{}), g1)),
      Feedback.word_eq(w3, w1), False{}, hne31)
  +efsym : {Feedback.feedback_eq(Feedback.feedback(w3, w2),
              Feedback.feedback(w3, w1)) == True{} : Bool} =
    FbProof.FeedbackProof.feedback_eq_sym(Feedback.feedback(w3, w1),
      Feedback.feedback(w3, w2), efb3)
  +s2a : {Groups.groups_build(w3, w2 <> (w3 <> Nil{}), g1)
          == Groups.groups_build(w3, w3 <> Nil{},
               Groups.group_add(w2, Feedback.feedback(w3, w2), g1))
          : +List<Groups.Group>} =
    Equal.cong(Bool, +List<Groups.Group>,
      b => Feedback.Bool.case(+List<Groups.Group>, b,
             Groups.groups_build(w3, w3 <> Nil{}, g1),
             Groups.groups_build(w3, w3 <> Nil{},
               Groups.group_add(w2, Feedback.feedback(w3, w2), g1))),
      Feedback.word_eq(w3, w2), False{}, hne32)
  +s2b : {Groups.group_add(w2, Feedback.feedback(w3, w2), g1) == g2
          : +List<Groups.Group>} =
    Equal.cong(Bool, +List<Groups.Group>,
      b => Feedback.Bool.case(+List<Groups.Group>, b, g2,
             Groups.Group{Feedback.feedback(w3, w1), w1 <> Nil{}}
             <> (Groups.Group{Feedback.feedback(w3, w2), w2 <> Nil{}} <> Nil{})),
      Feedback.feedback_eq(Feedback.feedback(w3, w2), Feedback.feedback(w3, w1)),
      True{}, efsym)
  +s3 : {Groups.groups_build(w3, w3 <> Nil{}, g2) == g2
         : +List<Groups.Group>} =
    Equal.cong(Bool, +List<Groups.Group>,
      b => Feedback.Bool.case(+List<Groups.Group>, b, g2,
             Groups.group_add(w3, Feedback.feedback(w3, w3), g2)),
      Feedback.word_eq(w3, w3), True{}, FbProof.FbPrf.word_eq_refl(w3))
  Equal.trans(+List<Groups.Group>,
    Groups.groups_build(w3, w1 <> (w2 <> (w3 <> Nil{})), Nil{}),
    Groups.groups_build(w3, w3 <> Nil{}, g2), g2,
    Equal.trans(+List<Groups.Group>,
      Groups.groups_build(w3, w1 <> (w2 <> (w3 <> Nil{})), Nil{}),
      Groups.groups_build(w3, w2 <> (w3 <> Nil{}), g1),
      Groups.groups_build(w3, w3 <> Nil{}, g2), s1,
      Equal.trans(+List<Groups.Group>,
        Groups.groups_build(w3, w2 <> (w3 <> Nil{}), g1),
        Groups.groups_build(w3, w3 <> Nil{},
          Groups.group_add(w2, Feedback.feedback(w3, w2), g1)),
        Groups.groups_build(w3, w3 <> Nil{}, g2), s2a,
        Equal.cong(+List<Groups.Group>, +List<Groups.Group>,
          acc => Groups.groups_build(w3, w3 <> Nil{}, acc),
          Groups.group_add(w2, Feedback.feedback(w3, w2), g1), g2, s2b))),
    s3)

def FT3.guess_skip_of_lb(+pp: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +g: +List<Nat>, +best: SolveRef.Best,
    us: Bool,
    +eus: {us == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
           : Bool},
    +ele: {Nat.is_le(Groups.len_words(S), 1n+pp) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +hbest: {Nat.is_le(Eval.Eval.cost_of(best), inf) == True{} : Bool},
    +hle: {Nat.is_le(Eval.Eval.cost_of(best),
             SolveFast.lower_bound(Groups.len_words(S),
               Groups.groups_build(g, S, Nil{}))) == True{} : Bool}) ->
  {Eval.Eval.guess_bool(pp, G, S, g, Groups.groups_build(g, S, Nil{}), inf,
     us, best) == best : SolveRef.Best}:
  match us:
    case False{}:
      {==}
    case True{}:
      +hus : {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))
              == True{} : Bool} =
        Equal.sym(Bool, True{},
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), eus)
      FLB.FS.block_skip_eq(pp, inf, G, S, g, Groups.groups_build(g, S, Nil{}),
        best, hus, ele, hz, hbest, hle)

def FT3.lb_6_of_pair(+w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    +g: +List<Nat>, +fb: +List<Feedback.Color>, +pa: +List<Nat>, +pb: +List<Nat>,
    +egrp: {Groups.groups_build(g, w1 <> (w2 <> (w3 <> Nil{})), Nil{})
            == Groups.Group{fb, pa <> (pb <> Nil{})} <> Nil{}
            : +List<Groups.Group>},
    +hne: {Feedback.word_eq(pa, pb) == False{} : Bool}) ->
  {Nat.is_le(6n,
     SolveFast.lower_bound(3n,
       Groups.groups_build(g, w1 <> (w2 <> (w3 <> Nil{})), Nil{})))
   == True{} : Bool}:
  +ws3 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> Nil{}))
  +nd2 : {FN.FN.no_dup_ref(pa <> (pb <> Nil{})) == True{} : Bool} =
    FV.FV.no_dup_two_of_word_eq_false(pa, pb, hne)
  +eclb : {SolveFast.class_lb(pa <> (pb <> Nil{})) == 3n : Nat} =
    Equal.sym(Nat, 3n, SolveFast.class_lb(pa <> (pb <> Nil{})),
      FN.FN.class_lb_nodup_eq(pa <> (pb <> Nil{}), nd2))
  +elb : {SolveFast.lower_bound(3n, Groups.groups_build(g, ws3, Nil{})) == 6n : Nat} =
    Equal.trans(Nat,
      SolveFast.lower_bound(3n, Groups.groups_build(g, ws3, Nil{})),
      Nat.add(SolveFast.class_lb(pa <> (pb <> Nil{})), 3n),
      6n,
      Equal.cong(+List<Groups.Group>, Nat, gs => SolveFast.lower_bound(3n, gs),
        Groups.groups_build(g, ws3, Nil{}),
        Groups.Group{fb, pa <> (pb <> Nil{})} <> Nil{}, egrp),
      Equal.cong(Nat, Nat, x => Nat.add(x, 3n),
        SolveFast.class_lb(pa <> (pb <> Nil{})), 3n, eclb))
  NatProof.Nat.is_le_eq_r(6n, 6n,
    SolveFast.lower_bound(3n, Groups.groups_build(g, ws3, Nil{})),
    Equal.sym(Nat,
      SolveFast.lower_bound(3n, Groups.groups_build(g, ws3, Nil{})), 6n, elb),
    {==})

def FT3.guess_skip_6_b3(+pp: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>, +g: +List<Nat>,
    +tree: Tree.Tree,
    +ble: {Nat.is_le(3n, 1n+pp) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h6le: {Nat.is_le(6n, inf) == True{} : Bool},
    +hne12: {Feedback.word_eq(w1, w2) == False{} : Bool},
    +hne13: {Feedback.word_eq(w1, w3) == False{} : Bool},
    +hne23: {Feedback.word_eq(w2, w3) == False{} : Bool},
    +efb3: {Feedback.feedback_eq(Feedback.feedback(w3, w1),
              Feedback.feedback(w3, w2)) == True{} : Bool},
    +hf1: {Feedback.word_eq(g, w1) == False{} : Bool},
    +hf2: {Feedback.word_eq(g, w2) == False{} : Bool},
    b3: Bool, +eb3: {b3 == Feedback.word_eq(g, w3) : Bool}) ->
  {Eval.Eval.guess(pp, G, w1 <> (w2 <> (w3 <> Nil{})), g, inf,
     SolveRef.Best{tree, 6n}) == SolveRef.Best{tree, 6n} : SolveRef.Best}:
  match b3:
    case True{}:
      +ws3 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> Nil{}))
      +eg3 : {g == w3 : +List<Nat>} =
        CoverList.Cover.word_eq_true(g, w3,
          Equal.sym(Bool, True{}, Feedback.word_eq(g, w3), eb3))
      +egrp : {Groups.groups_build(g, ws3, Nil{})
               == Groups.Group{Feedback.feedback(w3, w1), w1 <> (w2 <> Nil{})} <> Nil{}
               : +List<Groups.Group>} =
        Equal.trans(+List<Groups.Group>,
          Groups.groups_build(g, ws3, Nil{}),
          Groups.groups_build(w3, ws3, Nil{}),
          Groups.Group{Feedback.feedback(w3, w1), w1 <> (w2 <> Nil{})} <> Nil{},
          Equal.cong(+List<Nat>, +List<Groups.Group>,
            x => Groups.groups_build(x, ws3, Nil{}), g, w3, eg3),
          FT3.groups_build_3_w3(w1, w2, w3,
            FO.FO.word_eq_sym_false(w1, w3, hne13),
            FO.FO.word_eq_sym_false(w2, w3, hne23), efb3))
      +hle = FT3.lb_6_of_pair(w1, w2, w3, g, Feedback.feedback(w3, w1), w1, w2,
               egrp, hne12)
      FT3.guess_skip_of_lb(pp, inf, G, ws3, g, SolveRef.Best{tree, 6n},
        Groups.groups_smaller(ws3, Groups.groups_build(g, ws3, Nil{})), {==},
        ble, hz, h6le, hle)
    case False{}:
      +ws3 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> Nil{}))
      +hf3 : {Feedback.word_eq(g, w3) == False{} : Bool} =
        Equal.sym(Bool, False{}, Feedback.word_eq(g, w3), eb3)
      +hnm3 : {Tree.member_word(g, w3 <> Nil{}) == False{} : Bool} =
        Equal.cong(Bool, Bool, b => Feedback.Bool.case(Bool, b, True{}, False{}),
          Feedback.word_eq(g, w3), False{}, hf3)
      +hnm2 : {Tree.member_word(g, w2 <> (w3 <> Nil{})) == False{} : Bool} =
        Equal.trans(Bool,
          Tree.member_word(g, w2 <> (w3 <> Nil{})),
          Tree.member_word(g, w3 <> Nil{}), False{},
          Equal.cong(Bool, Bool,
            b => Feedback.Bool.case(Bool, b, True{}, Tree.member_word(g, w3 <> Nil{})),
            Feedback.word_eq(g, w2), False{}, hf2),
          hnm3)
      +hnm : {Tree.member_word(g, ws3) == False{} : Bool} =
        Equal.trans(Bool,
          Tree.member_word(g, ws3),
          Tree.member_word(g, w2 <> (w3 <> Nil{})), False{},
          Equal.cong(Bool, Bool,
            b => Feedback.Bool.case(Bool, b, True{},
                   Tree.member_word(g, w2 <> (w3 <> Nil{}))),
            Feedback.word_eq(g, w1), False{}, hf1),
          hnm2)
      +hle : {Nat.is_le(6n, SolveFast.pre_lb(3n, g, ws3)) == True{} : Bool} =
        NatProof.Nat.is_le_eq_r(6n, 6n, SolveFast.pre_lb(3n, g, ws3),
          Equal.sym(Nat, SolveFast.pre_lb(3n, g, ws3), 6n,
            FN.FN.pre_lb_of_not_member(g, ws3, hnm)), {==})
      FLB.FS.pre_guess_skip_eq(pp, inf, G, ws3, g, SolveRef.Best{tree, 6n},
        ble, hz, h6le, hle)

def FT3.guess_skip_6_b2(+pp: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>, +g: +List<Nat>,
    +tree: Tree.Tree,
    +ble: {Nat.is_le(3n, 1n+pp) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h6le: {Nat.is_le(6n, inf) == True{} : Bool},
    +hne12: {Feedback.word_eq(w1, w2) == False{} : Bool},
    +hne13: {Feedback.word_eq(w1, w3) == False{} : Bool},
    +hne23: {Feedback.word_eq(w2, w3) == False{} : Bool},
    +efb2: {Feedback.feedback_eq(Feedback.feedback(w2, w1),
              Feedback.feedback(w2, w3)) == True{} : Bool},
    +efb3: {Feedback.feedback_eq(Feedback.feedback(w3, w1),
              Feedback.feedback(w3, w2)) == True{} : Bool},
    +hf1: {Feedback.word_eq(g, w1) == False{} : Bool},
    b2: Bool, +eb2: {b2 == Feedback.word_eq(g, w2) : Bool}) ->
  {Eval.Eval.guess(pp, G, w1 <> (w2 <> (w3 <> Nil{})), g, inf,
     SolveRef.Best{tree, 6n}) == SolveRef.Best{tree, 6n} : SolveRef.Best}:
  match b2:
    case True{}:
      +ws3 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> Nil{}))
      +eg2 : {g == w2 : +List<Nat>} =
        CoverList.Cover.word_eq_true(g, w2,
          Equal.sym(Bool, True{}, Feedback.word_eq(g, w2), eb2))
      +egrp : {Groups.groups_build(g, ws3, Nil{})
               == Groups.Group{Feedback.feedback(w2, w1), w1 <> (w3 <> Nil{})} <> Nil{}
               : +List<Groups.Group>} =
        Equal.trans(+List<Groups.Group>,
          Groups.groups_build(g, ws3, Nil{}),
          Groups.groups_build(w2, ws3, Nil{}),
          Groups.Group{Feedback.feedback(w2, w1), w1 <> (w3 <> Nil{})} <> Nil{},
          Equal.cong(+List<Nat>, +List<Groups.Group>,
            x => Groups.groups_build(x, ws3, Nil{}), g, w2, eg2),
          FT3.groups_build_3_w2(w1, w2, w3,
            FO.FO.word_eq_sym_false(w1, w2, hne12), hne23, efb2))
      +hle = FT3.lb_6_of_pair(w1, w2, w3, g, Feedback.feedback(w2, w1), w1, w3,
               egrp, hne13)
      FT3.guess_skip_of_lb(pp, inf, G, ws3, g, SolveRef.Best{tree, 6n},
        Groups.groups_smaller(ws3, Groups.groups_build(g, ws3, Nil{})), {==},
        ble, hz, h6le, hle)
    case False{}:
      +hf2 : {Feedback.word_eq(g, w2) == False{} : Bool} =
        Equal.sym(Bool, False{}, Feedback.word_eq(g, w2), eb2)
      FT3.guess_skip_6_b3(pp, inf, G, w1, w2, w3, g, tree, ble, hz, h6le,
        hne12, hne13, hne23, efb3, hf1, hf2, Feedback.word_eq(g, w3), {==})

def FT3.guess_skip_6_b1(+pp: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>, +g: +List<Nat>,
    +tree: Tree.Tree,
    +ble: {Nat.is_le(3n, 1n+pp) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h6le: {Nat.is_le(6n, inf) == True{} : Bool},
    +hne12: {Feedback.word_eq(w1, w2) == False{} : Bool},
    +hne13: {Feedback.word_eq(w1, w3) == False{} : Bool},
    +hne23: {Feedback.word_eq(w2, w3) == False{} : Bool},
    +efb1: {Feedback.feedback_eq(Feedback.feedback(w1, w2),
              Feedback.feedback(w1, w3)) == True{} : Bool},
    +efb2: {Feedback.feedback_eq(Feedback.feedback(w2, w1),
              Feedback.feedback(w2, w3)) == True{} : Bool},
    +efb3: {Feedback.feedback_eq(Feedback.feedback(w3, w1),
              Feedback.feedback(w3, w2)) == True{} : Bool},
    b1: Bool, +eb1: {b1 == Feedback.word_eq(g, w1) : Bool}) ->
  {Eval.Eval.guess(pp, G, w1 <> (w2 <> (w3 <> Nil{})), g, inf,
     SolveRef.Best{tree, 6n}) == SolveRef.Best{tree, 6n} : SolveRef.Best}:
  match b1:
    case True{}:
      +ws3 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> Nil{}))
      +eg1 : {g == w1 : +List<Nat>} =
        CoverList.Cover.word_eq_true(g, w1,
          Equal.sym(Bool, True{}, Feedback.word_eq(g, w1), eb1))
      +egrp : {Groups.groups_build(g, ws3, Nil{})
               == Groups.Group{Feedback.feedback(w1, w2), w2 <> (w3 <> Nil{})} <> Nil{}
               : +List<Groups.Group>} =
        Equal.trans(+List<Groups.Group>,
          Groups.groups_build(g, ws3, Nil{}),
          Groups.groups_build(w1, ws3, Nil{}),
          Groups.Group{Feedback.feedback(w1, w2), w2 <> (w3 <> Nil{})} <> Nil{},
          Equal.cong(+List<Nat>, +List<Groups.Group>,
            x => Groups.groups_build(x, ws3, Nil{}), g, w1, eg1),
          FT3.groups_build_3_w1(w1, w2, w3, hne12, hne13, efb1))
      +hle = FT3.lb_6_of_pair(w1, w2, w3, g, Feedback.feedback(w1, w2), w2, w3,
               egrp, hne23)
      FT3.guess_skip_of_lb(pp, inf, G, ws3, g, SolveRef.Best{tree, 6n},
        Groups.groups_smaller(ws3, Groups.groups_build(g, ws3, Nil{})), {==},
        ble, hz, h6le, hle)
    case False{}:
      +hf1 : {Feedback.word_eq(g, w1) == False{} : Bool} =
        Equal.sym(Bool, False{}, Feedback.word_eq(g, w1), eb1)
      FT3.guess_skip_6_b2(pp, inf, G, w1, w2, w3, g, tree, ble, hz, h6le,
        hne12, hne13, hne23, efb2, efb3, hf1, Feedback.word_eq(g, w2), {==})

def FT3.guesses_skip_6(+gs: +List<+List<Nat>>, +pp: Nat, +inf: Nat,
    +G: +List<+List<Nat>>,
    +w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>, +tree: Tree.Tree,
    +ble: {Nat.is_le(3n, 1n+pp) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h6le: {Nat.is_le(6n, inf) == True{} : Bool},
    +hne12: {Feedback.word_eq(w1, w2) == False{} : Bool},
    +hne13: {Feedback.word_eq(w1, w3) == False{} : Bool},
    +hne23: {Feedback.word_eq(w2, w3) == False{} : Bool},
    +efb1: {Feedback.feedback_eq(Feedback.feedback(w1, w2),
              Feedback.feedback(w1, w3)) == True{} : Bool},
    +efb2: {Feedback.feedback_eq(Feedback.feedback(w2, w1),
              Feedback.feedback(w2, w3)) == True{} : Bool},
    +efb3: {Feedback.feedback_eq(Feedback.feedback(w3, w1),
              Feedback.feedback(w3, w2)) == True{} : Bool}) ->
  {Eval.Eval.guesses(1n+pp, G, w1 <> (w2 <> (w3 <> Nil{})), inf, gs,
     SolveRef.Best{tree, 6n}) == SolveRef.Best{tree, 6n} : SolveRef.Best}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      +ws3 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> Nil{}))
      +eg = FT3.guess_skip_6_b1(pp, inf, G, w1, w2, w3, g, tree, ble, hz, h6le,
              hne12, hne13, hne23, efb1, efb2, efb3,
              Feedback.word_eq(g, w1), {==})
      Equal.trans(SolveRef.Best,
        Eval.Eval.guesses(1n+pp, G, ws3, inf, t,
          Eval.Eval.guess(pp, G, ws3, g, inf, SolveRef.Best{tree, 6n})),
        Eval.Eval.guesses(1n+pp, G, ws3, inf, t, SolveRef.Best{tree, 6n}),
        SolveRef.Best{tree, 6n},
        Equal.cong(SolveRef.Best, SolveRef.Best,
          b => Eval.Eval.guesses(1n+pp, G, ws3, inf, t, b),
          Eval.Eval.guess(pp, G, ws3, g, inf, SolveRef.Best{tree, 6n}),
          SolveRef.Best{tree, 6n}, eg),
        FT3.guesses_skip_6(t, pp, inf, G, w1, w2, w3, tree, ble, hz, h6le,
          hne12, hne13, hne23, efb1, efb2, efb3))

def FT3.done_three_le_ref_case(+pp: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    +tree: Tree.Tree, +cost: Nat,
    +ble: {Nat.is_le(3n, 1n+pp) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(w1 <> (w2 <> (w3 <> Nil{}))) == True{} : Bool},
    is5: Bool, +eis5: {is5 == Nat.is_eq(cost, 5n) : Bool},
    +hor: {Bool.or(is5,
             Bool.and(Nat.is_eq(cost, 6n),
               Bool.and(
                 Feedback.feedback_eq(Feedback.feedback(w1, w2),
                   Feedback.feedback(w1, w3)),
                 Bool.and(
                   Feedback.feedback_eq(Feedback.feedback(w2, w1),
                     Feedback.feedback(w2, w3)),
                   Feedback.feedback_eq(Feedback.feedback(w3, w1),
                     Feedback.feedback(w3, w2)))))) == True{} : Bool}) ->
  {Nat.is_le(cost, Eval.Eval.cost_of(
     FS.FS.ref_run_at(1n+pp, inf, G, w1 <> (w2 <> (w3 <> Nil{})))))
   == True{} : Bool}:
  match is5:
    case True{}:
      +ws3 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> Nil{}))
      +ec5 : {cost == 5n : Nat} =
        NatProof.NatPrf.is_eq_true(cost, 5n,
          Equal.sym(Bool, True{}, Nat.is_eq(cost, 5n), eis5))
      +h5le : {Nat.is_le(5n, inf) == True{} : Bool} =
        NatProof.Nat.is_le_trans(5n, 6n, inf, {==},
          NatProof.Nat.is_le_of_lt(6n, inf, h6))
      %Equal.sym(Nat, cost, 5n, ec5) :
        {Nat.is_le(_, Eval.Eval.cost_of(FS.FS.ref_run_at(1n+pp, inf, G, ws3)))
         == True{} : Bool}
      FV.FV.floor_init_le_ref(pp, inf, G, ws3, SolveRef.Best{tree, 5n},
        nd, ble, hz, h5le, {==})
    case False{}:
      +ws3 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> Nil{}))
      +h6eq = Logic.Proof.and_true_l(Nat.is_eq(cost, 6n),
                Bool.and(
                  Feedback.feedback_eq(Feedback.feedback(w1, w2),
                    Feedback.feedback(w1, w3)),
                  Bool.and(
                    Feedback.feedback_eq(Feedback.feedback(w2, w1),
                      Feedback.feedback(w2, w3)),
                    Feedback.feedback_eq(Feedback.feedback(w3, w1),
                      Feedback.feedback(w3, w2)))), hor)
      +hfbs = Logic.Proof.and_true_r(Nat.is_eq(cost, 6n),
                Bool.and(
                  Feedback.feedback_eq(Feedback.feedback(w1, w2),
                    Feedback.feedback(w1, w3)),
                  Bool.and(
                    Feedback.feedback_eq(Feedback.feedback(w2, w1),
                      Feedback.feedback(w2, w3)),
                    Feedback.feedback_eq(Feedback.feedback(w3, w1),
                      Feedback.feedback(w3, w2)))), hor)
      +efb1 = Logic.Proof.and_true_l(
                Feedback.feedback_eq(Feedback.feedback(w1, w2),
                  Feedback.feedback(w1, w3)),
                Bool.and(
                  Feedback.feedback_eq(Feedback.feedback(w2, w1),
                    Feedback.feedback(w2, w3)),
                  Feedback.feedback_eq(Feedback.feedback(w3, w1),
                    Feedback.feedback(w3, w2))), hfbs)
      +hr2 = Logic.Proof.and_true_r(
               Feedback.feedback_eq(Feedback.feedback(w1, w2),
                 Feedback.feedback(w1, w3)),
               Bool.and(
                 Feedback.feedback_eq(Feedback.feedback(w2, w1),
                   Feedback.feedback(w2, w3)),
                 Feedback.feedback_eq(Feedback.feedback(w3, w1),
                   Feedback.feedback(w3, w2))), hfbs)
      +efb2 = Logic.Proof.and_true_l(
                Feedback.feedback_eq(Feedback.feedback(w2, w1),
                  Feedback.feedback(w2, w3)),
                Feedback.feedback_eq(Feedback.feedback(w3, w1),
                  Feedback.feedback(w3, w2)), hr2)
      +efb3 = Logic.Proof.and_true_r(
                Feedback.feedback_eq(Feedback.feedback(w2, w1),
                  Feedback.feedback(w2, w3)),
                Feedback.feedback_eq(Feedback.feedback(w3, w1),
                  Feedback.feedback(w3, w2)), hr2)
      +ec6 : {cost == 6n : Nat} = NatProof.NatPrf.is_eq_true(cost, 6n, h6eq)
      +h6le : {Nat.is_le(6n, inf) == True{} : Bool} =
        NatProof.Nat.is_le_of_lt(6n, inf, h6)
      +hne12 = FT3.nd3_ne12(w1, w2, w3, nd)
      +hne13 = FT3.nd3_ne13(w1, w2, w3, nd)
      +hne23 = FT3.nd3_ne23(w1, w2, w3, nd)
      +efix = FT3.guesses_skip_6(G, pp, inf, G, w1, w2, w3, tree, ble, hz,
                h6le, hne12, hne13, hne23, efb1, efb2, efb3)
      %Equal.sym(Nat, cost, 6n, ec6) :
        {Nat.is_le(_, Eval.Eval.cost_of(FS.FS.ref_run_at(1n+pp, inf, G, ws3)))
         == True{} : Bool}
      FV.FV.le_ref_of_guesses_fixed(1n+pp, inf, G, ws3,
        SolveRef.Best{tree, 6n}, ble, h6le, efix)

def FT3.done_three_le_ref(+p: Nat, +inf: Nat, +G: +List<+List<Nat>>,
    +w1: +List<Nat>, +w2: +List<Nat>, +w3: +List<Nat>,
    +tree: Tree.Tree, +cost: Nat,
    +ble: {Nat.is_le(3n, p) == True{} : Bool},
    +hz: {Nat.is_lt(0n, inf) == True{} : Bool},
    +h6: {Nat.is_lt(6n, inf) == True{} : Bool},
    +nd: {FN.FN.no_dup_ref(w1 <> (w2 <> (w3 <> Nil{}))) == True{} : Bool},
    +hok: {FT3.done_three_ok_b(G, w1, w2, w3, tree, cost) == True{} : Bool}) ->
  {Nat.is_le(cost, Eval.Eval.cost_of(
     FS.FS.ref_run_at(p, inf, G, w1 <> (w2 <> (w3 <> Nil{})))))
   == True{} : Bool}:
  match p:
    case 0n:
      Empty.absurd(
        {Nat.is_le(cost, Eval.Eval.cost_of(
           FS.FS.ref_run_at(0n, inf, G, w1 <> (w2 <> (w3 <> Nil{})))))
         == True{} : Bool},
        Logic.Proof.false_ne_true(ble))
    case 1n++pp:
      +ws3 : +List<+List<Nat>> = w1 <> (w2 <> (w3 <> Nil{}))
      +r1 = Logic.Proof.and_true_r(FV.FV.valid_b(tree, G, ws3),
              Bool.and(Nat.is_le(Tree.cost(tree, ws3), cost),
                Bool.or(Nat.is_eq(cost, 5n),
                  Bool.and(Nat.is_eq(cost, 6n),
                    Bool.and(
                      Feedback.feedback_eq(Feedback.feedback(w1, w2),
                        Feedback.feedback(w1, w3)),
                      Bool.and(
                        Feedback.feedback_eq(Feedback.feedback(w2, w1),
                          Feedback.feedback(w2, w3)),
                        Feedback.feedback_eq(Feedback.feedback(w3, w1),
                          Feedback.feedback(w3, w2))))))), hok)
      +hor = Logic.Proof.and_true_r(Nat.is_le(Tree.cost(tree, ws3), cost),
               Bool.or(Nat.is_eq(cost, 5n),
                 Bool.and(Nat.is_eq(cost, 6n),
                   Bool.and(
                     Feedback.feedback_eq(Feedback.feedback(w1, w2),
                       Feedback.feedback(w1, w3)),
                     Bool.and(
                       Feedback.feedback_eq(Feedback.feedback(w2, w1),
                         Feedback.feedback(w2, w3)),
                       Feedback.feedback_eq(Feedback.feedback(w3, w1),
                         Feedback.feedback(w3, w2)))))), r1)
      FT3.done_three_le_ref_case(pp, inf, G, w1, w2, w3, tree, cost,
        ble, hz, h6, nd, Nat.is_eq(cost, 5n), {==}, hor)
