import Base
import ./LAWS.bend as Laws
import ./src/feedback.bend as Feedback
import ./src/tree.bend as Tree
import ./src/solve.bend as Solve
import ./src/json.bend as Json
import ./proofs/spec.bend as Spec
import ./proofs/logic.bend as Logic
import ./proofs/nat.bend as NatProof
import ./proofs/min.bend as Min

def Bool.disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def Bool.false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.disc(_)
  Unit{}

def Color.disc(c: Feedback.Color) -> Type:
  match c:
    case Feedback.Gray{}:
      Unit
    case Feedback.Yellow{}:
      Unit
    case Feedback.Green{}:
      Empty

def Color.gray_ne_green(e: {Feedback.Gray{} == Feedback.Green{} : Feedback.Color}) -> Empty:
  %e : Color.disc(_)
  Unit{}

def Color.yellow_ne_green(e: {Feedback.Yellow{} == Feedback.Green{} : Feedback.Color}) -> Empty:
  %e : Color.disc(_)
  Unit{}

def Nat.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def Nat.is_eq_refl(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.is_eq_refl(p)

def Nat.is_eq_true(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, Bool.false_ne_true(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, Bool.false_ne_true(e))
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, n => 1n+n, ap, bp, Nat.is_eq_true(ap, bp, e))

def Nat.succ_disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def Nat.zero_ne_succ(n: Nat, e: {0n == 1n+n : Nat}) -> Empty:
  e2 = Equal.sym(Nat, 0n, 1n+n, e)
  %e2 : Nat.succ_disc(_)
  Unit{}

def FeedbackProof.feedback_length_go(g: +List<Nat>, a: +List<Nat>, +pool: +List<Nat>, +same: Bool) ->
  {List.length(&2, Feedback.Color, Feedback.feedback.go(g, a, pool, same)) == List.length(&2, Nat, g) : Nat}:
  match g:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      match a:
        case Nil{}:
          Equal.cong(Nat, Nat, n => 1n+n,
            List.length(&2, Feedback.Color, Feedback.feedback.go(t, Nil{}, Nil{}, False{})),
            List.length(&2, Nat, t),
            FeedbackProof.feedback_length_go(t, Nil{}, Nil{}, False{}))
        case Con{+a0, +at}:
          match same:
            case True{}:
              Equal.cong(Nat, Nat, n => 1n+n,
                List.length(&2, Feedback.Color, Feedback.feedback.go(t, at, pool, Feedback.next_same(t, at))),
                List.length(&2, Nat, t),
                FeedbackProof.feedback_length_go(t, at, pool, Feedback.next_same(t, at)))
            case False{}:
              Equal.cong(Nat, Nat, n => 1n+n,
                List.length(&2, Feedback.Color, Feedback.feedback.go(t, at, Feedback.consume_pool(h, pool, Feedback.next_letter_same(h, pool)), Feedback.next_same(t, at))),
                List.length(&2, Nat, t),
                FeedbackProof.feedback_length_go(t, at, Feedback.consume_pool(h, pool, Feedback.next_letter_same(h, pool)), Feedback.next_same(t, at)))

def Laws.feedback_length(g, a):
  FeedbackProof.feedback_length_go(g, a, Feedback.non_green(g, a), Feedback.next_same(g, a))

def SameOK(w: +List<Nat>, same: Bool) -> Type:
  match w:
    case Nil{}:
      Unit
    case Con{h, t}:
      {True{} == same : Bool}

def Proof.same_ok_next(w: +List<Nat>) -> SameOK(w, Feedback.next_same(w, w)):
  match w:
    case Nil{}:
      Unit{}
    case Con{h, t}:
      Equal.sym(Bool, Nat.is_eq(h, h), True{}, Nat.is_eq_refl(h))

def Proof.all_green_go(w: +List<Nat>, +pool: +List<Nat>, +same: Bool, ok: SameOK(w, same)) ->
  Feedback.AllGreen(Feedback.feedback.go(w, w, pool, same)):
  match w:
    case Nil{}:
      Unit{}
    case Con{+h, +t}:
      %ok : Feedback.AllGreen(Feedback.feedback.go(h<>t, h<>t, pool, _))
      ({==}, Proof.all_green_go(t, pool, Feedback.next_same(t, t), Proof.same_ok_next(t)))

def Laws.feedback_all_green_when_equal(w):
  Proof.all_green_go(w, Feedback.non_green(w, w), Feedback.next_same(w, w), Proof.same_ok_next(w))

def FeedbackProof.consume_color_ne_green(+x: Nat, pool: +List<Nat>, same: Bool,
    e: {Feedback.consume_color(x, pool, same) == Feedback.Green{} : Feedback.Color}) -> Empty:
  match pool:
    case Nil{}:
      Color.gray_ne_green(e)
    case Con{h, +t}:
      match same:
        case True{}:
          Color.yellow_ne_green(e)
        case False{}:
          FeedbackProof.consume_color_ne_green(x, t, Feedback.next_letter_same(x, t), e)

def FeedbackProof.all_green_equal_go(g: +List<Nat>, a: +List<Nat>, +pool: +List<Nat>, same: Bool,
    link: {same == Feedback.next_same(g, a) : Bool},
    p: Feedback.AllGreen(Feedback.feedback.go(g, a, pool, same)),
    e: {List.length(&2, Nat, g) == List.length(&2, Nat, a) : Nat}) ->
  {g == a : +List<Nat>}:
  match g a:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+a0, +at}:
      Empty.absurd({Nil{} == a0 <> at : +List<Nat>},
                   Nat.zero_ne_succ(List.length(&2, Nat, at), e))
    case Con{+h, +t} Nil{}:
      (eg, rest) = p
      Empty.absurd({h <> t == Nil{} : +List<Nat>}, Color.gray_ne_green(eg))
    case Con{+h, +t} Con{+a0, +at}:
      match same:
        case True{}:
          (eg, p_tail) = p
          e_h = Nat.is_eq_true(h, a0, Equal.sym(Bool, True{}, Feedback.next_same(h<>t, a0<>at), link))
          e_len = Equal.cong(Nat, Nat, Nat.pred,
                             Nat.add(1n, List.length(&2, Nat, t)),
                             Nat.add(1n, List.length(&2, Nat, at)), e)
          e_tail = FeedbackProof.all_green_equal_go(t, at, pool, Feedback.next_same(t, at), {==}, p_tail, e_len)
          e1 = Equal.cong(Nat, +List<Nat>, x => x <> t, h, a0, e_h)
          e2 = Equal.cong(+List<Nat>, +List<Nat>, w => a0 <> w, t, at, e_tail)
          Equal.trans(+List<Nat>, h <> t, a0 <> t, a0 <> at, e1, e2)
        case False{}:
          (ec, rest) = p
          Empty.absurd({h <> t == a0 <> at : +List<Nat>},
                       FeedbackProof.consume_color_ne_green(h, pool, Feedback.next_letter_same(h, pool), ec))

def Laws.feedback_all_green_only_if_equal(g, a, p, e):
  FeedbackProof.all_green_equal_go(g, a, Feedback.non_green(g, a), Feedback.next_same(g, a), {==}, p, e)

def Color.eq_refl(c: Feedback.Color) -> {Feedback.Color.eq(c, c) == True{} : Bool}:
  match c:
    case Feedback.Gray{}:
      {==}
    case Feedback.Yellow{}:
      {==}
    case Feedback.Green{}:
      {==}

def FeedbackProof.pair_color_eq_refl(c: Feedback.Color) -> {Feedback.pair_color_eq((c, c)) == True{} : Bool}:
  Color.eq_refl(c)

def FeedbackProof.feedback_eq_refl(+a: +List<Feedback.Color>) ->
  {Feedback.feedback_eq(a, a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, Feedback.Color.eq(h, h), True{}, Color.eq_refl(h)) : {
        Bool.and(Cmp.is_eq(Nat.cmp(List.length(&2, Feedback.Color, t), List.length(&2, Feedback.Color, t))),
                 List.all.if(u => List.all(&1, Feedback.Color & Feedback.Color, Feedback.pair_color_eq,
                                            List.zip(&2, Feedback.Color, &2, Feedback.Color, t, t)),
                              _))
        == True{} : Bool}
      %Equal.sym(Bool, Feedback.feedback_eq(t, t), True{}, FeedbackProof.feedback_eq_refl(t)) : {
        _ == True{} : Bool}
      {==}

def FeedbackProof.pair_nat_eq_refl(n: Nat) -> {Feedback.pair_nat_eq((n, n)) == True{} : Bool}:
  Nat.is_eq_refl(n)

def FeedbackProof.word_eq_refl(+a: +List<Nat>) -> {Feedback.word_eq(a, a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, Nat.is_eq(h, h), True{}, Nat.is_eq_refl(h)) : {
        Bool.and(Nat.is_eq(List.length(&2, Nat, t), List.length(&2, Nat, t)),
                 List.all.if(u => List.all(&1, Nat & Nat, Feedback.pair_nat_eq,
                                            List.zip(&2, Nat, &2, Nat, t, t)),
                              _))
        == True{} : Bool}
      %Equal.sym(Bool, Feedback.word_eq(t, t), True{}, FeedbackProof.word_eq_refl(t)) : {
        _ == True{} : Bool}
      {==}

def Bool.and_true_l(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) ->
  {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Bool.false_ne_true(e))

def Bool.and_true_r(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) ->
  {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, Bool.false_ne_true(e))

def SolveProof.GroupsSmaller(+S: +List<+List<Nat>>, +groups: +List<Solve.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Solve.Group{f, ws}:
          {Nat.is_lt(Solve.len_words(ws), Solve.len_words(S)) == True{} : Bool}
          & SolveProof.GroupsSmaller(S, rest)

def SolveProof.groups_smaller_sound(+S: +List<+List<Nat>>, +groups: +List<Solve.Group>,
    +e: {Solve.groups_smaller(S, groups) == True{} : Bool}) ->
  SolveProof.GroupsSmaller(S, groups):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Solve.Group{+f, +ws}:
          (Bool.and_true_l(Nat.is_lt(Solve.len_words(ws), Solve.len_words(S)),
                            Solve.groups_smaller(S, rest), e),
           SolveProof.groups_smaller_sound(S, rest,
             Bool.and_true_r(Nat.is_lt(Solve.len_words(ws), Solve.len_words(S)),
                             Solve.groups_smaller(S, rest), e)))

def Bool.true_ne_false(e: {True{} == False{} : Bool}) -> Empty:
  Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, e))

def Cmp.lt_of_ge_false(c: Cmp, e: {Cmp.is_ge(c) == False{} : Bool}) ->
  {Cmp.is_lt(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_lt(EQ{}) == True{} : Bool}, Bool.true_ne_false(e))
    case GT{}:
      Empty.absurd({Cmp.is_lt(GT{}) == True{} : Bool}, Bool.true_ne_false(e))

def Cmp.ge_of_lt_false(c: Cmp, e: {Cmp.is_lt(c) == False{} : Bool}) ->
  {Cmp.is_ge(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_ge(LT{}) == True{} : Bool}, Bool.true_ne_false(e))
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Nat.lt_of_ge_false(a: Nat, b: Nat, e: {Nat.is_ge(a, b) == False{} : Bool}) ->
  {Nat.is_lt(a, b) == True{} : Bool}:
  Cmp.lt_of_ge_false(Nat.cmp(a, b), e)

def Nat.ge_of_lt_false(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == False{} : Bool}) ->
  {Nat.is_ge(a, b) == True{} : Bool}:
  Cmp.ge_of_lt_false(Nat.cmp(a, b), e)

def Nat.cmp_refl(n: Nat) -> {Nat.cmp(n, n) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Nat.cmp_refl(p)

def Nat.is_lt_self_false(n: Nat) -> {Nat.is_lt(n, n) == False{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(n, n), EQ{}, Nat.cmp_refl(n)) : {Cmp.is_lt(_) == False{} : Bool}
  {==}

def SolveProof.inf_not_lt_self(n: Nat, e: {Nat.is_lt(n, n) == True{} : Bool}) -> Empty:
  Bool.false_ne_true(Equal.trans(Bool, False{}, Nat.is_lt(n, n), True{},
    Equal.sym(Bool, Nat.is_lt(n, n), False{}, Nat.is_lt_self_false(n)), e))

def SolveProof.sat_add_lt_l_go(+inf: Nat, +a: Nat, +b: Nat, +ga: Bool, +gb: Bool,
    +ea: {ga == Nat.is_ge(a, inf) : Bool},
    +eb: {gb == Nat.is_ge(b, inf) : Bool},
    +e: {Nat.is_lt(Feedback.Bool.case(Nat, ga, inf,
                            Feedback.Bool.case(Nat, gb, inf, Nat.add(a, b))), inf) == True{} : Bool}) ->
  {Nat.is_lt(a, inf) == True{} : Bool}:
  match ga:
    case True{}:
      Empty.absurd({Nat.is_lt(a, inf) == True{} : Bool}, SolveProof.inf_not_lt_self(inf, e))
    case False{}:
      Nat.lt_of_ge_false(a, inf, Equal.sym(Bool, False{}, Nat.is_ge(a, inf), ea))

def SolveProof.sat_add_lt_l(+inf: Nat, +a: Nat, +b: Nat,
    +e: {Nat.is_lt(Solve.sat_add(inf, a, b), inf) == True{} : Bool}) ->
  {Nat.is_lt(a, inf) == True{} : Bool}:
  SolveProof.sat_add_lt_l_go(inf, a, b, Nat.is_ge(a, inf), Nat.is_ge(b, inf), {==}, {==}, e)

def SolveProof.sat_add_lt_r_go(+inf: Nat, +a: Nat, +b: Nat, +ga: Bool, +gb: Bool,
    +ea: {ga == Nat.is_ge(a, inf) : Bool},
    +eb: {gb == Nat.is_ge(b, inf) : Bool},
    +e: {Nat.is_lt(Feedback.Bool.case(Nat, ga, inf,
                            Feedback.Bool.case(Nat, gb, inf, Nat.add(a, b))), inf) == True{} : Bool}) ->
  {Nat.is_lt(b, inf) == True{} : Bool}:
  match ga:
    case True{}:
      Empty.absurd({Nat.is_lt(b, inf) == True{} : Bool}, SolveProof.inf_not_lt_self(inf, e))
    case False{}:
      match gb:
        case True{}:
          Empty.absurd({Nat.is_lt(b, inf) == True{} : Bool}, SolveProof.inf_not_lt_self(inf, e))
        case False{}:
          Nat.lt_of_ge_false(b, inf, Equal.sym(Bool, False{}, Nat.is_ge(b, inf), eb))

def SolveProof.sat_add_lt_r(+inf: Nat, +a: Nat, +b: Nat,
    +e: {Nat.is_lt(Solve.sat_add(inf, a, b), inf) == True{} : Bool}) ->
  {Nat.is_lt(b, inf) == True{} : Bool}:
  SolveProof.sat_add_lt_r_go(inf, a, b, Nat.is_ge(a, inf), Nat.is_ge(b, inf), {==}, {==}, e)

def SolveProof.MaybeTree.value(m: Maybe<Tree.Tree>) -> Tree.Tree:
  match m:
    case None{}:
      Tree.Node{Nil{}, Nil{}}
    case Some{t}:
      t

def SolveProof.MaybeTree.disc(m: Maybe<Tree.Tree>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{t}:
      Empty

def SolveProof.MaybeTree.none_ne_some(T: Tree.Tree, e: {None{} == Some{T} : Maybe<Tree.Tree>}) -> Empty:
  %e : SolveProof.MaybeTree.disc(_)
  Unit{}

def SolveProof.MaybeTree.some_inj(x: Tree.Tree, y: Tree.Tree,
    e: {Some{x} == Some{y} : Maybe<Tree.Tree>}) -> {x == y : Tree.Tree}:
  Equal.cong(Maybe<Tree.Tree>, Tree.Tree, SolveProof.MaybeTree.value, Some{x}, Some{y}, e)

def SolveProof.BestIs(inf: Nat, best: Solve.Best, T: Tree.Tree) -> Type:
  match best:
    case Solve.Best{tree, cost}:
      {tree == T : Tree.Tree} & {Nat.is_lt(cost, inf) == True{} : Bool}

def SolveProof.best_to_maybe_some_bool(+inf: Nat, +tree: Tree.Tree, +cost: Nat, T: Tree.Tree,
    b: Bool, +eb: {b == Nat.is_ge(cost, inf) : Bool},
    +e: {Feedback.Bool.case(Maybe<Tree.Tree>, b, None{}, Some{tree}) == Some{T} : Maybe<Tree.Tree>}) ->
  {tree == T : Tree.Tree} & {Nat.is_lt(cost, inf) == True{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({tree == T : Tree.Tree} & {Nat.is_lt(cost, inf) == True{} : Bool},
                   SolveProof.MaybeTree.none_ne_some(T, e))
    case False{}:
      (SolveProof.MaybeTree.some_inj(tree, T, e),
       Nat.lt_of_ge_false(cost, inf, Equal.sym(Bool, False{}, Nat.is_ge(cost, inf), eb)))

def SolveProof.best_to_maybe_some(+inf: Nat, best: Solve.Best, T: Tree.Tree,
    +e: {Solve.best_to_maybe(inf, best) == Some{T} : Maybe<Tree.Tree>}) ->
  SolveProof.BestIs(inf, best, T):
  match best:
    case Solve.Best{+tree, +cost}:
      SolveProof.best_to_maybe_some_bool(inf, tree, cost, T, Nat.is_ge(cost, inf), {==}, e)

def Color.eq_true(a: Feedback.Color, b: Feedback.Color,
    e: {Feedback.Color.eq(a, b) == True{} : Bool}) -> {a == b : Feedback.Color}:
  match a b:
    case Feedback.Gray{} Feedback.Gray{}:
      {==}
    case Feedback.Gray{} Feedback.Yellow{}:
      Empty.absurd({Feedback.Gray{} == Feedback.Yellow{} : Feedback.Color}, Bool.false_ne_true(e))
    case Feedback.Gray{} Feedback.Green{}:
      Empty.absurd({Feedback.Gray{} == Feedback.Green{} : Feedback.Color}, Bool.false_ne_true(e))
    case Feedback.Yellow{} Feedback.Gray{}:
      Empty.absurd({Feedback.Yellow{} == Feedback.Gray{} : Feedback.Color}, Bool.false_ne_true(e))
    case Feedback.Yellow{} Feedback.Yellow{}:
      {==}
    case Feedback.Yellow{} Feedback.Green{}:
      Empty.absurd({Feedback.Yellow{} == Feedback.Green{} : Feedback.Color}, Bool.false_ne_true(e))
    case Feedback.Green{} Feedback.Gray{}:
      Empty.absurd({Feedback.Green{} == Feedback.Gray{} : Feedback.Color}, Bool.false_ne_true(e))
    case Feedback.Green{} Feedback.Yellow{}:
      Empty.absurd({Feedback.Green{} == Feedback.Yellow{} : Feedback.Color}, Bool.false_ne_true(e))
    case Feedback.Green{} Feedback.Green{}:
      {==}

def Color.eq_trans(+a: Feedback.Color, +b: Feedback.Color, +c: Feedback.Color,
    +eab: {Feedback.Color.eq(a, b) == True{} : Bool},
    +ebc: {Feedback.Color.eq(b, c) == True{} : Bool}) ->
  {Feedback.Color.eq(a, c) == True{} : Bool}:
  eac = Equal.trans(Feedback.Color, a, b, c, Color.eq_true(a, b, eab), Color.eq_true(b, c, ebc))
  %eac : {Feedback.Color.eq(a, _) == True{} : Bool}
  Color.eq_refl(a)

def SolveProof.all_if_true_l(rest: Unit -> Bool, hit: Bool,
    e: {List.all.if(rest, hit) == True{} : Bool}) -> {hit == True{} : Bool}:
  match hit:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, Bool.false_ne_true(e))

def SolveProof.all_if_true_r(rest: Unit -> Bool, hit: Bool,
    e: {List.all.if(rest, hit) == True{} : Bool}) -> {rest(Unit{}) == True{} : Bool}:
  match hit:
    case True{}:
      e
    case False{}:
      Empty.absurd({rest(Unit{}) == True{} : Bool}, Bool.false_ne_true(e))

def Nat.succ_ne_zero(n: Nat, e: {1n+n == 0n : Nat}) -> Empty:
  Nat.zero_ne_succ(n, Equal.sym(Nat, 1n+n, 0n, e))

def SolveProof.all_pairs(+a: +List<Feedback.Color>, +b: +List<Feedback.Color>) -> Bool:
  List.all(&1, Feedback.Color & Feedback.Color, Feedback.pair_color_eq,
           List.zip(&2, Feedback.Color, &2, Feedback.Color, a, b))

def SolveProof.all_if_intro(rest: Unit -> Bool, hit: Bool,
    h: {hit == True{} : Bool}, t: {rest(Unit{}) == True{} : Bool}) ->
  {List.all.if(rest, hit) == True{} : Bool}:
  match hit:
    case True{}:
      t
    case False{}:
      Empty.absurd({List.all.if(rest, False{}) == True{} : Bool}, Bool.false_ne_true(h))

def SolveProof.all_pairs_trans(+a: +List<Feedback.Color>, +b: +List<Feedback.Color>,
    +c: +List<Feedback.Color>,
    +lab: {List.length(&2, Feedback.Color, a) == List.length(&2, Feedback.Color, b) : Nat},
    +lbc: {List.length(&2, Feedback.Color, b) == List.length(&2, Feedback.Color, c) : Nat},
    +eab: {SolveProof.all_pairs(a, b) == True{} : Bool},
    +ebc: {SolveProof.all_pairs(b, c) == True{} : Bool}) ->
  {SolveProof.all_pairs(a, c) == True{} : Bool}:
  match a b c:
    case Nil{} _ _:
      {==}
    case Con{+a0, +at} Nil{} Nil{}:
      {==}
    case Con{+a0, +at} Nil{} Con{+c0, +ct}:
      Empty.absurd({SolveProof.all_pairs(a0 <> at, c0 <> ct) == True{} : Bool},
                   Nat.succ_ne_zero(List.length(&2, Feedback.Color, at), lab))
    case Con{+a0, +at} Con{+b0, +bt} Nil{}:
      {==}
    case Con{+a0, +at} Con{+b0, +bt} Con{+c0, +ct}:
      +lab_t : {List.length(&2, Feedback.Color, at) == List.length(&2, Feedback.Color, bt) : Nat} =
        Equal.cong(Nat, Nat, Nat.pred,
                   List.length(&2, Feedback.Color, a0 <> at),
                   List.length(&2, Feedback.Color, b0 <> bt), lab)
      +lbc_t : {List.length(&2, Feedback.Color, bt) == List.length(&2, Feedback.Color, ct) : Nat} =
        Equal.cong(Nat, Nat, Nat.pred,
                   List.length(&2, Feedback.Color, b0 <> bt),
                   List.length(&2, Feedback.Color, c0 <> ct), lbc)
      +eq_ab : {Feedback.Color.eq(a0, b0) == True{} : Bool} =
        SolveProof.all_if_true_l(u => SolveProof.all_pairs(at, bt), Feedback.Color.eq(a0, b0), eab)
      +tail_ab : {SolveProof.all_pairs(at, bt) == True{} : Bool} =
        SolveProof.all_if_true_r(u => SolveProof.all_pairs(at, bt), Feedback.Color.eq(a0, b0), eab)
      +eq_bc : {Feedback.Color.eq(b0, c0) == True{} : Bool} =
        SolveProof.all_if_true_l(u => SolveProof.all_pairs(bt, ct), Feedback.Color.eq(b0, c0), ebc)
      +tail_bc : {SolveProof.all_pairs(bt, ct) == True{} : Bool} =
        SolveProof.all_if_true_r(u => SolveProof.all_pairs(bt, ct), Feedback.Color.eq(b0, c0), ebc)
      +eq_ac : {Feedback.Color.eq(a0, c0) == True{} : Bool} =
        Color.eq_trans(a0, b0, c0, eq_ab, eq_bc)
      +tail_ac : {SolveProof.all_pairs(at, ct) == True{} : Bool} =
        SolveProof.all_pairs_trans(at, bt, ct, lab_t, lbc_t, tail_ab, tail_bc)
      SolveProof.all_if_intro(u => SolveProof.all_pairs(at, ct), Feedback.Color.eq(a0, c0),
                              eq_ac, tail_ac)

def FeedbackProof.feedback_eq_trans(+a: +List<Feedback.Color>, +b: +List<Feedback.Color>,
    +c: +List<Feedback.Color>,
    +eab: {Feedback.feedback_eq(a, b) == True{} : Bool},
    +ebc: {Feedback.feedback_eq(b, c) == True{} : Bool}) ->
  {Feedback.feedback_eq(a, c) == True{} : Bool}:
  +len_ab : {List.length(&2, Feedback.Color, a) == List.length(&2, Feedback.Color, b) : Nat} =
    Nat.is_eq_true(List.length(&2, Feedback.Color, a), List.length(&2, Feedback.Color, b),
      Bool.and_true_l(Nat.is_eq(List.length(&2, Feedback.Color, a), List.length(&2, Feedback.Color, b)),
                      SolveProof.all_pairs(a, b), eab))
  +len_bc : {List.length(&2, Feedback.Color, b) == List.length(&2, Feedback.Color, c) : Nat} =
    Nat.is_eq_true(List.length(&2, Feedback.Color, b), List.length(&2, Feedback.Color, c),
      Bool.and_true_l(Nat.is_eq(List.length(&2, Feedback.Color, b), List.length(&2, Feedback.Color, c)),
                      SolveProof.all_pairs(b, c), ebc))
  +len_ac : {List.length(&2, Feedback.Color, a) == List.length(&2, Feedback.Color, c) : Nat} =
    Equal.trans(Nat, List.length(&2, Feedback.Color, a), List.length(&2, Feedback.Color, b),
                List.length(&2, Feedback.Color, c), len_ab, len_bc)
  +all_ac : {SolveProof.all_pairs(a, c) == True{} : Bool} =
    SolveProof.all_pairs_trans(a, b, c, len_ab, len_bc,
      Bool.and_true_r(Nat.is_eq(List.length(&2, Feedback.Color, a), List.length(&2, Feedback.Color, b)),
                      SolveProof.all_pairs(a, b), eab),
      Bool.and_true_r(Nat.is_eq(List.length(&2, Feedback.Color, b), List.length(&2, Feedback.Color, c)),
                      SolveProof.all_pairs(b, c), ebc))
  %Equal.sym(Nat, List.length(&2, Feedback.Color, a), List.length(&2, Feedback.Color, c), len_ac) : {
    Bool.and(Nat.is_eq(_, List.length(&2, Feedback.Color, c)), SolveProof.all_pairs(a, c))
    == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(List.length(&2, Feedback.Color, c), List.length(&2, Feedback.Color, c)),
             True{}, Nat.is_eq_refl(List.length(&2, Feedback.Color, c))) : {
    Bool.and(_, SolveProof.all_pairs(a, c)) == True{} : Bool}
  all_ac
