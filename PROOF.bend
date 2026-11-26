import Base
import ./LAWS.bend as Laws
import ./src/feedback.bend as Feedback
import ./src/tree.bend as Tree
import ./src/groups.bend as Groups
import ./src/solve_ref.bend as SolveRef
import ./src/json.bend as Json
import ./src/spec_json.bend as JsonSpec
import ./proofs/json_spec.bend as JsonProof
import ./proofs/spec.bend as Spec
import ./proofs/logic.bend as Logic
import ./proofs/nat.bend as NatProof
import ./proofs/min.bend as Min
import ./proofs/feedback.bend as FbProof
import ./proofs/depth.bend as DepthProof
import ./proofs/groups.bend as Grp
import ./proofs/best_nil.bend as BaseCase
import ./proofs/nodecost.bend as NodeCost
import ./proofs/cover.bend as CoverProof
import ./proofs/depthgroups.bend as DepthGroups
import ./proofs/validbag.bend as ValidBag
import ./proofs/solvevalid.bend as SVProof
import ./proofs/mainvalid.bend as MVProof
import ./proofs/optimalvalue.bend as OVProof
import ./proofs/classbound.bend as CBProof
import ./proofs/classbound_kids.bend as CBKids
import ./proofs/classbound_sum.bend as CBSum
import ./proofs/optfold.bend as OQProof
import ./proofs/optsum.bend as OQSumProof
import ./proofs/optguess.bend as OQGuessProof
import ./proofs/optnode.bend as OQNodeProof
import ./proofs/optind.bend as OQIndProof
import ./proofs/optcost.bend as OQCostProof
import ./proofs/optcomplete.bend as OQCompleteProof
import ./proofs/eval.bend as EvalProof
import ./proofs/optstrong.bend as OQStrongProof
import ./proofs/lb_size.bend as LBProof
import ./proofs/lb_twice.bend as LBProof2
import ./proofs/lb_capacity.bend as LBProof3
import ./src/solve_fast.bend as SolveFast
import ./proofs/fast_step.bend as FSProof
import ./proofs/fast_better.bend as FSPrune
import ./proofs/fast_groups.bend as FSGroups
import ./proofs/fast_lb.bend as FSLB
import ./proofs/fast_opt.bend as FSOpt
import ./src/solve_par.bend as SolvePar
import ./proofs/par_fold.bend as ParFold
import ./proofs/lb_nodup.bend as LBProof4
import ./proofs/lb_classes.bend as LBProof5
import ./proofs/lb_decomp.bend as LBProof6
import ./proofs/lb_adsplit.bend as LBProof7
import ./proofs/lb_capacity_sound.bend as LBProof8
import ./src/solve_k.bend as SolveK
import ./proofs/par_chunk.bend as ParChunk
import ./proofs/core_list.bend as CoreList
import ./proofs/core_nat.bend as CoreNat
import ./proofs/core_store.bend as CoreStore
import ./proofs/core_region.bend as CoreRegion
import ./proofs/core_dcount.bend as CoreDCount
import ./proofs/core_cells.bend as CoreCells

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

# Generic list algebra for the parser traces.
def ListProof.append_nil(a, -A: Kind(a), xs: List<a, A>) ->
  {List.append(a, A, xs, Nil{}) == xs : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<a, A>, List<a, A>, l => h <> l,
                 List.append(a, A, t, Nil{}), t,
                 ListProof.append_nil(a, A, t))

def ListProof.append_assoc(a, -A: Kind(a), xs: List<a, A>, ys: List<a, A>, zs: List<a, A>) ->
  {List.append(a, A, List.append(a, A, xs, ys), zs)
    == List.append(a, A, xs, List.append(a, A, ys, zs)) : List<a, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(List<a, A>, List<a, A>, l => h <> l,
                 List.append(a, A, List.append(a, A, t, ys), zs),
                 List.append(a, A, t, List.append(a, A, ys, zs)),
                 ListProof.append_assoc(a, A, t, ys, zs))

# Arithmetic on the decimal digit accumulator.
def NatAdd.add_succ(a: Nat, b: Nat) ->
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %NatAdd.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def NatAdd.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %NatAdd.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def NatAdd.add_one(+a: Nat) -> {Nat.add(a, 1n) == 1n+a : Nat}:
  e1 = NatAdd.add_succ(a, 0n)
  e2 = Equal.cong(Nat, Nat, m => 1n+m, Nat.add(a, 0n), a, NatAdd.add_zero(a))
  Equal.trans(Nat, Nat.add(a, 1n), 1n+Nat.add(a, 0n), 1n+a, e1, e2)

def StringProof.append_assoc(a: String, b: String, c: String) ->
  {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, r => SCon{h, r},
                 String.append(String.append(t, b), c),
                 String.append(t, String.append(b, c)),
                 StringProof.append_assoc(t, b, c))

def NatAdd.add_assoc(a: Nat, b: Nat, c: Nat) ->
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                 Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)),
                 NatAdd.add_assoc(p, b, c))

def NatAdd.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, NatAdd.add_zero(b))
    case 1n++p:
      e1 = Equal.cong(Nat, Nat, x => Nat.add(1n, x),
             Nat.add(p, b), Nat.add(b, p), NatAdd.add_comm(p, b))
      e2 = Equal.sym(Nat, Nat.add(b, 1n+p), Nat.add(1n, Nat.add(b, p)),
             NatAdd.add_succ(b, p))
      Equal.trans(Nat, Nat.add(1n+p, b), Nat.add(1n, Nat.add(b, p)),
                  Nat.add(b, 1n+p), e1, e2)

# (a + b) + (c + d) = (a + c) + (b + d), the regrouping used to distribute a
# product over a sum.
def NatAdd.add4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) ->
  {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  e1 = NatAdd.add_assoc(a, b, Nat.add(c, d))
  i1 = Equal.sym(Nat, Nat.add(Nat.add(b, c), d), Nat.add(b, Nat.add(c, d)),
                 NatAdd.add_assoc(b, c, d))
  i2 = Equal.cong(Nat, Nat, x => Nat.add(x, d),
                  Nat.add(b, c), Nat.add(c, b), NatAdd.add_comm(b, c))
  i3 = NatAdd.add_assoc(c, b, d)
  inner = Equal.trans(Nat, Nat.add(b, Nat.add(c, d)), Nat.add(Nat.add(b, c), d),
                      Nat.add(c, Nat.add(b, d)), i1,
                      Equal.trans(Nat, Nat.add(Nat.add(b, c), d),
                                  Nat.add(Nat.add(c, b), d),
                                  Nat.add(c, Nat.add(b, d)), i2, i3))
  e2 = Equal.cong(Nat, Nat, x => Nat.add(a, x),
                  Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), inner)
  e3 = Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)),
                 Nat.add(a, Nat.add(c, Nat.add(b, d))),
                 NatAdd.add_assoc(a, c, Nat.add(b, d)))
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)),
              Nat.add(a, Nat.add(b, Nat.add(c, d))),
              Nat.add(Nat.add(a, c), Nat.add(b, d)), e1,
              Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))),
                          Nat.add(a, Nat.add(c, Nat.add(b, d))),
                          Nat.add(Nat.add(a, c), Nat.add(b, d)), e2, e3))

def NatMul.mul_add(+a: Nat, +b: Nat, +c: Nat) ->
  {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      e1 = Equal.cong(Nat, Nat, x => Nat.add(Nat.add(b, c), x),
             Nat.mul(p, Nat.add(b, c)), Nat.add(Nat.mul(p, b), Nat.mul(p, c)),
             NatMul.mul_add(p, b, c))
      e2 = NatAdd.add4(b, c, Nat.mul(p, b), Nat.mul(p, c))
      Equal.trans(Nat, Nat.mul(1n+p, Nat.add(b, c)),
                  Nat.add(Nat.add(b, c), Nat.add(Nat.mul(p, b), Nat.mul(p, c))),
                  Nat.add(Nat.add(b, Nat.mul(p, b)), Nat.add(c, Nat.mul(p, c))),
                  e1, e2)

def NatMul.mul_one(a: Nat) -> {Nat.mul(a, 1n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                 Nat.mul(p, 1n), p, NatMul.mul_one(p))

def NatMul.mul10_succ(+x: Nat) ->
  {Nat.mul(10n, Nat.add(x, 1n)) == Nat.add(Nat.mul(10n, x), 10n) : Nat}:
  e1 = NatMul.mul_add(10n, x, 1n)
  e2 = Equal.cong(Nat, Nat, y => Nat.add(Nat.mul(10n, x), y),
                  Nat.mul(10n, 1n), 10n, NatMul.mul_one(10n))
  Equal.trans(Nat, Nat.mul(10n, Nat.add(x, 1n)),
              Nat.add(Nat.mul(10n, x), Nat.mul(10n, 1n)),
              Nat.add(Nat.mul(10n, x), 10n), e1, e2)

# Decimal digits.
def DigitList.nonempty(+ds: +List<Json.Digit>) -> Type:
  match ds:
    case Nil{}:
      Empty
    case Con{_, _}:
      Unit

# Adding one always leaves a nonempty list.
def DigitList.inc_nonempty(+ds: +List<Json.Digit>) -> DigitList.nonempty(Json.digits_inc(ds)):
  match ds:
    case Nil{}:
      Unit{}
    case Con{d, t}:
      match d:
        case Json.D0{}:
          Unit{}
        case Json.D1{}:
          Unit{}
        case Json.D2{}:
          Unit{}
        case Json.D3{}:
          Unit{}
        case Json.D4{}:
          Unit{}
        case Json.D5{}:
          Unit{}
        case Json.D6{}:
          Unit{}
        case Json.D7{}:
          Unit{}
        case Json.D8{}:
          Unit{}
        case Json.D9{}:
          Unit{}

def DigitList.digits_nonempty(n: Nat) -> DigitList.nonempty(Json.digits_lsb(n)):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      DigitList.inc_nonempty(Json.digits_lsb(p))

# Adding one carries through the least significant digits.
def Digits.value_inc(ds: +List<Json.Digit>) ->
  {Json.digits_value(Json.digits_inc(ds)) == Nat.add(Json.digits_value(ds), 1n) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, +t}:
      match d:
        case Json.D0{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 0n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 1n),
            NatAdd.add_assoc(Nat.mul(10n, Json.digits_value(t)), 0n, 1n))
        case Json.D1{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 1n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 2n),
            NatAdd.add_assoc(Nat.mul(10n, Json.digits_value(t)), 1n, 1n))
        case Json.D2{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 2n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 3n),
            NatAdd.add_assoc(Nat.mul(10n, Json.digits_value(t)), 2n, 1n))
        case Json.D3{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 3n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 4n),
            NatAdd.add_assoc(Nat.mul(10n, Json.digits_value(t)), 3n, 1n))
        case Json.D4{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 4n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 5n),
            NatAdd.add_assoc(Nat.mul(10n, Json.digits_value(t)), 4n, 1n))
        case Json.D5{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 5n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 6n),
            NatAdd.add_assoc(Nat.mul(10n, Json.digits_value(t)), 5n, 1n))
        case Json.D6{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 6n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 7n),
            NatAdd.add_assoc(Nat.mul(10n, Json.digits_value(t)), 6n, 1n))
        case Json.D7{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 7n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 8n),
            NatAdd.add_assoc(Nat.mul(10n, Json.digits_value(t)), 7n, 1n))
        case Json.D8{}:
          Equal.sym(Nat,
            Nat.add(Nat.add(Nat.mul(10n, Json.digits_value(t)), 8n), 1n),
            Nat.add(Nat.mul(10n, Json.digits_value(t)), 9n),
            NatAdd.add_assoc(Nat.mul(10n, Json.digits_value(t)), 8n, 1n))
        case Json.D9{}:
          +v : Nat = Json.digits_value(t)
          e0 = Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(10n, x), 0n),
                  Json.digits_value(Json.digits_inc(t)), Nat.add(v, 1n),
                  Digits.value_inc(t))
          e1 = NatAdd.add_zero(Nat.mul(10n, Nat.add(v, 1n)))
          e2 = NatMul.mul10_succ(v)
          e3 = Equal.sym(Nat,
                  Nat.add(Nat.add(Nat.mul(10n, v), 9n), 1n),
                  Nat.add(Nat.mul(10n, v), 10n),
                  NatAdd.add_assoc(Nat.mul(10n, v), 9n, 1n))
          Equal.trans(Nat,
            Nat.add(Nat.mul(10n, Json.digits_value(Json.digits_inc(t))), 0n),
            Nat.add(Nat.mul(10n, Nat.add(v, 1n)), 0n),
            Nat.add(Nat.add(Nat.mul(10n, v), 9n), 1n),
            e0,
            Equal.trans(Nat,
              Nat.add(Nat.mul(10n, Nat.add(v, 1n)), 0n),
              Nat.add(Nat.mul(10n, v), 10n),
              Nat.add(Nat.add(Nat.mul(10n, v), 9n), 1n),
              Equal.trans(Nat,
                Nat.add(Nat.mul(10n, Nat.add(v, 1n)), 0n),
                Nat.mul(10n, Nat.add(v, 1n)),
                Nat.add(Nat.mul(10n, v), 10n), e1, e2),
              e3))

def Digits.value_digits(n: Nat) -> {Json.digits_value(Json.digits_lsb(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      e1 = Digits.value_inc(Json.digits_lsb(p))
      e2 = Equal.cong(Nat, Nat, x => Nat.add(x, 1n),
             Json.digits_value(Json.digits_lsb(p)), p, Digits.value_digits(p))
      e3 = NatAdd.add_one(p)
      Equal.trans(Nat, Json.digits_value(Json.digits_lsb(1n+p)),
                  Nat.add(Json.digits_value(Json.digits_lsb(p)), 1n),
                  1n+p, e1,
                  Equal.trans(Nat,
                    Nat.add(Json.digits_value(Json.digits_lsb(p)), 1n),
                    Nat.add(p, 1n), 1n+p, e2, e3))

# Parsing the digits of one letter.
def LetterProof.digit_body(d: Json.Digit, +rest: String, +frames: +List<Json.Frame>,
    +cur: +List<Tree.Child>, +fb: +List<Feedback.Color>, +nums: +List<Nat>,
    +acc: +List<Json.Digit>) ->
  {Json.parse.go(Json.Digit.char(d) ++ rest, Json.MNatsBody{}, frames, cur, fb, nums, acc)
    == Json.parse.go(rest, Json.MNatsDigits{}, frames, cur, fb, nums, Con{d, acc})
   : Maybe<&1, Tree.Tree & String>}:
  match d:
    case Json.D0{}:
      {==}
    case Json.D1{}:
      {==}
    case Json.D2{}:
      {==}
    case Json.D3{}:
      {==}
    case Json.D4{}:
      {==}
    case Json.D5{}:
      {==}
    case Json.D6{}:
      {==}
    case Json.D7{}:
      {==}
    case Json.D8{}:
      {==}
    case Json.D9{}:
      {==}

def LetterProof.digit_more(d: Json.Digit, +rest: String, +frames: +List<Json.Frame>,
    +cur: +List<Tree.Child>, +fb: +List<Feedback.Color>, +nums: +List<Nat>,
    +acc: +List<Json.Digit>) ->
  {Json.parse.go(Json.Digit.char(d) ++ rest, Json.MNatsDigits{}, frames, cur, fb, nums, acc)
    == Json.parse.go(rest, Json.MNatsDigits{}, frames, cur, fb, nums, Con{d, acc})
   : Maybe<&1, Tree.Tree & String>}:
  match d:
    case Json.D0{}:
      {==}
    case Json.D1{}:
      {==}
    case Json.D2{}:
      {==}
    case Json.D3{}:
      {==}
    case Json.D4{}:
      {==}
    case Json.D5{}:
      {==}
    case Json.D6{}:
      {==}
    case Json.D7{}:
      {==}
    case Json.D8{}:
      {==}
    case Json.D9{}:
      {==}

# Reading a printed digit list from the digits state appends it, least
# significant first, to the accumulator.
def LetterProof.from_digits(+ds: +List<Json.Digit>, +rest: String, +frames: +List<Json.Frame>,
    +cur: +List<Tree.Child>, +fb: +List<Feedback.Color>, +nums: +List<Nat>,
    +acc: +List<Json.Digit>) ->
  {Json.parse.go(Json.digits_show(ds) ++ rest, Json.MNatsDigits{}, frames, cur, fb, nums, acc)
    == Json.parse.go(rest, Json.MNatsDigits{}, frames, cur, fb, nums,
                     List.append(&2, Json.Digit, ds, acc))
   : Maybe<&1, Tree.Tree & String>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      e1 = Equal.cong(String, Maybe<&1, Tree.Tree & String>,
             s => Json.parse.go(s, Json.MNatsDigits{}, frames, cur, fb, nums, acc),
             String.append(String.append(Json.digits_show(t), Json.Digit.char(d)), rest),
             String.append(Json.digits_show(t), String.append(Json.Digit.char(d), rest)),
             StringProof.append_assoc(Json.digits_show(t), Json.Digit.char(d), rest))
      e2 = LetterProof.from_digits(t, String.append(Json.Digit.char(d), rest),
             frames, cur, fb, nums, acc)
      e3 = LetterProof.digit_more(d, rest, frames, cur, fb, nums,
             List.append(&2, Json.Digit, t, acc))
      Equal.trans(Maybe<&1, Tree.Tree & String>,
        Json.parse.go(Json.digits_show(Con{d, t}) ++ rest, Json.MNatsDigits{}, frames, cur, fb, nums, acc),
        Json.parse.go(String.append(Json.digits_show(t), String.append(Json.Digit.char(d), rest)), Json.MNatsDigits{}, frames, cur, fb, nums, acc),
        Json.parse.go(rest, Json.MNatsDigits{}, frames, cur, fb, nums,
                      List.append(&2, Json.Digit, Con{d, t}, acc)),
        e1,
        Equal.trans(Maybe<&1, Tree.Tree & String>,
          Json.parse.go(String.append(Json.digits_show(t), String.append(Json.Digit.char(d), rest)), Json.MNatsDigits{}, frames, cur, fb, nums, acc),
          Json.parse.go(String.append(Json.Digit.char(d), rest), Json.MNatsDigits{}, frames, cur, fb, nums,
                        List.append(&2, Json.Digit, t, acc)),
          Json.parse.go(rest, Json.MNatsDigits{}, frames, cur, fb, nums,
                        List.append(&2, Json.Digit, Con{d, t}, acc)),
          e2, e3))

# Reading a printed digit list from the body of a guess array. The list is
# never empty, so the first digit moves the machine to the digits state.
def LetterProof.from_body(+ds: +List<Json.Digit>, ne: DigitList.nonempty(ds),
    +rest: String, +frames: +List<Json.Frame>, +cur: +List<Tree.Child>,
    +fb: +List<Feedback.Color>, +nums: +List<Nat>, +acc: +List<Json.Digit>) ->
  {Json.parse.go(Json.digits_show(ds) ++ rest, Json.MNatsBody{}, frames, cur, fb, nums, acc)
    == Json.parse.go(rest, Json.MNatsDigits{}, frames, cur, fb, nums,
                     List.append(&2, Json.Digit, ds, acc))
   : Maybe<&1, Tree.Tree & String>}:
  match ds:
    case Nil{}:
      match ne:
    case Con{+d, t}:
      match t:
        case Nil{}:
          LetterProof.digit_body(d, rest, frames, cur, fb, nums, acc)
        case Con{+h, +t2}:
          e1 = Equal.cong(String, Maybe<&1, Tree.Tree & String>,
                 s => Json.parse.go(s, Json.MNatsBody{}, frames, cur, fb, nums, acc),
                 String.append(String.append(Json.digits_show(Con{h, t2}), Json.Digit.char(d)), rest),
                 String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(d), rest)),
                 StringProof.append_assoc(Json.digits_show(Con{h, t2}), Json.Digit.char(d), rest))
          e2 = LetterProof.from_body(Con{h, t2}, Unit{},
                 String.append(Json.Digit.char(d), rest), frames, cur, fb, nums, acc)
          e3 = LetterProof.digit_more(d, rest, frames, cur, fb, nums,
                 List.append(&2, Json.Digit, Con{h, t2}, acc))
          Equal.trans(Maybe<&1, Tree.Tree & String>,
            Json.parse.go(Json.digits_show(Con{d, Con{h, t2}}) ++ rest, Json.MNatsBody{}, frames, cur, fb, nums, acc),
            Json.parse.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(d), rest)), Json.MNatsBody{}, frames, cur, fb, nums, acc),
            Json.parse.go(rest, Json.MNatsDigits{}, frames, cur, fb, nums,
                          List.append(&2, Json.Digit, Con{d, Con{h, t2}}, acc)),
            e1,
            Equal.trans(Maybe<&1, Tree.Tree & String>,
              Json.parse.go(String.append(Json.digits_show(Con{h, t2}), String.append(Json.Digit.char(d), rest)), Json.MNatsBody{}, frames, cur, fb, nums, acc),
              Json.parse.go(String.append(Json.Digit.char(d), rest), Json.MNatsDigits{}, frames, cur, fb, nums,
                            List.append(&2, Json.Digit, Con{h, t2}, acc)),
              Json.parse.go(rest, Json.MNatsDigits{}, frames, cur, fb, nums,
                            List.append(&2, Json.Digit, Con{d, Con{h, t2}}, acc)),
              e2, e3))

# Parsing one letter from the body of a guess array. It leaves the digits of
# the letter in the accumulator; the separator that follows turns them into a
# Nat and appends it to the guess.
def LetterProof.body(+n: Nat, +rest: String, +frames: +List<Json.Frame>,
    +cur: +List<Tree.Child>, +fb: +List<Feedback.Color>, +nums: +List<Nat>) ->
  {Json.parse.go(Json.show_letter(n) ++ rest, Json.MNatsBody{}, frames, cur, fb, nums, Nil{})
    == Json.parse.go(rest, Json.MNatsDigits{}, frames, cur, fb, nums, Json.digits_lsb(n))
   : Maybe<&1, Tree.Tree & String>}:
  e1 = LetterProof.from_body(Json.digits_lsb(n), DigitList.digits_nonempty(n),
         rest, frames, cur, fb, nums, Nil{})
  e2 = Equal.cong(+List<Json.Digit>, Maybe<&1, Tree.Tree & String>,
         l => Json.parse.go(rest, Json.MNatsDigits{}, frames, cur, fb, nums, l),
         List.append(&2, Json.Digit, Json.digits_lsb(n), Nil{}), Json.digits_lsb(n),
         ListProof.append_nil(&2, Json.Digit, Json.digits_lsb(n)))
  Equal.trans(Maybe<&1, Tree.Tree & String>,
    Json.parse.go(Json.show_letter(n) ++ rest, Json.MNatsBody{}, frames, cur, fb, nums, Nil{}),
    Json.parse.go(rest, Json.MNatsDigits{}, frames, cur, fb, nums,
                  List.append(&2, Json.Digit, Json.digits_lsb(n), Nil{})),
    Json.parse.go(rest, Json.MNatsDigits{}, frames, cur, fb, nums, Json.digits_lsb(n)),
    e1, e2)

# The separators that end a numeral turn the accumulated digits into a Nat.
def LetterProof.close_comma(+ds: +List<Json.Digit>, +rest: String,
    +frames: +List<Json.Frame>, +cur: +List<Tree.Child>, +fb: +List<Feedback.Color>,
    +nums: +List<Nat>) ->
  {Json.parse.go("," ++ rest, Json.MNatsDigits{}, frames, cur, fb, nums, ds)
    == Json.parse.go(rest, Json.MNatsBody{}, frames, cur, fb,
                     List.append(&2, Nat, nums, Json.one_nat(Json.digits_value(ds))), Nil{})
   : Maybe<&1, Tree.Tree & String>}:
  {==}

def LetterProof.close_bracket(+ds: +List<Json.Digit>, +rest: String,
    +frames: +List<Json.Frame>, +cur: +List<Tree.Child>, +fb: +List<Feedback.Color>,
    +nums: +List<Nat>) ->
  {Json.parse.go("]" ++ rest, Json.MNatsDigits{}, frames, cur, fb, nums, ds)
    == Json.parse.go(rest, Json.MNatsDone{}, frames, cur, fb,
                     List.append(&2, Nat, nums, Json.one_nat(Json.digits_value(ds))), Nil{})
   : Maybe<&1, Tree.Tree & String>}:
  {==}

def NatsProof.body(+xs: +List<Nat>, +rest: String, +frames: +List<Json.Frame>,
    +cur: +List<Tree.Child>, +fb: +List<Feedback.Color>, +nums: +List<Nat>) ->
  {Json.parse.go(Json.show_nats.body(xs) ++ ("]" ++ rest), Json.MNatsBody{}, frames, cur, fb, nums, Nil{})
    == Json.parse.go(rest, Json.MNatsDone{}, frames, cur, fb,
                     List.append(&2, Nat, nums, xs), Nil{})
   : Maybe<&1, Tree.Tree & String>}:
  match xs:
    case Nil{}:
      Equal.cong(+List<Nat>, Maybe<&1, Tree.Tree & String>,
                 l => Json.parse.go(rest, Json.MNatsDone{}, frames, cur, fb, l, Nil{}),
                 nums, List.append(&2, Nat, nums, Nil{}),
                 Equal.sym(+List<Nat>, List.append(&2, Nat, nums, Nil{}), nums,
                           ListProof.append_nil(&2, Nat, nums)))
    case Con{h, t}:
      match t:
        case Nil{}:
          e1 = StringProof.append_assoc(Json.show_letter(h), Json.show_nats.more(Nil{}), "]" ++ rest)
          e2 = LetterProof.body(h, Json.show_nats.more(Nil{}) ++ ("]" ++ rest),
                                frames, cur, fb, nums)
          e3 = LetterProof.close_bracket(Json.digits_lsb(h), rest, frames, cur, fb, nums)
          e4 = Equal.cong(Nat, Maybe<&1, Tree.Tree & String>,
                 m => Json.parse.go(rest, Json.MNatsDone{}, frames, cur, fb,
                                    List.append(&2, Nat, nums, Json.one_nat(m)), Nil{}),
                 Json.digits_value(Json.digits_lsb(h)), h, Digits.value_digits(h))
          e12 = Equal.cong(String, Maybe<&1, Tree.Tree & String>,
                    s => Json.parse.go(s, Json.MNatsBody{}, frames, cur, fb, nums, Nil{}),
                    String.append(String.append(Json.show_letter(h), Json.show_nats.more(Nil{})), "]" ++ rest),
                    String.append(Json.show_letter(h), String.append(Json.show_nats.more(Nil{}), "]" ++ rest)),
                    e1)
          Equal.trans(Maybe<&1, Tree.Tree & String>,
            Json.parse.go(String.append(String.append(Json.show_letter(h), Json.show_nats.more(Nil{})), "]" ++ rest), Json.MNatsBody{}, frames, cur, fb, nums, Nil{}),
            Json.parse.go(String.append(Json.show_letter(h), String.append(Json.show_nats.more(Nil{}), "]" ++ rest)), Json.MNatsBody{}, frames, cur, fb, nums, Nil{}),
            Json.parse.go(rest, Json.MNatsDone{}, frames, cur, fb, List.append(&2, Nat, nums, h <> Nil{}), Nil{}),
            e12,
            Equal.trans(Maybe<&1, Tree.Tree & String>,
              Json.parse.go(String.append(Json.show_letter(h), String.append(Json.show_nats.more(Nil{}), "]" ++ rest)), Json.MNatsBody{}, frames, cur, fb, nums, Nil{}),
              Json.parse.go(String.append(Json.show_nats.more(Nil{}), "]" ++ rest), Json.MNatsDigits{}, frames, cur, fb, nums, Json.digits_lsb(h)),
              Json.parse.go(rest, Json.MNatsDone{}, frames, cur, fb, List.append(&2, Nat, nums, h <> Nil{}), Nil{}),
              e2,
              Equal.trans(Maybe<&1, Tree.Tree & String>,
                Json.parse.go(String.append(Json.show_nats.more(Nil{}), "]" ++ rest), Json.MNatsDigits{}, frames, cur, fb, nums, Json.digits_lsb(h)),
                Json.parse.go(rest, Json.MNatsDone{}, frames, cur, fb,
                              List.append(&2, Nat, nums, Json.one_nat(Json.digits_value(Json.digits_lsb(h)))), Nil{}),
                Json.parse.go(rest, Json.MNatsDone{}, frames, cur, fb, List.append(&2, Nat, nums, h <> Nil{}), Nil{}),
                e3, e4)))
        case Con{h2, t2}:
          e1 = StringProof.append_assoc(Json.show_letter(h), Json.show_nats.more(h2 <> t2), "]" ++ rest)
          e2 = LetterProof.body(h, Json.show_nats.more(h2 <> t2) ++ ("]" ++ rest),
                                frames, cur, fb, nums)
          e3 = Equal.cong(String, Maybe<&1, Tree.Tree & String>,
                 s => Json.parse.go(s, Json.MNatsDigits{}, frames, cur, fb, nums, Json.digits_lsb(h)),
                 String.append(String.append(",", Json.show_nats.body(h2 <> t2)), "]" ++ rest),
                 String.append(",", String.append(Json.show_nats.body(h2 <> t2), "]" ++ rest)),
                 StringProof.append_assoc(",", Json.show_nats.body(h2 <> t2), "]" ++ rest))
          e4 = LetterProof.close_comma(Json.digits_lsb(h),
                 String.append(Json.show_nats.body(h2 <> t2), "]" ++ rest),
                 frames, cur, fb, nums)
          e5 = Equal.cong(Nat, Maybe<&1, Tree.Tree & String>,
                 m => Json.parse.go(String.append(Json.show_nats.body(h2 <> t2), "]" ++ rest), Json.MNatsBody{}, frames, cur, fb,
                                    List.append(&2, Nat, nums, Json.one_nat(m)), Nil{}),
                 Json.digits_value(Json.digits_lsb(h)), h, Digits.value_digits(h))
          e6 = NatsProof.body(h2 <> t2, rest, frames, cur, fb,
                              List.append(&2, Nat, nums, Json.one_nat(h)))
          e7 = Equal.cong(+List<Nat>, Maybe<&1, Tree.Tree & String>,
                 l => Json.parse.go(rest, Json.MNatsDone{}, frames, cur, fb, l, Nil{}),
                 List.append(&2, Nat, List.append(&2, Nat, nums, Json.one_nat(h)), h2 <> t2),
                 List.append(&2, Nat, nums, h <> (h2 <> t2)),
                 ListProof.append_assoc(&2, Nat, nums, Json.one_nat(h), h2 <> t2))
          e12 = Equal.cong(String, Maybe<&1, Tree.Tree & String>,
                    s => Json.parse.go(s, Json.MNatsBody{}, frames, cur, fb, nums, Nil{}),
                    String.append(String.append(Json.show_letter(h), Json.show_nats.more(h2 <> t2)), "]" ++ rest),
                    String.append(Json.show_letter(h), String.append(Json.show_nats.more(h2 <> t2), "]" ++ rest)),
                    e1)
          e1234 = Equal.trans(Maybe<&1, Tree.Tree & String>,
            Json.parse.go(String.append(String.append(Json.show_letter(h), Json.show_nats.more(h2 <> t2)), "]" ++ rest), Json.MNatsBody{}, frames, cur, fb, nums, Nil{}),
            Json.parse.go(String.append(Json.show_letter(h), String.append(Json.show_nats.more(h2 <> t2), "]" ++ rest)), Json.MNatsBody{}, frames, cur, fb, nums, Nil{}),
            Json.parse.go(String.append(",", String.append(Json.show_nats.body(h2 <> t2), "]" ++ rest)), Json.MNatsDigits{}, frames, cur, fb, nums, Json.digits_lsb(h)),
            e12,
            Equal.trans(Maybe<&1, Tree.Tree & String>,
              Json.parse.go(String.append(Json.show_letter(h), String.append(Json.show_nats.more(h2 <> t2), "]" ++ rest)), Json.MNatsBody{}, frames, cur, fb, nums, Nil{}),
              Json.parse.go(String.append(Json.show_nats.more(h2 <> t2), "]" ++ rest), Json.MNatsDigits{}, frames, cur, fb, nums, Json.digits_lsb(h)),
              Json.parse.go(String.append(",", String.append(Json.show_nats.body(h2 <> t2), "]" ++ rest)), Json.MNatsDigits{}, frames, cur, fb, nums, Json.digits_lsb(h)),
              e2, e3))
          e12345 = Equal.trans(Maybe<&1, Tree.Tree & String>,
            Json.parse.go(String.append(String.append(Json.show_letter(h), Json.show_nats.more(h2 <> t2)), "]" ++ rest), Json.MNatsBody{}, frames, cur, fb, nums, Nil{}),
            Json.parse.go(String.append(",", String.append(Json.show_nats.body(h2 <> t2), "]" ++ rest)), Json.MNatsDigits{}, frames, cur, fb, nums, Json.digits_lsb(h)),
            Json.parse.go(String.append(Json.show_nats.body(h2 <> t2), "]" ++ rest), Json.MNatsBody{}, frames, cur, fb,
                          List.append(&2, Nat, nums, Json.one_nat(Json.digits_value(Json.digits_lsb(h)))), Nil{}),
            e1234, e4)
          e123456 = Equal.trans(Maybe<&1, Tree.Tree & String>,
            Json.parse.go(String.append(String.append(Json.show_letter(h), Json.show_nats.more(h2 <> t2)), "]" ++ rest), Json.MNatsBody{}, frames, cur, fb, nums, Nil{}),
            Json.parse.go(String.append(Json.show_nats.body(h2 <> t2), "]" ++ rest), Json.MNatsBody{}, frames, cur, fb,
                          List.append(&2, Nat, nums, Json.one_nat(Json.digits_value(Json.digits_lsb(h)))), Nil{}),
            Json.parse.go(String.append(Json.show_nats.body(h2 <> t2), "]" ++ rest), Json.MNatsBody{}, frames, cur, fb,
                          List.append(&2, Nat, nums, Json.one_nat(h)), Nil{}),
            e12345, e5)
          e1234567 = Equal.trans(Maybe<&1, Tree.Tree & String>,
            Json.parse.go(String.append(String.append(Json.show_letter(h), Json.show_nats.more(h2 <> t2)), "]" ++ rest), Json.MNatsBody{}, frames, cur, fb, nums, Nil{}),
            Json.parse.go(String.append(Json.show_nats.body(h2 <> t2), "]" ++ rest), Json.MNatsBody{}, frames, cur, fb,
                          List.append(&2, Nat, nums, Json.one_nat(h)), Nil{}),
            Json.parse.go(rest, Json.MNatsDone{}, frames, cur, fb,
                          List.append(&2, Nat, List.append(&2, Nat, nums, Json.one_nat(h)), h2 <> t2), Nil{}),
            e123456, e6)
          Equal.trans(Maybe<&1, Tree.Tree & String>,
            Json.parse.go(String.append(String.append(Json.show_letter(h), Json.show_nats.more(h2 <> t2)), "]" ++ rest), Json.MNatsBody{}, frames, cur, fb, nums, Nil{}),
            Json.parse.go(rest, Json.MNatsDone{}, frames, cur, fb,
                          List.append(&2, Nat, List.append(&2, Nat, nums, Json.one_nat(h)), h2 <> t2), Nil{}),
            Json.parse.go(rest, Json.MNatsDone{}, frames, cur, fb,
                          List.append(&2, Nat, nums, h <> (h2 <> t2)), Nil{}),
            e1234567, e7)


def NatsProof.array(+xs: +List<Nat>, +rest: String, +frames: +List<Json.Frame>,
    +cur: +List<Tree.Child>, +fb: +List<Feedback.Color>, +nums: +List<Nat>) ->
  {Json.parse.go(Json.show_nats(xs) ++ rest, Json.MNatsOpen{}, frames, cur, fb, nums, Nil{})
    == Json.parse.go(rest, Json.MNatsDone{}, frames, cur, fb,
                     List.append(&2, Nat, nums, xs), Nil{})
   : Maybe<&1, Tree.Tree & String>}:
  e1 = StringProof.append_assoc("[", String.append(Json.show_nats.body(xs), "]"), rest)
  e2 = StringProof.append_assoc(Json.show_nats.body(xs), "]", rest)
  e2lift = Equal.cong(String, String, s => String.append("[", s),
            String.append(String.append(Json.show_nats.body(xs), "]"), rest),
            String.append(Json.show_nats.body(xs), String.append("]", rest)),
            e2)
  Equal.trans(Maybe<&1, Tree.Tree & String>,
    Json.parse.go(Json.show_nats(xs) ++ rest, Json.MNatsOpen{}, frames, cur, fb, nums, Nil{}),
    Json.parse.go(String.append("[", String.append(String.append(Json.show_nats.body(xs), "]"), rest)), Json.MNatsOpen{}, frames, cur, fb, nums, Nil{}),
    Json.parse.go(rest, Json.MNatsDone{}, frames, cur, fb, List.append(&2, Nat, nums, xs), Nil{}),
    Equal.cong(String, Maybe<&1, Tree.Tree & String>,
      s => Json.parse.go(s, Json.MNatsOpen{}, frames, cur, fb, nums, Nil{}),
      Json.show_nats(xs) ++ rest,
      String.append("[", String.append(String.append(Json.show_nats.body(xs), "]"), rest)),
      e1),
    Equal.trans(Maybe<&1, Tree.Tree & String>,
      Json.parse.go(String.append("[", String.append(String.append(Json.show_nats.body(xs), "]"), rest)), Json.MNatsOpen{}, frames, cur, fb, nums, Nil{}),
      Json.parse.go(String.append("[", String.append(Json.show_nats.body(xs), String.append("]", rest))), Json.MNatsOpen{}, frames, cur, fb, nums, Nil{}),
      Json.parse.go(rest, Json.MNatsDone{}, frames, cur, fb, List.append(&2, Nat, nums, xs), Nil{}),
      Equal.cong(String, Maybe<&1, Tree.Tree & String>,
        s => Json.parse.go(s, Json.MNatsOpen{}, frames, cur, fb, nums, Nil{}),
        String.append("[", String.append(String.append(Json.show_nats.body(xs), "]"), rest)),
        String.append("[", String.append(Json.show_nats.body(xs), String.append("]", rest))),
        e2lift),
      NatsProof.body(xs, rest, frames, cur, fb, nums)))

def FeedbackProof.code(+c: Feedback.Color, +rest: String, +frames: +List<Json.Frame>,
    +cur: +List<Tree.Child>, +fb: +List<Feedback.Color>, +nums: +List<Nat>) ->
  {Json.parse.go(Json.Color.code(c) ++ rest, Json.MFbBody{}, frames, cur, fb, nums, Nil{})
    == Json.parse.go(rest, Json.MFbNext{}, frames, cur,
                     List.append(&2, Feedback.Color, fb, Json.one_color(c)), nums, Nil{})
   : Maybe<&1, Tree.Tree & String>}:
  match c:
    case Feedback.Gray{}:
      {==}
    case Feedback.Yellow{}:
      {==}
    case Feedback.Green{}:
      {==}

def FeedbackProof.body(+xs: +List<Feedback.Color>, +rest: String, +frames: +List<Json.Frame>,
    +cur: +List<Tree.Child>, +fb: +List<Feedback.Color>, +nums: +List<Nat>) ->
  {Json.parse.go(Json.show_feedback.body(xs) ++ ("]" ++ rest), Json.MFbBody{}, frames, cur, fb, nums, Nil{})
    == Json.parse.go(rest, Json.MFbDone{}, frames, cur,
                     List.append(&2, Feedback.Color, fb, xs), nums, Nil{})
   : Maybe<&1, Tree.Tree & String>}:
  match xs:
    case Nil{}:
      Equal.cong(+List<Feedback.Color>, Maybe<&1, Tree.Tree & String>,
                 l => Json.parse.go(rest, Json.MFbDone{}, frames, cur, l, nums, Nil{}),
                 fb, List.append(&2, Feedback.Color, fb, Nil{}),
                 Equal.sym(+List<Feedback.Color>, List.append(&2, Feedback.Color, fb, Nil{}), fb,
                           ListProof.append_nil(&2, Feedback.Color, fb)))
    case Con{h, t}:
      match t:
        case Nil{}:
          e1 = StringProof.append_assoc(Json.Color.code(h), Json.show_feedback.more(Nil{}), "]" ++ rest)
          e2 = FeedbackProof.code(h, Json.show_feedback.more(Nil{}) ++ ("]" ++ rest), frames, cur, fb, nums)
          e12 = Equal.cong(String, Maybe<&1, Tree.Tree & String>,
                    s => Json.parse.go(s, Json.MFbBody{}, frames, cur, fb, nums, Nil{}),
                    String.append(String.append(Json.Color.code(h), Json.show_feedback.more(Nil{})), "]" ++ rest),
                    String.append(Json.Color.code(h), String.append(Json.show_feedback.more(Nil{}), "]" ++ rest)),
                    e1)
          Equal.trans(Maybe<&1, Tree.Tree & String>,
            Json.parse.go(String.append(String.append(Json.Color.code(h), Json.show_feedback.more(Nil{})), "]" ++ rest), Json.MFbBody{}, frames, cur, fb, nums, Nil{}),
            Json.parse.go(String.append(Json.Color.code(h), String.append(Json.show_feedback.more(Nil{}), "]" ++ rest)), Json.MFbBody{}, frames, cur, fb, nums, Nil{}),
            Json.parse.go(rest, Json.MFbDone{}, frames, cur, List.append(&2, Feedback.Color, fb, h <> Nil{}), nums, Nil{}),
            e12, e2)
        case Con{h2, t2}:
          e1 = StringProof.append_assoc(Json.Color.code(h), Json.show_feedback.more(h2 <> t2), "]" ++ rest)
          e2 = FeedbackProof.code(h, Json.show_feedback.more(h2 <> t2) ++ ("]" ++ rest), frames, cur, fb, nums)
          e3 = FeedbackProof.body(h2 <> t2, rest, frames, cur,
                                  List.append(&2, Feedback.Color, fb, Json.one_color(h)), nums)
          e12 = Equal.cong(String, Maybe<&1, Tree.Tree & String>,
                    s => Json.parse.go(s, Json.MFbBody{}, frames, cur, fb, nums, Nil{}),
                    String.append(String.append(Json.Color.code(h), Json.show_feedback.more(h2 <> t2)), "]" ++ rest),
                    String.append(Json.Color.code(h), String.append(Json.show_feedback.more(h2 <> t2), "]" ++ rest)),
                    e1)
          e123 = Equal.trans(Maybe<&1, Tree.Tree & String>,
            Json.parse.go(String.append(String.append(Json.Color.code(h), Json.show_feedback.more(h2 <> t2)), "]" ++ rest), Json.MFbBody{}, frames, cur, fb, nums, Nil{}),
            Json.parse.go(String.append(Json.Color.code(h), String.append(Json.show_feedback.more(h2 <> t2), "]" ++ rest)), Json.MFbBody{}, frames, cur, fb, nums, Nil{}),
            Json.parse.go(rest, Json.MFbDone{}, frames, cur,
                          List.append(&2, Feedback.Color, List.append(&2, Feedback.Color, fb, Json.one_color(h)), h2 <> t2), nums, Nil{}),
            e12,
            Equal.trans(Maybe<&1, Tree.Tree & String>,
              Json.parse.go(String.append(Json.Color.code(h), String.append(Json.show_feedback.more(h2 <> t2), "]" ++ rest)), Json.MFbBody{}, frames, cur, fb, nums, Nil{}),
              Json.parse.go(String.append(Json.show_feedback.more(h2 <> t2), "]" ++ rest), Json.MFbNext{}, frames, cur, List.append(&2, Feedback.Color, fb, Json.one_color(h)), nums, Nil{}),
              Json.parse.go(rest, Json.MFbDone{}, frames, cur,
                            List.append(&2, Feedback.Color, List.append(&2, Feedback.Color, fb, Json.one_color(h)), h2 <> t2), nums, Nil{}),
              e2, e3))
          Equal.trans(Maybe<&1, Tree.Tree & String>,
            Json.parse.go(String.append(String.append(Json.Color.code(h), Json.show_feedback.more(h2 <> t2)), "]" ++ rest), Json.MFbBody{}, frames, cur, fb, nums, Nil{}),
            Json.parse.go(rest, Json.MFbDone{}, frames, cur,
                          List.append(&2, Feedback.Color, List.append(&2, Feedback.Color, fb, Json.one_color(h)), h2 <> t2), nums, Nil{}),
            Json.parse.go(rest, Json.MFbDone{}, frames, cur,
                          List.append(&2, Feedback.Color, fb, h <> (h2 <> t2)), nums, Nil{}),
            e123,
            Equal.cong(+List<Feedback.Color>, Maybe<&1, Tree.Tree & String>,
              l => Json.parse.go(rest, Json.MFbDone{}, frames, cur, l, nums, Nil{}),
              List.append(&2, Feedback.Color, List.append(&2, Feedback.Color, fb, Json.one_color(h)), h2 <> t2),
              List.append(&2, Feedback.Color, fb, h <> (h2 <> t2)),
              ListProof.append_assoc(&2, Feedback.Color, fb, Json.one_color(h), h2 <> t2)))

def FeedbackProof.array(+xs: +List<Feedback.Color>, +rest: String, +frames: +List<Json.Frame>,
    +cur: +List<Tree.Child>, +fb: +List<Feedback.Color>, +nums: +List<Nat>) ->
  {Json.parse.go(Json.show_feedback(xs) ++ rest, Json.MChildOpen{}, frames, cur, fb, nums, Nil{})
    == Json.parse.go(rest, Json.MFbDone{}, frames, cur,
                     List.append(&2, Feedback.Color, fb, xs), nums, Nil{})
   : Maybe<&1, Tree.Tree & String>}:
  e1 = StringProof.append_assoc("[", String.append(Json.show_feedback.body(xs), "]"), rest)
  e2 = StringProof.append_assoc(Json.show_feedback.body(xs), "]", rest)
  e2lift = Equal.cong(String, String, s => String.append("[", s),
            String.append(String.append(Json.show_feedback.body(xs), "]"), rest),
            String.append(Json.show_feedback.body(xs), String.append("]", rest)),
            e2)
  Equal.trans(Maybe<&1, Tree.Tree & String>,
    Json.parse.go(Json.show_feedback(xs) ++ rest, Json.MChildOpen{}, frames, cur, fb, nums, Nil{}),
    Json.parse.go(String.append("[", String.append(String.append(Json.show_feedback.body(xs), "]"), rest)), Json.MChildOpen{}, frames, cur, fb, nums, Nil{}),
    Json.parse.go(rest, Json.MFbDone{}, frames, cur, List.append(&2, Feedback.Color, fb, xs), nums, Nil{}),
    Equal.cong(String, Maybe<&1, Tree.Tree & String>,
      s => Json.parse.go(s, Json.MChildOpen{}, frames, cur, fb, nums, Nil{}),
      Json.show_feedback(xs) ++ rest,
      String.append("[", String.append(String.append(Json.show_feedback.body(xs), "]"), rest)),
      e1),
    Equal.trans(Maybe<&1, Tree.Tree & String>,
      Json.parse.go(String.append("[", String.append(String.append(Json.show_feedback.body(xs), "]"), rest)), Json.MChildOpen{}, frames, cur, fb, nums, Nil{}),
      Json.parse.go(String.append("[", String.append(Json.show_feedback.body(xs), String.append("]", rest))), Json.MChildOpen{}, frames, cur, fb, nums, Nil{}),
      Json.parse.go(rest, Json.MFbDone{}, frames, cur, List.append(&2, Feedback.Color, fb, xs), nums, Nil{}),
      Equal.cong(String, Maybe<&1, Tree.Tree & String>,
        s => Json.parse.go(s, Json.MChildOpen{}, frames, cur, fb, nums, Nil{}),
        String.append("[", String.append(String.append(Json.show_feedback.body(xs), "]"), rest)),
        String.append("[", String.append(Json.show_feedback.body(xs), String.append("]", rest))),
        e2lift),
      FeedbackProof.body(xs, rest, frames, cur, fb, nums)))


def StringProof.append_assoc_rev(a: String, b: String, c: String) ->
  {String.append(a, String.append(b, c)) == String.append(String.append(a, b), c) : String}:
  Equal.sym(String, String.append(String.append(a, b), c), String.append(a, String.append(b, c)),
            StringProof.append_assoc(a, b, c))

def ListProof.append_assoc_rev(a, -A: Kind(a), xs: List<a, A>, ys: List<a, A>, zs: List<a, A>) ->
  {List.append(a, A, xs, List.append(a, A, ys, zs))
    == List.append(a, A, List.append(a, A, xs, ys), zs) : List<a, A>}:
  Equal.sym(List<a, A>, List.append(a, A, List.append(a, A, xs, ys), zs),
            List.append(a, A, xs, List.append(a, A, ys, zs)),
            ListProof.append_assoc(a, A, xs, ys, zs))


def KidsProof.prefix_eq(+h: Tree.Child, +t: +List<Tree.Child>, +prefix: String) ->
  {Json.show_kids.body(h <> t, prefix) == String.append(prefix, Json.show_kids.body(h <> t, "")) : String}:
  match h:
    case Tree.Child{f, child}:
      match child:
        case Tree.Node{g, ckids}:
          {==}

def KidsProof.comma(+h: Tree.Child, +t: +List<Tree.Child>, +rest0: String,
    +frames: +List<Json.Frame>, +cur: +List<Tree.Child>,
    +fb: +List<Feedback.Color>, +nums: +List<Nat>) ->
  {Json.parse.go(Json.show_kids.body(h <> t, "") ++ ("]" ++ rest0), Json.MKidsBody{}, frames, cur, fb, nums, Nil{})
    == Json.parse.go(Json.show_kids.body(h <> t, ",") ++ ("]" ++ rest0), Json.MKidsNext{}, frames, cur, fb, nums, Nil{})
   : Maybe<&1, Tree.Tree & String>}:
  Equal.cong(String, Maybe<&1, Tree.Tree & String>,
    s => Json.parse.go(String.append(s, "]" ++ rest0), Json.MKidsNext{}, frames, cur, fb, nums, Nil{}),
    String.append(",", Json.show_kids.body(h <> t, "")),
    Json.show_kids.body(h <> t, ","),
    Equal.sym(String, Json.show_kids.body(h <> t, ","),
              String.append(",", Json.show_kids.body(h <> t, "")),
              KidsProof.prefix_eq(h, t, ",")))

def KidsProof.body(+kids: +List<Tree.Child>, +rest0: String, +frames: +List<Json.Frame>,
    +cur: +List<Tree.Child>, +fb: +List<Feedback.Color>, +nums: +List<Nat>) ->
  {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                 List.append(&2, Tree.Child, cur, kids), fb, nums, Nil{})
    == Json.parse.go(Json.show_kids.body(kids, "") ++ ("]" ++ rest0), Json.MKidsBody{}, frames, cur, fb, nums, Nil{})
   : Maybe<&1, Tree.Tree & String>}:
  match kids:
    case Nil{}:
      Equal.cong(+List<Tree.Child>, Maybe<&1, Tree.Tree & String>,
                 l => Json.parse.go(rest0, Json.MKidsClosed{}, frames, l, fb, nums, Nil{}),
                 List.append(&2, Tree.Child, cur, Nil{}), cur,
                 ListProof.append_nil(&2, Tree.Child, cur))
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          match child:
            case Tree.Node{g, ckids}:
              match rest:
                case Nil{}:
                  +Br : String = ""
                  +X : String = "]" ++ rest0
                  +Bd : String = Json.show_kids.body(ckids, "")
                  +S : String = String.append("]]]", Br)
                  +Z2 : String = String.append(",[", String.append(Bd, S))
                  +BodyG : String = Json.show_nats.body(g)
                  +Z : String = String.append(",[", String.append(Json.show_nats(g), Z2))
                  +BodyF : String = Json.show_feedback.body(f)
                  +W : String = String.append(Br, X)
                  +R : String = String.append("]]", W)
                  +FramePushed : +List<Json.Frame> = Json.Frame{cur, fb, nums} <> frames
                  +Child : Tree.Child = Tree.Child{f, Tree.Node{g, ckids}}
                  +Cur1 : +List<Tree.Child> = List.append(&2, Tree.Child, cur, Child <> Nil{})
                  %StringProof.append_assoc_rev(String.append(BodyF, "]"), Z, X) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == Json.parse.go(_, Json.MFbBody{}, FramePushed, Nil{}, Nil{}, Nil{}, Nil{}) : Maybe<&1, Tree.Tree & String>}
                  %StringProof.append_assoc_rev(BodyF, "]", String.append(Z, X)) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == Json.parse.go(_, Json.MFbBody{}, FramePushed, Nil{}, Nil{}, Nil{}, Nil{}) : Maybe<&1, Tree.Tree & String>}
                  %Equal.sym(Maybe<&1, Tree.Tree & String>,
                     Json.parse.go(String.append(BodyF, String.append("]", String.append(Z, X))), Json.MFbBody{}, FramePushed, Nil{}, Nil{}, Nil{}, Nil{}),
                     Json.parse.go(String.append(Z, X), Json.MFbDone{}, FramePushed, Nil{},
                                   List.append(&2, Feedback.Color, Nil{}, f), Nil{}, Nil{}),
                     FeedbackProof.body(f, String.append(Z, X), FramePushed, Nil{}, Nil{}, Nil{})) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == _ : Maybe<&1, Tree.Tree & String>}
                  %StringProof.append_assoc_rev(String.append(BodyG, "]"), Z2, X) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == Json.parse.go(_, Json.MNatsBody{}, FramePushed, Nil{}, List.append(&2, Feedback.Color, Nil{}, f), Nil{}, Nil{}) : Maybe<&1, Tree.Tree & String>}
                  %StringProof.append_assoc_rev(BodyG, "]", String.append(Z2, X)) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == Json.parse.go(_, Json.MNatsBody{}, FramePushed, Nil{}, List.append(&2, Feedback.Color, Nil{}, f), Nil{}, Nil{}) : Maybe<&1, Tree.Tree & String>}
                  %Equal.sym(Maybe<&1, Tree.Tree & String>,
                     Json.parse.go(String.append(BodyG, String.append("]", String.append(Z2, X))), Json.MNatsBody{}, FramePushed, Nil{},
                                   List.append(&2, Feedback.Color, Nil{}, f), Nil{}, Nil{}),
                     Json.parse.go(String.append(Z2, X), Json.MNatsDone{}, FramePushed, Nil{},
                                   List.append(&2, Feedback.Color, Nil{}, f),
                                   List.append(&2, Nat, Nil{}, g), Nil{}),
                     NatsProof.body(g, String.append(Z2, X), FramePushed, Nil{},
                                    List.append(&2, Feedback.Color, Nil{}, f), Nil{})) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == _ : Maybe<&1, Tree.Tree & String>}
                  %StringProof.append_assoc_rev(Bd, S, X) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == Json.parse.go(_, Json.MKidsBody{}, FramePushed, Nil{}, List.append(&2, Feedback.Color, Nil{}, f), List.append(&2, Nat, Nil{}, g), Nil{}) : Maybe<&1, Tree.Tree & String>}
                  %StringProof.append_assoc_rev("]]]", Br, X) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == Json.parse.go(String.append(Bd, _), Json.MKidsBody{}, FramePushed, Nil{}, List.append(&2, Feedback.Color, Nil{}, f), List.append(&2, Nat, Nil{}, g), Nil{}) : Maybe<&1, Tree.Tree & String>}
                  %KidsProof.body(ckids, R, FramePushed, Nil{},
                                  List.append(&2, Feedback.Color, Nil{}, f),
                                  List.append(&2, Nat, Nil{}, g)) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == _ : Maybe<&1, Tree.Tree & String>}
                  {==}
                case Con{r1, r2}:
                  +Br : String = Json.show_kids.body(rest, ",")
                  +X : String = "]" ++ rest0
                  +Bd : String = Json.show_kids.body(ckids, "")
                  +S : String = String.append("]]]", Br)
                  +Z2 : String = String.append(",[", String.append(Bd, S))
                  +BodyG : String = Json.show_nats.body(g)
                  +Z : String = String.append(",[", String.append(Json.show_nats(g), Z2))
                  +BodyF : String = Json.show_feedback.body(f)
                  +W : String = String.append(Br, X)
                  +R : String = String.append("]]", W)
                  +FramePushed : +List<Json.Frame> = Json.Frame{cur, fb, nums} <> frames
                  +Child : Tree.Child = Tree.Child{f, Tree.Node{g, ckids}}
                  +Cur1 : +List<Tree.Child> = List.append(&2, Tree.Child, cur, Child <> Nil{})
                  %StringProof.append_assoc_rev(String.append(BodyF, "]"), Z, X) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == Json.parse.go(_, Json.MFbBody{}, FramePushed, Nil{}, Nil{}, Nil{}, Nil{}) : Maybe<&1, Tree.Tree & String>}
                  %StringProof.append_assoc_rev(BodyF, "]", String.append(Z, X)) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == Json.parse.go(_, Json.MFbBody{}, FramePushed, Nil{}, Nil{}, Nil{}, Nil{}) : Maybe<&1, Tree.Tree & String>}
                  %Equal.sym(Maybe<&1, Tree.Tree & String>,
                     Json.parse.go(String.append(BodyF, String.append("]", String.append(Z, X))), Json.MFbBody{}, FramePushed, Nil{}, Nil{}, Nil{}, Nil{}),
                     Json.parse.go(String.append(Z, X), Json.MFbDone{}, FramePushed, Nil{},
                                   List.append(&2, Feedback.Color, Nil{}, f), Nil{}, Nil{}),
                     FeedbackProof.body(f, String.append(Z, X), FramePushed, Nil{}, Nil{}, Nil{})) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == _ : Maybe<&1, Tree.Tree & String>}
                  %StringProof.append_assoc_rev(String.append(BodyG, "]"), Z2, X) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == Json.parse.go(_, Json.MNatsBody{}, FramePushed, Nil{}, List.append(&2, Feedback.Color, Nil{}, f), Nil{}, Nil{}) : Maybe<&1, Tree.Tree & String>}
                  %StringProof.append_assoc_rev(BodyG, "]", String.append(Z2, X)) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == Json.parse.go(_, Json.MNatsBody{}, FramePushed, Nil{}, List.append(&2, Feedback.Color, Nil{}, f), Nil{}, Nil{}) : Maybe<&1, Tree.Tree & String>}
                  %Equal.sym(Maybe<&1, Tree.Tree & String>,
                     Json.parse.go(String.append(BodyG, String.append("]", String.append(Z2, X))), Json.MNatsBody{}, FramePushed, Nil{},
                                   List.append(&2, Feedback.Color, Nil{}, f), Nil{}, Nil{}),
                     Json.parse.go(String.append(Z2, X), Json.MNatsDone{}, FramePushed, Nil{},
                                   List.append(&2, Feedback.Color, Nil{}, f),
                                   List.append(&2, Nat, Nil{}, g), Nil{}),
                     NatsProof.body(g, String.append(Z2, X), FramePushed, Nil{},
                                    List.append(&2, Feedback.Color, Nil{}, f), Nil{})) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == _ : Maybe<&1, Tree.Tree & String>}
                  %StringProof.append_assoc_rev(Bd, S, X) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == Json.parse.go(_, Json.MKidsBody{}, FramePushed, Nil{}, List.append(&2, Feedback.Color, Nil{}, f), List.append(&2, Nat, Nil{}, g), Nil{}) : Maybe<&1, Tree.Tree & String>}
                  %StringProof.append_assoc_rev("]]]", Br, X) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == Json.parse.go(String.append(Bd, _), Json.MKidsBody{}, FramePushed, Nil{}, List.append(&2, Feedback.Color, Nil{}, f), List.append(&2, Nat, Nil{}, g), Nil{}) : Maybe<&1, Tree.Tree & String>}
                  %KidsProof.body(ckids, R, FramePushed, Nil{},
                                  List.append(&2, Feedback.Color, Nil{}, f),
                                  List.append(&2, Nat, Nil{}, g)) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == _ : Maybe<&1, Tree.Tree & String>}
                  %KidsProof.comma(r1, r2, rest0, frames, Cur1, fb, nums) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == _ : Maybe<&1, Tree.Tree & String>}
                  %KidsProof.body(rest, rest0, frames, Cur1, fb, nums) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == _ : Maybe<&1, Tree.Tree & String>}
                  %ListProof.append_assoc_rev(&2, Tree.Child, cur, Child <> Nil{}, rest) :
                    {Json.parse.go(rest0, Json.MKidsClosed{}, frames,
                                   List.append(&2, Tree.Child, cur, c <> rest), fb, nums, Nil{})
                      == Json.parse.go(rest0, Json.MKidsClosed{}, frames, _, fb, nums, Nil{})
                     : Maybe<&1, Tree.Tree & String>}
                  {==}

def TreeProof.parsed_rev(+t: Tree.Tree) ->
  {Some{(t, SNil{})} == Json.parse.go(Json.print(t), Json.MStart{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{})
   : Maybe<&1, Tree.Tree & String>}:
  match t:
    case Tree.Node{g, kids}:
      Bd = Json.show_kids.body(kids, "")
      S = String.append(",", String.append(Json.show_kids(kids), "]"))
      %Equal.sym(Maybe<&1, Tree.Tree & String>,
         Json.parse.go(String.append(Json.show_nats(g), S), Json.MNatsOpen{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}),
         Json.parse.go(S, Json.MNatsDone{}, Nil{}, Nil{}, Nil{},
                      List.append(&2, Nat, Nil{}, g), Nil{}),
         NatsProof.array(g, S, Nil{}, Nil{}, Nil{}, Nil{})) :
        {Some{(Tree.Node{g, kids}, SNil{})} == _ : Maybe<&1, Tree.Tree & String>}
      %StringProof.append_assoc_rev(Bd, "]", "]") :
        {Some{(Tree.Node{g, kids}, SNil{})}
          == Json.parse.go(_, Json.MKidsBody{}, Nil{}, Nil{}, Nil{},
                           List.append(&2, Nat, Nil{}, g), Nil{})
         : Maybe<&1, Tree.Tree & String>}
      %KidsProof.body(kids, "]", Nil{}, Nil{}, Nil{},
                      List.append(&2, Nat, Nil{}, g)) :
        {Some{(Tree.Node{g, kids}, SNil{})} == _ : Maybe<&1, Tree.Tree & String>}
      {==}

def TreeProof.parsed(+t: Tree.Tree) ->
  {Json.parse.go(Json.print(t), Json.MStart{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}) == Some{(t, SNil{})}
   : Maybe<&1, Tree.Tree & String>}:
  Equal.sym(Maybe<&1, Tree.Tree & String>, Some{(t, SNil{})},
            Json.parse.go(Json.print(t), Json.MStart{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}),
            TreeProof.parsed_rev(t))

def Laws.tree_roundtrip(t):
  e = TreeProof.parsed(t)
  Equal.cong(Maybe<&1, Tree.Tree & String>, Maybe<Tree.Tree>,
             Json.finish, Json.parse.go(Json.print(t), Json.MStart{}, Nil{}, Nil{}, Nil{}, Nil{}, Nil{}),
             Some{(t, SNil{})}, e)


def Laws.print_matches_render(t):
  JsonProof.RenderProof.print(t)


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

def SolveProof.GroupsSmaller(+S: +List<+List<Nat>>, +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          {Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{} : Bool}
          & SolveProof.GroupsSmaller(S, rest)

def SolveProof.groups_smaller_sound(+S: +List<+List<Nat>>, +groups: +List<Groups.Group>,
    +e: {Groups.groups_smaller(S, groups) == True{} : Bool}) ->
  SolveProof.GroupsSmaller(S, groups):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+f, +ws}:
          (Bool.and_true_l(Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)),
                            Groups.groups_smaller(S, rest), e),
           SolveProof.groups_smaller_sound(S, rest,
             Bool.and_true_r(Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)),
                             Groups.groups_smaller(S, rest), e)))

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
    +e: {Nat.is_lt(SolveRef.sat_add(inf, a, b), inf) == True{} : Bool}) ->
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
    +e: {Nat.is_lt(SolveRef.sat_add(inf, a, b), inf) == True{} : Bool}) ->
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

def SolveProof.BestIs(inf: Nat, best: SolveRef.Best, T: Tree.Tree) -> Type:
  match best:
    case SolveRef.Best{tree, cost}:
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

def SolveProof.best_to_maybe_some(+inf: Nat, best: SolveRef.Best, T: Tree.Tree,
    +e: {SolveRef.best_to_maybe(inf, best) == Some{T} : Maybe<Tree.Tree>}) ->
  SolveProof.BestIs(inf, best, T):
  match best:
    case SolveRef.Best{+tree, +cost}:
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

def TreeWF.proof(+t: Tree.Tree) ->
  {JsonSpec.well_formed(Json.print(t)) == True{} : Bool}:
  e0 = JsonProof.Rec.tree(t, SNil{}, Nil{}, JsonSpec.SValue{}, Unit{})
  e1 = Equal.cong(String, Maybe<String>,
         ss => JsonSpec.recognise.go(ss, JsonSpec.SValue{}, Nil{}),
         String.append(Json.print(t), SNil{}), Json.print(t),
         JsonProof.Str.append_nil(Json.print(t)))
  e2 = Equal.trans(Maybe<String>,
         JsonSpec.recognise.go(Json.print(t), JsonSpec.SValue{}, Nil{}),
         JsonSpec.recognise.go(String.append(Json.print(t), SNil{}), JsonSpec.SValue{}, Nil{}),
         JsonSpec.recognise.go(SNil{}, JsonSpec.SAfter{}, Nil{}),
         Equal.sym(Maybe<String>,
           JsonSpec.recognise.go(String.append(Json.print(t), SNil{}), JsonSpec.SValue{}, Nil{}),
           JsonSpec.recognise.go(Json.print(t), JsonSpec.SValue{}, Nil{}),
           e1),
         e0)
  Equal.cong(Maybe<String>, Bool, JsonSpec.whole,
             JsonSpec.recognise.go(Json.print(t), JsonSpec.SValue{}, Nil{}),
             JsonSpec.recognise.go(SNil{}, JsonSpec.SAfter{}, Nil{}),
             e2)

def Laws.tree_json_wellformed(t):
  TreeWF.proof(t)

# The law: a tree returned by the solver is valid. The production entry point
# is the chunked solver at one chunk, and the proof is the general one, so the
# same argument covers every chunk count.
def Laws.solve_valid(G, C, T, e):
  ParChunk.P.solve_k_valid(G, C, 1n, T, e)

# The law: the tree returned by the solver is optimal.
def Laws.solve_optimal(G, C, T2, v):
  ParChunk.P.solve_k_optimal(G, C, 1n, T2, v)

# The reference solver remains verified as the exact specification.
def Ref.solve_valid(G: +List<+List<Nat>>, C: +List<+List<Nat>>, T: Tree.Tree,
    e: {SolveRef.solve(G, C) == Some{T} : Maybe<Tree.Tree>}) ->
  Tree.Valid(T, G, C):
  MVProof.MV.solve_valid(G, C, T, e)

def Ref.solve_optimal(G: +List<+List<Nat>>, C: +List<+List<Nat>>, T2: Tree.Tree,
    v: Tree.Valid(T2, G, C)) ->
  Exists(Tree.Tree, T =>
    {SolveRef.solve(G, C) == Some{T} : Maybe<Tree.Tree>}
    & {Nat.is_le(Tree.cost(T, C), Tree.cost(T2, C)) == True{} : Bool}):
  +guesses : +List<+List<Nat>> = G
  +cands : +List<+List<Nat>> = C
  +t2 : Tree.Tree = T2
  +inf : Nat = SolveRef.inf_of(Groups.len_words(cands))
  OQStrongProof.F2.use_pair(
    Exists(Tree.Tree, T =>
      {SolveRef.solve(guesses, cands) == Some{T} : Maybe<Tree.Tree>}
      & {Nat.is_le(Tree.cost(T, cands), Tree.cost(t2, cands)) == True{} : Bool}),
    {Nat.is_le(EvalProof.Eval.cost_of(MVProof.MV.solve_best(guesses, cands)),
       Tree.cost(t2, cands)) == True{} : Bool},
    {Nat.is_lt(EvalProof.Eval.cost_of(MVProof.MV.solve_best(guesses, cands)), inf)
     == True{} : Bool},
    OQStrongProof.F2.optimal_and_finite(guesses, cands, t2, v),
    opt => fin =>
      +fin2 : {Nat.is_lt(EvalProof.Eval.cost_of(MVProof.MV.solve_best(guesses, cands)),
                inf) == True{} : Bool} = fin
      +es : {SolveRef.solve(guesses, cands)
             == Some{EvalProof.Eval.tree_of(MVProof.MV.solve_best(guesses, cands))}
             : Maybe<Tree.Tree>} =
        OQCostProof.OC.best_to_maybe_fin(inf,
          MVProof.MV.solve_best(guesses, cands), fin2)
      +hcost : {Nat.is_le(
                  Tree.cost(EvalProof.Eval.tree_of(
                    MVProof.MV.solve_best(guesses, cands)), cands),
                  EvalProof.Eval.cost_of(MVProof.MV.solve_best(guesses, cands)))
                == True{} : Bool} =
        OQCostProof.OC.machine_cost(guesses, cands)(fin2)
      +le : {Nat.is_le(
               Tree.cost(EvalProof.Eval.tree_of(
                 MVProof.MV.solve_best(guesses, cands)), cands),
               Tree.cost(t2, cands)) == True{} : Bool} =
        NatProof.Nat.is_le_trans(
          Tree.cost(EvalProof.Eval.tree_of(MVProof.MV.solve_best(guesses, cands)),
            cands),
          EvalProof.Eval.cost_of(MVProof.MV.solve_best(guesses, cands)),
          Tree.cost(t2, cands), hcost, opt)
      (EvalProof.Eval.tree_of(MVProof.MV.solve_best(guesses, cands)), (es, le)))

# The parallel root solver returns exactly the reference tree for every input.
# The root guess list is split in halves, each half is evaluated by the
# reference machine in parallel, and the per-guess results are folded with the
# reference `better`, so the first minimal result wins exactly as in `solve`.
def Par.solve_eq(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>) ->
  {SolvePar.solve(G, C) == SolveRef.solve(G, C) : Maybe<Tree.Tree>}:
  ParFold.ParFold.solve_eq(G, C)
