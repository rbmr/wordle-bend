import Base
import ./LAWS.bend as Laws
import ./src/feedback.bend as Feedback
import ./src/tree.bend as Tree
import ./src/solve.bend as Solve
import ./src/json.bend as Json

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
