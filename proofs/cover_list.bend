# List and equality helpers for the cover lemma.
#
# The cover argument compares a valid tree with the per-class oracle and needs
# three list facts: syntactic word equality reflects to a propositional
# equality, a subsequence is never longer than its supersequence, and a
# subsequence of the same length is the list itself. This module proves those,
# together with the small `Nat` order facts the length argument uses.
import Base
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof

# Pointwise equality of two words.
def Cover.nat_pairs(+a: +List<Nat>, +b: +List<Nat>) -> Bool:
  List.all(&1, Nat & Nat, Feedback.pair_nat_eq,
           List.zip(&2, Nat, &2, Nat, a, b))

# Pointwise true means the words are equal.
def Cover.nat_pairs_true(+a: +List<Nat>, +b: +List<Nat>,
    +len: {List.length(&2, Nat, a) == List.length(&2, Nat, b) : Nat},
    +e: {Cover.nat_pairs(a, b) == True{} : Bool}) ->
  {a == b : +List<Nat>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b0, +bt}:
      Empty.absurd({Nil{} == b0 <> bt : +List<Nat>},
        NatProof.NatPrf.zero_ne_succ(List.length(&2, Nat, bt), len))
    case Con{+a0, +at} Nil{}:
      Empty.absurd({a0 <> at == Nil{} : +List<Nat>},
        NatProof.NatPrf.zero_ne_succ(List.length(&2, Nat, at),
          Equal.sym(Nat, List.length(&2, Nat, a0 <> at), 0n, len)))
    case Con{+a0, +at} Con{+b0, +bt}:
      +eh : {Nat.is_eq(a0, b0) == True{} : Bool} =
        FbProof.FbPrf.all_if_true_l(u => Cover.nat_pairs(at, bt),
          Nat.is_eq(a0, b0), e)
      +et : {Cover.nat_pairs(at, bt) == True{} : Bool} =
        FbProof.FbPrf.all_if_true_r(u => Cover.nat_pairs(at, bt),
          Nat.is_eq(a0, b0), e)
      +len_t : {List.length(&2, Nat, at) == List.length(&2, Nat, bt) : Nat} =
        Equal.cong(Nat, Nat, NatProof.NatPrf.pred,
                   List.length(&2, Nat, a0 <> at),
                   List.length(&2, Nat, b0 <> bt), len)
      +eh_eq : {a0 == b0 : Nat} = NatProof.NatPrf.is_eq_true(a0, b0, eh)
      +et_eq : {at == bt : +List<Nat>} = Cover.nat_pairs_true(at, bt, len_t, et)
      +e1 : {a0 <> at == b0 <> at : +List<Nat>} =
        Equal.cong(Nat, +List<Nat>, x => x <> at, a0, b0, eh_eq)
      +e2 : {b0 <> at == b0 <> bt : +List<Nat>} =
        Equal.cong(+List<Nat>, +List<Nat>, x => b0 <> x, at, bt, et_eq)
      Equal.trans(+List<Nat>, a0 <> at, b0 <> at, b0 <> bt, e1, e2)

# A true word comparison means the words are equal.
def Cover.word_eq_true(+a: +List<Nat>, +b: +List<Nat>,
    +e: {Feedback.word_eq(a, b) == True{} : Bool}) -> {a == b : +List<Nat>}:
  +len : {Nat.is_eq(List.length(&2, Nat, a), List.length(&2, Nat, b)) == True{} : Bool} =
    Logic.Proof.and_true_l(Nat.is_eq(List.length(&2, Nat, a), List.length(&2, Nat, b)),
      Cover.nat_pairs(a, b), e)
  +all : {Cover.nat_pairs(a, b) == True{} : Bool} =
    Logic.Proof.and_true_r(Nat.is_eq(List.length(&2, Nat, a), List.length(&2, Nat, b)),
      Cover.nat_pairs(a, b), e)
  Cover.nat_pairs_true(a, b,
    NatProof.NatPrf.is_eq_true(List.length(&2, Nat, a), List.length(&2, Nat, b), len), all)

# Length is zero only for the empty list.
def Cover.length_zero(+xs: +List<+List<Nat>>,
    e: {List.length(&2, +List<Nat>, xs) == 0n : Nat}) ->
  {xs == Nil{} : +List<+List<Nat>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Empty.absurd({h <> t == Nil{} : +List<+List<Nat>>},
        NatProof.NatPrf.zero_ne_succ(List.length(&2, +List<Nat>, t),
          Equal.sym(Nat, List.length(&2, +List<Nat>, h <> t), 0n, e)))

# Appending lists adds their lengths.
def Cover.length_append(+xs: +List<+List<Nat>>, +ys: +List<+List<Nat>>) ->
  {List.length(&2, +List<Nat>, List.append(&2, +List<Nat>, xs, ys))
   == Nat.add(List.length(&2, +List<Nat>, xs), List.length(&2, +List<Nat>, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, x => Nat.add(1n, x),
        List.length(&2, +List<Nat>, List.append(&2, +List<Nat>, t, ys)),
        Nat.add(List.length(&2, +List<Nat>, t), List.length(&2, +List<Nat>, ys)),
        Cover.length_append(t, ys))

# Appending one word adds one to the length.
def Cover.length_snoc(+xs: +List<+List<Nat>>, +w: +List<Nat>) ->
  {List.length(&2, +List<Nat>, List.append(&2, +List<Nat>, xs, [w]))
   == Nat.add(List.length(&2, +List<Nat>, xs), 1n) : Nat}:
  Equal.trans(Nat,
    List.length(&2, +List<Nat>, List.append(&2, +List<Nat>, xs, [w])),
    Nat.add(List.length(&2, +List<Nat>, xs), List.length(&2, +List<Nat>, [w])),
    Nat.add(List.length(&2, +List<Nat>, xs), 1n),
    Cover.length_append(xs, [w]),
    Equal.cong(Nat, Nat, x => Nat.add(List.length(&2, +List<Nat>, xs), x),
      List.length(&2, +List<Nat>, [w]), 1n, {==}))

# `1 + n` is never at most `n`.
def Cover.not_le_succ_self(n: Nat, e: {Nat.is_le(Nat.add(1n, n), n) == True{} : Bool}) -> Empty:
  match n:
    case 0n:
      Logic.Proof.false_ne_true(e)
    case 1n+p:
      Cover.not_le_succ_self(p, e)

# `a <= b` and `b <= a` give `a == b`.
def Cover.is_le_antisym(a: Nat, b: Nat,
    ab: {Nat.is_le(a, b) == True{} : Bool},
    ba: {Nat.is_le(b, a) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, Logic.Proof.false_ne_true(ba))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, Logic.Proof.false_ne_true(ab))
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, x => Nat.add(1n, x), ap, bp,
        Cover.is_le_antisym(ap, bp, ab, ba))

# Subsequence: the first list appears in order inside the second.
def Cover.Subseq(+xs: +List<+List<Nat>>, +ys: +List<+List<Nat>>) -> Type:
  match xs ys:
    case Nil{} _:
      Unit
    case Con{h, t} Nil{}:
      Empty
    case Con{h, t} Con{y, r}:
      ({h == y : +List<Nat>} & Cover.Subseq(t, r))
      | Cover.Subseq(xs, r)

# Extending the supersequence at the end keeps a subsequence.
def Cover.subseq_weaken(+xs: +List<+List<Nat>>, +ys: +List<+List<Nat>>,
    +w: +List<Nat>, p: Cover.Subseq(xs, ys)) ->
  Cover.Subseq(xs, List.append(&2, +List<Nat>, ys, [w])):
  match xs ys:
    case Nil{} _:
      Unit{}
    case Con{h, t} Nil{}:
      match p:
    case Con{h, t} Con{y, r}:
      match p:
        case Inl{q}:
          (e, pt) = q
          Inl{(e, Cover.subseq_weaken(t, r, w, pt))}
        case Inr{q}:
          Inr{Cover.subseq_weaken(xs, r, w, q)}

# The head of a list is a subsequence of the whole.
def Cover.subseq_head(+w: +List<Nat>, +ys: +List<+List<Nat>>) ->
  Cover.Subseq([w], List.append(&2, +List<Nat>, ys, [w])):
  match ys:
    case Nil{}:
      Inl{({==}, Unit{})}
    case Con{y, r}:
      Inr{Cover.subseq_head(w, r)}

# A subsequence is no longer than its supersequence.
def Cover.subseq_length(+xs: +List<+List<Nat>>, +ys: +List<+List<Nat>>,
    p: Cover.Subseq(xs, ys)) ->
  {Nat.is_le(List.length(&2, +List<Nat>, xs), List.length(&2, +List<Nat>, ys)) == True{} : Bool}:
  match xs ys:
    case Nil{} _:
      NatProof.Nat.is_le_zero_l(List.length(&2, +List<Nat>, ys))
    case Con{h, t} Nil{}:
      match p:
    case Con{h, t} Con{y, r}:
      match p:
        case Inl{q}:
          (e, pt) = q
          +lt : {Nat.is_le(List.length(&2, +List<Nat>, t),
                           List.length(&2, +List<Nat>, r)) == True{} : Bool} =
            Cover.subseq_length(t, r, pt)
          NatProof.Nat.is_le_succ(List.length(&2, +List<Nat>, t),
            List.length(&2, +List<Nat>, r), lt)
        case Inr{q}:
          +lt : {Nat.is_le(List.length(&2, +List<Nat>, xs),
                           List.length(&2, +List<Nat>, r)) == True{} : Bool} =
            Cover.subseq_length(xs, r, q)
          +lr : {Nat.is_le(List.length(&2, +List<Nat>, r),
                           Nat.add(1n, List.length(&2, +List<Nat>, r))) == True{} : Bool} =
            NatProof.Nat.is_le_of_lt(List.length(&2, +List<Nat>, r),
              Nat.add(1n, List.length(&2, +List<Nat>, r)),
              NatProof.Nat.is_lt_succ_self(List.length(&2, +List<Nat>, r)))
          NatProof.Nat.is_le_trans(List.length(&2, +List<Nat>, xs),
            List.length(&2, +List<Nat>, r),
            Nat.add(1n, List.length(&2, +List<Nat>, r)), lt, lr)

# A subsequence of the same length is the list itself.
def Cover.subseq_eq(+xs: +List<+List<Nat>>, +ys: +List<+List<Nat>>,
    p: Cover.Subseq(xs, ys),
    +len: {List.length(&2, +List<Nat>, xs) == List.length(&2, +List<Nat>, ys) : Nat}) ->
  {xs == ys : +List<+List<Nat>>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, r}:
      Empty.absurd({Nil{} == y <> r : +List<+List<Nat>>},
        NatProof.NatPrf.zero_ne_succ(List.length(&2, +List<Nat>, r), len))
    case Con{h, t} Nil{}:
      match p:
    case Con{h, t} Con{y, r}:
      match p:
        case Inl{q}:
          (e, pt) = q
          +len_t : {List.length(&2, +List<Nat>, t)
                   == List.length(&2, +List<Nat>, r) : Nat} =
            Equal.cong(Nat, Nat, NatProof.NatPrf.pred,
              List.length(&2, +List<Nat>, h <> t),
              List.length(&2, +List<Nat>, y <> r), len)
          +et : {t == r : +List<+List<Nat>>} = Cover.subseq_eq(t, r, pt, len_t)
          +e1 : {h <> t == y <> t : +List<+List<Nat>>} =
            Equal.cong(+List<Nat>, +List<+List<Nat>>, x => x <> t, h, y, e)
          +e2 : {y <> t == y <> r : +List<+List<Nat>>} =
            Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>, x => y <> x, t, r, et)
          Equal.trans(+List<+List<Nat>>, h <> t, y <> t, y <> r, e1, e2)
        case Inr{q}:
          +lt : {Nat.is_le(List.length(&2, +List<Nat>, h <> t),
                           List.length(&2, +List<Nat>, r)) == True{} : Bool} =
            Cover.subseq_length(h <> t, r, q)
          +eq2 : {Nat.is_le(Nat.add(1n, List.length(&2, +List<Nat>, r)),
                            List.length(&2, +List<Nat>, r)) == True{} : Bool} =
            Equal.trans(Bool,
              Nat.is_le(Nat.add(1n, List.length(&2, +List<Nat>, r)),
                        List.length(&2, +List<Nat>, r)),
              Nat.is_le(List.length(&2, +List<Nat>, h <> t),
                        List.length(&2, +List<Nat>, r)),
              True{},
              Equal.sym(Bool,
                Nat.is_le(List.length(&2, +List<Nat>, h <> t),
                          List.length(&2, +List<Nat>, r)),
                Nat.is_le(Nat.add(1n, List.length(&2, +List<Nat>, r)),
                          List.length(&2, +List<Nat>, r)),
                Equal.cong(Nat, Bool,
                  x => Nat.is_le(x, List.length(&2, +List<Nat>, r)),
                  List.length(&2, +List<Nat>, h <> t),
                  Nat.add(1n, List.length(&2, +List<Nat>, r)), len)),
              lt)
          Empty.absurd({h <> t == y <> r : +List<+List<Nat>>},
            Cover.not_le_succ_self(List.length(&2, +List<Nat>, r), eq2))
