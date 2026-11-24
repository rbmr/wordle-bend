# Obligation B, second part: the branching count is monotone under a subclass.
#
# `CK.count(g, ws)` is the number of feedback groups `g` cuts out of the class
# `ws`. This module proves that a subclass never has more of them:
#
#   Cover.Subseq(ws, S)  ->  CK.count(g, ws) <= CK.count(g, S)
#
# That is the step the capacity bound needs: at any node of the reference tree
# the children are the non-empty groups of the node's guess on the node's
# class, and every class below the root is a subsequence of the root class, so
# the number of children never exceeds the root's branching factor.
#
# The count is proved equal to the length of a de-duplicated list of codes
# (`CS.newc`, the number of first occurrences not already seen), and the
# monotonicity is then a proof about that list.
import Base
import ../src/feedback.bend as Feedback
import ../src/groups.bend as Groups
import ../src/solve_fast.bend as SolveFast
import ./feedback.bend as FbProof
import ./nat.bend as NatProof
import ./logic.bend as Logic
import ./cover_list.bend as Cover
import ./fast_hist5.bend as FH
import ./fast_nodup.bend as FN
import ./class_k.bend as CK

# ---------------------------------------------------------------------------
# Boolean helpers
# ---------------------------------------------------------------------------

def CS.or_true_r(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def CS.or_false_r(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# A true `or` with a false right side has a true left side.
def CS.or_false_true(a: Bool,
    +e: {Bool.or(a, False{}) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({a == True{} : Bool}, Logic.Proof.false_ne_true(e))

# `or` is constant false on a false left side.
def CS.or_false_l(b: Bool) -> {Bool.or(False{}, b) == b : Bool}:
  {==}

# A local `or` with the same right side, from equal left sides.
def CS.or_cong_r(a: Bool, p: Bool, q: Bool, e: {p == q : Bool}) ->
  {Bool.or(a, p) == Bool.or(a, q) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

# `or` with a true right side is true, from an equality.
def CS.or_r_mono(+a: Bool, +b: Bool, +h: {b == True{} : Bool}) ->
  {Bool.or(a, b) == True{} : Bool}:
  Equal.trans(Bool, Bool.or(a, b), Bool.or(a, True{}), True{},
    CS.or_cong_r(a, b, True{}, h), CS.or_true_r(a))

# `or` with a true left side is true.
def CS.or_true_l(b: Bool) -> {Bool.or(True{}, b) == True{} : Bool}:
  {==}

# Swapping the two leading alternatives of a right-nested `or`.
def CS.or_swap(a: Bool, b: Bool, c: Bool) ->
  {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

# `not p or p`.
def CS.or_not_self(p: Bool) -> {Bool.or(Bool.not(p), p) == True{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

# `(p implies q) implies ((a or p) implies (a or q))`.
def CS.or_imp(a: Bool, p: Bool, q: Bool,
    +h: {Bool.or(Bool.not(p), q) == True{} : Bool}) ->
  {Bool.or(Bool.not(Bool.or(a, p)), Bool.or(a, q)) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# `p implies q` as a boolean.
def CS.imp(p: Bool, q: Bool) -> Bool:
  Bool.or(Bool.not(p), q)

# ---------------------------------------------------------------------------
# Code lists
# ---------------------------------------------------------------------------
#
# A code is a feedback pattern, compared with `Feedback.feedback_eq`.

def CS.mem(+c: +List<Feedback.Color>, +cs: +List<+List<Feedback.Color>>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Feedback.feedback_eq(c, h), CS.mem(c, t))

# The number of codes of `cs` that are absent from `seen`, each counted once
# (the first occurrence wins). This is the number of groups the codes open.
# The membership test is a boolean case instead of a match, so the recursion
# stays structural on the code list.
def CS.newc(+cs: +List<+List<Feedback.Color>>,
            +seen: +List<+List<Feedback.Color>>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Con{h, t}:
      Feedback.Bool.case(Nat, CS.mem(h, seen), CS.newc(t, seen),
        Nat.add(1n, CS.newc(t, h <> seen)))

# One step of `newc` with the membership test as a parameter.
def CS.newc_step(+h: +List<Feedback.Color>, +t: +List<+List<Feedback.Color>>,
                 +seen: +List<+List<Feedback.Color>>, hit: Bool) -> Nat:
  match hit:
    case True{}:
      CS.newc(t, seen)
    case False{}:
      Nat.add(1n, CS.newc(t, h <> seen))

def CS.newc_case_b(+h: +List<Feedback.Color>,
    +t: +List<+List<Feedback.Color>>, +seen: +List<+List<Feedback.Color>>,
    hit: Bool) ->
  {Feedback.Bool.case(Nat, hit, CS.newc(t, seen),
     Nat.add(1n, CS.newc(t, h <> seen)))
   == CS.newc_step(h, t, seen, hit) : Nat}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def CS.newc_unfold(+h: +List<Feedback.Color>,
    +t: +List<+List<Feedback.Color>>, +seen: +List<+List<Feedback.Color>>) ->
  {CS.newc(h <> t, seen) == CS.newc_step(h, t, seen, CS.mem(h, seen)) : Nat}:
  +hit : Bool = CS.mem(h, seen)
  Equal.trans(Nat,
    CS.newc(h <> t, seen),
    Feedback.Bool.case(Nat, hit, CS.newc(t, seen),
      Nat.add(1n, CS.newc(t, h <> seen))),
    CS.newc_step(h, t, seen, hit),
    {==},
    CS.newc_case_b(h, t, seen, hit))

# Transport a lower bound from the step form to the list form.
def CS.le_unfold(+h: +List<Feedback.Color>, +t: +List<+List<Feedback.Color>>,
    +seen: +List<+List<Feedback.Color>>, +L: Nat,
    +p: {Nat.is_le(CS.newc_step(h, t, seen, CS.mem(h, seen)), L)
         == True{} : Bool}) ->
  {Nat.is_le(CS.newc(h <> t, seen), L) == True{} : Bool}:
  NatProof.Nat.is_le_eq_l(L, CS.newc_step(h, t, seen, CS.mem(h, seen)),
    CS.newc(h <> t, seen),
    Equal.sym(Nat, CS.newc(h <> t, seen),
      CS.newc_step(h, t, seen, CS.mem(h, seen)), CS.newc_unfold(h, t, seen)), p)

# Transport an upper bound from the step form to the list form.
def CS.le_fold(+h: +List<Feedback.Color>, +t: +List<+List<Feedback.Color>>,
    +seen: +List<+List<Feedback.Color>>, +A: Nat,
    +p: {Nat.is_le(A, CS.newc_step(h, t, seen, CS.mem(h, seen)))
         == True{} : Bool}) ->
  {Nat.is_le(A, CS.newc(h <> t, seen)) == True{} : Bool}:
  NatProof.Nat.is_le_eq_r(A, CS.newc_step(h, t, seen, CS.mem(h, seen)),
    CS.newc(h <> t, seen),
    Equal.sym(Nat, CS.newc(h <> t, seen),
      CS.newc_step(h, t, seen, CS.mem(h, seen)), CS.newc_unfold(h, t, seen)), p)

# Transport an upper bound of the form `1 + count` to the list form.
def CS.le_fold_add(+h: +List<Feedback.Color>,
    +t: +List<+List<Feedback.Color>>, +seen: +List<+List<Feedback.Color>>,
    +A: Nat,
    +p: {Nat.is_le(A, Nat.add(1n,
           CS.newc_step(h, t, seen, CS.mem(h, seen)))) == True{} : Bool}) ->
  {Nat.is_le(A, Nat.add(1n, CS.newc(h <> t, seen))) == True{} : Bool}:
  NatProof.Nat.is_le_eq_r(A,
    Nat.add(1n, CS.newc_step(h, t, seen, CS.mem(h, seen))),
    Nat.add(1n, CS.newc(h <> t, seen)),
    Equal.cong(Nat, Nat, x => Nat.add(1n, x),
      CS.newc_step(h, t, seen, CS.mem(h, seen)), CS.newc(h <> t, seen),
      Equal.sym(Nat, CS.newc(h <> t, seen),
        CS.newc_step(h, t, seen, CS.mem(h, seen)), CS.newc_unfold(h, t, seen))),
    p)

# Transport an equality from the step form to the list form.
def CS.eq_unfold(+h: +List<Feedback.Color>, +t: +List<+List<Feedback.Color>>,
    +seen: +List<+List<Feedback.Color>>, +X: Nat,
    +p: {CS.newc_step(h, t, seen, CS.mem(h, seen)) == X : Nat}) ->
  {CS.newc(h <> t, seen) == X : Nat}:
  Equal.trans(Nat, CS.newc(h <> t, seen),
    CS.newc_step(h, t, seen, CS.mem(h, seen)), X,
    CS.newc_unfold(h, t, seen), p)

# Transport an equality into the list form.
def CS.eq_fold(+h: +List<Feedback.Color>, +t: +List<+List<Feedback.Color>>,
    +seen: +List<+List<Feedback.Color>>, +X: Nat,
    +p: {X == CS.newc_step(h, t, seen, CS.mem(h, seen)) : Nat}) ->
  {X == CS.newc(h <> t, seen) : Nat}:
  Equal.trans(Nat, X, CS.newc_step(h, t, seen, CS.mem(h, seen)),
    CS.newc(h <> t, seen), p,
    Equal.sym(Nat, CS.newc(h <> t, seen),
      CS.newc_step(h, t, seen, CS.mem(h, seen)), CS.newc_unfold(h, t, seen)))

# `newc` never exceeds the length of the code list.
def CS.newc_le_len_step(+h: +List<Feedback.Color>,
    +t: +List<+List<Feedback.Color>>, +seen: +List<+List<Feedback.Color>>,
    hit: Bool,
    +ih: {Nat.is_le(CS.newc(t, seen), List.length(&2, +List<Feedback.Color>, t))
          == True{} : Bool},
    +ih2: {Nat.is_le(CS.newc(t, h <> seen),
                     List.length(&2, +List<Feedback.Color>, t))
           == True{} : Bool}) ->
  {Nat.is_le(CS.newc_step(h, t, seen, hit),
             List.length(&2, +List<Feedback.Color>, h <> t)) == True{} : Bool}:
  match hit:
    case True{}:
      NatProof.Nat.is_le_trans(CS.newc(t, seen),
        List.length(&2, +List<Feedback.Color>, t),
        List.length(&2, +List<Feedback.Color>, h <> t), ih,
        NatProof.Nat.is_le_add_self_l(1n,
          List.length(&2, +List<Feedback.Color>, t)))
    case False{}:
      NatProof.Nat.is_le_add_l(CS.newc(t, h <> seen),
        List.length(&2, +List<Feedback.Color>, t), 1n, ih2)

def CS.newc_le_len(+cs: +List<+List<Feedback.Color>>,
    +seen: +List<+List<Feedback.Color>>) ->
  {Nat.is_le(CS.newc(cs, seen), List.length(&2, +List<Feedback.Color>, cs))
   == True{} : Bool}:
  match cs:
    case Nil{}:
      NatProof.Nat.is_le_zero_l(0n)
    case Con{h, t}:
      CS.le_unfold(h, t, seen, List.length(&2, +List<Feedback.Color>, h <> t),
        CS.newc_le_len_step(h, t, seen, CS.mem(h, seen),
          CS.newc_le_len(t, seen), CS.newc_le_len(t, h <> seen)))

# ---------------------------------------------------------------------------
# Two seen lists that agree on the codes of a list
# ---------------------------------------------------------------------------

# Every code of `cs` that occurs in `a` also occurs in `b`.
def CS.sub(+cs: +List<+List<Feedback.Color>>,
           +a: +List<+List<Feedback.Color>>,
           +b: +List<+List<Feedback.Color>>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(CS.imp(CS.mem(h, a), CS.mem(h, b)), CS.sub(t, a, b))

# `a` and `b` hold the same codes of `cs`.
def CS.same(+cs: +List<+List<Feedback.Color>>,
            +a: +List<+List<Feedback.Color>>,
            +b: +List<+List<Feedback.Color>>) -> Bool:
  Bool.and(CS.sub(cs, a, b), CS.sub(cs, b, a))

def CS.same_sub1(+cs: +List<+List<Feedback.Color>>,
    +a: +List<+List<Feedback.Color>>, +b: +List<+List<Feedback.Color>>,
    +h: {CS.same(cs, a, b) == True{} : Bool}) ->
  {CS.sub(cs, a, b) == True{} : Bool}:
  Logic.Proof.and_true_l(CS.sub(cs, a, b), CS.sub(cs, b, a), h)

def CS.same_sub2(+cs: +List<+List<Feedback.Color>>,
    +a: +List<+List<Feedback.Color>>, +b: +List<+List<Feedback.Color>>,
    +h: {CS.same(cs, a, b) == True{} : Bool}) ->
  {CS.sub(cs, b, a) == True{} : Bool}:
  Logic.Proof.and_true_r(CS.sub(cs, a, b), CS.sub(cs, b, a), h)

def CS.sub_head(+hc: +List<Feedback.Color>, +t: +List<+List<Feedback.Color>>,
    +a: +List<+List<Feedback.Color>>, +b: +List<+List<Feedback.Color>>,
    +h: {CS.sub(hc <> t, a, b) == True{} : Bool}) ->
  {CS.imp(CS.mem(hc, a), CS.mem(hc, b)) == True{} : Bool}:
  Logic.Proof.and_true_l(CS.imp(CS.mem(hc, a), CS.mem(hc, b)), CS.sub(t, a, b),
    h)

def CS.sub_tail(+hc: +List<Feedback.Color>, +t: +List<+List<Feedback.Color>>,
    +a: +List<+List<Feedback.Color>>, +b: +List<+List<Feedback.Color>>,
    +h: {CS.sub(hc <> t, a, b) == True{} : Bool}) ->
  {CS.sub(t, a, b) == True{} : Bool}:
  Logic.Proof.and_true_r(CS.imp(CS.mem(hc, a), CS.mem(hc, b)), CS.sub(t, a, b),
    h)

# Mutual implication of booleans is equality.
def CS.imp_eq(p: Bool, q: Bool,
    +h1: {CS.imp(p, q) == True{} : Bool},
    +h2: {CS.imp(q, p) == True{} : Bool}) -> {p == q : Bool}:
  match p q:
    case True{} True{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, Logic.Proof.false_ne_true(h1))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, Logic.Proof.false_ne_true(h2))
    case False{} False{}:
      {==}

# Membership does not depend on the order of two leading codes.
def CS.mem_swap(+c: +List<Feedback.Color>,
    +seen: +List<+List<Feedback.Color>>, +y: +List<Feedback.Color>,
    +hc: +List<Feedback.Color>) ->
  {CS.mem(c, y <> (hc <> seen)) == CS.mem(c, hc <> (y <> seen)) : Bool}:
  CS.or_swap(Feedback.feedback_eq(c, y), Feedback.feedback_eq(c, hc),
    CS.mem(c, seen))

def CS.sub_swap(+cs: +List<+List<Feedback.Color>>,
    +seen: +List<+List<Feedback.Color>>, +y: +List<Feedback.Color>,
    +hc: +List<Feedback.Color>) ->
  {CS.sub(cs, y <> (hc <> seen), hc <> (y <> seen)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{c, t}:
      Logic.Proof.and_intro(
        CS.imp(CS.mem(c, y <> (hc <> seen)), CS.mem(c, hc <> (y <> seen))),
        CS.sub(t, y <> (hc <> seen), hc <> (y <> seen)),
        Equal.trans(Bool, CS.imp(CS.mem(c, y <> (hc <> seen)),
                       CS.mem(c, hc <> (y <> seen))),
          CS.imp(CS.mem(c, y <> (hc <> seen)), CS.mem(c, y <> (hc <> seen))),
          True{},
          Equal.cong(Bool, Bool,
            x => CS.imp(CS.mem(c, y <> (hc <> seen)), x),
            CS.mem(c, hc <> (y <> seen)), CS.mem(c, y <> (hc <> seen)),
            Equal.sym(Bool, CS.mem(c, y <> (hc <> seen)),
              CS.mem(c, hc <> (y <> seen)),
              CS.mem_swap(c, seen, y, hc))),
          CS.or_not_self(CS.mem(c, y <> (hc <> seen)))),
        CS.sub_swap(t, seen, y, hc))

def CS.same_swap(+cs: +List<+List<Feedback.Color>>,
    +seen: +List<+List<Feedback.Color>>, +y: +List<Feedback.Color>,
    +hc: +List<Feedback.Color>) ->
  {CS.same(cs, y <> (hc <> seen), hc <> (y <> seen)) == True{} : Bool}:
  Logic.Proof.and_intro(CS.sub(cs, y <> (hc <> seen), hc <> (y <> seen)),
    CS.sub(cs, hc <> (y <> seen), y <> (hc <> seen)),
    CS.sub_swap(cs, seen, y, hc), CS.sub_swap(cs, seen, hc, y))

# Consing the same code to both seen lists keeps the agreement.
def CS.sub_cons(+cs: +List<+List<Feedback.Color>>,
    +a: +List<+List<Feedback.Color>>, +b: +List<+List<Feedback.Color>>,
    +x: +List<Feedback.Color>,
    +h: {CS.sub(cs, a, b) == True{} : Bool}) ->
  {CS.sub(cs, x <> a, x <> b) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{hc, t}:
      Logic.Proof.and_intro(
        CS.imp(CS.mem(hc, x <> a), CS.mem(hc, x <> b)),
        CS.sub(t, x <> a, x <> b),
        CS.or_imp(Feedback.feedback_eq(hc, x), CS.mem(hc, a), CS.mem(hc, b),
          CS.sub_head(hc, t, a, b, h)),
        CS.sub_cons(t, a, b, x, CS.sub_tail(hc, t, a, b, h)))

def CS.same_cons(+cs: +List<+List<Feedback.Color>>,
    +a: +List<+List<Feedback.Color>>, +b: +List<+List<Feedback.Color>>,
    +x: +List<Feedback.Color>,
    +h: {CS.same(cs, a, b) == True{} : Bool}) ->
  {CS.same(cs, x <> a, x <> b) == True{} : Bool}:
  Logic.Proof.and_intro(CS.sub(cs, x <> a, x <> b), CS.sub(cs, x <> b, x <> a),
    CS.sub_cons(cs, a, b, x, CS.same_sub1(cs, a, b, h)),
    CS.sub_cons(cs, b, a, x, CS.same_sub2(cs, a, b, h)))

# ---------------------------------------------------------------------------
# The seen list is a set: agreement gives equal new-code counts
# ---------------------------------------------------------------------------

def CS.same_step(+h: +List<Feedback.Color>, +t: +List<+List<Feedback.Color>>,
    +a: +List<+List<Feedback.Color>>, +b: +List<+List<Feedback.Color>>,
    pa: Bool, pb: Bool,
    +ea: {pa == CS.mem(h, a) : Bool},
    +eb: {pb == CS.mem(h, b) : Bool},
    +heq: {pa == pb : Bool},
    +ih: {CS.newc(t, a) == CS.newc(t, b) : Nat},
    +ih2: {CS.newc(t, h <> a) == CS.newc(t, h <> b) : Nat}) ->
  {CS.newc_step(h, t, a, pa) == CS.newc_step(h, t, b, pb) : Nat}:
  match pa:
    case True{}:
      +epb : {pb == True{} : Bool} = Equal.sym(Bool, True{}, pb, heq)
      +e : {CS.newc_step(h, t, b, pb) == CS.newc(t, b) : Nat} =
        Equal.cong(Bool, Nat, x => CS.newc_step(h, t, b, x), pb, True{}, epb)
      Equal.trans(Nat, CS.newc(t, a), CS.newc(t, b), CS.newc_step(h, t, b, pb),
        ih, Equal.sym(Nat, CS.newc_step(h, t, b, pb), CS.newc(t, b), e))
    case False{}:
      +epb : {pb == False{} : Bool} = Equal.sym(Bool, False{}, pb, heq)
      +e : {CS.newc_step(h, t, b, pb)
            == Nat.add(1n, CS.newc(t, h <> b)) : Nat} =
        Equal.cong(Bool, Nat, x => CS.newc_step(h, t, b, x), pb, False{}, epb)
      Equal.trans(Nat, Nat.add(1n, CS.newc(t, h <> a)),
        Nat.add(1n, CS.newc(t, h <> b)),
        CS.newc_step(h, t, b, pb),
        Equal.cong(Nat, Nat, x => Nat.add(1n, x), CS.newc(t, h <> a),
          CS.newc(t, h <> b), ih2),
        Equal.sym(Nat, CS.newc_step(h, t, b, pb),
          Nat.add(1n, CS.newc(t, h <> b)), e))

def CS.same_mem(+h: +List<Feedback.Color>, +t: +List<+List<Feedback.Color>>,
    +a: +List<+List<Feedback.Color>>, +b: +List<+List<Feedback.Color>>,
    +hsm: {CS.same(h <> t, a, b) == True{} : Bool}) ->
  {CS.mem(h, a) == CS.mem(h, b) : Bool}:
  CS.imp_eq(CS.mem(h, a), CS.mem(h, b),
    CS.sub_head(h, t, a, b, CS.same_sub1(h <> t, a, b, hsm)),
    CS.sub_head(h, t, b, a, CS.same_sub2(h <> t, a, b, hsm)))

def CS.same_tail(+h: +List<Feedback.Color>, +t: +List<+List<Feedback.Color>>,
    +a: +List<+List<Feedback.Color>>, +b: +List<+List<Feedback.Color>>,
    +hsm: {CS.same(h <> t, a, b) == True{} : Bool}) ->
  {CS.same(t, a, b) == True{} : Bool}:
  Logic.Proof.and_intro(CS.sub(t, a, b), CS.sub(t, b, a),
    CS.sub_tail(h, t, a, b, CS.same_sub1(h <> t, a, b, hsm)),
    CS.sub_tail(h, t, b, a, CS.same_sub2(h <> t, a, b, hsm)))

def CS.newc_same(+cs: +List<+List<Feedback.Color>>,
    +a: +List<+List<Feedback.Color>>, +b: +List<+List<Feedback.Color>>,
    +h: {CS.same(cs, a, b) == True{} : Bool}) ->
  {CS.newc(cs, a) == CS.newc(cs, b) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case Con{hc, t}:
      +ht = CS.same_tail(hc, t, a, b, h)
      CS.eq_fold(hc, t, b, CS.newc(hc <> t, a),
        CS.eq_unfold(hc, t, a, CS.newc_step(hc, t, b, CS.mem(hc, b)),
          CS.same_step(hc, t, a, b, CS.mem(hc, a), CS.mem(hc, b),
            {==}, {==}, CS.same_mem(hc, t, a, b, h),
            CS.newc_same(t, a, b, ht),
            CS.newc_same(t, hc <> a, hc <> b, CS.same_cons(t, a, b, hc, ht)))))

# ---------------------------------------------------------------------------
# Adding one code to the seen set removes at most one new code
# ---------------------------------------------------------------------------

def CS.drop_step(+h: +List<Feedback.Color>, +t: +List<+List<Feedback.Color>>,
    +seen: +List<+List<Feedback.Color>>, +y: +List<Feedback.Color>,
    hit: Bool, hit2: Bool,
    +eh: {hit == CS.mem(h, seen) : Bool},
    +eh2: {hit2 == CS.mem(h, y <> seen) : Bool},
    +ih: {Nat.is_le(CS.newc(t, h <> seen),
                    Nat.add(1n, CS.newc(t, h <> (y <> seen))))
          == True{} : Bool},
    +ih2: {Nat.is_le(CS.newc(t, seen), Nat.add(1n, CS.newc(t, y <> seen)))
           == True{} : Bool}) ->
  {Nat.is_le(CS.newc_step(h, t, seen, hit),
             Nat.add(1n, CS.newc_step(h, t, y <> seen, hit2))) == True{} : Bool}:
  match hit:
    case True{}:
      +eht : {CS.mem(h, seen) == True{} : Bool} = Equal.sym(Bool, True{}, CS.mem(h, seen), eh)
      +eh2t : {hit2 == True{} : Bool} =
        Equal.trans(Bool, hit2, CS.mem(h, y <> seen), True{}, eh2,
          CS.or_r_mono(Feedback.feedback_eq(h, y), CS.mem(h, seen), eht))
      +eb : {CS.newc_step(h, t, y <> seen, hit2)
             == CS.newc(t, y <> seen) : Nat} =
        Equal.cong(Bool, Nat, x => CS.newc_step(h, t, y <> seen, x),
          hit2, True{}, eh2t)
      +econg : {Nat.add(1n, CS.newc(t, y <> seen))
                == Nat.add(1n, CS.newc_step(h, t, y <> seen, hit2)) : Nat} =
        Equal.sym(Nat,
          Nat.add(1n, CS.newc_step(h, t, y <> seen, hit2)),
          Nat.add(1n, CS.newc(t, y <> seen)),
          Equal.cong(Nat, Nat, x => Nat.add(1n, x),
            CS.newc_step(h, t, y <> seen, hit2), CS.newc(t, y <> seen), eb))
      NatProof.Nat.is_le_eq_r(CS.newc(t, seen),
        Nat.add(1n, CS.newc(t, y <> seen)),
        Nat.add(1n, CS.newc_step(h, t, y <> seen, hit2)), econg, ih2)
    case False{}:
      match hit2:
        case True{}:
          +ehf : {CS.mem(h, seen) == False{} : Bool} =
            Equal.sym(Bool, False{}, CS.mem(h, seen), eh)
          +em : {CS.mem(h, y <> seen) == True{} : Bool} =
            Equal.trans(Bool, CS.mem(h, y <> seen), hit2, True{},
              Equal.sym(Bool, hit2, CS.mem(h, y <> seen), eh2), {==})
          +e1 : {Bool.or(Feedback.feedback_eq(h, y), False{})
                 == True{} : Bool} =
            Equal.trans(Bool,
              Bool.or(Feedback.feedback_eq(h, y), False{}),
              Bool.or(Feedback.feedback_eq(h, y), CS.mem(h, seen)), True{},
              Equal.sym(Bool,
                Bool.or(Feedback.feedback_eq(h, y), CS.mem(h, seen)),
                Bool.or(Feedback.feedback_eq(h, y), False{}),
                CS.or_cong_r(Feedback.feedback_eq(h, y), CS.mem(h, seen),
                  False{}, ehf)),
              em)
          +ehy : {Feedback.feedback_eq(h, y) == True{} : Bool} =
            CS.or_false_true(Feedback.feedback_eq(h, y), e1)
          +ehy_eq : {h == y : +List<Feedback.Color>} =
            FbProof.FbPrf.feedback_eq_true(h, y, ehy)
          +eseen : {h <> seen == y <> seen : +List<+List<Feedback.Color>>} =
            Equal.cong(+List<Feedback.Color>, +List<+List<Feedback.Color>>,
              x => x <> seen, h, y, ehy_eq)
          +eyx : {CS.newc(t, h <> seen) == CS.newc(t, y <> seen) : Nat} =
            Equal.cong(+List<+List<Feedback.Color>>, Nat,
              s2 => CS.newc(t, s2), h <> seen, y <> seen, eseen)
          +eb : {CS.newc_step(h, t, y <> seen, hit2)
                 == CS.newc(t, y <> seen) : Nat} =
            Equal.cong(Bool, Nat, x => CS.newc_step(h, t, y <> seen, x),
              hit2, True{}, {==})
          +econg : {Nat.add(1n, CS.newc(t, y <> seen))
                    == Nat.add(1n, CS.newc_step(h, t, y <> seen, hit2))
                    : Nat} =
            Equal.sym(Nat,
              Nat.add(1n, CS.newc_step(h, t, y <> seen, hit2)),
              Nat.add(1n, CS.newc(t, y <> seen)),
              Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                CS.newc_step(h, t, y <> seen, hit2),
                CS.newc(t, y <> seen), eb))
          +p1 : {Nat.is_le(Nat.add(1n, CS.newc(t, h <> seen)),
                    Nat.add(1n, CS.newc(t, y <> seen))) == True{} : Bool} =
            NatProof.Nat.is_le_eq_r(Nat.add(1n, CS.newc(t, h <> seen)),
              Nat.add(1n, CS.newc(t, h <> seen)),
              Nat.add(1n, CS.newc(t, y <> seen)),
              Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                CS.newc(t, h <> seen), CS.newc(t, y <> seen), eyx),
              NatProof.Nat.is_le_add_l(CS.newc(t, h <> seen),
                CS.newc(t, h <> seen), 1n,
                NatProof.Nat.is_le_refl(CS.newc(t, h <> seen))))
          p1
        case False{}:
          NatProof.Nat.is_le_add_l(CS.newc(t, h <> seen),
            Nat.add(1n, CS.newc(t, h <> (y <> seen))), 1n, ih)

def CS.drop(+cs: +List<+List<Feedback.Color>>,
    +seen: +List<+List<Feedback.Color>>, +y: +List<Feedback.Color>) ->
  {Nat.is_le(CS.newc(cs, seen), Nat.add(1n, CS.newc(cs, y <> seen)))
   == True{} : Bool}:
  match cs:
    case Nil{}:
      NatProof.Nat.is_le_zero_l(1n)
    case Con{h, t}:
      +swap : {CS.newc(t, y <> (h <> seen)) == CS.newc(t, h <> (y <> seen))
               : Nat} =
        CS.newc_same(t, y <> (h <> seen), h <> (y <> seen),
          CS.same_swap(t, seen, y, h))
      +ih_swap : {Nat.is_le(CS.newc(t, h <> seen),
                     Nat.add(1n, CS.newc(t, h <> (y <> seen)))) == True{}
                   : Bool} =
        NatProof.Nat.is_le_eq_r(CS.newc(t, h <> seen),
          Nat.add(1n, CS.newc(t, y <> (h <> seen))),
          Nat.add(1n, CS.newc(t, h <> (y <> seen))),
          Equal.cong(Nat, Nat, x => Nat.add(1n, x),
            CS.newc(t, y <> (h <> seen)), CS.newc(t, h <> (y <> seen)), swap),
          CS.drop(t, h <> seen, y))
      CS.le_unfold(h, t, seen, Nat.add(1n, CS.newc(h <> t, y <> seen)),
        CS.le_fold_add(h, t, y <> seen,
          CS.newc_step(h, t, seen, CS.mem(h, seen)),
          CS.drop_step(h, t, seen, y, CS.mem(h, seen), CS.mem(h, y <> seen),
            {==}, {==}, ih_swap, CS.drop(t, seen, y))))

# Preprending a code to the list never lowers the count.
def CS.prepend(+cs: +List<+List<Feedback.Color>>,
    +seen: +List<+List<Feedback.Color>>, +y: +List<Feedback.Color>,
    hit: Bool, +eh: {hit == CS.mem(y, seen) : Bool}) ->
  {Nat.is_le(CS.newc(cs, seen), CS.newc_step(y, cs, seen, hit)) == True{} : Bool}:
  match hit:
    case True{}:
      NatProof.Nat.is_le_refl(CS.newc(cs, seen))
    case False{}:
      CS.drop(cs, seen, y)

# One step of the new-code count on two lists with the same leading code.
def CS.newc_step_le(+y: +List<Feedback.Color>, +t: +List<+List<Feedback.Color>>,
    +r: +List<+List<Feedback.Color>>, +seen: +List<+List<Feedback.Color>>,
    hit: Bool,
    +ih_t: {Nat.is_le(CS.newc(t, seen), CS.newc(r, seen)) == True{} : Bool},
    +ih_y: {Nat.is_le(CS.newc(t, y <> seen), CS.newc(r, y <> seen))
            == True{} : Bool}) ->
  {Nat.is_le(CS.newc_step(y, t, seen, hit),
             CS.newc_step(y, r, seen, hit)) == True{} : Bool}:
  match hit:
    case True{}:
      ih_t
    case False{}:
      ih_y

# ---------------------------------------------------------------------------
# Subsequences of code lists
# ---------------------------------------------------------------------------

# Subsequence of code lists.
def CS.SubC(+xs: +List<+List<Feedback.Color>>,
            +ys: +List<+List<Feedback.Color>>) -> Type:
  match xs ys:
    case Nil{} _:
      Unit
    case Con{h, t} Nil{}:
      Empty
    case Con{h, t} Con{y, r}:
      ({h == y : +List<Feedback.Color>} & CS.SubC(t, r)) | CS.SubC(xs, r)

# Eliminate a computed pair with a continuation, so it is destructured once.
def CS.use_pair(-R: Type, -A: Type, -B: Type, p: A & B,
    k: A -> B -> R) -> R:
  match p:
    case (a, b):
      k(a, b)

# A subsequence proof can be used twice.
def CS.subc_dup(+xs: +List<+List<Feedback.Color>>,
    +ys: +List<+List<Feedback.Color>>, p: CS.SubC(xs, ys)) ->
  CS.SubC(xs, ys) & CS.SubC(xs, ys):
  match xs ys:
    case Nil{} _:
      (Unit{}, Unit{})
    case Con{h, t} Nil{}:
      match p:
    case Con{h, t} Con{y, r}:
      match p:
        case Inl{q}:
          (+e, pt) = q
          CS.use_pair(CS.SubC(xs, ys) & CS.SubC(xs, ys),
            CS.SubC(t, r), CS.SubC(t, r), CS.subc_dup(t, r, pt),
            p1 => p2 => (Inl{(e, p1)}, Inl{(e, p2)}))
        case Inr{q}:
          CS.use_pair(CS.SubC(xs, ys) & CS.SubC(xs, ys),
            CS.SubC(xs, r), CS.SubC(xs, r), CS.subc_dup(xs, r, q),
            p1 => p2 => (Inr{p1}, Inr{p2}))

# The new-code count is monotone along a code subsequence.
def CS.subc_count(+xs: +List<+List<Feedback.Color>>,
    +ys: +List<+List<Feedback.Color>>, p: CS.SubC(xs, ys),
    +seen: +List<+List<Feedback.Color>>) ->
  {Nat.is_le(CS.newc(xs, seen), CS.newc(ys, seen)) == True{} : Bool}:
  match xs ys:
    case Nil{} _:
      NatProof.Nat.is_le_zero_l(CS.newc(ys, seen))
    case Con{h, t} Nil{}:
      match p:
    case Con{h, t} Con{y, r}:
      match p:
        case Inl{q}:
          (e, pt0) = q
          CS.use_pair(
            {Nat.is_le(CS.newc(h <> t, seen), CS.newc(y <> r, seen))
             == True{} : Bool},
            CS.SubC(t, r), CS.SubC(t, r), CS.subc_dup(t, r, pt0),
            pt => pt2 =>
              +eq : {CS.newc_step(h, t, seen, CS.mem(h, seen))
                     == CS.newc_step(y, t, seen, CS.mem(y, seen)) : Nat} =
                Equal.cong(+List<Feedback.Color>, Nat,
                  x => CS.newc_step(x, t, seen, CS.mem(x, seen)), h, y, e)
              +stp : {Nat.is_le(CS.newc_step(y, t, seen, CS.mem(y, seen)),
                        CS.newc_step(y, r, seen, CS.mem(y, seen)))
                      == True{} : Bool} =
                CS.newc_step_le(y, t, r, seen, CS.mem(y, seen),
                  CS.subc_count(t, r, pt, seen),
                  CS.subc_count(t, r, pt2, y <> seen))
              +stp2 : {Nat.is_le(CS.newc_step(h, t, seen, CS.mem(h, seen)),
                         CS.newc_step(y, r, seen, CS.mem(y, seen)))
                       == True{} : Bool} =
                NatProof.Nat.is_le_eq_l(
                  CS.newc_step(y, r, seen, CS.mem(y, seen)),
                  CS.newc_step(y, t, seen, CS.mem(y, seen)),
                  CS.newc_step(h, t, seen, CS.mem(h, seen)),
                  Equal.sym(Nat, CS.newc_step(h, t, seen, CS.mem(h, seen)),
                    CS.newc_step(y, t, seen, CS.mem(y, seen)), eq), stp)
              CS.le_unfold(h, t, seen, CS.newc(y <> r, seen),
                CS.le_fold(y, r, seen,
                  CS.newc_step(h, t, seen, CS.mem(h, seen)), stp2)))
        case Inr{q}:
          NatProof.Nat.is_le_trans(CS.newc(xs, seen), CS.newc(r, seen),
            CS.newc(y <> r, seen),
            CS.subc_count(xs, r, q, seen),
            CS.le_fold(y, r, seen, CS.newc(r, seen),
              CS.prepend(r, seen, y, CS.mem(y, seen), {==})))
