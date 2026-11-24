# Obligation B, second part: the branching count is monotone under a subclass.
#
# `CK.CK.count(g, ws)` is the number of feedback groups `g` cuts out of the class
# `ws`. This module proves that a subclass never has more of them:
#
#   Cover.Subseq(ws, S)  ->  CK.CK.count(g, ws) <= CK.CK.count(g, S)
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

# ---------------------------------------------------------------------------
# Codes of a word list
# ---------------------------------------------------------------------------

# The codes of the words of `ws` that differ from `g`, in order. The word test
# is a boolean case (not a match) so the recursion stays structural.
def CS.codes(+g: +List<Nat>, +ws: +List<+List<Nat>>) ->
  +List<+List<Feedback.Color>>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, t}:
      Feedback.Bool.case(+List<+List<Feedback.Color>>, Feedback.word_eq(g, w),
        CS.codes(g, t),
        Feedback.feedback(g, w) <> CS.codes(g, t))

# One step of `codes` with the word test as a parameter.
def CS.codes_step(+g: +List<Nat>, +w: +List<Nat>,
    +t: +List<+List<Nat>>, same: Bool) -> +List<+List<Feedback.Color>>:
  match same:
    case True{}:
      CS.codes(g, t)
    case False{}:
      Feedback.feedback(g, w) <> CS.codes(g, t)

# A code list with one code in front keeps a code subsequence.
def CS.subc_prepend(+xs: +List<+List<Feedback.Color>>,
    +c: +List<Feedback.Color>, +ys: +List<+List<Feedback.Color>>,
    p: CS.SubC(xs, ys)) -> CS.SubC(xs, c <> ys):
  match xs ys:
    case Nil{} _:
      Unit{}
    case Con{h, t} Nil{}:
      match p:
    case Con{h, t} Con{y, r}:
      Inr{p}

# The same head word on both sides keeps a code subsequence.
def CS.codes_cons_sub(+g: +List<Nat>, +w: +List<Nat>,
    +t: +List<+List<Nat>>, +r: +List<+List<Nat>>, b: Bool,
    p: CS.SubC(CS.codes(g, t), CS.codes(g, r))) ->
  CS.SubC(
    Feedback.Bool.case(+List<+List<Feedback.Color>>, b, CS.codes(g, t),
      Feedback.feedback(g, w) <> CS.codes(g, t)),
    Feedback.Bool.case(+List<+List<Feedback.Color>>, b, CS.codes(g, r),
      Feedback.feedback(g, w) <> CS.codes(g, r))):
  match b:
    case True{}:
      p
    case False{}:
      Inl{({==}, p)}

# A skipped head word keeps a code subsequence.
def CS.codes_tail_sub(+xs: +List<+List<Feedback.Color>>, +g: +List<Nat>,
    +w: +List<Nat>, +r: +List<+List<Nat>>, b: Bool,
    p: CS.SubC(xs, CS.codes(g, r))) ->
  CS.SubC(xs,
    Feedback.Bool.case(+List<+List<Feedback.Color>>, b, CS.codes(g, r),
      Feedback.feedback(g, w) <> CS.codes(g, r))):
  match b:
    case True{}:
      p
    case False{}:
      CS.subc_prepend(xs, Feedback.feedback(g, w), CS.codes(g, r), p)

# A subclass never has more codes for the same guess.
def CS.sub_codes(+g: +List<Nat>, +ws: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, p: Cover.Cover.Subseq(ws, S)) ->
  CS.SubC(CS.codes(g, ws), CS.codes(g, S)):
  match ws S:
    case Nil{} _:
      Unit{}
    case Con{h, t} Nil{}:
      match p:
    case Con{h, t} Con{y, r}:
      match p:
        case Inl{q}:
          (e, pt) = q
          +eh : {CS.codes(g, h <> t) == CS.codes(g, y <> t)
                 : +List<+List<Feedback.Color>>} =
            Equal.cong(+List<Nat>, +List<+List<Feedback.Color>>,
              x => CS.codes(g, x <> t), h, y, e)
          %Equal.sym(+List<+List<Feedback.Color>>,
              CS.codes(g, h <> t), CS.codes(g, y <> t), eh) :
            CS.SubC(_, CS.codes(g, y <> r))
          CS.codes_cons_sub(g, y, t, r, Feedback.word_eq(g, y),
            CS.sub_codes(g, t, r, pt))
        case Inr{q}:
          CS.codes_tail_sub(CS.codes(g, ws), g, y, r,
            Feedback.word_eq(g, y),
            CS.sub_codes(g, ws, r, q))

# ---------------------------------------------------------------------------
# The count as the length of the reference group list
# ---------------------------------------------------------------------------

def CS.len_fgroups_to_groups(+fg: +List<SolveFast.FGroup>) ->
  {List.length(&2, Groups.Group, FN.FN.fgroups_to_groups(fg))
   == FH.FH.fgroups_count(fg) : Nat}:
  match fg:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case SolveFast.FGroup{f, len, rws}:
          +ih : {List.length(&2, Groups.Group, FN.FN.fgroups_to_groups(rest))
                 == FH.FH.fgroups_count(rest) : Nat} =
            CS.len_fgroups_to_groups(rest)
          Equal.cong(Nat, Nat, x => Nat.add(1n, x),
            List.length(&2, Groups.Group, FN.FN.fgroups_to_groups(rest)),
            FH.FH.fgroups_count(rest), ih)

# The count is the length of the reference group list of the class.
def CS.count_eq_build(+g: +List<Nat>, +ws: +List<+List<Nat>>) ->
  {CK.CK.count(g, ws)
   == List.length(&2, Groups.Group, Groups.groups_build(g, ws, Nil{})) : Nat}:
  +e : {FN.FN.fgroups_to_groups(SolveFast.fgroups_build_fast(g, ws, Nil{}))
        == Groups.groups_build(g, ws, Nil{}) : +List<Groups.Group>} =
    FN.FN.fgroups_build_eq(g, ws, Nil{})
  +e2 : {List.length(&2, Groups.Group,
           FN.FN.fgroups_to_groups(SolveFast.fgroups_build_fast(g, ws, Nil{})))
         == List.length(&2, Groups.Group, Groups.groups_build(g, ws, Nil{}))
         : Nat} =
    Equal.cong(+List<Groups.Group>, Nat,
      x => List.length(&2, Groups.Group, x),
      FN.FN.fgroups_to_groups(SolveFast.fgroups_build_fast(g, ws, Nil{})),
      Groups.groups_build(g, ws, Nil{}), e)
  +e1 : {CK.CK.count(g, ws)
         == List.length(&2, Groups.Group,
              FN.FN.fgroups_to_groups(SolveFast.fgroups_build_fast(g, ws, Nil{})))
         : Nat} =
    Equal.sym(Nat,
      List.length(&2, Groups.Group,
        FN.FN.fgroups_to_groups(SolveFast.fgroups_build_fast(g, ws, Nil{}))),
      FH.FH.fgroups_count(SolveFast.fgroups_build_fast(g, ws, Nil{})),
      CS.len_fgroups_to_groups(SolveFast.fgroups_build_fast(g, ws, Nil{})))
  Equal.trans(Nat, CK.CK.count(g, ws),
    List.length(&2, Groups.Group,
      FN.FN.fgroups_to_groups(SolveFast.fgroups_build_fast(g, ws, Nil{}))),
    List.length(&2, Groups.Group, Groups.groups_build(g, ws, Nil{})), e1, e2)


# ---------------------------------------------------------------------------
# Feedback equality as an equivalence on codes
# ---------------------------------------------------------------------------

def CS.fe_of_eq(+a: +List<Feedback.Color>, +b: +List<Feedback.Color>,
    e: {a == b : +List<Feedback.Color>}) ->
  {Feedback.feedback_eq(a, b) == True{} : Bool}:
  Equal.trans(Bool, Feedback.feedback_eq(a, b), Feedback.feedback_eq(b, b),
    True{},
    Equal.cong(+List<Feedback.Color>, Bool,
      x => Feedback.feedback_eq(x, b), a, b, e),
    FbProof.FbPrf.feedback_eq_refl(b))

def CS.fe_trans(+c: +List<Feedback.Color>, +a: +List<Feedback.Color>,
    +b: +List<Feedback.Color>,
    +h1: {Feedback.feedback_eq(c, a) == True{} : Bool},
    +h2: {Feedback.feedback_eq(a, b) == True{} : Bool}) ->
  {Feedback.feedback_eq(c, b) == True{} : Bool}:
  CS.fe_of_eq(c, b,
    Equal.trans(+List<Feedback.Color>, c, a, b,
      FbProof.FbPrf.feedback_eq_true(c, a, h1),
      FbProof.FbPrf.feedback_eq_true(a, b, h2)))

# `or` with a true left side is true, from the equality.
def CS.or_l_mono(+a: Bool, +b: Bool, +h: {a == True{} : Bool}) ->
  {Bool.or(a, b) == True{} : Bool}:
  Equal.trans(Bool, Bool.or(a, b), Bool.or(True{}, b), True{},
    Equal.cong(Bool, Bool, x => Bool.or(x, b), a, True{}, h),
    CS.or_true_l(b))

# A code that is already at the head of the seen list adds nothing.
def CS.or_dup_l(a: Bool, b: Bool, m: Bool,
    +k: {CS.imp(a, b) == True{} : Bool}) ->
  {Bool.or(a, Bool.or(b, m)) == Bool.or(b, m) : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          Empty.absurd({True{} == m : Bool}, Logic.Proof.false_ne_true(k))
    case False{}:
      {==}

# The union with a redundant member absorbs into the smaller set.
def CS.or_absorb(a: Bool, z: Bool) ->
  {Bool.or(Bool.not(z), Bool.or(a, z)) == True{} : Bool}:
  match a:
    case True{}:
      match z:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      CS.or_not_self(z)

# An implication from an equality of the two sides.
def CS.imp_of_eq(+l: Bool, +r: Bool, e: {l == r : Bool}) ->
  {CS.imp(l, r) == True{} : Bool}:
  Equal.trans(Bool, CS.imp(l, r), CS.imp(r, r), True{},
    Equal.cong(Bool, Bool, y => CS.imp(y, r), l, r, e),
    CS.or_not_self(r))

# One code equality implies another, as a boolean implication.
def CS.fe_imp_of(+x: +List<Feedback.Color>, +c: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, q: Bool,
    +eq: {q == Feedback.feedback_eq(x, c) : Bool},
    +hcf: {Feedback.feedback_eq(c, f) == True{} : Bool}) ->
  {CS.imp(q, Feedback.feedback_eq(x, f)) == True{} : Bool}:
  match q:
    case True{}:
      CS.fe_trans(x, c, f, Equal.sym(Bool, True{}, Feedback.feedback_eq(x, c), eq),
        hcf)
    case False{}:
      {==}

# ---------------------------------------------------------------------------
# The codes of the group list
# ---------------------------------------------------------------------------

# The codes a group list holds, in order.
def CS.gcodes(+acc: +List<Groups.Group>) -> +List<+List<Feedback.Color>>:
  match acc:
    case Nil{}:
      Nil{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          fb <> CS.gcodes(rest)

# At most one new code per added word.
def CS.one_if_not(hit: Bool) -> Nat:
  Feedback.Bool.case(Nat, hit, 0n, 1n)

# A code already at the head of the seen list does not change the count.
def CS.sub_head_dup_widen(+cs: +List<+List<Feedback.Color>>,
    +c: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +seen: +List<+List<Feedback.Color>>) ->
  {CS.sub(cs, f <> seen, c <> (f <> seen)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{hc, t}:
      Logic.Proof.and_intro(
        CS.imp(CS.mem(hc, f <> seen), CS.mem(hc, c <> (f <> seen))),
        CS.sub(t, f <> seen, c <> (f <> seen)),
        CS.or_absorb(Feedback.feedback_eq(hc, c),
          Bool.or(Feedback.feedback_eq(hc, f), CS.mem(hc, seen))),
        CS.sub_head_dup_widen(t, c, f, seen))

def CS.sub_head_dup_narrow(+cs: +List<+List<Feedback.Color>>,
    +c: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +seen: +List<+List<Feedback.Color>>,
    +hcf: {Feedback.feedback_eq(c, f) == True{} : Bool}) ->
  {CS.sub(cs, c <> (f <> seen), f <> seen) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{hc, t}:
      Logic.Proof.and_intro(
        CS.imp(CS.mem(hc, c <> (f <> seen)), CS.mem(hc, f <> seen)),
        CS.sub(t, c <> (f <> seen), f <> seen),
        CS.imp_of_eq(Bool.or(Feedback.feedback_eq(hc, c),
            Bool.or(Feedback.feedback_eq(hc, f), CS.mem(hc, seen))),
          Bool.or(Feedback.feedback_eq(hc, f), CS.mem(hc, seen)),
          CS.or_dup_l(Feedback.feedback_eq(hc, c), Feedback.feedback_eq(hc, f),
            CS.mem(hc, seen), CS.fe_imp_of(hc, c, f, Feedback.feedback_eq(hc, c), {==}, hcf))),
        CS.sub_head_dup_narrow(t, c, f, seen, hcf))

def CS.newc_head_dup(+cs: +List<+List<Feedback.Color>>,
    +c: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +seen: +List<+List<Feedback.Color>>,
    +hcf: {Feedback.feedback_eq(c, f) == True{} : Bool}) ->
  {CS.newc(cs, f <> seen) == CS.newc(cs, c <> (f <> seen)) : Nat}:
  Equal.sym(Nat, CS.newc(cs, c <> (f <> seen)), CS.newc(cs, f <> seen),
    CS.newc_same(cs, c <> (f <> seen), f <> seen,
      Logic.Proof.and_intro(CS.sub(cs, c <> (f <> seen), f <> seen),
        CS.sub(cs, f <> seen, c <> (f <> seen)),
        CS.sub_head_dup_narrow(cs, c, f, seen, hcf),
        CS.sub_head_dup_widen(cs, c, f, seen))))

# A code-list inclusion is reflexive.
def CS.sub_self(+cs: +List<+List<Feedback.Color>>,
    +a: +List<+List<Feedback.Color>>) ->
  {CS.sub(cs, a, a) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{hc, t}:
      Logic.Proof.and_intro(CS.imp(CS.mem(hc, a), CS.mem(hc, a)),
        CS.sub(t, a, a), CS.or_not_self(CS.mem(hc, a)), CS.sub_self(t, a))

def CS.same_self(+cs: +List<+List<Feedback.Color>>,
    +a: +List<+List<Feedback.Color>>) ->
  {CS.same(cs, a, a) == True{} : Bool}:
  Logic.Proof.and_intro(CS.sub(cs, a, a), CS.sub(cs, a, a),
    CS.sub_self(cs, a), CS.sub_self(cs, a))

# Implication is transitive.
def CS.imp_trans(a: Bool, b: Bool, c: Bool,
    +k1: {CS.imp(a, b) == True{} : Bool},
    +k2: {CS.imp(b, c) == True{} : Bool}) ->
  {CS.imp(a, c) == True{} : Bool}:
  match a b c:
    case False{} _ _:
      {==}
    case True{} True{} _:
      k2
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      k1

# A code-list inclusion is transitive.
def CS.sub_trans(+cs: +List<+List<Feedback.Color>>,
    +a: +List<+List<Feedback.Color>>, +b: +List<+List<Feedback.Color>>,
    +c: +List<+List<Feedback.Color>>,
    +k1: {CS.sub(cs, a, b) == True{} : Bool},
    +k2: {CS.sub(cs, b, c) == True{} : Bool}) ->
  {CS.sub(cs, a, c) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{hc, t}:
      Logic.Proof.and_intro(CS.imp(CS.mem(hc, a), CS.mem(hc, c)),
        CS.sub(t, a, c),
        CS.imp_trans(CS.mem(hc, a), CS.mem(hc, b), CS.mem(hc, c),
          CS.sub_head(hc, t, a, b, k1), CS.sub_head(hc, t, b, c, k2)),
        CS.sub_trans(t, a, b, c,
          CS.sub_tail(hc, t, a, b, k1), CS.sub_tail(hc, t, b, c, k2)))

# Agreement is transitive.
def CS.same_trans(+cs: +List<+List<Feedback.Color>>,
    +a: +List<+List<Feedback.Color>>, +b: +List<+List<Feedback.Color>>,
    +c: +List<+List<Feedback.Color>>,
    +k1: {CS.same(cs, a, b) == True{} : Bool},
    +k2: {CS.same(cs, b, c) == True{} : Bool}) ->
  {CS.same(cs, a, c) == True{} : Bool}:
  Logic.Proof.and_intro(CS.sub(cs, a, c), CS.sub(cs, c, a),
    CS.sub_trans(cs, a, b, c,
      CS.same_sub1(cs, a, b, k1), CS.same_sub1(cs, b, c, k2)),
    CS.sub_trans(cs, c, b, a,
      CS.same_sub2(cs, b, c, k2), CS.same_sub2(cs, a, b, k1)))

# A code already at the head of the seen list agrees before and after.
def CS.same_head_dup(+cs: +List<+List<Feedback.Color>>,
    +c: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +seen: +List<+List<Feedback.Color>>,
    +hcf: {Feedback.feedback_eq(c, f) == True{} : Bool}) ->
  {CS.same(cs, f <> seen, c <> (f <> seen)) == True{} : Bool}:
  Logic.Proof.and_intro(CS.sub(cs, f <> seen, c <> (f <> seen)),
    CS.sub(cs, c <> (f <> seen), f <> seen),
    CS.sub_head_dup_widen(cs, c, f, seen),
    CS.sub_head_dup_narrow(cs, c, f, seen, hcf))

# The seen codes of `group_add` agree with the new code consed on.
def CS.gcodes_add_go(+cs: +List<+List<Feedback.Color>>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +rest: +List<Groups.Group>, q: Bool,
    +eq: {q == Feedback.feedback_eq(fb, f) : Bool},
    +k: {CS.same(cs, CS.gcodes(Groups.group_add(w, fb, rest)),
                 fb <> CS.gcodes(rest)) == True{} : Bool}) ->
  {CS.same(cs,
     CS.gcodes(Feedback.Bool.case(+List<Groups.Group>, q,
       Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])} <> rest,
       Groups.Group{f, ws} <> Groups.group_add(w, fb, rest))),
     fb <> CS.gcodes(Groups.Group{f, ws} <> rest)) == True{} : Bool}:
  match q:
    case True{}:
      CS.same_head_dup(cs, fb, f, CS.gcodes(rest),
        Equal.sym(Bool, True{}, Feedback.feedback_eq(fb, f), eq))
    case False{}:
      CS.same_trans(cs,
        CS.gcodes(Groups.Group{f, ws} <> Groups.group_add(w, fb, rest)),
        f <> (fb <> CS.gcodes(rest)),
        fb <> CS.gcodes(Groups.Group{f, ws} <> rest),
        CS.same_cons(cs, CS.gcodes(Groups.group_add(w, fb, rest)),
          fb <> CS.gcodes(rest), f, k),
        CS.same_swap(cs, CS.gcodes(rest), f, fb))

def CS.gcodes_add(+cs: +List<+List<Feedback.Color>>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +acc: +List<Groups.Group>) ->
  {CS.same(cs, CS.gcodes(Groups.group_add(w, fb, acc)),
           fb <> CS.gcodes(acc)) == True{} : Bool}:
  match acc:
    case Nil{}:
      CS.same_self(cs, fb <> CS.gcodes(Nil{}))
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          CS.gcodes_add_go(cs, w, fb, f, ws, rest,
            Feedback.feedback_eq(fb, f), {==},
            CS.gcodes_add(cs, w, fb, rest))

def CS.newc_gcodes_add(+cs: +List<+List<Feedback.Color>>, +w: +List<Nat>,
    +fb: +List<Feedback.Color>, +acc: +List<Groups.Group>) ->
  {CS.newc(cs, CS.gcodes(Groups.group_add(w, fb, acc)))
   == CS.newc(cs, fb <> CS.gcodes(acc)) : Nat}:
  CS.newc_same(cs, CS.gcodes(Groups.group_add(w, fb, acc)),
    fb <> CS.gcodes(acc), CS.gcodes_add(cs, w, fb, acc))

# ---------------------------------------------------------------------------
# Adding one code to the seen list
# ---------------------------------------------------------------------------

# Implication of a disjunction on the left.
def CS.imp_or_l(a: Bool, b: Bool, c: Bool,
    +k1: {CS.imp(a, c) == True{} : Bool},
    +k2: {CS.imp(b, c) == True{} : Bool}) ->
  {CS.imp(Bool.or(a, b), c) == True{} : Bool}:
  match a:
    case True{}:
      k1
    case False{}:
      k2

def CS.mem_fe_go(+x: +List<Feedback.Color>, +d: +List<Feedback.Color>,
    +h: +List<Feedback.Color>, +t: +List<+List<Feedback.Color>>, q: Bool,
    +h1: {Feedback.feedback_eq(x, d) == True{} : Bool},
    +hq: {q == Feedback.feedback_eq(d, h) : Bool},
    +h2: {Bool.or(q, CS.mem(d, t)) == True{} : Bool},
    k: {CS.mem(d, t) == True{} : Bool} ->
       {CS.mem(x, t) == True{} : Bool}) ->
  {Bool.or(Feedback.feedback_eq(x, h), CS.mem(x, t)) == True{} : Bool}:
  match q:
    case True{}:
      CS.or_l_mono(Feedback.feedback_eq(x, h), CS.mem(x, t),
        CS.fe_trans(x, d, h, h1,
          Equal.sym(Bool, True{}, Feedback.feedback_eq(d, h), hq)))
    case False{}:
      CS.or_r_mono(Feedback.feedback_eq(x, h), CS.mem(x, t), k(h2))

# Membership is congruent in the code.
def CS.mem_fe(+x: +List<Feedback.Color>, +d: +List<Feedback.Color>,
    +cs: +List<+List<Feedback.Color>>,
    +h1: {Feedback.feedback_eq(x, d) == True{} : Bool},
    +h2: {CS.mem(d, cs) == True{} : Bool}) ->
  {CS.mem(x, cs) == True{} : Bool}:
  match cs:
    case Nil{}:
      Empty.absurd({CS.mem(x, Nil{}) == True{} : Bool},
        Logic.Proof.false_ne_true(h2))
    case Con{h, t}:
      CS.mem_fe_go(x, d, h, t, Feedback.feedback_eq(d, h), h1, {==}, h2,
        h => CS.mem_fe(x, d, t, h1, h))

def CS.mem_fe_imp(+x: +List<Feedback.Color>, +d: +List<Feedback.Color>,
    +cs: +List<+List<Feedback.Color>>, z: Bool,
    +eq: {z == Feedback.feedback_eq(x, d) : Bool},
    +h2: {CS.mem(d, cs) == True{} : Bool}) ->
  {CS.imp(z, CS.mem(x, cs)) == True{} : Bool}:
  match z:
    case True{}:
      CS.mem_fe(x, d, cs,
        Equal.sym(Bool, True{}, Feedback.feedback_eq(x, d), eq), h2)
    case False{}:
      {==}

# A code already in the seen list adds nothing to the count.
def CS.sub_present_l(+cs: +List<+List<Feedback.Color>>,
    +c: +List<Feedback.Color>, +seen: +List<+List<Feedback.Color>>,
    +hm: {CS.mem(c, seen) == True{} : Bool}) ->
  {CS.sub(cs, c <> seen, seen) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{hc, t}:
      Logic.Proof.and_intro(CS.imp(CS.mem(hc, c <> seen), CS.mem(hc, seen)),
        CS.sub(t, c <> seen, seen),
        CS.imp_or_l(Feedback.feedback_eq(hc, c), CS.mem(hc, seen),
          CS.mem(hc, seen),
          CS.mem_fe_imp(hc, c, seen, Feedback.feedback_eq(hc, c), {==}, hm),
          CS.or_not_self(CS.mem(hc, seen))),
        CS.sub_present_l(t, c, seen, hm))

def CS.sub_present_r(+cs: +List<+List<Feedback.Color>>,
    +c: +List<Feedback.Color>, +seen: +List<+List<Feedback.Color>>) ->
  {CS.sub(cs, seen, c <> seen) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{hc, t}:
      Logic.Proof.and_intro(CS.imp(CS.mem(hc, seen), CS.mem(hc, c <> seen)),
        CS.sub(t, seen, c <> seen),
        CS.or_absorb(Feedback.feedback_eq(hc, c), CS.mem(hc, seen)),
        CS.sub_present_r(t, c, seen))

def CS.newc_seen_mem(+cs: +List<+List<Feedback.Color>>,
    +c: +List<Feedback.Color>, +seen: +List<+List<Feedback.Color>>,
    +hm: {CS.mem(c, seen) == True{} : Bool}) ->
  {CS.newc(cs, c <> seen) == CS.newc(cs, seen) : Nat}:
  CS.newc_same(cs, c <> seen, seen,
    Logic.Proof.and_intro(CS.sub(cs, c <> seen, seen),
      CS.sub(cs, seen, c <> seen),
      CS.sub_present_l(cs, c, seen, hm), CS.sub_present_r(cs, c, seen)))

# ---------------------------------------------------------------------------
# The accumulator length
# ---------------------------------------------------------------------------

# One step of the accumulator length with the feedback test as a parameter.
def CS.len_group_add_go(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +rest: +List<Groups.Group>, q: Bool,
    +ih: {List.length(&2, Groups.Group,
             Groups.group_add(w, fb, rest))
          == Nat.add(List.length(&2, Groups.Group, rest),
               CS.one_if_not(CS.mem(fb, CS.gcodes(rest)))) : Nat}) ->
  {List.length(&2, Groups.Group,
     Feedback.Bool.case(+List<Groups.Group>, q,
       Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])} <> rest,
       Groups.Group{f, ws} <> Groups.group_add(w, fb, rest)))
   == Nat.add(List.length(&2, Groups.Group, Groups.Group{f, ws} <> rest),
        CS.one_if_not(Bool.or(q, CS.mem(fb, CS.gcodes(rest))))) : Nat}:
  match q:
    case True{}:
      Equal.sym(Nat,
        Nat.add(Nat.add(1n, List.length(&2, Groups.Group, rest)), 0n),
        Nat.add(1n, List.length(&2, Groups.Group, rest)),
        NatProof.NatPrf.add_zero(
          Nat.add(1n, List.length(&2, Groups.Group, rest))))
    case False{}:
      +eih : {Nat.add(1n, List.length(&2, Groups.Group,
                 Groups.group_add(w, fb, rest)))
              == Nat.add(1n, Nat.add(List.length(&2, Groups.Group, rest),
                   CS.one_if_not(CS.mem(fb, CS.gcodes(rest))))) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(1n, x),
          List.length(&2, Groups.Group, Groups.group_add(w, fb, rest)),
          Nat.add(List.length(&2, Groups.Group, rest),
            CS.one_if_not(CS.mem(fb, CS.gcodes(rest)))), ih)
      Equal.trans(Nat, Nat.add(1n, List.length(&2, Groups.Group,
          Groups.group_add(w, fb, rest))),
        Nat.add(1n, Nat.add(List.length(&2, Groups.Group, rest),
          CS.one_if_not(CS.mem(fb, CS.gcodes(rest))))),
        Nat.add(Nat.add(1n, List.length(&2, Groups.Group, rest)),
          CS.one_if_not(CS.mem(fb, CS.gcodes(rest)))),
        eih,
        NatProof.NatPrf.add_assoc(1n, List.length(&2, Groups.Group, rest),
          CS.one_if_not(CS.mem(fb, CS.gcodes(rest)))))

# Adding a word raises the group count by at most one, and only with a new code.
def CS.len_group_add(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +acc: +List<Groups.Group>) ->
  {List.length(&2, Groups.Group, Groups.group_add(w, fb, acc))
   == Nat.add(List.length(&2, Groups.Group, acc),
        CS.one_if_not(CS.mem(fb, CS.gcodes(acc)))) : Nat}:
  match acc:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          CS.len_group_add_go(w, fb, f, ws, rest,
            Feedback.feedback_eq(fb, f), CS.len_group_add(w, fb, rest))

# ---------------------------------------------------------------------------
# The count of a class through its accumulator
# ---------------------------------------------------------------------------

# The arithmetic of one added word, with the membership test as a parameter.
def CS.build_arith(+len: Nat, +cs: +List<+List<Feedback.Color>>,
    +c: +List<Feedback.Color>, +seen: +List<+List<Feedback.Color>>,
    hit: Bool, +eh: {hit == CS.mem(c, seen) : Bool}) ->
  {Nat.add(Nat.add(len, CS.one_if_not(hit)), CS.newc(cs, c <> seen))
   == Nat.add(len, CS.newc_step(c, cs, seen, hit)) : Nat}:
  match hit:
    case True{}:
      +en : {CS.newc(cs, c <> seen) == CS.newc(cs, seen) : Nat} =
        CS.newc_seen_mem(cs, c, seen,
          Equal.sym(Bool, True{}, CS.mem(c, seen), eh))
      Equal.trans(Nat, Nat.add(Nat.add(len, 0n), CS.newc(cs, c <> seen)),
        Nat.add(len, CS.newc(cs, c <> seen)),
        Nat.add(len, CS.newc(cs, seen)),
        Equal.cong(Nat, Nat, x => Nat.add(x, CS.newc(cs, c <> seen)),
          Nat.add(len, 0n), len, NatProof.NatPrf.add_zero(len)),
        Equal.cong(Nat, Nat, x => Nat.add(len, x),
          CS.newc(cs, c <> seen), CS.newc(cs, seen), en))
    case False{}:
      NatProof.NatPrf.add_assoc(len, 1n, CS.newc(cs, c <> seen))

# One word of the class, with the word test and the membership test as
# parameters.
def CS.build_count_go(+g: +List<Nat>, +w: +List<Nat>,
    +t: +List<+List<Nat>>, +acc: +List<Groups.Group>, b: Bool, hit: Bool,
    +eh: {hit == CS.mem(Feedback.feedback(g, w), CS.gcodes(acc)) : Bool},
    +ih1: {List.length(&2, Groups.Group, Groups.groups_build(g, t, acc))
           == Nat.add(List.length(&2, Groups.Group, acc),
                CS.newc(CS.codes(g, t), CS.gcodes(acc))) : Nat},
    +ih2: {List.length(&2, Groups.Group,
             Groups.groups_build(g, t,
               Groups.group_add(w, Feedback.feedback(g, w), acc)))
           == Nat.add(List.length(&2, Groups.Group,
                Groups.group_add(w, Feedback.feedback(g, w), acc)),
                CS.newc(CS.codes(g, t),
                  CS.gcodes(Groups.group_add(w, Feedback.feedback(g, w),
                    acc)))) : Nat}) ->
  {List.length(&2, Groups.Group,
     Feedback.Bool.case(+List<Groups.Group>, b,
       Groups.groups_build(g, t, acc),
       Groups.groups_build(g, t,
         Groups.group_add(w, Feedback.feedback(g, w), acc))))
   == Nat.add(List.length(&2, Groups.Group, acc),
        CS.newc(Feedback.Bool.case(+List<+List<Feedback.Color>>, b,
          CS.codes(g, t),
          Feedback.feedback(g, w) <> CS.codes(g, t)), CS.gcodes(acc))) : Nat}:
  match b:
    case True{}:
      ih1
    case False{}:
      +hla : {List.length(&2, Groups.Group,
                Groups.group_add(w, Feedback.feedback(g, w), acc))
              == Nat.add(List.length(&2, Groups.Group, acc),
                   CS.one_if_not(hit)) : Nat} =
        Equal.trans(Nat, List.length(&2, Groups.Group,
            Groups.group_add(w, Feedback.feedback(g, w), acc)),
          Nat.add(List.length(&2, Groups.Group, acc),
            CS.one_if_not(CS.mem(Feedback.feedback(g, w), CS.gcodes(acc)))),
          Nat.add(List.length(&2, Groups.Group, acc), CS.one_if_not(hit)),
          CS.len_group_add(w, Feedback.feedback(g, w), acc),
          Equal.cong(Nat, Nat,
            x => Nat.add(List.length(&2, Groups.Group, acc), x),
            CS.one_if_not(CS.mem(Feedback.feedback(g, w), CS.gcodes(acc))),
            CS.one_if_not(hit),
            Equal.cong(Bool, Nat, CS.one_if_not,
              CS.mem(Feedback.feedback(g, w), CS.gcodes(acc)), hit,
              Equal.sym(Bool, hit,
                CS.mem(Feedback.feedback(g, w), CS.gcodes(acc)), eh))))
      +hnc : {CS.newc(CS.codes(g, t),
                CS.gcodes(Groups.group_add(w, Feedback.feedback(g, w), acc)))
              == CS.newc(CS.codes(g, t),
                   Feedback.feedback(g, w) <> CS.gcodes(acc)) : Nat} =
        CS.newc_gcodes_add(CS.codes(g, t), w, Feedback.feedback(g, w), acc)
      +e1 : {List.length(&2, Groups.Group,
               Groups.groups_build(g, t,
                 Groups.group_add(w, Feedback.feedback(g, w), acc)))
             == Nat.add(Nat.add(List.length(&2, Groups.Group, acc),
                  CS.one_if_not(hit)),
                  CS.newc(CS.codes(g, t),
                    Feedback.feedback(g, w) <> CS.gcodes(acc))) : Nat} =
        Equal.trans(Nat, List.length(&2, Groups.Group,
            Groups.groups_build(g, t,
              Groups.group_add(w, Feedback.feedback(g, w), acc))),
          Nat.add(List.length(&2, Groups.Group,
              Groups.group_add(w, Feedback.feedback(g, w), acc)),
            CS.newc(CS.codes(g, t),
              CS.gcodes(Groups.group_add(w, Feedback.feedback(g, w), acc)))),
          Nat.add(Nat.add(List.length(&2, Groups.Group, acc),
              CS.one_if_not(hit)),
            CS.newc(CS.codes(g, t),
              Feedback.feedback(g, w) <> CS.gcodes(acc))),
          ih2,
          Equal.trans(Nat,
            Nat.add(List.length(&2, Groups.Group,
                Groups.group_add(w, Feedback.feedback(g, w), acc)),
              CS.newc(CS.codes(g, t),
                CS.gcodes(Groups.group_add(w, Feedback.feedback(g, w), acc)))),
            Nat.add(Nat.add(List.length(&2, Groups.Group, acc),
                CS.one_if_not(hit)),
              CS.newc(CS.codes(g, t),
                CS.gcodes(Groups.group_add(w, Feedback.feedback(g, w), acc)))),
            Nat.add(Nat.add(List.length(&2, Groups.Group, acc),
                CS.one_if_not(hit)),
              CS.newc(CS.codes(g, t),
                Feedback.feedback(g, w) <> CS.gcodes(acc))),
            Equal.cong(Nat, Nat,
              x => Nat.add(x, CS.newc(CS.codes(g, t),
                     CS.gcodes(Groups.group_add(w, Feedback.feedback(g, w),
                       acc)))),
              List.length(&2, Groups.Group,
                Groups.group_add(w, Feedback.feedback(g, w), acc)),
              Nat.add(List.length(&2, Groups.Group, acc), CS.one_if_not(hit)),
              hla),
            Equal.cong(Nat, Nat,
              x => Nat.add(Nat.add(List.length(&2, Groups.Group, acc),
                     CS.one_if_not(hit)), x),
              CS.newc(CS.codes(g, t),
                CS.gcodes(Groups.group_add(w, Feedback.feedback(g, w), acc))),
              CS.newc(CS.codes(g, t),
                Feedback.feedback(g, w) <> CS.gcodes(acc)),
              hnc)))
      Equal.trans(Nat, List.length(&2, Groups.Group,
          Groups.groups_build(g, t,
            Groups.group_add(w, Feedback.feedback(g, w), acc))),
        Nat.add(Nat.add(List.length(&2, Groups.Group, acc),
            CS.one_if_not(hit)),
          CS.newc(CS.codes(g, t),
            Feedback.feedback(g, w) <> CS.gcodes(acc))),
        Nat.add(List.length(&2, Groups.Group, acc),
          CS.newc(Feedback.feedback(g, w) <> CS.codes(g, t), CS.gcodes(acc))),
        e1,
        Equal.trans(Nat,
          Nat.add(Nat.add(List.length(&2, Groups.Group, acc),
              CS.one_if_not(hit)),
            CS.newc(CS.codes(g, t),
              Feedback.feedback(g, w) <> CS.gcodes(acc))),
          Nat.add(List.length(&2, Groups.Group, acc),
            CS.newc_step(Feedback.feedback(g, w), CS.codes(g, t),
              CS.gcodes(acc), hit)),
          Nat.add(List.length(&2, Groups.Group, acc),
            CS.newc(Feedback.feedback(g, w) <> CS.codes(g, t), CS.gcodes(acc))),
          CS.build_arith(List.length(&2, Groups.Group, acc), CS.codes(g, t),
            Feedback.feedback(g, w), CS.gcodes(acc), hit, eh),
          Equal.cong(Nat, Nat,
            x => Nat.add(List.length(&2, Groups.Group, acc), x),
            CS.newc_step(Feedback.feedback(g, w), CS.codes(g, t),
              CS.gcodes(acc), hit),
            CS.newc(Feedback.feedback(g, w) <> CS.codes(g, t), CS.gcodes(acc)),
            Equal.trans(Nat,
              CS.newc_step(Feedback.feedback(g, w), CS.codes(g, t),
                CS.gcodes(acc), hit),
              CS.newc_step(Feedback.feedback(g, w), CS.codes(g, t),
                CS.gcodes(acc), CS.mem(Feedback.feedback(g, w), CS.gcodes(acc))),
              CS.newc(Feedback.feedback(g, w) <> CS.codes(g, t), CS.gcodes(acc)),
              Equal.cong(Bool, Nat,
                x => CS.newc_step(Feedback.feedback(g, w), CS.codes(g, t),
                  CS.gcodes(acc), x),
                hit, CS.mem(Feedback.feedback(g, w), CS.gcodes(acc)), eh),
              Equal.sym(Nat,
                CS.newc(Feedback.feedback(g, w) <> CS.codes(g, t),
                  CS.gcodes(acc)),
                CS.newc_step(Feedback.feedback(g, w), CS.codes(g, t),
                  CS.gcodes(acc),
                  CS.mem(Feedback.feedback(g, w), CS.gcodes(acc))),
                CS.newc_unfold(Feedback.feedback(g, w), CS.codes(g, t),
                  CS.gcodes(acc)))))))

# The group count of a class is the accumulated count plus the new codes.
def CS.build_count(+g: +List<Nat>, +ws: +List<+List<Nat>>,
    +acc: +List<Groups.Group>) ->
  {List.length(&2, Groups.Group, Groups.groups_build(g, ws, acc))
   == Nat.add(List.length(&2, Groups.Group, acc),
        CS.newc(CS.codes(g, ws), CS.gcodes(acc))) : Nat}:
  match ws:
    case Nil{}:
      Equal.sym(Nat, Nat.add(List.length(&2, Groups.Group, acc), 0n),
        List.length(&2, Groups.Group, acc),
        NatProof.NatPrf.add_zero(List.length(&2, Groups.Group, acc)))
    case Con{w, t}:
      CS.build_count_go(g, w, t, acc, Feedback.word_eq(g, w),
        CS.mem(Feedback.feedback(g, w), CS.gcodes(acc)), {==},
        CS.build_count(g, t, acc),
        CS.build_count(g, t,
          Groups.group_add(w, Feedback.feedback(g, w), acc)))
