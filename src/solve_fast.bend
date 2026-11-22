# The bound-pruned solver.
#
# This module is a drop-in replacement for the reference search in
# `src/solve_ref.bend`: `solve_fast` returns the same tree as `solve`, but it
# skips any guess or class whose lower bound cannot strictly beat the best
# cost found so far.
#
# For a guess `g` over a candidate list `S`, the reference builds one child per
# class of the feedback partition and the node costs one per candidate plus the
# children's costs. In any valid subtree for a class `ws`, only the subtree's
# root guess can end at depth one, so `cost(T, ws) >= 2 * |ws| - max_mult(ws)`
# (`proofs/lb_twice.bend`). When the root candidate list has no duplicates
# (checked once at the root by `no_dup_fast`), every feedback class is a
# subsequence of its parent (`proofs/cover_groups.bend`) and also has no
# duplicates, so `max_mult(ws) = 1`, `class_lb(ws) = 2 * |ws| - 1` in O(1),
# and every tree over `S` costs at least `2 * |S| - 1` — allowing immediate
# early exit from the node's guess loop once `best_cost(best) <= 2 * |S| - 1`.
#
# Feedback classes are accumulated in `FGroup{fb, len, rwords}` with O(1)
# prepend and cached length; usability and the depth-two lower bound are
# checked in tail-recursive passes before reversing any class or building
# schedule items. Each live `ClassItem` passes the tight remaining budget
# `best_cost(best) - (sum + tail_lb)` into its recursive child search, and
# `OneItem` resolves singleton classes directly in O(1) once the root confirms
# every candidate belongs to `G`.
import Base
import ./feedback.bend as Feedback
import ./tree.bend as Tree
import ./groups.bend as Groups
import ./solve_ref.bend as SolveRef

# `Begin` starts a usable guess that passed the initial lower-bound test.
# `ClassItem` carries the class words, their cached length `wlen`, and
# `tail_lb` (the lower bound of the remaining classes plus `|S|`) so each
# recursive child search runs with tight upper-bound cutoff
# `best_cost(best) - (sum + tail_lb)`. `Add` consumes the child and switches
# to `skip = True{}` as soon as `sum2 + tail_lb >= best_cost(best)`. `OneItem`
# resolves a singleton feedback class `[w]` directly in O(1).
type Item is Data:
  Begin{guess: +List<Nat>}
  ClassItem{fb: +List<Feedback.Color>, words: +List<+List<Nat>>, wlen: Nat, tail_lb: Nat}
  OneItem{fb: +List<Feedback.Color>, word: +List<Nat>}
  Add{fb: +List<Feedback.Color>, tail_lb: Nat}
  End{}

# A feedback class accumulated in reverse candidate order with its cached size.
type FGroup is Data:
  FGroup{fb: +List<Feedback.Color>, len: Nat, rwords: +List<+List<Nat>>}

# Single-pass word and feedback equality. `Feedback.word_eq` and
# `Feedback.feedback_eq` compute both list lengths and allocate a zipped pair
# list before comparing elements. Walking both lists in lockstep with a `Bool`
# head-equality parameter returns the same boolean (`proofs/fast_groups.bend`)
# without allocating and stops at the first mismatch.
def word_eq_go(+a: +List<Nat>, +b: +List<Nat>, same: Bool) -> Bool:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          True{}
        case Con{bh, bt}:
          False{}
    case Con{ah, at}:
      match b:
        case Nil{}:
          False{}
        case Con{bh, bt}:
          match same:
            case True{}:
              word_eq_go(at, bt, Feedback.next_same(at, bt))
            case False{}:
              False{}

def word_eq_fast(+a: +List<Nat>, +b: +List<Nat>) -> Bool:
  word_eq_go(a, b, Feedback.next_same(a, b))

# Linear membership, subset, and duplicate-free checks: tail-recursive loops
# that stop at the first match / missing candidate / repeated candidate.
def next_word_hit(+w: +List<Nat>, +gs: +List<+List<Nat>>) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case Con{h, t}:
      word_eq_fast(w, h)

def member_word_go(+w: +List<Nat>, +gs: +List<+List<Nat>>,
                   hit: Bool) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case Con{h, t}:
      match hit:
        case True{}:
          True{}
        case False{}:
          member_word_go(w, t, next_word_hit(w, t))

def member_word_fast(+w: +List<Nat>, +gs: +List<+List<Nat>>) -> Bool:
  member_word_go(w, gs, next_word_hit(w, gs))

def next_in(+S: +List<+List<Nat>>, +G: +List<+List<Nat>>) -> Bool:
  match S:
    case Nil{}:
      True{}
    case Con{w, t}:
      member_word_fast(w, G)

def all_in_go(+S: +List<+List<Nat>>, +G: +List<+List<Nat>>,
              ok: Bool) -> Bool:
  match S:
    case Nil{}:
      True{}
    case Con{w, t}:
      match ok:
        case True{}:
          all_in_go(t, G, next_in(t, G))
        case False{}:
          False{}

def all_in_fast(+S: +List<+List<Nat>>, +G: +List<+List<Nat>>) -> Bool:
  all_in_go(S, G, next_in(S, G))

def next_dup(+S: +List<+List<Nat>>) -> Bool:
  match S:
    case Nil{}:
      False{}
    case Con{w, t}:
      member_word_fast(w, t)

def no_dup_go(+S: +List<+List<Nat>>, dup: Bool) -> Bool:
  match S:
    case Nil{}:
      True{}
    case Con{w, t}:
      match dup:
        case True{}:
          False{}
        case False{}:
          no_dup_go(t, next_dup(t))

def no_dup_fast(+S: +List<+List<Nat>>) -> Bool:
  no_dup_go(S, next_dup(S))

def next_fb_same(+a: +List<Feedback.Color>,
                 +b: +List<Feedback.Color>) -> Bool:
  match a:
    case Nil{}:
      False{}
    case Con{ah, at}:
      match b:
        case Nil{}:
          False{}
        case Con{bh, bt}:
          Feedback.Color.eq(ah, bh)

def feedback_eq_go(+a: +List<Feedback.Color>,
                   +b: +List<Feedback.Color>, same: Bool) -> Bool:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          True{}
        case Con{bh, bt}:
          False{}
    case Con{ah, at}:
      match b:
        case Nil{}:
          False{}
        case Con{bh, bt}:
          match same:
            case True{}:
              feedback_eq_go(at, bt, next_fb_same(at, bt))
            case False{}:
              False{}

def feedback_eq_fast(+a: +List<Feedback.Color>,
                     +b: +List<Feedback.Color>) -> Bool:
  feedback_eq_go(a, b, next_fb_same(a, b))

# One when the candidate equals the guess, zero otherwise.
def hit_bool(b: Bool) -> Nat:
  Feedback.Bool.case(Nat, b, 1n, 0n)

def hit_word(+g: +List<Nat>, +w: +List<Nat>) -> Nat:
  hit_bool(word_eq_fast(g, w))

# The number of candidates in `S` not equal to `g`, and the pre-grouping
# lower bound `|S| + keep_fast(g, S) = 2 * |S| - word_mult(g, S)`.
def keep_step(+rest: Nat, same: Bool) -> Nat:
  match same:
    case True{}:
      rest
    case False{}:
      Nat.add(1n, rest)

def keep_fast(+g: +List<Nat>, +S: +List<+List<Nat>>) -> Nat:
  match S:
    case Nil{}:
      0n
    case Con{+w, +t}:
      keep_step(keep_fast(g, t), word_eq_fast(g, w))

def pre_lb(+n: Nat, +g: +List<Nat>, +S: +List<+List<Nat>>) -> Nat:
  Nat.add(n, keep_fast(g, S))

# The number of candidates in `S` equal to `g`, duplicates counted.
def word_mult(+g: +List<Nat>, +S: +List<+List<Nat>>) -> Nat:
  match S:
    case Nil{}:
      0n
    case Con{+h, +t}:
      Nat.add(hit_word(g, h), word_mult(g, t))

# The largest multiplicity of any candidate in `S`. Each head `h` contributes
# `1 + word_mult(h, t)` without comparing `h` with itself.
def max_mult(+S: +List<+List<Nat>>) -> Nat:
  match S:
    case Nil{}:
      0n
    case Con{+h, +t}:
      Nat.max(Nat.add(1n, word_mult(h, t)), max_mult(t))

# The depth-two lower bound on the cost of any valid tree for a class `ws`:
# `2 * |ws| - max_mult(ws)` (`proofs/lb_twice.bend`).
def class_lb(+ws: +List<+List<Nat>>) -> Nat:
  +m = Groups.len_words(ws)
  Nat.sub(Nat.add(m, m), max_mult(ws))

# In duplicate-free mode, `max_mult(ws) = 1` for every non-empty class (and
# `2*0 - 1 = 0 = class_lb(Nil{})`), so `class_lb_fast` runs in O(1) using the
# cached length `len`.
def class_lb_fast(+nodup: Bool, +len: Nat, +ws: +List<+List<Nat>>) -> Nat:
  match nodup:
    case True{}:
      Nat.sub(Nat.add(len, len), 1n)
    case False{}:
      class_lb(ws)

# The sum of class lower bounds over a class list.
def class_words(+groups: +List<Groups.Group>) -> Nat:
  match groups:
    case Nil{}:
      0n
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          Nat.add(class_lb(ws), class_words(rest))

# A lower bound on the cost of any tree rooted at a guess with these classes:
# the node costs one per candidate and each class costs at least `class_lb`.
def lower_bound(+n: Nat, +groups: +List<Groups.Group>) -> Nat:
  match groups:
    case Nil{}:
      n
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          Nat.add(class_lb(ws), lower_bound(n, rest))

def best_cost(+best: SolveRef.Best) -> Nat:
  match best:
    case SolveRef.Best{tree, cost}:
      cost

# The guess is skipped exactly when the best cost so far is at most its bound.
def skippable(+best: SolveRef.Best, +lb: Nat) -> Bool:
  Nat.is_le(best_cost(best), lb)

# When candidates are duplicate-free, every valid tree over `n` candidates
# costs at least `2*n - 1` (`0` when `n = 0`), so reaching `best_cost <= 2*n - 1`
# ends the node's guess loop immediately.
def is_floor_hit(+nodup: Bool, +n: Nat, +best: SolveRef.Best) -> Bool:
  match nodup:
    case True{}:
      skippable(best, Nat.sub(Nat.add(n, n), 1n))
    case False{}:
      False{}

def dummy_inf(+inf: Nat) -> SolveRef.Best:
  SolveRef.Best{Tree.Node{Nil{}, Nil{}}, inf}

def dummy_zero() -> SolveRef.Best:
  SolveRef.Best{Tree.Node{Nil{}, Nil{}}, 0n}

# Tail-recursive list reversal for restoring input order on unpruned classes.
def rev_words(+xs: +List<+List<Nat>>,
              +acc: +List<+List<Nat>>) -> +List<+List<Nat>>:
  match xs:
    case Nil{}:
      acc
    case Con{w, t}:
      rev_words(t, w <> acc)

# Reversal paired with length for single-pass draining of bucketed classes.
type RevLen is Data:
  RevLen{len: Nat, words: +List<+List<Nat>>}

def rev_words_len(+xs: +List<+List<Nat>>, +acc: +List<+List<Nat>>,
                  +len: Nat) -> RevLen:
  match xs:
    case Nil{}:
      RevLen{len, acc}
    case Con{w, t}:
      rev_words_len(t, w <> acc, Nat.add(1n, len))

# 2-bit-per-color encoding of 5-letter feedbacks in a 10-bit `U32` (`0..1023`):
# `Gray = 0`, `Yellow = 1`, `Green = 2` at bit offsets `0, 2, 4, 6, 8`.
# All-green is `2 + 8 + 32 + 128 + 512 = 682`.
def col_u32(c: Feedback.Color, +y: U32, +g: U32) -> U32:
  match c:
    case Feedback.Gray{}:
      0
    case Feedback.Yellow{}:
      y
    case Feedback.Green{}:
      g

def encode_fb5(c0: Feedback.Color, c1: Feedback.Color, c2: Feedback.Color,
               c3: Feedback.Color, c4: Feedback.Color) -> U32:
  U32.or(col_u32(c0, 1, 2),
    U32.or(col_u32(c1, 4, 8),
      U32.or(col_u32(c2, 16, 32),
        U32.or(col_u32(c3, 64, 128), col_u32(c4, 256, 512)))))

def decode_slot_y(is_y: Bool) -> Feedback.Color:
  match is_y:
    case True{}:
      Feedback.Yellow{}
    case False{}:
      Feedback.Gray{}

def decode_slot_g(is_g: Bool, +code: U32, +ymask: U32) -> Feedback.Color:
  match is_g:
    case True{}:
      Feedback.Green{}
    case False{}:
      decode_slot_y(U32.is_eq(U32.and(code, ymask), ymask))

def decode_slot(+code: U32, +gmask: U32, +ymask: U32) -> Feedback.Color:
  decode_slot_g(U32.is_eq(U32.and(code, gmask), gmask), code, ymask)

def decode_fb5(+code: U32) -> +List<Feedback.Color>:
  decode_slot(code, 2, 1)
  <> (decode_slot(code, 8, 4)
  <> (decode_slot(code, 32, 16)
  <> (decode_slot(code, 128, 64)
  <> (decode_slot(code, 512, 256) <> Nil{}))))

# Zero-allocation 5-letter feedback returning the 10-bit `U32` code directly.
# Non-green answer letters live in five `Nat` registers (`0n` = green/consumed,
# `1n + a` = available letter `a`).
def ng_slot(+a: Nat, same: Bool) -> Nat:
  match same:
    case True{}:
      0n
    case False{}:
      Nat.add(1n, a)

def fb5_s4_c4(eq: Bool, +acc: U32) -> U32:
  match eq:
    case True{}:
      U32.or(acc, 256)
    case False{}:
      acc

def fb5_s4_c3(eq: Bool, +acc: U32, +k: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      U32.or(acc, 256)
    case False{}:
      fb5_s4_c4(Nat.is_eq(k, p4), acc)

def fb5_s4_c2(eq: Bool, +acc: U32, +k: Nat, +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      U32.or(acc, 256)
    case False{}:
      fb5_s4_c3(Nat.is_eq(k, p3), acc, k, p4)

def fb5_s4_c1(eq: Bool, +acc: U32, +k: Nat, +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      U32.or(acc, 256)
    case False{}:
      fb5_s4_c2(Nat.is_eq(k, p2), acc, k, p3, p4)

def fb5_s4_c0(eq: Bool, +acc: U32, +k: Nat, +p1: Nat, +p2: Nat, +p3: Nat,
              +p4: Nat) -> U32:
  match eq:
    case True{}:
      U32.or(acc, 256)
    case False{}:
      fb5_s4_c1(Nat.is_eq(k, p1), acc, k, p2, p3, p4)

def fb5_s4(+acc: U32, +g4: Nat, e4: Bool,
           +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match e4:
    case True{}:
      U32.or(acc, 512)
    case False{}:
      +k = Nat.add(1n, g4)
      fb5_s4_c0(Nat.is_eq(k, p0), acc, k, p1, p2, p3, p4)

def fb5_s3_c4(eq: Bool, +acc: U32, +g4: Nat, +e4: Bool,
              +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s4(U32.or(acc, 64), g4, e4, p0, p1, p2, p3, 0n)
    case False{}:
      fb5_s4(acc, g4, e4, p0, p1, p2, p3, p4)

def fb5_s3_c3(eq: Bool, +acc: U32, +k: Nat, +g4: Nat, +e4: Bool,
              +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s4(U32.or(acc, 64), g4, e4, p0, p1, p2, 0n, p4)
    case False{}:
      fb5_s3_c4(Nat.is_eq(k, p4), acc, g4, e4, p0, p1, p2, p3, p4)

def fb5_s3_c2(eq: Bool, +acc: U32, +k: Nat, +g4: Nat, +e4: Bool,
              +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s4(U32.or(acc, 64), g4, e4, p0, p1, 0n, p3, p4)
    case False{}:
      fb5_s3_c3(Nat.is_eq(k, p3), acc, k, g4, e4, p0, p1, p2, p3, p4)

def fb5_s3_c1(eq: Bool, +acc: U32, +k: Nat, +g4: Nat, +e4: Bool,
              +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s4(U32.or(acc, 64), g4, e4, p0, 0n, p2, p3, p4)
    case False{}:
      fb5_s3_c2(Nat.is_eq(k, p2), acc, k, g4, e4, p0, p1, p2, p3, p4)

def fb5_s3_c0(eq: Bool, +acc: U32, +k: Nat, +g4: Nat, +e4: Bool,
              +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s4(U32.or(acc, 64), g4, e4, 0n, p1, p2, p3, p4)
    case False{}:
      fb5_s3_c1(Nat.is_eq(k, p1), acc, k, g4, e4, p0, p1, p2, p3, p4)

def fb5_s3(+acc: U32, +g3: Nat, e3: Bool, +g4: Nat, +e4: Bool,
           +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match e3:
    case True{}:
      fb5_s4(U32.or(acc, 128), g4, e4, p0, p1, p2, p3, p4)
    case False{}:
      +k = Nat.add(1n, g3)
      fb5_s3_c0(Nat.is_eq(k, p0), acc, k, g4, e4, p0, p1, p2, p3, p4)

def fb5_s2_c4(eq: Bool, +acc: U32, +g3: Nat, +e3: Bool, +g4: Nat, +e4: Bool,
              +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s3(U32.or(acc, 16), g3, e3, g4, e4, p0, p1, p2, p3, 0n)
    case False{}:
      fb5_s3(acc, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s2_c3(eq: Bool, +acc: U32, +k: Nat, +g3: Nat, +e3: Bool, +g4: Nat,
              +e4: Bool, +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s3(U32.or(acc, 16), g3, e3, g4, e4, p0, p1, p2, 0n, p4)
    case False{}:
      fb5_s2_c4(Nat.is_eq(k, p4), acc, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s2_c2(eq: Bool, +acc: U32, +k: Nat, +g3: Nat, +e3: Bool, +g4: Nat,
              +e4: Bool, +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s3(U32.or(acc, 16), g3, e3, g4, e4, p0, p1, 0n, p3, p4)
    case False{}:
      fb5_s2_c3(Nat.is_eq(k, p3), acc, k, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s2_c1(eq: Bool, +acc: U32, +k: Nat, +g3: Nat, +e3: Bool, +g4: Nat,
              +e4: Bool, +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s3(U32.or(acc, 16), g3, e3, g4, e4, p0, 0n, p2, p3, p4)
    case False{}:
      fb5_s2_c2(Nat.is_eq(k, p2), acc, k, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s2_c0(eq: Bool, +acc: U32, +k: Nat, +g3: Nat, +e3: Bool, +g4: Nat,
              +e4: Bool, +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s3(U32.or(acc, 16), g3, e3, g4, e4, 0n, p1, p2, p3, p4)
    case False{}:
      fb5_s2_c1(Nat.is_eq(k, p1), acc, k, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s2(+acc: U32, +g2: Nat, e2: Bool, +g3: Nat, +e3: Bool, +g4: Nat,
           +e4: Bool, +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match e2:
    case True{}:
      fb5_s3(U32.or(acc, 32), g3, e3, g4, e4, p0, p1, p2, p3, p4)
    case False{}:
      +k = Nat.add(1n, g2)
      fb5_s2_c0(Nat.is_eq(k, p0), acc, k, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s1_c4(eq: Bool, +acc: U32, +g2: Nat, +e2: Bool, +g3: Nat, +e3: Bool,
              +g4: Nat, +e4: Bool, +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat,
              +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s2(U32.or(acc, 4), g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, 0n)
    case False{}:
      fb5_s2(acc, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s1_c3(eq: Bool, +acc: U32, +k: Nat, +g2: Nat, +e2: Bool, +g3: Nat,
              +e3: Bool, +g4: Nat, +e4: Bool, +p0: Nat, +p1: Nat, +p2: Nat,
              +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s2(U32.or(acc, 4), g2, e2, g3, e3, g4, e4, p0, p1, p2, 0n, p4)
    case False{}:
      fb5_s1_c4(Nat.is_eq(k, p4), acc, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s1_c2(eq: Bool, +acc: U32, +k: Nat, +g2: Nat, +e2: Bool, +g3: Nat,
              +e3: Bool, +g4: Nat, +e4: Bool, +p0: Nat, +p1: Nat, +p2: Nat,
              +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s2(U32.or(acc, 4), g2, e2, g3, e3, g4, e4, p0, p1, 0n, p3, p4)
    case False{}:
      fb5_s1_c3(Nat.is_eq(k, p3), acc, k, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s1_c1(eq: Bool, +acc: U32, +k: Nat, +g2: Nat, +e2: Bool, +g3: Nat,
              +e3: Bool, +g4: Nat, +e4: Bool, +p0: Nat, +p1: Nat, +p2: Nat,
              +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s2(U32.or(acc, 4), g2, e2, g3, e3, g4, e4, p0, 0n, p2, p3, p4)
    case False{}:
      fb5_s1_c2(Nat.is_eq(k, p2), acc, k, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s1_c0(eq: Bool, +acc: U32, +k: Nat, +g2: Nat, +e2: Bool, +g3: Nat,
              +e3: Bool, +g4: Nat, +e4: Bool, +p0: Nat, +p1: Nat, +p2: Nat,
              +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s2(U32.or(acc, 4), g2, e2, g3, e3, g4, e4, 0n, p1, p2, p3, p4)
    case False{}:
      fb5_s1_c1(Nat.is_eq(k, p1), acc, k, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s1(+acc: U32, +g1: Nat, e1: Bool, +g2: Nat, +e2: Bool, +g3: Nat,
           +e3: Bool, +g4: Nat, +e4: Bool, +p0: Nat, +p1: Nat, +p2: Nat,
           +p3: Nat, +p4: Nat) -> U32:
  match e1:
    case True{}:
      fb5_s2(U32.or(acc, 8), g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)
    case False{}:
      +k = Nat.add(1n, g1)
      fb5_s1_c0(Nat.is_eq(k, p0), acc, k, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s0_c4(eq: Bool, +g1: Nat, +e1: Bool, +g2: Nat, +e2: Bool, +g3: Nat,
              +e3: Bool, +g4: Nat, +e4: Bool, +p0: Nat, +p1: Nat, +p2: Nat,
              +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s1(1, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, 0n)
    case False{}:
      fb5_s1(0, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s0_c3(eq: Bool, +k: Nat, +g1: Nat, +e1: Bool, +g2: Nat, +e2: Bool,
              +g3: Nat, +e3: Bool, +g4: Nat, +e4: Bool, +p0: Nat, +p1: Nat,
              +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s1(1, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, 0n, p4)
    case False{}:
      fb5_s0_c4(Nat.is_eq(k, p4), g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s0_c2(eq: Bool, +k: Nat, +g1: Nat, +e1: Bool, +g2: Nat, +e2: Bool,
              +g3: Nat, +e3: Bool, +g4: Nat, +e4: Bool, +p0: Nat, +p1: Nat,
              +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s1(1, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, 0n, p3, p4)
    case False{}:
      fb5_s0_c3(Nat.is_eq(k, p3), k, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s0_c1(eq: Bool, +k: Nat, +g1: Nat, +e1: Bool, +g2: Nat, +e2: Bool,
              +g3: Nat, +e3: Bool, +g4: Nat, +e4: Bool, +p0: Nat, +p1: Nat,
              +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s1(1, g1, e1, g2, e2, g3, e3, g4, e4, p0, 0n, p2, p3, p4)
    case False{}:
      fb5_s0_c2(Nat.is_eq(k, p2), k, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s0_c0(eq: Bool, +k: Nat, +g1: Nat, +e1: Bool, +g2: Nat, +e2: Bool,
              +g3: Nat, +e3: Bool, +g4: Nat, +e4: Bool, +p0: Nat, +p1: Nat,
              +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match eq:
    case True{}:
      fb5_s1(1, g1, e1, g2, e2, g3, e3, g4, e4, 0n, p1, p2, p3, p4)
    case False{}:
      fb5_s0_c1(Nat.is_eq(k, p1), k, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def fb5_s0(+g0: Nat, e0: Bool, +g1: Nat, +e1: Bool, +g2: Nat, +e2: Bool,
           +g3: Nat, +e3: Bool, +g4: Nat, +e4: Bool,
           +p0: Nat, +p1: Nat, +p2: Nat, +p3: Nat, +p4: Nat) -> U32:
  match e0:
    case True{}:
      fb5_s1(2, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)
    case False{}:
      +k = Nat.add(1n, g0)
      fb5_s0_c0(Nat.is_eq(k, p0), k, g1, e1, g2, e2, g3, e3, g4, e4, p0, p1, p2, p3, p4)

def feedback_code5(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
                   +a0: Nat, +a1: Nat, +a2: Nat, +a3: Nat, +a4: Nat) -> U32:
  +e0 = Nat.is_eq(g0, a0)
  +e1 = Nat.is_eq(g1, a1)
  +e2 = Nat.is_eq(g2, a2)
  +e3 = Nat.is_eq(g3, a3)
  +e4 = Nat.is_eq(g4, a4)
  fb5_s0(g0, e0, g1, e1, g2, e2, g3, e3, g4, e4,
         ng_slot(a0, e0), ng_slot(a1, e1), ng_slot(a2, e2),
         ng_slot(a3, e3), ng_slot(a4, e4))

# Specification of the class items of one guess: singleton classes `[w]`
# become `OneItem{f, w}`, and larger classes carry `wlen = |ws|` and
# `tail_lb = lower_bound(n, rest)` on `ClassItem` and `Add`.
def group_items(+n: Nat, +groups: +List<Groups.Group>) -> +List<Item>:
  match groups:
    case Nil{}:
      Nil{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+f, +ws}:
          match ws:
            case Nil{}:
              +tlb = lower_bound(n, rest)
              ClassItem{f, Nil{}, 0n, tlb} <> (Add{f, tlb} <> group_items(n, rest))
            case Con{+w, +wt}:
              match wt:
                case Nil{}:
                  OneItem{f, w} <> group_items(n, rest)
                case Con{+w2, +wt2}:
                  +ws2 : +List<+List<Nat>> = w <> (w2 <> wt2)
                  +tlb = lower_bound(n, rest)
                  ClassItem{f, ws2, Groups.len_words(ws2), tlb}
                  <> (Add{f, tlb} <> group_items(n, rest))

# Single-pass construction of a guess's lower bound and schedule items from
# `FGroup`s onto `tail`, reversing each multi-word class once and using O(1)
# `class_lb_fast` in duplicate-free mode.
type ItemsBound is Data:
  ItemsBound{lb: Nat, items: +List<Item>}

def group_items_step(+f: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
                     +wlen: Nat, +clb: Nat, ib: ItemsBound) -> ItemsBound:
  match ib:
    case ItemsBound{+rem_lb, +rest_items}:
      ItemsBound{Nat.add(clb, rem_lb),
        ClassItem{f, ws, wlen, rem_lb} <> (Add{f, rem_lb} <> rest_items)}

def group_items_one_step(+f: +List<Feedback.Color>, +w: +List<Nat>,
                         ib: ItemsBound) -> ItemsBound:
  match ib:
    case ItemsBound{+rem_lb, +rest_items}:
      ItemsBound{Nat.add(1n, rem_lb), OneItem{f, w} <> rest_items}

def fgroup_items_build(+nodup: Bool, +n: Nat, +fgroups: +List<FGroup>,
                       +tail: +List<Item>) -> ItemsBound:
  match fgroups:
    case Nil{}:
      ItemsBound{n, tail}
    case Con{gp, rest}:
      match gp:
        case FGroup{+f, +len, +rws}:
          match rws:
            case Nil{}:
              group_items_step(f, Nil{}, 0n, 0n,
                fgroup_items_build(nodup, n, rest, tail))
            case Con{+w, +wt}:
              match wt:
                case Nil{}:
                  group_items_one_step(f, w,
                    fgroup_items_build(nodup, n, rest, tail))
                case Con{+w2, +wt2}:
                  +ws : +List<+List<Nat>> = rev_words(wt2, w2 <> (w <> Nil{}))
                  group_items_step(f, ws, len, class_lb_fast(nodup, len, ws),
                    fgroup_items_build(nodup, n, rest, tail))

# Linear feedback and group partitioning. Matching on the `Bool` parameter
# makes one recursive call per step while returning the exact same feedbacks
# and partitions as `src/feedback.bend` and `src/groups.bend`.
def non_green_pick(+a: Nat, +rest: +List<Nat>, same: Bool) -> +List<Nat>:
  match same:
    case True{}:
      rest
    case False{}:
      a <> rest

def non_green_fast(+guess: +List<Nat>, +answer: +List<Nat>) -> +List<Nat>:
  match guess:
    case Nil{}:
      Nil{}
    case Con{+g, +t}:
      match answer:
        case Nil{}:
          Nil{}
        case Con{+a, +at}:
          non_green_pick(a, non_green_fast(t, at), Nat.is_eq(g, a))

def consume_color_fast(+x: Nat, +pool: +List<Nat>,
                       same: Bool) -> Feedback.Color:
  match pool:
    case Nil{}:
      Feedback.Gray{}
    case Con{+h, +t}:
      match same:
        case True{}:
          Feedback.Yellow{}
        case False{}:
          consume_color_fast(x, t, Feedback.next_letter_same(x, t))

def consume_pool_fast(+x: Nat, +pool: +List<Nat>, same: Bool) -> +List<Nat>:
  match pool:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      match same:
        case True{}:
          t
        case False{}:
          h <> consume_pool_fast(x, t, Feedback.next_letter_same(x, t))

def feedback_go_fast(+guess: +List<Nat>, +answer: +List<Nat>,
                     +pool: +List<Nat>, same: Bool) -> +List<Feedback.Color>:
  match guess:
    case Nil{}:
      Nil{}
    case Con{+g, +t}:
      match answer:
        case Nil{}:
          Feedback.Gray{} <> feedback_go_fast(t, Nil{}, Nil{}, False{})
        case Con{+a, +at}:
          match same:
            case True{}:
              Feedback.Green{}
              <> feedback_go_fast(t, at, pool, Feedback.next_same(t, at))
            case False{}:
              consume_color_fast(g, pool, Feedback.next_letter_same(g, pool))
              <> feedback_go_fast(t, at,
                   consume_pool_fast(g, pool,
                     Feedback.next_letter_same(g, pool)),
                   Feedback.next_same(t, at))

def feedback_fast(+guess: +List<Nat>,
                  +answer: +List<Nat>) -> +List<Feedback.Color>:
  feedback_go_fast(guess, answer, non_green_fast(guess, answer),
                   Feedback.next_same(guess, answer))

# O(1)-prepend feedback grouping with cached class sizes.
def next_fgroup_hit(+fb: +List<Feedback.Color>,
                    +fgroups: +List<FGroup>) -> Bool:
  match fgroups:
    case Nil{}:
      False{}
    case Con{gp, rest}:
      match gp:
        case FGroup{f, len, rws}:
          feedback_eq_fast(fb, f)

def fgroup_add_go(+w: +List<Nat>, +fb: +List<Feedback.Color>,
                  +fgroups: +List<FGroup>, hit: Bool) -> +List<FGroup>:
  match fgroups:
    case Nil{}:
      FGroup{fb, 1n, [w]} <> Nil{}
    case Con{gp, rest}:
      match gp:
        case FGroup{+f, +len, +rws}:
          match hit:
            case True{}:
              FGroup{f, Nat.add(1n, len), w <> rws} <> rest
            case False{}:
              FGroup{f, len, rws}
              <> fgroup_add_go(w, fb, rest, next_fgroup_hit(fb, rest))

def fgroup_add_fast(+w: +List<Nat>, +fb: +List<Feedback.Color>,
                    +fgroups: +List<FGroup>) -> +List<FGroup>:
  fgroup_add_go(w, fb, fgroups, next_fgroup_hit(fb, fgroups))

def fgroups_next_acc(+g: +List<Nat>, +w: +List<Nat>,
                     +acc: +List<FGroup>, same: Bool) -> +List<FGroup>:
  match same:
    case True{}:
      acc
    case False{}:
      fgroup_add_fast(w, feedback_fast(g, w), acc)

def fgroups_build_fast(+g: +List<Nat>, +S: +List<+List<Nat>>,
                       +acc: +List<FGroup>) -> +List<FGroup>:
  match S:
    case Nil{}:
      acc
    case Con{+w, +rest}:
      fgroups_build_fast(g, rest,
        fgroups_next_acc(g, w, acc, word_eq_fast(g, w)))

# Tail-recursive usability check using cached class lengths.
def next_fgroup_lt(+n: Nat, +fgroups: +List<FGroup>) -> Bool:
  match fgroups:
    case Nil{}:
      True{}
    case Con{gp, rest}:
      match gp:
        case FGroup{f, len, rws}:
          Nat.is_lt(len, n)

def fgroups_smaller_go(+n: Nat, +fgroups: +List<FGroup>, ok: Bool) -> Bool:
  match fgroups:
    case Nil{}:
      True{}
    case Con{gp, rest}:
      match ok:
        case True{}:
          fgroups_smaller_go(n, rest, next_fgroup_lt(n, rest))
        case False{}:
          False{}

def fgroups_smaller(+n: Nat, +fgroups: +List<FGroup>) -> Bool:
  fgroups_smaller_go(n, fgroups, next_fgroup_lt(n, fgroups))

# Tail-recursive depth-two lower bound over `FGroup`s before reversing or
# allocating schedule items.
def fgroups_lb_nodup(+fgroups: +List<FGroup>, +acc: Nat) -> Nat:
  match fgroups:
    case Nil{}:
      acc
    case Con{gp, rest}:
      match gp:
        case FGroup{f, +len, rws}:
          fgroups_lb_nodup(rest, Nat.add(acc, Nat.sub(Nat.add(len, len), 1n)))

def fgroups_lb_dup(+fgroups: +List<FGroup>, +acc: Nat) -> Nat:
  match fgroups:
    case Nil{}:
      acc
    case Con{gp, rest}:
      match gp:
        case FGroup{f, len, rws}:
          fgroups_lb_dup(rest, Nat.add(acc, class_lb(rev_words(rws, Nil{}))))

def fgroups_lb(+nodup: Bool, +n: Nat, +fgroups: +List<FGroup>) -> Nat:
  match nodup:
    case True{}:
      fgroups_lb_nodup(fgroups, n)
    case False{}:
      fgroups_lb_dup(fgroups, n)

# Schedule one guess: skip before reversing or allocating items whenever the
# guess is unusable or its depth-two lower bound cannot beat `best`.
def schedule_guess_ib(+g: +List<Nat>, ib: ItemsBound) -> +List<Item>:
  match ib:
    case ItemsBound{lb, +items}:
      Begin{g} <> items

def schedule_fguess_lb(+nodup: Bool, +g: +List<Nat>, +fgroups: +List<FGroup>,
                       +n: Nat, skip: Bool) -> +List<Item>:
  match skip:
    case True{}:
      Nil{}
    case False{}:
      schedule_guess_ib(g, fgroup_items_build(nodup, n, fgroups, End{} <> Nil{}))

def schedule_fguess(+nodup: Bool, +g: +List<Nat>, +fgroups: +List<FGroup>,
                    +n: Nat, +best: SolveRef.Best, usable: Bool) -> +List<Item>:
  match usable:
    case False{}:
      Nil{}
    case True{}:
      schedule_fguess_lb(nodup, g, fgroups, n,
        skippable(best, fgroups_lb(nodup, n, fgroups)))

# Fast schedule for a singleton candidate list `[w]`: a guess `g` is usable
# exactly when `g == w` (producing no children and bound 1).
def schedule_one_lb(+g: +List<Nat>, skip: Bool) -> +List<Item>:
  match skip:
    case True{}:
      Nil{}
    case False{}:
      Begin{g} <> (End{} <> Nil{})

def schedule_one_guess(+g: +List<Nat>, +best: SolveRef.Best,
                       same: Bool) -> +List<Item>:
  match same:
    case True{}:
      schedule_one_lb(g, skippable(best, 1n))
    case False{}:
      Nil{}

# Per-guess lazy schedule items. In duplicate-free mode, `best_cost > 2*n`
# skips the pre-grouping candidate scan altogether, while `best_cost == 2*n`
# uses tail-recursive `member_word_fast` to skip every non-candidate guess
# without grouping.
def guess_body(+nodup: Bool, +g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
               +best: SolveRef.Best) -> +List<Item>:
  match S:
    case Nil{}:
      +fg = fgroups_build_fast(g, Nil{}, Nil{})
      schedule_fguess(nodup, g, fg, 0n, best, fgroups_smaller(0n, fg))
    case Con{+w, +t}:
      match t:
        case Nil{}:
          schedule_one_guess(g, best, word_eq_fast(g, w))
        case Con{+w2, +t2}:
          +fg = fgroups_build_fast(g, w <> (w2 <> t2), Nil{})
          schedule_fguess(nodup, g, fg, n, best, fgroups_smaller(n, fg))

def guess_items_go(+nodup: Bool, +g: +List<Nat>, +S: +List<+List<Nat>>,
                   +n: Nat, +best: SolveRef.Best, pre_skip: Bool) -> +List<Item>:
  match pre_skip:
    case True{}:
      Nil{}
    case False{}:
      guess_body(nodup, g, S, n, best)

def guess_items_mem(+g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
                    +best: SolveRef.Best, in_s: Bool) -> +List<Item>:
  match in_s:
    case True{}:
      guess_body(True{}, g, S, n, best)
    case False{}:
      Nil{}

def guess_items_nodup(+g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
                      +best: SolveRef.Best, le_2n: Bool) -> +List<Item>:
  match le_2n:
    case False{}:
      guess_body(True{}, g, S, n, best)
    case True{}:
      guess_items_mem(g, S, n, best, member_word_fast(g, S))

def guess_items(+nodup: Bool, +g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
                +best: SolveRef.Best) -> +List<Item>:
  match nodup:
    case True{}:
      guess_items_nodup(g, S, n, best, skippable(best, Nat.add(n, n)))
    case False{}:
      guess_items_go(False{}, g, S, n, best, skippable(best, pre_lb(n, g, S)))

# Per-node reusable 1024-entry flat arrays for 5-letter duplicate-free nodes:
# `seen` stores a generation stamp for O(1) zero-allocation lower-bound and
# usability pruning (`hist5_go`), and `buckets` stores reversed candidate lists
# for O(|S|) bucketing (`fill5_go` + `drain5_go`) on surviving guesses.
type Buf5 is Type:
  NoBuf{}
  Buf5{seen: Array<Nat>, buckets: Array<+List<+List<Nat>>>, gen: Nat}

type GuessRes is Type:
  GuessRes{items: +List<Item>, buf: Buf5}

def mk_buf_go(use: Bool) -> Buf5:
  match use:
    case True{}:
      Buf5{Array.new(Nat, 10n, 0n), Array.new(+List<+List<Nat>>, 10n, Nil{}), 1n}
    case False{}:
      NoBuf{}

def mk_buf_nodup(+n: Nat, +b0: SolveRef.Best) -> Buf5:
  mk_buf_go(
    Bool.or(Nat.is_le(8n, n),
      Bool.and(Nat.is_le(2n, n), Bool.not(skippable(b0, Nat.add(n, n))))))

def mk_buf(+nodup: Bool, +n: Nat, +b0: SolveRef.Best) -> Buf5:
  match nodup:
    case True{}:
      mk_buf_nodup(n, b0)
    case False{}:
      NoBuf{}

# Pass 1: generation-stamped O(1) histogram counting `m` (non-matching
# candidates) and `k` (distinct feedback classes) without allocating classes.
type Hist5Res is Type:
  Hist5Ok{seen: Array<Nat>, m: Nat, k: Nat}
  Hist5Fallback{seen: Array<Nat>}

def hist5_hit(seen: Array<Nat>, +m: Nat, +k: Nat,
              seen_before: Bool) -> Hist5Res:
  match seen_before:
    case True{}:
      Hist5Ok{seen, Nat.add(1n, m), k}
    case False{}:
      Hist5Ok{seen, Nat.add(1n, m), Nat.add(1n, k)}

def hist5_swap(+gen: Nat, +m: Nat, +k: Nat, r: Array<Nat> & Nat) -> Hist5Res:
  (seen2, +old) = r
  hist5_hit(seen2, m, k, Nat.is_eq(old, gen))

def hist5_step(seen: Array<Nat>, +gen: Nat, +m: Nat, +k: Nat, +code: U32,
               same: Bool) -> Hist5Res:
  match same:
    case True{}:
      Hist5Ok{seen, m, k}
    case False{}:
      hist5_swap(gen, m, k, Array.swap(Nat, seen, code, gen))

def hist5_one(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
              +w: +List<Nat>, seen: Array<Nat>, +gen: Nat,
              +m: Nat, +k: Nat) -> Hist5Res:
  match w:
    case Nil{}:
      Hist5Fallback{seen}
    case Con{a0, t1}:
      match t1:
        case Nil{}:
          Hist5Fallback{seen}
        case Con{a1, t2}:
          match t2:
            case Nil{}:
              Hist5Fallback{seen}
            case Con{a2, t3}:
              match t3:
                case Nil{}:
                  Hist5Fallback{seen}
                case Con{a3, t4}:
                  match t4:
                    case Nil{}:
                      Hist5Fallback{seen}
                    case Con{a4, t5}:
                      match t5:
                        case Nil{}:
                          +code = feedback_code5(g0, g1, g2, g3, g4,
                                                 a0, a1, a2, a3, a4)
                          hist5_step(seen, gen, m, k, code, U32.is_eq(code, 682))
                        case Con{a5, t6}:
                          Hist5Fallback{seen}

def hist5_go(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
             +S: +List<+List<Nat>>, +gen: Nat, st: Hist5Res) -> Hist5Res:
  match S:
    case Nil{}:
      st
    case Con{w, rest}:
      match st:
        case Hist5Fallback{seen}:
          Hist5Fallback{seen}
        case Hist5Ok{seen, +m, +k}:
          hist5_go(g0, g1, g2, g3, g4, rest, gen,
            hist5_one(g0, g1, g2, g3, g4, w, seen, gen, m, k))

# Pass 2 (surviving guesses only): O(|S|) bucketing into `buckets` with
# `touched` recording distinct codes in reverse first-seen order, followed by a
# single tail-recursive drain that resets every touched slot back to `Nil{}`
# while emitting exact schedule items with `tail_lb`.
type Fill5State is Type:
  Fill5State{buckets: Array<+List<+List<Nat>>>, touched: +List<U32>}

def fill5_get_done(+w: +List<Nat>, +code: U32, +touched: +List<U32>,
                   r: Array<+List<+List<Nat>>> & +List<+List<Nat>>) -> Fill5State:
  (b2, +old) = r
  match old:
    case Nil{}:
      Fill5State{Array.set(+List<+List<Nat>>, b2, code, w <> Nil{}),
                 code <> touched}
    case Con{h, t}:
      Fill5State{Array.set(+List<+List<Nat>>, b2, code, w <> (h <> t)),
                 touched}

def fill5_step(+w: +List<Nat>, +code: U32, same: Bool,
               buckets: Array<+List<+List<Nat>>>,
               +touched: +List<U32>) -> Fill5State:
  match same:
    case True{}:
      Fill5State{buckets, touched}
    case False{}:
      fill5_get_done(w, code, touched,
        Array.get(+List<+List<Nat>>, buckets, code))

def fill5_one(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
              +w: +List<Nat>, buckets: Array<+List<+List<Nat>>>,
              +touched: +List<U32>) -> Fill5State:
  match w:
    case Nil{}:
      Fill5State{buckets, touched}
    case Con{a0, t1}:
      match t1:
        case Nil{}:
          Fill5State{buckets, touched}
        case Con{a1, t2}:
          match t2:
            case Nil{}:
              Fill5State{buckets, touched}
            case Con{a2, t3}:
              match t3:
                case Nil{}:
                  Fill5State{buckets, touched}
                case Con{a3, t4}:
                  match t4:
                    case Nil{}:
                      Fill5State{buckets, touched}
                    case Con{a4, t5}:
                      match t5:
                        case Nil{}:
                          +code = feedback_code5(g0, g1, g2, g3, g4,
                                                 a0, a1, a2, a3, a4)
                          fill5_step(w, code, U32.is_eq(code, 682),
                            buckets, touched)
                        case Con{a5, t6}:
                          Fill5State{buckets, touched}

def fill5_go(+g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat, +g4: Nat,
             +S: +List<+List<Nat>>, st: Fill5State) -> Fill5State:
  match S:
    case Nil{}:
      st
    case Con{w, rest}:
      match st:
        case Fill5State{buckets, +touched}:
          fill5_go(g0, g1, g2, g3, g4, rest,
            fill5_one(g0, g1, g2, g3, g4, w, buckets, touched))

type Drain5State is Type:
  Drain5State{buckets: Array<+List<+List<Nat>>>, rem_lb: Nat, items: +List<Item>}

def drain5_add_ge2(+fb: +List<Feedback.Color>, +rem_lb: Nat,
                   +items: +List<Item>, buckets: Array<+List<+List<Nat>>>,
                   rl: RevLen) -> Drain5State:
  match rl:
    case RevLen{+len, +ws}:
      +clb = Nat.sub(Nat.add(len, len), 1n)
      Drain5State{buckets, Nat.add(clb, rem_lb),
        ClassItem{fb, ws, len, rem_lb} <> (Add{fb, rem_lb} <> items)}

def drain5_add(+code: U32, +rem_lb: Nat, +items: +List<Item>,
               buckets: Array<+List<+List<Nat>>>,
               +rws: +List<+List<Nat>>) -> Drain5State:
  match rws:
    case Nil{}:
      +fb = decode_fb5(code)
      Drain5State{buckets, rem_lb,
        ClassItem{fb, Nil{}, 0n, rem_lb} <> (Add{fb, rem_lb} <> items)}
    case Con{+w, +wt}:
      match wt:
        case Nil{}:
          Drain5State{buckets, Nat.add(1n, rem_lb),
            OneItem{decode_fb5(code), w} <> items}
        case Con{+w2, +wt2}:
          drain5_add_ge2(decode_fb5(code), rem_lb, items, buckets,
            rev_words_len(wt2, w2 <> (w <> Nil{}), 2n))

def drain5_swap(+code: U32, +rem_lb: Nat, +items: +List<Item>,
                r: Array<+List<+List<Nat>>> & +List<+List<Nat>>) -> Drain5State:
  (b2, +rws) = r
  drain5_add(code, rem_lb, items, b2, rws)

def drain5_go(+touched: +List<U32>, st: Drain5State) -> Drain5State:
  match touched:
    case Nil{}:
      st
    case Con{+code, +rest}:
      match st:
        case Drain5State{buckets, +rem_lb, +items}:
          drain5_go(rest,
            drain5_swap(code, rem_lb, items,
              Array.swap(+List<+List<Nat>>, buckets, code, Nil{})))

def finish_drain5(+g: +List<Nat>, seen: Array<Nat>, +gen2: Nat,
                  dr: Drain5State) -> GuessRes:
  match dr:
    case Drain5State{buckets3, rem_lb, +items}:
      GuessRes{Begin{g} <> items, Buf5{seen, buckets3, gen2}}

def run_drain5(+g: +List<Nat>, +n: Nat, seen: Array<Nat>, +gen2: Nat,
               fs: Fill5State) -> GuessRes:
  match fs:
    case Fill5State{buckets2, +touched}:
      finish_drain5(g, seen, gen2,
        drain5_go(touched, Drain5State{buckets2, n, End{} <> Nil{}}))

def schedule5_lb(+g: +List<Nat>, +g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat,
                 +g4: Nat, +S: +List<+List<Nat>>, +n: Nat,
                 seen: Array<Nat>, buckets: Array<+List<+List<Nat>>>,
                 +gen2: Nat, skip: Bool) -> GuessRes:
  match skip:
    case True{}:
      GuessRes{Nil{}, Buf5{seen, buckets, gen2}}
    case False{}:
      run_drain5(g, n, seen, gen2,
        fill5_go(g0, g1, g2, g3, g4, S, Fill5State{buckets, Nil{}}))

def schedule5_usable(+g: +List<Nat>, +g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat,
                     +g4: Nat, +S: +List<+List<Nat>>, +n: Nat,
                     +best: SolveRef.Best, seen: Array<Nat>,
                     buckets: Array<+List<+List<Nat>>>, +gen2: Nat,
                     +m: Nat, +k: Nat, usable: Bool) -> GuessRes:
  match usable:
    case False{}:
      GuessRes{Nil{}, Buf5{seen, buckets, gen2}}
    case True{}:
      +lb = Nat.sub(Nat.add(n, Nat.add(m, m)), k)
      schedule5_lb(g, g0, g1, g2, g3, g4, S, n, seen, buckets, gen2,
        skippable(best, lb))

def schedule5_hist(+g: +List<Nat>, +g0: Nat, +g1: Nat, +g2: Nat, +g3: Nat,
                   +g4: Nat, +S: +List<+List<Nat>>, +n: Nat,
                   +best: SolveRef.Best, buckets: Array<+List<+List<Nat>>>,
                   +gen: Nat, hr: Hist5Res) -> GuessRes:
  match hr:
    case Hist5Fallback{seen2}:
      +fg = fgroups_build_fast(g, S, Nil{})
      GuessRes{
        schedule_fguess(True{}, g, fg, n, best, fgroups_smaller(n, fg)),
        Buf5{seen2, buckets, Nat.add(1n, gen)}}
    case Hist5Ok{seen2, +m, +k}:
      schedule5_usable(g, g0, g1, g2, g3, g4, S, n, best, seen2, buckets,
        Nat.add(1n, gen), m, k,
        Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)))

def guess_body_buf5(+g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
                    +best: SolveRef.Best, seen: Array<Nat>,
                    buckets: Array<+List<+List<Nat>>>, +gen: Nat) -> GuessRes:
  match g:
    case Nil{}:
      +fg = fgroups_build_fast(Nil{}, S, Nil{})
      GuessRes{schedule_fguess(True{}, Nil{}, fg, n, best, fgroups_smaller(n, fg)),
               Buf5{seen, buckets, gen}}
    case Con{+g0, +t1}:
      match t1:
        case Nil{}:
          +fg = fgroups_build_fast(g0 <> Nil{}, S, Nil{})
          GuessRes{schedule_fguess(True{}, g0 <> Nil{}, fg, n, best,
                     fgroups_smaller(n, fg)),
                   Buf5{seen, buckets, gen}}
        case Con{+g1, +t2}:
          match t2:
            case Nil{}:
              +gw : +List<Nat> = g0 <> (g1 <> Nil{})
              +fg = fgroups_build_fast(gw, S, Nil{})
              GuessRes{schedule_fguess(True{}, gw, fg, n, best,
                         fgroups_smaller(n, fg)),
                       Buf5{seen, buckets, gen}}
            case Con{+g2, +t3}:
              match t3:
                case Nil{}:
                  +gw : +List<Nat> = g0 <> (g1 <> (g2 <> Nil{}))
                  +fg = fgroups_build_fast(gw, S, Nil{})
                  GuessRes{schedule_fguess(True{}, gw, fg, n, best,
                             fgroups_smaller(n, fg)),
                           Buf5{seen, buckets, gen}}
                case Con{+g3, +t4}:
                  match t4:
                    case Nil{}:
                      +gw : +List<Nat> = g0 <> (g1 <> (g2 <> (g3 <> Nil{})))
                      +fg = fgroups_build_fast(gw, S, Nil{})
                      GuessRes{schedule_fguess(True{}, gw, fg, n, best,
                                 fgroups_smaller(n, fg)),
                               Buf5{seen, buckets, gen}}
                    case Con{+g4, +t5}:
                      match t5:
                        case Nil{}:
                          +gw : +List<Nat> =
                            g0 <> (g1 <> (g2 <> (g3 <> (g4 <> Nil{}))))
                          schedule5_hist(gw, g0, g1, g2, g3, g4, S, n, best,
                            buckets, gen,
                            hist5_go(g0, g1, g2, g3, g4, S, gen,
                              Hist5Ok{seen, 0n, 0n}))
                        case Con{+g5, +t6}:
                          +gw : +List<Nat> =
                            g0 <> (g1 <> (g2 <> (g3 <> (g4 <> (g5 <> t6)))))
                          +fg = fgroups_build_fast(gw, S, Nil{})
                          GuessRes{schedule_fguess(True{}, gw, fg, n, best,
                                     fgroups_smaller(n, fg)),
                                   Buf5{seen, buckets, gen}}

def guess_body_buf_ge2(+g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
                       +best: SolveRef.Best, buf: Buf5) -> GuessRes:
  match buf:
    case NoBuf{}:
      +fg = fgroups_build_fast(g, S, Nil{})
      GuessRes{schedule_fguess(True{}, g, fg, n, best, fgroups_smaller(n, fg)),
               NoBuf{}}
    case Buf5{seen, buckets, +gen}:
      guess_body_buf5(g, S, n, best, seen, buckets, gen)

def guess_body_buf(+g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
                   +best: SolveRef.Best, buf: Buf5) -> GuessRes:
  match S:
    case Nil{}:
      +fg = fgroups_build_fast(g, Nil{}, Nil{})
      GuessRes{schedule_fguess(True{}, g, fg, 0n, best, fgroups_smaller(0n, fg)),
               buf}
    case Con{+w, +t}:
      match t:
        case Nil{}:
          GuessRes{schedule_one_guess(g, best, word_eq_fast(g, w)), buf}
        case Con{+w2, +t2}:
          guess_body_buf_ge2(g, w <> (w2 <> t2), n, best, buf)

def guess_items_mem_buf(+g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
                        +best: SolveRef.Best, buf: Buf5,
                        in_s: Bool) -> GuessRes:
  match in_s:
    case True{}:
      guess_body_buf(g, S, n, best, buf)
    case False{}:
      GuessRes{Nil{}, buf}

def guess_items_nodup_buf(+g: +List<Nat>, +S: +List<+List<Nat>>, +n: Nat,
                          +best: SolveRef.Best, buf: Buf5,
                          le_2n: Bool) -> GuessRes:
  match le_2n:
    case False{}:
      guess_body_buf(g, S, n, best, buf)
    case True{}:
      guess_items_mem_buf(g, S, n, best, buf, member_word_fast(g, S))

def guess_items_buf(+nodup: Bool, +g: +List<Nat>, +S: +List<+List<Nat>>,
                    +n: Nat, +best: SolveRef.Best, buf: Buf5) -> GuessRes:
  match nodup:
    case True{}:
      guess_items_nodup_buf(g, S, n, best, buf,
        skippable(best, Nat.add(n, n)))
    case False{}:
      GuessRes{
        guess_items_go(False{}, g, S, n, best, skippable(best, pre_lb(n, g, S))),
        buf}

# One step of the pruned search. Lexicographic structural recursion on
# `(fuel, gs, phase, cs)` builds each guess lazily into `gres` when `cs`
# becomes `Nil{}`, unpacks `gres` on `phase = 1n`, caches `n = |S|` and
# `nodup`, threads the node's reusable `Buf5` across guesses, and exits
# immediately once `done` signals `best_cost(best) <= 2 * n - 1` in
# duplicate-free mode.
def step(+fuel: Nat, +gs: +List<+List<Nat>>, +phase: Nat, +cs: +List<Item>,
         +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +n: Nat, +nodup: Bool,
         +inf: Nat, +g: +List<Nat>, +kids: +List<Tree.Child>, +sum: Nat,
         +best: SolveRef.Best, +pending: SolveRef.Best, skip: Bool,
         done: Bool, gres: GuessRes) -> SolveRef.Best:
  match fuel:
    case 0n:
      match gs:
        case Nil{}:
          match cs:
            case Nil{}:
              best
            case Con{item, rest}:
              match item:
                case Begin{g2}:
                  step(0n, Nil{}, phase, rest, G, S, n, nodup, inf, g2, Nil{},
                       0n, best, pending, False{}, False{}, gres)
                case ClassItem{fb, words, wlen, tail_lb}:
                  dummy_inf(inf)
                case OneItem{fb, w}:
                  dummy_inf(inf)
                case Add{fb, tail_lb}:
                  match pending:
                    case SolveRef.Best{tree, cost}:
                      step(0n, Nil{}, phase, rest, G, S, n, nodup, inf, g,
                           Tree.Child{fb, tree} <> kids,
                           SolveRef.sat_add(inf, sum, cost), best,
                           dummy_zero(), skip, False{}, gres)
                case End{}:
                  step(0n, Nil{}, phase, rest, G, S, n, nodup, inf, Nil{},
                       Nil{}, 0n,
                       SolveRef.finish_guess(inf, g, kids, sum, n, best),
                       dummy_zero(), False{}, False{}, gres)
        case Con{+g2, +grest}:
          match cs:
            case Nil{}:
              step(0n, grest, phase, Begin{g2} <> (End{} <> Nil{}),
                   G, S, n, nodup, inf, Nil{}, Nil{}, 0n, best,
                   dummy_zero(), False{}, False{}, gres)
            case Con{item, rest}:
              match item:
                case Begin{g3}:
                  step(0n, g2 <> grest, phase, rest, G, S, n, nodup, inf, g3,
                       Nil{}, 0n, best, pending, False{}, False{}, gres)
                case ClassItem{fb, words, wlen, tail_lb}:
                  dummy_inf(inf)
                case OneItem{fb, w}:
                  dummy_inf(inf)
                case Add{fb, tail_lb}:
                  match pending:
                    case SolveRef.Best{tree, cost}:
                      step(0n, g2 <> grest, phase, rest, G, S, n, nodup, inf, g,
                           Tree.Child{fb, tree} <> kids,
                           SolveRef.sat_add(inf, sum, cost), best,
                           dummy_zero(), skip, False{}, gres)
                case End{}:
                  step(0n, g2 <> grest, phase, rest, G, S, n, nodup, inf,
                       Nil{}, Nil{}, 0n,
                       SolveRef.finish_guess(inf, g, kids, sum, n, best),
                       dummy_zero(), False{}, False{}, gres)
    case 1n+p:
      match gs:
        case Nil{}:
          match phase:
            case 1n+q:
              match gres:
                case GuessRes{items, buf2}:
                  step(fuel, Nil{}, q, items, G, S, n, nodup, inf,
                       Nil{}, Nil{}, 0n, best, dummy_zero(), False{}, False{},
                       GuessRes{Nil{}, buf2})
            case 0n:
              match cs:
                case Nil{}:
                  best
                case Con{item, rest}:
                  match item:
                    case Begin{g2}:
                      step(fuel, Nil{}, 0n, rest, G, S, n, nodup, inf, g2,
                           Nil{}, 0n, best, dummy_zero(), False{}, False{}, gres)
                    case ClassItem{fb, words, +wlen, +tail_lb}:
                      match skip:
                        case True{}:
                          step(fuel, Nil{}, 0n, rest, G, S, n, nodup, inf, g,
                               kids, sum, best, dummy_zero(), True{}, False{},
                               gres)
                        case False{}:
                          +b0 = dummy_inf(Nat.sub(best_cost(best), Nat.add(sum, tail_lb)))
                          step(fuel, Nil{}, 0n, rest, G, S, n, nodup, inf, g,
                               kids, sum, best,
                               step(p, G, 0n, Nil{}, G, words, wlen, nodup, inf,
                                    Nil{}, Nil{}, 0n, b0, dummy_zero(), False{},
                                    is_floor_hit(nodup, wlen, b0),
                                    GuessRes{Nil{}, mk_buf(nodup, wlen, b0)}),
                               False{}, False{}, gres)
                    case OneItem{fb, w}:
                      match skip:
                        case True{}:
                          step(fuel, Nil{}, 0n, rest, G, S, n, nodup, inf, g,
                               kids, sum, best, dummy_zero(), True{}, False{},
                               gres)
                        case False{}:
                          step(fuel, Nil{}, 0n, rest, G, S, n, nodup, inf, g,
                               Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
                               SolveRef.sat_add(inf, sum, 1n), best,
                               dummy_zero(), False{}, False{}, gres)
                    case Add{fb, +tail_lb}:
                      match pending:
                        case SolveRef.Best{tree, +cost}:
                          match skip:
                            case True{}:
                              step(fuel, Nil{}, 0n, rest, G, S, n, nodup, inf,
                                   g, kids, sum, best, dummy_zero(), True{},
                                   False{}, gres)
                            case False{}:
                              +sum2 = SolveRef.sat_add(inf, sum, cost)
                              step(fuel, Nil{}, 0n, rest, G, S, n, nodup, inf,
                                   g, Tree.Child{fb, tree} <> kids,
                                   sum2, best, dummy_zero(),
                                   skippable(best, Nat.add(sum2, tail_lb)),
                                   False{}, gres)
                    case End{}:
                      match skip:
                        case True{}:
                          step(fuel, Nil{}, 0n, rest, G, S, n, nodup, inf,
                               Nil{}, Nil{}, 0n, best, dummy_zero(), False{},
                               False{}, gres)
                        case False{}:
                          +best2 = SolveRef.finish_guess(inf, g, kids, sum, n, best)
                          step(fuel, Nil{}, 0n, rest, G, S, n, nodup, inf,
                               Nil{}, Nil{}, 0n, best2, dummy_zero(), False{},
                               is_floor_hit(nodup, n, best2), gres)
        case Con{+g2, +grest}:
          match phase:
            case 1n+q:
              match gres:
                case GuessRes{items, buf2}:
                  step(fuel, g2 <> grest, q, items, G, S, n, nodup, inf,
                       Nil{}, Nil{}, 0n, best, dummy_zero(), False{}, False{},
                       GuessRes{Nil{}, buf2})
            case 0n:
              match cs:
                case Nil{}:
                  match done:
                    case True{}:
                      best
                    case False{}:
                      match gres:
                        case GuessRes{old_items, buf}:
                          step(fuel, grest, 1n, Nil{}, G, S, n, nodup, inf,
                               Nil{}, Nil{}, 0n, best, dummy_zero(), False{},
                               False{},
                               guess_items_buf(nodup, g2, S, n, best, buf))
                case Con{item, rest}:
                  match item:
                    case Begin{g3}:
                      step(fuel, g2 <> grest, 0n, rest, G, S, n, nodup, inf, g3,
                           Nil{}, 0n, best, dummy_zero(), False{}, False{}, gres)
                    case ClassItem{fb, words, +wlen, +tail_lb}:
                      match skip:
                        case True{}:
                          step(fuel, g2 <> grest, 0n, rest, G, S, n, nodup, inf,
                               g, kids, sum, best, dummy_zero(), True{},
                               False{}, gres)
                        case False{}:
                          +b0 = dummy_inf(Nat.sub(best_cost(best), Nat.add(sum, tail_lb)))
                          step(fuel, g2 <> grest, 0n, rest, G, S, n, nodup, inf,
                               g, kids, sum, best,
                               step(p, G, 0n, Nil{}, G, words, wlen, nodup, inf,
                                    Nil{}, Nil{}, 0n, b0, dummy_zero(), False{},
                                    is_floor_hit(nodup, wlen, b0),
                                    GuessRes{Nil{}, mk_buf(nodup, wlen, b0)}),
                               False{}, False{}, gres)
                    case OneItem{fb, w}:
                      match skip:
                        case True{}:
                          step(fuel, g2 <> grest, 0n, rest, G, S, n, nodup, inf,
                               g, kids, sum, best, dummy_zero(), True{},
                               False{}, gres)
                        case False{}:
                          step(fuel, g2 <> grest, 0n, rest, G, S, n, nodup, inf,
                               g, Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
                               SolveRef.sat_add(inf, sum, 1n), best,
                               dummy_zero(), False{}, False{}, gres)
                    case Add{fb, +tail_lb}:
                      match pending:
                        case SolveRef.Best{tree, +cost}:
                          match skip:
                            case True{}:
                              step(fuel, g2 <> grest, 0n, rest, G, S, n, nodup,
                                   inf, g, kids, sum, best, dummy_zero(),
                                   True{}, False{}, gres)
                            case False{}:
                              +sum2 = SolveRef.sat_add(inf, sum, cost)
                              step(fuel, g2 <> grest, 0n, rest, G, S, n, nodup,
                                   inf, g, Tree.Child{fb, tree} <> kids,
                                   sum2, best, dummy_zero(),
                                   skippable(best, Nat.add(sum2, tail_lb)),
                                   False{}, gres)
                    case End{}:
                      match skip:
                        case True{}:
                          step(fuel, g2 <> grest, 0n, rest, G, S, n, nodup, inf,
                               Nil{}, Nil{}, 0n, best, dummy_zero(), False{},
                               False{}, gres)
                        case False{}:
                          +best2 = SolveRef.finish_guess(inf, g, kids, sum, n, best)
                          step(fuel, g2 <> grest, 0n, rest, G, S, n, nodup, inf,
                               Nil{}, Nil{}, 0n, best2, dummy_zero(), False{},
                               is_floor_hit(nodup, n, best2), gres)

# The pruned search on a guess list and candidate list. Checks once at the root
# that every candidate belongs to `guesses` (returning `None{}` immediately if
# not) and whether `candidates` is duplicate-free (enabling O(1) `class_lb`,
# O(1) floor exit at `2 * |S| - 1`, fast pre-bound filtering, and the flat
# 1024-entry 5-letter histogram and bucketing path throughout).
def solve_fast_valid(+guesses: +List<+List<Nat>>,
                     +candidates: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  match candidates:
    case Nil{}:
      +inf = SolveRef.inf_of(0n)
      +b0 = dummy_inf(inf)
      SolveRef.best_to_maybe(inf,
        step(0n, guesses, 0n, Nil{}, guesses, Nil{}, 0n, True{}, inf,
             Nil{}, Nil{}, 0n, b0, dummy_zero(), False{},
             is_floor_hit(True{}, 0n, b0),
             GuessRes{Nil{}, mk_buf(True{}, 0n, b0)}))
    case Con{+w, +t}:
      match t:
        case Nil{}:
          Some{Tree.Node{w, Nil{}}}
        case Con{+w2, +t2}:
          +cs : +List<+List<Nat>> = w <> (w2 <> t2)
          +n = Groups.len_words(cs)
          +inf = SolveRef.inf_of(n)
          +nd = no_dup_fast(cs)
          +b0 = dummy_inf(inf)
          SolveRef.best_to_maybe(inf,
            step(n, guesses, 0n, Nil{}, guesses, cs, n, nd, inf,
                 Nil{}, Nil{}, 0n, b0, dummy_zero(), False{},
                 is_floor_hit(nd, n, b0),
                 GuessRes{Nil{}, mk_buf(nd, n, b0)}))

def solve_fast_checked(ok: Bool, +guesses: +List<+List<Nat>>,
                       +candidates: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  match ok:
    case False{}:
      None{}
    case True{}:
      solve_fast_valid(guesses, candidates)

def solve_fast(+guesses: +List<+List<Nat>>,
               +candidates: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  solve_fast_checked(all_in_fast(candidates, guesses), guesses, candidates)

def solve(+guesses: +List<+List<Nat>>,
          +candidates: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  solve_fast(guesses, candidates)
