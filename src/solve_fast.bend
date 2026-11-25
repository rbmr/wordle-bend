# The bound-pruned solver.
#
# This module implements the exact solver behind `src/solve.bend`, proved
# directly valid and optimal (`Laws.solve_valid` and `Laws.solve_optimal` in
# `proofs/fast_opt.bend`) while `src/solve_ref.bend` stays in the tree as the
# reference specification. Returning any optimal tree (rather than matching the
# reference's tie-breaking order) lets the search reorder guesses, resolve
# duplicate-free two-word classes in O(1), and stop at a tighter floor once
# candidate guesses have been checked.
#
# For a guess `g` over a candidate list `S`, the node costs one per candidate
# plus its feedback children's costs. In any valid subtree for a class `ws`,
# only the subtree's root guess can end at depth one, so
# `cost(T, ws) >= 2 * |ws| - max_mult(ws)` (`proofs/lb_twice.bend`). When the
# root candidate list has no duplicates (checked once at the root by
# `no_dup_fast`), every feedback class is a subsequence of its parent
# (`proofs/cover_groups.bend`) and also has no duplicates, so `max_mult(ws) = 1`,
# `class_lb(ws) = 2 * |ws| - 1` in O(1), and every tree over `S` costs at least
# `2 * |S| - 1` — allowing immediate early exit once `best_cost(best) <= floor`.
#
# On duplicate-free 5-letter inputs (checked once at the root), a single
# reusable `Buf5` holding a generation-stamped 1024-entry `seen` array, a
# 1024-entry `buckets` array, and a precomputed `|G| x |C|` flat `Array<U32>`
# feedback code table `tbl` is allocated once at the root and threaded linearly
# through the entire search tree via `StepRes`. Each candidate carries its
# column index and guess-row offset in `CWord`, eliminating repeated feedback
# computation in `hist5_go` and `fill5_go`. On child nodes, candidate words `S`
# are tried before `G` via `GList` (`GTry` / `GThen` / `GEnd`); after `GThen`
# raises the floor from `2 * |S| - 1` to `2 * |S|`, stage-two histograms skip
# already-tried candidate guesses (`code == 682`) and tighten the collision
# budget to `best_cost(best) - 2 * |S| - 1`. Surviving guesses drain feedback
# classes Largest-Class-First (`BigClass`), resolve singleton (`OneItem`),
# duplicate-free two-word (`TwoItem`, cost 3), and duplicate-free three-word
# (`DoneItem`, exact cost 5 or 6 via `solve_three_tbl`) classes in O(1), and
# pass tight remaining budgets `best_cost(best) - (sum + tail_lb)` to recursive
# `ClassItem` searches.
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
type CWord is Data:
  CWord{ci: U32, grow: U32, word: +List<Nat>}

def cwords_words(+cs: +List<CWord>) -> +List<+List<Nat>>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{cw, rest}:
      match cw:
        case CWord{ci, grow, w}:
          w <> cwords_words(rest)

def dummy_cwords(+ws: +List<+List<Nat>>) -> +List<CWord>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, rest}:
      CWord{0, 0, w} <> dummy_cwords(rest)

type Item is Data:
  Begin{guess: +List<Nat>}
  ClassItem{fb: +List<Feedback.Color>, words: +List<CWord>, wlen: Nat, tail_lb: Nat}
  OneItem{fb: +List<Feedback.Color>, word: +List<Nat>}
  TwoItem{fb: +List<Feedback.Color>, w1: +List<Nat>, w2: +List<Nat>}
  DoneItem{fb: +List<Feedback.Color>, tree: Tree.Tree, cost: Nat}
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

# --- capacity lower bound -------------------------------------------------
#
# A class whose biggest branching factor over the guess list is `k` can hold
# only `G_j = 1 + k + ... + k^(j-1)` candidates in its first `j` levels, so a
# tree over it costs at least `capbound(n, k)` (see proofs/lb_capacity.bend).
# Only duplicate-free buffered nodes use this: `mk_buf_tbl` is built for the
# no-duplicate path only, so a level ends at most one candidate per node.
#
# The exact `k` costs a pass over the guess table times the class size, so the
# walk below runs at most once per node and only for classes of at least 16
# candidates; it stops as soon as the bound already reaches `best`. Nodes with
# fewer than 512 candidates skip it entirely: the pass costs more there than
# the bound saves.

# `n + sum over levels of (n - capacity(level))+`, where level 1 holds one
# candidate and each further level holds `1 + k * capacity`.
def cap_go(+rem: Nat, +n: Nat, +k: Nat, +cap: Nat, +acc: Nat) -> Nat:
  match rem:
    case 0n:
      acc
    case 1n+p:
      cap_go(p, n, k, Nat.min(n, Nat.add(1n, Nat.mul(k, cap))),
             Nat.add(Nat.sub(n, cap), acc))

def capbound(+n: Nat, +k: Nat) -> Nat:
  Nat.add(n, cap_go(n, n, k, 1n, 0n))

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

# Floor-hit check: in duplicate-free mode, exiting as soon as
# `best_cost(best) <= floor` (`2*n - 1` while candidates remain untried, and
# `2*n` once every candidate in `S` has been tried).
def is_floor_hit(+nodup: Bool, +floor: Nat, +best: SolveRef.Best) -> Bool:
  match nodup:
    case True{}:
      skippable(best, floor)
    case False{}:
      False{}

def init_floor(+n: Nat) -> Nat:
  Nat.sub(Nat.add(n, n), 1n)

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

def group_items_two(nodup: Bool, +n: Nat, +f: +List<Feedback.Color>,
                    +w: +List<Nat>, +w2: +List<Nat>,
                    +rest: +List<Groups.Group>, +rest_items: +List<Item>) -> +List<Item>:
  match nodup:
    case True{}:
      TwoItem{f, w, w2} <> rest_items
    case False{}:
      +ws2 : +List<+List<Nat>> = w <> (w2 <> Nil{})
      +tlb = lower_bound(n, rest)
      ClassItem{f, dummy_cwords(ws2), 2n, tlb} <> (Add{f, tlb} <> rest_items)

# Specification of the class items of one guess: singleton classes `[w]`
# become `OneItem{f, w}`, duplicate-free two-word classes `[w, w2]` become
# `TwoItem{f, w, w2}`, and larger classes carry `wlen = |ws|` and
# `tail_lb = lower_bound(n, rest)` on `ClassItem` and `Add`.
def group_items(+nodup: Bool, +n: Nat, +groups: +List<Groups.Group>) -> +List<Item>:
  match groups:
    case Nil{}:
      Nil{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+f, +ws}:
          match ws:
            case Nil{}:
              +tlb = lower_bound(n, rest)
              ClassItem{f, Nil{}, 0n, tlb} <> (Add{f, tlb} <> group_items(nodup, n, rest))
            case Con{+w, +wt}:
              match wt:
                case Nil{}:
                  OneItem{f, w} <> group_items(nodup, n, rest)
                case Con{+w2, +wt2}:
                  match wt2:
                    case Nil{}:
                      group_items_two(nodup, n, f, w, w2, rest,
                        group_items(nodup, n, rest))
                    case Con{+w3, +wt3}:
                      +ws3 : +List<+List<Nat>> = w <> (w2 <> (w3 <> wt3))
                      +tlb = lower_bound(n, rest)
                      ClassItem{f, dummy_cwords(ws3), Groups.len_words(ws3), tlb}
                      <> (Add{f, tlb} <> group_items(nodup, n, rest))

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
        ClassItem{f, dummy_cwords(ws), wlen, rem_lb} <> (Add{f, rem_lb} <> rest_items)}

def group_items_one_step(+f: +List<Feedback.Color>, +w: +List<Nat>,
                         ib: ItemsBound) -> ItemsBound:
  match ib:
    case ItemsBound{+rem_lb, +rest_items}:
      ItemsBound{Nat.add(1n, rem_lb), OneItem{f, w} <> rest_items}

def group_items_two_step(+f: +List<Feedback.Color>, +w1: +List<Nat>,
                         +w2: +List<Nat>, ib: ItemsBound) -> ItemsBound:
  match ib:
    case ItemsBound{+rem_lb, +rest_items}:
      ItemsBound{Nat.add(3n, rem_lb), TwoItem{f, w1, w2} <> rest_items}

def fgroup_items_two(nodup: Bool, +f: +List<Feedback.Color>, +len: Nat,
                     +w: +List<Nat>, +w2: +List<Nat>,
                     ib: ItemsBound) -> ItemsBound:
  match nodup:
    case True{}:
      group_items_two_step(f, w2, w, ib)
    case False{}:
      +ws2 : +List<+List<Nat>> = w2 <> (w <> Nil{})
      group_items_step(f, ws2, len, class_lb(ws2), ib)

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
                  match wt2:
                    case Nil{}:
                      fgroup_items_two(nodup, f, len, w, w2,
                        fgroup_items_build(nodup, n, rest, tail))
                    case Con{+w3, +wt3}:
                      +ws : +List<+List<Nat>> =
                        rev_words(wt3, w3 <> (w2 <> (w <> Nil{})))
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

# Staged guess queue carrying each guess's precomputed row offset in `tbl`.
type GList is Data:
  GEnd{}
  GTry{row: U32, g: +List<Nat>, rest: GList}
  GThen{rest: GList}

def glist_of_words(+ws: +List<+List<Nat>>, +tail: GList) -> GList:
  match ws:
    case Nil{}:
      tail
    case Con{w, rest}:
      GTry{0, w, glist_of_words(rest, tail)}

def glist_of_cwords(+cs: +List<CWord>, +tail: GList) -> GList:
  match cs:
    case Nil{}:
      tail
    case Con{cw, rest}:
      match cw:
        case CWord{ci, grow, w}:
          GTry{grow, w, glist_of_cwords(rest, tail)}

def glist_of_guesses(+G: +List<+List<Nat>>, +row: U32, +stride: U32) -> GList:
  match G:
    case Nil{}:
      GEnd{}
    case Con{g, rest}:
      GTry{row, g, glist_of_guesses(rest, U32.add(row, stride), stride)}

def child_glist_nodup(+words: +List<CWord>, +glist_G: GList,
                      le_2n: Bool) -> GList:
  match le_2n:
    case True{}:
      glist_of_cwords(words, GEnd{})
    case False{}:
      glist_of_cwords(words, GThen{glist_G})

def child_glist(+nodup: Bool, +words: +List<CWord>, +wlen: Nat,
                +b0: SolveRef.Best, +glist_G: GList) -> GList:
  match nodup:
    case True{}:
      child_glist_nodup(words, glist_G, skippable(b0, Nat.add(wlen, wlen)))
    case False{}:
      glist_G

type Buf5 is Type:
  NoBuf{}
  Buf5{seen: Array<Nat>, buckets: Array<+List<CWord>>, tbl: Array<U32>,
       gen: Nat, gn: Nat}

type GuessRes is Type:
  GuessRes{items: +List<Item>, buf: Buf5}

# Length-5 check and root feedback table construction.
def is_len5(+w: +List<Nat>) -> Bool:
  match w:
    case Nil{}:
      False{}
    case Con{a0, t1}:
      match t1:
        case Nil{}:
          False{}
        case Con{a1, t2}:
          match t2:
            case Nil{}:
              False{}
            case Con{a2, t3}:
              match t3:
                case Nil{}:
                  False{}
                case Con{a3, t4}:
                  match t4:
                    case Nil{}:
                      False{}
                    case Con{a4, t5}:
                      match t5:
                        case Nil{}:
                          True{}
                        case Con{_, _}:
                          False{}

def next_len5(+ws: +List<+List<Nat>>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{w, _}:
      is_len5(w)

def all_len5_go(+ws: +List<+List<Nat>>, ok: Bool) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{w, t}:
      match ok:
        case True{}:
          all_len5_go(t, next_len5(t))
        case False{}:
          False{}

def all_len5(+ws: +List<+List<Nat>>) -> Bool:
  all_len5_go(ws, next_len5(ws))

def depth_for_go(+rem: Nat, +target: Nat, +pow: Nat, +d: Nat,
                 ok: Bool) -> Maybe<Nat>:
  match rem:
    case 0n:
      match ok:
        case True{}:
          Some{d}
        case False{}:
          None{}
    case 1n+p:
      match ok:
        case True{}:
          Some{d}
        case False{}:
          +pow2 = Nat.add(pow, pow)
          depth_for_go(p, target, pow2, Nat.add(1n, d), Nat.is_le(target, pow2))

def depth_for(+target: Nat) -> Maybe<Nat>:
  depth_for_go(25n, target, 1n, 0n, Nat.is_le(target, 1n))

def find_grow_go(+w: +List<Nat>, +G: +List<+List<Nat>>, +row: U32,
                 +stride: U32, hit: Bool) -> U32:
  match G:
    case Nil{}:
      0
    case Con{g, rest}:
      match hit:
        case True{}:
          row
        case False{}:
          find_grow_go(w, rest, U32.add(row, stride), stride,
            next_word_hit(w, rest))

def find_grow(+w: +List<Nat>, +G: +List<+List<Nat>>, +stride: U32) -> U32:
  find_grow_go(w, G, 0, stride, next_word_hit(w, G))

def build_cwords(+C: +List<+List<Nat>>, +G: +List<+List<Nat>>,
                 +ci: U32, +gcount: U32) -> +List<CWord>:
  match C:
    case Nil{}:
      Nil{}
    case Con{+w, +rest}:
      CWord{ci, find_grow(w, G, 1), w}
      <> build_cwords(rest, G, U32.add(ci, gcount), gcount)

# Fill one candidate's block of the table: consecutive slots from `idx`, one
# per guess, stopping at the first guess that is not five letters.
def fill_tbl_col(+w0: Nat, +w1: Nat, +w2: Nat, +w3: Nat, +w4: Nat,
                 +G: +List<+List<Nat>>, +idx: U32,
                 tbl: Array<U32>) -> Array<U32>:
  match G:
    case Nil{}:
      tbl
    case Con{g, rest}:
      match g:
        case Nil{}:
          tbl
        case Con{g0, t1}:
          match t1:
            case Nil{}:
              tbl
            case Con{g1, t2}:
              match t2:
                case Nil{}:
                  tbl
                case Con{g2, t3}:
                  match t3:
                    case Nil{}:
                      tbl
                    case Con{g3, t4}:
                      match t4:
                        case Nil{}:
                          tbl
                        case Con{g4, t5}:
                          match t5:
                            case Nil{}:
                              +code = feedback_code5(g0, g1, g2, g3, g4,
                                                     w0, w1, w2, w3, w4)
                              fill_tbl_col(w0, w1, w2, w3, w4, rest,
                                U32.inc(idx), Array.set(U32, tbl, idx, code))
                            case Con{_, _}:
                              tbl

# Candidate-major table: candidate `ci` owns the block of `step` slots that
# starts at `row`, so the slots of a block are consecutive.
def fill_tbl_go(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>, +row: U32,
                +step: U32, tbl: Array<U32>) -> Array<U32>:
  match C:
    case Nil{}:
      tbl
    case Con{w, rest}:
      match w:
        case Nil{}:
          tbl
        case Con{w0, t1}:
          match t1:
            case Nil{}:
              tbl
            case Con{w1, t2}:
              match t2:
                case Nil{}:
                  tbl
                case Con{w2, t3}:
                  match t3:
                    case Nil{}:
                      tbl
                    case Con{w3, t4}:
                      match t4:
                        case Nil{}:
                          tbl
                        case Con{w4, t5}:
                          match t5:
                            case Nil{}:
                              fill_tbl_go(G, rest, U32.add(row, step), step,
                                fill_tbl_col(w0, w1, w2, w3, w4, G, row, tbl))
                            case Con{_, _}:
                              tbl

def mk_buf_tbl_depth(+G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
                     +gcount: U32, md: Maybe<Nat>) -> Buf5:
  match md:
    case None{}:
      NoBuf{}
    case Some{+d}:
      Buf5{Array.new(Nat, 10n, 0n), Array.new(+List<CWord>, 10n, Nil{}),
           fill_tbl_go(G, C, 0, gcount, Array.new(U32, d, 0)), 1n,
           U32.to_nat(gcount)}

def mk_buf_tbl_if(ok: Bool, +G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
                  +n: Nat) -> Buf5:
  match ok:
    case False{}:
      NoBuf{}
    case True{}:
      +gl = Groups.len_words(G)
      mk_buf_tbl_depth(G, C, U32.from_nat(gl), depth_for(Nat.mul(gl, n)))

def mk_buf_tbl(+nodup: Bool, +G: +List<+List<Nat>>, +C: +List<+List<Nat>>,
               +n: Nat) -> Buf5:
  match nodup:
    case False{}:
      NoBuf{}
    case True{}:
      mk_buf_tbl_if(Bool.and(all_len5(G), all_len5(C)), G, C, n)

# Pass 1: O(1) table-backed generation-stamped histogram with early abort.
type Hist5Res is Type:
  Hist5Ok{seen: Array<Nat>, tbl: Array<U32>, m: Nat, k: Nat, budget: Nat}
  Hist5Pruned{seen: Array<Nat>, tbl: Array<U32>}

def hist5_hit(seen: Array<Nat>, tbl: Array<U32>, +m: Nat, +k: Nat,
              seen_before: Bool, budget: Nat) -> Hist5Res:
  match seen_before:
    case True{}:
      match budget:
        case 0n:
          Hist5Pruned{seen, tbl}
        case 1n+bp:
          Hist5Ok{seen, tbl, Nat.add(1n, m), k, bp}
    case False{}:
      Hist5Ok{seen, tbl, Nat.add(1n, m), Nat.add(1n, k), budget}

def hist5_swap(tbl: Array<U32>, +gen: Nat, +m: Nat, +k: Nat, +budget: Nat,
               r: Array<Nat> & Nat) -> Hist5Res:
  (seen2, +old) = r
  hist5_hit(seen2, tbl, m, k, Nat.is_eq(old, gen), budget)

def hist5_same(seen: Array<Nat>, tbl: Array<U32>, +m: Nat, +k: Nat,
               +budget: Nat, skip_self: Bool) -> Hist5Res:
  match skip_self:
    case True{}:
      Hist5Pruned{seen, tbl}
    case False{}:
      Hist5Ok{seen, tbl, m, k, budget}

def hist5_step(seen: Array<Nat>, tbl: Array<U32>, +gen: Nat, +m: Nat, +k: Nat,
               +budget: Nat, +skip_self: Bool, +code: U32, same: Bool) -> Hist5Res:
  match same:
    case True{}:
      hist5_same(seen, tbl, m, k, budget, skip_self)
    case False{}:
      hist5_swap(tbl, gen, m, k, budget, Array.swap(Nat, seen, code, gen))

def hist5_tbl_done(seen: Array<Nat>, +gen: Nat, +m: Nat, +k: Nat, +budget: Nat,
                   +skip_self: Bool, r: Array<U32> & U32) -> Hist5Res:
  (tbl2, +code) = r
  hist5_step(seen, tbl2, gen, m, k, budget, skip_self, code, U32.is_eq(code, 682))

def hist5_one(+row: U32, +cw: CWord, seen: Array<Nat>, tbl: Array<U32>,
              +gen: Nat, +m: Nat, +k: Nat, +budget: Nat,
              +skip_self: Bool) -> Hist5Res:
  match cw:
    case CWord{+ci, grow, w}:
      hist5_tbl_done(seen, gen, m, k, budget, skip_self,
        Array.get(U32, tbl, U32.add(row, ci)))

def hist5_go(+row: U32, +S: +List<CWord>, +gen: Nat, +skip_self: Bool,
             st: Hist5Res) -> Hist5Res:
  match S:
    case Nil{}:
      st
    case Con{cw, rest}:
      match st:
        case Hist5Pruned{seen, tbl}:
          Hist5Pruned{seen, tbl}
        case Hist5Ok{seen, tbl, +m, +k, +budget}:
          hist5_go(row, rest, gen, skip_self,
            hist5_one(row, cw, seen, tbl, gen, m, k, budget, skip_self))

# Pass 2: O(1) table-backed bucketing + LCF drain + O(1) exact ThreeItem solver.
type Fill5State is Type:
  Fill5State{buckets: Array<+List<CWord>>, tbl: Array<U32>, touched: +List<U32>}

def fill5_get_done(+cw: CWord, +code: U32, tbl: Array<U32>,
                   +touched: +List<U32>,
                   r: Array<+List<CWord>> & +List<CWord>) -> Fill5State:
  (b2, +old) = r
  match old:
    case Nil{}:
      Fill5State{Array.set(+List<CWord>, b2, code, cw <> Nil{}), tbl,
                 code <> touched}
    case Con{h, t}:
      Fill5State{Array.set(+List<CWord>, b2, code, cw <> (h <> t)), tbl,
                 touched}

def fill5_step(+cw: CWord, +code: U32, same: Bool,
               buckets: Array<+List<CWord>>, tbl: Array<U32>,
               +touched: +List<U32>) -> Fill5State:
  match same:
    case True{}:
      Fill5State{buckets, tbl, touched}
    case False{}:
      fill5_get_done(cw, code, tbl, touched,
        Array.get(+List<CWord>, buckets, code))

def fill5_tbl_done(+cw: CWord, buckets: Array<+List<CWord>>,
                   +touched: +List<U32>,
                   r: Array<U32> & U32) -> Fill5State:
  (tbl2, +code) = r
  fill5_step(cw, code, U32.is_eq(code, 682), buckets, tbl2, touched)

def fill5_one(+row: U32, +cw: CWord, buckets: Array<+List<CWord>>,
              tbl: Array<U32>, +touched: +List<U32>) -> Fill5State:
  match cw:
    case CWord{+ci, +grow, +w}:
      fill5_tbl_done(CWord{ci, grow, w}, buckets, touched,
        Array.get(U32, tbl, U32.add(row, ci)))

def fill5_go(+row: U32, +S: +List<CWord>, st: Fill5State) -> Fill5State:
  match S:
    case Nil{}:
      st
    case Con{cw, rest}:
      match st:
        case Fill5State{buckets, tbl, +touched}:
          fill5_go(row, rest, fill5_one(row, cw, buckets, tbl, touched))

type RevCWordsLen is Data:
  RevCWordsLen{len: Nat, words: +List<CWord>}

def rev_cwords_len(+xs: +List<CWord>, +acc: +List<CWord>,
                   +len: Nat) -> RevCWordsLen:
  match xs:
    case Nil{}:
      RevCWordsLen{len, acc}
    case Con{cw, t}:
      rev_cwords_len(t, cw <> acc, Nat.add(1n, len))

type BigClass is Data:
  BigClass{fb: +List<Feedback.Color>, ws: +List<CWord>, len: Nat, clb: Nat}

def next_big_le(+len: Nat, +bs: +List<BigClass>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{h, t}:
      match h:
        case BigClass{fb2, ws2, len2, clb2}:
          Nat.is_le(len, len2)

def insert_big(+bc: BigClass, +len: Nat, +bs: +List<BigClass>,
               le: Bool) -> +List<BigClass>:
  match bs:
    case Nil{}:
      bc <> Nil{}
    case Con{h, t}:
      match le:
        case True{}:
          bc <> (h <> t)
        case False{}:
          h <> insert_big(bc, len, t, next_big_le(len, t))

def emit_bigs(+bs: +List<BigClass>, +rem_lb: Nat, +acc: +List<Item>) -> +List<Item>:
  match bs:
    case Nil{}:
      acc
    case Con{bc, rest}:
      match bc:
        case BigClass{+fb, +ws, +len, +clb}:
          +clb2 = Nat.sub(Nat.add(len, len), 1n)
          emit_bigs(rest, Nat.add(clb2, rem_lb),
            ClassItem{fb, ws, len, rem_lb} <> (Add{fb, rem_lb} <> acc))

def two_tree(+w1: +List<Nat>, +w2: +List<Nat>) -> Tree.Tree:
  Tree.Node{w1, Tree.Child{feedback_fast(w1, w2), Tree.Node{w2, Nil{}}} <> Nil{}}

type ThreeRes is Type:
  ThreeRes{tree: Tree.Tree, cost: Nat, tbl: Array<U32>}

def three_tree_sep(+g: +List<Nat>, +c1: U32, +w1: +List<Nat>,
                   +c2: U32, +w2: +List<Nat>) -> Tree.Tree:
  Tree.Node{g,
    Tree.Child{decode_fb5(c1), Tree.Node{w1, Nil{}}}
    <> (Tree.Child{decode_fb5(c2), Tree.Node{w2, Nil{}}} <> Nil{})}

def three_tree_6(+w1: +List<Nat>, +c12: U32, +w2: +List<Nat>,
                 +c23: U32, +w3: +List<Nat>) -> Tree.Tree:
  Tree.Node{w1,
    Tree.Child{decode_fb5(c12),
      Tree.Node{w2, Tree.Child{decode_fb5(c23), Tree.Node{w3, Nil{}}} <> Nil{}}}
    <> Nil{}}

def three_s3_cmp(+w1: +List<Nat>, +c12: U32, +w2: +List<Nat>, +c23: U32,
                 +w3: +List<Nat>, +c31: U32, +c32: U32,
                 same: Bool, tbl: Array<U32>) -> ThreeRes:
  match same:
    case False{}:
      ThreeRes{three_tree_sep(w3, c31, w1, c32, w2), 5n, tbl}
    case True{}:
      ThreeRes{three_tree_6(w1, c12, w2, c23, w3), 6n, tbl}

def three_s3_b(+w1: +List<Nat>, +c12: U32, +w2: +List<Nat>, +c23: U32,
               +w3: +List<Nat>, +c31: U32, r: Array<U32> & U32) -> ThreeRes:
  (tbl, +c32) = r
  three_s3_cmp(w1, c12, w2, c23, w3, c31, c32, U32.is_eq(c31, c32), tbl)

def three_s3_a(+w1: +List<Nat>, +c12: U32, +ci2: U32, +w2: +List<Nat>,
               +c23: U32, +gr3: U32, +w3: +List<Nat>,
               r: Array<U32> & U32) -> ThreeRes:
  (tbl, +c31) = r
  three_s3_b(w1, c12, w2, c23, w3, c31, Array.get(U32, tbl, U32.add(gr3, ci2)))

def three_s2_cmp(+ci1: U32, +w1: +List<Nat>, +c12: U32,
                 +ci2: U32, +w2: +List<Nat>, +c21: U32, +c23: U32,
                 +gr3: U32, +w3: +List<Nat>,
                 same: Bool, tbl: Array<U32>) -> ThreeRes:
  match same:
    case False{}:
      ThreeRes{three_tree_sep(w2, c21, w1, c23, w3), 5n, tbl}
    case True{}:
      three_s3_a(w1, c12, ci2, w2, c23, gr3, w3,
        Array.get(U32, tbl, U32.add(gr3, ci1)))

def three_s2_b(+ci1: U32, +w1: +List<Nat>, +c12: U32, +ci2: U32, +w2: +List<Nat>,
               +c21: U32, +gr3: U32, +w3: +List<Nat>,
               r: Array<U32> & U32) -> ThreeRes:
  (tbl, +c23) = r
  three_s2_cmp(ci1, w1, c12, ci2, w2, c21, c23, gr3, w3,
    U32.is_eq(c21, c23), tbl)

def three_s2_a(+ci1: U32, +w1: +List<Nat>, +c12: U32, +ci2: U32, +gr2: U32,
               +w2: +List<Nat>, +ci3: U32, +gr3: U32, +w3: +List<Nat>,
               r: Array<U32> & U32) -> ThreeRes:
  (tbl, +c21) = r
  three_s2_b(ci1, w1, c12, ci2, w2, c21, gr3, w3,
    Array.get(U32, tbl, U32.add(gr2, ci3)))

def three_s1_cmp(+ci1: U32, +w1: +List<Nat>, +c12: U32, +c13: U32,
                 +ci2: U32, +gr2: U32, +w2: +List<Nat>,
                 +ci3: U32, +gr3: U32, +w3: +List<Nat>,
                 same: Bool, tbl: Array<U32>) -> ThreeRes:
  match same:
    case False{}:
      ThreeRes{three_tree_sep(w1, c12, w2, c13, w3), 5n, tbl}
    case True{}:
      three_s2_a(ci1, w1, c12, ci2, gr2, w2, ci3, gr3, w3,
        Array.get(U32, tbl, U32.add(gr2, ci1)))

def three_s1_b(+ci1: U32, +w1: +List<Nat>, +c12: U32,
               +ci2: U32, +gr2: U32, +w2: +List<Nat>,
               +ci3: U32, +gr3: U32, +w3: +List<Nat>,
               r: Array<U32> & U32) -> ThreeRes:
  (tbl, +c13) = r
  three_s1_cmp(ci1, w1, c12, c13, ci2, gr2, w2, ci3, gr3, w3,
    U32.is_eq(c12, c13), tbl)

def three_s1_a(+ci1: U32, +gr1: U32, +w1: +List<Nat>,
               +ci2: U32, +gr2: U32, +w2: +List<Nat>,
               +ci3: U32, +gr3: U32, +w3: +List<Nat>,
               r: Array<U32> & U32) -> ThreeRes:
  (tbl, +c12) = r
  three_s1_b(ci1, w1, c12, ci2, gr2, w2, ci3, gr3, w3,
    Array.get(U32, tbl, U32.add(gr1, ci3)))

def solve_three_tbl(+cw1: CWord, +cw2: CWord, +cw3: CWord,
                    tbl: Array<U32>) -> ThreeRes:
  match cw1:
    case CWord{+ci1, +gr1, +w1}:
      match cw2:
        case CWord{+ci2, +gr2, +w2}:
          match cw3:
            case CWord{+ci3, +gr3, +w3}:
              three_s1_a(ci1, gr1, w1, ci2, gr2, w2, ci3, gr3, w3,
                Array.get(U32, tbl, U32.add(gr1, ci2)))

type Drain5State is Type:
  Drain5State{buckets: Array<+List<CWord>>, tbl: Array<U32>, rem_lb: Nat,
              items: +List<Item>, bigs: +List<BigClass>}

def drain5_ge2_emit(+fb: +List<Feedback.Color>, +rem_lb: Nat,
                    +items: +List<Item>, +bigs: +List<BigClass>,
                    buckets: Array<+List<CWord>>, tbl: Array<U32>,
                    +len: Nat, +ws: +List<CWord>, +clb: Nat) -> Drain5State:
  Drain5State{buckets, tbl, rem_lb, items,
    insert_big(BigClass{fb, ws, len, clb}, len, bigs, next_big_le(len, bigs))}

def drain5_add_ge2(+fb: +List<Feedback.Color>, +rem_lb: Nat,
                   +items: +List<Item>, +bigs: +List<BigClass>,
                   buckets: Array<+List<CWord>>, tbl: Array<U32>,
                   rl: RevCWordsLen) -> Drain5State:
  match rl:
    case RevCWordsLen{+len, +ws}:
      drain5_ge2_emit(fb, rem_lb, items, bigs, buckets, tbl, len, ws,
        Nat.sub(Nat.add(len, len), 1n))

def drain5_add_three(+fb: +List<Feedback.Color>, +rem_lb: Nat,
                     +items: +List<Item>, +bigs: +List<BigClass>,
                     buckets: Array<+List<CWord>>,
                     tr: ThreeRes) -> Drain5State:
  match tr:
    case ThreeRes{tree, +cost, tbl2}:
      Drain5State{buckets, tbl2, Nat.add(cost, rem_lb),
        DoneItem{fb, tree, cost} <> items, bigs}

def cword_w(+cw: CWord) -> +List<Nat>:
  match cw:
    case CWord{ci, grow, w}:
      w

def drain5_add(+code: U32, +rem_lb: Nat, +items: +List<Item>,
               +bigs: +List<BigClass>, buckets: Array<+List<CWord>>,
               tbl: Array<U32>, +rws: +List<CWord>) -> Drain5State:
  match rws:
    case Nil{}:
      +fb = decode_fb5(code)
      Drain5State{buckets, tbl, rem_lb,
        ClassItem{fb, Nil{}, 0n, rem_lb} <> (Add{fb, rem_lb} <> items), bigs}
    case Con{+cw, +wt}:
      match wt:
        case Nil{}:
          Drain5State{buckets, tbl, Nat.add(1n, rem_lb),
            OneItem{decode_fb5(code), cword_w(cw)} <> items, bigs}
        case Con{+cw2, +wt2}:
          match wt2:
            case Nil{}:
              Drain5State{buckets, tbl, Nat.add(3n, rem_lb),
                TwoItem{decode_fb5(code), cword_w(cw2), cword_w(cw)} <> items,
                bigs}
            case Con{+cw3, +wt3}:
              match wt3:
                case Nil{}:
                  drain5_add_three(decode_fb5(code), rem_lb, items, bigs, buckets,
                    solve_three_tbl(cw3, cw2, cw, tbl))
                case Con{+cw4, +wt4}:
                  drain5_add_ge2(decode_fb5(code), rem_lb, items, bigs, buckets, tbl,
                    rev_cwords_len(wt4, cw4 <> (cw3 <> (cw2 <> (cw <> Nil{}))), 4n))

def drain5_swap(+code: U32, +rem_lb: Nat, +items: +List<Item>,
                +bigs: +List<BigClass>, tbl: Array<U32>,
                r: Array<+List<CWord>> & +List<CWord>) -> Drain5State:
  (b2, +rws) = r
  drain5_add(code, rem_lb, items, bigs, b2, tbl, rws)

def drain5_go(+gn: Nat, +touched: +List<U32>, st: Drain5State) -> Drain5State:
  match touched:
    case Nil{}:
      st
    case Con{+code, +rest}:
      match st:
        case Drain5State{buckets, tbl, +rem_lb, +items, +bigs}:
          drain5_go(gn, rest,
            drain5_swap(code, rem_lb, items, bigs, tbl,
              Array.swap(+List<CWord>, buckets, code, Nil{})))

# The scan result: the table rides through and `k` is the largest count so far.
# The dedup scratch array never leaves the scan, so no consumer or proof state
# has to mention it.
type CKRes is Type:
  CKRes{tbl: Array<U32>, k: Nat}

# One pass over the class per guess, reusing the proven histogram fold: the
# `k` of a `Hist5Ok` is the number of distinct feedback codes of that guess on
# the class. `fuel` counts the guesses still to process, `more` says whether a
# further guess follows the current one, and the row of each pass is its guess
# index, so the scan never reads a table row past the guess list. The dedup
# buffer is allocated once per class and reused: every pass raises `gen`, which
# makes the stamps of the previous pass stale.
def ck_loop(+fuel: Nat, +i: Nat, +C: +List<CWord>, +gen: Nat, +m: Nat,
            +kmax: Nat, hist: Hist5Res, more: Bool) -> CKRes:
  match fuel:
    case 0n:
      match hist:
        case Hist5Pruned{seen2, tbl2}:
          CKRes{tbl2, kmax}
        case Hist5Ok{seen2, tbl2, +m2, +k2, budget}:
          CKRes{tbl2, Nat.max(kmax, k2)}
    case 1n+p:
      match hist:
        case Hist5Pruned{seen2, tbl2}:
          CKRes{tbl2, kmax}
        case Hist5Ok{seen2, tbl2, +m2, +k2, budget}:
          match more:
            case False{}:
              CKRes{tbl2, Nat.max(kmax, k2)}
            case True{}:
              ck_loop(p, Nat.add(1n, i), C, Nat.add(1n, gen), m,
                Nat.max(kmax, k2),
                hist5_go(U32.from_nat(Nat.add(1n, i)), C, Nat.add(1n, gen),
                  False{}, Hist5Ok{seen2, tbl2, 0n, 0n, m}),
                Nat.is_le(2n, p))

def class_k_start_b(empty: Bool, +ws: +List<CWord>, +m: Nat, +gn: Nat,
                    tbl: Array<U32>) -> CKRes:
  match empty:
    case True{}:
      CKRes{tbl, 0n}
    case False{}:
      ck_loop(gn, 0n, ws, 1n, m, 0n,
        hist5_go(0, ws, 1n, False{}, Hist5Ok{Array.new(Nat, 10n, 0n), tbl,
          0n, 0n, m}),
        Nat.is_le(2n, gn))

def class_k_start(+ws: +List<CWord>, +m: Nat, +gn: Nat,
                  tbl: Array<U32>) -> CKRes:
  class_k_start_b(Nat.is_le(gn, 0n), ws, m, gn, tbl)

def bigs_total(+bigs: +List<BigClass>, +acc: Nat) -> Nat:
  match bigs:
    case Nil{}:
      acc
    case Con{bc, rest}:
      match bc:
        case BigClass{fb, ws, len, +clb}:
          bigs_total(rest, Nat.add(clb, acc))

# The class-independent part of the lower bound: `n` plus the class lower
# bounds of the non-big items. A solved class of three candidates contributes
# its depth bound `5`, not its exact tree cost (five or six), so this stays a
# function of the class sizes and keeps the capacity walk's running total
# comparable with the class list.
def cap_base(+n: Nat, +items: +List<Item>, +acc: Nat) -> Nat:
  match items:
    case Nil{}:
      acc
    case Con{it, rest}:
      match it:
        case Begin{g}:
          cap_base(n, rest, acc)
        case ClassItem{fb, cws, +wlen, tlb}:
          cap_base(n, rest, Nat.add(Nat.sub(Nat.add(wlen, wlen), 1n), acc))
        case OneItem{fb, w}:
          cap_base(n, rest, Nat.add(1n, acc))
        case TwoItem{fb, w1, w2}:
          cap_base(n, rest, Nat.add(3n, acc))
        case DoneItem{fb, tree, cost}:
          cap_base(n, rest, Nat.add(5n, acc))
        case Add{fb, tlb}:
          cap_base(n, rest, acc)
        case End{}:
          Nat.add(n, acc)

type CapRes is Type:
  CapSkip{tbl: Array<U32>}
  CapOk{bigs: +List<BigClass>, tbl: Array<U32>}

def rev_bigs(+bs: +List<BigClass>, +acc: +List<BigClass>) -> +List<BigClass>:
  match bs:
    case Nil{}:
      acc
    case Con{b, t}:
      rev_bigs(t, b <> acc)

def bigs_len(+bs: +List<BigClass>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{b, t}:
      Nat.add(1n, bigs_len(t))

def ck_cheap(+m: Nat, tbl: Array<U32>) -> CKRes:
  CKRes{tbl, m}

def class_k_opt(big: Bool, +ws: +List<CWord>, +m: Nat, +gn: Nat,
                tbl: Array<U32>) -> CKRes:
  match big:
    case False{}:
      ck_cheap(m, tbl)
    case True{}:
      class_k_start(ws, m, gn, tbl)

# One class per two steps. A positive phase starts the k pass for the list head
# and zero consumes it; the walk is structural on the class list, so it needs no
# fuel. `stop` is checked on entry, so the walk ends as soon as the running
# capacity gain reaches the best cost. The table rides in `st` and is handed
# back through CapOk/CapSkip. The rebuilt list keeps the input order and the
# input `clb` fields, because `emit_bigs` recomputes the class bound.
def cap_walk(+bs: +List<BigClass>, +phase: Nat, stop: Bool,
             +acc: +List<BigClass>, +gain: Nat, +total0: Nat,
             +best: SolveRef.Best, +gn: Nat, st: CKRes) -> CapRes:
  match bs:
    case Nil{}:
      match phase:
        case 0n:
          match stop:
            case True{}:
              match st:
                case CKRes{tbl, k}:
                  CapSkip{tbl}
            case False{}:
              match st:
                case CKRes{tbl, k}:
                  CapOk{rev_bigs(acc, Nil{}), tbl}
        case 1n+hp:
          match stop:
            case True{}:
              match st:
                case CKRes{tbl, k}:
                  CapSkip{tbl}
            case False{}:
              match st:
                case CKRes{tbl, k}:
                  CapOk{rev_bigs(acc, Nil{}), tbl}
    case Con{bc, rest}:
      match bc:
        case BigClass{+fb, +ws, +len, +clb}:
          match phase:
            case 1n+hp:
              match stop:
                case True{}:
                  match st:
                    case CKRes{tbl, k}:
                      CapSkip{tbl}
                case False{}:
                  match st:
                    case CKRes{tbl, k}:
                      cap_walk(bs, hp, False{}, acc, gain, total0, best, gn,
                        class_k_opt(Nat.is_le(16n, len), ws, len, gn, tbl))
            case 0n:
              match stop:
                case True{}:
                  match st:
                    case CKRes{tbl, k}:
                      CapSkip{tbl}
                case False{}:
                  match st:
                    case CKRes{tbl, +k}:
                      +clb2 = Nat.max(clb, capbound(len, k))
                      +gain2 = Nat.add(gain, Nat.sub(clb2, clb))
                      cap_walk(rest, 1n,
                        Nat.is_le(best_cost(best), Nat.add(total0, gain2)),
                        BigClass{fb, ws, len, clb} <> acc, gain2, total0,
                        best, gn, CKRes{tbl, k})

def finish_cap(r: CapRes, +g: +List<Nat>, seen: Array<Nat>, +gen2: Nat,
               +gn: Nat, +rem_lb: Nat, +items: +List<Item>,
               buckets3: Array<+List<CWord>>) -> GuessRes:
  match r:
    case CapSkip{tbl}:
      GuessRes{Nil{}, Buf5{seen, buckets3, tbl, gen2, gn}}
    case CapOk{+bigs2, tbl}:
      GuessRes{Begin{g} <> emit_bigs(bigs2, rem_lb, items),
               Buf5{seen, buckets3, tbl, gen2, gn}}

# The capacity walk runs only for nodes with at least 512 candidates: below
# that the class scans cost more than the bound saves. `cap_base` is the
# class-independent part of the lower bound and `bigs_total` adds the depth
# bound of every big class, so `total0` is the walk's starting value.
def finish_node(ok: Bool, +g: +List<Nat>, seen: Array<Nat>, +gen2: Nat,
                +gn: Nat, +rem_lb: Nat, +items: +List<Item>,
                +bigs: +List<BigClass>, buckets3: Array<+List<CWord>>,
                tbl3: Array<U32>, +best: SolveRef.Best) -> GuessRes:
  match ok:
    case False{}:
      GuessRes{Begin{g} <> emit_bigs(bigs, rem_lb, items),
               Buf5{seen, buckets3, tbl3, gen2, gn}}
    case True{}:
      finish_cap(cap_walk(bigs, 1n, False{}, Nil{}, 0n,
                   bigs_total(bigs, cap_base(n, items, 0n)),
                   best, gn, ck_cheap(0n, tbl3)),
        g, seen, gen2, gn, rem_lb, items, buckets3)

def finish_drain5(+g: +List<Nat>, seen: Array<Nat>, +gen2: Nat, +gn: Nat,
                  +best: SolveRef.Best, +n: Nat, dr: Drain5State) -> GuessRes:
  match dr:
    case Drain5State{buckets3, tbl3, +rem_lb, +items, +bigs}:
      finish_node(Nat.is_le(512n, n),
        g, seen, gen2, gn, rem_lb, items, bigs, buckets3, tbl3, best)

def run_drain5(+g: +List<Nat>, +n: Nat, seen: Array<Nat>, +gen2: Nat,
               +gn: Nat, +best: SolveRef.Best, fs: Fill5State) -> GuessRes:
  match fs:
    case Fill5State{buckets2, tbl2, +touched}:
      finish_drain5(g, seen, gen2, gn, best, n,
        drain5_go(gn, touched,
          Drain5State{buckets2, tbl2, n, End{} <> Nil{}, Nil{}}))

def schedule5_lb(+row: U32, +g: +List<Nat>, +S: +List<CWord>, +n: Nat,
                 seen: Array<Nat>, buckets: Array<+List<CWord>>,
                 tbl: Array<U32>, +gen2: Nat, +gn: Nat, +best: SolveRef.Best,
                 skip: Bool) -> GuessRes:
  match skip:
    case True{}:
      GuessRes{Nil{}, Buf5{seen, buckets, tbl, gen2, gn}}
    case False{}:
      run_drain5(g, n, seen, gen2, gn, best,
        fill5_go(row, S, Fill5State{buckets, tbl, Nil{}}))

def schedule5_usable(+row: U32, +g: +List<Nat>, +S: +List<CWord>, +n: Nat,
                     +best: SolveRef.Best, seen: Array<Nat>,
                     buckets: Array<+List<CWord>>, tbl: Array<U32>,
                     +gen2: Nat, +gn: Nat, +m: Nat, +k: Nat,
                     usable: Bool) -> GuessRes:
  match usable:
    case False{}:
      GuessRes{Nil{}, Buf5{seen, buckets, tbl, gen2, gn}}
    case True{}:
      +lb = Nat.sub(Nat.add(n, Nat.add(m, m)), k)
      schedule5_lb(row, g, S, n, seen, buckets, tbl, gen2, gn, best,
        skippable(best, lb))

def schedule5_hist(+row: U32, +g: +List<Nat>, +S: +List<CWord>, +n: Nat,
                   +best: SolveRef.Best, buckets: Array<+List<CWord>>,
                   +gen: Nat, +gn: Nat, hr: Hist5Res) -> GuessRes:
  match hr:
    case Hist5Pruned{seen2, tbl2}:
      GuessRes{Nil{}, Buf5{seen2, buckets, tbl2, Nat.add(1n, gen), gn}}
    case Hist5Ok{seen2, tbl2, +m, +k, budget}:
      schedule5_usable(row, g, S, n, best, seen2, buckets, tbl2,
        Nat.add(1n, gen), gn, m, k,
        Bool.or(Nat.is_lt(m, n), Nat.is_le(2n, k)))

def budget_for(+n: Nat, +best: SolveRef.Best, skip_self: Bool) -> Nat:
  match skip_self:
    case True{}:
      Nat.sub(Nat.sub(best_cost(best), Nat.add(n, n)), 1n)
    case False{}:
      Nat.sub(best_cost(best), Nat.add(n, n))

def guess_body_buf_ge2(+row: U32, +g: +List<Nat>, +S: +List<CWord>, +n: Nat,
                       +best: SolveRef.Best, +skip_self: Bool, buf: Buf5) -> GuessRes:
  match buf:
    case NoBuf{}:
      +fg = fgroups_build_fast(g, cwords_words(S), Nil{})
      GuessRes{schedule_fguess(True{}, g, fg, n, best, fgroups_smaller(n, fg)),
               NoBuf{}}
    case Buf5{seen, buckets, tbl, +gen, +gn}:
      +budget0 = budget_for(n, best, skip_self)
      schedule5_hist(row, g, S, n, best, buckets, gen, gn,
        hist5_go(row, S, gen, skip_self, Hist5Ok{seen, tbl, 0n, 0n, budget0}))

# How many candidates `S` holds, capped at two. Reading the shape in a
# definition of its own keeps `S` intact, so the caller can pass the same list
# on instead of rebuilding it.
type CWordsShape is Type:
  ShapeNil{}
  ShapeOne{}
  ShapeMany{}

def cwords_shape(+S: +List<CWord>) -> CWordsShape:
  match S:
    case Nil{}:
      ShapeNil{}
    case Con{cw, t}:
      match t:
        case Nil{}:
          ShapeOne{}
        case Con{cw2, t2}:
          ShapeMany{}

# The one-candidate case, reached only when `cwords_shape` reported one. The
# empty arm cannot be reached with a length that matches `n`, and it returns
# the neutral result so the definition stays total.
def guess_body_buf_one(+row: U32, +g: +List<Nat>, +S: +List<CWord>, +n: Nat,
                       +best: SolveRef.Best, +skip_self: Bool,
                       buf: Buf5) -> GuessRes:
  match S:
    case Nil{}:
      GuessRes{Nil{}, buf}
    case Con{cw, t}:
      GuessRes{schedule_one_guess(g, best, word_eq_fast(g, cword_w(cw))), buf}

def guess_body_shape(sh: CWordsShape, +row: U32, +g: +List<Nat>,
                     +S: +List<CWord>, +n: Nat, +best: SolveRef.Best,
                     +skip_self: Bool, buf: Buf5) -> GuessRes:
  match sh:
    case ShapeNil{}:
      +fg = fgroups_build_fast(g, Nil{}, Nil{})
      GuessRes{schedule_fguess(True{}, g, fg, 0n, best, fgroups_smaller(0n, fg)),
               buf}
    case ShapeOne{}:
      guess_body_buf_one(row, g, S, n, best, skip_self, buf)
    case ShapeMany{}:
      guess_body_buf_ge2(row, g, S, n, best, skip_self, buf)

def guess_body_buf(+row: U32, +g: +List<Nat>, +S: +List<CWord>, +n: Nat,
                   +best: SolveRef.Best, +skip_self: Bool, buf: Buf5) -> GuessRes:
  guess_body_shape(cwords_shape(S), row, g, S, n, best, skip_self, buf)

def guess_items_mem_buf(+row: U32, +g: +List<Nat>, +S: +List<CWord>, +n: Nat,
                        +best: SolveRef.Best, +skip_self: Bool, buf: Buf5,
                        in_s: Bool) -> GuessRes:
  match in_s:
    case True{}:
      guess_body_buf(row, g, S, n, best, skip_self, buf)
    case False{}:
      GuessRes{Nil{}, buf}

def guess_items_nodup_buf(+row: U32, +g: +List<Nat>, +S: +List<CWord>, +n: Nat,
                          +best: SolveRef.Best, +skip_self: Bool, buf: Buf5,
                          le_2n: Bool) -> GuessRes:
  match le_2n:
    case False{}:
      guess_body_buf(row, g, S, n, best, skip_self, buf)
    case True{}:
      guess_items_mem_buf(row, g, S, n, best, skip_self, buf,
        member_word_fast(g, cwords_words(S)))

def guess_items_buf(+nodup: Bool, +row: U32, +g: +List<Nat>, +S: +List<CWord>,
                    +n: Nat, +floor: Nat, +best: SolveRef.Best, buf: Buf5) -> GuessRes:
  match nodup:
    case True{}:
      +skip_self = Nat.is_eq(floor, Nat.add(n, n))
      guess_items_nodup_buf(row, g, S, n, best, skip_self, buf,
        skippable(best, Nat.add(n, n)))
    case False{}:
      +ws = cwords_words(S)
      GuessRes{
        guess_items_go(False{}, g, ws, n, best, skippable(best, pre_lb(n, g, ws))),
        buf}

type StepRes is Type:
  StepRes{best: SolveRef.Best, buf: Buf5}

def step_res_best(r: StepRes) -> SolveRef.Best:
  match r:
    case StepRes{best, buf}:
      best

def step_res_buf(r: StepRes) -> Buf5:
  match r:
    case StepRes{best, buf}:
      buf

def gres_buf(gres: GuessRes) -> Buf5:
  match gres:
    case GuessRes{_, buf}:
      buf

def dummy_step_zero() -> StepRes:
  StepRes{dummy_zero(), NoBuf{}}

def step(+fuel: Nat, +gs: GList, +phase: Nat, +cs: +List<Item>,
         +glist_G: GList, +S: +List<CWord>, +n: Nat, +nodup: Bool,
         +floor: Nat, +inf: Nat, +g: +List<Nat>, +kids: +List<Tree.Child>,
         +sum: Nat, +best: SolveRef.Best, pending: StepRes, skip: Bool,
         done: Bool, gres: GuessRes) -> StepRes:
  match fuel:
    case 0n:
      match gs:
        case GEnd{}:
          match cs:
            case Nil{}:
              StepRes{best, gres_buf(gres)}
            case Con{item, rest}:
              match item:
                case Begin{g2}:
                  step(0n, GEnd{}, phase, rest, glist_G, S, n, nodup,
                       floor, inf, g2, Nil{}, 0n, best, pending, False{},
                       False{}, gres)
                case ClassItem{fb, words, wlen, tail_lb}:
                  StepRes{dummy_inf(inf), gres_buf(gres)}
                case OneItem{fb, w}:
                  StepRes{dummy_inf(inf), gres_buf(gres)}
                case TwoItem{fb, w1, w2}:
                  StepRes{dummy_inf(inf), gres_buf(gres)}
                case DoneItem{fb, tree, cost}:
                  StepRes{dummy_inf(inf), gres_buf(gres)}
                case Add{fb, tail_lb}:
                  match pending:
                    case StepRes{pbest, pbuf}:
                      match pbest:
                        case SolveRef.Best{tree, cost}:
                          step(0n, GEnd{}, phase, rest, glist_G, S, n, nodup,
                               floor, inf, g, Tree.Child{fb, tree} <> kids,
                               SolveRef.sat_add(inf, sum, cost), best,
                               dummy_step_zero(), skip, False{}, gres)
                case End{}:
                  step(0n, GEnd{}, phase, rest, glist_G, S, n, nodup,
                       floor, inf, Nil{}, Nil{}, 0n,
                       SolveRef.finish_guess(inf, g, kids, sum, n, best),
                       dummy_step_zero(), False{}, False{}, gres)
        case GThen{grest}:
          match cs:
            case Nil{}:
              step(0n, grest, phase, Nil{}, glist_G, S, n, nodup,
                   floor, inf, Nil{}, Nil{}, 0n, best, dummy_step_zero(),
                   False{}, False{}, gres)
            case Con{item, rest}:
              StepRes{dummy_inf(inf), gres_buf(gres)}
        case GTry{+row2, +g2, +grest}:
          match cs:
            case Nil{}:
              step(0n, grest, phase, Begin{g2} <> (End{} <> Nil{}),
                   glist_G, S, n, nodup, floor, inf, Nil{}, Nil{}, 0n, best,
                   dummy_step_zero(), False{}, False{}, gres)
            case Con{item, rest}:
              match item:
                case Begin{g3}:
                  step(0n, GTry{row2, g2, grest}, phase, rest, glist_G, S, n,
                       nodup, floor, inf, g3, Nil{}, 0n, best, pending, False{},
                       False{}, gres)
                case ClassItem{fb, words, wlen, tail_lb}:
                  StepRes{dummy_inf(inf), gres_buf(gres)}
                case OneItem{fb, w}:
                  StepRes{dummy_inf(inf), gres_buf(gres)}
                case TwoItem{fb, w1, w2}:
                  StepRes{dummy_inf(inf), gres_buf(gres)}
                case DoneItem{fb, tree, cost}:
                  StepRes{dummy_inf(inf), gres_buf(gres)}
                case Add{fb, tail_lb}:
                  match pending:
                    case StepRes{pbest, pbuf}:
                      match pbest:
                        case SolveRef.Best{tree, cost}:
                          step(0n, GTry{row2, g2, grest}, phase, rest, glist_G, S,
                               n, nodup, floor, inf, g, Tree.Child{fb, tree} <> kids,
                               SolveRef.sat_add(inf, sum, cost), best,
                               dummy_step_zero(), skip, False{}, gres)
                case End{}:
                  step(0n, GTry{row2, g2, grest}, phase, rest, glist_G, S, n,
                       nodup, floor, inf, Nil{}, Nil{}, 0n,
                       SolveRef.finish_guess(inf, g, kids, sum, n, best),
                       dummy_step_zero(), False{}, False{}, gres)
    case 1n+p:
      match gs:
        case GEnd{}:
          match phase:
            case 1n+q:
              match gres:
                case GuessRes{items, buf2}:
                  step(fuel, GEnd{}, q, items, glist_G, S, n, nodup,
                       floor, inf, Nil{}, Nil{}, 0n, best, dummy_step_zero(),
                       False{}, False{}, GuessRes{Nil{}, buf2})
            case 0n:
              match cs:
                case Nil{}:
                  StepRes{best, gres_buf(gres)}
                case Con{item, rest}:
                  match item:
                    case Begin{g2}:
                      step(fuel, GEnd{}, 0n, rest, glist_G, S, n, nodup,
                           floor, inf, g2, Nil{}, 0n, best, dummy_step_zero(),
                           False{}, False{}, gres)
                    case ClassItem{fb, words, +wlen, +tail_lb}:
                      match skip:
                        case True{}:
                          step(fuel, GEnd{}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, g, kids, sum, best,
                               dummy_step_zero(), True{}, False{}, gres)
                        case False{}:
                          match gres:
                            case GuessRes{_, buf}:
                              +b0 = dummy_inf(Nat.sub(best_cost(best), Nat.add(sum, tail_lb)))
                              +fl = init_floor(wlen)
                              step(fuel, GEnd{}, 0n, rest, glist_G, S, n,
                                   nodup, floor, inf, g, kids, sum, best,
                                   step(p, child_glist(nodup, words, wlen, b0, glist_G),
                                        0n, Nil{}, glist_G, words, wlen, nodup, fl,
                                        inf, Nil{}, Nil{}, 0n, b0, dummy_step_zero(),
                                        False{}, is_floor_hit(nodup, fl, b0),
                                        GuessRes{Nil{}, buf}),
                                   False{}, False{}, GuessRes{Nil{}, NoBuf{}})
                    case OneItem{fb, w}:
                      match skip:
                        case True{}:
                          step(fuel, GEnd{}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, g, kids, sum, best,
                               dummy_step_zero(), True{}, False{}, gres)
                        case False{}:
                          step(fuel, GEnd{}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, g,
                               Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
                               SolveRef.sat_add(inf, sum, 1n), best,
                               dummy_step_zero(), False{}, False{}, gres)
                    case TwoItem{fb, w1, w2}:
                      match skip:
                        case True{}:
                          step(fuel, GEnd{}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, g, kids, sum, best,
                               dummy_step_zero(), True{}, False{}, gres)
                        case False{}:
                          step(fuel, GEnd{}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, g,
                               Tree.Child{fb, two_tree(w1, w2)} <> kids,
                               SolveRef.sat_add(inf, sum, 3n), best,
                               dummy_step_zero(), False{}, False{}, gres)
                    case DoneItem{fb, tree, cost}:
                      match skip:
                        case True{}:
                          step(fuel, GEnd{}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, g, kids, sum, best,
                               dummy_step_zero(), True{}, False{}, gres)
                        case False{}:
                          step(fuel, GEnd{}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, g,
                               Tree.Child{fb, tree} <> kids,
                               SolveRef.sat_add(inf, sum, cost), best,
                               dummy_step_zero(), False{}, False{}, gres)
                    case Add{fb, +tail_lb}:
                      match pending:
                        case StepRes{pbest, pbuf}:
                          match pbest:
                            case SolveRef.Best{tree, +cost}:
                              match skip:
                                case True{}:
                                  step(fuel, GEnd{}, 0n, rest, glist_G, S, n,
                                       nodup, floor, inf, g, kids, sum, best,
                                       dummy_step_zero(), True{}, False{}, gres)
                                case False{}:
                                  +sum2 = SolveRef.sat_add(inf, sum, cost)
                                  step(fuel, GEnd{}, 0n, rest, glist_G, S, n,
                                       nodup, floor, inf, g,
                                       Tree.Child{fb, tree} <> kids,
                                       sum2, best, dummy_step_zero(),
                                       skippable(best, Nat.add(sum2, tail_lb)),
                                       False{}, GuessRes{Nil{}, pbuf})
                    case End{}:
                      match skip:
                        case True{}:
                          step(fuel, GEnd{}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, Nil{}, Nil{}, 0n, best,
                               dummy_step_zero(), False{}, False{}, gres)
                        case False{}:
                          +best2 = SolveRef.finish_guess(inf, g, kids, sum, n, best)
                          step(fuel, GEnd{}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, Nil{}, Nil{}, 0n, best2,
                               dummy_step_zero(), False{},
                               is_floor_hit(nodup, floor, best2), gres)
        case GThen{grest}:
          match phase:
            case 1n+q:
              match gres:
                case GuessRes{items, buf2}:
                  step(fuel, GThen{grest}, q, items, glist_G, S, n, nodup,
                       floor, inf, Nil{}, Nil{}, 0n, best, dummy_step_zero(),
                       False{}, False{}, GuessRes{Nil{}, buf2})
            case 0n:
              match cs:
                case Nil{}:
                  match done:
                    case True{}:
                      StepRes{best, gres_buf(gres)}
                    case False{}:
                      +fl2 = Nat.add(n, n)
                      step(fuel, grest, 0n, Nil{}, glist_G, S, n, nodup, fl2,
                           inf, Nil{}, Nil{}, 0n, best, dummy_step_zero(),
                           False{}, is_floor_hit(nodup, fl2, best), gres)
                case Con{item, rest}:
                  match item:
                    case Begin{g2}:
                      step(fuel, GThen{grest}, 0n, rest, glist_G, S, n, nodup,
                           floor, inf, g2, Nil{}, 0n, best, dummy_step_zero(),
                           False{}, False{}, gres)
                    case ClassItem{fb, words, +wlen, +tail_lb}:
                      match skip:
                        case True{}:
                          step(fuel, GThen{grest}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, g, kids, sum, best,
                               dummy_step_zero(), True{}, False{}, gres)
                        case False{}:
                          match gres:
                            case GuessRes{_, buf}:
                              +b0 = dummy_inf(Nat.sub(best_cost(best), Nat.add(sum, tail_lb)))
                              +fl = init_floor(wlen)
                              step(fuel, GThen{grest}, 0n, rest, glist_G, S, n,
                                   nodup, floor, inf, g, kids, sum, best,
                                   step(p, child_glist(nodup, words, wlen, b0, glist_G),
                                        0n, Nil{}, glist_G, words, wlen, nodup, fl,
                                        inf, Nil{}, Nil{}, 0n, b0, dummy_step_zero(),
                                        False{}, is_floor_hit(nodup, fl, b0),
                                        GuessRes{Nil{}, buf}),
                                   False{}, False{}, GuessRes{Nil{}, NoBuf{}})
                    case OneItem{fb, w}:
                      match skip:
                        case True{}:
                          step(fuel, GThen{grest}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, g, kids, sum, best,
                               dummy_step_zero(), True{}, False{}, gres)
                        case False{}:
                          step(fuel, GThen{grest}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, g,
                               Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
                               SolveRef.sat_add(inf, sum, 1n), best,
                               dummy_step_zero(), False{}, False{}, gres)
                    case TwoItem{fb, w1, w2}:
                      match skip:
                        case True{}:
                          step(fuel, GThen{grest}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, g, kids, sum, best,
                               dummy_step_zero(), True{}, False{}, gres)
                        case False{}:
                          step(fuel, GThen{grest}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, g,
                               Tree.Child{fb, two_tree(w1, w2)} <> kids,
                               SolveRef.sat_add(inf, sum, 3n), best,
                               dummy_step_zero(), False{}, False{}, gres)
                    case DoneItem{fb, tree, cost}:
                      match skip:
                        case True{}:
                          step(fuel, GThen{grest}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, g, kids, sum, best,
                               dummy_step_zero(), True{}, False{}, gres)
                        case False{}:
                          step(fuel, GThen{grest}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, g,
                               Tree.Child{fb, tree} <> kids,
                               SolveRef.sat_add(inf, sum, cost), best,
                               dummy_step_zero(), False{}, False{}, gres)
                    case Add{fb, +tail_lb}:
                      match pending:
                        case StepRes{pbest, pbuf}:
                          match pbest:
                            case SolveRef.Best{tree, +cost}:
                              match skip:
                                case True{}:
                                  step(fuel, GThen{grest}, 0n, rest, glist_G, S, n,
                                       nodup, floor, inf, g, kids, sum, best,
                                       dummy_step_zero(), True{}, False{}, gres)
                                case False{}:
                                  +sum2 = SolveRef.sat_add(inf, sum, cost)
                                  step(fuel, GThen{grest}, 0n, rest, glist_G, S, n,
                                       nodup, floor, inf, g,
                                       Tree.Child{fb, tree} <> kids,
                                       sum2, best, dummy_step_zero(),
                                       skippable(best, Nat.add(sum2, tail_lb)),
                                       False{}, GuessRes{Nil{}, pbuf})
                    case End{}:
                      match skip:
                        case True{}:
                          step(fuel, GThen{grest}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, Nil{}, Nil{}, 0n, best,
                               dummy_step_zero(), False{}, False{}, gres)
                        case False{}:
                          +best2 = SolveRef.finish_guess(inf, g, kids, sum, n, best)
                          step(fuel, GThen{grest}, 0n, rest, glist_G, S, n,
                               nodup, floor, inf, Nil{}, Nil{}, 0n, best2,
                               dummy_step_zero(), False{},
                               is_floor_hit(nodup, floor, best2), gres)
        case GTry{+row2, +g2, +grest}:
          match phase:
            case 1n+q:
              match gres:
                case GuessRes{items, buf2}:
                  step(fuel, GTry{row2, g2, grest}, q, items, glist_G, S, n,
                       nodup, floor, inf, Nil{}, Nil{}, 0n, best, dummy_step_zero(),
                       False{}, False{}, GuessRes{Nil{}, buf2})
            case 0n:
              match cs:
                case Nil{}:
                  match done:
                    case True{}:
                      StepRes{best, gres_buf(gres)}
                    case False{}:
                      match gres:
                        case GuessRes{old_items, buf}:
                          step(fuel, grest, 1n, Nil{}, glist_G, S, n,
                               nodup, floor, inf, Nil{}, Nil{}, 0n, best,
                               dummy_step_zero(), False{}, False{},
                               guess_items_buf(nodup, row2, g2, S, n, floor, best, buf))
                case Con{item, rest}:
                  match item:
                    case Begin{g3}:
                      step(fuel, GTry{row2, g2, grest}, 0n, rest, glist_G, S,
                           n, nodup, floor, inf, g3, Nil{}, 0n, best,
                           dummy_step_zero(), False{}, False{}, gres)
                    case ClassItem{fb, words, +wlen, +tail_lb}:
                      match skip:
                        case True{}:
                          step(fuel, GTry{row2, g2, grest}, 0n, rest, glist_G,
                               S, n, nodup, floor, inf, g, kids, sum, best,
                               dummy_step_zero(), True{}, False{}, gres)
                        case False{}:
                          match gres:
                            case GuessRes{_, buf}:
                              +b0 = dummy_inf(Nat.sub(best_cost(best), Nat.add(sum, tail_lb)))
                              +fl = init_floor(wlen)
                              step(fuel, GTry{row2, g2, grest}, 0n, rest, glist_G,
                                   S, n, nodup, floor, inf, g, kids, sum, best,
                                   step(p, child_glist(nodup, words, wlen, b0, glist_G),
                                        0n, Nil{}, glist_G, words, wlen, nodup, fl,
                                        inf, Nil{}, Nil{}, 0n, b0, dummy_step_zero(),
                                        False{}, is_floor_hit(nodup, fl, b0),
                                        GuessRes{Nil{}, buf}),
                                   False{}, False{}, GuessRes{Nil{}, NoBuf{}})
                    case OneItem{fb, w}:
                      match skip:
                        case True{}:
                          step(fuel, GTry{row2, g2, grest}, 0n, rest, glist_G,
                               S, n, nodup, floor, inf, g, kids, sum, best,
                               dummy_step_zero(), True{}, False{}, gres)
                        case False{}:
                          step(fuel, GTry{row2, g2, grest}, 0n, rest, glist_G,
                               S, n, nodup, floor, inf, g,
                               Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
                               SolveRef.sat_add(inf, sum, 1n), best,
                               dummy_step_zero(), False{}, False{}, gres)
                    case TwoItem{fb, w1, w2}:
                      match skip:
                        case True{}:
                          step(fuel, GTry{row2, g2, grest}, 0n, rest, glist_G,
                               S, n, nodup, floor, inf, g, kids, sum, best,
                               dummy_step_zero(), True{}, False{}, gres)
                        case False{}:
                          step(fuel, GTry{row2, g2, grest}, 0n, rest, glist_G,
                               S, n, nodup, floor, inf, g,
                               Tree.Child{fb, two_tree(w1, w2)} <> kids,
                               SolveRef.sat_add(inf, sum, 3n), best,
                               dummy_step_zero(), False{}, False{}, gres)
                    case DoneItem{fb, tree, cost}:
                      match skip:
                        case True{}:
                          step(fuel, GTry{row2, g2, grest}, 0n, rest, glist_G,
                               S, n, nodup, floor, inf, g, kids, sum, best,
                               dummy_step_zero(), True{}, False{}, gres)
                        case False{}:
                          step(fuel, GTry{row2, g2, grest}, 0n, rest, glist_G,
                               S, n, nodup, floor, inf, g,
                               Tree.Child{fb, tree} <> kids,
                               SolveRef.sat_add(inf, sum, cost), best,
                               dummy_step_zero(), False{}, False{}, gres)
                    case Add{fb, +tail_lb}:
                      match pending:
                        case StepRes{pbest, pbuf}:
                          match pbest:
                            case SolveRef.Best{tree, +cost}:
                              match skip:
                                case True{}:
                                  step(fuel, GTry{row2, g2, grest}, 0n, rest,
                                       glist_G, S, n, nodup, floor, inf, g, kids,
                                       sum, best, dummy_step_zero(), True{}, False{},
                                       gres)
                                case False{}:
                                  +sum2 = SolveRef.sat_add(inf, sum, cost)
                                  step(fuel, GTry{row2, g2, grest}, 0n, rest,
                                       glist_G, S, n, nodup, floor, inf, g,
                                       Tree.Child{fb, tree} <> kids, sum2, best,
                                       dummy_step_zero(),
                                       skippable(best, Nat.add(sum2, tail_lb)),
                                       False{}, GuessRes{Nil{}, pbuf})
                    case End{}:
                      match skip:
                        case True{}:
                          step(fuel, GTry{row2, g2, grest}, 0n, rest, glist_G,
                               S, n, nodup, floor, inf, Nil{}, Nil{}, 0n, best,
                               dummy_step_zero(), False{}, False{}, gres)
                        case False{}:
                          +best2 = SolveRef.finish_guess(inf, g, kids, sum, n, best)
                          step(fuel, GTry{row2, g2, grest}, 0n, rest, glist_G,
                               S, n, nodup, floor, inf, Nil{}, Nil{}, 0n, best2,
                               dummy_step_zero(), False{},
                               is_floor_hit(nodup, floor, best2), gres)

def solve_fast_two(+w: +List<Nat>, +w2: +List<Nat>, same: Bool) -> Maybe<Tree.Tree>:
  match same:
    case True{}:
      Some{Tree.Node{w, Nil{}}}
    case False{}:
      Some{two_tree(w, w2)}

def solve_fast_valid(+guesses: +List<+List<Nat>>,
                     +candidates: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  match candidates:
    case Nil{}:
      +inf = SolveRef.inf_of(0n)
      +b0 = dummy_inf(inf)
      +gG = glist_of_words(guesses, GEnd{})
      SolveRef.best_to_maybe(inf,
        step_res_best(
          step(0n, gG, 0n, Nil{}, gG, Nil{}, 0n, True{}, 0n, inf,
               Nil{}, Nil{}, 0n, b0, dummy_step_zero(), False{},
               is_floor_hit(True{}, 0n, b0),
               GuessRes{Nil{}, NoBuf{}})))
    case Con{+w, +t}:
      match t:
        case Nil{}:
          Some{Tree.Node{w, Nil{}}}
        case Con{+w2, +t2}:
          match t2:
            case Nil{}:
              solve_fast_two(w, w2, word_eq_fast(w, w2))
            case Con{+w3, +t3}:
              +ws : +List<+List<Nat>> = w <> (w2 <> (w3 <> t3))
              +n = Groups.len_words(ws)
              +gcount = U32.from_nat(Groups.len_words(guesses))
              +inf = SolveRef.inf_of(n)
              +nd = no_dup_fast(ws)
              +b0 = dummy_inf(inf)
              +fl = init_floor(n)
              +gG = glist_of_guesses(guesses, 0, 1)
              +cs = build_cwords(ws, guesses, 0, gcount)
              SolveRef.best_to_maybe(inf,
                step_res_best(
                  step(n, gG, 0n, Nil{}, gG, cs, n, nd, fl, inf,
                       Nil{}, Nil{}, 0n, b0, dummy_step_zero(), False{},
                       is_floor_hit(nd, fl, b0),
                       GuessRes{Nil{}, mk_buf_tbl(nd, guesses, ws, n)})))

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
