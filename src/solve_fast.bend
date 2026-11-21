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

# One step of the pruned search. Lexicographic structural recursion on
# `(fuel, gs, cs)` builds each guess lazily when `cs` becomes `Nil{}`, caches
# `n = |S|` and `nodup`, and exits the node immediately once `done` signals
# `best_cost(best) <= 2 * n - 1` in duplicate-free mode.
def step(+fuel: Nat, +gs: +List<+List<Nat>>, +cs: +List<Item>,
         +G: +List<+List<Nat>>, +S: +List<+List<Nat>>, +n: Nat, +nodup: Bool,
         +inf: Nat, +g: +List<Nat>, +kids: +List<Tree.Child>, +sum: Nat,
         +best: SolveRef.Best, +pending: SolveRef.Best, skip: Bool,
         done: Bool) -> SolveRef.Best:
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
                  step(0n, Nil{}, rest, G, S, n, nodup, inf, g2, Nil{}, 0n,
                       best, pending, False{}, False{})
                case ClassItem{fb, words, wlen, tail_lb}:
                  dummy_inf(inf)
                case OneItem{fb, w}:
                  dummy_inf(inf)
                case Add{fb, tail_lb}:
                  match pending:
                    case SolveRef.Best{tree, cost}:
                      step(0n, Nil{}, rest, G, S, n, nodup, inf, g,
                           Tree.Child{fb, tree} <> kids,
                           SolveRef.sat_add(inf, sum, cost), best,
                           dummy_zero(), skip, False{})
                case End{}:
                  step(0n, Nil{}, rest, G, S, n, nodup, inf, Nil{}, Nil{}, 0n,
                       SolveRef.finish_guess(inf, g, kids, sum, n, best),
                       dummy_zero(), False{}, False{})
        case Con{+g2, +grest}:
          match cs:
            case Nil{}:
              step(0n, grest, Begin{g2} <> (End{} <> Nil{}),
                   G, S, n, nodup, inf, Nil{}, Nil{}, 0n, best,
                   dummy_zero(), False{}, False{})
            case Con{item, rest}:
              match item:
                case Begin{g3}:
                  step(0n, g2 <> grest, rest, G, S, n, nodup, inf, g3,
                       Nil{}, 0n, best, pending, False{}, False{})
                case ClassItem{fb, words, wlen, tail_lb}:
                  dummy_inf(inf)
                case OneItem{fb, w}:
                  dummy_inf(inf)
                case Add{fb, tail_lb}:
                  match pending:
                    case SolveRef.Best{tree, cost}:
                      step(0n, g2 <> grest, rest, G, S, n, nodup, inf, g,
                           Tree.Child{fb, tree} <> kids,
                           SolveRef.sat_add(inf, sum, cost), best,
                           dummy_zero(), skip, False{})
                case End{}:
                  step(0n, g2 <> grest, rest, G, S, n, nodup, inf,
                       Nil{}, Nil{}, 0n,
                       SolveRef.finish_guess(inf, g, kids, sum, n, best),
                       dummy_zero(), False{}, False{})
    case 1n+p:
      match gs:
        case Nil{}:
          match cs:
            case Nil{}:
              best
            case Con{item, rest}:
              match item:
                case Begin{g2}:
                  step(fuel, Nil{}, rest, G, S, n, nodup, inf, g2, Nil{}, 0n,
                       best, dummy_zero(), False{}, False{})
                case ClassItem{fb, words, +wlen, +tail_lb}:
                  match skip:
                    case True{}:
                      step(fuel, Nil{}, rest, G, S, n, nodup, inf, g, kids,
                           sum, best, dummy_zero(), True{}, False{})
                    case False{}:
                      +b0 = dummy_inf(Nat.sub(best_cost(best), Nat.add(sum, tail_lb)))
                      step(fuel, Nil{}, rest, G, S, n, nodup, inf, g, kids,
                           sum, best,
                           step(p, G, Nil{}, G, words, wlen, nodup, inf,
                                Nil{}, Nil{}, 0n, b0, dummy_zero(), False{},
                                is_floor_hit(nodup, wlen, b0)),
                           False{}, False{})
                case OneItem{fb, w}:
                  match skip:
                    case True{}:
                      step(fuel, Nil{}, rest, G, S, n, nodup, inf, g, kids,
                           sum, best, dummy_zero(), True{}, False{})
                    case False{}:
                      step(fuel, Nil{}, rest, G, S, n, nodup, inf, g,
                           Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
                           SolveRef.sat_add(inf, sum, 1n), best,
                           dummy_zero(), False{}, False{})
                case Add{fb, +tail_lb}:
                  match pending:
                    case SolveRef.Best{tree, +cost}:
                      match skip:
                        case True{}:
                          step(fuel, Nil{}, rest, G, S, n, nodup, inf, g, kids,
                               sum, best, dummy_zero(), True{}, False{})
                        case False{}:
                          +sum2 = SolveRef.sat_add(inf, sum, cost)
                          step(fuel, Nil{}, rest, G, S, n, nodup, inf, g,
                               Tree.Child{fb, tree} <> kids,
                               sum2, best, dummy_zero(),
                               skippable(best, Nat.add(sum2, tail_lb)), False{})
                case End{}:
                  match skip:
                    case True{}:
                      step(fuel, Nil{}, rest, G, S, n, nodup, inf,
                           Nil{}, Nil{}, 0n, best, dummy_zero(), False{}, False{})
                    case False{}:
                      +best2 = SolveRef.finish_guess(inf, g, kids, sum, n, best)
                      step(fuel, Nil{}, rest, G, S, n, nodup, inf,
                           Nil{}, Nil{}, 0n, best2, dummy_zero(), False{},
                           is_floor_hit(nodup, n, best2))
        case Con{+g2, +grest}:
          match cs:
            case Nil{}:
              match done:
                case True{}:
                  best
                case False{}:
                  step(fuel, grest, guess_items(nodup, g2, S, n, best),
                       G, S, n, nodup, inf, Nil{}, Nil{}, 0n, best,
                       dummy_zero(), False{}, False{})
            case Con{item, rest}:
              match item:
                case Begin{g3}:
                  step(fuel, g2 <> grest, rest, G, S, n, nodup, inf, g3,
                       Nil{}, 0n, best, dummy_zero(), False{}, False{})
                case ClassItem{fb, words, +wlen, +tail_lb}:
                  match skip:
                    case True{}:
                      step(fuel, g2 <> grest, rest, G, S, n, nodup, inf, g,
                           kids, sum, best, dummy_zero(), True{}, False{})
                    case False{}:
                      +b0 = dummy_inf(Nat.sub(best_cost(best), Nat.add(sum, tail_lb)))
                      step(fuel, g2 <> grest, rest, G, S, n, nodup, inf, g,
                           kids, sum, best,
                           step(p, G, Nil{}, G, words, wlen, nodup, inf,
                                Nil{}, Nil{}, 0n, b0, dummy_zero(), False{},
                                is_floor_hit(nodup, wlen, b0)),
                           False{}, False{})
                case OneItem{fb, w}:
                  match skip:
                    case True{}:
                      step(fuel, g2 <> grest, rest, G, S, n, nodup, inf, g,
                           kids, sum, best, dummy_zero(), True{}, False{})
                    case False{}:
                      step(fuel, g2 <> grest, rest, G, S, n, nodup, inf, g,
                           Tree.Child{fb, Tree.Node{w, Nil{}}} <> kids,
                           SolveRef.sat_add(inf, sum, 1n), best,
                           dummy_zero(), False{}, False{})
                case Add{fb, +tail_lb}:
                  match pending:
                    case SolveRef.Best{tree, +cost}:
                      match skip:
                        case True{}:
                          step(fuel, g2 <> grest, rest, G, S, n, nodup, inf, g,
                               kids, sum, best, dummy_zero(), True{}, False{})
                        case False{}:
                          +sum2 = SolveRef.sat_add(inf, sum, cost)
                          step(fuel, g2 <> grest, rest, G, S, n, nodup, inf, g,
                               Tree.Child{fb, tree} <> kids,
                               sum2, best, dummy_zero(),
                               skippable(best, Nat.add(sum2, tail_lb)), False{})
                case End{}:
                  match skip:
                    case True{}:
                      step(fuel, g2 <> grest, rest, G, S, n, nodup, inf,
                           Nil{}, Nil{}, 0n, best, dummy_zero(), False{}, False{})
                    case False{}:
                      +best2 = SolveRef.finish_guess(inf, g, kids, sum, n, best)
                      step(fuel, g2 <> grest, rest, G, S, n, nodup, inf,
                           Nil{}, Nil{}, 0n, best2, dummy_zero(), False{},
                           is_floor_hit(nodup, n, best2))

# The pruned search on a guess list and candidate list. Checks once at the root
# that every candidate belongs to `guesses` (returning `None{}` immediately if
# not) and whether `candidates` is duplicate-free (enabling O(1) `class_lb`,
# O(1) floor exit at `2 * |S| - 1`, and fast pre-bound filtering throughout).
def solve_fast_valid(+guesses: +List<+List<Nat>>,
                     +candidates: +List<+List<Nat>>) -> Maybe<Tree.Tree>:
  match candidates:
    case Nil{}:
      +inf = SolveRef.inf_of(0n)
      +b0 = dummy_inf(inf)
      SolveRef.best_to_maybe(inf,
        step(0n, guesses, Nil{}, guesses, Nil{}, 0n, True{}, inf,
             Nil{}, Nil{}, 0n, b0, dummy_zero(), False{},
             is_floor_hit(True{}, 0n, b0)))
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
            step(n, guesses, Nil{}, guesses, cs, n, nd, inf,
                 Nil{}, Nil{}, 0n, b0, dummy_zero(), False{},
                 is_floor_hit(nd, n, b0)))

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
