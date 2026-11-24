# Proofs

All eight laws in `LAWS.bend` are proved. `PROOF.bend` imports the solver modules and the helper
modules under `proofs/`, then defines one `def Laws.<name>` for each law. `PENDING_LAWS` is empty,
so no law is allowed to be open.

This document maps the proof modules, explains the gate, and records the local commands and the
Bend restrictions that shaped the proofs. The laws themselves, with their proof strategies, are in
[laws.md](laws.md).

## Map of `proofs/`

Each module has a header comment with the exact statement it proves. The groups below follow the
purpose of the proof work, not the import order.

### Feedback

| File | What it proves |
| --- | --- |
| `feedback.bend` | Feedback equality is symmetric, from the component-wise symmetry of colour equality. This aligns `lookup`, which tests the feedbacks in one order, with `depth`, which tests them in the other. |
| `depth.bend` | `lookup` and `depth.go` scan a child list in the same way, so the child found by one is the child found by the other. This bridges `Valid`, which is defined with `depth`, and trees selected with `lookup`. |

### JSON

| File | What it proves |
| --- | --- |
| `decimal.bend` | The arithmetic of decimal numerals: the printer's least-significant-first digit list, its value, and the canonical decimal form used by the independent renderer. |
| `json_spec.bend` | The digit bridge and the renderer induction behind `print_matches_render`, plus the recogniser lemmas for decimal letters, guess arrays, feedback arrays, kids arrays and whole trees behind `tree_json_wellformed`. |

### Grouping

| File | What it proves |
| --- | --- |
| `groups.bend` | The membership half of the feedback partition: every candidate other than the guess lies in some group built by `groups_build`. |
| `groupsdistinct.bend` | The groups built for one guess have pairwise different feedback patterns, so a child list has at most one child per feedback. |
| `groupsmeasure.bend` | Turns the `groups_smaller` boolean into a proof-carrying list with one size bound per group, so the validity induction can read the bound for the group it is looking at. |
| `depthgroups.bend` | A candidate in a group is found by the `depth` scan over the group children. The lemma threads the feedbacks still above the candidate in one traversal, so the membership fact is not needed twice. |
| `children.bend` | Names the children of a guess in group order, proves that the accumulator inside the evaluator is their reverse, and that reversing twice is the identity. |
| `kids.bend` | The child that `lookup` finds for a group's feedback is valid for that group, transported from facts about the `Maybe` result without using the lookup equation twice. |

### Cost arithmetic

| File | What it proves |
| --- | --- |
| `logic.bend` | Small logical helpers used across the proofs, including the type family that turns a boolean equality into `Empty` or `Unit`. |
| `nat.bend` | The `Nat` order and arithmetic lemmas the solver needs. Base provides `Nat.cmp` and the comparisons but proves very little about them. |
| `maybe.bend` | `Maybe Nat` costs with `None` as infinity: saturating addition, comparison, and minimum with `None` as the identity. |
| `min.bend` | The minimum of a list is below its accumulator, below every member, and is either the accumulator or a member. This is the guess-selection fold. |
| `sat.bend` | Saturating addition: a finite accumulated guess cost means every part is finite, which turns a finite guess cost into finite, valid child costs. |
| `nodecost.bend` | The cost of `Node(g, kids)` over a candidate list is the number of candidates plus the children's costs, one per non-guess candidate. |
| `groupcost.bend` | The total child cost over a group list, and how it grows when one word is added to a group. |
| `classbound_nat.bend` | The multiplication lemmas behind the class bound: distributivity, commutativity, monotonicity, and a fold over a multiplied list. |
| `classbound_sum.bend` | A saturating sum that stays below infinity is the plain sum of its parts, and the `Maybe` fold agrees with that sum. It returns both facts from one traversal. |
| `classbound.bend` | The partition arithmetic: class sizes sum to at most `|S|`, so with a cost bound of `m*m` per class the node cost fits `|S|*|S|`, which is below the solver's infinity. |
| `classbound_kids.bend` | The finished guess's node cost splits into the candidate count plus the class costs, and the stored cost agrees with the cost of the tree it carries. |
| `optimalvalue.bend` | The value of a search result as a `Maybe` cost, its correspondence with the saturating sum, associativity of `MAdd`, and monotonicity of `MMin`. |
| `optsum.bend` | The class sums of one guess in plain `Nat` order: the folded sum is below the children's total when every class result is below its child's cost. |

### Cover lemma

| File | What it proves |
| --- | --- |
| `cover.bend` | The cover lemma: a valid tree costs at least the per-class oracle's minimum for its root. A usable root splits into feedback classes; an unusable root has one class holding all candidates and descends on the same list. |
| `cover_groups.bend` | A class is a subsequence of the candidate list, a class at least as long as the list is the list itself, and a full class exists when `groups_smaller` is false. |
| `cover_kids.bend` | Turns a valid node's depth evidence into `GroupKids`: for every class, the child found by `lookup` is a valid tree for that class. |
| `cover_list.bend` | List and equality helpers for the cover argument: syntactic word equality reflects to propositional equality, a subsequence is no longer than its supersequence, and a same-length subsequence is the list itself. |
| `cover_maybe.bend` | The copyable `Maybe<&2, Nat>` used for oracle costs, with its own arithmetic and order lemmas so the oracle can copy entries freely. |
| `cover_oracle.bend` | The per-class optimality oracle, the value it gives a guess, the minimum over guesses, and the order lemmas the cover induction uses. |

### Validity

| File | What it proves |
| --- | --- |
| `spec.bend` | The proof-carrying outcome of the solver: a tree with validity and optimality proofs, or a proof that no valid tree exists. |
| `eval.bend` | A recursive specification evaluator for the flat schedule: the class fold, the guess fold and the guess-list fold, with equations showing that `step` is exactly that computation. |
| `stepsched.bend` | A datatype mirror of the flat schedule. Inducting on it is inducting on the schedule the solver actually runs, while `items` erases the proof-only context back to the list `step` consumes. |
| `best_nil.bend` | The zero-fuel base case: an empty candidate list has a valid tree of cost zero, or no valid tree when the guess list is empty. |
| `bestok.bend` | The invariant that the stored result is either absent or a valid tree, and that `better` and the zero-fuel fold preserve it. |
| `nodevalid.bend` | A node built from a guess and its group children is valid: the guess is in the input list, every non-guess candidate is in a class, and each class child gives its candidates a depth. |
| `validbag.bend` | Flattens the per-word depth facts of the classes into one linear bag, then strings them back together in candidate order for the node. |
| `solvevalid.bend` | The arithmetic and fold plumbing for validity, and the node step that recovers each candidate's depth from its feedback class. |
| `stepvalid.bend` | Every finite result of `step` is a valid tree, by induction on fuel together with a loop invariant over the schedule and the accumulated children. |
| `mainvalid.bend` | The validity invariant at every fuel for the whole fused search, ending in `Laws.solve_valid`. |

### Optimality
| File | What it proves |
| --- | --- |
| `optnode.bend` | The node step of the optimality induction: for a usable root, the node cost splits into one guess per candidate plus the class costs, and the class results are below the children's costs. |
| `optfold.bend` | `better` keeps the cheaper result, so the folded guess cost is below every candidate cost the fold produced. The facts are `Bool` equalities so they can be reused. |
| `optguess.bend` | The guess fold reaches the cost of the guess a valid tree uses: that guess is in the list, and the fold only lowers the cost from there. |
| `optind.bend` | The fuel induction of the lower bound: the stored cost is at most the cost of any valid tree, with every class of every guess handed its own obligation at the smaller fuel. |
| `optcost.bend` | When the stored cost is finite it is the cost of the tree the search returns, because the saturating sum is then a plain sum and the returned tree is the node of class results. |
| `optcomplete.bend` | Completeness: if a valid tree exists, the stored cost is below infinity and fits the square of the candidate count, by the same fuel induction over the classes of the given tree. |
| `optstrong.bend` | Merges the optimality and completeness walks: one traversal of the given tree produces both the cost comparison and the class size and cost bounds, ending in `Laws.solve_optimal`. |


### Lower bounds

Standalone facts about the cost of an arbitrary valid tree, stated about `Tree.cost` only.
They are what a pruning rule needs to discard a guess or a class before searching it.

| File | What it proves |
| --- | --- |
| `lb_size.bend` | Every depth the tree produces is absent or at least one, so a valid tree costs at least the number of candidates: `cost(T, S) >= |S|`. |
| `lb_twice.bend` | Only the root guess can end a candidate at depth one, so `2|S| <= cost(T, S) + mult(root, S)`, with `mult` the number of candidates equal to the root guess. This is exact with duplicates; `mult <= maxMult(S)` and the duplicate-free `2|S| - 1` bound follow. |
| `lb_nodup.bend` | Duplicate-freeness of a candidate list, stated as `maxMult(S) <= 1`, and the fact it gives the capacity argument: every word occurs at most once, so the root guess's multiplicity is at most one. The predicate is a boolean equality, so a proof of it can be reused across the per-class recursion. |
| `lb_classes.bend` | The first-match partition of a candidate list over a node's children: each child takes the words not yet taken whose feedback is the child's feedback, so a repeated feedback gets an empty class. The class sizes plus the leftover length are the candidate count, and neither filter raises a word's multiplicity or the largest multiplicity of the list, which is how duplicate-freeness reaches every class. |
| `lb_decomp.bend` | The node cost splits over the first-match classes: `cost(Node(g, kids), S) >= |S| + sum over the classes of cost(child, words)`, given that each class's words are non-guess words with the child's feedback and the child list looks up the class's own child. Each class cost can then be bounded on its own; the words no child takes only make the inequality weaker. |
| `lb_adsplit.bend` | The depth facts of a candidate list split over a child's two filters: `AllHaveDepth(t, S)` gives `AllHaveDepth(t, kept)` and `AllHaveDepth(t, dropped)`. This is how a node's validity reaches the classes in the capacity induction, one traversal per node. |
| `lb_capacity.bend` | The capacity bound function `capbound(n, k) = n + sum over j of (n - (1 + k + ... + k^(j-1)))+`, with the facts a pruning rule needs about the bound itself: it is monotone in `n`, its capacity sequence grows by at least one per level, and it is at least the depth bound `2n - 1`. |

The soundness statement for the capacity bound, that a valid tree with no duplicate candidates whose nodes have at most `k` children costs at least `capbound(|S|, k)`, is not proved yet. The induction runs over the tree with a capacity sequence of its own: a node can hold at most its own guess's candidates below depth one plus the candidates its classes hold one level further down, which is why the bound is stated with the per-node class sizes rather than with `k` alone. The partition in `lb_classes.bend` and the duplicate-freeness of its classes in `lb_nodup.bend` are the two inputs that step needs.

The solver now uses the bound in the duplicate-free buffered path (`cap_walk` and the node gate in `src/solve_fast.bend`), so the open goal has three parts:

1. `LB.capbound_sound`: for `t : Tree`, `S, G : List (List Nat)` and `k : Nat`, given `Tree.Valid(t, G, S)`, no duplicate word in `S`, and every node of `t` having at most `k` children, prove `Nat.is_le(LB.capbound(len(S), k), Tree.cost(t, S)) == True{}`. The inductive invariant that makes the level counting work is `countDepthLess(t, L, S) <= G(L - 1)` for every `L`, with `G(0) = 0` and `G(j) = 1 + k + ... + k^(j-1)`, followed by the telescoping identity `cost(t, S) = sum over j from 1 to len(S) + 1 of (len(S) - countDepthLess(t, j, S))`.
2. `LB.class_k_bounds_branching`: `class_k_start` returns the maximum over the whole guess list of the number of distinct feedback codes on the class words. A child class is a subset of its parent, so a guess produces no more classes on the child, and every node of any valid tree over the class has at most that many children. The implementation side needs a specification of `ck_go` in the style of the `hist5_go` proof in `fast_hist5.bend`.
3. The wiring in `fast_hist5.bend`: `FH.big_ok_b` and `FH.BodyMatch` must carry `clb <= cost of the class`, and the whole-guess skip in `cap_walk`/`finish_node` uses the same bound. With `clb = max(2*m - 1, capbound(m, k))` for every class of size `m`, the guess costs at least `n` plus the sum of its class bounds.

### Bound-pruned search

| File | What it proves |
| --- | --- |
| `fast_step.bend` | Computation lemmas for the pruned state machine in `src/solve_fast.bend`: early exit on `done`, popping the next guess from `GList` (`GTry` / `GThen` / `GEnd`), unpacking a `GuessRes` on `phase = 1n`, one step per item kind (`Begin`, `ClassItem`, `OneItem`, `TwoItem`, `DoneItem`, `Add`, `End`), recursive child search from an arbitrary cutoff accumulator, and the dead-block lemma when a guess is pruned mid-block. |
| `fast_better.bend` | The skip lemma: `better` replaces only on a strictly lower cost, so a guess whose candidate cost is at least a bound `lb` leaves any accumulator with cost at most `lb` unchanged. |
| `fast_groups.bend` | The single-pass `word_eq_fast` and `feedback_eq_fast` and the non-duplicating `non_green_fast`, `consume_color_fast`, `consume_pool_fast`, `feedback_go_fast`, and `feedback_fast` in `src/solve_fast.bend` return the exact same booleans and feedback lists as the reference definitions in `src/feedback.bend`. |
| `fast_lb.bend` | Soundness of the pre-grouping lower bound `pre_lb(|S|, g, S) = |S| + keep_fast(g, S)` (`lb_size.bend`, `classbound.bend`) and of `sum + lower_bound(|S|, groups)` for any suffix `groups` of the reference class fold starting from `(kids, sum)`: when the candidate cost is finite, every remaining class cost is finite, valid (`mainvalid.bend`), equals its tree's cost (`optcost.bend`), and is at least both `|ws|` and `2 * |ws| - max_mult(ws)` (`lb_twice.bend`, `lb_capacity.bend`); when the candidate cost is at least infinity, `better` also keeps any accumulator below or at infinity. |
| `fast_cutoff.bend` | Soundness of recursive child cutoff propagation: `SolveRef.better` is associative with exact tie-breaking, so starting `Eval.guesses` from `dummy_inf(cutoff)` (where `cutoff = best_cost(best) - (sum + tail_lb)`) returns the exact reference child whenever its cost is strictly below `cutoff`, and otherwise returns `dummy_inf(cutoff)` so `Add` prunes the remaining classes of the guess while the reference accumulator is also unchanged. |
| `fast_one.bend` | Soundness of the root candidate-membership check `all_in_fast(C, G)` and O(1) singleton leaf resolution (`OneItem{fb, w}`): if any candidate is absent from `G`, no valid tree exists (`mainvalid.bend`) and `SolveRef.solve` returns `None{}`; if every candidate is in `G`, every feedback class preserves membership (`cover_groups.bend`) and every singleton class `[w]` at positive fuel with `1 < inf` equals `SolveRef.Best{Tree.Node{w, Nil{}}, 1n}` in the reference search. |
| `fast_nodup.bend` | Soundness of the root duplicate-free check `no_dup_fast(C)`, subsequence preservation of duplicate-freedom (`cover_groups.bend`), O(1) `class_lb_fast` (`2*|ws| - 1`), `2*|S| - 1` node-level early exit, fast duplicate-free pre-bound filtering, and O(1)-prepend `FGroup` grouping (`fgroups_build_fast`, `fgroups_smaller`, `fgroups_lb`, `fgroup_items_build`). |
| `array.bend` | General-purpose reasoning library for `Base.Array`: depth invariant `Arr.Depth`, affine duplication `Arr.dup`, 32-bit power-of-two and bit-masking helpers, and read/write specifications (`Arr.get_depth`, `Arr.swap_depth`, `Arr.swap_old`, `Arr.set_eq`, `Arr.get_fst`, `Arr.get_new`, `Arr.get_swap_same`, `Arr.get_swap_diff`). |
| `fast_fb5.bend` | Exact equivalence of the zero-allocation 10-bit 5-letter feedback encoder (`feedback_code5`) and decoder (`decode_fb5`) with `Feedback.feedback` and `Feedback.word_eq`, including 10-bit range bounds and all-green code `682` reflection. |
| `fast_perm.bend` | Explicit permutation witnesses (`FP.Perm`, `FP.PermOk`) over `List<Groups.Group>` preserving `allNe`, `distinctB`, feedback-group membership, `total`, `lower_bound`, `groups_smaller`, `all_in_jobs_b`, `nodup_ok_jobs`, `MV.Bounds`, and `ks_cost` — used to justify largest-class-first child ordering. |
| `fast_tbl.bend` | Exact specification of the precomputed `|G| x |C|` `Array<U32>` feedback table (`FT.TblOk`, `FT.mk_tbl_ok_go`, `FT.tbl_get_use`), candidate index/row wrappers (`CWord`, `FT.build_cwords_ok`), and row-annotated guess lists (`FT.RowWord`, `FT.guesses_to_rws_ok`, `FT.cwords_to_rws_ok`), proving every table lookup equals `feedback_code5`. |
| `fast_three.bend` | O(1) resolution of 3-candidate classes (`solve_three_tbl`, emitted as `DoneItem{fb, tree, cost}` with cost 5 or 6): proves `tree` is valid for `(G, ws)`, `Tree.cost(tree, ws) <= cost`, and `cost <= cost(SolveRef)` by checking via the feedback table whether one of the three candidates splits the other two (cost 5) or else falls back to a 2-step split (cost 6). |
| `fast_hist5.bend` | Exact correctness of the root-threaded `Buf5` buffer (reusable 1024-entry `seen`/`bkts` arrays plus the precomputed `tbl`), table-backed histogramming (`hist5_tbl_go`, including mid-pass collision-budget early abort and stage-2 `skip_self` detection), two-pass bucketing (`fill5_tbl_go`, `drain5_go`) with largest-class-first ordering and O(1) 3-word `DoneItem` resolution, proving the 5-case semantic specification `FH.GuessSpec` (`GCSkipSelf`, `GCSkipUnusable`, `GCSkipPre`, `GCSkipLb`, `GCLive`) while preserving `FH.BufOk`. |
| `fast_valid.bend` | Direct validity and cost-accounting primitives for `SolveFast`: boolean validity `FV.valid_b` with reflection to `Tree.Valid`, accumulator invariant `FV.best_ok_b`, O(1) validity/cost/lower-bound proofs for `OneItem` and `TwoItem` (`two_tree`), `Eval.guesses` monotonicity, permutation-aware finished-node validity and cost reconstruction (`FV.end_node_ok_perm`), and soundness of the `2*|S| - 1` initial floor and `2*|S|` post-candidate floor (`FV.after_s_floor_le`). |
| `fast_opt.bend` | Fuel induction over the staged `GList` search proving directly that for every candidate subset `S`, cutoff `best0`, and valid root-threaded buffer `buf0`, `SolveFast` satisfies `FV.best_ok_b`, never worsens `best0`, achieves cost at most `SolveRef`, and returns a valid `FH.BufOk` buffer. Chained with `optstrong.bend` and `lb_size.bend`, this proves validity and optimality for the sequential search, which is `Solve.solve` at one chunk. |

### Parallel root

| File | What it proves |
| --- | --- |
| `par_list.bend` | `take` and `drop` put a guess list back together, so the two parallel halves cover every guess exactly once, and appending two chunks' result lists is the result list of the appended chunks. |
| `par_elt.bend` | Replaying one guess's independently computed result on a running accumulator is the guess's own step. The result carries the candidate and the comparison with the accumulator is exactly `better`'s, including the neutral result at infinity. |
| `par_fold.bend` | Folding the per-guess results is the reference guess fold, the parallel split produces the same result list as the sequential one, and `SolvePar.solve` returns exactly `SolveRef.solve`'s tree. `PROOF.bend` states the last step as `Par.solve_eq`. |
| `par_chunk.bend` | The chunked root of `src/solve_k.bend`. A chunk job specification whose third conjunct bounds a result by the reference fold over the chunk's own guesses; clones of the five staged walks over a chunk reference list; the chunk leaf (`P.chunk_best_leaf`) from the prefix invariant and the feedback table's row annotations; continuity of the split (`List.take`/`List.drop`) through the prefix, the suffix and the `U32` row offset; the strong fold induction (`P.par_cost`) showing the folded chunk results cost at most the reference fold over the whole root guess list from any accumulator below infinity; and `P.par_ok`, which keeps every chunk result valid and finite. `P.solve_k_valid` and `P.solve_k_optimal` chain those into `OQStrong.F2.optimal_and_finite` for every chunk count `k`, and the laws use them at `k = 1`. |

## How the gate works

`scripts/check-proofs.sh` is the gate. CI runs it, and contributors run the same script locally.

- It reads the law names from the `law <name>:` lines in `LAWS.bend` and the proved names from the
  `def Laws.<name>(` lines in `PROOF.bend`.
- Every law must have a proof def, unless it is named in `PENDING_LAWS`.
- Every name in `PENDING_LAWS` must be a law in `LAWS.bend` and must not have a proof def. A stale
  or misspelled entry fails the gate.

`PENDING_LAWS` is a plain text file at the repository root, one law name per line. Blank lines and
`#` comments are ignored. It exists so that a law can be stated before its implementation and still
pass the gate. It is not a place for broken proofs.

When the pending list is empty, the gate requires `bend PROOF.bend` to exit 0 and print
`ALL PROOFS CHECK`, then runs `bend PROOF.bend --verdict` and requires the same. An empty list means
that no law is allowed to be open: every law has a proof and the whole development must pass both
Bend's checker and the kernel recheck. It also prints the summary, currently:

```text
check-proofs: 8 of 8 law(s) proved, 0 pending
```

When the pending list is non-empty, the gate instead requires `bend PROOF.bend` to exit 1 with
`SOME PROOFS FAIL` and exactly one error, `Error: N TODOs found.`, where `N` is the number of
pending laws. Any other error fails the gate, so a pending law means "not attempted", never
"broken". In that mode `--verdict` is skipped, because the kernel needs every proof to be present.

## Running the checks locally

From the repository root:

```sh
bend PROOF.bend
bend PROOF.bend --verdict
scripts/check-proofs.sh
```

- `bend PROOF.bend` checks and proves the development with Bend's own checker. Success is
  `ALL PROOFS CHECK` and exit 0.
- `bend PROOF.bend --verdict` checks it again with the proven kernel. Success is the same line.
- `scripts/check-proofs.sh` runs both, after checking the law and pending lists.

To type-check the law statements alone, without proving them, run
`bend LAWS.bend --check-only`. Open laws appear there as TODOs.

The checks need the toolchain pinned in `.github/workflows/proofs.yml`:

| Tool | Version |
| --- | --- |
| Bend | 2.0.40 |
| elan | 4.4.0 |
| Lean | `leanprover/lean4:v4.34.0` |

CI also sets `BEND_NO_TELEMETRY=1` and caches the Lean toolchain and the kernel under
`~/.bend/bendtt`. A toolchain bump changes what the proofs accept, so it belongs in its own pull
request.

## What the Lean kernel recheck is

Bend's normal check is its own type checker. `--verdict` additionally translates the development to
BendTT and rechecks it with the proven kernel, which runs on Lean. The two checks are independent:
a proof that Bend accepts but the kernel rejects fails the gate. That is why the verdict run needs
elan and the pinned Lean toolchain, and why the gate only runs it when every law has a proof.

## Bend limitations that shaped the proofs

The proofs are written around three restrictions in Bend. They explain the shape of the modules,
not just their content.

**No mutual recursion and no forward references.** A definition can only use definitions that
appear before it, and two definitions cannot call each other. The proofs are therefore split into
small modules with a linear import order: a lemma lives in an earlier file than every proof that
uses it. It also means a useful lemma shape is sometimes written twice for two types rather than
shared through a mutual definition, as `maybe.bend` and `cover_maybe.bend` do for the two `Maybe`
cost types.

**Proof values are affine.** A hypothesis or proof value is consumed when it is matched, so a proof
cannot use the same fact twice in two branches. Two techniques avoid that:

- State the fact as a `Bool` equality (`{... == True{} : Bool}`). A boolean equality is `Data`, so
  it can be copied and used in several places. `optfold.bend`, `optind.bend` and `classbound_kids.bend`
  rely on this.
- Prove both facts in one traversal and return them together. `classbound_sum.bend` returns the
  plain sum and the `Maybe` fold together, `depthgroups.bend` threads the feedbacks still above the
  candidate in one list, and `optstrong.bend` merges the optimality and completeness walks so the
  same class subtrees are read once.

**Recursion must be structural.** The solver's recursion is fused into one definition, `step`,
driven by a flat schedule and a fuel argument, because that is the form whose termination Bend
accepts. The proofs follow the same structure: they induct on the fuel, on the schedule datatype in
`stepsched.bend`, or on the candidate list, and the class results are handed to the next level as a
single conjunction rather than fetched again from an induction hypothesis.
