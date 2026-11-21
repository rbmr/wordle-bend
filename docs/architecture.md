# Architecture

**Status: scaffolding, in progress.** This document describes the intended components and the data
flow between them. Nothing in it is implemented yet. Where a detail is not settled, it is marked as
such rather than guessed at.

## Shape of the problem

The solver takes two lists of words:

- the **guesses list**: the words that may be played as a guess;
- the **candidates list**: the words that may be the answer.

Words are arbitrary over some alphabet, and all words in a run have the same length. Each guess
against a candidate produces a pattern of per-letter feedback, which is the same three-way feedback
the game publishes for each position. A strategy is a decision tree: each node is a guess, and each
edge leaves the node on one feedback pattern toward the next node.

The objective is to minimise the total number of guesses over all candidates. This is a sum over
candidates, not a worst case, so the optimal tree can favour a guess that resolves many likely
candidates quickly over one that shortens the worst branch.

## Components

### `words/`

Bundled word lists, with the provenance of each list recorded. The CLI may read word lists from
this directory, or from paths the user supplies. Not yet present.

### `src/`

The Bend solver. Its job is to search for the optimal tree and emit it as output. The search is
what makes the problem expensive, and it is the part written for HVM so that the work parallelises
across GPU and CPU.

The internal decomposition of the solver (for example, how candidate sets are partitioned per
feedback pattern, how subtrees are costed, and where the search is pruned) is not settled yet and
will be documented here as it is built.

### `laws/`

Formal statements and machine-checked proofs. Two properties matter:

- **validity**: every leaf of the returned tree is a candidate, and following the tree for a
  candidate reaches that candidate as a leaf;
- **optimality**: no valid tree for the same input has a lower total cost than the returned tree.

The laws are the correctness argument for the solver. Their exact formulation, and the proof
mechanism used to check them, are still to be decided and will be recorded here.

### `cli/`

The command-line entry point. It reads a guesses list and a candidates list and writes the decision
tree. The output format is not settled yet. Not yet present.

### `bench/`

A standardised benchmark harness. It runs fixed inputs through the solver and reports wall-clock
time, so runs are comparable across machines and across changes. Benchmarks measure performance
only; they do not establish correctness. The harness is present; the solver it drives is not yet.
See [benchmarking.md](benchmarking.md).

## Data flow

```
word lists (words/ or user paths)
          │
          ▼
        cli  ──────────────►  src/ (Bend solver on HVM)
          │                        │
          │                        ▼
          │                 decision tree
          │                        │
          ▼                        ▼
     bench/ (timing)        tree out (stdout or file)

     laws/ ── checks the tree is valid and optimal for the input
```

A normal run starts at the CLI, which reads the two lists and passes them to the solver. The solver
computes the optimal tree and the CLI writes it out. `bench/` drives the same solver entry point
with fixed inputs and measures how long it takes. `laws/` is a separate check over the same
definitions: it establishes that any tree the solver can return satisfies validity and optimality
for its input, independently of how long the run took.

## Open questions

These are deliberately unresolved in the scaffolding and will be settled as the components are
built:

- the concrete tree output format;
- the feedback encoding and how the alphabet is represented;
- how large inputs are split across HVM workers;
- the precise proof mechanism used in `laws/`.
