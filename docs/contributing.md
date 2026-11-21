# Contributing

The repository is public. Everything committed to it is visible to anyone, permanently, including
in history. Keep contributions about the code and the project, and nothing else.

## Branches

Never commit or push to `main`. All work happens on a branch named:

```
<type>/<kebab-desc>
```

`<type>` is one of:

| Type | Use for |
| --- | --- |
| `feat` | a new feature |
| `fix` | a bug fix |
| `docs` | documentation only |
| `chore` | maintenance that is not a feature, fix, or refactor |
| `refactor` | a change to structure without changing behaviour |
| `test` | tests only |
| `perf` | a performance improvement |
| `ci` | CI configuration |
| `build` | build system or dependency changes |

`<kebab-desc>` is a short lowercase description with words joined by hyphens, for example
`feat/setup-laws` or `docs/repo-scaffold`.

The name of the branch is checked before a push and again by CI on the pull request.

## Commits

Every commit message is a Conventional Commit:

```
<type>(<optional scope>): <lowercase imperative summary>
```

The type is one of the branch types above. The summary is lowercase, imperative ("add the tree
printer", not "added" or "Adds"), and says what changed and why. Keep it terse; put longer
reasoning in the commit body if it is needed.

Examples:

```
docs: describe the solver data flow
feat(laws): state the optimality property
ci: check branch names on pull requests
```

Do not add co-author trailers, or any other trailer that attributes work to a person or tool.

## Hooks

The repository ships hooks in `.githooks/`. Install them once per clone:

```sh
git config core.hooksPath .githooks
```

- `commit-msg` rejects a non-conventional commit message, and rejects any message containing a
  `Co-authored-by` trailer.
- `pre-push` rejects a push to `main`, and rejects a branch whose name does not match
  `<type>/<kebab-desc>`.

The hooks are a convenience. CI enforces the same rules on the pull request, so a bypassed hook
does not get a non-conforming change merged.

## Laws and proofs

Laws are stated in `LAWS.bend` and proved in `PROOF.bend`, with helper lemmas under `proofs/`. All
eight laws are proved. Run the proof gate before pushing:

```sh
scripts/check-proofs.sh
```

CI runs the same script, so a local pass and a green `proofs` check mean the same thing. The gate
requires a proof for every law, except the laws named in `PENDING_LAWS` at the repository root.

`PENDING_LAWS` lists laws that are stated but intentionally unproved, one name per line. Blank
lines and `#` comments are ignored. It is empty now, and the target is to keep it empty.

- Adding a name to `PENDING_LAWS` needs an explicit explanation in the pull request description:
  which law, why it cannot be proved yet, and what will make it provable.
- The name must be a law in `LAWS.bend` and must not have a proof in `PROOF.bend`. A typo, or a law
  that has already been proved, fails the gate.
- The list should only shrink over time. Remove a name in the same pull request that adds its proof.
- The target is an empty list.

See [testing.md](testing.md) for what the gate checks, [proofs.md](proofs.md) for the proof modules,
and [laws.md](laws.md) for the laws themselves.

A performance change must keep every law proved. A faster solver that weakens a law, leaves a proof
broken, or moves a law into `PENDING_LAWS` is not an optimisation. See
[performance.md](performance.md).

## Protected files

Some files define what the program must do and how that is measured. A pull request that changes
any of them fails the `protected-files` check:

- `LAWS.bend` states the goal, and `scripts/check-proofs.sh` is the gate that proves it. Weakening
  either one makes every other check meaningless.
- `PENDING_LAWS` records the laws that are allowed to remain unproved. A name may be removed, but
  no name may be added.
- `bench/run.sh`, `bench/sample.sh`, `bench/start.sh`, `bench/status.sh` and `bench/record.sh` are
  the benchmark harness. Changing them changes the numbers that every later result is compared
  against.
- `bench/results.csv` holds measured runs. Existing lines may not be changed or removed. New rows
  may only be appended at the end.
- `.github/workflows/*.yml` and `.githooks/*` enforce the checks, locally and in CI. This includes
  the pinned toolchain versions and the Bend checksum in the `env:` block of
  `.github/workflows/proofs.yml`.
- `scripts/guard-protected.sh` is the guard itself.

The guard runs from the base branch's copy of the workflow and reads the pull request as git
objects. It never checks out the pull request's tree or runs its code. Documentation is not
protected, so `docs/` can be edited freely, but a statement may not be removed from `LAWS.bend`.

Changing a protected file is the maintainer's job. The maintainer lifts the `protected-files`
requirement from the branch protection for that one merge, merges the change, and restores the
requirement immediately afterwards.

## Pull requests

1. Push the branch and open a pull request into `main` with `gh pr create`.
2. The PR title is itself a conventional commit, in the same format as a commit subject.
3. CI checks the PR title, every commit subject in the branch, the head branch name, the proof
   gate, and that no protected file is changed.
4. Merge with a merge commit only:

   ```sh
   gh pr merge <n> --merge --delete-branch
   ```

   Squash merges and rebase merges are disabled on the repository. Do not change the merge method.
5. Update the local default branch afterwards:

   ```sh
   git checkout main && git pull
   ```

Prefer small, logically separate commits and pull requests. A commit should do one thing, so that
the history stays readable and a change can be reverted on its own.

## Repository hygiene

This repository is public and must contain only things about the code and the project.

- No personal details: no real names, email addresses, hostnames, IP addresses, home directory
  paths, machine names, private network names, or credentials of any kind.
- No attribution to people or tools beyond the repository's configured commit identity. No co-author trailers, no "generated by" lines.
- No secrets, tokens, keys, or private data, in any file or in history.
- Do not commit local editor state, build output, caches, or machine-specific configuration. Add
  such paths to `.gitignore` instead of committing them.
- Do not commit word list data without recording its provenance, as described in
  [licenses.md](licenses.md).

If a secret is ever committed, treat it as compromised: rotate it, and do not assume removing it in
a later commit is sufficient, because it remains in history.
