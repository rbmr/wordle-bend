# Licences

## Code

The code in this repository is released under the MIT licence. The full text is in
[LICENSE](../LICENSE).

In short: anyone may use, copy, modify, merge, publish, distribute, sublicense, and sell copies of
the software, provided the copyright notice and permission notice are included in all copies or
substantial portions. The software is provided as is, without warranty of any kind.

New source files do not need a per-file licence header. The repository-level [LICENSE](../LICENSE)
covers them.

## Bundled word lists

Word lists are data with their own origin and their own terms, and those terms are frequently not
MIT, and sometimes not permissive at all. The MIT licence on the code does not extend to data
bundled in `words/`.

The lists in `words/` were carried over from the earlier, unverified Rust implementation of this
solver; `words/guesses.txt` was then upper-cased as recorded below. No upstream source is asserted
here, and no licence is claimed for them beyond what that earlier implementation established. If
the lists are replaced or a new list is added, record its source, licence, attribution and any
modification in this document in the same change.

| File | Contents | Provenance |
| --- | --- | --- |
| `words/candidates.txt` | 2,341 five-letter candidate words, one per line. | Carried over unchanged from the earlier, unverified implementation of this solver. |
| `words/guesses.txt` | 14,854 five-letter guess words, one per line. | Carried over from the earlier, unverified implementation of this solver, then upper-cased as described below. |

`words/guesses.txt` was upper-cased in place: its ASCII letters were mapped from `a`-`z` to
`A`-`Z` with no other change. Line order and line count are unchanged. The CLI reads letters as
exact code points and does not fold case, so `words/candidates.txt` and `words/guesses.txt` must
use the same case for a guess ever to equal a candidate; both are now upper case.

A list whose licence cannot be established, or whose terms do not permit redistribution in a public
repository, is not bundled.

## Contributions

By opening a pull request you confirm you have the right to contribute the change under the terms
above, and that any data you add is either your own or is added with its provenance and terms
recorded as described here.
