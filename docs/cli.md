# Command line

The command-line entry point reads a guesses list and a candidates list, solves the game, and
prints the decision tree as JSON.

## Building and running

`bend` parses its own options before the program's, so a flag such as `--guesses` is taken by
`bend` instead of reaching the program. Build the binary first, then run it:

```sh
bend src/main.bend -o wordle-bend
./wordle-bend --guesses words/guesses.txt --candidates words/candidates.txt
```

## Usage

```text
wordle-bend --guesses <file> --candidates <file>
wordle-bend --help
```

`--guesses <file>` and `--candidates <file>` are required and may appear in either order. Each
takes its value from the next argument; the `--flag=value` form is not accepted. `--help` prints
the same usage text as this document at a coarser grain and exits 0. It may appear anywhere
among the other flags, and the request for help wins over a missing file flag, but not over an
unknown argument.

The first argument, the program name the runtime passes, is ignored. Every other argument must
be one of the three flags or the value of a file flag. An unknown flag or a stray argument is
a usage error, as is giving `--guesses` or `--candidates` more than once or leaving a file flag
without a value.

## Input

Each file holds one word per line. A line is read as follows:

- Leading and trailing whitespace is removed. This makes a CRLF file read like an LF file and
  makes a blank or whitespace-only line empty.
- An empty line is skipped.
- The rest of the line is the word. A word is any non-empty text without whitespace, over any
  alphabet.

A letter is the exact code point of one character, with nothing added, removed or changed in
case. Case is not folded, so a guess and a candidate compare equal only when every code point
is equal: both lists must use the same case. The bundled lists are upper case, so the trees
they produce contain upper-case code points. A list in another alphabet or another case works
without being changed, as long as the guesses and the candidates agree with each other.
Folding case, which earlier versions of the CLI did, would alter the input words instead of
reading them, and would break words that use letters outside ASCII.

Both files are read to the end. The reader asks `File.read` for one megabyte at a time and
repeats until a read returns no bytes, so no list is truncated at a fixed size. The loop is
bounded at one million chunks, a terabyte, which no realistic list reaches; a file past that
bound is an input error.

## Output

On success the program writes exactly one line to stdout, the tree as JSON, followed by a
newline. Nothing else is written to stdout. The encoding is arrays only:

```text
tree     = [ guess, kids ]
guess    = [ letter, ... ]
kids     = [ child, ... ]
child    = [ feedback, tree ]
feedback = [ colour, ... ]
```

A letter is a decimal code point: one or more digits, with no sign. The printer writes it in
the usual form, without leading zeros, and writes `0` for zero; so the letters of `abc` are
`97`, `98` and `99`. A colour is `0` (gray), `1` (yellow) or `2` (green). For example, a tree
whose first guess is `abc` and whose first child is a green-green-green feedback followed by
the guess `abd` prints as:

```text
[[97,98,99],[[2,2,2],[[97,98,100],[]]]]
```

The parser reads each letter back from its digits, so `97` is the single letter with code point
97 and not two letters. `Json.parse` accepts exactly the grammar above and rejects anything
else, including trailing text.

The JSON is one line so that it can be piped to another program without reassembly.

## Exit codes

| Code | Meaning |
| --- | --- |
| `0` | Success, or `--help`. |
| `1` | An input or solving error: a file that cannot be opened or read, an empty guesses or candidates list, or a solver that returned no tree. |
| `2` | A usage error: a missing, repeated or unknown flag, or a file flag without a value. |

Every error prints one line on stderr and nothing on stdout. The messages are:

```text
error: --guesses needs a file argument (try --help)
error: --candidates needs a file argument (try --help)
error: --guesses given more than once (try --help)
error: --candidates given more than once (try --help)
error: unknown flag or argument '<argument>' (try --help)
error: missing required flag --guesses <file> (try --help)
error: missing required flag --candidates <file> (try --help)
error: cannot open <path>: <system message>
error: cannot read <path>: <system message>
error: no guesses in <path>
error: no candidates in <path>
error: solve returned no tree
error: <path> is too large to read
```

An empty list is an input error even when the other list is valid, and it is reported before the
solver runs.

## Examples

Print the help and exit 0:

```sh
./wordle-bend --help
```

Solve the bundled lists:

```sh
./wordle-bend --guesses words/guesses.txt --candidates words/candidates.txt
```

Read a CRLF file with blank lines and keep the words as they are:

```sh
printf 'abc\r\n\r\ndef\r\n' > guesses.txt
printf 'abc\r\n' > candidates.txt
./wordle-bend --guesses guesses.txt --candidates candidates.txt
```

Report a usage error and exit 2:

```sh
./wordle-bend --guesses words/guesses.txt
# error: missing required flag --candidates <file> (try --help)
```

Report an unreadable file and exit 1:

```sh
./wordle-bend --guesses missing.txt --candidates words/candidates.txt
# error: cannot open missing.txt: No such file or directory
```
