# Command-line entry point.
#
#   wordle-bend --guesses <file> --candidates <file>
#   wordle-bend --help
#
# Both files hold one word per line. Leading and trailing whitespace on a line
# is ignored, so CRLF line endings and blank lines are fine, and the rest of
# the line is the word. A letter is the code point of one character, unchanged:
# any alphabet works, and the guesses and candidates must agree on case.
import Base
import ./tree.bend as Tree
import ./solve_fast.bend as Solve
import ./json.bend as Json

# ---------------------------------------------------------------------------
# Exit codes and errors
# ---------------------------------------------------------------------------

# 0 is success (and --help). 1 is an input or solving error: a file that cannot
# be read, an empty list, or a solver that returned no tree. 2 is a usage
# error: a missing, repeated or unknown flag.
def status_input() -> U32:
  1

def status_usage() -> U32:
  2

# Every error is one line on stderr. IO.die appends the newline and exits with
# the given code. The result type is whatever the caller needs, so a failed
# parse can stand in for the value it did not produce.
def die_input(-A: Type, +message: String) -> IO(A):
  IO.die(A, status_input(), message)

def die_usage(-A: Type, +message: String) -> IO(A):
  IO.die(A, status_usage(), message)

# ---------------------------------------------------------------------------
# Command line
# ---------------------------------------------------------------------------

# What an argument names, or Unknown when it names nothing.
type Flag is Data:
  Help{}
  Guesses{}
  Candidates{}
  Unknown{}

# The parsed command line. A flag's value stays None until it is seen.
type Args is Data:
  Args{guesses: Maybe<&2, String>, candidates: Maybe<&2, String>, help: Bool}

def choose(cond: Bool, yes: Flag, no: Flag) -> Flag:
  match cond:
    case True{}:
      yes
    case False{}:
      no

# The three flags are the only words that name one; anything else is Unknown.
# String.eq only compares, so the argument stays usable for the error message.
def flag_of(+a: String) -> Flag:
  choose(String.eq(a, "--help"), Help{},
    choose(String.eq(a, "--guesses"), Guesses{},
      choose(String.eq(a, "--candidates"), Candidates{}, Unknown{})))

# The arguments without the program name.
def program_args(args: List<String>) -> List<String>:
  match args:
    case Nil{}:
      Nil{}
    case Con{program, rest}:
      rest

def set_help(opts: Args) -> Args:
  match opts:
    case Args{guesses, candidates, help}:
      Args{guesses, candidates, True{}}

def put_guesses(
  value: String, guesses: Maybe<&2, String>, candidates: Maybe<&2, String>,
  help: Bool
) -> IO(Args):
  match guesses:
    case None{}:
      IO.pure(Args, Args{Some{value}, candidates, help})
    case Some{_}:
      die_usage(Args, "error: --guesses given more than once (try --help)")

def record_guesses(value: String, opts: Args) -> IO(Args):
  match opts:
    case Args{guesses, candidates, help}:
      put_guesses(value, guesses, candidates, help)

def put_candidates(
  value: String, guesses: Maybe<&2, String>, candidates: Maybe<&2, String>,
  help: Bool
) -> IO(Args):
  match candidates:
    case None{}:
      IO.pure(Args, Args{guesses, Some{value}, help})
    case Some{_}:
      die_usage(Args, "error: --candidates given more than once (try --help)")

def record_candidates(value: String, opts: Args) -> IO(Args):
  match opts:
    case Args{guesses, candidates, help}:
      put_candidates(value, guesses, candidates, help)

# Walk the arguments one at a time. `flag` is the classification of `arg`, and
# `rest` is what follows it; the first parameter is the list the recursion
# shrinks, as Bend's termination check requires. A value flag reads its value
# from `rest` here, so a trailing "--guesses" is a clear error.
def run_steps(rest: List<String>, flag: Flag, +arg: String, +opts: Args) -> IO(Args):
  match rest flag:
    case Nil{} Help{}:
      IO.pure(Args, set_help(opts))
    case Con{+next, more} Help{}:
      run_steps(more, flag_of(next), next, set_help(opts))
    case Nil{} Guesses{}:
      die_usage(Args, "error: --guesses needs a file argument (try --help)")
    case Con{+value, Nil{}} Guesses{}:
      record_guesses(value, opts)
    case Con{+value, Con{+next, more}} Guesses{}:
      do IO<Args>:
        opts2 : Args <- record_guesses(value, opts)
        run_steps(more, flag_of(next), next, opts2)
    case Nil{} Candidates{}:
      die_usage(Args, "error: --candidates needs a file argument (try --help)")
    case Con{+value, Nil{}} Candidates{}:
      record_candidates(value, opts)
    case Con{+value, Con{+next, more}} Candidates{}:
      do IO<Args>:
        opts2 : Args <- record_candidates(value, opts)
        run_steps(more, flag_of(next), next, opts2)
    case _ Unknown{}:
      die_usage(Args, "error: unknown flag or argument '" ++ arg ++ "' (try --help)")

def parse_args(args: List<String>, +opts: Args) -> IO(Args):
  match args:
    case Nil{}:
      IO.pure(Args, opts)
    case Con{+arg, rest}:
      run_steps(rest, flag_of(arg), arg, opts)

# ---------------------------------------------------------------------------
# Help
# ---------------------------------------------------------------------------

def print_help() -> IO(Unit):
  do IO<Unit>:
    IO.print("usage: wordle-bend --guesses <file> --candidates <file>")
    IO.print("       wordle-bend --help")
    IO.print("")
    IO.print("Read a guesses list and a candidates list, solve the game, and print")
    IO.print("the optimal decision tree as JSON on stdout.")
    IO.print("")
    IO.print("Flags:")
    IO.print("  --guesses <file>     words that may be played as a guess")
    IO.print("  --candidates <file>  words that may be the answer")
    IO.print("  --help               print this help and exit")
    IO.print("")
    IO.print("Input: one word per line in each file. Leading and trailing")
    IO.print("whitespace on a line is ignored, so CRLF files and blank lines are")
    IO.print("fine. A word is any non-empty text without whitespace, and a letter")
    IO.print("is the code point of one character, unchanged: any alphabet works.")
    IO.print("")
    IO.print("Output: one JSON tree on stdout, then a newline. A tree is")
    IO.print("[guess, kids], a guess is a list of code points, a kid is")
    IO.print("[feedback, tree], and a feedback is a list of 0 (gray), 1 (yellow)")
    IO.print("or 2 (green).")
    IO.print("")
    IO.print("Exit codes: 0 success or --help, 1 input or solving error,")
    IO.print("2 usage error. An error prints one line on stderr.")

# ---------------------------------------------------------------------------
# Files
# ---------------------------------------------------------------------------

# Read a whole file in chunks until a read returns no bytes. File.read answers
# at most the requested count, so one call cannot see past it. The fuel bounds
# the loop for the termination checker: one million chunks of one megabyte is
# a terabyte, past any file a run should need.
def chunk_size() -> U32:
  1000000

def max_chunks() -> Nat:
  1000000n

def open_result(path: String, opened: Result<&1, &1, U32 & String, File>) -> IO(File):
  match opened:
    case Done{file}:
      IO.pure(File, file)
    case Fail{e}:
      (code, message) = e
      IO.die(File, status_input(), "error: cannot open " ++ path ++ ": " ++ message)

def open_file(+path: String) -> IO(File):
  do IO<File>:
    opened : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    open_result(path, opened)

def close_then_die(file: File, +message: String) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    Unit <- File.close(file)
    IO.die(List<&2, String>, status_input(), message)

# The reader alternates between asking for the next chunk and handling the one
# that arrived. The state is a parameter so the loop is one self-recursive def:
# Bend has no forward references and rejects mutual recursion.
type Reading is Type:
  NeedRead{file: File}
  HaveChunk{pair: File & Result<&1, &1, U32 & String, String>}

# `acc` holds the chunks newest first, so concatenating its reverse restores
# the file order without copying the text at every step. An empty chunk is the
# end of the file.
def read_loop(
  fuel: Nat, +acc: List<&2, String>, +path: String, state: Reading
) -> IO(List<&2, String>):
  match fuel:
    case 0n:
      IO.die(List<&2, String>, status_input(), "error: " ++ path ++ " is too large to read")
    case 1n+rest:
      match state:
        case NeedRead{file}:
          IO.bind(File & Result<&1, &1, U32 & String, String>, List<&2, String>,
                  File.read(file, chunk_size()),
                  pair => read_loop(rest, acc, path, HaveChunk{pair}))
        case HaveChunk{pair}:
          (file, result) = pair
          match result:
            case Fail{e}:
              (code, message) = e
              close_then_die(file, "error: cannot read " ++ path ++ ": " ++ message)
            case Done{+text}:
              match text:
                case SNil{}:
                  do IO<List<&2, String>>:
                    Unit <- File.close(file)
                    IO.pure(List<&2, String>, acc)
                case SCon{h, t}:
                  read_loop(rest, SCon{h, t} <> acc, path, NeedRead{file})

def read_file(+path: String) -> IO(String):
  do IO<String>:
    file : File <- open_file(path)
    chunks : List<&2, String> <- read_loop(max_chunks(), Nil{}, path, NeedRead{file})
    return String.concat(List.reverse(&2, String, chunks))

# ---------------------------------------------------------------------------
# Words
# ---------------------------------------------------------------------------

def word_of_string(s: String) -> +List<Nat>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      U32.to_nat(c) <> word_of_string(t)

# One trimmed line per word, blank lines dropped. Trimming handles the CR of a
# CRLF line and any surrounding whitespace; an empty result is a blank line.
# Both walks make one recursive call per step and pass its result to a helper
# that chooses what to do with it. Writing the call in both branches of a Bool
# makes the compiler evaluate both branches, which is exponential.
def keep_line(word: String, +rest: List<&2, String>) -> List<&2, String>:
  match word:
    case SNil{}:
      rest
    case SCon{h, t}:
      SCon{h, t} <> rest

def trimmed_lines(lines: +List<String>) -> +List<String>:
  match lines:
    case Nil{}:
      Nil{}
    case Con{line, rest}:
      keep_line(String.trim(line), trimmed_lines(rest))

def words_of_lines(lines: +List<String>) -> +List<+List<Nat>>:
  match lines:
    case Nil{}:
      Nil{}
    case Con{line, rest}:
      word_of_string(line) <> words_of_lines(rest)

def words_of_text(text: String) -> +List<+List<Nat>>:
  words_of_lines(trimmed_lines(String.lines(text)))

# ---------------------------------------------------------------------------
# Run
# ---------------------------------------------------------------------------

def emit(tree: Maybe<Tree.Tree>) -> IO(Unit):
  match tree:
    case None{}:
      die_input(Unit, "error: solve returned no tree")
    case Some{t}:
      IO.print(Json.print(t))

def with_guesses(
  guesses: +List<+List<Nat>>, candidates: +List<+List<Nat>>,
  +candidates_path: String
) -> IO(Unit):
  match candidates:
    case Nil{}:
      die_input(Unit, "error: no candidates in " ++ candidates_path)
    case Con{+c, +ct}:
      emit(Solve.solve(guesses, Con{c, ct}))

# An empty list is an input error, reported before the solver runs. Matching
# the list and rebuilding it is how the check sees the words without reading
# the list twice.
def solve_lists(
  guesses: +List<+List<Nat>>, candidates: +List<+List<Nat>>,
  +guesses_path: String, +candidates_path: String
) -> IO(Unit):
  match guesses:
    case Nil{}:
      die_input(Unit, "error: no guesses in " ++ guesses_path)
    case Con{+g, +gt}:
      with_guesses(Con{g, gt}, candidates, candidates_path)

def solve_files(+guesses_path: String, +candidates_path: String) -> IO(Unit):
  do IO<Unit>:
    guesses_text : String <- read_file(guesses_path)
    candidates_text : String <- read_file(candidates_path)
    guesses : +List<+List<Nat>> = words_of_text(guesses_text)
    candidates : +List<+List<Nat>> = words_of_text(candidates_text)
    solve_lists(guesses, candidates, guesses_path, candidates_path)

def required_candidates(guesses: String, candidates: Maybe<&2, String>) -> IO(Unit):
  match candidates:
    case None{}:
      die_usage(Unit, "error: missing required flag --candidates <file> (try --help)")
    case Some{c}:
      solve_files(guesses, c)

def required_guesses(guesses: Maybe<&2, String>, candidates: Maybe<&2, String>) -> IO(Unit):
  match guesses:
    case None{}:
      die_usage(Unit, "error: missing required flag --guesses <file> (try --help)")
    case Some{g}:
      required_candidates(g, candidates)

def run_flags(help: Bool, guesses: Maybe<&2, String>, candidates: Maybe<&2, String>) -> IO(Unit):
  match help:
    case True{}:
      print_help()
    case False{}:
      required_guesses(guesses, candidates)

def run(opts: Args) -> IO(Unit):
  match opts:
    case Args{guesses, candidates, help}:
      run_flags(help, guesses, candidates)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    opts : Args <- parse_args(program_args(args), Args{None{}, None{}, False{}})
    run(opts)
