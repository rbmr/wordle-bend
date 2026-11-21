# Command-line entry point.
#
#   wordle-bend --guesses <file> --candidates <file>
#
# Both files hold one word per line. Letters are mapped to Nat by their code
# point, with lower-case ASCII folded to upper case so the bundled lists agree.
import Base
import ./feedback.bend as Feedback
import ./tree.bend as Tree
import ./solve.bend as Solve
import ./json.bend as Json

def arg_value(args: List<String>, +flag: String) -> Maybe<String>:
  match args:
    case Con{a, Con{+b, rest}}:
      Feedback.Bool.case(Maybe<String>, String.eq(a, flag), Some{b}, arg_value(b <> rest, flag))
    case _:
      None{}

def letter_code(+c: U32) -> Nat:
  Feedback.Bool.case(Nat, Bool.and(U32.is_ge(c, 97), U32.is_le(c, 122)),
                     U32.to_nat(U32.sub(c, 32)), U32.to_nat(c))

def word_of_string(s: String) -> +List<Nat>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{c}, t}:
      letter_code(c) <> word_of_string(t)

def map_words(lines: +List<String>) -> +List<+List<Nat>>:
  match lines:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      Feedback.Bool.case(+List<+List<Nat>>, String.is_empty(h), map_words(t),
                          word_of_string(h) <> map_words(t))

def lines_to_words(s: String) -> +List<+List<Nat>>:
  map_words(String.lines(s))

def read_file(path: String) -> IO(String):
  do IO<String>:
    file : File <- IO.try(File, File.open(path, "r"))
    pair : File & Result<&1, &1, U32 & String, String> <- File.read(file, 1000000)
    result : Result<&1, &1, U32 & String, String> =
      Pair.snd(File, Result<&1, &1, U32 & String, String>, pair)
    text : String <- IO.try(String, IO.pure(Result<&1, &1, U32 & String, String>, result))
    return text

def output(tree: Maybe<Tree.Tree>) -> IO(Unit):
  match tree:
    case None{}:
      IO.print_err("error: solve returned no tree\n")
    case Some{t}:
      IO.print(Json.print(t) ++ "\n")

def solve_files(guesses_path: String, candidates_path: String) -> IO(Unit):
  do IO<Unit>:
    guesses_text : String <- read_file(guesses_path)
    candidates_text : String <- read_file(candidates_path)
    tree : Maybe<Tree.Tree> = Solve.solve(lines_to_words(guesses_text), lines_to_words(candidates_text))
    output(tree)

def with_candidates(guesses: String, candidates: Maybe<String>) -> IO(Unit):
  match candidates:
    case None{}:
      IO.print_err("error: expected --guesses <file> --candidates <file>\n")
    case Some{c}:
      solve_files(guesses, c)

def with_guesses(guesses: Maybe<String>, candidates: Maybe<String>) -> IO(Unit):
  match guesses:
    case None{}:
      IO.print_err("error: expected --guesses <file> --candidates <file>\n")
    case Some{g}:
      with_candidates(g, candidates)

def main() -> IO(Unit):
  do IO<Unit>:
    args1 : List<String> <- IO.args()
    args2 : List<String> <- IO.args()
    with_guesses(arg_value(args1, "--guesses"), arg_value(args2, "--candidates"))
