# The bag of per-word depth facts, and the search that takes one out.
#
# The node built from a guess and its class children has a `Some` depth at every
# candidate. The class passes prove that fact for their own word lists; this
# module flattens those facts into one linear list of (word, fact) pairs and
# strings them back together in candidate order. The word list is carried as
# reusable data beside the linear bag so a candidate can be located without
# consuming the proofs of the candidates still to come.
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ../src/groups.bend as Groups
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as Fb
import ./groups.bend as Grp
import ./groupsdistinct.bend as GD
import ./cover_list.bend as CoverL

# The depth fact of one candidate at a node.
def VB.Fact(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>) -> Type:
  {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool}

# The linear bag of facts, one entry per word.
def VB.Bag(+g: +List<Nat>, +kids: +List<Tree.Child>) -> Type:
  List<&2, Sigma<&2, &2, +List<Nat>, w => {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool}>>

# An entry.
def VB.entry(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    f: VB.Fact(g, kids, w)) ->
  Sigma<&2, &2, +List<Nat>, x => {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, x)) == True{} : Bool}>:
  Tuple{w, f}

# The words of a bag, in the same order, as reusable data.
def VB.words(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +bag: List<&2, Sigma<&2, &2, +List<Nat>, w => {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool}>>) -> +List<+List<Nat>>:
  match bag:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match h:
        case Tuple{w, f}:
          w <> VB.words(g, kids, t)

# Equal words compare equal.
def VB.word_eq_of_eq(+a: +List<Nat>, +b: +List<Nat>, e: {a == b : +List<Nat>}) ->
  {Feedback.word_eq(a, b) == True{} : Bool}:
  +e1 : {Feedback.word_eq(a, b) == Feedback.word_eq(a, a) : Bool} =
    Equal.cong(+List<Nat>, Bool, x => Feedback.word_eq(a, x), b, a, Equal.sym(+List<Nat>, a, b, e))
  Equal.trans(Bool, Feedback.word_eq(a, b), Feedback.word_eq(a, a), True{}, e1,
    Fb.FbPrf.word_eq_refl(a))

# A word in a cons list whose head differs lies in the tail.
def VB.in_words_tail(+w: +List<Nat>, +x: +List<Nat>, +t: +List<+List<Nat>>,
    +ne: {Feedback.word_eq(w, x) == False{} : Bool},
    m: Grp.Grp.InWords(w, x <> t)) -> Grp.Grp.InWords(w, t):
  match m:
    case Inl{e}:
      eq1 : {Feedback.word_eq(w, x) == True{} : Bool} = VB.word_eq_of_eq(w, x, e)
      Empty.absurd(Grp.Grp.InWords(w, t),
        Logic.Proof.true_ne_false(Equal.trans(Bool, True{}, Feedback.word_eq(w, x), False{},
          Equal.sym(Bool, Feedback.word_eq(w, x), True{}, eq1), ne)))
    case Inr{m2}:
      m2

# Put a skipped entry back in front of the bag.
def VB.rebuild(+g: +List<Nat>, +kids: +List<Tree.Child>, +x: +List<Nat>,
    f: VB.Fact(g, kids, x), +w: +List<Nat>,
    r: VB.Fact(g, kids, w) & VB.Bag(g, kids)) ->
  VB.Fact(g, kids, w) & VB.Bag(g, kids):
  match r:
    case (fr, br):
      (fr, VB.entry(g, kids, x, f) <> br)

# The fact at the head, moved to an equal word.
def VB.fact_eq(+g: +List<Nat>, +kids: +List<Tree.Child>, +x: +List<Nat>,
    +w: +List<Nat>, f: VB.Fact(g, kids, x), e: {w == x : +List<Nat>}) ->
  VB.Fact(g, kids, w):
  %Equal.sym(+List<Nat>, w, x, e) : VB.Fact(g, kids, _)
  f

# Find a candidate in the bag by membership in the carried word list.
def VB.take(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +bag: List<&2, Sigma<&2, &2, +List<Nat>, w => {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool}>>,
    +w: +List<Nat>, m: Grp.Grp.InWords(w, VB.words(g, kids, bag)))
    -> VB.Fact(g, kids, w) & VB.Bag(g, kids):
  match bag:
    case Nil{}:
      Empty.absurd(VB.Fact(g, kids, w) & VB.Bag(g, kids), m)
    case Con{h, t}:
      match h:
        case Tuple{x, f}:
          match m:
            case Inl{e}:
              (VB.fact_eq(g, kids, x, w, f, e), t)
            case Inr{m2}:
              VB.rebuild(g, kids, x, f, w, VB.take(g, kids, t, w, m2))

# The append of two bags.
def VB.app(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +xs: List<&2, Sigma<&2, &2, +List<Nat>, w => {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool}>>,
    +ys: List<&2, Sigma<&2, &2, +List<Nat>, w => {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool}>>) -> VB.Bag(g, kids):
  List.append(&2, Sigma<&2, &2, +List<Nat>, w => {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool}>, xs, ys)

# The words of an appended bag are the appended words.
def VB.words_append(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +xs: List<&2, Sigma<&2, &2, +List<Nat>, w => {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool}>>,
    +ys: List<&2, Sigma<&2, &2, +List<Nat>, w => {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool}>>) ->
  {VB.words(g, kids, VB.app(g, kids, xs, ys))
   == List.append(&2, +List<Nat>, VB.words(g, kids, xs), VB.words(g, kids, ys))
   : +List<+List<Nat>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      match h:
        case Tuple{w, f}:
          Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>, l => w <> l,
            VB.words(g, kids, VB.app(g, kids, t, ys)),
            List.append(&2, +List<Nat>, VB.words(g, kids, t), VB.words(g, kids, ys)),
            VB.words_append(g, kids, t, ys))

# A reusable name for a bag value.
def VB.copy(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +bag: List<&2, Sigma<&2, &2, +List<Nat>, w =>
      {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool}>>) ->
  List<&2, Sigma<&2, &2, +List<Nat>, w =>
      {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool}>>:
  bag
