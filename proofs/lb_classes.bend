# Lower bounds for valid trees, part 5: the first-match partition over children.
#
# A node with guess `g` and children `kids` sends each candidate down the first
# child whose feedback equals the candidate's feedback. The classes of the node
# are those filters: the child at a position takes the words of the remaining
# list that are not the guess and whose feedback is that child's feedback, and
# the words it does not take go on to the later children. So the classes plus
# the leftover words partition the candidate list.
#
# A child whose feedback repeats an earlier child's gets an empty class, because
# every word with that feedback was taken earlier: the partition follows the
# first match, exactly like `Tree.lookup` and `Tree.depth.go`.
#
# This module defines the partition and proves the pure list facts the capacity
# bound needs: the class sizes plus the leftover length are the candidate count,
# and a filter never raises the multiplicity of a word or the largest
# multiplicity of a list.
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ../src/groups.bend as Groups
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./classbound_nat.bend as CB
import ./lb_twice.bend as Twice
import ./lb_nodup.bend as NodupProof

# One class: the child tree and the candidates that reach it.
type LB.Class is Data:
  LClass{tree: Tree.Tree, words: +List<+List<Nat>>}

# The keep test, with the two comparisons as parameters: the word is not the
# guess, and the child's feedback is the word's feedback.
def LB.keepb(bw: Bool, bf: Bool) -> Bool:
  Feedback.Bool.case(Bool, bw, False{}, bf)

def LB.keep(+g: +List<Nat>, +f: +List<Feedback.Color>, +h: +List<Nat>) -> Bool:
  LB.keepb(Feedback.word_eq(g, h), Feedback.feedback_eq(f, Feedback.feedback(g, h)))

# The words of `S` that the child takes.
def LB.keepw_b(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +S: +List<+List<Nat>>) -> +List<+List<Nat>>:
  match S:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Feedback.Bool.case(+List<+List<Nat>>, LB.keep(g, f, h), h <> LB.keepw_b(g, f, t),
                         LB.keepw_b(g, f, t))

# The words of `S` left for the later children.
def LB.remw(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +S: +List<+List<Nat>>) -> +List<+List<Nat>>:
  match S:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Feedback.Bool.case(+List<+List<Nat>>, LB.keep(g, f, h), LB.remw(g, f, t),
                         h <> LB.remw(g, f, t))

# One step of `keepw_b`, with the test as a parameter.
def LB.keepw_of(+g: +List<Nat>, +f: +List<Feedback.Color>, +h: +List<Nat>,
    +t: +List<+List<Nat>>, b: Bool) -> +List<+List<Nat>>:
  Feedback.Bool.case(+List<+List<Nat>>, b, h <> LB.keepw_b(g, f, t),
                     LB.keepw_b(g, f, t))

# One step of `remw`, with the test as a parameter.
def LB.remw_of(+g: +List<Nat>, +f: +List<Feedback.Color>, +h: +List<Nat>,
    +t: +List<+List<Nat>>, b: Bool) -> +List<+List<Nat>>:
  Feedback.Bool.case(+List<+List<Nat>>, b, LB.remw(g, f, t), h <> LB.remw(g, f, t))

# The classes of a node, in child order.
def LB.classes(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>) -> +List<LB.Class>:
  match kids:
    case Nil{}:
      Nil{}
    case Con{c, rest}:
      match c:
        case Tree.Child{f, t}:
          LClass{t, LB.keepw_b(g, f, S)} <> LB.classes(g, rest, LB.remw(g, f, S))

# The words no child takes.
def LB.rem(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>) -> +List<+List<Nat>>:
  match kids:
    case Nil{}:
      S
    case Con{c, rest}:
      match c:
        case Tree.Child{f, t}:
          LB.rem(g, rest, LB.remw(g, f, S))

# The total size of the classes.
def LB.totSize(+cls: +List<LB.Class>) -> Nat:
  match cls:
    case Nil{}:
      0n
    case Con{c, rest}:
      match c:
        case LClass{t, ws}:
          Nat.add(Groups.len_words(ws), LB.totSize(rest))

# The length of a cons, and of an append of one word.
def LB.len_cons(+h: +List<Nat>, +t: +List<+List<Nat>>) ->
  {List.length(&2, +List<Nat>, h <> t)
   == Nat.add(1n, List.length(&2, +List<Nat>, t)) : Nat}:
  {==}

# The two filters split the length of the list, with the test as a parameter.
def LB.keep_len_go(+g: +List<Nat>, +f: +List<Feedback.Color>, +h: +List<Nat>,
    +t: +List<+List<Nat>>, b: Bool, +eb: {b == LB.keep(g, f, h) : Bool},
    ih: {List.length(&2, +List<Nat>, t)
         == Nat.add(List.length(&2, +List<Nat>, LB.keepw_b(g, f, t)),
                    List.length(&2, +List<Nat>, LB.remw(g, f, t))) : Nat}) ->
  {List.length(&2, +List<Nat>, h <> t)
   == Nat.add(List.length(&2, +List<Nat>, LB.keepw_of(g, f, h, t, b)),
              List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, b))) : Nat}:
  match b:
    case True{}:
      +lk : Nat = List.length(&2, +List<Nat>, LB.keepw_b(g, f, t))
      +lr : Nat = List.length(&2, +List<Nat>, LB.remw(g, f, t))
      +lt : Nat = List.length(&2, +List<Nat>, t)
      +e_l : {List.length(&2, +List<Nat>, h <> t) == Nat.add(1n, lt) : Nat} =
        LB.len_cons(h, t)
      +e_k : {List.length(&2, +List<Nat>, LB.keepw_of(g, f, h, t, True{}))
              == Nat.add(1n, lk) : Nat} =
        LB.len_cons(h, LB.keepw_b(g, f, t))
      +c1 : {Nat.add(1n, lt) == Nat.add(1n, Nat.add(lk, lr)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(1n, x), lt, Nat.add(lk, lr), ih)
      +c2 : {Nat.add(1n, Nat.add(lk, lr)) == Nat.add(Nat.add(1n, lk), lr) : Nat} =
        Equal.sym(Nat, Nat.add(Nat.add(1n, lk), lr), Nat.add(1n, Nat.add(lk, lr)),
          NatProof.NatPrf.add_assoc(1n, lk, lr))
      +c3 : {Nat.add(Nat.add(1n, lk), lr)
             == Nat.add(List.length(&2, +List<Nat>, LB.keepw_of(g, f, h, t, True{})), lr) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(x, lr), Nat.add(1n, lk),
          List.length(&2, +List<Nat>, LB.keepw_of(g, f, h, t, True{})),
          Equal.sym(Nat, List.length(&2, +List<Nat>, LB.keepw_of(g, f, h, t, True{})),
            Nat.add(1n, lk), e_k))
      Equal.trans(Nat, List.length(&2, +List<Nat>, h <> t), Nat.add(1n, lt),
        Nat.add(List.length(&2, +List<Nat>, LB.keepw_of(g, f, h, t, True{})), lr),
        e_l,
        Equal.trans(Nat, Nat.add(1n, lt), Nat.add(1n, Nat.add(lk, lr)),
          Nat.add(List.length(&2, +List<Nat>, LB.keepw_of(g, f, h, t, True{})), lr),
          c1, Equal.trans(Nat, Nat.add(1n, Nat.add(lk, lr)),
            Nat.add(Nat.add(1n, lk), lr),
            Nat.add(List.length(&2, +List<Nat>, LB.keepw_of(g, f, h, t, True{})), lr),
            c2, c3)))
    case False{}:
      +lk : Nat = List.length(&2, +List<Nat>, LB.keepw_b(g, f, t))
      +lr : Nat = List.length(&2, +List<Nat>, LB.remw(g, f, t))
      +lt : Nat = List.length(&2, +List<Nat>, t)
      +e_l : {List.length(&2, +List<Nat>, h <> t) == Nat.add(1n, lt) : Nat} =
        LB.len_cons(h, t)
      +e_r : {List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, False{}))
              == Nat.add(1n, lr) : Nat} =
        LB.len_cons(h, LB.remw(g, f, t))
      +c1 : {Nat.add(1n, lt) == Nat.add(1n, Nat.add(lk, lr)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(1n, x), lt, Nat.add(lk, lr), ih)
      +c2 : {Nat.add(1n, Nat.add(lk, lr)) == Nat.add(lk, Nat.add(1n, lr)) : Nat} =
        Equal.trans(Nat, Nat.add(1n, Nat.add(lk, lr)), Nat.add(Nat.add(1n, lk), lr),
          Nat.add(lk, Nat.add(1n, lr)),
          Equal.sym(Nat, Nat.add(Nat.add(1n, lk), lr), Nat.add(1n, Nat.add(lk, lr)),
            NatProof.NatPrf.add_assoc(1n, lk, lr)),
          Equal.trans(Nat, Nat.add(Nat.add(1n, lk), lr), Nat.add(Nat.add(lk, 1n), lr),
            Nat.add(lk, Nat.add(1n, lr)),
            Equal.cong(Nat, Nat, x => Nat.add(x, lr), Nat.add(1n, lk), Nat.add(lk, 1n),
              NatProof.NatPrf.add_comm(1n, lk)),
            NatProof.NatPrf.add_assoc(lk, 1n, lr)))
      +c3 : {Nat.add(lk, Nat.add(1n, lr))
             == Nat.add(lk, List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, False{}))) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(lk, x), Nat.add(1n, lr),
          List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, False{})),
          Equal.sym(Nat, List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, False{})),
            Nat.add(1n, lr), e_r))
      Equal.trans(Nat, List.length(&2, +List<Nat>, h <> t), Nat.add(1n, lt),
        Nat.add(lk, List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, False{}))),
        e_l,
        Equal.trans(Nat, Nat.add(1n, lt), Nat.add(1n, Nat.add(lk, lr)),
          Nat.add(lk, List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, False{}))),
          c1, Equal.trans(Nat, Nat.add(1n, Nat.add(lk, lr)),
            Nat.add(lk, Nat.add(1n, lr)),
            Nat.add(lk, List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, False{}))),
            c2, c3)))

# Rewrite the test of the two filters.
def LB.keepw_eq(+g: +List<Nat>, +f: +List<Feedback.Color>, +h: +List<Nat>,
    +t: +List<+List<Nat>>, b: Bool, +eb: {b == LB.keep(g, f, h) : Bool}) ->
  {LB.keepw_b(g, f, h <> t) == LB.keepw_of(g, f, h, t, b) : +List<+List<Nat>>}:
  Equal.cong(Bool, +List<+List<Nat>>,
    x => Feedback.Bool.case(+List<+List<Nat>>, x, h <> LB.keepw_b(g, f, t),
                             LB.keepw_b(g, f, t)),
    LB.keep(g, f, h), b, Equal.sym(Bool, b, LB.keep(g, f, h), eb))

def LB.remw_eq(+g: +List<Nat>, +f: +List<Feedback.Color>, +h: +List<Nat>,
    +t: +List<+List<Nat>>, b: Bool, +eb: {b == LB.keep(g, f, h) : Bool}) ->
  {LB.remw(g, f, h <> t) == LB.remw_of(g, f, h, t, b) : +List<+List<Nat>>}:
  Equal.cong(Bool, +List<+List<Nat>>,
    x => Feedback.Bool.case(+List<+List<Nat>>, x, LB.remw(g, f, t),
                             h <> LB.remw(g, f, t)),
    LB.keep(g, f, h), b, Equal.sym(Bool, b, LB.keep(g, f, h), eb))

# The two filters split the length of the list.
def LB.keep_len(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +S: +List<+List<Nat>>) ->
  {List.length(&2, +List<Nat>, S)
   == Nat.add(List.length(&2, +List<Nat>, LB.keepw_b(g, f, S)),
              List.length(&2, +List<Nat>, LB.remw(g, f, S))) : Nat}:
  match S:
    case Nil{}:
      {==}
    case Con{h, t}:
      +b : Bool = LB.keep(g, f, h)
      +ih : {List.length(&2, +List<Nat>, t)
             == Nat.add(List.length(&2, +List<Nat>, LB.keepw_b(g, f, t)),
                        List.length(&2, +List<Nat>, LB.remw(g, f, t))) : Nat} =
        LB.keep_len(g, f, t)
      +core : {List.length(&2, +List<Nat>, h <> t)
               == Nat.add(List.length(&2, +List<Nat>, LB.keepw_of(g, f, h, t, b)),
                          List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, b))) : Nat} =
        LB.keep_len_go(g, f, h, t, b, {==}, ih)
      +ek : {List.length(&2, +List<Nat>, LB.keepw_b(g, f, h <> t))
             == List.length(&2, +List<Nat>, LB.keepw_of(g, f, h, t, b)) : Nat} =
        Equal.cong(+List<+List<Nat>>, Nat, List.length(&2, +List<Nat>),
          LB.keepw_b(g, f, h <> t), LB.keepw_of(g, f, h, t, b), LB.keepw_eq(g, f, h, t, b, {==}))
      +er : {List.length(&2, +List<Nat>, LB.remw(g, f, h <> t))
             == List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, b)) : Nat} =
        Equal.cong(+List<+List<Nat>>, Nat, List.length(&2, +List<Nat>),
          LB.remw(g, f, h <> t), LB.remw_of(g, f, h, t, b), LB.remw_eq(g, f, h, t, b, {==}))
      +rhs : {Nat.add(List.length(&2, +List<Nat>, LB.keepw_of(g, f, h, t, b)),
                      List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, b)))
              == Nat.add(List.length(&2, +List<Nat>, LB.keepw_b(g, f, h <> t)),
                         List.length(&2, +List<Nat>, LB.remw(g, f, h <> t))) : Nat} =
        Equal.trans(Nat,
          Nat.add(List.length(&2, +List<Nat>, LB.keepw_of(g, f, h, t, b)),
                  List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, b))),
          Nat.add(List.length(&2, +List<Nat>, LB.keepw_b(g, f, h <> t)),
                  List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, b))),
          Nat.add(List.length(&2, +List<Nat>, LB.keepw_b(g, f, h <> t)),
                  List.length(&2, +List<Nat>, LB.remw(g, f, h <> t))),
          Equal.cong(Nat, Nat, x => Nat.add(x, List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, b))),
            List.length(&2, +List<Nat>, LB.keepw_of(g, f, h, t, b)),
            List.length(&2, +List<Nat>, LB.keepw_b(g, f, h <> t)),
            Equal.sym(Nat, List.length(&2, +List<Nat>, LB.keepw_b(g, f, h <> t)),
              List.length(&2, +List<Nat>, LB.keepw_of(g, f, h, t, b)), ek)),
          Equal.cong(Nat, Nat,
            x => Nat.add(List.length(&2, +List<Nat>, LB.keepw_b(g, f, h <> t)), x),
            List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, b)),
            List.length(&2, +List<Nat>, LB.remw(g, f, h <> t)),
            Equal.sym(Nat, List.length(&2, +List<Nat>, LB.remw(g, f, h <> t)),
              List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, b)), er)))
      Equal.trans(Nat, List.length(&2, +List<Nat>, h <> t),
        Nat.add(List.length(&2, +List<Nat>, LB.keepw_of(g, f, h, t, b)),
                List.length(&2, +List<Nat>, LB.remw_of(g, f, h, t, b))),
        Nat.add(List.length(&2, +List<Nat>, LB.keepw_b(g, f, h <> t)),
                List.length(&2, +List<Nat>, LB.remw(g, f, h <> t))),
        core, rhs)

# The class sizes plus the leftover length are the candidate count.
def LB.totSize_split(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>) ->
  {List.length(&2, +List<Nat>, S)
   == Nat.add(LB.totSize(LB.classes(g, kids, S)),
              List.length(&2, +List<Nat>, LB.rem(g, kids, S))) : Nat}:
  match kids:
    case Nil{}:
      {==}
    case Con{c, rest}:
      match c:
        case Tree.Child{f, t}:
          +kh : {List.length(&2, +List<Nat>, S)
                 == Nat.add(List.length(&2, +List<Nat>, LB.keepw_b(g, f, S)),
                            List.length(&2, +List<Nat>, LB.remw(g, f, S))) : Nat} =
            LB.keep_len(g, f, S)
          +ih : {List.length(&2, +List<Nat>, LB.remw(g, f, S))
                 == Nat.add(LB.totSize(LB.classes(g, rest, LB.remw(g, f, S))),
                            List.length(&2, +List<Nat>, LB.rem(g, rest, LB.remw(g, f, S)))) : Nat} =
            LB.totSize_split(g, rest, LB.remw(g, f, S))
          +lk : Nat = List.length(&2, +List<Nat>, LB.keepw_b(g, f, S))
          +lr : Nat = List.length(&2, +List<Nat>, LB.remw(g, f, S))
          +tr : Nat = LB.totSize(LB.classes(g, rest, LB.remw(g, f, S)))
          +lr2 : Nat = List.length(&2, +List<Nat>,
                           LB.rem(g, rest, LB.remw(g, f, S)))
          +c1 : {List.length(&2, +List<Nat>, S) == Nat.add(lk, lr) : Nat} = kh
          +c2 : {Nat.add(lk, lr) == Nat.add(lk, Nat.add(tr, lr2)) : Nat} =
            Equal.cong(Nat, Nat, x => Nat.add(lk, x), lr, Nat.add(tr, lr2), ih)
          +c3 : {Nat.add(lk, Nat.add(tr, lr2)) == Nat.add(Nat.add(lk, tr), lr2) : Nat} =
            Equal.sym(Nat, Nat.add(Nat.add(lk, tr), lr2), Nat.add(lk, Nat.add(tr, lr2)),
              NatProof.NatPrf.add_assoc(lk, tr, lr2))
          Equal.trans(Nat, List.length(&2, +List<Nat>, S), Nat.add(lk, lr),
            Nat.add(Nat.add(lk, tr), lr2), c1, Equal.trans(Nat, Nat.add(lk, lr),
              Nat.add(lk, Nat.add(tr, lr2)), Nat.add(Nat.add(lk, tr), lr2), c2, c3))

# A list's multiplicity is at most the multiplicity in the list with one more
# word in front.
def LB.mult_le_cons(+w: +List<Nat>, +h: +List<Nat>, +t: +List<+List<Nat>>) ->
  {Nat.is_le(Twice.LB.mult(w, t), Twice.LB.mult(w, h <> t)) == True{} : Bool}:
  NatProof.Nat.is_le_eq_r(Twice.LB.mult(w, t),
    Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, t)), Twice.LB.mult(w, h <> t), {==},
    NatProof.Nat.is_le_add_self_l(Twice.LB.hit(w, h), Twice.LB.mult(w, t)))

# A word is counted no more often in a filtered list than in the whole one.
def LB.mult_keep_go(+w: +List<Nat>, +g: +List<Nat>, +f: +List<Feedback.Color>,
    +h: +List<Nat>, +t: +List<+List<Nat>>, b: Bool,
    +eb: {b == LB.keep(g, f, h) : Bool},
    ih: {Nat.is_le(Twice.LB.mult(w, LB.keepw_b(g, f, t)), Twice.LB.mult(w, t))
         == True{} : Bool}) ->
  {Nat.is_le(Twice.LB.mult(w, LB.keepw_of(g, f, h, t, b)), Twice.LB.mult(w, h <> t))
   == True{} : Bool}:
  match b:
    case True{}:
      +ih2 : {Nat.is_le(Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, LB.keepw_b(g, f, t))),
                        Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, t))) == True{} : Bool} =
        NatProof.Nat.is_le_add_l(Twice.LB.mult(w, LB.keepw_b(g, f, t)),
          Twice.LB.mult(w, t), Twice.LB.hit(w, h), ih)
      +e1 : {Twice.LB.mult(w, LB.keepw_of(g, f, h, t, True{}))
             == Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, LB.keepw_b(g, f, t))) : Nat} =
        {==}
      +e2 : {Twice.LB.mult(w, h <> t)
             == Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, t)) : Nat} =
        {==}
      NatProof.Nat.is_le_eq_l(Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, t)),
        Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, LB.keepw_b(g, f, t))),
        Twice.LB.mult(w, LB.keepw_of(g, f, h, t, True{})),
        Equal.sym(Nat, Twice.LB.mult(w, LB.keepw_of(g, f, h, t, True{})),
          Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, LB.keepw_b(g, f, t))), e1),
        NatProof.Nat.is_le_eq_r(
          Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, LB.keepw_b(g, f, t))),
          Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, t)), Twice.LB.mult(w, h <> t),
          Equal.sym(Nat, Twice.LB.mult(w, h <> t),
            Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, t)), e2), ih2))
    case False{}:
      NatProof.Nat.is_le_trans(Twice.LB.mult(w, LB.keepw_b(g, f, t)),
        Twice.LB.mult(w, t), Twice.LB.mult(w, h <> t), ih,
        LB.mult_le_cons(w, h, t))

def LB.mult_keep(+w: +List<Nat>, +g: +List<Nat>, +f: +List<Feedback.Color>,
    +S: +List<+List<Nat>>) ->
  {Nat.is_le(Twice.LB.mult(w, LB.keepw_b(g, f, S)), Twice.LB.mult(w, S))
   == True{} : Bool}:
  match S:
    case Nil{}:
      NatProof.Nat.is_le_refl(0n)
    case Con{h, t}:
      +b : Bool = LB.keep(g, f, h)
      +core : {Nat.is_le(Twice.LB.mult(w, LB.keepw_of(g, f, h, t, b)),
                         Twice.LB.mult(w, h <> t)) == True{} : Bool} =
        LB.mult_keep_go(w, g, f, h, t, b, {==}, LB.mult_keep(w, g, f, t))
      Equal.trans(Bool,
        Nat.is_le(Twice.LB.mult(w, LB.keepw_b(g, f, h <> t)), Twice.LB.mult(w, h <> t)),
        Nat.is_le(Twice.LB.mult(w, LB.keepw_of(g, f, h, t, b)), Twice.LB.mult(w, h <> t)),
        True{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, Twice.LB.mult(w, h <> t)),
          Twice.LB.mult(w, LB.keepw_b(g, f, h <> t)),
          Twice.LB.mult(w, LB.keepw_of(g, f, h, t, b)),
          Equal.cong(+List<+List<Nat>>, Nat, x => Twice.LB.mult(w, x),
            LB.keepw_b(g, f, h <> t), LB.keepw_of(g, f, h, t, b),
            LB.keepw_eq(g, f, h, t, b, {==}))),
        core)

def LB.mult_rem_go(+w: +List<Nat>, +g: +List<Nat>, +f: +List<Feedback.Color>,
    +h: +List<Nat>, +t: +List<+List<Nat>>, b: Bool,
    +eb: {b == LB.keep(g, f, h) : Bool},
    ih: {Nat.is_le(Twice.LB.mult(w, LB.remw(g, f, t)), Twice.LB.mult(w, t))
         == True{} : Bool}) ->
  {Nat.is_le(Twice.LB.mult(w, LB.remw_of(g, f, h, t, b)), Twice.LB.mult(w, h <> t))
   == True{} : Bool}:
  match b:
    case True{}:
      NatProof.Nat.is_le_trans(Twice.LB.mult(w, LB.remw(g, f, t)),
        Twice.LB.mult(w, t), Twice.LB.mult(w, h <> t), ih,
        LB.mult_le_cons(w, h, t))
    case False{}:
      +ih2 : {Nat.is_le(Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, LB.remw(g, f, t))),
                        Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, t))) == True{} : Bool} =
        NatProof.Nat.is_le_add_l(Twice.LB.mult(w, LB.remw(g, f, t)),
          Twice.LB.mult(w, t), Twice.LB.hit(w, h), ih)
      +e1 : {Twice.LB.mult(w, LB.remw_of(g, f, h, t, False{}))
             == Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, LB.remw(g, f, t))) : Nat} =
        {==}
      +e2 : {Twice.LB.mult(w, h <> t)
             == Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, t)) : Nat} =
        {==}
      NatProof.Nat.is_le_eq_l(Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, t)),
        Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, LB.remw(g, f, t))),
        Twice.LB.mult(w, LB.remw_of(g, f, h, t, False{})),
        Equal.sym(Nat, Twice.LB.mult(w, LB.remw_of(g, f, h, t, False{})),
          Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, LB.remw(g, f, t))), e1),
        NatProof.Nat.is_le_eq_r(
          Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, LB.remw(g, f, t))),
          Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, t)), Twice.LB.mult(w, h <> t),
          Equal.sym(Nat, Twice.LB.mult(w, h <> t),
            Nat.add(Twice.LB.hit(w, h), Twice.LB.mult(w, t)), e2), ih2))

def LB.mult_rem(+w: +List<Nat>, +g: +List<Nat>, +f: +List<Feedback.Color>,
    +S: +List<+List<Nat>>) ->
  {Nat.is_le(Twice.LB.mult(w, LB.remw(g, f, S)), Twice.LB.mult(w, S))
   == True{} : Bool}:
  match S:
    case Nil{}:
      NatProof.Nat.is_le_refl(0n)
    case Con{h, t}:
      +b : Bool = LB.keep(g, f, h)
      +core : {Nat.is_le(Twice.LB.mult(w, LB.remw_of(g, f, h, t, b)),
                         Twice.LB.mult(w, h <> t)) == True{} : Bool} =
        LB.mult_rem_go(w, g, f, h, t, b, {==}, LB.mult_rem(w, g, f, t))
      Equal.trans(Bool,
        Nat.is_le(Twice.LB.mult(w, LB.remw(g, f, h <> t)), Twice.LB.mult(w, h <> t)),
        Nat.is_le(Twice.LB.mult(w, LB.remw_of(g, f, h, t, b)), Twice.LB.mult(w, h <> t)),
        True{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, Twice.LB.mult(w, h <> t)),
          Twice.LB.mult(w, LB.remw(g, f, h <> t)),
          Twice.LB.mult(w, LB.remw_of(g, f, h, t, b)),
          Equal.cong(+List<+List<Nat>>, Nat, x => Twice.LB.mult(w, x),
            LB.remw(g, f, h <> t), LB.remw_of(g, f, h, t, b),
            LB.remw_eq(g, f, h, t, b, {==}))),
        core)

# A word counts itself once.
def LB.hit_self(+h: +List<Nat>) -> {Twice.LB.hit(h, h) == 1n : Nat}:
  Equal.trans(Nat, Twice.LB.hit(h, h),
    Twice.LB.hit_bool(Feedback.word_eq(h, h)), 1n, {==},
    Twice.LB.hit_bool_eq(Feedback.word_eq(h, h), True{},
      FbProof.FbPrf.word_eq_refl(h)))

# The multiplicity in a list with the same word in front.
def LB.mult_cons_self(+h: +List<Nat>, +t: +List<+List<Nat>>) ->
  {Twice.LB.mult(h, h <> t) == Nat.add(1n, Twice.LB.mult(h, t)) : Nat}:
  Equal.trans(Nat, Twice.LB.mult(h, h <> t),
    Nat.add(Twice.LB.hit(h, h), Twice.LB.mult(h, t)),
    Nat.add(1n, Twice.LB.mult(h, t)),
    {==},
    Equal.cong(Nat, Nat, x => Nat.add(x, Twice.LB.mult(h, t)),
      Twice.LB.hit(h, h), 1n, LB.hit_self(h)))

# A filter never raises the largest multiplicity of a list.
def LB.maxMult_keep_go(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +h: +List<Nat>, +t: +List<+List<Nat>>, b: Bool,
    +eb: {b == LB.keep(g, f, h) : Bool},
    ih: {Nat.is_le(Twice.LB.maxMult(LB.keepw_b(g, f, t)), Twice.LB.maxMult(t))
         == True{} : Bool}) ->
  {Nat.is_le(Twice.LB.maxMult(LB.keepw_of(g, f, h, t, b)), Twice.LB.maxMult(h <> t))
   == True{} : Bool}:
  match b:
    case True{}:
      +mt : {Nat.is_le(Twice.LB.maxMult(t), Twice.LB.maxMult(h <> t)) == True{} : Bool} =
        NodupProof.LB.maxMult_tail(h, t)
      +t2 : {Nat.is_le(Twice.LB.maxMult(LB.keepw_b(g, f, t)), Twice.LB.maxMult(h <> t))
             == True{} : Bool} =
        NatProof.Nat.is_le_trans(Twice.LB.maxMult(LB.keepw_b(g, f, t)),
          Twice.LB.maxMult(t), Twice.LB.maxMult(h <> t), ih, mt)
      +mk : {Nat.is_le(Twice.LB.mult(h, LB.keepw_b(g, f, t)), Twice.LB.mult(h, t))
             == True{} : Bool} =
        LB.mult_keep(h, g, f, t)
      +mh : {Nat.is_le(Nat.add(1n, Twice.LB.mult(h, LB.keepw_b(g, f, t))),
                       Nat.add(1n, Twice.LB.mult(h, t))) == True{} : Bool} =
        NatProof.Nat.is_le_add_l(Twice.LB.mult(h, LB.keepw_b(g, f, t)),
          Twice.LB.mult(h, t), 1n, mk)
      +mp : {Nat.is_le(Nat.add(1n, Twice.LB.mult(h, t)), Twice.LB.maxMult(h <> t))
             == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(Twice.LB.maxMult(h <> t),
          Twice.LB.mult(h, h <> t), Nat.add(1n, Twice.LB.mult(h, t)),
          LB.mult_cons_self(h, t),
          Twice.LB.mult_le_maxMult(h, h <> t))
      +mhead : {Nat.is_le(Nat.add(1n, Twice.LB.mult(h, LB.keepw_b(g, f, t))),
                          Twice.LB.maxMult(h <> t)) == True{} : Bool} =
        NatProof.Nat.is_le_trans(Nat.add(1n, Twice.LB.mult(h, LB.keepw_b(g, f, t))),
          Nat.add(1n, Twice.LB.mult(h, t)), Twice.LB.maxMult(h <> t), mh, mp)
      +e_def : {Twice.LB.maxMult(LB.keepw_of(g, f, h, t, True{}))
                == Nat.max(Nat.add(1n, Twice.LB.mult(h, LB.keepw_b(g, f, t))),
                           Twice.LB.maxMult(LB.keepw_b(g, f, t))) : Nat} =
        Equal.cong(Nat, Nat,
          x => Nat.max(x, Twice.LB.maxMult(LB.keepw_b(g, f, t))),
          Twice.LB.mult(h, h <> LB.keepw_b(g, f, t)),
          Nat.add(1n, Twice.LB.mult(h, LB.keepw_b(g, f, t))),
          LB.mult_cons_self(h, LB.keepw_b(g, f, t)))
      Equal.trans(Bool,
        Nat.is_le(Twice.LB.maxMult(LB.keepw_of(g, f, h, t, True{})),
                  Twice.LB.maxMult(h <> t)),
        Nat.is_le(Nat.max(Nat.add(1n, Twice.LB.mult(h, LB.keepw_b(g, f, t))),
                          Twice.LB.maxMult(LB.keepw_b(g, f, t))),
                  Twice.LB.maxMult(h <> t)),
        True{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, Twice.LB.maxMult(h <> t)),
          Twice.LB.maxMult(LB.keepw_of(g, f, h, t, True{})),
          Nat.max(Nat.add(1n, Twice.LB.mult(h, LB.keepw_b(g, f, t))),
                  Twice.LB.maxMult(LB.keepw_b(g, f, t))), e_def),
        NodupProof.LB.max_le(Nat.add(1n, Twice.LB.mult(h, LB.keepw_b(g, f, t))),
          Twice.LB.maxMult(LB.keepw_b(g, f, t)), Twice.LB.maxMult(h <> t), mhead, t2))
    case False{}:
      +mt : {Nat.is_le(Twice.LB.maxMult(t), Twice.LB.maxMult(h <> t)) == True{} : Bool} =
        NodupProof.LB.maxMult_tail(h, t)
      NatProof.Nat.is_le_eq_l(Twice.LB.maxMult(h <> t),
        Twice.LB.maxMult(LB.keepw_b(g, f, t)),
        Twice.LB.maxMult(LB.keepw_of(g, f, h, t, False{})), {==},
        NatProof.Nat.is_le_trans(Twice.LB.maxMult(LB.keepw_b(g, f, t)),
          Twice.LB.maxMult(t), Twice.LB.maxMult(h <> t), ih, mt))

def LB.maxMult_keep(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +S: +List<+List<Nat>>) ->
  {Nat.is_le(Twice.LB.maxMult(LB.keepw_b(g, f, S)), Twice.LB.maxMult(S))
   == True{} : Bool}:
  match S:
    case Nil{}:
      NatProof.Nat.is_le_refl(0n)
    case Con{h, t}:
      +b : Bool = LB.keep(g, f, h)
      +core : {Nat.is_le(Twice.LB.maxMult(LB.keepw_of(g, f, h, t, b)),
                         Twice.LB.maxMult(h <> t)) == True{} : Bool} =
        LB.maxMult_keep_go(g, f, h, t, b, {==}, LB.maxMult_keep(g, f, t))
      Equal.trans(Bool,
        Nat.is_le(Twice.LB.maxMult(LB.keepw_b(g, f, h <> t)), Twice.LB.maxMult(h <> t)),
        Nat.is_le(Twice.LB.maxMult(LB.keepw_of(g, f, h, t, b)), Twice.LB.maxMult(h <> t)),
        True{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, Twice.LB.maxMult(h <> t)),
          Twice.LB.maxMult(LB.keepw_b(g, f, h <> t)),
          Twice.LB.maxMult(LB.keepw_of(g, f, h, t, b)),
          Equal.cong(+List<+List<Nat>>, Nat, x => Twice.LB.maxMult(x),
            LB.keepw_b(g, f, h <> t), LB.keepw_of(g, f, h, t, b),
            LB.keepw_eq(g, f, h, t, b, {==}))),
        core)

# The complement filter never raises the largest multiplicity either.
def LB.maxMult_rem_go(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +h: +List<Nat>, +t: +List<+List<Nat>>, b: Bool,
    +eb: {b == LB.keep(g, f, h) : Bool},
    ih: {Nat.is_le(Twice.LB.maxMult(LB.remw(g, f, t)), Twice.LB.maxMult(t))
         == True{} : Bool}) ->
  {Nat.is_le(Twice.LB.maxMult(LB.remw_of(g, f, h, t, b)), Twice.LB.maxMult(h <> t))
   == True{} : Bool}:
  match b:
    case True{}:
      +mt : {Nat.is_le(Twice.LB.maxMult(t), Twice.LB.maxMult(h <> t)) == True{} : Bool} =
        NodupProof.LB.maxMult_tail(h, t)
      NatProof.Nat.is_le_eq_l(Twice.LB.maxMult(h <> t),
        Twice.LB.maxMult(LB.remw(g, f, t)),
        Twice.LB.maxMult(LB.remw_of(g, f, h, t, True{})), {==},
        NatProof.Nat.is_le_trans(Twice.LB.maxMult(LB.remw(g, f, t)),
          Twice.LB.maxMult(t), Twice.LB.maxMult(h <> t), ih, mt))
    case False{}:
      +mt : {Nat.is_le(Twice.LB.maxMult(t), Twice.LB.maxMult(h <> t)) == True{} : Bool} =
        NodupProof.LB.maxMult_tail(h, t)
      +t2 : {Nat.is_le(Twice.LB.maxMult(LB.remw(g, f, t)), Twice.LB.maxMult(h <> t))
             == True{} : Bool} =
        NatProof.Nat.is_le_trans(Twice.LB.maxMult(LB.remw(g, f, t)),
          Twice.LB.maxMult(t), Twice.LB.maxMult(h <> t), ih, mt)
      +mk : {Nat.is_le(Twice.LB.mult(h, LB.remw(g, f, t)), Twice.LB.mult(h, t))
             == True{} : Bool} =
        LB.mult_rem(h, g, f, t)
      +mh : {Nat.is_le(Nat.add(1n, Twice.LB.mult(h, LB.remw(g, f, t))),
                       Nat.add(1n, Twice.LB.mult(h, t))) == True{} : Bool} =
        NatProof.Nat.is_le_add_l(Twice.LB.mult(h, LB.remw(g, f, t)),
          Twice.LB.mult(h, t), 1n, mk)
      +mp : {Nat.is_le(Nat.add(1n, Twice.LB.mult(h, t)), Twice.LB.maxMult(h <> t))
             == True{} : Bool} =
        NatProof.Nat.is_le_eq_l(Twice.LB.maxMult(h <> t),
          Twice.LB.mult(h, h <> t), Nat.add(1n, Twice.LB.mult(h, t)),
          LB.mult_cons_self(h, t),
          Twice.LB.mult_le_maxMult(h, h <> t))
      +mhead : {Nat.is_le(Nat.add(1n, Twice.LB.mult(h, LB.remw(g, f, t))),
                          Twice.LB.maxMult(h <> t)) == True{} : Bool} =
        NatProof.Nat.is_le_trans(Nat.add(1n, Twice.LB.mult(h, LB.remw(g, f, t))),
          Nat.add(1n, Twice.LB.mult(h, t)), Twice.LB.maxMult(h <> t), mh, mp)
      +e_def : {Twice.LB.maxMult(LB.remw_of(g, f, h, t, False{}))
                == Nat.max(Nat.add(1n, Twice.LB.mult(h, LB.remw(g, f, t))),
                           Twice.LB.maxMult(LB.remw(g, f, t))) : Nat} =
        Equal.cong(Nat, Nat,
          x => Nat.max(x, Twice.LB.maxMult(LB.remw(g, f, t))),
          Twice.LB.mult(h, h <> LB.remw(g, f, t)),
          Nat.add(1n, Twice.LB.mult(h, LB.remw(g, f, t))),
          LB.mult_cons_self(h, LB.remw(g, f, t)))
      Equal.trans(Bool,
        Nat.is_le(Twice.LB.maxMult(LB.remw_of(g, f, h, t, False{})),
                  Twice.LB.maxMult(h <> t)),
        Nat.is_le(Nat.max(Nat.add(1n, Twice.LB.mult(h, LB.remw(g, f, t))),
                          Twice.LB.maxMult(LB.remw(g, f, t))),
                  Twice.LB.maxMult(h <> t)),
        True{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, Twice.LB.maxMult(h <> t)),
          Twice.LB.maxMult(LB.remw_of(g, f, h, t, False{})),
          Nat.max(Nat.add(1n, Twice.LB.mult(h, LB.remw(g, f, t))),
                  Twice.LB.maxMult(LB.remw(g, f, t))), e_def),
        NodupProof.LB.max_le(Nat.add(1n, Twice.LB.mult(h, LB.remw(g, f, t))),
          Twice.LB.maxMult(LB.remw(g, f, t)), Twice.LB.maxMult(h <> t), mhead, t2))

def LB.maxMult_rem(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +S: +List<+List<Nat>>) ->
  {Nat.is_le(Twice.LB.maxMult(LB.remw(g, f, S)), Twice.LB.maxMult(S))
   == True{} : Bool}:
  match S:
    case Nil{}:
      NatProof.Nat.is_le_refl(0n)
    case Con{h, t}:
      +b : Bool = LB.keep(g, f, h)
      +core : {Nat.is_le(Twice.LB.maxMult(LB.remw_of(g, f, h, t, b)),
                         Twice.LB.maxMult(h <> t)) == True{} : Bool} =
        LB.maxMult_rem_go(g, f, h, t, b, {==}, LB.maxMult_rem(g, f, t))
      Equal.trans(Bool,
        Nat.is_le(Twice.LB.maxMult(LB.remw(g, f, h <> t)), Twice.LB.maxMult(h <> t)),
        Nat.is_le(Twice.LB.maxMult(LB.remw_of(g, f, h, t, b)), Twice.LB.maxMult(h <> t)),
        True{},
        Equal.cong(Nat, Bool, x => Nat.is_le(x, Twice.LB.maxMult(h <> t)),
          Twice.LB.maxMult(LB.remw(g, f, h <> t)),
          Twice.LB.maxMult(LB.remw_of(g, f, h, t, b)),
          Equal.cong(+List<+List<Nat>>, Nat, x => Twice.LB.maxMult(x),
            LB.remw(g, f, h <> t), LB.remw_of(g, f, h, t, b),
            LB.remw_eq(g, f, h, t, b, {==}))),
        core)

# Duplicate-freeness survives both filters.
def LB.nodup_keep(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +S: +List<+List<Nat>>, +nd: {Nat.is_le(Twice.LB.maxMult(S), 1n) == True{} : Bool}) ->
  {Nat.is_le(Twice.LB.maxMult(LB.keepw_b(g, f, S)), 1n) == True{} : Bool}:
  NatProof.Nat.is_le_trans(Twice.LB.maxMult(LB.keepw_b(g, f, S)),
    Twice.LB.maxMult(S), 1n, LB.maxMult_keep(g, f, S), nd)

def LB.nodup_rem(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +S: +List<+List<Nat>>, +nd: {Nat.is_le(Twice.LB.maxMult(S), 1n) == True{} : Bool}) ->
  {Nat.is_le(Twice.LB.maxMult(LB.remw(g, f, S)), 1n) == True{} : Bool}:
  NatProof.Nat.is_le_trans(Twice.LB.maxMult(LB.remw(g, f, S)),
    Twice.LB.maxMult(S), 1n, LB.maxMult_rem(g, f, S), nd)
