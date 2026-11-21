# The groups built by the reference search, as a partition of the candidates.
#
# `groups_build` splits the candidate list into feedback classes, dropping the
# candidates equal to the guess. A tree built from one subtree per group is
# valid for the candidates exactly when each candidate other than the guess is
# in some group and every group's subtree is valid for that group. The lemmas
# here establish the membership half of that statement.
import Base
import ../src/feedback.bend as Feedback
import ../src/tree.bend as Tree
import ../src/solve.bend as Solve
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof

# Membership by syntactic word equality.
def Grp.InWords(w: +List<Nat>, +ws: +List<+List<Nat>>) -> Type:
  match ws:
    case Nil{}:
      Empty
    case Con{h, t}:
      {w == h : +List<Nat>} | Grp.InWords(w, t)

def Grp.InGroups(w: +List<Nat>, +gs: +List<Solve.Group>) -> Type:
  match gs:
    case Nil{}:
      Empty
    case Con{gp, t}:
      match gp:
        case Solve.Group{fb, ws}:
          Grp.InWords(w, ws) | Grp.InGroups(w, t)

# A word in the left list is in the append.
def Grp.in_words_append_l(w: +List<Nat>, +xs: +List<+List<Nat>>,
    +ys: +List<+List<Nat>>, m: Grp.InWords(w, xs)) ->
  Grp.InWords(w, List.append(&2, +List<Nat>, xs, ys)):
  match xs:
    case Nil{}:
      Empty.absurd(Grp.InWords(w, List.append(&2, +List<Nat>, Nil{}, ys)), m)
    case Con{h, t}:
      match m:
        case Inl{e}:
          Inl{e}
        case Inr{rest}:
          Inr{Grp.in_words_append_l(w, t, ys, rest)}

# The new word is at the end of `ws ++ [w]`.
def Grp.in_words_snoc(w: +List<Nat>, +ws: +List<+List<Nat>>) ->
  Grp.InWords(w, List.append(&2, +List<Nat>, ws, [w])):
  match ws:
    case Nil{}:
      Inl{{==}}
    case Con{h, t}:
      Inr{Grp.in_words_snoc(w, t)}

# Branch of `group_add_mem`. The recursive proof for the tail is passed as a
# continuation, so the original membership proof is consumed only once.
def Grp.group_add_mem_go(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, +ws: +List<+List<Nat>>, +t: +List<Solve.Group>,
    +x: +List<Nat>, b: Bool, m: Grp.InGroups(x, Solve.Group{f, ws} <> t),
    k: Grp.InGroups(x, t) -> Grp.InGroups(x, Solve.group_add(w, fb, t))) ->
  Grp.InGroups(x,
    Feedback.Bool.case(+List<Solve.Group>, b,
      Solve.Group{f, List.append(&2, +List<Nat>, ws, [w])} <> t,
      Solve.Group{f, ws} <> Solve.group_add(w, fb, t))):
  match b:
    case True{}:
      match m:
        case Inl{iw}:
          Inl{Grp.in_words_append_l(x, ws, [w], iw)}
        case Inr{ig}:
          Inr{ig}
    case False{}:
      match m:
        case Inl{iw}:
          Inl{iw}
        case Inr{ig}:
          Inr{k(ig)}

# Extending a group list with a word keeps every earlier word.
def Grp.group_add_mem(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +gs: +List<Solve.Group>, +x: +List<Nat>, m: Grp.InGroups(x, gs)) ->
  Grp.InGroups(x, Solve.group_add(w, fb, gs)):
  match gs:
    case Nil{}:
      Empty.absurd(Grp.InGroups(x, Solve.group_add(w, fb, Nil{})), m)
    case Con{gp, t}:
      match gp:
        case Solve.Group{f, ws}:
          Grp.group_add_mem_go(w, fb, f, ws, t, x, Feedback.feedback_eq(fb, f), m,
            ig => Grp.group_add_mem(w, fb, t, x, ig))

# Branch of `group_add_new`.
def Grp.group_add_new_branch(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, +ws: +List<+List<Nat>>, +t: +List<Solve.Group>,
    b: Bool, tail: Grp.InGroups(w, Solve.group_add(w, fb, t))) ->
  Grp.InGroups(w,
    Feedback.Bool.case(+List<Solve.Group>, b,
      Solve.Group{f, List.append(&2, +List<Nat>, ws, [w])} <> t,
      Solve.Group{f, ws} <> Solve.group_add(w, fb, t))):
  match b:
    case True{}:
      Inl{Grp.in_words_snoc(w, ws)}
    case False{}:
      Inr{tail}

# The added word itself is in the result of `group_add`.
def Grp.group_add_new(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +gs: +List<Solve.Group>) ->
  Grp.InGroups(w, Solve.group_add(w, fb, gs)):
  match gs:
    case Nil{}:
      Inl{Inl{{==}}}
    case Con{gp, t}:
      match gp:
        case Solve.Group{f, ws}:
          Grp.group_add_new_branch(w, fb, f, ws, t, Feedback.feedback_eq(fb, f),
            Grp.group_add_new(w, fb, t))

# Branch of `groups_build_extends`. The two recursive proofs are passed as
# continuations so the membership proof is consumed only once.
def Grp.groups_build_extends_branch(+g: +List<Nat>, +rest: +List<+List<Nat>>,
    +acc: +List<Solve.Group>, +w: +List<Nat>, b: Bool, +x: +List<Nat>,
    m: Grp.InGroups(x, acc),
    kt: Grp.InGroups(x, acc) -> Grp.InGroups(x, Solve.groups_build(g, rest, acc)),
    kf: Grp.InGroups(x, acc) -> Grp.InGroups(x, Solve.groups_build(g, rest,
          Solve.group_add(w, Feedback.feedback(g, w), acc)))) ->
  Grp.InGroups(x,
    Feedback.Bool.case(+List<Solve.Group>, b,
      Solve.groups_build(g, rest, acc),
      Solve.groups_build(g, rest, Solve.group_add(w, Feedback.feedback(g, w), acc)))):
  match b:
    case True{}:
      kt(m)
    case False{}:
      kf(m)

# Every group in the old list survives `groups_build`.
def Grp.groups_build_extends(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +acc: +List<Solve.Group>, +x: +List<Nat>, m: Grp.InGroups(x, acc)) ->
  Grp.InGroups(x, Solve.groups_build(g, S, acc)):
  match S:
    case Nil{}:
      m
    case Con{w, rest}:
      Grp.groups_build_extends_branch(g, rest, acc, w, Feedback.word_eq(g, w), x, m,
        m2 => Grp.groups_build_extends(g, rest, acc, x, m2),
        m2 => Grp.groups_build_extends(g, rest,
          Solve.group_add(w, Feedback.feedback(g, w), acc), x,
          Grp.group_add_mem(w, Feedback.feedback(g, w), acc, x, m2)))

# Congruence of `word_eq` in its second argument.
def Grp.word_eq_eq_r(+g: +List<Nat>, +w: +List<Nat>, +w2: +List<Nat>,
    e: {w == w2 : +List<Nat>}) ->
  {Feedback.word_eq(g, w) == Feedback.word_eq(g, w2) : Bool}:
  Equal.cong(+List<Nat>, Bool, y => Feedback.word_eq(g, y), w, w2, e)

# Transport group membership along a word equality.
def Grp.ingroups_eq_word(+w: +List<Nat>, +w0: +List<Nat>, +gs: +List<Solve.Group>,
    e: {w == w0 : +List<Nat>}, p: Grp.InGroups(w0, gs)) ->
  Grp.InGroups(w, gs):
  %Equal.sym(+List<Nat>, w, w0, e) : Grp.InGroups(_, gs)
  p

# Branch of the main membership lemma, when the head word is the one wanted.
def Grp.groups_build_mem_inl(+g: +List<Nat>, +rest: +List<+List<Nat>>,
    +w: +List<Nat>, +w0: +List<Nat>, +e: {w == w0 : +List<Nat>},
    +ne: {Feedback.word_eq(g, w) == False{} : Bool}, b: Bool,
    +eb: {b == Feedback.word_eq(g, w0) : Bool}, +acc: +List<Solve.Group>) ->
  Grp.InGroups(w,
    Feedback.Bool.case(+List<Solve.Group>, b,
      Solve.groups_build(g, rest, acc),
      Solve.groups_build(g, rest,
        Solve.group_add(w0, Feedback.feedback(g, w0), acc)))):
  match b:
    case True{}:
      +e2 : {Feedback.word_eq(g, w) == Feedback.word_eq(g, w0) : Bool} =
        Grp.word_eq_eq_r(g, w, w0, e)
      +e3 : {Feedback.word_eq(g, w0) == False{} : Bool} =
        Equal.trans(Bool, Feedback.word_eq(g, w0), Feedback.word_eq(g, w),
                    False{}, Equal.sym(Bool, Feedback.word_eq(g, w), Feedback.word_eq(g, w0), e2), ne)
      Empty.absurd(
        Grp.InGroups(w, Solve.groups_build(g, rest, acc)),
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, Feedback.word_eq(g, w0), False{},
                      eb, e3)))
    case False{}:
      Grp.groups_build_extends(g, rest,
        Solve.group_add(w0, Feedback.feedback(g, w0), acc), w,
        Grp.ingroups_eq_word(w, w0, Solve.group_add(w0, Feedback.feedback(g, w0), acc),
          e, Grp.group_add_new(w0, Feedback.feedback(g, w0), acc)))

# Branch of the main membership lemma, when the word is in the tail.
def Grp.groups_build_mem_inr(+g: +List<Nat>, +rest: +List<+List<Nat>>,
    +w: +List<Nat>, +w0: +List<Nat>, b: Bool, +acc: +List<Solve.Group>,
    k: @a: +List<Solve.Group> -> Grp.InGroups(w, Solve.groups_build(g, rest, a))) ->
  Grp.InGroups(w,
    Feedback.Bool.case(+List<Solve.Group>, b,
      Solve.groups_build(g, rest, acc),
      Solve.groups_build(g, rest,
        Solve.group_add(w0, Feedback.feedback(g, w0), acc)))):
  match b:
    case True{}:
      k(acc)
    case False{}:
      k(Solve.group_add(w0, Feedback.feedback(g, w0), acc))

# Every candidate other than the guess belongs to some group. The accumulator
# is abstract, so the lemma composes with `groups_build_extends`.
def Grp.groups_build_mem(+g: +List<Nat>, +S: +List<+List<Nat>>, +w: +List<Nat>,
    m: Grp.InWords(w, S), +ne: {Feedback.word_eq(g, w) == False{} : Bool}) ->
  @acc: +List<Solve.Group> -> Grp.InGroups(w, Solve.groups_build(g, S, acc)):
  match S:
    case Nil{}:
      Empty.absurd(@acc: +List<Solve.Group> -> Grp.InGroups(w, Solve.groups_build(g, Nil{}, acc)), m)
    case Con{w0, rest}:
      match m:
        case Inl{e}:
          acc => Grp.groups_build_mem_inl(g, rest, w, w0, e, ne,
            Feedback.word_eq(g, w0), {==}, acc)
        case Inr{restm}:
          acc => Grp.groups_build_mem_inr(g, rest, w, w0,
            Feedback.word_eq(g, w0), acc,
            Grp.groups_build_mem(g, rest, w, restm, ne))

# The membership fact the solver uses: starting from no groups, every candidate
# other than the guess lands in some group.
def Grp.groups_build_contains(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +w: +List<Nat>, m: Grp.InWords(w, S),
    +ne: {Feedback.word_eq(g, w) == False{} : Bool}) ->
  Grp.InGroups(w, Solve.groups_build(g, S, Nil{})):
  Grp.groups_build_mem(g, S, w, m, ne, Nil{})
