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
import ../src/groups.bend as Groups
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

def Grp.InGroups(w: +List<Nat>, +gs: +List<Groups.Group>) -> Type:
  match gs:
    case Nil{}:
      Empty
    case Con{gp, t}:
      match gp:
        case Groups.Group{fb, ws}:
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
    +f: +List<Feedback.Color>, +ws: +List<+List<Nat>>, +t: +List<Groups.Group>,
    +x: +List<Nat>, b: Bool, m: Grp.InGroups(x, Groups.Group{f, ws} <> t),
    k: Grp.InGroups(x, t) -> Grp.InGroups(x, Groups.group_add(w, fb, t))) ->
  Grp.InGroups(x,
    Feedback.Bool.case(+List<Groups.Group>, b,
      Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])} <> t,
      Groups.Group{f, ws} <> Groups.group_add(w, fb, t))):
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
    +gs: +List<Groups.Group>, +x: +List<Nat>, m: Grp.InGroups(x, gs)) ->
  Grp.InGroups(x, Groups.group_add(w, fb, gs)):
  match gs:
    case Nil{}:
      Empty.absurd(Grp.InGroups(x, Groups.group_add(w, fb, Nil{})), m)
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          Grp.group_add_mem_go(w, fb, f, ws, t, x, Feedback.feedback_eq(fb, f), m,
            ig => Grp.group_add_mem(w, fb, t, x, ig))

# Branch of `group_add_new`.
def Grp.group_add_new_branch(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, +ws: +List<+List<Nat>>, +t: +List<Groups.Group>,
    b: Bool, tail: Grp.InGroups(w, Groups.group_add(w, fb, t))) ->
  Grp.InGroups(w,
    Feedback.Bool.case(+List<Groups.Group>, b,
      Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])} <> t,
      Groups.Group{f, ws} <> Groups.group_add(w, fb, t))):
  match b:
    case True{}:
      Inl{Grp.in_words_snoc(w, ws)}
    case False{}:
      Inr{tail}

# The added word itself is in the result of `group_add`.
def Grp.group_add_new(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +gs: +List<Groups.Group>) ->
  Grp.InGroups(w, Groups.group_add(w, fb, gs)):
  match gs:
    case Nil{}:
      Inl{Inl{{==}}}
    case Con{gp, t}:
      match gp:
        case Groups.Group{f, ws}:
          Grp.group_add_new_branch(w, fb, f, ws, t, Feedback.feedback_eq(fb, f),
            Grp.group_add_new(w, fb, t))

# Branch of `groups_build_extends`. The two recursive proofs are passed as
# continuations so the membership proof is consumed only once.
def Grp.groups_build_extends_branch(+g: +List<Nat>, +rest: +List<+List<Nat>>,
    +acc: +List<Groups.Group>, +w: +List<Nat>, b: Bool, +x: +List<Nat>,
    m: Grp.InGroups(x, acc),
    kt: Grp.InGroups(x, acc) -> Grp.InGroups(x, Groups.groups_build(g, rest, acc)),
    kf: Grp.InGroups(x, acc) -> Grp.InGroups(x, Groups.groups_build(g, rest,
          Groups.group_add(w, Feedback.feedback(g, w), acc)))) ->
  Grp.InGroups(x,
    Feedback.Bool.case(+List<Groups.Group>, b,
      Groups.groups_build(g, rest, acc),
      Groups.groups_build(g, rest, Groups.group_add(w, Feedback.feedback(g, w), acc)))):
  match b:
    case True{}:
      kt(m)
    case False{}:
      kf(m)

# Every group in the old list survives `groups_build`.
def Grp.groups_build_extends(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +acc: +List<Groups.Group>, +x: +List<Nat>, m: Grp.InGroups(x, acc)) ->
  Grp.InGroups(x, Groups.groups_build(g, S, acc)):
  match S:
    case Nil{}:
      m
    case Con{w, rest}:
      Grp.groups_build_extends_branch(g, rest, acc, w, Feedback.word_eq(g, w), x, m,
        m2 => Grp.groups_build_extends(g, rest, acc, x, m2),
        m2 => Grp.groups_build_extends(g, rest,
          Groups.group_add(w, Feedback.feedback(g, w), acc), x,
          Grp.group_add_mem(w, Feedback.feedback(g, w), acc, x, m2)))

# Congruence of `word_eq` in its second argument.
def Grp.word_eq_eq_r(+g: +List<Nat>, +w: +List<Nat>, +w2: +List<Nat>,
    e: {w == w2 : +List<Nat>}) ->
  {Feedback.word_eq(g, w) == Feedback.word_eq(g, w2) : Bool}:
  Equal.cong(+List<Nat>, Bool, y => Feedback.word_eq(g, y), w, w2, e)

# Transport group membership along a word equality.
def Grp.ingroups_eq_word(+w: +List<Nat>, +w0: +List<Nat>, +gs: +List<Groups.Group>,
    e: {w == w0 : +List<Nat>}, p: Grp.InGroups(w0, gs)) ->
  Grp.InGroups(w, gs):
  %Equal.sym(+List<Nat>, w, w0, e) : Grp.InGroups(_, gs)
  p

# Branch of the main membership lemma, when the head word is the one wanted.
def Grp.groups_build_mem_inl(+g: +List<Nat>, +rest: +List<+List<Nat>>,
    +w: +List<Nat>, +w0: +List<Nat>, +e: {w == w0 : +List<Nat>},
    +ne: {Feedback.word_eq(g, w) == False{} : Bool}, b: Bool,
    +eb: {b == Feedback.word_eq(g, w0) : Bool}, +acc: +List<Groups.Group>) ->
  Grp.InGroups(w,
    Feedback.Bool.case(+List<Groups.Group>, b,
      Groups.groups_build(g, rest, acc),
      Groups.groups_build(g, rest,
        Groups.group_add(w0, Feedback.feedback(g, w0), acc)))):
  match b:
    case True{}:
      +e2 : {Feedback.word_eq(g, w) == Feedback.word_eq(g, w0) : Bool} =
        Grp.word_eq_eq_r(g, w, w0, e)
      +e3 : {Feedback.word_eq(g, w0) == False{} : Bool} =
        Equal.trans(Bool, Feedback.word_eq(g, w0), Feedback.word_eq(g, w),
                    False{}, Equal.sym(Bool, Feedback.word_eq(g, w), Feedback.word_eq(g, w0), e2), ne)
      Empty.absurd(
        Grp.InGroups(w, Groups.groups_build(g, rest, acc)),
        Logic.Proof.true_ne_false(
          Equal.trans(Bool, True{}, Feedback.word_eq(g, w0), False{},
                      eb, e3)))
    case False{}:
      Grp.groups_build_extends(g, rest,
        Groups.group_add(w0, Feedback.feedback(g, w0), acc), w,
        Grp.ingroups_eq_word(w, w0, Groups.group_add(w0, Feedback.feedback(g, w0), acc),
          e, Grp.group_add_new(w0, Feedback.feedback(g, w0), acc)))

# Branch of the main membership lemma, when the word is in the tail.
def Grp.groups_build_mem_inr(+g: +List<Nat>, +rest: +List<+List<Nat>>,
    +w: +List<Nat>, +w0: +List<Nat>, b: Bool, +acc: +List<Groups.Group>,
    k: @a: +List<Groups.Group> -> Grp.InGroups(w, Groups.groups_build(g, rest, a))) ->
  Grp.InGroups(w,
    Feedback.Bool.case(+List<Groups.Group>, b,
      Groups.groups_build(g, rest, acc),
      Groups.groups_build(g, rest,
        Groups.group_add(w0, Feedback.feedback(g, w0), acc)))):
  match b:
    case True{}:
      k(acc)
    case False{}:
      k(Groups.group_add(w0, Feedback.feedback(g, w0), acc))

# Every candidate other than the guess belongs to some group. The accumulator
# is abstract, so the lemma composes with `groups_build_extends`.
def Grp.groups_build_mem(+g: +List<Nat>, +S: +List<+List<Nat>>, +w: +List<Nat>,
    m: Grp.InWords(w, S), +ne: {Feedback.word_eq(g, w) == False{} : Bool}) ->
  @acc: +List<Groups.Group> -> Grp.InGroups(w, Groups.groups_build(g, S, acc)):
  match S:
    case Nil{}:
      Empty.absurd(@acc: +List<Groups.Group> -> Grp.InGroups(w, Groups.groups_build(g, Nil{}, acc)), m)
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
  Grp.InGroups(w, Groups.groups_build(g, S, Nil{})):
  Grp.groups_build_mem(g, S, w, m, ne, Nil{})

# The per-word facts a group carries: the word is not the guess, its feedback
# is the group's feedback, and its depth at the node exists.
def Grp.WordDepths(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +fb: +List<Feedback.Color>, +w: +List<Nat>) -> Type:
  {Feedback.word_eq(g, w) == False{} : Bool}
  & {Feedback.feedback_eq(Feedback.feedback(g, w), fb) == True{} : Bool}
  & {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool}

def Grp.WordsDepths(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>) -> Type:
  match ws:
    case Nil{}:
      Unit
    case Con{h, t}:
      Grp.WordDepths(g, kids, fb, h) & Grp.WordsDepths(g, kids, fb, t)

def Grp.GroupDepths(+g: +List<Nat>, +kids: +List<Tree.Child>, gp: Groups.Group) -> Type:
  match gp:
    case Groups.Group{fb, ws}:
      Grp.WordsDepths(g, kids, fb, ws)

def Grp.AllGroupDepths(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +gs: +List<Groups.Group>) -> Type:
  match gs:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      Grp.GroupDepths(g, kids, gp) & Grp.AllGroupDepths(g, kids, rest)

# The per-word facts extend over an append.
def Grp.words_depths_append(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +fb: +List<Feedback.Color>, +xs: +List<+List<Nat>>, +ys: +List<+List<Nat>>,
    px: Grp.WordsDepths(g, kids, fb, xs), py: Grp.WordsDepths(g, kids, fb, ys)) ->
  Grp.WordsDepths(g, kids, fb, List.append(&2, +List<Nat>, xs, ys)):
  match xs:
    case Nil{}:
      py
    case Con{h, t}:
      (ph, pt) = px
      (ph, Grp.words_depths_append(g, kids, fb, t, ys, pt, py))

# Transport the per-word facts to an equal feedback pattern.
def Grp.word_depths_fb(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +fb: +List<Feedback.Color>, +f: +List<Feedback.Color>, +w: +List<Nat>,
    e: {fb == f : +List<Feedback.Color>},
    p: Grp.WordDepths(g, kids, fb, w)) ->
  Grp.WordDepths(g, kids, f, w):
  (pne, pfb, pd) = p
  ec : {Feedback.feedback_eq(Feedback.feedback(g, w), fb)
         == Feedback.feedback_eq(Feedback.feedback(g, w), f) : Bool} =
    Equal.cong(+List<Feedback.Color>, Bool,
               x => Feedback.feedback_eq(Feedback.feedback(g, w), x), fb, f, e)
  pfb2 : {Feedback.feedback_eq(Feedback.feedback(g, w), f) == True{} : Bool} =
    Equal.trans(Bool, Feedback.feedback_eq(Feedback.feedback(g, w), f),
                Feedback.feedback_eq(Feedback.feedback(g, w), fb), True{},
                Equal.sym(Bool, Feedback.feedback_eq(Feedback.feedback(g, w), fb),
                          Feedback.feedback_eq(Feedback.feedback(g, w), f), ec),
                pfb)
  (pne, pfb2, pd)

# Branch of `group_add_depths`, split on the feedback test.
def Grp.group_add_depths_go(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +w: +List<Nat>, +fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +rest: +List<Groups.Group>, b: Bool,
    +eb: {b == Feedback.feedback_eq(fb, f) : Bool},
    local: Grp.WordDepths(g, kids, fb, w),
    acc_ok: Grp.GroupDepths(g, kids, Groups.Group{f, ws})
            & Grp.AllGroupDepths(g, kids, rest),
    k: Grp.WordDepths(g, kids, fb, w) -> Grp.AllGroupDepths(g, kids, rest)
       -> Grp.AllGroupDepths(g, kids, Groups.group_add(w, fb, rest))) ->
  Grp.AllGroupDepths(g, kids,
    Feedback.Bool.case(+List<Groups.Group>, b,
      Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])} <> rest,
      Groups.Group{f, ws} <> Groups.group_add(w, fb, rest))):
  match b:
    case True{}:
      (gp_ok, rest_ok) = acc_ok
      pfb : {Feedback.feedback_eq(fb, f) == True{} : Bool} =
        Equal.sym(Bool, b, Feedback.feedback_eq(fb, f), eb)
      e_f : {fb == f : +List<Feedback.Color>} = FbProof.FbPrf.feedback_eq_true(fb, f, pfb)
      local_f : Grp.WordDepths(g, kids, f, w) =
        Grp.word_depths_fb(g, kids, fb, f, w, e_f, local)
      ws_ok : Grp.WordsDepths(g, kids, f, List.append(&2, +List<Nat>, ws, [w])) =
        Grp.words_depths_append(g, kids, f, ws, [w], gp_ok, (local_f, Unit{}))
      (ws_ok, rest_ok)
    case False{}:
      (gp_ok, rest_ok) = acc_ok
      (gp_ok, k(local, rest_ok))

# Adding a word keeps every group's per-word facts.
def Grp.group_add_depths(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +w: +List<Nat>, +fb: +List<Feedback.Color>, +gs: +List<Groups.Group>,
    local: Grp.WordDepths(g, kids, fb, w),
    acc_ok: Grp.AllGroupDepths(g, kids, gs)) ->
  Grp.AllGroupDepths(g, kids, Groups.group_add(w, fb, gs)):
  match gs:
    case Nil{}:
      ((local, Unit{}), Unit{})
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          Grp.group_add_depths_go(g, kids, w, fb, f, ws, rest,
            Feedback.feedback_eq(fb, f), {==}, local, acc_ok,
            l => ok => Grp.group_add_depths(g, kids, w, fb, rest, l, ok))

# Branch of `groups_build_depths`, split on the word test. The recursive call
# is passed as a continuation because Bend checks defs in file order.
def Grp.groups_build_of(+g: +List<Nat>, +w: +List<Nat>, +t: +List<+List<Nat>>,
    +acc: +List<Groups.Group>, b: Bool) -> +List<Groups.Group>:
  Feedback.Bool.case(+List<Groups.Group>, b,
    Groups.groups_build(g, t, acc),
    Groups.groups_build(g, t, Groups.group_add(w, Feedback.feedback(g, w), acc)))

def Grp.groups_build_depths_go(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +w: +List<Nat>, +t: +List<+List<Nat>>, +acc: +List<Groups.Group>, b: Bool,
    +eb: {b == Feedback.word_eq(g, w) : Bool},
    +dw: {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool},
    dt: Tree.AllHaveDepth(Tree.Node{g, kids}, t),
    acc_ok: Grp.AllGroupDepths(g, kids, acc),
    k: @a: +List<Groups.Group> -> Grp.AllGroupDepths(g, kids, a)
       -> Tree.AllHaveDepth(Tree.Node{g, kids}, t)
       -> Grp.AllGroupDepths(g, kids, Groups.groups_build(g, t, a))) ->
  Grp.AllGroupDepths(g, kids, Grp.groups_build_of(g, w, t, acc, b)):
  match b:
    case True{}:
      k(acc, acc_ok, dt)
    case False{}:
      ne : {Feedback.word_eq(g, w) == False{} : Bool} =
        Equal.sym(Bool, b, Feedback.word_eq(g, w), eb)
      local : Grp.WordDepths(g, kids, Feedback.feedback(g, w), w) =
        (ne, (FbProof.FbPrf.feedback_eq_refl(Feedback.feedback(g, w)), dw))
      k(Groups.group_add(w, Feedback.feedback(g, w), acc),
        Grp.group_add_depths(g, kids, w, Feedback.feedback(g, w), acc, local, acc_ok),
        dt)

# Every group built from S carries the per-word facts.
def Grp.groups_build_depths(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>, +acc: +List<Groups.Group>,
    depths: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    acc_ok: Grp.AllGroupDepths(g, kids, acc)) ->
  Grp.AllGroupDepths(g, kids, Groups.groups_build(g, S, acc)):
  match S:
    case Nil{}:
      acc_ok
    case Con{w, t}:
      (dw, dt) = depths
      Grp.groups_build_depths_go(g, kids, w, t, acc, Feedback.word_eq(g, w),
        {==}, dw, dt, acc_ok,
        a => ok => d => Grp.groups_build_depths(g, kids, t, a, d, ok))
