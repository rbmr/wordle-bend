# The per-class oracle and the value of a guess.
#
# The cover argument needs a cost for each feedback class of a guess, supplied
# by an optimality oracle that is sound for strictly smaller candidate lists.
# This module defines that oracle, the value it gives a guess, and the minimum
# over a list of guesses, plus the order lemmas the cover induction uses. The
# oracle is data: for every guess it carries one `Maybe Nat` per class, in the
# class order `groups_build` produces, together with the soundness proof.
import Base
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./cover_maybe.bend as CoverMaybe
import ./nodecost.bend as NodeCost
import ./groupcost.bend as GC

# A lower bound `n` on every valid tree for the candidate list `ws`, or the
# claim that no valid tree exists at all.
def Cover.Opt(+G: +List<+List<Nat>>, +ws: +List<+List<Nat>>, +o: Maybe<&2, Nat>) -> Type:
  match o:
    case None{}:
      @T: Tree.Tree -> Tree.Valid(T, G, ws) -> Empty
    case Some{n}:
      @T: Tree.Tree -> Tree.Valid(T, G, ws) ->
        {Nat.is_le(n, Tree.cost(T, ws)) == True{} : Bool}

# The same bound, required only when `ws` is strictly shorter than `S`.
def Cover.OptBelow(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +ws: +List<+List<Nat>>, +o: Maybe<&2, Nat>) -> Type:
  {Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{} : Bool}
  -> Cover.Opt(G, ws, o)

# The oracle's per-class entries, aligned with a class list.
def Cover.EntryOK(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +os: +List<Maybe<&2, Nat>>, +groups: +List<Groups.Group>) -> Type:
  match os:
    case Nil{}:
      match groups:
        case Nil{}:
          Unit
        case Con{gp, gs2}:
          Empty
    case Con{o, os2}:
      match groups:
        case Nil{}:
          Empty
        case Con{gp, gs2}:
          match gp:
            case Groups.Group{fb, ws}:
              Cover.OptBelow(G, S, ws, o) & Cover.EntryOK(G, S, os2, gs2)

# The oracle entry for one guess, with the classes of that guess.
def Cover.GuessOK(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +g: +List<Nat>, +os: +List<Maybe<&2, Nat>>) -> Type:
  Cover.EntryOK(G, S, os, Groups.groups_build(g, S, Nil{}))

# One entry per guess, aligned with the guess list.
def Cover.Oracle(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>) -> Type:
  match G:
    case Nil{}:
      match entries:
        case Nil{}:
          Unit
        case Con{es, erest}:
          Empty
    case Con{g, rest}:
      match entries:
        case Nil{}:
          Empty
        case Con{es, erest}:
          Cover.GuessOK(G, S, g, es) & Cover.Oracle(rest, S, erest)

# Classes that are all strictly shorter than the candidate list.
def Cover.EntrySmall(+S: +List<+List<Nat>>,
    +os: +List<Maybe<&2, Nat>>, +groups: +List<Groups.Group>) -> Type:
  match os:
    case Nil{}:
      match groups:
        case Nil{}:
          Unit
        case Con{gp, gs2}:
          Empty
    case Con{o, os2}:
      match groups:
        case Nil{}:
          Empty
        case Con{gp, gs2}:
          match gp:
            case Groups.Group{fb, ws}:
              {Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{} : Bool}
              & Cover.EntrySmall(S, os2, gs2)

# Per-class smallness for one guess.
def Cover.GuessSmall(+S: +List<+List<Nat>>, +g: +List<Nat>,
    +os: +List<Maybe<&2, Nat>>) -> Type:
  Cover.EntrySmall(S, os, Groups.groups_build(g, S, Nil{}))

# `groups_smaller` split into its per-class facts.
def Cover.GroupSmall(+S: +List<+List<Nat>>, +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          {Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{} : Bool}
          & Cover.GroupSmall(S, rest)

def Cover.groups_smaller_sound(+S: +List<+List<Nat>>, +groups: +List<Groups.Group>,
    +e: {Groups.groups_smaller(S, groups) == True{} : Bool}) ->
  Cover.GroupSmall(S, groups):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          (Logic.Proof.and_true_l(
             Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)),
             Groups.groups_smaller(S, rest), e),
           Cover.groups_smaller_sound(S, rest,
             Logic.Proof.and_true_r(
               Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)),
               Groups.groups_smaller(S, rest), e)))

# An aligned oracle entry supplies the per-class smallness facts.
def Cover.entry_small_of(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +os: +List<Maybe<&2, Nat>>, +groups: +List<Groups.Group>,
    small: Cover.GroupSmall(S, groups),
    ok: Cover.EntryOK(G, S, os, groups)) -> Cover.EntrySmall(S, os, groups):
  match os:
    case Nil{}:
      match groups:
        case Nil{}:
          Unit{}
        case Con{gp, gs2}:
          match ok:
    case Con{o, os2}:
      match groups:
        case Nil{}:
          match ok:
        case Con{gp, gs2}:
          match gp:
            case Groups.Group{fb, ws}:
              (sh, st) = small
              (oh, ot) = ok
              (sh, Cover.entry_small_of(G, S, os2, gs2, st, ot))

# Folding the oracle over the classes of a guess.
def Cover.TotalOpts(+os: +List<Maybe<&2, Nat>>, +groups: +List<Groups.Group>) -> Maybe<&2, Nat>:
  match os:
    case Nil{}:
      match groups:
        case Nil{}:
          Some{0n}
        case Con{gp, gs2}:
          None{}
    case Con{o, os2}:
      match groups:
        case Nil{}:
          None{}
        case Con{gp, gs2}:
          CoverMaybe.Cover.MAdd(o, Cover.TotalOpts(os2, gs2))

# The value of one guess: `|S|` plus its class optima, or infinity.
def Cover.GuessValue(+S: +List<+List<Nat>>, +g: +List<Nat>,
    +os: +List<Maybe<&2, Nat>>) -> Maybe<&2, Nat>:
  +groups = Groups.groups_build(g, S, Nil{})
  Feedback.Bool.case(Maybe<&2, Nat>, Groups.groups_smaller(S, groups),
    CoverMaybe.Cover.MAdd(Some{Groups.len_words(S)}, Cover.TotalOpts(os, groups)),
    None{})

# The minimum of the guess values, with no guesses giving infinity.
def Cover.BestValue(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +entries: +List<+List<Maybe<&2, Nat>>>) -> Maybe<&2, Nat>:
  match G:
    case Nil{}:
      None{}
    case Con{g, rest}:
      match entries:
        case Nil{}:
          None{}
        case Con{es, erest}:
          CoverMaybe.Cover.MMin(Cover.GuessValue(S, g, es), Cover.BestValue(rest, S, erest))

# The oracle entry found at a matching position.
def Cover.EntryOf(+S: +List<+List<Nat>>, +g: +List<Nat>,
    +G: +List<+List<Nat>>, +entries: +List<+List<Maybe<&2, Nat>>>,
    +es: +List<Maybe<&2, Nat>>) -> Type:
  match G entries:
    case Nil{} Nil{}:
      Empty
    case Con{h, rest} Con{es2, erest}:
      ({g == h : +List<Nat>} & {es == es2 : +List<Maybe<&2, Nat>>})
      | Cover.EntryOf(S, g, rest, erest, es)
    case _ _:
      Empty

# A found entry together with its oracle proof.
def Cover.Find(+S: +List<+List<Nat>>, +g: +List<Nat>,
    +G: +List<+List<Nat>>, +entries: +List<+List<Maybe<&2, Nat>>>) -> Type:
  Sigma<&1, &1, +List<Maybe<&2, Nat>>, es =>
    Cover.EntryOf(S, g, G, entries, es) & Cover.GuessOK(G, S, g, es)>

# A boolean case at a known value.
def Cover.bool_case_true(~A: Type, b: Bool, t: A, f: A,
    +e: {b == True{} : Bool}) ->
  {Feedback.Bool.case(A, b, t, f) == t : A}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({Feedback.Bool.case(A, False{}, t, f) == t : A},
        Logic.Proof.false_ne_true(e))

def Cover.bool_case_false(~A: Type, b: Bool, t: A, f: A,
    +e: {b == False{} : Bool}) ->
  {Feedback.Bool.case(A, b, t, f) == f : A}:
  match b:
    case True{}:
      Empty.absurd({Feedback.Bool.case(A, True{}, t, f) == f : A},
        Logic.Proof.true_ne_false(e))
    case False{}:
      {==}

# `Some` is injective.
def Cover.some_eq(+a: Nat, +b: Nat, e: {a == b : Nat}) ->
  {Some{a} == Some{b} : Maybe<&2, Nat>}:
  Equal.cong(Nat, Maybe<&2, Nat>, x => Some{x}, a, b, e)

# Rewriting the left and right arguments of the cost order.
def Cover.mle_eq_l(+a: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>,
    e: {a == b : Maybe<&2, Nat>}, p: CoverMaybe.Cover.MLe(b, c)) -> CoverMaybe.Cover.MLe(a, c):
  %Equal.sym(Maybe<&2, Nat>, a, b, e) : CoverMaybe.Cover.MLe(_, c)
  p

def Cover.mle_eq_r(+a: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>,
    e: {b == c : Maybe<&2, Nat>}, p: CoverMaybe.Cover.MLe(a, b)) -> CoverMaybe.Cover.MLe(a, c):
  %e : CoverMaybe.Cover.MLe(a, _)
  p

# The guess value of a usable guess is its explicit class sum.
def Cover.guess_value_usable(+S: +List<+List<Nat>>, +g: +List<Nat>,
    +os: +List<Maybe<&2, Nat>>,
    +e: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{} : Bool}) ->
  {Cover.GuessValue(S, g, os)
   == CoverMaybe.Cover.MAdd(Some{Groups.len_words(S)},
        Cover.TotalOpts(os, Groups.groups_build(g, S, Nil{}))) : Maybe<&2, Nat>}:
  Cover.bool_case_true(Maybe<&2, Nat>,
    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
    CoverMaybe.Cover.MAdd(Some{Groups.len_words(S)},
      Cover.TotalOpts(os, Groups.groups_build(g, S, Nil{}))),
    None{}, e)

# The guess value of an unusable guess is infinity.
def Cover.guess_value_unusable(+S: +List<+List<Nat>>, +g: +List<Nat>,
    +os: +List<Maybe<&2, Nat>>,
    +e: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == False{} : Bool}) ->
  {Cover.GuessValue(S, g, os) == None{} : Maybe<&2, Nat>}:
  Cover.bool_case_false(Maybe<&2, Nat>,
    Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})),
    CoverMaybe.Cover.MAdd(Some{Groups.len_words(S)},
      Cover.TotalOpts(os, Groups.groups_build(g, S, Nil{}))),
    None{}, e)

# A valid child selected by a class's feedback.
def Cover.GroupKid(+G: +List<+List<Nat>>, +kids: +List<Tree.Child>,
    gp: Groups.Group) -> Type:
  match gp:
    case Groups.Group{fb, ws}:
      Sigma<&2, &1, Tree.Tree, T =>
        {Tree.lookup(fb, kids) == Some{T} : Maybe<Tree.Tree>}
        & Tree.Valid(T, G, ws)>

# Every class of a group list has a valid child.
def Cover.GroupKids(+G: +List<+List<Nat>>, +kids: +List<Tree.Child>,
    +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      Cover.GroupKid(G, kids, gp) & Cover.GroupKids(G, kids, rest)

# A valid class child turns an oracle entry into a bound on its class cost.
def Cover.opt_le_group(+G: +List<+List<Nat>>, +kids: +List<Tree.Child>,
    +fb: +List<Feedback.Color>, +ws: +List<+List<Nat>>, +o: Maybe<&2, Nat>,
    opt: Cover.Opt(G, ws, o),
    kid: Cover.GroupKid(G, kids, Groups.Group{fb, ws})) ->
  CoverMaybe.Cover.MLe(o, Some{GC.GC.GroupCost(kids, Groups.Group{fb, ws})}):
  match o:
    case None{}:
      match kid:
        case Tuple{T, kp}:
          (e_look, valid) = kp
          Empty.absurd(CoverMaybe.Cover.MLe(None{}, Some{GC.GC.GroupCost(kids, Groups.Group{fb, ws})}),
            opt(T, valid))
    case Some{n}:
      match kid:
        case Tuple{+T, kp}:
          (e_look, valid) = kp
          +gc : {GC.GC.GroupCost(kids, Groups.Group{fb, ws}) == Tree.cost(T, ws) : Nat} =
            Equal.cong(Maybe<Tree.Tree>, Nat,
              m => GC.GC.group_cost_of(kids, ws, m),
              Tree.lookup(fb, kids), Some{T}, e_look)
          +le : {Nat.is_le(n, Tree.cost(T, ws)) == True{} : Bool} = opt(T, valid)
          NatProof.Nat.is_le_eq_r(n, Tree.cost(T, ws),
            GC.GC.GroupCost(kids, Groups.Group{fb, ws}),
            Equal.sym(Nat, GC.GC.GroupCost(kids, Groups.Group{fb, ws}),
              Tree.cost(T, ws), gc), le)

# The classes of a guess cost at most the tree's child sum.
def Cover.total_opts_le(+G: +List<+List<Nat>>, +S: +List<+List<Nat>>,
    +os: +List<Maybe<&2, Nat>>, +groups: +List<Groups.Group>,
    +kids: +List<Tree.Child>,
    ok: Cover.EntryOK(G, S, os, groups),
    small: Cover.EntrySmall(S, os, groups),
    kidsok: Cover.GroupKids(G, kids, groups)) ->
  CoverMaybe.Cover.MLe(Cover.TotalOpts(os, groups), Some{GC.GC.Total(kids, groups)}):
  match os:
    case Nil{}:
      match groups:
        case Nil{}:
          CoverMaybe.Cover.MLe_refl(Some{0n})
        case Con{gp, gs2}:
          match ok:
    case Con{o, os2}:
      match groups:
        case Nil{}:
          match ok:
        case Con{gp, gs2}:
          match gp:
            case Groups.Group{fb, ws}:
              (oh, ot) = ok
              (sh, st) = small
              (kh, kt) = kidsok
              head : CoverMaybe.Cover.MLe(o, Some{GC.GC.GroupCost(kids, Groups.Group{fb, ws})}) =
                Cover.opt_le_group(G, kids, fb, ws, o, oh(sh), kh)
              tail : CoverMaybe.Cover.MLe(Cover.TotalOpts(os2, gs2), Some{GC.GC.Total(kids, gs2)}) =
                Cover.total_opts_le(G, S, os2, gs2, kids, ot, st, kt)
              CoverMaybe.Cover.MAdd_le_some(o, Cover.TotalOpts(os2, gs2),
                GC.GC.GroupCost(kids, Groups.Group{fb, ws}), GC.GC.Total(kids, gs2),
                head, tail)
