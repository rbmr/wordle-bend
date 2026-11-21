# From a valid node to the per-class child invariant.
#
# The cover argument must compare the oracle's class optima with the children
# of an arbitrary valid tree. `groups_build` drops the guess itself, so every
# class consists of non-guess candidates; the node's depth for such a word
# exists only when `lookup` finds the class's child, and then that child has a
# depth for every word of the class. This module turns the node's depth
# evidence into `GroupKids`: for each class, the looked-up child is a valid
# tree for the class.
import Base
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./groups.bend as Grp
import ./depth.bend as DepthProof
import ./nodecost.bend as NodeCost
import ./kids.bend as KidsProof
import ./cover_oracle.bend as CoverOracle
import ./cover_list.bend as CoverList

# Whether a class has a word.
def Cover.words_ne(+ws: +List<+List<Nat>>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{h, t}:
      True{}

# Appending a word makes a class nonempty.
def Cover.words_ne_snoc(+ws: +List<+List<Nat>>, +w: +List<Nat>) ->
  {Cover.words_ne(List.append(&2, +List<Nat>, ws, [w])) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# Whether every class of a group list has a word.
def Cover.all_ne(+gs: +List<Groups.Group>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          Bool.and(Cover.words_ne(ws), Cover.all_ne(rest))

# `group_add` keeps every class nonempty.
def Cover.group_add_ne_go(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +rest: +List<Groups.Group>, b: Bool,
    +eb: {b == Feedback.feedback_eq(fb, f) : Bool},
    +nh: {Cover.words_ne(ws) == True{} : Bool},
    +nt: {Cover.all_ne(rest) == True{} : Bool},
    +rec: {Cover.all_ne(Groups.group_add(w, fb, rest)) == True{} : Bool}) ->
  {Cover.all_ne(Feedback.Bool.case(+List<Groups.Group>, b,
     Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])} <> rest,
     Groups.Group{f, ws} <> Groups.group_add(w, fb, rest))) == True{} : Bool}:
  match b:
    case True{}:
      +es : {Cover.words_ne(List.append(&2, +List<Nat>, ws, [w])) == True{} : Bool} =
        Cover.words_ne_snoc(ws, w)
      Equal.trans(Bool,
        Bool.and(Cover.words_ne(List.append(&2, +List<Nat>, ws, [w])),
          Cover.all_ne(rest)),
        Bool.and(True{}, Cover.all_ne(rest)), True{},
        Equal.cong(Bool, Bool, x => Bool.and(x, Cover.all_ne(rest)),
          Cover.words_ne(List.append(&2, +List<Nat>, ws, [w])), True{}, es),
        nt)
    case False{}:
      Logic.Proof.and_intro(Cover.words_ne(ws),
        Cover.all_ne(Groups.group_add(w, fb, rest)), nh, rec)

def Cover.group_add_ne(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +gs: +List<Groups.Group>,
    +ok: {Cover.all_ne(gs) == True{} : Bool}) ->
  {Cover.all_ne(Groups.group_add(w, fb, gs)) == True{} : Bool}:
  match gs:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          +nh : {Cover.words_ne(ws) == True{} : Bool} =
            Logic.Proof.and_true_l(Cover.words_ne(ws), Cover.all_ne(rest), ok)
          +nt : {Cover.all_ne(rest) == True{} : Bool} =
            Logic.Proof.and_true_r(Cover.words_ne(ws), Cover.all_ne(rest), ok)
          Cover.group_add_ne_go(w, fb, f, ws, rest, Feedback.feedback_eq(fb, f),
            {==}, nh, nt, Cover.group_add_ne(w, fb, rest, nt))

def Cover.groups_build_ne_go(+g: +List<Nat>, +rest: +List<+List<Nat>>,
    +w: +List<Nat>, +acc: +List<Groups.Group>, b: Bool,
    +eb: {b == Feedback.word_eq(g, w) : Bool},
    +ok: {Cover.all_ne(acc) == True{} : Bool},
    k: @a: +List<Groups.Group> -> {Cover.all_ne(a) == True{} : Bool}
       -> {Cover.all_ne(Groups.groups_build(g, rest, a)) == True{} : Bool}) ->
  {Cover.all_ne(Feedback.Bool.case(+List<Groups.Group>, b,
     Groups.groups_build(g, rest, acc),
     Groups.groups_build(g, rest,
       Groups.group_add(w, Feedback.feedback(g, w), acc)))) == True{} : Bool}:
  match b:
    case True{}:
      k(acc, ok)
    case False{}:
      +eacc : {Cover.all_ne(Groups.group_add(w, Feedback.feedback(g, w), acc))
               == True{} : Bool} =
        Cover.group_add_ne(w, Feedback.feedback(g, w), acc, ok)
      k(Groups.group_add(w, Feedback.feedback(g, w), acc), eacc)

def Cover.groups_build_ne(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +acc: +List<Groups.Group>,
    +ok: {Cover.all_ne(acc) == True{} : Bool}) ->
  {Cover.all_ne(Groups.groups_build(g, S, acc)) == True{} : Bool}:
  match S:
    case Nil{}:
      ok
    case Con{w, t}:
      Cover.groups_build_ne_go(g, t, w, acc, Feedback.word_eq(g, w), {==}, ok,
        a => eok => Cover.groups_build_ne(g, t, a, eok))

# Transport the per-word looked-up depth facts along an equality of lookups.
def Cover.kid_every_transport(m1: Maybe<Tree.Tree>, m2: Maybe<Tree.Tree>,
    +ws: +List<+List<Nat>>, e: {m1 == m2 : Maybe<Tree.Tree>},
    every: KidsProof.KidsProof.KidEvery(m1, ws)) -> KidsProof.KidsProof.KidEvery(m2, ws):
  %e : KidsProof.KidsProof.KidEvery(_, ws)
  every

# A `Maybe` tree known to be `Some` with a continuation.
def Cover.some_lookup(-R: Type, m: Maybe<Tree.Tree>,
    +s: {Maybe.is_some(&1, Tree.Tree, m) == True{} : Bool},
    k: @+T: Tree.Tree -> @+e: {m == Some{T} : Maybe<Tree.Tree>} -> R) -> R:
  match m:
    case None{}:
      Empty.absurd(R, Logic.Proof.false_ne_true(s))
    case Some{T}:
      k(T, {==})

# A boolean form of `KidsIn`, so the evidence can be reused across classes.
def Cover.kids_in_b(+kids: +List<Tree.Child>, +G: +List<+List<Nat>>) -> Bool:
  match kids:
    case Nil{}:
      True{}
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          match child:
            case Tree.Node{g, ckids}:
              Bool.and(Bool.and(Tree.member_word(g, G),
                                Cover.kids_in_b(ckids, G)),
                       Cover.kids_in_b(rest, G))

def Cover.tree_in_b(t: Tree.Tree, +G: +List<+List<Nat>>) -> Bool:
  match t:
    case Tree.Node{g, kids}:
      Bool.and(Tree.member_word(g, G), Cover.kids_in_b(kids, G))

# The boolean form implies the invariant.
def Cover.kids_in_of_b(+kids: +List<Tree.Child>, +G: +List<+List<Nat>>,
    +e: {Cover.kids_in_b(kids, G) == True{} : Bool}) -> Tree.KidsIn(kids, G):
  match kids:
    case Nil{}:
      Unit{}
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          match child:
            case Tree.Node{g, ckids}:
              +eh : {Bool.and(Bool.and(Tree.member_word(g, G),
                         Cover.kids_in_b(ckids, G)),
                         Cover.kids_in_b(rest, G)) == True{} : Bool} = e
              +ein : {Bool.and(Tree.member_word(g, G),
                         Cover.kids_in_b(ckids, G)) == True{} : Bool} =
                Logic.Proof.and_true_l(Bool.and(Tree.member_word(g, G),
                    Cover.kids_in_b(ckids, G)), Cover.kids_in_b(rest, G), eh)
              +erest : {Cover.kids_in_b(rest, G) == True{} : Bool} =
                Logic.Proof.and_true_r(Bool.and(Tree.member_word(g, G),
                    Cover.kids_in_b(ckids, G)), Cover.kids_in_b(rest, G), eh)
              +ew : {Tree.member_word(g, G) == True{} : Bool} =
                Logic.Proof.and_true_l(Tree.member_word(g, G),
                  Cover.kids_in_b(ckids, G), ein)
              +ek : {Cover.kids_in_b(ckids, G) == True{} : Bool} =
                Logic.Proof.and_true_r(Tree.member_word(g, G),
                  Cover.kids_in_b(ckids, G), ein)
              ((ew, Cover.kids_in_of_b(ckids, G, ek)),
               Cover.kids_in_of_b(rest, G, erest))

# The invariant implies the boolean form.
def Cover.kids_in_to_b(+kids: +List<Tree.Child>, +G: +List<+List<Nat>>,
    ki: Tree.KidsIn(kids, G)) ->
  {Cover.kids_in_b(kids, G) == True{} : Bool}:
  match kids:
    case Nil{}:
      {==}
    case Con{c, rest}:
      match c:
        case Tree.Child{f, child}:
          match child:
            case Tree.Node{g, ckids}:
              (ti, ki2) = ki
              (ew, ek) = ti
              +eb : {Cover.kids_in_b(ckids, G) == True{} : Bool} =
                Cover.kids_in_to_b(ckids, G, ek)
              +er : {Cover.kids_in_b(rest, G) == True{} : Bool} =
                Cover.kids_in_to_b(rest, G, ki2)
              Logic.Proof.and_intro(Bool.and(Tree.member_word(g, G),
                  Cover.kids_in_b(ckids, G)), Cover.kids_in_b(rest, G),
                Logic.Proof.and_intro(Tree.member_word(g, G),
                  Cover.kids_in_b(ckids, G), ew, eb), er)

# The class child, from the per-word looked-up depths. The lookup result `m` is
# a parameter so matching it refines the per-word facts; the equality to the
# real lookup and the head fact are taken in reusable pairs.
def Cover.groupkid_class_go(-R: Type, +G: +List<+List<Nat>>, +g: +List<Nat>,
    +kids: +List<Tree.Child>, +fb: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>,
    +ne: {Cover.words_ne(ws) == True{} : Bool},
    +kb: {Cover.kids_in_b(kids, G) == True{} : Bool},
    m: Maybe<Tree.Tree>,
    every: KidsProof.KidsProof.KidEvery(m, ws),
    p: ({Tree.lookup(fb, kids) == m : Maybe<Tree.Tree>} & Unit),
    k: CoverOracle.Cover.GroupKid(G, kids, Groups.Group{fb, ws}) -> R) -> R:
  match ws:
    case Nil{}:
      Empty.absurd(R, Logic.Proof.false_ne_true(ne))
    case Con{w, t}:
      match m:
        case None{}:
          (+eh0, et0) = every
          Empty.absurd(R, Logic.Proof.false_ne_true(
            NodeCost.NodeCost.some_of_lookup_depth(m, w, eh0)))
        case Some{+T}:
          (+eh, et) = every
          (+e_lm, u) = p
          ad : Tree.AllHaveDepth(T, w <> t) =
            KidsProof.KidsProof.kid_every_depth(T, w <> t, (eh, et))
          mem : KidsProof.KidsProof.ChildMem(T, kids) =
            KidsProof.KidsProof.lookup_mem(fb, kids, T, e_lm)
          ti : Tree.TreeIn(T, G) =
            KidsProof.KidsProof.kids_in_member(kids, G,
              Cover.kids_in_of_b(kids, G, kb), T, mem)
          k((T, (e_lm, (ti, ad))))

# From a class with at least one word and its per-word facts, the looked-up
# child is valid for the whole class.
def Cover.groupkid_class(-R: Type, +G: +List<+List<Nat>>, +g: +List<Nat>,
    +kids: +List<Tree.Child>, +fb: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>,
    +ne: {Cover.words_ne(ws) == True{} : Bool},
    +kb: {Cover.kids_in_b(kids, G) == True{} : Bool},
    wd: Grp.Grp.WordsDepths(g, kids, fb, ws),
    k: CoverOracle.Cover.GroupKid(G, kids, Groups.Group{fb, ws}) -> R) -> R:
  every : KidsProof.KidsProof.KidEvery(Tree.lookup(fb, kids), ws) =
    KidsProof.KidsProof.words_kid_every(g, kids, fb, ws, wd)
  p : ({Tree.lookup(fb, kids) == Tree.lookup(fb, kids) : Maybe<Tree.Tree>} & Unit) =
    ({==}, Unit{})
  Cover.groupkid_class_go(R, G, g, kids, fb, ws, ne, kb,
    Tree.lookup(fb, kids), every, p, k)

# The per-class child invariant for a whole group list, from the per-class
# word/depth facts and the nonemptiness of every class.
def Cover.groupkids_from(-R: Type, +G: +List<+List<Nat>>, +g: +List<Nat>,
    +kids: +List<Tree.Child>, +groups: +List<Groups.Group>,
    +kb: {Cover.kids_in_b(kids, G) == True{} : Bool},
    +neok: {Cover.all_ne(groups) == True{} : Bool},
    agd: Grp.Grp.AllGroupDepths(g, kids, groups),
    k: CoverOracle.Cover.GroupKids(G, kids, groups) -> R) -> R:
  match groups:
    case Nil{}:
      k(Unit{})
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          (gd, adrest) = agd
          +nh : {Cover.words_ne(ws) == True{} : Bool} =
            Logic.Proof.and_true_l(Cover.words_ne(ws), Cover.all_ne(rest), neok)
          +nt : {Cover.all_ne(rest) == True{} : Bool} =
            Logic.Proof.and_true_r(Cover.words_ne(ws), Cover.all_ne(rest), neok)
          Cover.groupkid_class(R, G, g, kids, f, ws, nh, kb, gd,
            kid =>
              Cover.groupkids_from(R, G, g, kids, rest, kb, nt, adrest,
                restkids => k((kid, restkids))))
