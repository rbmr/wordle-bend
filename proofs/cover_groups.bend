# Subsequences of the candidate list and the classes of a guess.
#
# In the no-progress case the root guess does not shrink the candidate list, so
# one feedback class holds all of `S` and the tree descends on the same `S`.
# This module proves that a class is always a subsequence of `S`, that a class
# with at least `|S|` words is exactly `S`, and finds such a class when
# `groups_smaller` is false. It also bounds one class's cost by the whole sum.
import Base
import ../src/tree.bend as Tree
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./groups.bend as Grp
import ./groupcost.bend as GC
import ./cover_list.bend as CoverList

# Every class of a group list is a subsequence of the same list.
def Cover.AllSubseq(+groups: +List<Groups.Group>,
    +ys: +List<+List<Nat>>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          CoverList.Cover.Subseq(ws, ys) & Cover.AllSubseq(rest, ys)

# Appending a word preserves the subsequence relation.
def Cover.subseq_snoc(+ws: +List<+List<Nat>>, +ys: +List<+List<Nat>>,
    +w: +List<Nat>, p: CoverList.Cover.Subseq(ws, ys)) ->
  CoverList.Cover.Subseq(List.append(&2, +List<Nat>, ws, [w]),
                         List.append(&2, +List<Nat>, ys, [w])):
  match ws ys:
    case Nil{} _:
      CoverList.Cover.subseq_head(w, ys)
    case Con{h, t} Nil{}:
      match p:
    case Con{h, t} Con{y, r}:
      match p:
        case Inl{q}:
          (e, pt) = q
          Inl{(e, Cover.subseq_snoc(t, r, w, pt))}
        case Inr{q}:
          Inr{Cover.subseq_snoc(ws, r, w, q)}

# Weakening every class of a group list.
def Cover.all_subseq_weaken(+groups: +List<Groups.Group>,
    +ys: +List<+List<Nat>>, +w: +List<Nat>,
    p: Cover.AllSubseq(groups, ys)) ->
  Cover.AllSubseq(groups, List.append(&2, +List<Nat>, ys, [w])):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          (ph, pt) = p
          (CoverList.Cover.subseq_weaken(ws, ys, w, ph),
           Cover.all_subseq_weaken(rest, ys, w, pt))

# Split of `group_add` on the feedback test.
def Cover.all_subseq_group_add_go(+w: +List<Nat>,
    +fb: +List<Feedback.Color>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +rest: +List<Groups.Group>,
    +ys: +List<+List<Nat>>, b: Bool,
    +eb: {b == Feedback.feedback_eq(fb, f) : Bool},
    ph: CoverList.Cover.Subseq(ws, ys), pt: Cover.AllSubseq(rest, ys),
    k: Cover.AllSubseq(rest, ys)
       -> Cover.AllSubseq(Groups.group_add(w, fb, rest),
                          List.append(&2, +List<Nat>, ys, [w]))) ->
  Cover.AllSubseq(
    Feedback.Bool.case(+List<Groups.Group>, b,
      Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])} <> rest,
      Groups.Group{f, ws} <> Groups.group_add(w, fb, rest)),
    List.append(&2, +List<Nat>, ys, [w])):
  match b:
    case True{}:
      (Cover.subseq_snoc(ws, ys, w, ph),
       Cover.all_subseq_weaken(rest, ys, w, pt))
    case False{}:
      (CoverList.Cover.subseq_weaken(ws, ys, w, ph), k(pt))

# Adding a word keeps every class a subsequence.
def Cover.all_subseq_group_add(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +acc: +List<Groups.Group>, +ys: +List<+List<Nat>>,
    p: Cover.AllSubseq(acc, ys)) ->
  Cover.AllSubseq(Groups.group_add(w, fb, acc),
                  List.append(&2, +List<Nat>, ys, [w])):
  match acc:
    case Nil{}:
      (CoverList.Cover.subseq_head(w, ys), Unit{})
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          (ph, pt) = p
          Cover.all_subseq_group_add_go(w, fb, f, ws, rest, ys,
            Feedback.feedback_eq(fb, f), {==}, ph, pt,
            p2 => Cover.all_subseq_group_add(w, fb, rest, ys, p2))

# `(ys ++ [w]) ++ rest` is `ys ++ (w :: rest)`.
def Cover.append_word_assoc(+ys: +List<+List<Nat>>, +w: +List<Nat>,
    +rest: +List<+List<Nat>>) ->
  {List.append(&2, +List<Nat>, List.append(&2, +List<Nat>, ys, [w]), rest)
   == List.append(&2, +List<Nat>, ys, w <> rest) : +List<+List<Nat>>}:
  match ys:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>,
        x => h <> x,
        List.append(&2, +List<Nat>, List.append(&2, +List<Nat>, t, [w]), rest),
        List.append(&2, +List<Nat>, t, w <> rest),
        Cover.append_word_assoc(t, w, rest))

# The empty suffix appends to nothing.
def Cover.append_nil(+xs: +List<+List<Nat>>) ->
  {List.append(&2, +List<Nat>, xs, Nil{}) == xs : +List<+List<Nat>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>, x => h <> x,
        List.append(&2, +List<Nat>, t, Nil{}), t, Cover.append_nil(t))

# Reassociate the build's suffix into the goal's shape.
def Cover.build_transport(+g: +List<Nat>, +t: +List<+List<Nat>>,
    +acc: +List<Groups.Group>, +ys: +List<+List<Nat>>, +w: +List<Nat>,
    p: Cover.AllSubseq(Groups.groups_build(g, t, acc),
      List.append(&2, +List<Nat>,
        List.append(&2, +List<Nat>, ys, [w]), t))) ->
  Cover.AllSubseq(Groups.groups_build(g, t, acc),
                  List.append(&2, +List<Nat>, ys, w <> t)):
  %Cover.append_word_assoc(ys, w, t) :
    Cover.AllSubseq(Groups.groups_build(g, t, acc), _)
  p

# Split of `groups_build` on the word test.
def Cover.all_subseq_build_go(+g: +List<Nat>, +w: +List<Nat>,
    +t: +List<+List<Nat>>, +acc: +List<Groups.Group>,
    +ys: +List<+List<Nat>>, b: Bool,
    +eb: {b == Feedback.word_eq(g, w) : Bool},
    p: Cover.AllSubseq(acc, ys),
    k: @acc2: +List<Groups.Group> -> @ys2: +List<+List<Nat>> ->
       Cover.AllSubseq(acc2, ys2) ->
       Cover.AllSubseq(Groups.groups_build(g, t, acc2),
                       List.append(&2, +List<Nat>, ys2, t))) ->
  Cover.AllSubseq(
    Feedback.Bool.case(+List<Groups.Group>, b,
      Groups.groups_build(g, t, acc),
      Groups.groups_build(g, t,
        Groups.group_add(w, Feedback.feedback(g, w), acc))),
    List.append(&2, +List<Nat>, ys, w <> t)):
  match b:
    case True{}:
      Cover.build_transport(g, t, acc, ys, w,
        k(acc, List.append(&2, +List<Nat>, ys, [w]),
          Cover.all_subseq_weaken(acc, ys, w, p)))
    case False{}:
      Cover.build_transport(g, t,
        Groups.group_add(w, Feedback.feedback(g, w), acc), ys, w,
        k(Groups.group_add(w, Feedback.feedback(g, w), acc),
          List.append(&2, +List<Nat>, ys, [w]),
          Cover.all_subseq_group_add(w, Feedback.feedback(g, w), acc, ys, p)))

# Every class built from `S` is a subsequence of `ys ++ S`.
def Cover.all_subseq_build(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +acc: +List<Groups.Group>, +ys: +List<+List<Nat>>,
    p: Cover.AllSubseq(acc, ys)) ->
  Cover.AllSubseq(Groups.groups_build(g, S, acc),
                  List.append(&2, +List<Nat>, ys, S)):
  match S:
    case Nil{}:
      %Equal.sym(+List<+List<Nat>>,
        List.append(&2, +List<Nat>, ys, Nil{}), ys, Cover.append_nil(ys)) :
        Cover.AllSubseq(Groups.groups_build(g, Nil{}, acc), _)
      p
    case Con{w, t}:
      Cover.all_subseq_build_go(g, w, t, acc, ys, Feedback.word_eq(g, w), {==}, p,
        acc2 => ys2 => p2 => Cover.all_subseq_build(g, t, acc2, ys2, p2))

# The starting call: every class is a subsequence of `S`.
def Cover.all_subseq_nil(+g: +List<Nat>, +S: +List<+List<Nat>>) ->
  Cover.AllSubseq(Groups.groups_build(g, S, Nil{}), S):
  Cover.all_subseq_build(g, S, Nil{}, Nil{}, Unit{})

# Membership of a group in a group list.
def Cover.MemGroup(+gp: Groups.Group, +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Empty
    case Con{q, rest}:
      {gp == q : Groups.Group} | Cover.MemGroup(gp, rest)

# A class costs at most the total of its list.
def Cover.mem_total_le(+kids: +List<Tree.Child>, +groups: +List<Groups.Group>,
    +gp: Groups.Group, m: Cover.MemGroup(gp, groups)) ->
  {Nat.is_le(GC.GC.GroupCost(kids, gp), GC.GC.Total(kids, groups)) == True{} : Bool}:
  match groups:
    case Nil{}:
      match m:
    case Con{q, rest}:
      match m:
        case Inl{e}:
          %Equal.sym(Groups.Group, gp, q, e) :
            {Nat.is_le(GC.GC.GroupCost(kids, _), GC.GC.Total(kids, q <> rest)) == True{} : Bool}
          +gc : Nat = GC.GC.GroupCost(kids, q)
          +tr : Nat = GC.GC.Total(kids, rest)
          +e_comm : {Nat.add(gc, tr) == Nat.add(tr, gc) : Nat} =
            NatProof.NatPrf.add_comm(gc, tr)
          +le : {Nat.is_le(gc, Nat.add(tr, gc)) == True{} : Bool} =
            NatProof.Nat.is_le_add_self_l(tr, gc)
          Equal.trans(Bool, Nat.is_le(gc, Nat.add(gc, tr)),
            Nat.is_le(gc, Nat.add(tr, gc)), True{},
            Equal.cong(Nat, Bool, x => Nat.is_le(gc, x),
              Nat.add(gc, tr), Nat.add(tr, gc), e_comm), le)
        case Inr{m2}:
          +le_gp : {Nat.is_le(GC.GC.GroupCost(kids, gp),
                     GC.GC.Total(kids, rest)) == True{} : Bool} =
            Cover.mem_total_le(kids, rest, gp, m2)
          +le_tot : {Nat.is_le(GC.GC.Total(kids, rest),
                      Nat.add(GC.GC.GroupCost(kids, q),
                        GC.GC.Total(kids, rest))) == True{} : Bool} =
            NatProof.Nat.is_le_add_self_l(GC.GC.GroupCost(kids, q),
              GC.GC.Total(kids, rest))
          NatProof.Nat.is_le_trans(GC.GC.GroupCost(kids, gp),
            GC.GC.Total(kids, rest),
            Nat.add(GC.GC.GroupCost(kids, q), GC.GC.Total(kids, rest)),
            le_gp, le_tot)

# A class with all its per-word facts and a subsequence witness.
def Cover.BadFacts(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +groups: +List<Groups.Group>, +S: +List<+List<Nat>>,
    gp: Groups.Group) -> Type:
  match gp:
    case Groups.Group{fb, ws}:
      Grp.Grp.WordsDepths(g, kids, fb, ws)
      & CoverList.Cover.Subseq(ws, S)
      & {Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == False{} : Bool}
      & Cover.MemGroup(Groups.Group{fb, ws}, groups)

# Every class of a built group list carries its per-word facts and is a
# subsequence of `S`.
def Cover.ClassData(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>, +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          (Grp.Grp.WordsDepths(g, kids, fb, ws) & CoverList.Cover.Subseq(ws, S))
          & Cover.ClassData(g, kids, S, rest)

def Cover.class_data(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>, +groups: +List<Groups.Group>,
    agd: Grp.Grp.AllGroupDepths(g, kids, groups),
    allsub: Cover.AllSubseq(groups, S)) -> Cover.ClassData(g, kids, S, groups):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          (wd, agd2) = agd
          (sub, sub2) = allsub
          ((wd, sub), Cover.class_data(g, kids, S, rest, agd2, sub2))

# Extend the membership witness when the found class sits in a tail.
def Cover.badfacts_lift(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>, +fb: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +rest: +List<Groups.Group>,
    gp: Groups.Group, bf: Cover.BadFacts(g, kids, rest, S, gp)) ->
  Cover.BadFacts(g, kids, Groups.Group{fb, ws} <> rest, S, gp):
  match gp:
    case Groups.Group{f2, w2}:
      (wd, rest2) = bf
      (sub, rest3) = rest2
      (bad, mem) = rest3
      (wd, (sub, (bad, Inr{mem})))

def Cover.badfacts_lift_sigma(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>, +fb: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +rest: +List<Groups.Group>,
    r: Sigma<&2, &1, Groups.Group, gp => Cover.BadFacts(g, kids, rest, S, gp)>) ->
  Sigma<&2, &1, Groups.Group, gp =>
    Cover.BadFacts(g, kids, Groups.Group{fb, ws} <> rest, S, gp)>:
  match r:
    case Tuple{+gp, bf}:
      (gp, Cover.badfacts_lift(g, kids, S, fb, ws, rest, gp, bf))

# The `groups_smaller` conjunction is false only for a bad class.
def Cover.find_bad_go(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>, +fb: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +rest: +List<Groups.Group>,
    facts: (Grp.Grp.WordsDepths(g, kids, fb, ws)
            & CoverList.Cover.Subseq(ws, S)),
    data_rest: Cover.ClassData(g, kids, S, rest),
    b: Bool, +eb: {b == Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) : Bool},
    e: {Groups.groups_smaller(S, Groups.Group{fb, ws} <> rest) == False{} : Bool},
    k: Cover.ClassData(g, kids, S, rest)
       -> {Groups.groups_smaller(S, rest) == False{} : Bool}
       -> Sigma<&2, &1, Groups.Group, gp =>
            Cover.BadFacts(g, kids, Groups.Group{fb, ws} <> rest, S, gp)>) ->
  Sigma<&2, &1, Groups.Group, gp =>
    Cover.BadFacts(g, kids, Groups.Group{fb, ws} <> rest, S, gp)>:
  (wd, sub) = facts
  match b:
    case True{}:
      +efull : {Bool.and(Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)),
                         Groups.groups_smaller(S, rest)) == False{} : Bool} = e
      +econg : {Bool.and(True{}, Groups.groups_smaller(S, rest))
                == Bool.and(Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)),
                            Groups.groups_smaller(S, rest)) : Bool} =
        Equal.cong(Bool, Bool, x => Bool.and(x, Groups.groups_smaller(S, rest)),
          True{}, Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)), eb)
      +e_tail : {Groups.groups_smaller(S, rest) == False{} : Bool} =
        Equal.trans(Bool, Bool.and(True{}, Groups.groups_smaller(S, rest)),
          Bool.and(Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)),
                   Groups.groups_smaller(S, rest)),
          False{}, econg, efull)
      k(data_rest, e_tail)
    case False{}:
      +bad : {Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == False{} : Bool} =
        Equal.sym(Bool, False{},
          Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)), eb)
      (Groups.Group{fb, ws},
       (wd, (sub, (bad, Inl{{==}}))))

# Find a class that is not shorter than `S`.
def Cover.find_bad(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>, +groups: +List<Groups.Group>,
    data: Cover.ClassData(g, kids, S, groups),
    e: {Groups.groups_smaller(S, groups) == False{} : Bool}) ->
  Sigma<&2, &1, Groups.Group, gp => Cover.BadFacts(g, kids, groups, S, gp)>:
  match groups:
    case Nil{}:
      Empty.absurd(Sigma<&2, &1, Groups.Group, gp => Cover.BadFacts(g, kids, Nil{}, S, gp)>,
        Logic.Proof.true_ne_false(e))
    case Con{gp, rest}:
      match gp:
        case Groups.Group{fb, ws}:
          (facts, data_rest) = data
          Cover.find_bad_go(g, kids, S, fb, ws, rest, facts, data_rest,
            Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)), {==}, e,
            data2 => e2 =>
              Cover.badfacts_lift_sigma(g, kids, S, fb, ws, rest,
                Cover.find_bad(g, kids, S, rest, data2, e2)))

# Comparison with its arguments swapped.
def Cover.cmp_swap(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def Cover.cmp_swap_cmp(a: Nat, b: Nat) ->
  {Nat.cmp(b, a) == Cover.cmp_swap(Nat.cmp(a, b)) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      Cover.cmp_swap_cmp(ap, bp)

def Cover.is_le_swap_go(c: Cmp, +e: {Cmp.is_lt(c) == False{} : Bool}) ->
  {Cmp.is_le(Cover.cmp_swap(c)) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({Cmp.is_le(Cover.cmp_swap(LT{})) == True{} : Bool},
        Logic.Proof.true_ne_false(e))
    case EQ{}:
      {==}
    case GT{}:
      {==}

# A false `is_lt` gives the swapped `is_le`.
def Cover.is_le_of_lt_false(+a: Nat, +b: Nat,
    +e: {Nat.is_lt(a, b) == False{} : Bool}) ->
  {Nat.is_le(b, a) == True{} : Bool}:
  +c : Cmp = Nat.cmp(a, b)
  +h : {Nat.cmp(b, a) == Cover.cmp_swap(c) : Cmp} = Cover.cmp_swap_cmp(a, b)
  +eg : {Cmp.is_le(Nat.cmp(b, a)) == Cmp.is_le(Cover.cmp_swap(c)) : Bool} =
    Equal.cong(Cmp, Bool, Cmp.is_le, Nat.cmp(b, a), Cover.cmp_swap(c), h)
  Equal.trans(Bool, Cmp.is_le(Nat.cmp(b, a)),
    Cmp.is_le(Cover.cmp_swap(c)), True{}, eg, Cover.is_le_swap_go(c, e))
