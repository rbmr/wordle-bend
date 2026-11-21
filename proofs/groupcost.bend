# The cost of a list of feedback groups, and how it grows when a word is added.
#
# `Total` sums the children's costs over the groups. Building the groups one
# word at a time adds exactly the word's `kid_cost`, which is what turns the
# node-cost decomposition into the per-class bound of the optimality proof.
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ../src/groups.bend as Groups
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./nodecost.bend as NodeCost

# Cost of one group, given the `Maybe` tree its feedback looks up.
def GC.group_cost_of(+kids: +List<Tree.Child>, +ws: +List<+List<Nat>>,
    m: Maybe<Tree.Tree>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{t}:
      Tree.cost(t, ws)

def GC.GroupCost(+kids: +List<Tree.Child>, gp: Groups.Group) -> Nat:
  match gp:
    case Groups.Group{fb, ws}:
      GC.group_cost_of(kids, ws, Tree.lookup(fb, kids))

def GC.Total(+kids: +List<Tree.Child>, +gs: +List<Groups.Group>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case Con{gp, rest}:
      Nat.add(GC.GroupCost(kids, gp), GC.Total(kids, rest))

# A one-word class costs the depth of that word in its child.
def GC.single_cost(+kids: +List<Tree.Child>, +w: +List<Nat>, m: Maybe<Tree.Tree>) ->
  {GC.group_cost_of(kids, [w], m) == NodeCost.NodeCost.maybe_depth(m, w) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      NatProof.NatPrf.add_zero(Maybe.default(&1, Nat, Tree.depth(t, w), 0n))

# `cost` splits over an append.
def GC.cost_append(+t: Tree.Tree, +xs: +List<+List<Nat>>, +ys: +List<+List<Nat>>) ->
  {Tree.cost(t, List.append(&2, +List<Nat>, xs, ys))
   == Nat.add(Tree.cost(t, xs), Tree.cost(t, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, tail}:
      +ih : {Tree.cost(t, List.append(&2, +List<Nat>, tail, ys))
             == Nat.add(Tree.cost(t, tail), Tree.cost(t, ys)) : Nat} =
        GC.cost_append(t, tail, ys)
      +d : Nat = Maybe.default(&1, Nat, Tree.depth(t, h), 0n)
      +e1 : {Nat.add(d, Tree.cost(t, List.append(&2, +List<Nat>, tail, ys)))
             == Nat.add(d, Nat.add(Tree.cost(t, tail), Tree.cost(t, ys))) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(d, x),
                   Tree.cost(t, List.append(&2, +List<Nat>, tail, ys)),
                   Nat.add(Tree.cost(t, tail), Tree.cost(t, ys)), ih)
      +e2 : {Nat.add(d, Nat.add(Tree.cost(t, tail), Tree.cost(t, ys)))
             == Nat.add(Nat.add(d, Tree.cost(t, tail)), Tree.cost(t, ys)) : Nat} =
        Equal.sym(Nat, Nat.add(Nat.add(d, Tree.cost(t, tail)), Tree.cost(t, ys)),
                  Nat.add(d, Nat.add(Tree.cost(t, tail), Tree.cost(t, ys))),
                  NatProof.NatPrf.add_assoc(d, Tree.cost(t, tail), Tree.cost(t, ys)))
      Equal.trans(Nat,
                  Nat.add(d, Tree.cost(t, List.append(&2, +List<Nat>, tail, ys))),
                  Nat.add(d, Nat.add(Tree.cost(t, tail), Tree.cost(t, ys))),
                  Nat.add(Nat.add(d, Tree.cost(t, tail)), Tree.cost(t, ys)),
                  e1, e2)

# Appending a word to a class splits its cost.
def GC.append_cost(+kids: +List<Tree.Child>, +ws: +List<+List<Nat>>, +w: +List<Nat>,
    m: Maybe<Tree.Tree>) ->
  {GC.group_cost_of(kids, List.append(&2, +List<Nat>, ws, [w]), m)
   == Nat.add(GC.group_cost_of(kids, ws, m), GC.group_cost_of(kids, [w], m)) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      GC.cost_append(t, ws, [w])

# Appending a word to a group raises the group's cost by the word's one-word cost.
def GC.group_cost_append(+kids: +List<Tree.Child>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +w: +List<Nat>) ->
  {GC.GroupCost(kids, Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])})
   == Nat.add(GC.GroupCost(kids, Groups.Group{f, ws}),
              GC.group_cost_of(kids, [w], Tree.lookup(f, kids))) : Nat}:
  GC.append_cost(kids, ws, w, Tree.lookup(f, kids))

# `group_add` written with the feedback test as a parameter, so proofs can
# split on it even though the real test is a computed boolean.
def GC.group_add_bool(+g: +List<Nat>, +w: +List<Nat>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +rest: +List<Groups.Group>, b: Bool) -> +List<Groups.Group>:
  Feedback.Bool.case(+List<Groups.Group>, b,
    Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])} <> rest,
    Groups.Group{f, ws} <> Groups.group_add(w, Feedback.feedback(g, w), rest))

# The total after applying `group_add_bool`.
def GC.total_add_bool(+g: +List<Nat>, +kids: +List<Tree.Child>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +w: +List<Nat>, +rest: +List<Groups.Group>, b: Bool) -> Nat:
  GC.Total(kids, GC.group_add_bool(g, w, f, ws, rest, b))

# A word has the same cost in a group whose feedback equals the guess feedback.
def GC.kid_cost_at(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    +f: +List<Feedback.Color>,
    e: {Feedback.feedback(g, w) == f : +List<Feedback.Color>},
    ne: {Feedback.word_eq(g, w) == False{} : Bool}) ->
  {GC.group_cost_of(kids, [w], Tree.lookup(f, kids))
   == NodeCost.NodeCost.kid_cost(g, kids, w) : Nat}:
  single : {GC.group_cost_of(kids, [w], Tree.lookup(f, kids))
            == NodeCost.NodeCost.maybe_depth(Tree.lookup(f, kids), w) : Nat} =
    GC.single_cost(kids, w, Tree.lookup(f, kids))
  e_lk : {Tree.lookup(Feedback.feedback(g, w), kids) == Tree.lookup(f, kids)
          : Maybe<Tree.Tree>} =
    Equal.cong(+List<Feedback.Color>, Maybe<Tree.Tree>, x => Tree.lookup(x, kids),
               Feedback.feedback(g, w), f, e)
  e_md : {NodeCost.NodeCost.maybe_depth(Tree.lookup(f, kids), w)
          == NodeCost.NodeCost.maybe_depth(Tree.lookup(Feedback.feedback(g, w), kids), w) : Nat} =
    Equal.sym(Nat,
      NodeCost.NodeCost.maybe_depth(Tree.lookup(Feedback.feedback(g, w), kids), w),
      NodeCost.NodeCost.maybe_depth(Tree.lookup(f, kids), w),
      Equal.cong(Maybe<Tree.Tree>, Nat,
                 x => NodeCost.NodeCost.maybe_depth(x, w),
                 Tree.lookup(Feedback.feedback(g, w), kids), Tree.lookup(f, kids), e_lk))
  e_kid : {NodeCost.NodeCost.kid_cost(g, kids, w)
           == NodeCost.NodeCost.maybe_depth(Tree.lookup(Feedback.feedback(g, w), kids), w) : Nat} =
    Equal.cong(Bool, Nat,
      x => Feedback.Bool.case(Nat, x, 0n,
             NodeCost.NodeCost.maybe_depth(Tree.lookup(Feedback.feedback(g, w), kids), w)),
      Feedback.word_eq(g, w), False{}, ne)
  Equal.trans(Nat, GC.group_cost_of(kids, [w], Tree.lookup(f, kids)),
              NodeCost.NodeCost.maybe_depth(Tree.lookup(f, kids), w),
              NodeCost.NodeCost.kid_cost(g, kids, w), single,
              Equal.trans(Nat, NodeCost.NodeCost.maybe_depth(Tree.lookup(f, kids), w),
                          NodeCost.NodeCost.maybe_depth(Tree.lookup(Feedback.feedback(g, w), kids), w),
                          NodeCost.NodeCost.kid_cost(g, kids, w), e_md,
                          Equal.sym(Nat, NodeCost.NodeCost.kid_cost(g, kids, w),
                                    NodeCost.NodeCost.maybe_depth(Tree.lookup(Feedback.feedback(g, w), kids), w),
                                    e_kid)))

# Branch of `group_add_cost`, split on the feedback test.
def GC.group_add_cost_go(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    +f: +List<Feedback.Color>, +ws: +List<+List<Nat>>, +rest: +List<Groups.Group>,
    b: Bool, +eb: {b == Feedback.feedback_eq(Feedback.feedback(g, w), f) : Bool},
    ne: {Feedback.word_eq(g, w) == False{} : Bool},
    k: {Feedback.word_eq(g, w) == False{} : Bool}
       -> {GC.Total(kids, Groups.group_add(w, Feedback.feedback(g, w), rest))
           == Nat.add(GC.Total(kids, rest), NodeCost.NodeCost.kid_cost(g, kids, w)) : Nat}) ->
  {GC.total_add_bool(g, kids, f, ws, w, rest, b)
   == Nat.add(GC.Total(kids, Groups.Group{f, ws} <> rest),
              NodeCost.NodeCost.kid_cost(g, kids, w)) : Nat}:
  match b:
    case True{}:
      pfb : {Feedback.feedback_eq(Feedback.feedback(g, w), f) == True{} : Bool} =
        Equal.sym(Bool, b, Feedback.feedback_eq(Feedback.feedback(g, w), f), eb)
      e_f : {Feedback.feedback(g, w) == f : +List<Feedback.Color>} =
        FbProof.FbPrf.feedback_eq_true(Feedback.feedback(g, w), f, pfb)
      +gc : Nat = GC.GroupCost(kids, Groups.Group{f, ws})
      +tr : Nat = GC.Total(kids, rest)
      +kw : Nat = NodeCost.NodeCost.kid_cost(g, kids, w)
      e_gc : {GC.GroupCost(kids, Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])})
              == Nat.add(gc, kw) : Nat} =
        Equal.trans(Nat,
          GC.GroupCost(kids, Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])}),
          Nat.add(gc, GC.group_cost_of(kids, [w], Tree.lookup(f, kids))),
          Nat.add(gc, kw),
          GC.group_cost_append(kids, f, ws, w),
          Equal.cong(Nat, Nat, x => Nat.add(gc, x),
                     GC.group_cost_of(kids, [w], Tree.lookup(f, kids)), kw,
                     GC.kid_cost_at(g, kids, w, f, e_f, ne)))
      e0 : {Nat.add(GC.GroupCost(kids, Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])}), tr)
            == Nat.add(Nat.add(gc, kw), tr) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(x, tr),
                   GC.GroupCost(kids, Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])}),
                   Nat.add(gc, kw), e_gc)
      e1 : {Nat.add(Nat.add(gc, kw), tr) == Nat.add(Nat.add(gc, tr), kw) : Nat} =
        Equal.trans(Nat, Nat.add(Nat.add(gc, kw), tr), Nat.add(gc, Nat.add(kw, tr)),
                    Nat.add(Nat.add(gc, tr), kw),
                    NatProof.NatPrf.add_assoc(gc, kw, tr),
                    Equal.trans(Nat, Nat.add(gc, Nat.add(kw, tr)),
                                Nat.add(gc, Nat.add(tr, kw)),
                                Nat.add(Nat.add(gc, tr), kw),
                                Equal.cong(Nat, Nat, x => Nat.add(gc, x),
                                           Nat.add(kw, tr), Nat.add(tr, kw),
                                           NatProof.NatPrf.add_comm(kw, tr)),
                                Equal.sym(Nat, Nat.add(Nat.add(gc, tr), kw),
                                          Nat.add(gc, Nat.add(tr, kw)),
                                          NatProof.NatPrf.add_assoc(gc, tr, kw))))
      Equal.trans(Nat,
                  Nat.add(GC.GroupCost(kids, Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])}), tr),
                  Nat.add(Nat.add(gc, kw), tr),
                  Nat.add(Nat.add(gc, tr), kw), e0, e1)
    case False{}:
      +gc : Nat = GC.GroupCost(kids, Groups.Group{f, ws})
      +tr : Nat = GC.Total(kids, rest)
      +kw : Nat = NodeCost.NodeCost.kid_cost(g, kids, w)
      e_ih : {GC.Total(kids, Groups.group_add(w, Feedback.feedback(g, w), rest))
              == Nat.add(tr, kw) : Nat} = k(ne)
      e1 : {Nat.add(gc, GC.Total(kids, Groups.group_add(w, Feedback.feedback(g, w), rest)))
            == Nat.add(gc, Nat.add(tr, kw)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(gc, x),
                   GC.Total(kids, Groups.group_add(w, Feedback.feedback(g, w), rest)),
                   Nat.add(tr, kw), e_ih)
      e2 : {Nat.add(gc, Nat.add(tr, kw)) == Nat.add(Nat.add(gc, tr), kw) : Nat} =
        Equal.sym(Nat, Nat.add(Nat.add(gc, tr), kw), Nat.add(gc, Nat.add(tr, kw)),
                  NatProof.NatPrf.add_assoc(gc, tr, kw))
      Equal.trans(Nat, Nat.add(gc, GC.Total(kids, Groups.group_add(w, Feedback.feedback(g, w), rest))),
                  Nat.add(gc, Nat.add(tr, kw)),
                  Nat.add(Nat.add(gc, tr), kw), e1, e2)

# Adding one word raises the total cost by exactly that word's `kid_cost`.
def GC.group_add_cost(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    +gs: +List<Groups.Group>, ne: {Feedback.word_eq(g, w) == False{} : Bool}) ->
  {GC.Total(kids, Groups.group_add(w, Feedback.feedback(g, w), gs))
   == Nat.add(GC.Total(kids, gs), NodeCost.NodeCost.kid_cost(g, kids, w)) : Nat}:
  match gs:
    case Nil{}:
      +gc : Nat = GC.group_cost_of(kids, [w], Tree.lookup(Feedback.feedback(g, w), kids))
      +kw : Nat = NodeCost.NodeCost.kid_cost(g, kids, w)
      e_single : {gc == kw : Nat} =
        GC.kid_cost_at(g, kids, w, Feedback.feedback(g, w), {==}, ne)
      Equal.trans(Nat, Nat.add(gc, 0n), gc, kw, NatProof.NatPrf.add_zero(gc), e_single)
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          GC.group_add_cost_go(g, kids, w, f, ws, rest,
            Feedback.feedback_eq(Feedback.feedback(g, w), f), {==}, ne,
            ne2 => GC.group_add_cost(g, kids, w, rest, ne2))

# `groups_build` written with the word test as a parameter.
def GC.groups_build_bool(+g: +List<Nat>, +w: +List<Nat>, +t: +List<+List<Nat>>,
    +acc: +List<Groups.Group>, b: Bool) -> +List<Groups.Group>:
  Feedback.Bool.case(+List<Groups.Group>, b,
    Groups.groups_build(g, t, acc),
    Groups.groups_build(g, t, Groups.group_add(w, Feedback.feedback(g, w), acc)))

# Unfold `kid_cost` at an explicit boolean.
def GC.kid_unfold(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    b: Bool, +eb: {b == Feedback.word_eq(g, w) : Bool}) ->
  {NodeCost.NodeCost.kid_cost(g, kids, w)
   == Feedback.Bool.case(Nat, b, 0n,
        NodeCost.NodeCost.maybe_depth(Tree.lookup(Feedback.feedback(g, w), kids), w)) : Nat}:
  Equal.cong(Bool, Nat,
    x => Feedback.Bool.case(Nat, x, 0n,
           NodeCost.NodeCost.maybe_depth(Tree.lookup(Feedback.feedback(g, w), kids), w)),
    Feedback.word_eq(g, w), b, Equal.sym(Bool, b, Feedback.word_eq(g, w), eb))

# Branch of `groups_build_cost`, split on the word test.
def GC.groups_build_cost_go(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +w: +List<Nat>, +t: +List<+List<Nat>>, +acc: +List<Groups.Group>, b: Bool,
    +eb: {b == Feedback.word_eq(g, w) : Bool},
    k: @a: +List<Groups.Group>
       -> {GC.Total(kids, Groups.groups_build(g, t, a))
           == Nat.add(GC.Total(kids, a), NodeCost.NodeCost.kid_sum(g, kids, t)) : Nat}) ->
  {GC.Total(kids, GC.groups_build_bool(g, w, t, acc, b))
   == Nat.add(GC.Total(kids, acc), NodeCost.NodeCost.kid_sum(g, kids, w <> t)) : Nat}:
  match b:
    case True{}:
      ih : {GC.Total(kids, Groups.groups_build(g, t, acc))
            == Nat.add(GC.Total(kids, acc), NodeCost.NodeCost.kid_sum(g, kids, t)) : Nat} =
        k(acc)
      e_k0 : {NodeCost.NodeCost.kid_cost(g, kids, w) == 0n : Nat} =
        GC.kid_unfold(g, kids, w, b, eb)
      e_ks : {Nat.add(NodeCost.NodeCost.kid_cost(g, kids, w),
                      NodeCost.NodeCost.kid_sum(g, kids, t))
              == NodeCost.NodeCost.kid_sum(g, kids, t) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(x, NodeCost.NodeCost.kid_sum(g, kids, t)),
                   NodeCost.NodeCost.kid_cost(g, kids, w), 0n, e_k0)
      e_rhs : {Nat.add(GC.Total(kids, acc),
                       Nat.add(NodeCost.NodeCost.kid_cost(g, kids, w),
                               NodeCost.NodeCost.kid_sum(g, kids, t)))
               == Nat.add(GC.Total(kids, acc), NodeCost.NodeCost.kid_sum(g, kids, t)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(GC.Total(kids, acc), x),
                   Nat.add(NodeCost.NodeCost.kid_cost(g, kids, w),
                           NodeCost.NodeCost.kid_sum(g, kids, t)),
                   NodeCost.NodeCost.kid_sum(g, kids, t), e_ks)
      Equal.trans(Nat, GC.Total(kids, Groups.groups_build(g, t, acc)),
                  Nat.add(GC.Total(kids, acc), NodeCost.NodeCost.kid_sum(g, kids, t)),
                  Nat.add(GC.Total(kids, acc), NodeCost.NodeCost.kid_sum(g, kids, w <> t)),
                  ih, Equal.sym(Nat,
                    Nat.add(GC.Total(kids, acc), NodeCost.NodeCost.kid_sum(g, kids, w <> t)),
                    Nat.add(GC.Total(kids, acc), NodeCost.NodeCost.kid_sum(g, kids, t)),
                    e_rhs))
    case False{}:
      +ne : {Feedback.word_eq(g, w) == False{} : Bool} =
        Equal.sym(Bool, b, Feedback.word_eq(g, w), eb)
      +ih : {GC.Total(kids, Groups.groups_build(g, t,
                Groups.group_add(w, Feedback.feedback(g, w), acc)))
             == Nat.add(GC.Total(kids, Groups.group_add(w, Feedback.feedback(g, w), acc)),
                        NodeCost.NodeCost.kid_sum(g, kids, t)) : Nat} =
        k(Groups.group_add(w, Feedback.feedback(g, w), acc))
      +gac : {GC.Total(kids, Groups.group_add(w, Feedback.feedback(g, w), acc))
              == Nat.add(GC.Total(kids, acc), NodeCost.NodeCost.kid_cost(g, kids, w)) : Nat} =
        GC.group_add_cost(g, kids, w, acc, ne)
      +e1 : {Nat.add(GC.Total(kids, Groups.group_add(w, Feedback.feedback(g, w), acc)),
                     NodeCost.NodeCost.kid_sum(g, kids, t))
             == Nat.add(Nat.add(GC.Total(kids, acc), NodeCost.NodeCost.kid_cost(g, kids, w)),
                        NodeCost.NodeCost.kid_sum(g, kids, t)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(x, NodeCost.NodeCost.kid_sum(g, kids, t)),
                   GC.Total(kids, Groups.group_add(w, Feedback.feedback(g, w), acc)),
                   Nat.add(GC.Total(kids, acc), NodeCost.NodeCost.kid_cost(g, kids, w)), gac)
      +e2 : {Nat.add(Nat.add(GC.Total(kids, acc), NodeCost.NodeCost.kid_cost(g, kids, w)),
                     NodeCost.NodeCost.kid_sum(g, kids, t))
             == Nat.add(GC.Total(kids, acc),
                        Nat.add(NodeCost.NodeCost.kid_cost(g, kids, w),
                                NodeCost.NodeCost.kid_sum(g, kids, t))) : Nat} =
        NatProof.NatPrf.add_assoc(GC.Total(kids, acc), NodeCost.NodeCost.kid_cost(g, kids, w),
                                  NodeCost.NodeCost.kid_sum(g, kids, t))
      Equal.trans(Nat, GC.Total(kids, Groups.groups_build(g, t,
                    Groups.group_add(w, Feedback.feedback(g, w), acc))),
                  Nat.add(GC.Total(kids, Groups.group_add(w, Feedback.feedback(g, w), acc)),
                          NodeCost.NodeCost.kid_sum(g, kids, t)),
                  Nat.add(GC.Total(kids, acc),
                          Nat.add(NodeCost.NodeCost.kid_cost(g, kids, w),
                                  NodeCost.NodeCost.kid_sum(g, kids, t))),
                  ih, Equal.trans(Nat,
                    Nat.add(GC.Total(kids, Groups.group_add(w, Feedback.feedback(g, w), acc)),
                            NodeCost.NodeCost.kid_sum(g, kids, t)),
                    Nat.add(Nat.add(GC.Total(kids, acc), NodeCost.NodeCost.kid_cost(g, kids, w)),
                            NodeCost.NodeCost.kid_sum(g, kids, t)),
                    Nat.add(GC.Total(kids, acc),
                            Nat.add(NodeCost.NodeCost.kid_cost(g, kids, w),
                                    NodeCost.NodeCost.kid_sum(g, kids, t))),
                    e1, e2))

# The total cost of the groups built from S is the sum of the words' kid costs.
def GC.groups_build_cost(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>, +acc: +List<Groups.Group>) ->
  {GC.Total(kids, Groups.groups_build(g, S, acc))
   == Nat.add(GC.Total(kids, acc), NodeCost.NodeCost.kid_sum(g, kids, S)) : Nat}:
  match S:
    case Nil{}:
      Equal.sym(Nat, Nat.add(GC.Total(kids, acc), 0n), GC.Total(kids, acc),
                NatProof.NatPrf.add_zero(GC.Total(kids, acc)))
    case Con{w, t}:
      GC.groups_build_cost_go(g, kids, w, t, acc, Feedback.word_eq(g, w), {==},
        a => GC.groups_build_cost(g, kids, t, a))

# Starting from no groups, the total is exactly the node's child cost sum.
def GC.groups_build_total(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>) ->
  {GC.Total(kids, Groups.groups_build(g, S, Nil{}))
   == NodeCost.NodeCost.kid_sum(g, kids, S) : Nat}:
  GC.groups_build_cost(g, kids, S, Nil{})
