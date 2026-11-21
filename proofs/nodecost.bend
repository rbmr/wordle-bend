# The cost of a node splits into one guess per candidate plus the children.
#
# `Tree.depth` at a node is one plus the depth of the looked-up child, so the
# cost of `Node(g, kids)` over a candidate list is the number of candidates
# plus the sum of the children's depths, one per non-guess candidate. This is
# the pointwise half of the cost decomposition the optimality proof needs.
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./depth.bend as DepthProof

# `bump` keeps whether a depth exists.
def NodeCost.is_some_bump(m: Maybe<Nat>) ->
  {Maybe.is_some(&1, Nat, Tree.depth.bump(m)) == Maybe.is_some(&1, Nat, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

# A `Some` depth is the successor of its default.
def NodeCost.bump_default(m: Maybe<Nat>,
    s: {Maybe.is_some(&1, Nat, m) == True{} : Bool}) ->
  {Tree.depth.bump(m) == Some{(1n + Maybe.default(&1, Nat, m, 0n) : Nat)} : Maybe<Nat>}:
  match m:
    case None{}:
      Empty.absurd(
        {Tree.depth.bump(None{}) == Some{(1n + Maybe.default(&1, Nat, None{}, 0n) : Nat)} : Maybe<Nat>},
        Logic.Proof.false_ne_true(s))
    case Some{n}:
      {==}

# If a looked-up depth exists then the lookup found a tree.
def NodeCost.some_of_lookup_depth(m: Maybe<Tree.Tree>, +a: +List<Nat>,
    s: {Maybe.is_some(&1, Nat, DepthProof.DepthProof.lookup_depth(m, a)) == True{} : Bool}) ->
  {Maybe.is_some(&1, Tree.Tree, m) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Maybe.is_some(&1, Tree.Tree, None{}) == True{} : Bool},
                   Logic.Proof.false_ne_true(s))
    case Some{t}:
      {==}

# The depth contribution of a looked-up child, or zero when there is none.
def NodeCost.maybe_depth(m: Maybe<Tree.Tree>, +a: +List<Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{t}:
      Maybe.default(&1, Nat, Tree.depth(t, a), 0n)

def NodeCost.kid_depth(+kids: +List<Tree.Child>, +fb: +List<Feedback.Color>,
    +a: +List<Nat>) -> Nat:
  NodeCost.maybe_depth(Tree.lookup(fb, kids), a)

# `step` is exactly the depth of its child.
def NodeCost.step_is_depth(t: Tree.Tree, +a: +List<Nat>) ->
  {DepthProof.DepthProof.step(t, a) == Tree.depth(t, a) : Maybe<Nat>}:
  match t:
    case Tree.Node{+g, kids}:
      {==}

# The cost one candidate adds to the children of a node: zero when the
# candidate is the guess itself, otherwise the depth of its looked-up child.
def NodeCost.kid_cost(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>) -> Nat:
  Feedback.Bool.case(Nat, Feedback.word_eq(g, w), 0n,
    NodeCost.kid_depth(kids, Feedback.feedback(g, w), w))

# The total contribution of the children over a candidate list.
def NodeCost.kid_sum(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>) -> Nat:
  match S:
    case Nil{}:
      0n
    case Con{+w, +t}:
      Nat.add(NodeCost.kid_cost(g, kids, w), NodeCost.kid_sum(g, kids, t))

# The default of a looked-up child's depth is the sum of the child's depths.
def NodeCost.maybe_depth_default(m: Maybe<Tree.Tree>, +a: +List<Nat>) ->
  {NodeCost.maybe_depth(m, a) == Maybe.default(&1, Nat, DepthProof.DepthProof.lookup_depth(m, a), 0n)
   : Nat}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      Equal.sym(Nat, Maybe.default(&1, Nat, DepthProof.DepthProof.step(t, a), 0n),
                Maybe.default(&1, Nat, Tree.depth(t, a), 0n),
                Equal.cong(Maybe<Nat>, Nat, x => Maybe.default(&1, Nat, x, 0n),
                           DepthProof.DepthProof.step(t, a), Tree.depth(t, a),
                           NodeCost.step_is_depth(t, a)))

# A bump adds one to the default of its argument, when the argument exists.
def NodeCost.default_bump(m: Maybe<Nat>,
    s: {Maybe.is_some(&1, Nat, Tree.depth.bump(m)) == True{} : Bool}) ->
  {Maybe.default(&1, Nat, Tree.depth.bump(m), 0n)
   == Nat.add(1n, Maybe.default(&1, Nat, m, 0n)) : Nat}:
  match m:
    case None{}:
      Empty.absurd(
        {Maybe.default(&1, Nat, Tree.depth.bump(None{}), 0n)
         == Nat.add(1n, Maybe.default(&1, Nat, None{}, 0n)) : Nat},
        Logic.Proof.false_ne_true(s))
    case Some{n}:
      {==}

# The depth of a node written so that the equality decision is a parameter,
# which lets the proof case split on it (a computed Bool cannot be matched).
def NodeCost.node_depth_of(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    b: Bool) -> Maybe<Nat>:
  Feedback.Bool.case(Maybe<Nat>, b, Some{1n},
    Tree.depth.bump(Tree.depth.go(kids, Feedback.feedback(g, w), w)))

def NodeCost.kid_cost_of(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    b: Bool) -> Nat:
  Feedback.Bool.case(Nat, b, 0n,
    NodeCost.maybe_depth(Tree.lookup(Feedback.feedback(g, w), kids), w))

def NodeCost.depth_step_bool(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    b: Bool,
    s: {Maybe.is_some(&1, Nat, NodeCost.node_depth_of(g, kids, w, b)) == True{} : Bool}) ->
  {Maybe.default(&1, Nat, NodeCost.node_depth_of(g, kids, w, b), 0n)
   == Nat.add(1n, NodeCost.kid_cost_of(g, kids, w, b)) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      +fb : +List<Feedback.Color> = Feedback.feedback(g, w)
      e_lookup : {Tree.depth.go(kids, fb, w)
                  == DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w) : Maybe<Nat>} =
        DepthProof.DepthProof.depth_go_lookup(kids, fb, w)
      e_bump : {Maybe.default(&1, Nat, Tree.depth.bump(Tree.depth.go(kids, fb, w)), 0n)
                == Nat.add(1n, Maybe.default(&1, Nat, Tree.depth.go(kids, fb, w), 0n)) : Nat} =
        NodeCost.default_bump(Tree.depth.go(kids, fb, w), s)
      e_go : {Maybe.default(&1, Nat, Tree.depth.go(kids, fb, w), 0n)
              == Maybe.default(&1, Nat,
                   DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w), 0n) : Nat} =
        Equal.cong(Maybe<Nat>, Nat, x => Maybe.default(&1, Nat, x, 0n),
                   Tree.depth.go(kids, fb, w),
                   DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w), e_lookup)
      e_kid : {Maybe.default(&1, Nat,
                  DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w), 0n)
               == NodeCost.maybe_depth(Tree.lookup(fb, kids), w) : Nat} =
        Equal.sym(Nat, NodeCost.maybe_depth(Tree.lookup(fb, kids), w),
                  Maybe.default(&1, Nat,
                    DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w), 0n),
                  NodeCost.maybe_depth_default(Tree.lookup(fb, kids), w))
      Equal.trans(Nat,
                  Maybe.default(&1, Nat, Tree.depth.bump(Tree.depth.go(kids, fb, w)), 0n),
                  Nat.add(1n, Maybe.default(&1, Nat, Tree.depth.go(kids, fb, w), 0n)),
                  Nat.add(1n, NodeCost.maybe_depth(Tree.lookup(fb, kids), w)), e_bump,
                  Equal.trans(Nat,
                              Nat.add(1n, Maybe.default(&1, Nat, Tree.depth.go(kids, fb, w), 0n)),
                              Nat.add(1n, Maybe.default(&1, Nat,
                                DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w), 0n)),
                              Nat.add(1n, NodeCost.maybe_depth(Tree.lookup(fb, kids), w)),
                              Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                                         Maybe.default(&1, Nat, Tree.depth.go(kids, fb, w), 0n),
                                         Maybe.default(&1, Nat,
                                           DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w), 0n),
                                         e_go),
                              Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                                         Maybe.default(&1, Nat,
                                           DepthProof.DepthProof.lookup_depth(Tree.lookup(fb, kids), w), 0n),
                                         NodeCost.maybe_depth(Tree.lookup(fb, kids), w), e_kid)))

# The depth of one candidate at a node is one plus the cost of its child.
def NodeCost.depth_step(+g: +List<Nat>, +kids: +List<Tree.Child>, +w: +List<Nat>,
    s: {Maybe.is_some(&1, Nat, Tree.depth(Tree.Node{g, kids}, w)) == True{} : Bool}) ->
  {Maybe.default(&1, Nat, Tree.depth(Tree.Node{g, kids}, w), 0n)
   == Nat.add(1n, NodeCost.kid_cost(g, kids, w)) : Nat}:
  NodeCost.depth_step_bool(g, kids, w, Feedback.word_eq(g, w), s)

# Cost of a node on a valid candidate list: one guess per candidate plus the
# children's contributions.
def NodeCost.cost_node(+g: +List<Nat>, +kids: +List<Tree.Child>, +S: +List<+List<Nat>>,
    v: Tree.AllHaveDepth(Tree.Node{g, kids}, S)) ->
  {Tree.cost(Tree.Node{g, kids}, S)
   == Nat.add(List.length(&2, +List<Nat>, S), NodeCost.kid_sum(g, kids, S)) : Nat}:
  match S:
    case Nil{}:
      {==}
    case Con{h, t}:
      (sh, st) = v
      +ih : {Tree.cost(Tree.Node{g, kids}, t)
             == Nat.add(List.length(&2, +List<Nat>, t), NodeCost.kid_sum(g, kids, t)) : Nat} =
        NodeCost.cost_node(g, kids, t, st)
      +es : {Maybe.default(&1, Nat, Tree.depth(Tree.Node{g, kids}, h), 0n)
             == Nat.add(1n, NodeCost.kid_cost(g, kids, h)) : Nat} =
        NodeCost.depth_step(g, kids, h, sh)
      +d : Nat = Maybe.default(&1, Nat, Tree.depth(Tree.Node{g, kids}, h), 0n)
      +lt : Nat = List.length(&2, +List<Nat>, t)
      +ks : Nat = NodeCost.kid_sum(g, kids, t)
      +kw : Nat = NodeCost.kid_cost(g, kids, h)
      +e_ih : {Nat.add(d, Tree.cost(Tree.Node{g, kids}, t))
               == Nat.add(d, Nat.add(lt, ks)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(d, x),
                   Tree.cost(Tree.Node{g, kids}, t), Nat.add(lt, ks), ih)
      +e_d : {Nat.add(d, Nat.add(lt, ks))
              == Nat.add(Nat.add(1n, kw), Nat.add(lt, ks)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(x, Nat.add(lt, ks)),
                   d, Nat.add(1n, kw), es)
      +e_regroup : {Nat.add(Nat.add(1n, kw), Nat.add(lt, ks))
                    == Nat.add(Nat.add(1n, lt), Nat.add(kw, ks)) : Nat} =
        NatProof.NatPrf.add4(1n, kw, lt, ks)
      Equal.trans(Nat, Nat.add(d, Tree.cost(Tree.Node{g, kids}, t)),
                  Nat.add(d, Nat.add(lt, ks)),
                  Nat.add(Nat.add(1n, lt), Nat.add(kw, ks)), e_ih,
                  Equal.trans(Nat, Nat.add(d, Nat.add(lt, ks)),
                              Nat.add(Nat.add(1n, kw), Nat.add(lt, ks)),
                              Nat.add(Nat.add(1n, lt), Nat.add(kw, ks)),
                              e_d, e_regroup))

# A `Maybe` that is `Some` is the `Some` of its value.
def MaybePrf.some_of_is_some(-A: Type, m: Maybe<A>,
    s: {Maybe.is_some(&1, A, m) == True{} : Bool}) ->
  &x: A -> {m == Some{x} : Maybe<A>}:
  match m:
    case None{}:
      Empty.absurd(&x: A -> {None{} == Some{x} : Maybe<A>},
                   Logic.Proof.false_ne_true(s))
    case Some{x}:
      (x, {==})
