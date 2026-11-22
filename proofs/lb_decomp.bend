# Lower bounds for valid trees, part 6: the cost of a node splits over its
# classes.
#
# A node's cost over a candidate list is one per candidate plus the children's
# depth contributions (`nodecost.bend`). The first-match partition of
# `lb_classes.bend` groups the candidates by the child that reaches them, so the
# children's contribution is the sum of the class costs:
#
#   cost(Node(g, kids), S) >= |S| + sum over the classes of cost(child, words)
#
# The inequality is what a pruning rule needs: each class cost can then be
# bounded on its own, for instance by the depth-two bound of `lb_twice.bend` or
# by the capacity bound. It is an inequality because the words no child takes
# contribute nothing to the right-hand side while costing at least zero on the
# left.
#
# The per-class step needs two facts: every word of a class is a non-guess word
# with the child's feedback, which the filter guarantees, and the child the
# child list looks up for that feedback is the class's own child.
import Base
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ../src/groups.bend as Groups
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./feedback.bend as FbProof
import ./nodecost.bend as NodeCost
import ./classbound_nat.bend as CB
import ./lb_classes.bend as Part

# The kept words are non-guess words with the child's feedback.
def LB.KeepFacts(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>) -> Type:
  match ws:
    case Nil{}:
      Unit
    case Con{h, t}:
      {Feedback.word_eq(g, h) == False{} : Bool}
      & {Feedback.feedback_eq(f, Feedback.feedback(g, h)) == True{} : Bool}
      & LB.KeepFacts(g, f, t)

# The two comparisons behind a true keep test.
def LB.keep_true_l(bw: Bool, bf: Bool,
    e: {Part.LB.keepb(bw, bf) == True{} : Bool}) -> {bw == False{} : Bool}:
  match bw:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, Logic.Proof.false_ne_true(e))
    case False{}:
      {==}

def LB.keep_true_r(bw: Bool, bf: Bool,
    e: {Part.LB.keepb(bw, bf) == True{} : Bool}) -> {bf == True{} : Bool}:
  match bw:
    case True{}:
      Empty.absurd({bf == True{} : Bool}, Logic.Proof.false_ne_true(e))
    case False{}:
      e

# The kept words carry the class facts, with the keep test as a parameter.
def LB.keep_facts_go(+g: +List<Nat>, +f: +List<Feedback.Color>, +h: +List<Nat>,
    +t: +List<+List<Nat>>, b: Bool, +eb: {b == Part.LB.keep(g, f, h) : Bool},
    ih: LB.KeepFacts(g, f, Part.LB.keepw_b(g, f, t))) ->
  LB.KeepFacts(g, f, Part.LB.keepw_of(g, f, h, t, b)):
  match b:
    case True{}:
      +kt : {Part.LB.keep(g, f, h) == True{} : Bool} =
        Equal.sym(Bool, b, Part.LB.keep(g, f, h), eb)
      +bw : {Feedback.word_eq(g, h) == False{} : Bool} =
        LB.keep_true_l(Feedback.word_eq(g, h),
          Feedback.feedback_eq(f, Feedback.feedback(g, h)), kt)
      +bf : {Feedback.feedback_eq(f, Feedback.feedback(g, h)) == True{} : Bool} =
        LB.keep_true_r(Feedback.word_eq(g, h),
          Feedback.feedback_eq(f, Feedback.feedback(g, h)), kt)
      (bw, (bf, ih))
    case False{}:
      ih

# Transport the per-word class facts along an equality of word lists.
def LB.keepfacts_eq(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +ws1: +List<+List<Nat>>, +ws2: +List<+List<Nat>>,
    e: {ws1 == ws2 : +List<+List<Nat>>}, p: LB.KeepFacts(g, f, ws1)) ->
  LB.KeepFacts(g, f, ws2):
  %e : LB.KeepFacts(g, f, _)
  p

# Every kept word is a non-guess word with the child's feedback.
def LB.keep_facts(+g: +List<Nat>, +f: +List<Feedback.Color>,
    +S: +List<+List<Nat>>) -> LB.KeepFacts(g, f, Part.LB.keepw_b(g, f, S)):
  match S:
    case Nil{}:
      Unit{}
    case Con{h, t}:
      +b : Bool = Part.LB.keep(g, f, h)
      core : LB.KeepFacts(g, f, Part.LB.keepw_of(g, f, h, t, b)) =
        LB.keep_facts_go(g, f, h, t, b, {==}, LB.keep_facts(g, f, t))
      +eq : {Part.LB.keepw_of(g, f, h, t, b) == Part.LB.keepw_b(g, f, h <> t)
             : +List<+List<Nat>>} =
        Equal.sym(+List<+List<Nat>>, Part.LB.keepw_b(g, f, h <> t),
          Part.LB.keepw_of(g, f, h, t, b), Part.LB.keepw_eq(g, f, h, t, b, {==}))
      LB.keepfacts_eq(g, f, Part.LB.keepw_of(g, f, h, t, b),
        Part.LB.keepw_b(g, f, h <> t), eq, core)

# A true feedback comparison gives the equal feedback patterns.
def LB.fb_eq(+f: +List<Feedback.Color>, +h: +List<Nat>, +g: +List<Nat>,
    fe: {Feedback.feedback_eq(f, Feedback.feedback(g, h)) == True{} : Bool}) ->
  {Feedback.feedback(g, h) == f : +List<Feedback.Color>}:
  Equal.sym(+List<Feedback.Color>, f, Feedback.feedback(g, h),
    FbProof.FbPrf.feedback_eq_true(f, Feedback.feedback(g, h), fe))

# One candidate's contribution is the depth in its class's child.
def LB.kid_cost_at(+g: +List<Nat>, +kids: +List<Tree.Child>, +f: +List<Feedback.Color>,
    +h: +List<Nat>, +t: Tree.Tree,
    ne: {Feedback.word_eq(g, h) == False{} : Bool},
    fe: {Feedback.feedback_eq(f, Feedback.feedback(g, h)) == True{} : Bool},
    +lk: {Tree.lookup(f, kids) == Some{t} : Maybe<&1, Tree.Tree>}) ->
  {NodeCost.NodeCost.kid_cost(g, kids, h)
   == Maybe.default(&1, Nat, Tree.depth(t, h), 0n) : Nat}:
  +e_kid : {NodeCost.NodeCost.kid_cost(g, kids, h)
            == NodeCost.NodeCost.maybe_depth(
                 Tree.lookup(Feedback.feedback(g, h), kids), h) : Nat} =
    Equal.cong(Bool, Nat,
      x => Feedback.Bool.case(Nat, x, 0n,
             NodeCost.NodeCost.maybe_depth(
               Tree.lookup(Feedback.feedback(g, h), kids), h)),
      Feedback.word_eq(g, h), False{}, ne)
  +e_f : {Feedback.feedback(g, h) == f : +List<Feedback.Color>} =
    LB.fb_eq(f, h, g, fe)
  +e_lk : {Tree.lookup(Feedback.feedback(g, h), kids) == Tree.lookup(f, kids)
           : Maybe<&1, Tree.Tree>} =
    Equal.cong(+List<Feedback.Color>, Maybe<Tree.Tree>, x => Tree.lookup(x, kids),
      Feedback.feedback(g, h), f, e_f)
  Equal.trans(Nat, NodeCost.NodeCost.kid_cost(g, kids, h),
    NodeCost.NodeCost.maybe_depth(Tree.lookup(Feedback.feedback(g, h), kids), h),
    Maybe.default(&1, Nat, Tree.depth(t, h), 0n), e_kid,
    Equal.trans(Nat,
      NodeCost.NodeCost.maybe_depth(Tree.lookup(Feedback.feedback(g, h), kids), h),
      NodeCost.NodeCost.maybe_depth(Tree.lookup(f, kids), h),
      Maybe.default(&1, Nat, Tree.depth(t, h), 0n),
      Equal.cong(Maybe<Tree.Tree>, Nat,
        x => NodeCost.NodeCost.maybe_depth(x, h),
        Tree.lookup(Feedback.feedback(g, h), kids), Tree.lookup(f, kids), e_lk),
      Equal.trans(Nat, NodeCost.NodeCost.maybe_depth(Tree.lookup(f, kids), h),
        NodeCost.NodeCost.maybe_depth(Some{t}, h),
        Maybe.default(&1, Nat, Tree.depth(t, h), 0n),
        Equal.cong(Maybe<Tree.Tree>, Nat,
          x => NodeCost.NodeCost.maybe_depth(x, h), Tree.lookup(f, kids),
          Some{t}, lk),
        {==})))

# The class's child contribution over the whole class.
def LB.class_cost(+g: +List<Nat>, +kids: +List<Tree.Child>, +f: +List<Feedback.Color>,
    +t: Tree.Tree, +ws: +List<+List<Nat>>,
    +lk: {Tree.lookup(f, kids) == Some{t} : Maybe<&1, Tree.Tree>},
    facts: LB.KeepFacts(g, f, ws)) ->
  {NodeCost.NodeCost.kid_sum(g, kids, ws) == Tree.cost(t, ws) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, tl}:
      (ne_h, rest) = facts
      (fe_h, facts_tl) = rest
      +ih : {NodeCost.NodeCost.kid_sum(g, kids, tl) == Tree.cost(t, tl) : Nat} =
        LB.class_cost(g, kids, f, t, tl, lk, facts_tl)
      +e_h : {NodeCost.NodeCost.kid_cost(g, kids, h)
              == Maybe.default(&1, Nat, Tree.depth(t, h), 0n) : Nat} =
        LB.kid_cost_at(g, kids, f, h, t, ne_h, fe_h, lk)
      +e_sum : {NodeCost.NodeCost.kid_sum(g, kids, h <> tl)
                == Nat.add(Maybe.default(&1, Nat, Tree.depth(t, h), 0n),
                           NodeCost.NodeCost.kid_sum(g, kids, tl)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(x, NodeCost.NodeCost.kid_sum(g, kids, tl)),
          NodeCost.NodeCost.kid_cost(g, kids, h),
          Maybe.default(&1, Nat, Tree.depth(t, h), 0n), e_h)
      Equal.trans(Nat, NodeCost.NodeCost.kid_sum(g, kids, h <> tl),
        Nat.add(Maybe.default(&1, Nat, Tree.depth(t, h), 0n),
                NodeCost.NodeCost.kid_sum(g, kids, tl)),
        Tree.cost(t, h <> tl), e_sum,
        Equal.trans(Nat,
          Nat.add(Maybe.default(&1, Nat, Tree.depth(t, h), 0n),
                  NodeCost.NodeCost.kid_sum(g, kids, tl)),
          Nat.add(Maybe.default(&1, Nat, Tree.depth(t, h), 0n), Tree.cost(t, tl)),
          Tree.cost(t, h <> tl),
          Equal.cong(Nat, Nat,
            x => Nat.add(Maybe.default(&1, Nat, Tree.depth(t, h), 0n), x),
            NodeCost.NodeCost.kid_sum(g, kids, tl), Tree.cost(t, tl), ih),
          {==}))

# The class costs of a class list.
def LB.clsCost(+cls: +List<Part.LB.Class>) -> Nat:
  match cls:
    case Nil{}:
      0n
    case Con{c, rest}:
      match c:
        case Part.LClass{t, ws}:
          Nat.add(Tree.cost(t, ws), LB.clsCost(rest))

# The children's own contribution, class by class.
def LB.clsCostOf(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +cls: +List<Part.LB.Class>) -> Nat:
  match cls:
    case Nil{}:
      0n
    case Con{c, rest}:
      match c:
        case Part.LClass{t, ws}:
          Nat.add(NodeCost.NodeCost.kid_sum(g, kids, ws),
                  LB.clsCostOf(g, kids, rest))

# A word's contribution splits over the two filters.
def LB.kid_sum_go(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +f: +List<Feedback.Color>,
    +h: +List<Nat>, +t: +List<+List<Nat>>, b: Bool,
    +eb: {b == Part.LB.keep(g, f, h) : Bool},
    ih: {NodeCost.NodeCost.kid_sum(g, kids, t)
         == Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                    NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t))) : Nat}) ->
  {NodeCost.NodeCost.kid_sum(g, kids, h <> t)
   == Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_of(g, f, h, t, b)),
              NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw_of(g, f, h, t, b))) : Nat}:
  match b:
    case True{}:
      +e1 : {NodeCost.NodeCost.kid_sum(g, kids, h <> t)
             == Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                        NodeCost.NodeCost.kid_sum(g, kids, t)) : Nat} =
        {==}
      +e2 : {Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                     NodeCost.NodeCost.kid_sum(g, kids, t))
             == Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                        Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                                NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t)))) : Nat} =
        Equal.cong(Nat, Nat,
          x => Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h), x),
          NodeCost.NodeCost.kid_sum(g, kids, t),
          Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                  NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t))), ih)
      +e3 : {Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                     Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                             NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t))))
             == Nat.add(Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                                NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t))),
                        NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t))) : Nat} =
        Equal.sym(Nat,
          Nat.add(Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                          NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t))),
                  NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t))),
          Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                  Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                          NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t)))),
          NatProof.NatPrf.add_assoc(NodeCost.NodeCost.kid_cost(g, kids, h),
            NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
            NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t))))
      Equal.trans(Nat, NodeCost.NodeCost.kid_sum(g, kids, h <> t),
        Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                NodeCost.NodeCost.kid_sum(g, kids, t)),
        Nat.add(Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                        NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t))),
                NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t))),
        e1, Equal.trans(Nat,
          Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                  NodeCost.NodeCost.kid_sum(g, kids, t)),
          Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                  Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                          NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t)))),
          Nat.add(Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                          NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t))),
                  NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t))),
          e2, e3))
    case False{}:
      +e1 : {NodeCost.NodeCost.kid_sum(g, kids, h <> t)
             == Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                        NodeCost.NodeCost.kid_sum(g, kids, t)) : Nat} =
        {==}
      +e2 : {Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                     NodeCost.NodeCost.kid_sum(g, kids, t))
             == Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                        Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                                NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t)))) : Nat} =
        Equal.cong(Nat, Nat,
          x => Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h), x),
          NodeCost.NodeCost.kid_sum(g, kids, t),
          Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                  NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t))), ih)
      +e3 : {Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                     Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                             NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t))))
             == Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                        Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                                NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t)))) : Nat} =
        Equal.trans(Nat,
          Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                  Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                          NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t)))),
          Nat.add(Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                          NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t))),
                  NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t))),
          Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                  Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                          NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t)))),
          Equal.sym(Nat,
            Nat.add(Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                            NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t))),
                    NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t))),
            Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                    Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                            NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t)))),
            NatProof.NatPrf.add_assoc(NodeCost.NodeCost.kid_cost(g, kids, h),
              NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
              NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t)))),
          Equal.trans(Nat,
            Nat.add(Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                            NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t))),
                    NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t))),
            Nat.add(Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                            NodeCost.NodeCost.kid_cost(g, kids, h)),
                    NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t))),
            Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                    Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                            NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t)))),
            Equal.cong(Nat, Nat,
              x => Nat.add(x, NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t))),
              Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                      NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t))),
              Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                      NodeCost.NodeCost.kid_cost(g, kids, h)),
              NatProof.NatPrf.add_comm(NodeCost.NodeCost.kid_cost(g, kids, h),
                NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)))),
            NatProof.NatPrf.add_assoc(
              NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
              NodeCost.NodeCost.kid_cost(g, kids, h),
              NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t)))))
      Equal.trans(Nat, NodeCost.NodeCost.kid_sum(g, kids, h <> t),
        Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                NodeCost.NodeCost.kid_sum(g, kids, t)),
        Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                        NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t)))),
        e1, Equal.trans(Nat,
          Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                  NodeCost.NodeCost.kid_sum(g, kids, t)),
          Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                  Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                          NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t)))),
          Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, t)),
                  Nat.add(NodeCost.NodeCost.kid_cost(g, kids, h),
                          NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, t)))),
          e2, e3))

# A word's contribution splits over the two filters.
def LB.kid_sum_split(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +f: +List<Feedback.Color>, +S: +List<+List<Nat>>) ->
  {NodeCost.NodeCost.kid_sum(g, kids, S)
   == Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, S)),
              NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, S))) : Nat}:
  match S:
    case Nil{}:
      {==}
    case Con{h, t}:
      +b : Bool = Part.LB.keep(g, f, h)
      +core : {NodeCost.NodeCost.kid_sum(g, kids, h <> t)
               == Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_of(g, f, h, t, b)),
                          NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw_of(g, f, h, t, b))) : Nat} =
        LB.kid_sum_go(g, kids, f, h, t, b, {==}, LB.kid_sum_split(g, kids, f, t))
      +ek : {Part.LB.keepw_b(g, f, h <> t) == Part.LB.keepw_of(g, f, h, t, b)
             : +List<+List<Nat>>} =
        Part.LB.keepw_eq(g, f, h, t, b, {==})
      +er : {Part.LB.remw(g, f, h <> t) == Part.LB.remw_of(g, f, h, t, b)
             : +List<+List<Nat>>} =
        Part.LB.remw_eq(g, f, h, t, b, {==})
      %Equal.sym(+List<+List<Nat>>, Part.LB.keepw_of(g, f, h, t, b),
                 Part.LB.keepw_b(g, f, h <> t), ek) :
        {NodeCost.NodeCost.kid_sum(g, kids, h <> t)
         == Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, h <> t)),
                    NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw_of(g, f, h, t, b))) : Nat}
      %Equal.sym(+List<+List<Nat>>, Part.LB.remw_of(g, f, h, t, b),
                 Part.LB.remw(g, f, h <> t), er) :
        {NodeCost.NodeCost.kid_sum(g, kids, h <> t)
         == Nat.add(NodeCost.NodeCost.kid_sum(g, kids, Part.LB.keepw_b(g, f, h <> t)),
                    NodeCost.NodeCost.kid_sum(g, kids, Part.LB.remw(g, f, h <> t))) : Nat}
      core

# The partition of the children's contribution over the classes.
def LB.kid_sum_classes(+g: +List<Nat>, +kids0: +List<Tree.Child>,
    +kids: +List<Tree.Child>, +S: +List<+List<Nat>>) ->
  {NodeCost.NodeCost.kid_sum(g, kids0, S)
   == Nat.add(LB.clsCostOf(g, kids0, Part.LB.classes(g, kids, S)),
              NodeCost.NodeCost.kid_sum(g, kids0, Part.LB.rem(g, kids, S))) : Nat}:
  match kids:
    case Nil{}:
      {==}
    case Con{c, rest}:
      match c:
        case Tree.Child{f, t}:
          +sp : {NodeCost.NodeCost.kid_sum(g, kids0, S)
                 == Nat.add(NodeCost.NodeCost.kid_sum(g, kids0, Part.LB.keepw_b(g, f, S)),
                            NodeCost.NodeCost.kid_sum(g, kids0, Part.LB.remw(g, f, S))) : Nat} =
            LB.kid_sum_split(g, kids0, f, S)
          +ih : {NodeCost.NodeCost.kid_sum(g, kids0, Part.LB.remw(g, f, S))
                 == Nat.add(LB.clsCostOf(g, kids0,
                              Part.LB.classes(g, rest, Part.LB.remw(g, f, S))),
                            NodeCost.NodeCost.kid_sum(g, kids0,
                              Part.LB.rem(g, rest, Part.LB.remw(g, f, S)))) : Nat} =
            LB.kid_sum_classes(g, kids0, rest, Part.LB.remw(g, f, S))
          +a : Nat = NodeCost.NodeCost.kid_sum(g, kids0, Part.LB.keepw_b(g, f, S))
          +b : Nat = NodeCost.NodeCost.kid_sum(g, kids0, Part.LB.remw(g, f, S))
          +c : Nat = LB.clsCostOf(g, kids0, Part.LB.classes(g, rest, Part.LB.remw(g, f, S)))
          +d : Nat = NodeCost.NodeCost.kid_sum(g, kids0,
                       Part.LB.rem(g, rest, Part.LB.remw(g, f, S)))
          +e1 : {NodeCost.NodeCost.kid_sum(g, kids0, S) == Nat.add(a, b) : Nat} = sp
          +e2 : {Nat.add(a, b) == Nat.add(a, Nat.add(c, d)) : Nat} =
            Equal.cong(Nat, Nat, x => Nat.add(a, x), b, Nat.add(c, d), ih)
          +e3 : {Nat.add(a, Nat.add(c, d)) == Nat.add(Nat.add(a, c), d) : Nat} =
            Equal.sym(Nat, Nat.add(Nat.add(a, c), d), Nat.add(a, Nat.add(c, d)),
              NatProof.NatPrf.add_assoc(a, c, d))
          Equal.trans(Nat, NodeCost.NodeCost.kid_sum(g, kids0, S), Nat.add(a, b),
            Nat.add(Nat.add(a, c), d), e1, Equal.trans(Nat, Nat.add(a, b),
              Nat.add(a, Nat.add(c, d)), Nat.add(Nat.add(a, c), d), e2, e3))

# The per-class conditions the sum comparison needs.
def LB.ClsConds(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +cls: +List<Part.LB.Class>) -> Type:
  match cls:
    case Nil{}:
      Unit
    case Con{c, rest}:
      match c:
        case Part.LClass{t, ws}:
          {NodeCost.NodeCost.kid_sum(g, kids, ws) == Tree.cost(t, ws) : Nat}
          & LB.ClsConds(g, kids, rest)

# The children's contribution is the sum of the class costs.
def LB.clsCostOf_eq(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +cls: +List<Part.LB.Class>, c: LB.ClsConds(g, kids, cls)) ->
  {LB.clsCostOf(g, kids, cls) == LB.clsCost(cls) : Nat}:
  match cls:
    case Nil{}:
      {==}
    case Con{hd, rest}:
      match hd:
        case Part.LClass{t, ws}:
          (ch, ct) = c
          +ih : {LB.clsCostOf(g, kids, rest) == LB.clsCost(rest) : Nat} =
            LB.clsCostOf_eq(g, kids, rest, ct)
          +e1 : {Nat.add(NodeCost.NodeCost.kid_sum(g, kids, ws), LB.clsCostOf(g, kids, rest))
                 == Nat.add(Tree.cost(t, ws), LB.clsCostOf(g, kids, rest)) : Nat} =
            Equal.cong(Nat, Nat, x => Nat.add(x, LB.clsCostOf(g, kids, rest)),
              NodeCost.NodeCost.kid_sum(g, kids, ws), Tree.cost(t, ws), ch)
          +e2 : {Nat.add(Tree.cost(t, ws), LB.clsCostOf(g, kids, rest))
                 == Nat.add(Tree.cost(t, ws), LB.clsCost(rest)) : Nat} =
            Equal.cong(Nat, Nat, x => Nat.add(Tree.cost(t, ws), x),
              LB.clsCostOf(g, kids, rest), LB.clsCost(rest), ih)
          Equal.trans(Nat,
            Nat.add(NodeCost.NodeCost.kid_sum(g, kids, ws), LB.clsCostOf(g, kids, rest)),
            Nat.add(Tree.cost(t, ws), LB.clsCostOf(g, kids, rest)),
            Nat.add(Tree.cost(t, ws), LB.clsCost(rest)), e1, e2)

# A node's cost is its candidate count plus the class costs at least.
def LB.node_cost_ge(+g: +List<Nat>, +kids: +List<Tree.Child>,
    +S: +List<+List<Nat>>, ad: Tree.AllHaveDepth(Tree.Node{g, kids}, S),
    c: LB.ClsConds(g, kids, Part.LB.classes(g, kids, S))) ->
  {Nat.is_le(Nat.add(List.length(&2, +List<Nat>, S),
                     LB.clsCost(Part.LB.classes(g, kids, S))),
             Tree.cost(Tree.Node{g, kids}, S)) == True{} : Bool}:
  +n : Nat = List.length(&2, +List<Nat>, S)
  +kr : Nat = NodeCost.NodeCost.kid_sum(g, kids, Part.LB.rem(g, kids, S))
  +co : Nat = LB.clsCostOf(g, kids, Part.LB.classes(g, kids, S))
  +cl : Nat = LB.clsCost(Part.LB.classes(g, kids, S))
  +cn : {Tree.cost(Tree.Node{g, kids}, S)
         == Nat.add(n, NodeCost.NodeCost.kid_sum(g, kids, S)) : Nat} =
    NodeCost.NodeCost.cost_node(g, kids, S, ad)
  +part : {NodeCost.NodeCost.kid_sum(g, kids, S) == Nat.add(co, kr) : Nat} =
    LB.kid_sum_classes(g, kids, kids, S)
  +cc : {co == cl : Nat} =
    LB.clsCostOf_eq(g, kids, Part.LB.classes(g, kids, S), c)
  +e_a : {Tree.cost(Tree.Node{g, kids}, S) == Nat.add(n, Nat.add(co, kr)) : Nat} =
    Equal.trans(Nat, Tree.cost(Tree.Node{g, kids}, S),
      Nat.add(n, NodeCost.NodeCost.kid_sum(g, kids, S)),
      Nat.add(n, Nat.add(co, kr)), cn,
      Equal.cong(Nat, Nat, x => Nat.add(n, x),
        NodeCost.NodeCost.kid_sum(g, kids, S), Nat.add(co, kr), part))
  +e_b : {Nat.add(n, Nat.add(co, kr)) == Nat.add(Nat.add(n, co), kr) : Nat} =
    Equal.sym(Nat, Nat.add(Nat.add(n, co), kr), Nat.add(n, Nat.add(co, kr)),
      NatProof.NatPrf.add_assoc(n, co, kr))
  +le_self : {Nat.is_le(Nat.add(n, co), Nat.add(Nat.add(n, co), kr)) == True{} : Bool} =
    CB.CB.is_le_add_self_r(Nat.add(n, co), kr)
  +le_mid : {Nat.is_le(Nat.add(n, co), Tree.cost(Tree.Node{g, kids}, S)) == True{} : Bool} =
    NatProof.Nat.is_le_eq_r(Nat.add(n, co), Nat.add(Nat.add(n, co), kr),
      Tree.cost(Tree.Node{g, kids}, S),
      Equal.sym(Nat, Tree.cost(Tree.Node{g, kids}, S), Nat.add(Nat.add(n, co), kr),
        Equal.trans(Nat, Tree.cost(Tree.Node{g, kids}, S), Nat.add(n, Nat.add(co, kr)),
          Nat.add(Nat.add(n, co), kr), e_a, e_b)),
      le_self)
  +e_n : {Nat.add(n, co) == Nat.add(n, cl) : Nat} =
    Equal.cong(Nat, Nat, x => Nat.add(n, x), co, cl, cc)
  NatProof.Nat.is_le_eq_l(Tree.cost(Tree.Node{g, kids}, S), Nat.add(n, co),
    Nat.add(n, cl), e_n, le_mid)

# The root guess of a tree.
def LB.guessOf(t: Tree.Tree) -> +List<Nat>:
  match t:
    case Tree.Node{g, kids}:
      g

# The children of a tree.
def LB.kidsOf(t: Tree.Tree) -> +List<Tree.Child>:
  match t:
    case Tree.Node{g, kids}:
      kids

# The same bound for a tree, naming its root guess and children.
def LB.cost_ge_classes(t: Tree.Tree, +S: +List<+List<Nat>>,
    ad: Tree.AllHaveDepth(t, S),
    c: LB.ClsConds(LB.guessOf(t), LB.kidsOf(t),
         Part.LB.classes(LB.guessOf(t), LB.kidsOf(t), S))) ->
  {Nat.is_le(Nat.add(List.length(&2, +List<Nat>, S),
                     LB.clsCost(Part.LB.classes(LB.guessOf(t), LB.kidsOf(t), S))),
             Tree.cost(t, S)) == True{} : Bool}:
  match t:
    case Tree.Node{g, kids}:
      LB.node_cost_ge(g, kids, S, ad, c)
