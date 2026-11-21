# The partition arithmetic of the feedback classes.
#
# `groups_build` splits a candidate list `S` for a guess `g`. The classes are
# nonempty and disjoint, and every candidate whose word differs from `g` lies in
# exactly one of them, so the sizes of the classes sum to at most `|S|`. That is
# the `part` hypothesis of `CB.bound`: with a cost bound `c <= m*m` per class,
# the node cost `|S| + sum c` fits `|S|*|S|`, hence the solver's infinity.
#
# The module also states that arithmetic over an actual group list and its
# per-class costs (`CB.PointLeG`, `CB.Bounds`) and assembles the below-infinity
# bound `CB.fits_inf`.
import Base
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./classbound_nat.bend as CBN

# `length (ws ++ [w]) = length ws + 1`, for a class.
def CB.len_words_append_single(+ws: +List<+List<Nat>>, +w: +List<Nat>) ->
  {Groups.len_words(List.append(&2, +List<Nat>, ws, w <> Nil{}))
   == Nat.add(Groups.len_words(ws), 1n) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case Con{h, t}:
      +ih : {Groups.len_words(List.append(&2, +List<Nat>, t, w <> Nil{}))
             == Nat.add(Groups.len_words(t), 1n) : Nat} =
        CB.len_words_append_single(t, w)
      +e1 : {Nat.add(1n, Groups.len_words(List.append(&2, +List<Nat>, t, w <> Nil{})))
             == Nat.add(1n, Nat.add(Groups.len_words(t), 1n)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                   Groups.len_words(List.append(&2, +List<Nat>, t, w <> Nil{})),
                   Nat.add(Groups.len_words(t), 1n), ih)
      +e2 : {Nat.add(1n, Nat.add(Groups.len_words(t), 1n))
             == Nat.add(Nat.add(1n, Groups.len_words(t)), 1n) : Nat} =
        Equal.sym(Nat, Nat.add(Nat.add(1n, Groups.len_words(t)), 1n),
                  Nat.add(1n, Nat.add(Groups.len_words(t), 1n)),
                  NatProof.NatPrf.add_assoc(1n, Groups.len_words(t), 1n))
      Equal.trans(Nat,
        Nat.add(1n, Groups.len_words(List.append(&2, +List<Nat>, t, w <> Nil{}))),
        Nat.add(1n, Nat.add(Groups.len_words(t), 1n)),
        Nat.add(Nat.add(1n, Groups.len_words(t)), 1n), e1, e2)

# The class sizes of a group list, in order.
def CB.sizes(+groups: +List<Groups.Group>) -> +List<Nat>:
  match groups:
    case Nil{}:
      Nil{}
    case Con{gp, gt}:
      match gp:
        case Groups.Group{f, ws}:
          Groups.len_words(ws) <> CB.sizes(gt)

# Cons of a size list, written out for the proofs.
def CB.size_of(gp: Groups.Group) -> Nat:
  match gp:
    case Groups.Group{f, ws}:
      Groups.len_words(ws)

# The words of `S` that are not the guess, and those that are.
def CB.keep(+g: +List<Nat>, +S: +List<+List<Nat>>) -> Nat:
  match S:
    case Nil{}:
      0n
    case Con{w, t}:
      Feedback.Bool.case(Nat, Feedback.word_eq(g, w), CB.keep(g, t),
                         Nat.add(1n, CB.keep(g, t)))

def CB.dropped(+g: +List<Nat>, +S: +List<+List<Nat>>) -> Nat:
  match S:
    case Nil{}:
      0n
    case Con{w, t}:
      Feedback.Bool.case(Nat, Feedback.word_eq(g, w), Nat.add(1n, CB.dropped(g, t)),
                         CB.dropped(g, t))

# The true and false branches of `keep`, as equalities.
def CB.keep_true(+g: +List<Nat>, +w: +List<Nat>, +t: +List<+List<Nat>>,
    +e: {Feedback.word_eq(g, w) == True{} : Bool}) ->
  {CB.keep(g, w <> t) == CB.keep(g, t) : Nat}:
  Equal.cong(Bool, Nat,
    x => Feedback.Bool.case(Nat, x, CB.keep(g, t), Nat.add(1n, CB.keep(g, t))),
    Feedback.word_eq(g, w), True{}, e)

def CB.keep_false(+g: +List<Nat>, +w: +List<Nat>, +t: +List<+List<Nat>>,
    +e: {Feedback.word_eq(g, w) == False{} : Bool}) ->
  {CB.keep(g, w <> t) == Nat.add(1n, CB.keep(g, t)) : Nat}:
  Equal.cong(Bool, Nat,
    x => Feedback.Bool.case(Nat, x, CB.keep(g, t), Nat.add(1n, CB.keep(g, t))),
    Feedback.word_eq(g, w), False{}, e)

# One head of `group_add`: the two branches, given the tail's induction.
def CB.sum_sizes_add_head(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +f: +List<Feedback.Color>, +ws: +List<+List<Nat>>,
    +rest: +List<Groups.Group>, b: Bool,
    +eb: {b == Feedback.feedback_eq(fb, f) : Bool},
    ih: {CBN.CB.sum(CB.sizes(Groups.group_add(w, fb, rest)))
         == Nat.add(CBN.CB.sum(CB.sizes(rest)), 1n) : Nat}) ->
  {CBN.CB.sum(CB.sizes(
     Feedback.Bool.case(+List<Groups.Group>, b,
       Groups.Group{f, List.append(&2, +List<Nat>, ws, w <> Nil{})} <> rest,
       Groups.Group{f, ws} <> Groups.group_add(w, fb, rest))))
   == Nat.add(CBN.CB.sum(CB.sizes(Groups.Group{f, ws} <> rest)), 1n) : Nat}:
  match b:
    case True{}:
      +s : Nat = CBN.CB.sum(CB.sizes(rest))
      +lw : Nat = Groups.len_words(ws)
      +e0 : {Nat.add(Groups.len_words(List.append(&2, +List<Nat>, ws, w <> Nil{})), s)
             == Nat.add(Nat.add(lw, 1n), s) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(x, s),
                   Groups.len_words(List.append(&2, +List<Nat>, ws, w <> Nil{})),
                   Nat.add(lw, 1n), CB.len_words_append_single(ws, w))
      +e1 : {Nat.add(Nat.add(lw, 1n), s)
             == Nat.add(lw, Nat.add(1n, s)) : Nat} =
        NatProof.NatPrf.add_assoc(lw, 1n, s)
      +e2a : {Nat.add(lw, Nat.add(1n, s)) == Nat.add(lw, Nat.add(s, 1n)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(lw, x), Nat.add(1n, s), Nat.add(s, 1n),
                   NatProof.NatPrf.add_comm(1n, s))
      +e2b : {Nat.add(lw, Nat.add(s, 1n)) == Nat.add(Nat.add(lw, s), 1n) : Nat} =
        Equal.sym(Nat, Nat.add(Nat.add(lw, s), 1n), Nat.add(lw, Nat.add(s, 1n)),
                  NatProof.NatPrf.add_assoc(lw, s, 1n))
      Equal.trans(Nat,
        Nat.add(Groups.len_words(List.append(&2, +List<Nat>, ws, w <> Nil{})), s),
        Nat.add(Nat.add(lw, 1n), s),
        Nat.add(Nat.add(lw, s), 1n), e0,
        Equal.trans(Nat, Nat.add(Nat.add(lw, 1n), s),
                    Nat.add(lw, Nat.add(1n, s)),
                    Nat.add(Nat.add(lw, s), 1n), e1,
                    Equal.trans(Nat, Nat.add(lw, Nat.add(1n, s)),
                                Nat.add(lw, Nat.add(s, 1n)),
                                Nat.add(Nat.add(lw, s), 1n), e2a, e2b)))
    case False{}:
      +s : Nat = CBN.CB.sum(CB.sizes(rest))
      +e1 : {Nat.add(Groups.len_words(ws), CBN.CB.sum(CB.sizes(Groups.group_add(w, fb, rest))))
             == Nat.add(Groups.len_words(ws), Nat.add(s, 1n)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(Groups.len_words(ws), x),
                   CBN.CB.sum(CB.sizes(Groups.group_add(w, fb, rest))),
                   Nat.add(s, 1n), ih)
      Equal.trans(Nat,
        Nat.add(Groups.len_words(ws), CBN.CB.sum(CB.sizes(Groups.group_add(w, fb, rest)))),
        Nat.add(Groups.len_words(ws), Nat.add(s, 1n)),
        Nat.add(Nat.add(Groups.len_words(ws), s), 1n), e1,
        Equal.sym(Nat, Nat.add(Nat.add(Groups.len_words(ws), s), 1n),
                  Nat.add(Groups.len_words(ws), Nat.add(s, 1n)),
                  NatProof.NatPrf.add_assoc(Groups.len_words(ws), s, 1n)))

# `group_add` raises the size sum by one.
def CB.sum_sizes_add(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +gs: +List<Groups.Group>) ->
  {CBN.CB.sum(CB.sizes(Groups.group_add(w, fb, gs)))
   == Nat.add(CBN.CB.sum(CB.sizes(gs)), 1n) : Nat}:
  match gs:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+f, +ws}:
          CB.sum_sizes_add_head(w, fb, f, ws, rest,
            Feedback.feedback_eq(fb, f), {==},
            CB.sum_sizes_add(w, fb, rest))

# The partition bound over `groups_build`.
def CB.partition_go(+g: +List<Nat>, +w: +List<Nat>, +t: +List<+List<Nat>>,
    +acc: +List<Groups.Group>, b: Bool,
    +eb: {b == Feedback.word_eq(g, w) : Bool},
    k: @a: +List<Groups.Group> ->
       {CBN.CB.sum(CB.sizes(Groups.groups_build(g, t, a)))
        == Nat.add(CBN.CB.sum(CB.sizes(a)), CB.keep(g, t)) : Nat}) ->
  {CBN.CB.sum(CB.sizes(
     Feedback.Bool.case(+List<Groups.Group>, b,
       Groups.groups_build(g, t, acc),
       Groups.groups_build(g, t, Groups.group_add(w, Feedback.feedback(g, w), acc)))))
   == Nat.add(CBN.CB.sum(CB.sizes(acc)), CB.keep(g, w <> t)) : Nat}:
  match b:
    case True{}:
      +eh : {Feedback.word_eq(g, w) == True{} : Bool} =
        Equal.sym(Bool, b, Feedback.word_eq(g, w), eb)
      +ih : {CBN.CB.sum(CB.sizes(Groups.groups_build(g, t, acc)))
             == Nat.add(CBN.CB.sum(CB.sizes(acc)), CB.keep(g, t)) : Nat} =
        k(acc)
      +ek : {CB.keep(g, w <> t) == CB.keep(g, t) : Nat} = CB.keep_true(g, w, t, eh)
      Equal.trans(Nat, CBN.CB.sum(CB.sizes(Groups.groups_build(g, t, acc))),
                  Nat.add(CBN.CB.sum(CB.sizes(acc)), CB.keep(g, t)),
                  Nat.add(CBN.CB.sum(CB.sizes(acc)), CB.keep(g, w <> t)), ih,
                  Equal.cong(Nat, Nat, x => Nat.add(CBN.CB.sum(CB.sizes(acc)), x),
                             CB.keep(g, t), CB.keep(g, w <> t), Equal.sym(Nat, CB.keep(g, w <> t), CB.keep(g, t), ek)))
    case False{}:
      +ef : {Feedback.word_eq(g, w) == False{} : Bool} =
        Equal.sym(Bool, b, Feedback.word_eq(g, w), eb)
      +ih : {CBN.CB.sum(CB.sizes(Groups.groups_build(g, t,
                 Groups.group_add(w, Feedback.feedback(g, w), acc))))
             == Nat.add(CBN.CB.sum(CB.sizes(Groups.group_add(w, Feedback.feedback(g, w), acc))),
                        CB.keep(g, t)) : Nat} =
        k(Groups.group_add(w, Feedback.feedback(g, w), acc))
      +ea : {CBN.CB.sum(CB.sizes(Groups.group_add(w, Feedback.feedback(g, w), acc)))
             == Nat.add(CBN.CB.sum(CB.sizes(acc)), 1n) : Nat} =
        CB.sum_sizes_add(w, Feedback.feedback(g, w), acc)
      +e0 : {Nat.add(CBN.CB.sum(CB.sizes(Groups.group_add(w, Feedback.feedback(g, w), acc))),
                    CB.keep(g, t))
             == Nat.add(Nat.add(CBN.CB.sum(CB.sizes(acc)), 1n), CB.keep(g, t)) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(x, CB.keep(g, t)),
                   CBN.CB.sum(CB.sizes(Groups.group_add(w, Feedback.feedback(g, w), acc))),
                   Nat.add(CBN.CB.sum(CB.sizes(acc)), 1n), ea)
      +e1 : {Nat.add(Nat.add(CBN.CB.sum(CB.sizes(acc)), 1n), CB.keep(g, t))
             == Nat.add(CBN.CB.sum(CB.sizes(acc)), Nat.add(1n, CB.keep(g, t))) : Nat} =
        NatProof.NatPrf.add_assoc(CBN.CB.sum(CB.sizes(acc)), 1n, CB.keep(g, t))
      +ek : {CB.keep(g, w <> t) == Nat.add(1n, CB.keep(g, t)) : Nat} =
        CB.keep_false(g, w, t, ef)
      Equal.trans(Nat,
        CBN.CB.sum(CB.sizes(Groups.groups_build(g, t,
          Groups.group_add(w, Feedback.feedback(g, w), acc)))),
        Nat.add(CBN.CB.sum(CB.sizes(Groups.group_add(w, Feedback.feedback(g, w), acc))),
                CB.keep(g, t)),
        Nat.add(CBN.CB.sum(CB.sizes(acc)), CB.keep(g, w <> t)),
        ih,
        Equal.trans(Nat,
          Nat.add(CBN.CB.sum(CB.sizes(Groups.group_add(w, Feedback.feedback(g, w), acc))),
                  CB.keep(g, t)),
          Nat.add(Nat.add(CBN.CB.sum(CB.sizes(acc)), 1n), CB.keep(g, t)),
          Nat.add(CBN.CB.sum(CB.sizes(acc)), CB.keep(g, w <> t)),
          e0,
          Equal.trans(Nat,
            Nat.add(Nat.add(CBN.CB.sum(CB.sizes(acc)), 1n), CB.keep(g, t)),
            Nat.add(CBN.CB.sum(CB.sizes(acc)), Nat.add(1n, CB.keep(g, t))),
            Nat.add(CBN.CB.sum(CB.sizes(acc)), CB.keep(g, w <> t)),
            e1,
            Equal.cong(Nat, Nat, x => Nat.add(CBN.CB.sum(CB.sizes(acc)), x),
                       Nat.add(1n, CB.keep(g, t)), CB.keep(g, w <> t),
                       Equal.sym(Nat, CB.keep(g, w <> t), Nat.add(1n, CB.keep(g, t)), ek)))))

# The partition bound over `groups_build`.
def CB.partition(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +acc: +List<Groups.Group>) ->
  {CBN.CB.sum(CB.sizes(Groups.groups_build(g, S, acc)))
   == Nat.add(CBN.CB.sum(CB.sizes(acc)), CB.keep(g, S)) : Nat}:
  match S:
    case Nil{}:
      Equal.sym(Nat, Nat.add(CBN.CB.sum(CB.sizes(acc)), 0n), CBN.CB.sum(CB.sizes(acc)),
                NatProof.NatPrf.add_zero(CBN.CB.sum(CB.sizes(acc))))
    case Con{w, t}:
      CB.partition_go(g, w, t, acc, Feedback.word_eq(g, w), {==},
        a => CB.partition(g, t, a))

# `keep` and `dropped` together count the whole list.
def CB.len_split_go(+g: +List<Nat>, +w: +List<Nat>, +t: +List<+List<Nat>>,
    b: Bool, +eb: {b == Feedback.word_eq(g, w) : Bool},
    ih: {List.length(&2, +List<Nat>, t)
         == Nat.add(CB.keep(g, t), CB.dropped(g, t)) : Nat}) ->
  {Nat.add(1n, List.length(&2, +List<Nat>, t))
   == Nat.add(
        Feedback.Bool.case(Nat, b, CB.keep(g, t), Nat.add(1n, CB.keep(g, t))),
        Feedback.Bool.case(Nat, b, Nat.add(1n, CB.dropped(g, t)), CB.dropped(g, t)))
   : Nat}:
  match b:
    case True{}:
      +e1 : {Nat.add(1n, List.length(&2, +List<Nat>, t))
             == Nat.add(1n, Nat.add(CB.keep(g, t), CB.dropped(g, t))) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                   List.length(&2, +List<Nat>, t),
                   Nat.add(CB.keep(g, t), CB.dropped(g, t)), ih)
      Equal.trans(Nat, Nat.add(1n, List.length(&2, +List<Nat>, t)),
                  Nat.add(1n, Nat.add(CB.keep(g, t), CB.dropped(g, t))),
                  Nat.add(CB.keep(g, t), Nat.add(1n, CB.dropped(g, t))), e1,
                  Equal.sym(Nat,
                    Nat.add(CB.keep(g, t), Nat.add(1n, CB.dropped(g, t))),
                    Nat.add(1n, Nat.add(CB.keep(g, t), CB.dropped(g, t))),
                    NatProof.NatPrf.add_succ(CB.keep(g, t), CB.dropped(g, t))))
    case False{}:
      +e1 : {Nat.add(1n, List.length(&2, +List<Nat>, t))
             == Nat.add(1n, Nat.add(CB.keep(g, t), CB.dropped(g, t))) : Nat} =
        Equal.cong(Nat, Nat, x => Nat.add(1n, x),
                   List.length(&2, +List<Nat>, t),
                   Nat.add(CB.keep(g, t), CB.dropped(g, t)), ih)
      e1

# The list length splits into the kept and the dropped words.
def CB.len_split(+g: +List<Nat>, +S: +List<+List<Nat>>) ->
  {List.length(&2, +List<Nat>, S)
   == Nat.add(CB.keep(g, S), CB.dropped(g, S)) : Nat}:
  match S:
    case Nil{}:
      {==}
    case Con{w, t}:
      CB.len_split_go(g, w, t, Feedback.word_eq(g, w), {==},
        CB.len_split(g, t))

# The kept words are no more than the whole list.
def CB.keep_le_len_go(+g: +List<Nat>, +w: +List<Nat>, +t: +List<+List<Nat>>,
    b: Bool, +eb: {b == Feedback.word_eq(g, w) : Bool},
    ih: {Nat.is_le(CB.keep(g, t), List.length(&2, +List<Nat>, t)) == True{} : Bool}) ->
  {Nat.is_le(
     Feedback.Bool.case(Nat, b, CB.keep(g, t), Nat.add(1n, CB.keep(g, t))),
     Nat.add(1n, List.length(&2, +List<Nat>, t))) == True{} : Bool}:
  match b:
    case True{}:
      NatProof.Nat.is_le_of_lt(CB.keep(g, t), Nat.add(1n, List.length(&2, +List<Nat>, t)),
        NatProof.Nat.is_lt_succ_of_le(CB.keep(g, t), List.length(&2, +List<Nat>, t), ih))
    case False{}:
      ih

def CB.keep_le_len(+g: +List<Nat>, +S: +List<+List<Nat>>) ->
  {Nat.is_le(CB.keep(g, S), List.length(&2, +List<Nat>, S)) == True{} : Bool}:
  match S:
    case Nil{}:
      NatProof.Nat.is_le_refl(0n)
    case Con{w, t}:
      CB.keep_le_len_go(g, w, t, Feedback.word_eq(g, w), {==},
        CB.keep_le_len(g, t))

# The class sizes built from `S` sum to at most the length of `S`.
def CB.partition_le(+g: +List<Nat>, +S: +List<+List<Nat>>) ->
  {Nat.is_le(CBN.CB.sum(CB.sizes(Groups.groups_build(g, S, Nil{}))),
             List.length(&2, +List<Nat>, S)) == True{} : Bool}:
  +eq : {CBN.CB.sum(CB.sizes(Groups.groups_build(g, S, Nil{})))
         == CB.keep(g, S) : Nat} =
    CB.partition(g, S, Nil{})
  +h : {Nat.is_le(CB.keep(g, S), List.length(&2, +List<Nat>, S)) == True{} : Bool} =
    CB.keep_le_len(g, S)
  NatProof.Nat.is_le_eq_l(List.length(&2, +List<Nat>, S), CB.keep(g, S),
    CBN.CB.sum(CB.sizes(Groups.groups_build(g, S, Nil{}))),
    Equal.sym(Nat, CBN.CB.sum(CB.sizes(Groups.groups_build(g, S, Nil{}))),
              CB.keep(g, S), eq), h)

# The natural per-class facts: the class is smaller than `n`, and its cost is
# bounded by its own square.
def CB.Bounds(+n: Nat, +groups: +List<Groups.Group>, +cs: +List<Nat>) -> Type:
  match groups:
    case Nil{}:
      match cs:
        case Nil{}:
          Unit
        case Con{c, ct}:
          Empty
    case Con{gp, gt}:
      match gp:
        case Groups.Group{f, ws}:
          match cs:
            case Nil{}:
              Empty
            case Con{c, ct}:
              {Nat.is_lt(Groups.len_words(ws), n) == True{} : Bool}
              & {Nat.is_le(c, Nat.mul(Groups.len_words(ws), Groups.len_words(ws))) == True{} : Bool}
              & CB.Bounds(n, gt, ct)

# The pointwise `c <= m*pred n` form of the class facts.
def CB.PointLeG(+n: Nat, +groups: +List<Groups.Group>, +cs: +List<Nat>) -> Type:
  match groups:
    case Nil{}:
      match cs:
        case Nil{}:
          Unit
        case Con{c, ct}:
          Empty
    case Con{gp, gt}:
      match gp:
        case Groups.Group{f, ws}:
          match cs:
            case Nil{}:
              Empty
            case Con{c, ct}:
              {Nat.is_le(c, Nat.mul(Groups.len_words(ws), CBN.CB.pred(n))) == True{} : Bool}
              & CB.PointLeG(n, gt, ct)

# Turn the natural facts into the scaled form, one class at a time.
def CB.point_le_g_of_bounds(+n: Nat, +groups: +List<Groups.Group>, +cs: +List<Nat>,
    b: CB.Bounds(n, groups, cs)) -> CB.PointLeG(n, groups, cs):
  match groups:
    case Nil{}:
      match cs:
        case Nil{}:
          Unit{}
        case Con{c, ct}:
          match b:
    case Con{gp, gt}:
      match gp:
        case Groups.Group{f, ws}:
          match cs:
            case Nil{}:
              match b:
            case Con{c, ct}:
              (bl, br) = b
              (ble, bt) = br
              (CBN.CB.cost_le_size_pred(Groups.len_words(ws), c, n, ble, bl),
               CB.point_le_g_of_bounds(n, gt, ct, bt))

# Read the scaled group form as the size list form `CB.bound` consumes.
def CB.point_le_p_of_g(+n: Nat, +groups: +List<Groups.Group>, +cs: +List<Nat>,
    p: CB.PointLeG(n, groups, cs)) ->
  CBN.CB.PointLeP(n, CB.sizes(groups), cs):
  match groups:
    case Nil{}:
      match cs:
        case Nil{}:
          Unit{}
        case Con{c, ct}:
          match p:
    case Con{gp, gt}:
      match gp:
        case Groups.Group{f, ws}:
          match cs:
            case Nil{}:
              match p:
            case Con{c, ct}:
              (ph, pt) = p
              (ph, CB.point_le_p_of_g(n, gt, ct, pt))

# The class bound over an actual group list and its per-class costs.
def CB.bound_groups(+n: Nat, +groups: +List<Groups.Group>, +cs: +List<Nat>,
    b: CB.Bounds(n, groups, cs),
    +part: {Nat.is_le(CBN.CB.sum(CB.sizes(groups)), n) == True{} : Bool}) ->
  {Nat.is_le(Nat.add(n, CBN.CB.sum(cs)), Nat.mul(n, n)) == True{} : Bool}:
  CBN.CB.bound(n, CB.sizes(groups), cs,
    CB.point_le_p_of_g(n, groups, cs, CB.point_le_g_of_bounds(n, groups, cs, b)),
    part)

# The same bound below the solver's infinity: with `n <= N` the node cost is
# strictly below `N*N + 1`.
def CB.fits_inf(+n: Nat, +N: Nat, +groups: +List<Groups.Group>, +cs: +List<Nat>,
    b: CB.Bounds(n, groups, cs),
    +part: {Nat.is_le(CBN.CB.sum(CB.sizes(groups)), n) == True{} : Bool},
    +leN: {Nat.is_le(n, N) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(n, CBN.CB.sum(cs)), Nat.add(Nat.mul(N, N), 1n)) == True{} : Bool}:
  +bounds : {Nat.is_le(Nat.add(n, CBN.CB.sum(cs)), Nat.mul(n, n)) == True{} : Bool} =
    CB.bound_groups(n, groups, cs, b, part)
  +h1 : {Nat.is_le(Nat.mul(n, n), Nat.mul(N, n)) == True{} : Bool} =
    CBN.CB.is_le_mul_l(n, N, n, leN)
  +h2 : {Nat.is_le(Nat.mul(N, n), Nat.mul(N, N)) == True{} : Bool} =
    CBN.CB.is_le_mul_r(n, N, N, leN)
  +h3 : {Nat.is_le(Nat.mul(n, n), Nat.mul(N, N)) == True{} : Bool} =
    NatProof.Nat.is_le_trans(Nat.mul(n, n), Nat.mul(N, n), Nat.mul(N, N), h1, h2)
  +h4 : {Nat.is_lt(Nat.mul(n, n), Nat.add(Nat.mul(N, N), 1n)) == True{} : Bool} =
    NatProof.Nat.is_le_lt_trans(Nat.mul(n, n), Nat.mul(N, N), Nat.add(Nat.mul(N, N), 1n),
      h3, CBN.CB.lt_add_one(Nat.mul(N, N)))
  NatProof.Nat.is_le_lt_trans(Nat.add(n, CBN.CB.sum(cs)), Nat.mul(n, n),
    Nat.add(Nat.mul(N, N), 1n), bounds, h4)

# The same bound for the classes of a guess, with the size of the candidate list
# as the node size and the partition bound discharged by `groups_build`.
def CB.fits_inf_classes(+N: Nat, +S: +List<+List<Nat>>, +g: +List<Nat>,
    +cs: +List<Nat>,
    b: CB.Bounds(Groups.len_words(S), Groups.groups_build(g, S, Nil{}), cs),
    +leN: {Nat.is_le(Groups.len_words(S), N) == True{} : Bool}) ->
  {Nat.is_lt(Nat.add(Groups.len_words(S), CBN.CB.sum(cs)),
             Nat.add(Nat.mul(N, N), 1n)) == True{} : Bool}:
  CB.fits_inf(Groups.len_words(S), N, Groups.groups_build(g, S, Nil{}), cs, b,
    CB.partition_le(g, S), leN)
