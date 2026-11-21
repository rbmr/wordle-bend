# Linear feedback and group partitioning for the pruned solver.
#
# In `src/feedback.bend` and `src/groups.bend`, `non_green`, `consume_color`,
# `consume_pool`, `feedback.go`, `group_add` and `groups_build` pass their
# recursive calls in both branches of `Feedback.Bool.case`. Because function
# arguments are evaluated before the call, each step evaluates both recursive
# branches, making `groups_build` exponential in the candidate count and
# `feedback` exponential in the word length.
#
# `src/solve_fast.bend` defines the same operations with `match` on a `Bool`
# parameter so each step makes one recursive call. This module proves that they
# return the exact same feedback lists and group lists as the reference
# definitions.
import Base
import ../src/solve_fast.bend as SolveFast
import ../src/groups.bend as Groups
import ../src/feedback.bend as Feedback

# `False` is a right absorber for `Bool.and`.
def FG.and_false_r(x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def FG.word_step_rhs(+at: +List<Nat>, +bt: +List<Nat>, same: Bool) -> Bool:
  Bool.and(
    Nat.is_eq(List.length(&2, Nat, at), List.length(&2, Nat, bt)),
    List.all.if(
      u => List.all(&1, Nat & Nat, Feedback.pair_nat_eq,
             List.zip(&2, Nat, &2, Nat, at, bt)),
      same))

# `word_eq_go` agrees with `Feedback.word_eq`.
def FG.word_eq_go_eq(+a: +List<Nat>, +b: +List<Nat>, same: Bool,
    +es: {same == Feedback.next_same(a, b) : Bool}) ->
  {SolveFast.word_eq_go(a, b, same) == Feedback.word_eq(a, b) : Bool}:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          {==}
        case Con{bh, bt}:
          {==}
    case Con{+ah, +at}:
      match b:
        case Nil{}:
          {==}
        case Con{+bh, +bt}:
          match same:
            case True{}:
              +e1 : {SolveFast.word_eq_go(at, bt, Feedback.next_same(at, bt))
                     == Feedback.word_eq(at, bt) : Bool} =
                FG.word_eq_go_eq(at, bt, Feedback.next_same(at, bt), {==})
              +e2 : {FG.word_step_rhs(at, bt, True{})
                     == FG.word_step_rhs(at, bt, Nat.is_eq(ah, bh)) : Bool} =
                Equal.cong(Bool, Bool,
                  s => FG.word_step_rhs(at, bt, s),
                  True{}, Nat.is_eq(ah, bh), es)
              Equal.trans(Bool,
                SolveFast.word_eq_go(at, bt, Feedback.next_same(at, bt)),
                Feedback.word_eq(at, bt),
                Feedback.word_eq(ah <> at, bh <> bt),
                e1, e2)
            case False{}:
              +e1 : {False{} == FG.word_step_rhs(at, bt, False{}) : Bool} =
                Equal.sym(Bool,
                  FG.word_step_rhs(at, bt, False{}),
                  False{},
                  FG.and_false_r(
                    Nat.is_eq(List.length(&2, Nat, at),
                      List.length(&2, Nat, bt))))
              +e2 : {FG.word_step_rhs(at, bt, False{})
                     == FG.word_step_rhs(at, bt, Nat.is_eq(ah, bh)) : Bool} =
                Equal.cong(Bool, Bool,
                  s => FG.word_step_rhs(at, bt, s),
                  False{}, Nat.is_eq(ah, bh), es)
              Equal.trans(Bool,
                False{},
                FG.word_step_rhs(at, bt, False{}),
                Feedback.word_eq(ah <> at, bh <> bt),
                e1, e2)

# `word_eq_fast` agrees with `Feedback.word_eq`.
def FG.word_eq_fast_eq(+a: +List<Nat>, +b: +List<Nat>) ->
  {SolveFast.word_eq_fast(a, b) == Feedback.word_eq(a, b) : Bool}:
  FG.word_eq_go_eq(a, b, Feedback.next_same(a, b), {==})

def FG.fb_step_rhs(+at: +List<Feedback.Color>, +bt: +List<Feedback.Color>,
    same: Bool) -> Bool:
  Bool.and(
    Nat.is_eq(List.length(&2, Feedback.Color, at),
      List.length(&2, Feedback.Color, bt)),
    List.all.if(
      u => List.all(&1, Feedback.Color & Feedback.Color,
             Feedback.pair_color_eq,
             List.zip(&2, Feedback.Color, &2, Feedback.Color, at, bt)),
      same))

# `feedback_eq_go` agrees with `Feedback.feedback_eq`.
def FG.feedback_eq_go_eq(+a: +List<Feedback.Color>,
    +b: +List<Feedback.Color>, same: Bool,
    +es: {same == SolveFast.next_fb_same(a, b) : Bool}) ->
  {SolveFast.feedback_eq_go(a, b, same)
   == Feedback.feedback_eq(a, b) : Bool}:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          {==}
        case Con{bh, bt}:
          {==}
    case Con{+ah, +at}:
      match b:
        case Nil{}:
          {==}
        case Con{+bh, +bt}:
          match same:
            case True{}:
              +e1 : {SolveFast.feedback_eq_go(at, bt,
                       SolveFast.next_fb_same(at, bt))
                     == Feedback.feedback_eq(at, bt) : Bool} =
                FG.feedback_eq_go_eq(at, bt,
                  SolveFast.next_fb_same(at, bt), {==})
              +e2 : {FG.fb_step_rhs(at, bt, True{})
                     == FG.fb_step_rhs(at, bt, Feedback.Color.eq(ah, bh))
                     : Bool} =
                Equal.cong(Bool, Bool,
                  s => FG.fb_step_rhs(at, bt, s),
                  True{}, Feedback.Color.eq(ah, bh), es)
              Equal.trans(Bool,
                SolveFast.feedback_eq_go(at, bt,
                  SolveFast.next_fb_same(at, bt)),
                Feedback.feedback_eq(at, bt),
                Feedback.feedback_eq(ah <> at, bh <> bt),
                e1, e2)
            case False{}:
              +e1 : {False{} == FG.fb_step_rhs(at, bt, False{}) : Bool} =
                Equal.sym(Bool,
                  FG.fb_step_rhs(at, bt, False{}),
                  False{},
                  FG.and_false_r(
                    Nat.is_eq(List.length(&2, Feedback.Color, at),
                      List.length(&2, Feedback.Color, bt))))
              +e2 : {FG.fb_step_rhs(at, bt, False{})
                     == FG.fb_step_rhs(at, bt, Feedback.Color.eq(ah, bh))
                     : Bool} =
                Equal.cong(Bool, Bool,
                  s => FG.fb_step_rhs(at, bt, s),
                  False{}, Feedback.Color.eq(ah, bh), es)
              Equal.trans(Bool,
                False{},
                FG.fb_step_rhs(at, bt, False{}),
                Feedback.feedback_eq(ah <> at, bh <> bt),
                e1, e2)

# `feedback_eq_fast` agrees with `Feedback.feedback_eq`.
def FG.feedback_eq_fast_eq(+a: +List<Feedback.Color>,
    +b: +List<Feedback.Color>) ->
  {SolveFast.feedback_eq_fast(a, b) == Feedback.feedback_eq(a, b) : Bool}:
  FG.feedback_eq_go_eq(a, b, SolveFast.next_fb_same(a, b), {==})

# `non_green_pick` agrees with `Bool.case` when the recursive tails agree.
def FG.non_green_pick_eq(+a: Nat, +r1: +List<Nat>, +r2: +List<Nat>,
    same: Bool, er: {r1 == r2 : +List<Nat>}) ->
  {SolveFast.non_green_pick(a, r1, same)
   == Feedback.Bool.case(+List<Nat>, same, r2, a <> r2) : +List<Nat>}:
  match same:
    case True{}:
      er
    case False{}:
      Equal.cong(+List<Nat>, +List<Nat>, l => a <> l, r1, r2, er)

# `non_green_fast` agrees with `Feedback.non_green`.
def FG.non_green_eq(+guess: +List<Nat>, +answer: +List<Nat>) ->
  {SolveFast.non_green_fast(guess, answer)
   == Feedback.non_green(guess, answer) : +List<Nat>}:
  match guess:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      match answer:
        case Nil{}:
          {==}
        case Con{+a, +at}:
          FG.non_green_pick_eq(a, SolveFast.non_green_fast(t, at),
            Feedback.non_green(t, at), Nat.is_eq(g, a),
            FG.non_green_eq(t, at))

# `consume_color_fast` agrees with `Feedback.consume_color`.
def FG.consume_color_eq(+x: Nat, +pool: +List<Nat>, same: Bool) ->
  {SolveFast.consume_color_fast(x, pool, same)
   == Feedback.consume_color(x, pool, same) : Feedback.Color}:
  match pool:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      match same:
        case True{}:
          {==}
        case False{}:
          FG.consume_color_eq(x, t, Feedback.next_letter_same(x, t))

# `consume_pool_fast` agrees with `Feedback.consume_pool`.
def FG.consume_pool_eq(+x: Nat, +pool: +List<Nat>, same: Bool) ->
  {SolveFast.consume_pool_fast(x, pool, same)
   == Feedback.consume_pool(x, pool, same) : +List<Nat>}:
  match pool:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      match same:
        case True{}:
          {==}
        case False{}:
          Equal.cong(+List<Nat>, +List<Nat>, l => h <> l,
            SolveFast.consume_pool_fast(x, t, Feedback.next_letter_same(x, t)),
            Feedback.consume_pool(x, t, Feedback.next_letter_same(x, t)),
            FG.consume_pool_eq(x, t, Feedback.next_letter_same(x, t)))

# Helper to combine head and tail equalities on a color list.
def FG.color_cons_eq(+c1: Feedback.Color, +c2: Feedback.Color,
    +t1: +List<Feedback.Color>, +t2: +List<Feedback.Color>,
    ec: {c1 == c2 : Feedback.Color},
    et: {t1 == t2 : +List<Feedback.Color>}) ->
  {c1 <> t1 == c2 <> t2 : +List<Feedback.Color>}:
  Equal.trans(+List<Feedback.Color>, c1 <> t1, c2 <> t1, c2 <> t2,
    Equal.cong(Feedback.Color, +List<Feedback.Color>, c => c <> t1, c1, c2, ec),
    Equal.cong(+List<Feedback.Color>, +List<Feedback.Color>, l => c2 <> l,
      t1, t2, et))

# `feedback_go_fast` agrees with `Feedback.feedback.go`.
def FG.feedback_go_eq(+guess: +List<Nat>, +answer: +List<Nat>,
    +pool: +List<Nat>, same: Bool) ->
  {SolveFast.feedback_go_fast(guess, answer, pool, same)
   == Feedback.feedback.go(guess, answer, pool, same)
   : +List<Feedback.Color>}:
  match guess:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      match answer:
        case Nil{}:
          Equal.cong(+List<Feedback.Color>, +List<Feedback.Color>,
            l => Feedback.Gray{} <> l,
            SolveFast.feedback_go_fast(t, Nil{}, Nil{}, False{}),
            Feedback.feedback.go(t, Nil{}, Nil{}, False{}),
            FG.feedback_go_eq(t, Nil{}, Nil{}, False{}))
        case Con{+a, +at}:
          match same:
            case True{}:
              Equal.cong(+List<Feedback.Color>, +List<Feedback.Color>,
                l => Feedback.Green{} <> l,
                SolveFast.feedback_go_fast(t, at, pool,
                  Feedback.next_same(t, at)),
                Feedback.feedback.go(t, at, pool, Feedback.next_same(t, at)),
                FG.feedback_go_eq(t, at, pool, Feedback.next_same(t, at)))
            case False{}:
              +p1 : +List<Nat> =
                SolveFast.consume_pool_fast(g, pool,
                  Feedback.next_letter_same(g, pool))
              +p2 : +List<Nat> =
                Feedback.consume_pool(g, pool,
                  Feedback.next_letter_same(g, pool))
              +ep : {p1 == p2 : +List<Nat>} =
                FG.consume_pool_eq(g, pool, Feedback.next_letter_same(g, pool))
              +et1 : {SolveFast.feedback_go_fast(t, at, p1,
                        Feedback.next_same(t, at))
                      == SolveFast.feedback_go_fast(t, at, p2,
                           Feedback.next_same(t, at))
                      : +List<Feedback.Color>} =
                Equal.cong(+List<Nat>, +List<Feedback.Color>,
                  p => SolveFast.feedback_go_fast(t, at, p,
                         Feedback.next_same(t, at)),
                  p1, p2, ep)
              +et2 : {SolveFast.feedback_go_fast(t, at, p2,
                        Feedback.next_same(t, at))
                      == Feedback.feedback.go(t, at, p2,
                           Feedback.next_same(t, at))
                      : +List<Feedback.Color>} =
                FG.feedback_go_eq(t, at, p2, Feedback.next_same(t, at))
              FG.color_cons_eq(
                SolveFast.consume_color_fast(g, pool,
                  Feedback.next_letter_same(g, pool)),
                Feedback.consume_color(g, pool,
                  Feedback.next_letter_same(g, pool)),
                SolveFast.feedback_go_fast(t, at, p1,
                  Feedback.next_same(t, at)),
                Feedback.feedback.go(t, at, p2, Feedback.next_same(t, at)),
                FG.consume_color_eq(g, pool,
                  Feedback.next_letter_same(g, pool)),
                Equal.trans(+List<Feedback.Color>,
                  SolveFast.feedback_go_fast(t, at, p1,
                    Feedback.next_same(t, at)),
                  SolveFast.feedback_go_fast(t, at, p2,
                    Feedback.next_same(t, at)),
                  Feedback.feedback.go(t, at, p2, Feedback.next_same(t, at)),
                  et1, et2))

# `feedback_fast` agrees with `Feedback.feedback`.
def FG.feedback_eq(+guess: +List<Nat>, +answer: +List<Nat>) ->
  {SolveFast.feedback_fast(guess, answer)
   == Feedback.feedback(guess, answer) : +List<Feedback.Color>}:
  +e1 : {SolveFast.feedback_go_fast(guess, answer,
           SolveFast.non_green_fast(guess, answer),
           Feedback.next_same(guess, answer))
         == SolveFast.feedback_go_fast(guess, answer,
              Feedback.non_green(guess, answer),
              Feedback.next_same(guess, answer))
         : +List<Feedback.Color>} =
    Equal.cong(+List<Nat>, +List<Feedback.Color>,
      p => SolveFast.feedback_go_fast(guess, answer, p,
             Feedback.next_same(guess, answer)),
      SolveFast.non_green_fast(guess, answer),
      Feedback.non_green(guess, answer),
      FG.non_green_eq(guess, answer))
  +e2 : {SolveFast.feedback_go_fast(guess, answer,
           Feedback.non_green(guess, answer),
           Feedback.next_same(guess, answer))
         == Feedback.feedback.go(guess, answer,
              Feedback.non_green(guess, answer),
              Feedback.next_same(guess, answer))
         : +List<Feedback.Color>} =
    FG.feedback_go_eq(guess, answer, Feedback.non_green(guess, answer),
      Feedback.next_same(guess, answer))
  Equal.trans(+List<Feedback.Color>,
    SolveFast.feedback_fast(guess, answer),
    SolveFast.feedback_go_fast(guess, answer,
      Feedback.non_green(guess, answer),
      Feedback.next_same(guess, answer)),
    Feedback.feedback(guess, answer),
    e1, e2)

def FG.group_add_go_eq(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +groups: +List<Groups.Group>, hit: Bool,
    +eh: {hit == SolveFast.next_group_hit(fb, groups) : Bool}) ->
  {SolveFast.group_add_go(w, fb, groups, hit)
   == Groups.group_add(w, fb, groups) : +List<Groups.Group>}:
  match groups:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+f, +ws}:
          match hit:
            case True{}:
              +eh_ref : {True{} == Feedback.feedback_eq(fb, f) : Bool} =
                Equal.trans(Bool, True{},
                  SolveFast.feedback_eq_fast(fb, f),
                  Feedback.feedback_eq(fb, f),
                  eh, FG.feedback_eq_fast_eq(fb, f))
              Equal.cong(Bool, +List<Groups.Group>,
                b => Feedback.Bool.case(+List<Groups.Group>, b,
                       Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])}
                         <> rest,
                       Groups.Group{f, ws} <> Groups.group_add(w, fb, rest)),
                True{}, Feedback.feedback_eq(fb, f), eh_ref)
            case False{}:
              +eh_ref : {False{} == Feedback.feedback_eq(fb, f) : Bool} =
                Equal.trans(Bool, False{},
                  SolveFast.feedback_eq_fast(fb, f),
                  Feedback.feedback_eq(fb, f),
                  eh, FG.feedback_eq_fast_eq(fb, f))
              +e1 : {Groups.Group{f, ws}
                     <> SolveFast.group_add_go(w, fb, rest,
                          SolveFast.next_group_hit(fb, rest))
                     == Groups.Group{f, ws} <> Groups.group_add(w, fb, rest)
                     : +List<Groups.Group>} =
                Equal.cong(+List<Groups.Group>, +List<Groups.Group>,
                  l => Groups.Group{f, ws} <> l,
                  SolveFast.group_add_go(w, fb, rest,
                    SolveFast.next_group_hit(fb, rest)),
                  Groups.group_add(w, fb, rest),
                  FG.group_add_go_eq(w, fb, rest,
                    SolveFast.next_group_hit(fb, rest), {==}))
              +e2 : {Groups.Group{f, ws} <> Groups.group_add(w, fb, rest)
                     == Feedback.Bool.case(+List<Groups.Group>,
                          Feedback.feedback_eq(fb, f),
                          Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])}
                            <> rest,
                          Groups.Group{f, ws} <> Groups.group_add(w, fb, rest))
                     : +List<Groups.Group>} =
                Equal.cong(Bool, +List<Groups.Group>,
                  b => Feedback.Bool.case(+List<Groups.Group>, b,
                         Groups.Group{f, List.append(&2, +List<Nat>, ws, [w])}
                           <> rest,
                         Groups.Group{f, ws} <> Groups.group_add(w, fb, rest)),
                  False{}, Feedback.feedback_eq(fb, f), eh_ref)
              Equal.trans(+List<Groups.Group>,
                Groups.Group{f, ws}
                <> SolveFast.group_add_go(w, fb, rest,
                     SolveFast.next_group_hit(fb, rest)),
                Groups.Group{f, ws} <> Groups.group_add(w, fb, rest),
                Groups.group_add(w, fb, Groups.Group{f, ws} <> rest),
                e1, e2)

# `group_add_fast` agrees with `Groups.group_add`.
def FG.group_add_eq(+w: +List<Nat>, +fb: +List<Feedback.Color>,
    +groups: +List<Groups.Group>) ->
  {SolveFast.group_add_fast(w, fb, groups)
   == Groups.group_add(w, fb, groups) : +List<Groups.Group>}:
  FG.group_add_go_eq(w, fb, groups,
    SolveFast.next_group_hit(fb, groups), {==})

# `group_add_fast(w, feedback_fast(g, w), acc)` agrees with the reference.
def FG.group_add_feedback_eq(+g: +List<Nat>, +w: +List<Nat>,
    +acc: +List<Groups.Group>) ->
  {SolveFast.group_add_fast(w, SolveFast.feedback_fast(g, w), acc)
   == Groups.group_add(w, Feedback.feedback(g, w), acc)
   : +List<Groups.Group>}:
  +e1 : {SolveFast.group_add_fast(w, SolveFast.feedback_fast(g, w), acc)
         == SolveFast.group_add_fast(w, Feedback.feedback(g, w), acc)
         : +List<Groups.Group>} =
    Equal.cong(+List<Feedback.Color>, +List<Groups.Group>,
      fb => SolveFast.group_add_fast(w, fb, acc),
      SolveFast.feedback_fast(g, w), Feedback.feedback(g, w),
      FG.feedback_eq(g, w))
  +e2 : {SolveFast.group_add_fast(w, Feedback.feedback(g, w), acc)
         == Groups.group_add(w, Feedback.feedback(g, w), acc)
         : +List<Groups.Group>} =
    FG.group_add_eq(w, Feedback.feedback(g, w), acc)
  Equal.trans(+List<Groups.Group>,
    SolveFast.group_add_fast(w, SolveFast.feedback_fast(g, w), acc),
    SolveFast.group_add_fast(w, Feedback.feedback(g, w), acc),
    Groups.group_add(w, Feedback.feedback(g, w), acc),
    e1, e2)

# One step of `groups_build_fast` agrees with `Groups.groups_build`.
def FG.groups_step_eq(+g: +List<Nat>, +w: +List<Nat>,
    +rest: +List<+List<Nat>>, +acc: +List<Groups.Group>, same: Bool) ->
  {Groups.groups_build(g, rest, SolveFast.groups_next_acc(g, w, acc, same))
   == Feedback.Bool.case(+List<Groups.Group>, same,
        Groups.groups_build(g, rest, acc),
        Groups.groups_build(g, rest,
          Groups.group_add(w, Feedback.feedback(g, w), acc)))
   : +List<Groups.Group>}:
  match same:
    case True{}:
      {==}
    case False{}:
      Equal.cong(+List<Groups.Group>, +List<Groups.Group>,
        a => Groups.groups_build(g, rest, a),
        SolveFast.group_add_fast(w, SolveFast.feedback_fast(g, w), acc),
        Groups.group_add(w, Feedback.feedback(g, w), acc),
        FG.group_add_feedback_eq(g, w, acc))

# `groups_build_fast` agrees with `Groups.groups_build`.
def FG.groups_build_eq(+g: +List<Nat>, +S: +List<+List<Nat>>,
    +acc: +List<Groups.Group>) ->
  {SolveFast.groups_build_fast(g, S, acc)
   == Groups.groups_build(g, S, acc) : +List<Groups.Group>}:
  match S:
    case Nil{}:
      {==}
    case Con{+w, +rest}:
      +ew : {Groups.groups_build(g, rest,
               SolveFast.groups_next_acc(g, w, acc,
                 SolveFast.word_eq_fast(g, w)))
             == Groups.groups_build(g, rest,
                  SolveFast.groups_next_acc(g, w, acc,
                    Feedback.word_eq(g, w)))
             : +List<Groups.Group>} =
        Equal.cong(Bool, +List<Groups.Group>,
          b => Groups.groups_build(g, rest,
                 SolveFast.groups_next_acc(g, w, acc, b)),
          SolveFast.word_eq_fast(g, w), Feedback.word_eq(g, w),
          FG.word_eq_fast_eq(g, w))
      Equal.trans(+List<Groups.Group>,
        SolveFast.groups_build_fast(g, rest,
          SolveFast.groups_next_acc(g, w, acc, SolveFast.word_eq_fast(g, w))),
        Groups.groups_build(g, rest,
          SolveFast.groups_next_acc(g, w, acc, Feedback.word_eq(g, w))),
        Feedback.Bool.case(+List<Groups.Group>, Feedback.word_eq(g, w),
          Groups.groups_build(g, rest, acc),
          Groups.groups_build(g, rest,
            Groups.group_add(w, Feedback.feedback(g, w), acc))),
        Equal.trans(+List<Groups.Group>,
          SolveFast.groups_build_fast(g, rest,
            SolveFast.groups_next_acc(g, w, acc, SolveFast.word_eq_fast(g, w))),
          Groups.groups_build(g, rest,
            SolveFast.groups_next_acc(g, w, acc, SolveFast.word_eq_fast(g, w))),
          Groups.groups_build(g, rest,
            SolveFast.groups_next_acc(g, w, acc, Feedback.word_eq(g, w))),
          FG.groups_build_eq(g, rest,
            SolveFast.groups_next_acc(g, w, acc, SolveFast.word_eq_fast(g, w))),
          ew),
        FG.groups_step_eq(g, w, rest, acc, Feedback.word_eq(g, w)))

# `groups_smaller_fast` with `len_words(S)` agrees with `Groups.groups_smaller`.
def FG.groups_smaller_fast_eq(+S: +List<+List<Nat>>,
    +groups: +List<Groups.Group>) ->
  {SolveFast.groups_smaller_fast(Groups.len_words(S), groups)
   == Groups.groups_smaller(S, groups) : Bool}:
  match groups:
    case Nil{}:
      {==}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          Equal.cong(Bool, Bool,
            b => Bool.and(
                   Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)), b),
            SolveFast.groups_smaller_fast(Groups.len_words(S), rest),
            Groups.groups_smaller(S, rest),
            FG.groups_smaller_fast_eq(S, rest))
