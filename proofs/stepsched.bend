# The flat schedule the solver consumes, written as a datatype.
#
# `step` matches on a list of `Item`s. This module mirrors that list with a
# `Sched` whose constructors carry the groups and the accumulated processing
# context. The mirror is only for the proof: `items` erases the context and
# gives back the exact list `step` sees, so an induction on `Sched` is an
# induction on the schedule the solver actually runs.
import Base
import ../src/solve_ref.bend as SolveRef
import ../src/tree.bend as Tree
import ../src/feedback.bend as Feedback
import ../src/groups.bend as Groups
import ./logic.bend as Logic
import ./nat.bend as NatProof
import ./bestok.bend as BO
import ./eval.bend as Eval
import ./stepvalid.bend as SV

# A usable guess: its groups passed `groups_smaller`, and its guess is in the
# input list.
type SB.Block is Data:
  Block{G: +List<+List<Nat>>, S: +List<+List<Nat>>, g: +List<Nat>,
        g_in: {Tree.member_word(g, G) == True{} : Bool},
        smaller: {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == True{} : Bool}}

def SB.block_G(b: SB.Block) -> +List<+List<Nat>>:
  match b:
    case Block{G, S, g, g_in, smaller}:
      G

def SB.block_S(b: SB.Block) -> +List<+List<Nat>>:
  match b:
    case Block{G, S, g, g_in, smaller}:
      S

def SB.block_g(b: SB.Block) -> +List<Nat>:
  match b:
    case Block{G, S, g, g_in, smaller}:
      g

def SB.block_in(b: SB.Block) -> {Tree.member_word(SB.block_g(b), SB.block_G(b)) == True{} : Bool}:
  match b:
    case Block{G, S, g, g_in, smaller}:
      g_in

def SB.block_smaller(b: SB.Block) ->
  {Groups.groups_smaller(SB.block_S(b),
     Groups.groups_build(SB.block_g(b), SB.block_S(b), Nil{})) == True{} : Bool}:
  match b:
    case Block{G, S, g, g_in, smaller}:
      smaller

def SB.block_groups(b: SB.Block) -> +List<Groups.Group>:
  match b:
    case Block{G, S, g, g_in, smaller}:
      Groups.groups_build(g, S, Nil{})

# The schedule mirror. Every constructor's `rest` is the rest of the item list.
type SB.Sched is Data:
  SchedNil{}
  SBegin{b: SB.Block, tail: +List<SB.Block>, rest: SB.Sched}
  SClass{b: SB.Block, fb: +List<Feedback.Color>, ws: +List<+List<Nat>>,
         processed: +List<Groups.Group>, restGroups: +List<Groups.Group>,
         rest: SB.Sched,
         +split: {SB.block_groups(b)
                 == List.append(&2, Groups.Group, processed,
                      Groups.Group{fb, ws} <> restGroups) : +List<Groups.Group>}}
  SAdd{b: SB.Block, fb: +List<Feedback.Color>, ws: +List<+List<Nat>>,
       processed: +List<Groups.Group>, restGroups: +List<Groups.Group>,
       rest: SB.Sched,
       +split: {SB.block_groups(b)
               == List.append(&2, Groups.Group, processed,
                    Groups.Group{fb, ws} <> restGroups) : +List<Groups.Group>}}
  SEnd{b: SB.Block, processed: +List<Groups.Group>, tail: +List<SB.Block>,
       rest: SB.Sched,
       +split: {SB.block_groups(b)
               == List.append(&2, Groups.Group, processed, Nil{}) : +List<Groups.Group>}}

# The flat item list.
def SB.items(sched: SB.Sched) -> +List<SolveRef.Item>:
  match sched:
    case SchedNil{}:
      Nil{}
    case SBegin{b, tail, rest}:
      SolveRef.Begin{SB.block_g(b)} <> SB.items(rest)
    case SClass{b, fb, ws, processed, restGroups, rest, split}:
      SolveRef.ClassItem{fb, ws} <> SB.items(rest)
    case SAdd{b, fb, ws, processed, restGroups, rest, split}:
      SolveRef.Add{fb} <> SB.items(rest)
    case SEnd{b, processed, tail, rest, split}:
      SolveRef.End{} <> SB.items(rest)

# `(xs ++ [x]) ++ ys = xs ++ (x :: ys)`.
def SB.group_append(+xs: +List<Groups.Group>, +fb: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +ys: +List<Groups.Group>) ->
  {List.append(&2, Groups.Group,
     List.append(&2, Groups.Group, xs, Groups.Group{fb, ws} <> Nil{}), ys)
   == List.append(&2, Groups.Group, xs, Groups.Group{fb, ws} <> ys)
   : +List<Groups.Group>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(+List<Groups.Group>, +List<Groups.Group>, l => h <> l,
        List.append(&2, Groups.Group,
          List.append(&2, Groups.Group, t, Groups.Group{fb, ws} <> Nil{}), ys),
        List.append(&2, Groups.Group, t, Groups.Group{fb, ws} <> ys),
        SB.group_append(t, fb, ws, ys))

# `processed ++ (gp :: rest)` is `(processed ++ [gp]) ++ rest`.
def SB.split_after(b: SB.Block, +processed: +List<Groups.Group>, +fb: +List<Feedback.Color>,
    +ws: +List<+List<Nat>>, +restg: +List<Groups.Group>,
    +split: {SB.block_groups(b)
            == List.append(&2, Groups.Group, processed,
                 Groups.Group{fb, ws} <> restg) : +List<Groups.Group>})
    -> {SB.block_groups(b)
        == List.append(&2, Groups.Group,
             List.append(&2, Groups.Group, processed, Groups.Group{fb, ws} <> Nil{}),
             restg) : +List<Groups.Group>}:
  Equal.trans(+List<Groups.Group>,
    SB.block_groups(b),
    List.append(&2, Groups.Group, processed, Groups.Group{fb, ws} <> restg),
    List.append(&2, Groups.Group,
      List.append(&2, Groups.Group, processed, Groups.Group{fb, ws} <> Nil{}), restg),
    split,
    Equal.sym(+List<Groups.Group>,
      List.append(&2, Groups.Group,
        List.append(&2, Groups.Group, processed, Groups.Group{fb, ws} <> Nil{}), restg),
      List.append(&2, Groups.Group, processed, Groups.Group{fb, ws} <> restg),
      SB.group_append(processed, fb, ws, restg)))

# The usable blocks of a guess list, in order. Skipped guesses contribute
# nothing.
def SB.blocks_of_head(+S: +List<+List<Nat>>, +G: +List<+List<Nat>>,
    +g: +List<Nat>, g_in: Tree.WordIn(g, G), b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    restBlocks: +List<SB.Block>) -> +List<SB.Block>:
  match b:
    case True{}:
      Block{G, S, g, g_in,
        Equal.sym(Bool, b, Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), eb)}
      <> restBlocks
    case False{}:
      restBlocks

def SB.blocks_of_G(+S: +List<+List<Nat>>, G: +List<+List<Nat>>) -> +List<SB.Block>:
  match G:
    case Nil{}:
      Nil{}
    case Con{+g, +rest}:
      SB.blocks_of_head(S, G, g, BO.BO.word_in_cons(g, rest),
        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==},
        SB.blocks_of_G(S, rest))

# The body of one block: its class/add pairs followed by End. The schedule of
# the following blocks is already built and is placed after End.
def SB.sched_groups(+b: SB.Block, remaining: +List<Groups.Group>,
    +processed: +List<Groups.Group>, +tail: +List<SB.Block>, +tailSched: SB.Sched,
    +split: {SB.block_groups(b)
            == List.append(&2, Groups.Group, processed, remaining) : +List<Groups.Group>})
    -> SB.Sched:
  match remaining:
    case Nil{}:
      SEnd{b, processed, tail, tailSched, split}
    case Con{gp, +restg}:
      match gp:
        case Groups.Group{+fb, +ws}:
          SClass{b, fb, ws, processed, restg,
            SAdd{b, fb, ws, processed, restg,
              SB.sched_groups(b, restg,
                List.append(&2, Groups.Group, processed, Groups.Group{fb, ws} <> Nil{}),
                tail, tailSched,
                SB.split_after(b, processed, fb, ws, restg, split)),
              split},
            split}

# The schedule of a list of usable blocks. The tail is built first so the
# definition is an ordinary recursion on the block list.
def SB.sched_of_blocks(+S: +List<+List<Nat>>, blocks: +List<SB.Block>) -> SB.Sched:
  match blocks:
    case Nil{}:
      SchedNil{}
    case Con{+b, +rest}:
      +tailSched = SB.sched_of_blocks(S, rest)
      SBegin{b, rest,
        SB.sched_groups(b, SB.block_groups(b), Nil{}, rest, tailSched, {==})}

def SB.sched_cons(+S: +List<+List<Nat>>, +g: +List<Nat>,
    +rest: +List<+List<Nat>>, b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    +tailSched: SB.Sched) -> SB.Sched:
  match b:
    case True{}:
      +groups : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
      +b0 : SB.Block = Block{g <> rest, S, g, BO.BO.word_in_cons(g, rest),
        Equal.sym(Bool, True{}, Groups.groups_smaller(S, groups), eb)}
      +tail : +List<SB.Block> = SB.blocks_of_G(S, rest)
      SBegin{b0, tail,
        SB.sched_groups(b0, groups, Nil{}, tail, tailSched, {==})}
    case False{}:
      tailSched

def SB.sched_of_G(+S: +List<+List<Nat>>, G: +List<+List<Nat>>) -> SB.Sched:
  match G:
    case Nil{}:
      SchedNil{}
    case Con{+g, +rest}:
      +tailSched = SB.sched_of_G(S, rest)
      SB.sched_cons(S, g, rest,
        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==}, tailSched)

# `(xs ++ [x]) ++ ys = xs ++ (x :: ys)` for item lists.
def SB.item_append_singleton(+xs: +List<SolveRef.Item>, x: SolveRef.Item,
    +ys: +List<SolveRef.Item>) ->
  {List.append(&2, SolveRef.Item,
     List.append(&2, SolveRef.Item, xs, x <> Nil{}), ys)
   == List.append(&2, SolveRef.Item, xs, x <> ys)
   : +List<SolveRef.Item>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(+List<SolveRef.Item>, +List<SolveRef.Item>, l => h <> l,
        List.append(&2, SolveRef.Item,
          List.append(&2, SolveRef.Item, t, x <> Nil{}), ys),
        List.append(&2, SolveRef.Item, t, x <> ys),
        SB.item_append_singleton(t, x, ys))

# The items of one block body are its groups followed by End.
def SB.items_groups(+S: +List<+List<Nat>>, +b: SB.Block,
    +remaining: +List<Groups.Group>, +processed: +List<Groups.Group>,
    +tail: +List<SB.Block>, +tailSched: SB.Sched,
    +split: {SB.block_groups(b)
             == List.append(&2, Groups.Group, processed, remaining) : +List<Groups.Group>}) ->
  {SB.items(SB.sched_groups(b, remaining, processed, tail, tailSched, split))
   == List.append(&2, SolveRef.Item, SolveRef.group_items(remaining),
        SolveRef.End{} <> SB.items(tailSched)) : +List<SolveRef.Item>}:
  match remaining:
    case Nil{}:
      {==}
    case Con{gp, +restg}:
      match gp:
        case Groups.Group{+fb, +ws}:
          +split2 : {SB.block_groups(b)
                     == List.append(&2, Groups.Group,
                          List.append(&2, Groups.Group, processed, Groups.Group{fb, ws} <> Nil{}),
                          restg) : +List<Groups.Group>} =
            SB.split_after(b, processed, fb, ws, restg, split)
          +ih : {SB.items(SB.sched_groups(b, restg,
                    List.append(&2, Groups.Group, processed, Groups.Group{fb, ws} <> Nil{}),
                    tail, tailSched, split2))
                == List.append(&2, SolveRef.Item, SolveRef.group_items(restg),
                     SolveRef.End{} <> SB.items(tailSched)) : +List<SolveRef.Item>} =
            SB.items_groups(S, b, restg,
              List.append(&2, Groups.Group, processed, Groups.Group{fb, ws} <> Nil{}),
              tail, tailSched, split2)
          +eq_l : {SB.items(SClass{b, fb, ws, processed, restg,
                       SAdd{b, fb, ws, processed, restg,
                         SB.sched_groups(b, restg,
                           List.append(&2, Groups.Group, processed,
                             Groups.Group{fb, ws} <> Nil{}),
                           tail, tailSched, split2),
                         split},
                       split})
                  == SolveRef.ClassItem{fb, ws}
                     <> (SolveRef.Add{fb}
                          <> SB.items(SB.sched_groups(b, restg,
                               List.append(&2, Groups.Group, processed,
                                 Groups.Group{fb, ws} <> Nil{}),
                               tail, tailSched, split2))) : +List<SolveRef.Item>} =
            {==}
          +eq_r : {SolveRef.ClassItem{fb, ws}
                    <> (SolveRef.Add{fb}
                         <> List.append(&2, SolveRef.Item, SolveRef.group_items(restg),
                              SolveRef.End{} <> SB.items(tailSched)))
                  == List.append(&2, SolveRef.Item, SolveRef.group_items(Groups.Group{fb, ws} <> restg),
                       SolveRef.End{} <> SB.items(tailSched)) : +List<SolveRef.Item>} =
            {==}
          Equal.trans(+List<SolveRef.Item>,
            SB.items(SClass{b, fb, ws, processed, restg,
              SAdd{b, fb, ws, processed, restg,
                SB.sched_groups(b, restg,
                  List.append(&2, Groups.Group, processed,
                    Groups.Group{fb, ws} <> Nil{}),
                  tail, tailSched, split2),
                split}, split}),
            SolveRef.ClassItem{fb, ws}
              <> (SolveRef.Add{fb}
                   <> SB.items(SB.sched_groups(b, restg,
                        List.append(&2, Groups.Group, processed,
                          Groups.Group{fb, ws} <> Nil{}),
                        tail, tailSched, split2))),
            List.append(&2, SolveRef.Item, SolveRef.group_items(Groups.Group{fb, ws} <> restg),
              SolveRef.End{} <> SB.items(tailSched)),
            eq_l,
            Equal.trans(+List<SolveRef.Item>,
              SolveRef.ClassItem{fb, ws}
                <> (SolveRef.Add{fb}
                     <> SB.items(SB.sched_groups(b, restg,
                          List.append(&2, Groups.Group, processed,
                            Groups.Group{fb, ws} <> Nil{}),
                          tail, tailSched, split2))),
              SolveRef.ClassItem{fb, ws}
                <> (SolveRef.Add{fb}
                     <> List.append(&2, SolveRef.Item, SolveRef.group_items(restg),
                          SolveRef.End{} <> SB.items(tailSched))),
              List.append(&2, SolveRef.Item, SolveRef.group_items(Groups.Group{fb, ws} <> restg),
                SolveRef.End{} <> SB.items(tailSched)),
              Equal.cong(+List<SolveRef.Item>, +List<SolveRef.Item>,
                l => SolveRef.ClassItem{fb, ws} <> (SolveRef.Add{fb} <> l),
                SB.items(SB.sched_groups(b, restg,
                  List.append(&2, Groups.Group, processed,
                    Groups.Group{fb, ws} <> Nil{}),
                  tail, tailSched, split2)),
                List.append(&2, SolveRef.Item, SolveRef.group_items(restg),
                  SolveRef.End{} <> SB.items(tailSched)), ih),
              eq_r))

# The items of one block followed by the schedule of the remaining blocks.
def SB.items_block(+S: +List<+List<Nat>>, +b: SB.Block,
    +tail: +List<SB.Block>, +tailSched: SB.Sched) ->
  {SB.items(SBegin{b, tail,
     SB.sched_groups(b, SB.block_groups(b), Nil{}, tail, tailSched, {==})})
   == List.append(&2, SolveRef.Item,
        SolveRef.guess_items(SB.block_g(b), SB.block_groups(b)),
        SB.items(tailSched)) : +List<SolveRef.Item>}:
  +ig : {SB.items(SB.sched_groups(b, SB.block_groups(b), Nil{}, tail, tailSched, {==}))
        == List.append(&2, SolveRef.Item, SolveRef.group_items(SB.block_groups(b)),
             SolveRef.End{} <> SB.items(tailSched)) : +List<SolveRef.Item>} =
    SB.items_groups(S, b, SB.block_groups(b), Nil{}, tail, tailSched, {==})
  +eq1 : {SB.items(SBegin{b, tail,
              SB.sched_groups(b, SB.block_groups(b), Nil{}, tail, tailSched, {==})})
          == SolveRef.Begin{SB.block_g(b)}
             <> List.append(&2, SolveRef.Item, SolveRef.group_items(SB.block_groups(b)),
                  SolveRef.End{} <> SB.items(tailSched)) : +List<SolveRef.Item>} =
    Equal.cong(+List<SolveRef.Item>, +List<SolveRef.Item>,
      l => SolveRef.Begin{SB.block_g(b)} <> l,
      SB.items(SB.sched_groups(b, SB.block_groups(b), Nil{}, tail, tailSched, {==})),
      List.append(&2, SolveRef.Item, SolveRef.group_items(SB.block_groups(b)),
        SolveRef.End{} <> SB.items(tailSched)), ig)
  +e_assoc : {List.append(&2, SolveRef.Item,
                List.append(&2, SolveRef.Item, SolveRef.group_items(SB.block_groups(b)),
                  SolveRef.End{} <> Nil{}),
                SB.items(tailSched))
              == List.append(&2, SolveRef.Item, SolveRef.group_items(SB.block_groups(b)),
                   SolveRef.End{} <> SB.items(tailSched)) : +List<SolveRef.Item>} =
    Eval.Eval.append_assoc_item(SolveRef.group_items(SB.block_groups(b)),
      SolveRef.End{} <> Nil{}, SB.items(tailSched))
  +eq2 : {SolveRef.Begin{SB.block_g(b)}
            <> List.append(&2, SolveRef.Item, SolveRef.group_items(SB.block_groups(b)),
                 SolveRef.End{} <> SB.items(tailSched))
          == List.append(&2, SolveRef.Item,
               SolveRef.guess_items(SB.block_g(b), SB.block_groups(b)),
               SB.items(tailSched)) : +List<SolveRef.Item>} =
    Equal.sym(+List<SolveRef.Item>,
      List.append(&2, SolveRef.Item,
        SolveRef.guess_items(SB.block_g(b), SB.block_groups(b)),
        SB.items(tailSched)),
      SolveRef.Begin{SB.block_g(b)}
        <> List.append(&2, SolveRef.Item, SolveRef.group_items(SB.block_groups(b)),
             SolveRef.End{} <> SB.items(tailSched)),
      Equal.cong(+List<SolveRef.Item>, +List<SolveRef.Item>,
        l => SolveRef.Begin{SB.block_g(b)} <> l,
        List.append(&2, SolveRef.Item,
          List.append(&2, SolveRef.Item, SolveRef.group_items(SB.block_groups(b)),
            SolveRef.End{} <> Nil{}),
          SB.items(tailSched)),
        List.append(&2, SolveRef.Item, SolveRef.group_items(SB.block_groups(b)),
          SolveRef.End{} <> SB.items(tailSched)),
        e_assoc))
  Equal.trans(+List<SolveRef.Item>,
    SB.items(SBegin{b, tail,
      SB.sched_groups(b, SB.block_groups(b), Nil{}, tail, tailSched, {==})}),
    SolveRef.Begin{SB.block_g(b)}
      <> List.append(&2, SolveRef.Item, SolveRef.group_items(SB.block_groups(b)),
           SolveRef.End{} <> SB.items(tailSched)),
    List.append(&2, SolveRef.Item,
      SolveRef.guess_items(SB.block_g(b), SB.block_groups(b)),
      SB.items(tailSched)),
    eq1, eq2)

# The flat schedule of a list of usable blocks.
def SB.flat_blocks(+S: +List<+List<Nat>>, blocks: +List<SB.Block>)
    -> +List<SolveRef.Item>:
  match blocks:
    case Nil{}:
      Nil{}
    case Con{+b, +rest}:
      List.append(&2, SolveRef.Item,
        SolveRef.guess_items(SB.block_g(b), SB.block_groups(b)),
        SB.flat_blocks(S, rest))

def SB.items_blocks(+S: +List<+List<Nat>>, blocks: +List<SB.Block>) ->
  {SB.items(SB.sched_of_blocks(S, blocks)) == SB.flat_blocks(S, blocks)
   : +List<SolveRef.Item>}:
  match blocks:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      +tailSched = SB.sched_of_blocks(S, rest)
      +e1 : {SB.items(SBegin{b, rest, SB.sched_groups(b, SB.block_groups(b), Nil{},
                rest, tailSched, {==})})
            == List.append(&2, SolveRef.Item,
                 SolveRef.guess_items(SB.block_g(b), SB.block_groups(b)),
                 SB.items(tailSched)) : +List<SolveRef.Item>} =
        SB.items_block(S, b, rest, tailSched)
      +ih : {SB.items(tailSched) == SB.flat_blocks(S, rest)
            : +List<SolveRef.Item>} =
        SB.items_blocks(S, rest)
      Equal.trans(+List<SolveRef.Item>,
        SB.items(SBegin{b, rest, SB.sched_groups(b, SB.block_groups(b), Nil{},
          rest, tailSched, {==})}),
        List.append(&2, SolveRef.Item,
          SolveRef.guess_items(SB.block_g(b), SB.block_groups(b)),
          SB.items(tailSched)),
        List.append(&2, SolveRef.Item,
          SolveRef.guess_items(SB.block_g(b), SB.block_groups(b)),
          SB.flat_blocks(S, rest)),
        e1,
        Equal.cong(+List<SolveRef.Item>, +List<SolveRef.Item>,
          l => List.append(&2, SolveRef.Item,
            SolveRef.guess_items(SB.block_g(b), SB.block_groups(b)), l),
          SB.items(tailSched), SB.flat_blocks(S, rest), ih))

# The items of a cons schedule are the block's items followed by the rest.
def SB.items_sched_cons(+S: +List<+List<Nat>>, +g: +List<Nat>,
    +rest: +List<+List<Nat>>, b: Bool,
    +eb: {b == Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) : Bool},
    +tailSched: SB.Sched,
    restEq: {SB.items(tailSched) == SolveRef.mk_schedule(rest, S)
             : +List<SolveRef.Item>}) ->
  {SB.items(SB.sched_cons(S, g, rest, b, eb, tailSched))
   == SolveRef.mk_schedule(g <> rest, S) : +List<SolveRef.Item>}:
  match b:
    case True{}:
      +groups : +List<Groups.Group> = Groups.groups_build(g, S, Nil{})
      +b0 : SB.Block = Block{g <> rest, S, g, BO.BO.word_in_cons(g, rest),
        Equal.sym(Bool, True{}, Groups.groups_smaller(S, groups), eb)}
      +tail : +List<SB.Block> = SB.blocks_of_G(S, rest)
      +e_items : {SB.items(SBegin{b0, tail,
                    SB.sched_groups(b0, groups, Nil{}, tail, tailSched, {==})})
                  == List.append(&2, SolveRef.Item,
                       SolveRef.guess_items(g, groups),
                       SB.items(tailSched)) : +List<SolveRef.Item>} =
        SB.items_block(S, b0, tail, tailSched)
      +e_gs : {Groups.groups_smaller(S, groups) == True{} : Bool} =
        Equal.sym(Bool, True{}, Groups.groups_smaller(S, groups), eb)
      +e_guess : {SolveRef.schedule_guess(g, S) == SolveRef.guess_items(g, groups)
                  : +List<SolveRef.Item>} =
        Equal.cong(Bool, +List<SolveRef.Item>,
          b2 => Feedback.Bool.case(+List<SolveRef.Item>, b2,
            SolveRef.guess_items(g, groups), Nil{}),
          Groups.groups_smaller(S, groups), True{}, e_gs)
      +e_sched : {SolveRef.mk_schedule(g <> rest, S)
                 == List.append(&2, SolveRef.Item,
                      SolveRef.guess_items(g, groups),
                      SolveRef.mk_schedule(rest, S)) : +List<SolveRef.Item>} =
        Equal.cong(+List<SolveRef.Item>, +List<SolveRef.Item>,
          l => List.append(&2, SolveRef.Item, l, SolveRef.mk_schedule(rest, S)),
          SolveRef.schedule_guess(g, S), SolveRef.guess_items(g, groups), e_guess)
      Equal.trans(+List<SolveRef.Item>,
        SB.items(SB.sched_cons(S, g, rest, True{}, eb, tailSched)),
        List.append(&2, SolveRef.Item,
          SolveRef.guess_items(g, groups), SB.items(tailSched)),
        SolveRef.mk_schedule(g <> rest, S),
        e_items,
        Equal.trans(+List<SolveRef.Item>,
          List.append(&2, SolveRef.Item,
            SolveRef.guess_items(g, groups), SB.items(tailSched)),
          List.append(&2, SolveRef.Item,
            SolveRef.guess_items(g, groups), SolveRef.mk_schedule(rest, S)),
          SolveRef.mk_schedule(g <> rest, S),
          Equal.cong(+List<SolveRef.Item>, +List<SolveRef.Item>,
            l => List.append(&2, SolveRef.Item, SolveRef.guess_items(g, groups), l),
            SB.items(tailSched), SolveRef.mk_schedule(rest, S), restEq),
          Equal.sym(+List<SolveRef.Item>,
            SolveRef.mk_schedule(g <> rest, S),
            List.append(&2, SolveRef.Item,
              SolveRef.guess_items(g, groups), SolveRef.mk_schedule(rest, S)),
            e_sched)))
    case False{}:
      +e_gs : {Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})) == False{} : Bool} =
        Equal.sym(Bool, False{}, Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), eb)
      +e_guess : {SolveRef.schedule_guess(g, S) == Nil{} : +List<SolveRef.Item>} =
        Equal.cong(Bool, +List<SolveRef.Item>,
          b2 => Feedback.Bool.case(+List<SolveRef.Item>, b2,
            SolveRef.guess_items(g, Groups.groups_build(g, S, Nil{})), Nil{}),
          Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), False{}, e_gs)
      +e_sched : {SolveRef.mk_schedule(g <> rest, S)
                 == SolveRef.mk_schedule(rest, S) : +List<SolveRef.Item>} =
        Equal.cong(+List<SolveRef.Item>, +List<SolveRef.Item>,
          l => List.append(&2, SolveRef.Item, l, SolveRef.mk_schedule(rest, S)),
          SolveRef.schedule_guess(g, S), Nil{}, e_guess)
      Equal.trans(+List<SolveRef.Item>,
        SB.items(SB.sched_cons(S, g, rest, False{}, eb, tailSched)),
        SB.items(tailSched),
        SolveRef.mk_schedule(g <> rest, S),
        {==},
        Equal.trans(+List<SolveRef.Item>,
          SB.items(tailSched),
          SolveRef.mk_schedule(rest, S),
          SolveRef.mk_schedule(g <> rest, S),
          restEq,
          Equal.sym(+List<SolveRef.Item>,
            SolveRef.mk_schedule(g <> rest, S), SolveRef.mk_schedule(rest, S), e_sched)))

def SB.items_sched(+S: +List<+List<Nat>>, G: +List<+List<Nat>>) ->
  {SB.items(SB.sched_of_G(S, G)) == SolveRef.mk_schedule(G, S)
   : +List<SolveRef.Item>}:
  match G:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      +tailSched = SB.sched_of_G(S, rest)
      SB.items_sched_cons(S, g, rest,
        Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})), {==},
        tailSched, SB.items_sched(S, rest))
