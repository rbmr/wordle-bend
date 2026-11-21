# List facts for the parallel root split.
#
# The split takes the first half with `List.take` and the rest with
# `List.drop`; putting them back together must give the original list, so the
# per-guess work of the two parallel halves covers every guess exactly once.
# `ones` is the sequential list of per-guess results, and appending the results
# of two chunks is the results of the appended chunks.
import Base
import ../src/solve_par.bend as SolvePar
import ../src/solve_ref.bend as SolveRef
import ../src/groups.bend as Groups

# The successor case of `take_drop`, with the induction hypothesis as an
# argument so the computed suffix stays out of the scrutinee.
def ParList.take_drop_cong(+h: +List<Nat>, +t: +List<+List<Nat>>, +p: Nat,
    ih: {List.append(&2, +List<Nat>, List.take(&2, +List<Nat>, t, p),
                      List.drop(&2, +List<Nat>, t, p)) == t : +List<+List<Nat>>}) ->
  {List.append(&2, +List<Nat>, List.take(&2, +List<Nat>, h <> t, 1n+p),
               List.drop(&2, +List<Nat>, h <> t, 1n+p)) == h <> t
   : +List<+List<Nat>>}:
  Equal.cong(+List<+List<Nat>>, +List<+List<Nat>>, l => h <> l,
    List.append(&2, +List<Nat>, List.take(&2, +List<Nat>, t, p),
               List.drop(&2, +List<Nat>, t, p)),
    t, ih)

# `take n` and `drop n` put the list back together.
def ParList.take_drop(+xs: +List<+List<Nat>>, +n: Nat) ->
  {List.append(&2, +List<Nat>, List.take(&2, +List<Nat>, xs, n),
               List.drop(&2, +List<Nat>, xs, n)) == xs
   : +List<+List<Nat>>}:
  match xs n:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      ParList.take_drop_cong(h, t, p, ParList.take_drop(t, p))

def ParList.ones_concat_cong(+g: +List<Nat>, +t: +List<+List<Nat>>,
    +ys: +List<+List<Nat>>, +fuel: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat,
    ih: {SolvePar.ones(fuel, G, S, inf, List.append(&2, +List<Nat>, t, ys))
         == List.append(&2, SolveRef.Best, SolvePar.ones(fuel, G, S, inf, t),
                        SolvePar.ones(fuel, G, S, inf, ys))
         : +List<SolveRef.Best>}) ->
  {SolvePar.ones(fuel, G, S, inf,
      List.append(&2, +List<Nat>, g <> t, ys))
   == List.append(&2, SolveRef.Best, SolvePar.ones(fuel, G, S, inf, g <> t),
                  SolvePar.ones(fuel, G, S, inf, ys))
   : +List<SolveRef.Best>}:
  +e1 : {SolvePar.ones(fuel, G, S, inf,
             List.append(&2, +List<Nat>, g <> t, ys))
         == SolvePar.one(fuel, G, S, inf, g,
      Groups.groups_build(g, S, Nil{}), Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})))
            <> SolvePar.ones(fuel, G, S, inf,
                 List.append(&2, +List<Nat>, t, ys))
         : +List<SolveRef.Best>} = {==}
  +e2 : {SolvePar.one(fuel, G, S, inf, g,
      Groups.groups_build(g, S, Nil{}), Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})))
            <> SolvePar.ones(fuel, G, S, inf,
                 List.append(&2, +List<Nat>, t, ys))
         == SolvePar.one(fuel, G, S, inf, g,
      Groups.groups_build(g, S, Nil{}), Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})))
            <> List.append(&2, SolveRef.Best,
                 SolvePar.ones(fuel, G, S, inf, t),
                 SolvePar.ones(fuel, G, S, inf, ys))
         : +List<SolveRef.Best>} =
    Equal.cong(+List<SolveRef.Best>, +List<SolveRef.Best>,
      l => SolvePar.one(fuel, G, S, inf, g,
      Groups.groups_build(g, S, Nil{}), Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))) <> l,
      SolvePar.ones(fuel, G, S, inf, List.append(&2, +List<Nat>, t, ys)),
      List.append(&2, SolveRef.Best, SolvePar.ones(fuel, G, S, inf, t),
                  SolvePar.ones(fuel, G, S, inf, ys)),
      ih)
  +e3 : {SolvePar.one(fuel, G, S, inf, g,
      Groups.groups_build(g, S, Nil{}), Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})))
            <> List.append(&2, SolveRef.Best,
                 SolvePar.ones(fuel, G, S, inf, t),
                 SolvePar.ones(fuel, G, S, inf, ys))
         == List.append(&2, SolveRef.Best,
              SolvePar.one(fuel, G, S, inf, g,
      Groups.groups_build(g, S, Nil{}), Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))) <> SolvePar.ones(fuel, G, S, inf, t),
              SolvePar.ones(fuel, G, S, inf, ys))
         : +List<SolveRef.Best>} = {==}
  +e4 : {SolvePar.one(fuel, G, S, inf, g,
      Groups.groups_build(g, S, Nil{}), Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))) <> SolvePar.ones(fuel, G, S, inf, t)
         == SolvePar.ones(fuel, G, S, inf, g <> t)
         : +List<SolveRef.Best>} = {==}
  Equal.trans(+List<SolveRef.Best>,
    SolvePar.ones(fuel, G, S, inf, List.append(&2, +List<Nat>, g <> t, ys)),
    List.append(&2, SolveRef.Best,
      SolvePar.one(fuel, G, S, inf, g,
      Groups.groups_build(g, S, Nil{}), Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))) <> SolvePar.ones(fuel, G, S, inf, t),
      SolvePar.ones(fuel, G, S, inf, ys)),
    List.append(&2, SolveRef.Best, SolvePar.ones(fuel, G, S, inf, g <> t),
                SolvePar.ones(fuel, G, S, inf, ys)),
    Equal.trans(+List<SolveRef.Best>,
      SolvePar.ones(fuel, G, S, inf, List.append(&2, +List<Nat>, g <> t, ys)),
      SolvePar.one(fuel, G, S, inf, g,
      Groups.groups_build(g, S, Nil{}), Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})))
        <> List.append(&2, SolveRef.Best,
             SolvePar.ones(fuel, G, S, inf, t),
             SolvePar.ones(fuel, G, S, inf, ys)),
      List.append(&2, SolveRef.Best,
        SolvePar.one(fuel, G, S, inf, g,
      Groups.groups_build(g, S, Nil{}), Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))) <> SolvePar.ones(fuel, G, S, inf, t),
        SolvePar.ones(fuel, G, S, inf, ys)),
      Equal.trans(+List<SolveRef.Best>,
        SolvePar.ones(fuel, G, S, inf, List.append(&2, +List<Nat>, g <> t, ys)),
        SolvePar.one(fuel, G, S, inf, g,
      Groups.groups_build(g, S, Nil{}), Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})))
          <> SolvePar.ones(fuel, G, S, inf, List.append(&2, +List<Nat>, t, ys)),
        SolvePar.one(fuel, G, S, inf, g,
      Groups.groups_build(g, S, Nil{}), Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{})))
          <> List.append(&2, SolveRef.Best,
               SolvePar.ones(fuel, G, S, inf, t),
               SolvePar.ones(fuel, G, S, inf, ys)),
        e1, e2),
      e3),
    Equal.cong(+List<SolveRef.Best>, +List<SolveRef.Best>,
      l => List.append(&2, SolveRef.Best, l, SolvePar.ones(fuel, G, S, inf, ys)),
      SolvePar.one(fuel, G, S, inf, g,
      Groups.groups_build(g, S, Nil{}), Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))) <> SolvePar.ones(fuel, G, S, inf, t),
      SolvePar.ones(fuel, G, S, inf, g <> t),
      Equal.sym(+List<SolveRef.Best>, SolvePar.ones(fuel, G, S, inf, g <> t),
                SolvePar.one(fuel, G, S, inf, g,
      Groups.groups_build(g, S, Nil{}), Groups.groups_smaller(S, Groups.groups_build(g, S, Nil{}))) <> SolvePar.ones(fuel, G, S, inf, t),
                e4)))

# Appending the result lists of two chunks is the result list of the appended
# chunks, in the same order.
def ParList.ones_concat(+fuel: Nat, +G: +List<+List<Nat>>,
    +S: +List<+List<Nat>>, +inf: Nat, +xs: +List<+List<Nat>>,
    +ys: +List<+List<Nat>>) ->
  {SolvePar.ones(fuel, G, S, inf, List.append(&2, +List<Nat>, xs, ys))
   == List.append(&2, SolveRef.Best, SolvePar.ones(fuel, G, S, inf, xs),
                  SolvePar.ones(fuel, G, S, inf, ys))
   : +List<SolveRef.Best>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      ParList.ones_concat_cong(g, t, ys, fuel, G, S, inf,
        ParList.ones_concat(fuel, G, S, inf, t, ys))

