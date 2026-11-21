# The sizes of the feedback groups.
#
# `groups_smaller` checks that every class is strictly shorter than the
# candidate list, which is what lets the solver recurse with less fuel. This
# module turns the boolean check into a proof-carrying list, one bound per
# group, so the validity induction can read the bound for the group it is
# looking at.
import Base
import ../src/groups.bend as Groups
import ./logic.bend as Logic
import ./nat.bend as NatProof

def GM.GroupsSmaller(+S: +List<+List<Nat>>,
    +groups: +List<Groups.Group>) -> Type:
  match groups:
    case Nil{}:
      Unit
    case Con{gp, rest}:
      match gp:
        case Groups.Group{f, ws}:
          {Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)) == True{} : Bool}
          & GM.GroupsSmaller(S, rest)

def GM.groups_smaller_sound(+S: +List<+List<Nat>>,
    +groups: +List<Groups.Group>,
    +e: {Groups.groups_smaller(S, groups) == True{} : Bool}) ->
  GM.GroupsSmaller(S, groups):
  match groups:
    case Nil{}:
      Unit{}
    case Con{gp, rest}:
      match gp:
        case Groups.Group{+f, +ws}:
          (Logic.Proof.and_true_l(
             Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)),
             Groups.groups_smaller(S, rest), e),
           GM.groups_smaller_sound(S, rest,
             Logic.Proof.and_true_r(
               Nat.is_lt(Groups.len_words(ws), Groups.len_words(S)),
               Groups.groups_smaller(S, rest), e)))
