From elpi.apps Require Import derive.
Require Import core_defs tag fields eqb eqbcorrect eqbP.

Set Implicit Arguments.

#[only(induction,param1_full,param1_trivial)] derive list.
Elpi tag     list.
Elpi fields  list.
Elpi eqb     list.
Elpi eqbcorrect list.
Elpi eqbP list.


#[only(induction,param1_full,param1_trivial)] derive nat.
Elpi tag     nat.
Elpi fields  nat.
Elpi eqb     nat.
Elpi eqbcorrect nat.
Elpi eqbP nat.

From mathcomp Require Import eqtype.
Goal (cons 1 nil == nil).
unfold eq_op.
unfold list_eqbP, list_eqb.
Abort.
