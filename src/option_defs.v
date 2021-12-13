From elpi.apps Require Import derive.
Require Import core_defs  tag fields eqb eqbcorrect eqbP.

#[only(induction,param1_full,param1_trivial)] derive option.
Elpi tag     option.
Elpi fields  option.
Elpi eqb     option.
Elpi eqbcorrect option.
Elpi eqbP option.

Check option_eqbP : eqtype.Equality.type -> eqtype.Equality.type.


