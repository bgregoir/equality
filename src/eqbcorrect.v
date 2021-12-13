From elpi Require Import elpi.
From elpi.apps Require Import derive.

From Coq Require Import PArith ssreflect ssrfun ssrbool.
Open Scope positive_scope.

Require Import core_defs.
Require Export tag fields eqb.

Export ssreflect ssrbool ssrfun. (* otherwise the tactic fails *)
Ltac eqb_correct_on__solver :=
  by repeat (try case/andP; match reverse goal with H : @eqb_correct_on _ _ _ |- _ => move=> /=/H{H}-> end).
Ltac eqb_refl_on__solver :=
  rewrite /eqb_fields_refl_on /=;
  repeat
    (reflexivity || apply/andP; split; assumption).

Elpi Db eqcorrect.db lp:{{

  pred eqcorrect-for
    o:inductive,
    o:constant, % correct
    o:constant. % reflexive
  
}}.
      
Elpi Command eqbcorrect.
Elpi Accumulate Db eqb.db.
Elpi Accumulate Db fields.db.
Elpi Accumulate Db eqcorrect.db.
Elpi Accumulate Db derive.induction.db.
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.inhab.db.
Elpi Accumulate File "src/elpi-ltac.elpi".
Elpi Accumulate File "src/eqbcorrect.elpi".
Elpi Accumulate lp:{{
  main [str S] :-
    std.assert! (coq.locate S (indt I)) "Not an inductive type",
    Prefix is S ^ "_",
    eqbcorrect.main I Prefix _.
}}.
Elpi Typecheck.
