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
  by repeat (reflexivity || apply/andP; split; assumption).

Elpi Db eqcorrect.db lp:{{

  pred eqcorrect-for
    o:inductive,
    o:constant, % correct
    o:constant. % reflexive
    
    pred what-for i:(gref -> term -> prop), i:(term -> term -> prop), i:term, o:term.
    pred eqb-correct-aux-for i:term, o:term.
    eqb-correct-aux-for T R :-
      what-for correct-lemma-for eqb-correct-aux-for T R.

    pred eqb-refl-aux-for i:term, o:term.

  /* JC HERE 

  pred eqb-correct-aux-for o:term, o:term.
  eqb-correct-aux-for
    {{ @eq_correct_on lp:T lp:F }}
    {{ (fun (a : lp:T) (H : @eq_correct_on lp:T lp:F) => H) }}.
  %
  eqb-correct-aux-for
    {{ option_is_option lp:T (@eqb_correct_on _ _) }}
    {{ (fun (a : lp:T) (H : option_eqb_correct_aux lp:T lp:Cmp }}.
  eqb-correct-aux-for
    {{ option_is_option lp:T lp:P }}
    {{ fun x H => option_is_option_functor lp:T _ (@eqb_correct_on _ _) (lp:Rec x H) }} :-
    eqb-correct-aux-for P Rec.

  
  eqb-correct-aux-for {{ list_is_list lp:A lp:P }} {{ list_eqb_correct_aux ... }} :-
    eqb-correct-aux-for P X.

    option_is_option (list A) (list_is_list A (eqb_correct_on A FA))

  :name "eqb-correct-aux-for:default"
  eqb-correct-aux-for T {{ fun (x : lp:T) H => H }}.
  */
  :name "eqb-refl-aux-for:default"
  eqb-refl-aux-for T {{ fun (x : lp:T) H => H }}.



}}.
      
Elpi Command eqbcorrect.
Elpi Accumulate Db tag.db.
Elpi Accumulate Db eqb.db.
Elpi Accumulate Db fields.db.
Elpi Accumulate Db eqcorrect.db.
Elpi Accumulate Db derive.induction.db.
Elpi Accumulate Db derive.param1.inhab.db.
(*Elpi Accumulate Db derive.param1.functor.db. bad db shape *)
Elpi Accumulate File "src/elpi-ltac.elpi".
Elpi Accumulate File "src/eqbcorrect.elpi".
Elpi Accumulate File "src/paramX-lib.elpi".
Elpi Accumulate File "src/param1.elpi".
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate lp:{{
  main [str S] :-
    std.assert! (coq.locate S (indt I)) "Not an inductive type",
    Prefix is S ^ "_",
    eqbcorrect.main I Prefix _.
}}.
Elpi Typecheck.

Elpi Print eqbcorrect.