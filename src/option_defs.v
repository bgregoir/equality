From elpi.apps Require Import derive.
Require Import core_defs  tag fields eqb eqbcorrect eqbP.

#[verbose,only(induction,param1_functor,param1_trivial)] derive option.
Elpi tag     option.
Elpi fields  option.
Elpi eqb     option.
Elpi eqbcorrect option.
Elpi eqbP option.

#[verbose,only(induction,param1_functor,param1_trivial)] derive list.
Elpi tag     list.
Elpi fields  list.
Elpi eqb     list.
Elpi eqbcorrect list.
Elpi eqbP list.

Lemma list_eqb_refl_aux (A : Type) (eqA : A -> A -> bool) (o : list A) :
     @list_is_list     A          (@eqb_refl_on A eqA) o  ->
     @eqb_refl_on   (list A)   (list_eqb A eqA)        o.
Admitted.

Lemma option_eqb_refl_aux (A : Type) (eqA : A -> A -> bool) (o : option A) :
     @option_is_option A          (@eqb_refl_on A eqA) o  ->
     @eqb_refl_on   (option A) (option_eqb A eqA)      o.
Proof.
Admitted.


Inductive t := 
  | T0 
  | T1 of option (list (option t)).



Elpi Accumulate eqcorrect.db lp:{{


   % correct-lemma-for {{:gref list }} {{ list_eqb_correct_aux }}.
   % correct-lemma-for {{:gref option }} {{ option_eqb_correct_aux }}.

   functor-lemma-for {{:gref list }} {{ list_is_list_functor }}.
   functor-lemma-for {{:gref option }} {{ option_is_option_functor }}.



/*
  :before "eqb-correct-aux-for:default"
  eqb-correct-aux-for {{ list lp:X }}
                      {{ fun x H => list_eqb_correct_aux _ _ x (list_is_list_functor _ _ _ lp:Rec x H) }} :-
    eqb-correct-aux-for X Rec.

  :before "eqb-correct-aux-for:default"
  eqb-correct-aux-for {{ option lp:X }}
                      {{ fun x H => option_eqb_correct_aux _ _ x (option_is_option_functor _ _ _ lp:Rec x H) }} :-
    eqb-correct-aux-for X Rec.

*/

  :before "eqb-refl-aux-for:default"
  eqb-refl-aux-for {{ list lp:X }}
                      {{ fun x H => list_eqb_refl_aux _ _ x (list_is_list_functor _ _ _ lp:Rec x H) }} :-
    eqb-refl-aux-for X Rec.

  :before "eqb-refl-aux-for:default"
  eqb-refl-aux-for {{ option lp:X }}
                      {{ fun x H => option_eqb_refl_aux _ _ x (option_is_option_functor _ _ _ lp:Rec x H) }} :-
    eqb-refl-aux-for X Rec.

}}.

#[only(induction,param1_functor,param1_trivial)] derive t.
Elpi tag     t.
Elpi fields  t.
Elpi eqb     t.
Elpi eqbcorrect t.
Elpi eqbP t.

Import eqtype.

Check (forall x : t, x == x).


