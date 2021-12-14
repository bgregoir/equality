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

About option_is_option_functor.
About list_is_list_functor.

(* forall (A : Type) (PA1 PA2 : A -> Type),
   (forall x : A, PA1 x -> PA2 x) ->
    forall x : option A, option_is_option A PA1 x -> option_is_option A PA2 x *)

Lemma option_eqb_correct_Some (A:Type) (eqA: A -> A -> bool) (a:A) : 
  eqb_correct_on eqA a -> eqb_correct_on (option_eqb A eqA) (Some a).
Proof.
  move=> H.
  refine 
    (@eqb_body_correct (option A) (option_tag A) (option_fields_t A) (option_fields A) (option_construct A)
      (option_constructP A) (option_eqb_fields A eqA (option_eqb A eqA)) (Some a) (fun x => _)).
  eqb_correct_on__solver.
Qed.

Lemma option_eqb_correct_None (A:Type) (eqA: A -> A -> bool) : 
  eqb_correct_on (option_eqb A eqA) None.
Proof.
  refine 
    (@eqb_body_correct (option A) (option_tag A) (option_fields_t A) (option_fields A) (option_construct A)
      (option_constructP A) (option_eqb_fields A eqA (option_eqb A eqA)) None (fun x => _)).
  eqb_correct_on__solver.
Qed.
  
Lemma option_eqb_correct_aux (A : Type) (eqA : A -> A -> bool) (o : option A) :
     @option_is_option A          (@eqb_correct_on A eqA) o  ->
     @eqb_correct_on   (option A) (option_eqb A eqA)      o.
Proof.
  refine (@option_induction A _ _ (option_eqb_correct_Some A eqA)
                                  (option_eqb_correct_None A eqA) o).
Qed.

Lemma option_eqb_correct' (A : Type) (eqA : A -> A -> bool) :
  eqb_correct eqA ->
  eqb_correct (option_eqb A eqA).
Proof.
  move=> H o; apply:option_eqb_correct_aux.
  apply: option_is_option_full; apply H.
Qed.




Lemma list_eqb_correct_aux (A : Type) (eqA : A -> A -> bool) (o : list A) :
     @list_is_list     A          (@eqb_correct_on A eqA) o  ->
     @eqb_correct_on   (list A)   (list_eqb A eqA)        o.
Admitted.

Inductive t := 
  | T0 
  | T1 of option (list (option t)).

#[only(induction,param1_functor,param1_trivial)] derive t.
Elpi tag     t.
Elpi fields  t.
Elpi eqb     t.
(* Elpi eqbcorrect t. *)

Lemma t_eqb_correct_T0 : eqb_correct_on t_eqb T0.
Proof.
  refine 
    (@eqb_body_correct t t_tag t_fields_t t_fields t_construct
      t_constructP (t_eqb_fields t_eqb) T0 (fun x => _)).
  eqb_correct_on__solver.
Qed.

Lemma t_eqb_correct_T1 (o : option (list (option t))) :
  option_is_option (list (option t))
    (list_is_list (option t)
      (option_is_option t (eqb_correct_on t_eqb))) o ->
   eqb_correct_on t_eqb (T1 o).
Proof.
  move=> H.

  refine 
  (@eqb_body_correct t t_tag t_fields_t t_fields t_construct
    t_constructP (t_eqb_fields t_eqb) (T1 o) (fun x => _)).
  rewrite /= => W.
  congr (Some (T1 _)).
  move: x W.
  change (eqb_correct_on (option_eqb _ (list_eqb (option t) (option_eqb t t_eqb))) o).

  apply option_eqb_correct_aux.
  move: o H; apply option_is_option_functor => o H.
  apply list_eqb_correct_aux.
  move: o H; apply list_is_list_functor => o H.
  apply option_eqb_correct_aux.
  by [].
(*
  refine 
    (@eqb_body_correct t t_tag t_fields_t t_fields t_construct
      t_constructP (t_eqb_fields t_eqb) (T1 o) (fun x => _)).
  eqb_correct_on__solver.
  *)
Qed.

Lemma t_eqb_correct_aux :
  let P := @eqb_correct_on t t_eqb in
  forall x : t, t_is_t x -> P x.
Proof.
  move=> P.
  apply: (@t_induction P); rewrite /P.
  + apply t_eqb_correct_T0.
  apply t_eqb_correct_T1.
Qed.

Lemma t_eqb_correct : eqb_correct t_eqb.
Proof.
  move=> t; apply t_eqb_correct_aux.
  apply t_is_t_full.
Qed.




