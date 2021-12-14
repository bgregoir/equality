From elpi.apps Require Import derive.
Require Import core_defs  tag fields eqb eqbcorrect eqbP.

#[only(induction,param1_full,param1_trivial)] derive option.
Elpi tag     option.
Elpi fields  option.
Elpi eqb     option.
Elpi eqbcorrect option.
Elpi eqbP option.



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
  
Lemma option_eqb_correct_aux (A : Type) (eqA : A -> A -> bool) :
  let PA := @eqb_correct_on A eqA in
  let P := @eqb_correct_on (option A) (option_eqb A eqA) in
  forall (o : option A) (H:option_is_option A PA o), P o.
Proof.
  move=> PA P.
  apply: (@option_induction A PA P); rewrite /PA /P.
  + apply option_eqb_correct_Some.
  apply option_eqb_correct_None.
Qed.

Lemma option_eqb_correct' (A : Type) (eqA : A -> A -> bool) :
  eqb_correct eqA ->
  eqb_correct (option_eqb A eqA).
Proof.
  move=> H o; apply:option_eqb_correct_aux.
  apply: option_is_option_full; apply H.
Qed.


Inductive t := 
  | T0 
  | T1 of option t.

#[only(induction,param1_functor,param1_trivial)] derive t.
Elpi tag     t.
Elpi fields  t.
Elpi eqb     t.
Elpi eqbcorrect t.

Check t_induction.

Lemma t_eqb_correct_T0 : eqb_correct_on t_eqb T0.
Proof.
  refine 
    (@eqb_body_correct t t_tag t_fields_t t_fields t_construct
      t_constructP (t_eqb_fields t_eqb) T0 (fun x => _)).
  eqb_correct_on__solver.
Qed.

Lemma t_eqb_correct_T1 (o : option t) :
  option_is_option t (eqb_correct_on t_eqb) o -> eqb_correct_on t_eqb (T1 o).
Proof.
  move=> H.
  (* This is the key point. If we don't do it here the tactic eqb_correct_on__solver does not work *)
  have H' := option_eqb_correct_aux _ _ _ H.
  refine 
    (@eqb_body_correct t t_tag t_fields_t t_fields t_construct
      t_constructP (t_eqb_fields t_eqb) (T1 o) (fun x => _)).
  eqb_correct_on__solver.
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




