
From elpi.apps Require Import derive.
Require Import core_defs  tag fields eqb eqbcorrect eqbP.

Require Import option_defs.

Inductive t := 
  | T0 
  | T1 of option t.


#[only(induction,param1_functor,param1_trivial)] derive t.
About t_induction.
Elpi tag     t.
Elpi fields  t.
Elpi eqb     t.

Lemma option_some_correct :
  forall (A : Type) (eqA : A -> A -> bool),
    let PA := @eqb_correct_on A eqA in
    let P := @eqb_correct_on (option A) (@option_eqb A eqA) in
 forall s1 : option A, option_is_option A PA s1 -> P s1.
move=> A eqA PA P o.
apply: option_induction.
  move=> x Px.
Admitted.

reali A PA =>
  reali (list A) P => 

   option (list A)   ----< option_is_option A P
   option (box A)   ----< option_is_option A (box_is_box A PA)



Lemma T1_correct :
    let P := @eqb_correct_on t t_eqb in
    forall s1 : t, t_is_t s1 -> P s1.
move=> P s1.
apply: t_induction.
  move=> x Px. admit.
  move=> x Px.
  have H := @option_some_correct t t_eqb _ Px.
  rewrite /P.
  apply: @eqb_body_correct _ _ _ _ t_construct _ _ _ _.
  apply: t_constructP.
  rewrite /eqb_fields_correct_on /= -/t_eqb => y H1.
  by rewrite (H _ H1).


About option_induction.



About option_eqb_correct.
About t_induction.

   
   

  (forall x : option t, option_is_option t (eqb_correct_on t_eqb) x ->
     (eqb_correct_on t_eqb) (T1 x)) ->

  (forall x : option t, option_is_option (option_eqb t t_eqb) x ->
     (eqb_correct_on t_eqb) (T1 x)




Elpi eqbcorrect t.
Elpi eqbP t.
  
rec (t -> P)
IH : list t -> list_is_list P
bool -> bool_is_bool

x : T
rec : P x

IH -> (list_is_list P -> list_is_list Q)


(*







Section Ind.

  Context (Po : option t -> Prop) (P : t -> Prop).
  Context (Hnone : Po None) (Hsome: forall t, P t -> Po (Some t))
          (HT0 : P T0) (HT1 : forall o, Po o -> P (T1 o)).

  Fixpoint t_Ind (x : t) : P x := 
    match x with 
    | T0 => HT0
    | T1 o => @HT1 o (@option_defs.option_Ind t P Po t_Ind Hnone Hsome o)
    end.

End Ind.

Module AUX.

Definition tag (x : t) := 
  match x with
  | T0     => 1
  | T1 _   => 2
  end.

Definition fields_t (p:positive) : Type := 
  match p with
  | 2 => option t  
  | _ => unit
  end.

Definition fields (x:t) : fields_t (tag x) := 
  match x return fields_t (tag x) with
  | T0 => tt
  | T1 o => o
  end.

Definition construct (p:positive) : fields_t p -> option t := 
  match p with
  | 1 => fun _ => Some T0 
  | 2 => fun o => Some (T1 o)
  | _ => fun _ => None
  end.

Lemma constructP x : construct (fields x) = Some x.
Proof. by case: x. Qed.

End AUX.

Local Instance t_obj : @obj t := 
  {| tag        := AUX.tag
   ; fields_t   := AUX.fields_t
   ; fields     := AUX.fields
   ; construct  := AUX.construct
   ; constructP := AUX.constructP |}.

Section Fields.

Context (eqb : t -> t -> bool).

Definition eqb_fields (p:positive) : fields_t p -> fields_t p -> bool := 
  match p return fields_t p -> fields_t p -> bool with
  | 1 => eq_op
  | 2 => @option_defs.eqb t eqb
  | _ => eq_op 
  end.

End Fields.

Fixpoint eqb (x1 x2:t) := 
  match x1 with
  | T0   => eqb_body (eqb_fields eqb) (t1:=1) tt x2
  | T1 o => eqb_body (eqb_fields eqb) (t1:=2) o x2
  end.

Lemma eqb_correct_on_T0 : eqb_correct_on eqb T0.
Proof. 
  rewrite /eqb_correct_on /=.
  by apply (@eqb_body_correct _ t_obj (eqb_fields eqb) T0).
Qed.

Lemma eqb_correct_on_T1 (o : option t) : 
  eqb_correct_on (option_defs.eqb eqb) o -> eqb_correct_on eqb (T1 o).
Proof.
  rewrite /eqb_correct_on /=.
  move=> h; apply (@eqb_body_correct _ t_obj (eqb_fields eqb) (T1 o)).
  by rewrite /eqb_fields_correct_on /= => ? /h ->.
Qed.

Lemma eqb_correct (x1 x2: t) : eqb x1 x2 -> x1 = x2.
Proof.
  apply (@t_Ind (eqb_correct_on (option_defs.eqb eqb)) (eqb_correct_on eqb)) => {x1 x2}.
  + by apply option_defs.eqb_correct_on_None.  
  + by apply option_defs.eqb_correct_on_Some.
  + by apply eqb_correct_on_T0.
  by apply eqb_correct_on_T1.
Qed.

Lemma eqb_refl_on_T0 : eqb_refl_on eqb T0.
Proof. done. Qed.

Lemma eqb_refl_on_T1 (o : option t) : 
  eqb_refl_on (option_defs.eqb eqb) o -> eqb_refl_on eqb (T1 o).
Proof. apply (@eqb_body_refl _ t_obj (eqb_fields eqb) (T1 o)). Qed.

Lemma eqb_refl (x:t) : eqb x x.
Proof.
  apply (@t_Ind (eqb_refl_on (option_defs.eqb eqb)) (eqb_refl_on eqb)) => {x}.
  + by apply option_defs.eqb_refl_on_None.
  + by apply option_defs.eqb_refl_on_Some.
  + by apply eqb_refl_on_T0.
  apply eqb_refl_on_T1.
Qed.

Lemma eqbP x1 x2 : reflect (x1 = x2) (eqb x1 x2).
Proof. apply (iffP idP);[ apply eqb_correct | move=> ->; apply eqb_refl]. Qed.

*)
