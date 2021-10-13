Require Import Eqdep_dec.

From mathcomp Require Import all_ssreflect.
Require Import core_defs  tag fields.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import PArith.
Open Scope positive_scope.

Section Ind.

  Context (A : Type) (PA : A -> Prop) (P : option A -> Prop).
  Context (A_ind : forall a, PA a) (Hnone : P None) (Hsome : forall a, PA a -> P (Some a)).

  Definition option_Ind (o : option A) : P o := 
    match o with
    | None => Hnone
    | Some a => Hsome (A_ind a)
    end.

End Ind.

Module AUX.

Section Section.
Context {A : Type}.

Elpi tag option.
Definition tag {A} := @option_tag A. (*(x : option A) := 
  match x with
  | None     => 1
  | Some _   => 2
  end.
*)

Elpi fields option.
Definition fields_t := @option_fields_t A. (*(t:positive) : Type := 
  match t with
  | 1 => A  
  | _ => unit
  end.*)

Definition fields := @option_fields A. (* (x:option A) : fields_t (tag x) := 
  match x return fields_t (tag x) with
  | None => tt
  | Some a => a
  end.*)

Definition construct := @option_construct A. (* (t:positive) : fields_t t -> option (option A) := 
  match t with
  | 1 => fun a => Some (Some a)
  | 2 => fun _ => Some None 
  | _ => fun _ => None
  end.*)

Lemma constructP x : construct (fields x) = Some x.
Proof. by case: x. Qed.

End Section. End AUX.

Local Instance option_obj (A:Type) : @obj (option A) := 
  {| tag        := AUX.tag
   ; fields_t   := AUX.fields_t
   ; fields     := AUX.fields
   ; construct  := AUX.construct
   ; constructP := AUX.constructP |}.

Section Section.

Context (A:Type) (Aeqb : A -> A -> bool).

Definition eqb_fields (t:positive) : fields_t t -> fields_t t -> bool := 
  match t return fields_t t -> fields_t t -> bool with
  | 1 => Aeqb
  | 2 => eq_op
  | _ => eq_op
  end.

Definition eqb (x1 x2:option A) := 
  match x1 with
  | Some a => eqb_body eqb_fields (t1:=1) a x2
  | None => eqb_body eqb_fields (t1:=2) tt x2
  end.

Lemma eqb_correct_on_None : eqb_correct_on eqb None.
Proof.
  rewrite /eqb_correct_on /eqb.
  by apply (@eqb_body_correct _ (option_obj A) eqb_fields None).
Qed.

Lemma eqb_correct_on_Some a : 
   eqb_correct_on Aeqb a -> 
   eqb_correct_on eqb (Some a).
Proof.
  rewrite /eqb_correct_on /eqb => ha.
  apply (@eqb_body_correct _ (option_obj A) eqb_fields (Some a)).
  by move=> a2 /ha ->.
Qed.

Lemma eqb_refl_on_None : eqb_refl_on eqb None.
Proof. done. Qed.

Lemma eqb_refl_on_Some a :
  eqb_refl_on Aeqb a -> 
  eqb_refl_on eqb (Some a).
Proof. apply (@eqb_body_refl _ (option_obj A) eqb_fields (Some a)). Qed.

End Section.

Section EqType.

Context (A:eqType).

Lemma eqb_correct (x:option A) : eqb_correct_on (eqb eq_op) x.
Proof.
  case: x => [ a | ].
  + by apply/eqb_correct_on_Some => x'; apply /eqP.
  apply eqb_correct_on_None.
Qed.

Lemma eqb_refl (x:option A) : eqb_refl_on (eqb eq_op) x.
Proof.
  case: x => [ a | ].
  + by apply/eqb_refl_on_Some/eqxx.
  apply eqb_refl_on_None.
Qed.

Lemma eqbP (x1 x2 : option A) : reflect (x1 = x2) (eqb eq_op x1 x2).
Proof. apply (iffP idP);[ apply eqb_correct | move=> ->; apply eqb_refl]. Qed.

End EqType.

