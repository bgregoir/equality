Require Import Eqdep_dec.
Require Import PArith.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope positive_scope.

Section Section.
Context {A:Type}.

Definition eqb_correct_on (eqb : A -> A -> bool) (a1:A) := 
   forall a2, eqb a1 a2 -> a1 = a2.

Definition eqb_refl_on (eqb : A -> A -> bool) (a:A) := 
  eqb a a.

Definition eqb_correct (eqb : A -> A -> bool) := 
  forall  (a1:A) a2, eqb a1 a2 -> a1 = a2.

Definition eqb_reflexive (eqb : A -> A -> bool) := forall (a:A),
  eqb a a.
 
Lemma iffP2 (f : A -> A -> bool) (H1 : eqb_correct f) (H2 : eqb_reflexive f)
 (x1 x2 : A) : reflect (x1 = x2) (f x1 x2).
Proof. apply (iffP idP);[ apply H1 | move->; apply H2 ]. Qed.

Definition eqax_on (eqb : A -> A -> bool) (a1:A) := 
   forall a2, reflect (a1 = a2) (eqb a1 a2).

Variable tag       : A -> positive.
Variable fields_t  : positive -> Type.
Variable fields    : forall a, fields_t (tag a).
Variable construct : forall t, fields_t t -> option A.
Variable constructP : forall a, construct (fields a) = Some a.

Variable eqb_fields : forall t, fields_t t -> fields_t t -> bool.

Definition eqb_body (t1:positive) (f1:fields_t t1) (x2:A) := 
  let t2 := tag x2 in
  match Pos.eq_dec t2 t1 with
  | left heq => 
    let f2 := fields x2 in
    @eqb_fields t1 f1 (@eq_rect positive t2 fields_t f2 t1 heq)
  | right _ => false 
  end.

Definition eqb_fields_correct_on (a:A) := 
  forall f : fields_t (tag a), 
    eqb_fields (fields a) f -> Some a = construct f.

Lemma eqb_body_correct a1 : 
  eqb_fields_correct_on a1 ->
  forall a2, eqb_body (fields a1) a2 -> a1 = a2.
Proof.
  move=> hf a2 hb.
  suff : Some a1 = Some a2 by move=> [->].
  rewrite -(constructP a2); move: hb; rewrite /eqb_body.
  case: Pos.eq_dec => // heq.
  move: (tag a2) heq (fields a2) => t2 ?; subst t2 => f2 /=; apply hf.
Qed.

Definition eqb_fields_refl_on (a:A) := 
  eqb_fields (fields a) (fields a).

Lemma eqb_body_refl a : 
  eqb_fields_refl_on a -> 
  eqb_body (fields a) a.
Proof.
  rewrite /eqb_body => hf.
  case: Pos.eq_dec => // heq.
  have -> /= := Eqdep_dec.UIP_dec Pos.eq_dec heq erefl; apply hf.
Qed.

End Section.

