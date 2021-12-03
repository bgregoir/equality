Require Import Eqdep_dec.

From mathcomp Require Import all_ssreflect.
Require Import core_defs tag fields eqb.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import PArith.
Open Scope positive_scope.

Elpi tag list.
Definition tag {A} := @list_tag A.

Elpi fields list.
Definition fields_t {A} := @list_fields_t A.

Definition fields {A} := @list_fields A.

Definition construct {A} := @ list_construct A.

Definition constructP {A} := @list_constructP A.

Elpi eqb list.
Print list_eqb_fields.

Definition eqb_fields := list_eqb_fields.

About eqb_body.
Definition list_eqb A (eqA : A -> A -> bool) := fix eqb (x1 x2 : list A) :=
  match x1 with
  | [::] => @eqb_body (list A) (@list_tag A) (@list_fields_t A) (@list_fields A) (@list_eqb_fields A eqA eqb) (@list_tag A [::]) tt x2
  | a::l => @eqb_body (list A) (@list_tag A) (@list_fields_t A) (@list_fields A) (@list_eqb_fields A eqA eqb) (@list_tag A (a::l)) (a,l) x2
  end.

Ltac eqb_correct_on__solver :=
  by repeat (try case/andP; match goal with H : eqb_correct_on _ _ |- _ => move=> /=/H-> end).


Lemma eqb_correct_on_nil A (eqA : A -> A -> bool) : eqb_correct_on (list_eqb eqA) nil.
Proof.
  refine (
    @eqb_body_correct (list A) (@list_tag A) (@list_fields_t A) (@list_fields A) (@list_construct A) (@list_constructP A)
      (@list_eqb_fields A eqA (@list_eqb A eqA))
      [::] _).
  eqb_correct_on__solver.
Qed.

Lemma eqb_correct_on_cons A (eqA : A -> A -> bool): 
   forall a, eqb_correct_on eqA a -> 
   forall l, eqb_correct_on (list_eqb eqA) l -> 
   eqb_correct_on (list_eqb eqA) (a :: l).
Proof.
  refine (fun a P1 l P2 =>
    @eqb_body_correct (list A) (@list_tag A) (@list_fields_t A) (@list_fields A) (@list_construct A) (@list_constructP A)
      (@list_eqb_fields A eqA (@list_eqb A eqA))
      (a::l) (fun f => _)). 
  eqb_correct_on__solver.
Qed.


Ltac eqb_refl_on__solver :=
  rewrite /eqb_fields_refl_on /=;
  repeat
    (reflexivity || apply/andP; split; assumption).

Lemma eqb_refl_on_nil A (eqA : A -> A -> bool) : eqb_refl_on (list_eqb eqA) [::].
Proof.
  refine (
  (@eqb_body_refl _ _ _ _ (@list_eqb_fields A eqA (list_eqb eqA)) [::]) _).
  eqb_refl_on__solver.
Qed.

Lemma eqb_refl_on_cons A (eqA : A -> A -> bool):
  forall a, eqb_refl_on eqA a -> 
  forall l, eqb_refl_on (list_eqb eqA) l -> 
  eqb_refl_on (list_eqb eqA) (a :: l).
Proof. 
  refine (fun a ha l hl =>
   (@eqb_body_refl _ _ _ _ (@list_eqb_fields A eqA (list_eqb eqA)) (a :: l)) _).
   eqb_refl_on__solver.
Qed.


From elpi.apps Require Import derive.
#[only(induction,param1_full,param1_trivial)] derive list.

Lemma list_eqb_correct (A:Type) (eqA: A -> A -> bool) (eqAc : eqb_correct eqA)
  (x:list A) : eqb_correct_on (list_eqb eqA) x.
Proof.
  refine (@list_induction _ _ _
              (@eqb_correct_on_nil A eqA)
              (@eqb_correct_on_cons A eqA)
              x (@list_is_list_full _ _ eqAc x)).
Qed.

Lemma list_eqb_refl (A:Type) (eqA: A -> A -> bool) (eqAr : @eqb_reflexive A eqA)
  (x:list A) : eqb_refl_on (list_eqb eqA) x.
Proof.
  refine (@list_induction _ _ _
              (@eqb_refl_on_nil A eqA)
              (@eqb_refl_on_cons A eqA)
              x (@list_is_list_full _ _ eqAr x)).
Qed.

Lemma list_eqbP (A:Type) (eqA: A -> A -> bool)
 (eqAc : eqb_correct eqA)
 (eqAr : eqb_reflexive eqA) 
: forall (x1 x2 : list A), reflect (x1 = x2) (list_eqb eqA x1 x2).
Proof. refine (iffP2 (list_eqb_correct eqAc) (list_eqb_refl eqAr)). Qed.


