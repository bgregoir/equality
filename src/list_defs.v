Require Import Eqdep_dec.

From mathcomp Require Import all_ssreflect.
Require Import core_defs tag fields eqb.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import PArith.
Open Scope positive_scope.

Section Ind.

  Context (A : Type) (PA : A -> Prop) (P : list A -> Prop).
  Context (A_ind : forall a, PA a) (Hnil : P [::]) (Hcons : forall a l, PA a -> P l -> P (a::l)).

  Fixpoint list_Ind (l : list A) : P l := 
    match l with
    | [::] => Hnil
    | a :: l => Hcons (A_ind a) (list_Ind l)
    end.

End Ind.

Module AUX.

Section Section.
Context {A : Type}.

Elpi tag list.
Definition tag {A} := @list_tag A. (*
Definition tag (x : list A) := 
  match x with
  | [::]     => 1
  | _ :: _   => 2
  end.
*)

Elpi fields list.
Definition fields_t := @list_fields_t A. (*(t : positive) : Type := 
  match t with
  | 2 => (A * list A)%type
  | _ => unit
  end.
*)

Definition fields := @list_fields A. (*(x : list A) : fields_t (tag x) := 
  match x return fields_t (tag x) with
  | [::] => tt
  | a::l => (a, l)
  end.*)

Definition construct := @ list_construct A. (*(t:positive) : fields_t t -> option (list A) := 
  match t with
  | 1 => fun _ => Some [::] 
  | 2 => fun p => Some (p.1 :: p.2)
  | _ => fun _ => None
  end.*)

Definition constructP := @list_constructP A. (*x : construct (fields x) = Some x.
Proof. by case: x. Qed.*)

End Section. End AUX.

Local Instance list_obj (A:Type) : @obj (list A) := 
  {| tag        := AUX.tag
   ; fields_t   := AUX.fields_t
   ; fields     := AUX.fields
   ; construct  := AUX.construct
   ; constructP := AUX.constructP |}.

Section Section.

Context (A:Type) (Aeqb : A -> A -> bool).

Section Fields.

Context (eqb : list A -> list A -> bool).

Elpi eqb list.

Definition eqb_fields (t:positive) : fields_t t -> fields_t t -> bool := 
  match t return fields_t t -> fields_t t -> bool with
  | 1 => eq_op
  | 2 => fun p1 p2 => Aeqb p1.1 p2.1 && eqb p1.2 p2.2
  | _ => eq_op
  end.

End Fields.

Fixpoint eqb (x1 x2 : list A) := 
  match x1 with
  | [::] => eqb_body (eqb_fields eqb) (t1:=1) tt x2
  | a::l => eqb_body (eqb_fields eqb) (t1:=2) (a,l) x2
  end.

Lemma eqb_correct_on_nil : eqb_correct_on eqb nil.
Proof.
  rewrite /eqb_correct_on /eqb.
  by apply (@eqb_body_correct _ (list_obj A) (eqb_fields eqb) [::]).
Qed.

Lemma eqb_correct_on_cons a l: 
   eqb_correct_on Aeqb a -> 
   eqb_correct_on eqb l -> 
   eqb_correct_on eqb (a :: l).
Proof.
  rewrite /eqb_correct_on => ha hl.
  apply (@eqb_body_correct _ (list_obj A) (eqb_fields eqb) (a :: l)).
  by move=> a2 /andP[] /= /ha -> /hl ->.
Qed.

Lemma eqb_refl_on_nil : eqb_refl_on eqb [::].
Proof. done. Qed.

Lemma eqb_refl_on_cons a l:
  eqb_refl_on Aeqb a -> 
  eqb_refl_on eqb l -> 
  eqb_refl_on eqb (a :: l).
Proof. 
  rewrite /eqb_refl_on=> ha hl.
  apply (@eqb_body_refl _ (list_obj A) (eqb_fields eqb) (a :: l)). 
  by rewrite /eqb_fields_refl_on /= ha hl.
Qed.

End Section.

Section EqType.

Context (A:eqType).

Lemma eqb_correct (x:list A) : eqb_correct_on (eqb eq_op) x.
Proof.
  elim: x => [ | a l hrec].
  + by apply eqb_correct_on_nil.
  by apply eqb_correct_on_cons => // a'; apply /eqP.
Qed.

Lemma eqb_refl (x:list A) : eqb_refl_on (eqb eq_op) x.
Proof.
  elim x => [ | a l hrec].
  + by apply eqb_refl_on_nil.
  apply eqb_refl_on_cons => //; apply /eqxx.
Qed.

Lemma eqbP (x1 x2 : list A) : reflect (x1 = x2) (eqb eq_op x1 x2).
Proof. apply (iffP idP);[ apply eqb_correct | move=> ->; apply eqb_refl]. Qed.

End EqType.


