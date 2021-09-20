Require Import Eqdep_dec.
From mathcomp Require Import all_ssreflect.
Require Import PArith core_defs.
Require list_defs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope positive_scope.

Inductive t := 
  | T0 
  | T1 of list t.

Section Ind.

  Context (Pl : list t -> Prop) (P : t -> Prop).
  Context (Hnil : Pl [::]) (Hcons: forall t l, P t -> Pl l -> Pl (t::l))
          (HT0 : P T0) (HT1 : forall l, Pl l -> P (T1 l)).

  Fixpoint t_Ind (x : t) : P x := 
    match x with 
    | T0 => HT0
    | T1 l => @HT1 l (@list_defs.list_Ind t P Pl t_Ind Hnil Hcons l)
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
  | 2 => list t  
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
  | 2 => @list_defs.eqb t eqb
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

Lemma eqb_correct_on_T1 (o : list t) : 
  eqb_correct_on (list_defs.eqb eqb) o -> eqb_correct_on eqb (T1 o).
Proof.
  rewrite /eqb_correct_on /=.
  move=> h; apply (@eqb_body_correct _ t_obj (eqb_fields eqb) (T1 o)).
  by rewrite /eqb_fields_correct_on /= => ? /h ->.
Qed.

Lemma eqb_correct (x1 x2: t) : eqb x1 x2 -> x1 = x2.
Proof.
  apply (@t_Ind (eqb_correct_on (list_defs.eqb eqb)) (eqb_correct_on eqb)) => {x1 x2}.
  + by apply list_defs.eqb_correct_on_nil.  
  + by apply list_defs.eqb_correct_on_cons.
  + by apply eqb_correct_on_T0.
  by apply eqb_correct_on_T1.
Qed.

Lemma eqb_refl_on_T0 : eqb_refl_on eqb T0.
Proof. done. Qed.

Lemma eqb_refl_on_T1 (o : list t) : 
  eqb_refl_on (list_defs.eqb eqb) o -> eqb_refl_on eqb (T1 o).
Proof. apply (@eqb_body_refl _ t_obj (eqb_fields eqb) (T1 o)). Qed.

Lemma eqb_refl (x:t) : eqb x x.
Proof.
  apply (@t_Ind (eqb_refl_on (list_defs.eqb eqb)) (eqb_refl_on eqb)) => {x}.
  + by apply list_defs.eqb_refl_on_nil.
  + by apply list_defs.eqb_refl_on_cons.
  + by apply eqb_refl_on_T0.
  apply eqb_refl_on_T1.
Qed.

Lemma eqbP x1 x2 : reflect (x1 = x2) (eqb x1 x2).
Proof. apply (iffP idP);[ apply eqb_correct | move=> ->; apply eqb_refl]. Qed.

