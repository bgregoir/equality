Require Import Eqdep_dec.
From mathcomp Require Import all_ssreflect.
Require Import PArith core_defs.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope positive_scope.

Inductive expr :=
| Var : nat -> expr
| IfThenElse : bool_expr -> expr -> expr -> expr
| Plus : expr -> expr -> expr
| Minus : expr -> expr -> expr
with bool_expr :=
| True : bool_expr
| False : bool_expr
| And : bool_expr -> bool_expr -> bool_expr
| Or : bool_expr -> bool_expr -> bool_expr
| Equal : expr -> expr -> bool_expr
| Lt : expr -> expr -> bool_expr.

Section Ind.

Scheme expr_ind_mut := Induction for expr Sort Prop
  with bool_expr_ind_mut := Induction for bool_expr Sort Prop.

Combined Scheme expr_combined_ind from expr_ind_mut, bool_expr_ind_mut.

End Ind.

Module AUX.

Definition etag (e : expr) := 
  match e with
  | Var _            => 1
  | IfThenElse _ _ _ => 2
  | Plus _ _         => 3
  | Minus _ _        => 4
  end.

Definition btag (b : bool_expr) :=
  match b with
  | True      => 1
  | False     => 2
  | And _ _   => 3
  | Or _ _    => 4
  | Equal _ _ => 5
  | Lt _ _    => 6
  end.

Definition efields_t (p:positive) : Type := 
  match p with
  | 1 => nat
  | 2 => bool_expr * expr * expr
  | 3 | 4 => expr * expr
  | _ => unit
  end.

Definition bfields_t (p:positive) : Type :=
  match p with
  | 3 | 4 => bool_expr * bool_expr
  | 5 | 6 => expr * expr
  | _ => unit
  end.

Definition efields (e:expr) : efields_t (etag e) := 
  match e with
  | Var n => n
  | IfThenElse b e1 e2 => (b, e1, e2)
  | Plus e1 e2 | Minus e1 e2 => (e1, e2)
  end.

Definition bfields (b:bool_expr) : bfields_t (btag b) := 
  match b with
  | True | False => tt
  | And b1 b2 | Or b1 b2 => (b1, b2)
  | Equal e1 e2 | Lt e1 e2 => (e1, e2)
  end.

Definition econstruct (p:positive) : efields_t p -> option expr :=
  match p with
  | 1 => fun n => Some (Var n)
  | 2 => fun '(b, e1, e2) => Some (IfThenElse b e1 e2)
  | 3 => fun '(e1, e2) => Some (Plus e1 e2)
  | 4 => fun '(e1, e2) => Some (Minus e1 e2)
  | _ => fun _ => None
  end.

Lemma econstructP e : econstruct (efields e) = Some e.
Proof. by case: e. Qed.

Definition bconstruct (p:positive) : bfields_t p -> option bool_expr :=
  match p with
  | 1 => fun _ => Some True
  | 2 => fun _ => Some False
  | 3 => fun '(b1, b2) => Some (And b1 b2)
  | 4 => fun '(b1, b2) => Some (Or b1 b2)
  | 5 => fun '(e1, e2) => Some (Equal e1 e2)
  | 6 => fun '(e1, e2) => Some (Lt e1 e2)
  | _ => fun _ => None
  end.

Lemma bconstructP b : bconstruct (bfields b) = Some b.
Proof. by case: b. Qed.

End AUX.

Local Instance expr_obj : @obj expr := 
  {| tag        := AUX.etag
   ; fields_t   := AUX.efields_t
   ; fields     := AUX.efields
   ; construct  := AUX.econstruct
   ; constructP := AUX.econstructP |}.

Local Instance bool_expr_obj : @obj bool_expr := 
  {| tag        := AUX.btag
   ; fields_t   := AUX.bfields_t
   ; fields     := AUX.bfields
   ; construct  := AUX.bconstruct
   ; constructP := AUX.bconstructP |}.

Section Fields.

Context (eqb_e : expr -> expr -> bool) (eqb_b : bool_expr -> bool_expr -> bool).

Definition eqb_fields_e (p:positive) : fields_t (obj:=expr_obj) p -> fields_t (obj:=expr_obj) p -> bool :=
  match p with
  | 2 => fun '(b1, e11, e12) '(b2, e21, e22) => [&& eqb_b b1 b2, eqb_e e11 e21 & eqb_e e12 e22]
  | 3 | 4 => fun '(e11, e12) '(e21, e22) => eqb_e e11 e21 && eqb_e e12 e22
  | _ => eq_op
  end.

Definition eqb_fields_b (p:positive) : fields_t (obj:=bool_expr_obj) p -> fields_t (obj:=bool_expr_obj) p -> bool :=
  match p with
  | 3 | 4 => fun '(b11, b12) '(b21, b22) => eqb_b b11 b21 && eqb_b b12 b22
  | 5 | 6 => fun '(e11, e12) '(e21, e22) => eqb_e e11 e21 && eqb_e e12 e22
  | _ => eq_op
  end.

End Fields.

Fixpoint eqb_e (e1 e2 : expr) :=
  match e1 with
  | Var n => eqb_body (eqb_fields_e eqb_e eqb_b) (t1:=1) n e2
  | IfThenElse b1 e11 e12 => eqb_body (eqb_fields_e eqb_e eqb_b) (t1:=2) (b1,e11,e12) e2
  | Plus e11 e12 => eqb_body (eqb_fields_e eqb_e eqb_b) (t1:=3) (e11,e12) e2
  | Minus e11 e12 => eqb_body (eqb_fields_e eqb_e eqb_b) (t1:=4) (e11,e12) e2
  end
with eqb_b (b1 b2 : bool_expr) :=
  match b1 with
  | True => eqb_body (eqb_fields_b eqb_e eqb_b) (t1:=1) tt b2
  | False => eqb_body (eqb_fields_b eqb_e eqb_b) (t1:=2) tt b2
  | And b11 b12 => eqb_body (eqb_fields_b eqb_e eqb_b) (t1:=3) (b11,b12) b2
  | Or b11 b12 => eqb_body (eqb_fields_b eqb_e eqb_b) (t1:=4) (b11,b12) b2
  | Equal e1 e2 => eqb_body (eqb_fields_b eqb_e eqb_b) (t1:=5) (e1,e2) b2
  | Lt e1 e2 => eqb_body (eqb_fields_b eqb_e eqb_b) (t1:=6) (e1,e2) b2
  end.

Lemma eqb_e_correct_on_Var n : eqb_correct_on eqb_e (Var n).
Proof.
  rewrite /eqb_correct_on /=.
  apply (@eqb_body_correct _ expr_obj (eqb_fields_e eqb_e eqb_b) (Var n)).
  by rewrite /eqb_fields_correct_on /= => ? /eqP <-.
Qed.

Lemma eqb_e_correct_on_IfThenElse b e1 e2 : 
  eqb_correct_on eqb_b b ->
  eqb_correct_on eqb_e e1 ->
  eqb_correct_on eqb_e e2 ->
  eqb_correct_on eqb_e (IfThenElse b e1 e2).
Proof.
  rewrite /eqb_correct_on /=.
  move=> hb he1 he2;
    apply (@eqb_body_correct _ expr_obj (eqb_fields_e eqb_e eqb_b) (IfThenElse b e1 e2)).
  by rewrite /eqb_fields_correct_on /= => -[[??]?] /and3P [/hb <- /he1 <- /he2 <-].
Qed.

Lemma eqb_e_correct_on_Plus e1 e2 :
  eqb_correct_on eqb_e e1 ->
  eqb_correct_on eqb_e e2 ->
  eqb_correct_on eqb_e (Plus e1 e2).
Proof.
  rewrite /eqb_correct_on /=.
  move=> he1 he2;
    apply (@eqb_body_correct _ expr_obj (eqb_fields_e eqb_e eqb_b) (Plus e1 e2)).
  by rewrite /eqb_fields_correct_on /= => -[??] /andP [/he1 <- /he2 <-].
Qed.

Lemma eqb_e_correct_on_Minus e1 e2 :
  eqb_correct_on eqb_e e1 ->
  eqb_correct_on eqb_e e2 ->
  eqb_correct_on eqb_e (Minus e1 e2).
Proof.
  rewrite /eqb_correct_on /=.
  move=> he1 he2;
    apply (@eqb_body_correct _ expr_obj (eqb_fields_e eqb_e eqb_b) (Minus e1 e2)).
  by rewrite /eqb_fields_correct_on /= => -[??] /andP [/he1 <- /he2 <-].
Qed.

Lemma eqb_b_correct_on_True :
  eqb_correct_on eqb_b True.
Proof.
  rewrite /eqb_correct_on /=.
  by apply (@eqb_body_correct _ bool_expr_obj (eqb_fields_b eqb_e eqb_b) True).
Qed.

Lemma eqb_b_correct_on_False :
  eqb_correct_on eqb_b False.
Proof.
  rewrite /eqb_correct_on /=.
  by apply (@eqb_body_correct _ bool_expr_obj (eqb_fields_b eqb_e eqb_b) False).
Qed.

Lemma eqb_b_correct_on_And b1 b2 :
  eqb_correct_on eqb_b b1 ->
  eqb_correct_on eqb_b b2 ->
  eqb_correct_on eqb_b (And b1 b2).
Proof.
  rewrite /eqb_correct_on /=.
  move=> hb1 hb2;
    apply (@eqb_body_correct _ bool_expr_obj (eqb_fields_b eqb_e eqb_b) (And b1 b2)).
  by rewrite /eqb_fields_correct_on /= => -[??] /andP [/hb1 <- /hb2 <-].
Qed.

Lemma eqb_b_correct_on_Or b1 b2 :
  eqb_correct_on eqb_b b1 ->
  eqb_correct_on eqb_b b2 ->
  eqb_correct_on eqb_b (Or b1 b2).
Proof.
  rewrite /eqb_correct_on /=.
  move=> hb1 hb2;
    apply (@eqb_body_correct _ bool_expr_obj (eqb_fields_b eqb_e eqb_b) (Or b1 b2)).
  by rewrite /eqb_fields_correct_on /= => -[??] /andP [/hb1 <- /hb2 <-].
Qed.

Lemma eqb_b_correct_on_Equal e1 e2 :
  eqb_correct_on eqb_e e1 ->
  eqb_correct_on eqb_e e2 ->
  eqb_correct_on eqb_b (Equal e1 e2).
Proof.
  rewrite /eqb_correct_on /=.
  move=> he1 he2;
    apply (@eqb_body_correct _ bool_expr_obj (eqb_fields_b eqb_e eqb_b) (Equal e1 e2)).
  by rewrite /eqb_fields_correct_on /= => -[??] /andP [/he1 <- /he2 <-].
Qed.

Lemma eqb_b_correct_on_Lt e1 e2 :
  eqb_correct_on eqb_e e1 ->
  eqb_correct_on eqb_e e2 ->
  eqb_correct_on eqb_b (Lt e1 e2).
Proof.
  rewrite /eqb_correct_on /=.
  move=> he1 he2;
    apply (@eqb_body_correct _ bool_expr_obj (eqb_fields_b eqb_e eqb_b) (Lt e1 e2)).
  by rewrite /eqb_fields_correct_on /= => -[??] /andP [/he1 <- /he2 <-].
Qed.

Lemma eqb_correct :
  (forall e1 e2, eqb_e e1 e2 -> e1 = e2)
  /\
  (forall b1 b2, eqb_b b1 b2 -> b1 = b2).
Proof.
  apply expr_combined_ind => *.
  + by apply eqb_e_correct_on_Var.
  + by apply eqb_e_correct_on_IfThenElse.
  + by apply eqb_e_correct_on_Plus.
  + by apply eqb_e_correct_on_Minus.
  + by apply eqb_b_correct_on_True.
  + by apply eqb_b_correct_on_False.
  + by apply eqb_b_correct_on_And.
  + by apply eqb_b_correct_on_Or.
  + by apply eqb_b_correct_on_Equal.
  + by apply eqb_b_correct_on_Lt.
Qed.

Lemma eqb_e_correct e1 e2 : eqb_e e1 e2 -> e1 = e2.
Proof. by have [h _] := eqb_correct; apply h. Qed.

Lemma eqb_b_correct b1 b2 : eqb_b b1 b2 -> b1 = b2.
Proof. by have [_ h] := eqb_correct; apply h. Qed.

Lemma eqb_e_refl_on_Var n : eqb_refl_on eqb_e (Var n).
Proof.
  apply (@eqb_body_refl _ expr_obj (eqb_fields_e eqb_e eqb_b) (Var n)).
  by apply eqxx.
Qed.

Lemma eqb_e_refl_on_IfThenElse b e1 e2 :
  eqb_refl_on eqb_b b ->
  eqb_refl_on eqb_e e1 ->
  eqb_refl_on eqb_e e2 ->
  eqb_refl_on eqb_e (IfThenElse b e1 e2).
Proof.
  move=> hb he1 he2.
  apply (@eqb_body_refl _ expr_obj (eqb_fields_e eqb_e eqb_b) (IfThenElse b e1 e2)).
  by apply /and3P.
Qed.

Lemma eqb_e_refl_on_Plus e1 e2 :
  eqb_refl_on eqb_e e1 ->
  eqb_refl_on eqb_e e2 ->
  eqb_refl_on eqb_e (Plus e1 e2).
Proof.
  move=> he1 he2.
  apply (@eqb_body_refl _ expr_obj (eqb_fields_e eqb_e eqb_b) (Plus e1 e2)).
  by apply /andP.
Qed.

Lemma eqb_e_refl_on_Minus e1 e2 :
  eqb_refl_on eqb_e e1 ->
  eqb_refl_on eqb_e e2 ->
  eqb_refl_on eqb_e (Minus e1 e2).
Proof.
  move=> he1 he2.
  apply (@eqb_body_refl _ expr_obj (eqb_fields_e eqb_e eqb_b) (Minus e1 e2)).
  by apply /andP.
Qed.

Lemma eqb_b_refl_on_True :
  eqb_refl_on eqb_b True.
Proof. done. Qed.

Lemma eqb_b_refl_on_False :
  eqb_refl_on eqb_b False.
Proof. done. Qed.

Lemma eqb_b_refl_on_And b1 b2 :
  eqb_refl_on eqb_b b1 ->
  eqb_refl_on eqb_b b2 ->
  eqb_refl_on eqb_b (And b1 b2).
Proof.
  move=> hb1 hb2.
  apply (@eqb_body_refl _ bool_expr_obj (eqb_fields_b eqb_e eqb_b) (And b1 b2)).
  by apply /andP.
Qed.

Lemma eqb_b_refl_on_Or b1 b2 :
  eqb_refl_on eqb_b b1 ->
  eqb_refl_on eqb_b b2 ->
  eqb_refl_on eqb_b (Or b1 b2).
Proof.
  move=> hb1 hb2.
  apply (@eqb_body_refl _ bool_expr_obj (eqb_fields_b eqb_e eqb_b) (Or b1 b2)).
  by apply /andP.
Qed.

Lemma eqb_b_refl_on_Equal e1 e2 :
  eqb_refl_on eqb_e e1 ->
  eqb_refl_on eqb_e e2 ->
  eqb_refl_on eqb_b (Equal e1 e2).
Proof.
  move=> he1 he2.
  apply (@eqb_body_refl _ bool_expr_obj (eqb_fields_b eqb_e eqb_b) (Equal e1 e2)).
  by apply /andP.
Qed.

Lemma eqb_b_refl_on_Lt e1 e2 :
  eqb_refl_on eqb_e e1 ->
  eqb_refl_on eqb_e e2 ->
  eqb_refl_on eqb_b (Lt e1 e2).
Proof.
  move=> he1 he2.
  (*
  apply (@eqb_body_refl _ expr_obj (eqb_fields_e eqb_e eqb_b) (Minus e1 e2))
  works ??
  *)
  apply (@eqb_body_refl _ bool_expr_obj (eqb_fields_b eqb_e eqb_b) (Lt e1 e2)).
  by apply /andP.
Qed.

Lemma eqb_refl :
  (forall e, eqb_e e e) /\ (forall b, eqb_b b b).
Proof.
  apply expr_combined_ind; move=> *.
  + by apply eqb_e_refl_on_Var.
  + by apply eqb_e_refl_on_IfThenElse.
  + by apply eqb_e_refl_on_Plus.
  + by apply eqb_e_refl_on_Minus.
  + by apply eqb_b_refl_on_True.
  + by apply eqb_b_refl_on_False.
  + by apply eqb_b_refl_on_And.
  + by apply eqb_b_refl_on_Or.
  + by apply eqb_b_refl_on_Equal.
  + by apply eqb_b_refl_on_Lt.
Qed.

Lemma eqb_e_refl e : eqb_e e e.
Proof. by have [h _] := eqb_refl; apply h. Qed.

Lemma eqb_b_refl b : eqb_b b b.
Proof. by have [_ h] := eqb_refl; apply h. Qed.

Lemma eqb_eP e1 e2 : reflect (e1 = e2) (eqb_e e1 e2).
Proof. apply (iffP idP);[ apply eqb_e_correct | move=> ->; apply eqb_e_refl]. Qed.

Lemma eqb_bP b1 b2 : reflect (b1 = b2) (eqb_b b1 b2).
Proof. apply (iffP idP);[ apply eqb_b_correct | move=> ->; apply eqb_b_refl]. Qed.
