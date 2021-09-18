Require Import Eqdep_dec.

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import PArith.
Open Scope positive_scope.

Module Simple.

Inductive t : Set := 
  | T0 
  | T1 of nat
  | T2 of nat & nat.

Module t.

Definition tag (x:t) : positive := 
  match x with
  | T0     => 1
  | T1 _   => 2
  | T2 _ _ => 3
  end.

Definition fields_t (tag:positive) : Type := 
  match tag with
  | 2 => nat 
  | 3 => (nat * nat)%type
  | _ => unit
  end.

Definition construct (tag:positive) : fields_t tag -> option t := 
  match tag (* return fields_t tag -> option t *) with
  | 1 => fun _ => Some T0 
  | 2 => fun n => Some (T1 n)
  | 3 => fun (p: _ * _) => Some (T2 p.1 p.2) 
  | _ => fun _ => None
  end.

Definition fields (x:t) : fields_t (tag x) := 
  match x return fields_t (tag x) with
  | T0 => tt
  | T1 n => n
  | T2 n1 n2 => (n1, n2)
  end.

Definition eqb_fields (t:positive) : fields_t t -> fields_t t -> bool := 
  match t return fields_t t -> fields_t t -> bool with
  | 1 => eq_op
  | 2 => eq_op 
  | 3 => eq_op 
  | _ => eq_op
  end.

Definition eqb (x1 x2:t) := 
  let t1 := tag x1 in
  let t2 := tag x2 in
  match Pos.eq_dec t2 t1 with
  | left heq => 
     let f1 := fields x1 in
     let f2 := fields x2 in
     @eqb_fields t1 f1 (@eq_rect positive t2 fields_t f2 t1 heq) 
  | right _ => false 
  end.

Definition reconstruct (x:t) : option t := 
  construct (fields x).

Lemma eqb_fieldsP tag (f1 f2 : fields_t tag) : reflect (f1 = f2) (eqb_fields f1 f2).
Proof.
  move: tag f1 f2; repeat (case; try by move=> *;apply eqP).
Qed.

(*
Lemma eqb_fields_correct tag (f1 f2 : fields_t tag) : eqb_fields f1 f2 -> f1 = f2.
Proof.
  move: tag f1 f2; repeat (case; try by move=> *;apply/eqP).
Qed.

Lemma eqb_fields_refl tag (f : fields_t tag) : eqb_fields f f.
Proof.
  case: tag f => //.
Admitted.
*)

Lemma L1 x y : eqb x y -> reconstruct x = reconstruct y.
Proof.
  rewrite /eqb /reconstruct.
  case: Pos.eq_dec => // heq.
  move: (fields x) (fields y).
  move: (tag x) heq => tx ?; subst tx => /=.
  by move=> ?? /eqb_fieldsP ->.
Qed.

Lemma L2 x : reconstruct x = Some x.
Proof. by case x. Qed.

Lemma L3 x y : eqb x y -> x = y.
Proof. by move=> /L1; rewrite !L2 => -[<-]. Qed.

Lemma L4 x : eqb x x.
Proof. 
  rewrite /eqb.
  case: Pos.eq_dec => // heq.
  have -> /= := Eqdep_dec.UIP_dec Pos.eq_dec heq erefl.
  by apply/eqb_fieldsP.
Qed.

Lemma L5 x y : reflect (x = y) (eqb x y).
Proof. by apply (iffP idP); [ apply L3 | move=> ->; apply L4]. Qed.

End t.

End Simple.

Module Rec.

Inductive t : Set := 
  | T0
  | T1 of t
  | T2 of t & t.

Module t.

Definition tag (x:t) : positive := 
  match x with
  | T0     => 1
  | T1 _   => 2
  | T2 _ _ => 3
  end.

Definition fields_t (tag:positive) : Type := 
  match tag with
  | 2 => t
  | 3 => (t * t)%type
  | _ => unit
  end.

Definition fields (x:t) : fields_t (tag x) := 
  match x return fields_t (tag x) with
  | T0 => tt
  | T1 t => t
  | T2 t1 t2 => (t1, t2)
  end.

Definition construct (tag:positive) : fields_t tag -> option t := 
  match tag (* return fields_t tag -> option t *) with
  | 1 => fun _ => Some T0 
  | 2 => fun n => Some (T1 n)
  | 3 => fun (p: _ * _) => Some (T2 p.1 p.2) 
  | _ => fun _ => None
  end.

Definition reconstruct (x:t) : option t := 
  construct (fields x).

Definition hrec (P : t -> Prop) (tag:positive) : fields_t tag -> Prop := 
  match tag return fields_t tag -> Prop with
  | 1 => fun _ => True 
  | 2 => fun n => P n
  | 3 => fun (p: _ * _) => P p.1 /\ P p.2
  | _ => fun _ => True
  end.

Lemma L2 x : reconstruct x = Some x.
Proof. by case x. Qed.

Section eqb_fields.

Context (eqb : t -> t -> bool).

Definition eqb_fields (tag:positive) : fields_t tag -> fields_t tag -> bool := 
  match tag return fields_t tag -> fields_t tag -> bool with
  | 1 => eq_op
  | 2 => eqb
  | 3 => fun (p1 p2 : t * t) => eqb p1.1 p2.1 && eqb p1.2 p2.2
  | _ => eq_op
  end.

Definition PL1 (x:t) := forall y, eqb x y -> Some x = reconstruct y.

Lemma eqb_fields_correct tag (f1 f2 : fields_t tag) : 
  @hrec PL1 tag f1 ->
  eqb_fields f1 f2 -> f1 = f2.
Proof.
  move: tag f1 f2.
  repeat (match goal with |- forall (_: positive), _ => case; try by move=> *;apply/eqP end).
  + by move=> [f11 f12] [f21 f22] /= [h1 h2] /andP[] /h1; rewrite L2 => -[->] /h2; rewrite L2 => -[->].
  by move=> f1 f2 /= h1 /h1; rewrite L2 => -[->].
Qed.

Definition PL4 (x:t) := eqb x x.

Lemma eqb_fields_refl tag (f : fields_t tag) : @hrec PL4 tag f -> eqb_fields f f.
Proof.
  move: tag f; rewrite /PL4.
  repeat (match goal with |- forall (_: positive), _ => case; try by move=> *;apply/eqP end).
  + by move => -[f1 f2] /= [-> ->].
  by move=> f /= ->.
Qed.

Definition eqb_body (t1:positive) (f1:fields_t t1) (x2:t) := 
  let t2 := tag x2 in
  match Pos.eq_dec t2 t1 with
  | left heq => 
    let f2 := fields x2 in
    @eqb_fields t1 f1 (@eq_rect positive t2 fields_t f2 t1 heq)
  | right _ => false 
  end.

Lemma eqb_body_construct t1 (f1:fields_t t1) x2 : 
  @hrec PL1 t1 f1 ->
  eqb_body f1 x2 -> construct f1 = reconstruct x2.
Proof.
  rewrite /eqb_body => /eqb_fields_correct hr.
  case: Pos.eq_dec => // heq.
  by subst t1 => /= /hr ->.
Qed.

Lemma eqb_body_refl (x:t): 
  @hrec PL4 (tag x) (fields x) ->
  eqb_body (fields x) x.
Proof.
  rewrite /eqb_body.
  case: Pos.eq_dec => // heq.
  have -> /= := Eqdep_dec.UIP_dec Pos.eq_dec heq erefl.
  by apply eqb_fields_refl.
Qed.

End eqb_fields.

(* Does not work *)
(*
Fixpoint eqb (x1 x2:t) := 
  let t1 := tag x1 in
  let t2 := tag x2 in
  match positive.eq_dec t1 t2 with
  | left heq => 
     let f1 := fields x1 in
     let f2 := fields x2 in
     @eqb_fields eqb t2 (@eq_rect positive t1 fields_t f1 t2 heq) f2
  | right _ => false 
  end.
*)

Fixpoint eqb (x1 x2:t) := 
  match x1 with 
  | T0         => @eqb_body eqb 1 tt x2
  | T1 x1'     => @eqb_body eqb 2 x1' x2
  | T2 x1' x2' => @eqb_body eqb 3 (x1', x2') x2
  end.

(*  
Definition eqb_aux (x1 x2:t) := 
  let t1 := tag x1 in
  let t2 := tag x2 in
  match positive.eq_dec t2 t1 with
  | left heq => 
     let f1 := fields x1 in
     let f2 := fields x2 in
     @eqb_fields eqb t1 f1  (@eq_rect positive t2 fields_t f2 t1 heq)
  | right _ => false 
  end.
*)

Lemma L1 x y : eqb x y -> Some x = reconstruct y.
Proof.
  elim: x y => [ | x1' hrec1 | x1' hrec1 x2' hrec2 ] y /=.
  + by move => /eqb_body_construct -/(_ I) <-.
  + by move=> /eqb_body_construct -/(_ hrec1) <-.
  by move=> /eqb_body_construct -/(_ (conj hrec1 hrec2)) <-.
Qed.

Lemma L3 x y : eqb x y -> x = y.
Proof. by move=> /L1; rewrite !L2 => -[<-]. Qed.

Lemma L4 x : eqb x x.
Proof. 
  by elim: x => [ | x1' hrec1 | x1' hrec1 x2' hrec2] /=; apply eqb_body_refl.
Qed.

Lemma L5 x y : reflect (x = y) (eqb x y).
Proof. by apply (iffP idP); [ apply L3 | move=> ->; apply L4]. Qed.

End t.

End Rec.

Module Poly.

Module option.

Section Section.
Context (A:Type).

Notation t := (option A).

Section Ind.

  Context (PA : A -> Prop) (P: option A -> Prop).
  Context (A_ind : forall a, PA a) (Hnone : P None) (Hsome : forall a, PA a -> P (Some a)).

  Definition option_ind (o : option A) : P o := 
    match o with
    | None => Hnone
    | Some a => Hsome (A_ind a)
    end.
End Ind.

Definition tag (x:t) : positive := 
  match x with
  | None     => 1
  | Some _   => 2
  end.

Definition fields_t (tag:positive) : Type := 
  match tag with
  | 2 => A  
  | _ => unit
  end.

Definition construct (tag:positive) : fields_t tag -> option t := 
  match tag (* return fields_t tag -> option t *) with
  | 1 => fun _ => Some None 
  | 2 => fun a => Some (Some a)
  | _ => fun _ => None
  end.

Definition fields (x:t) : fields_t (tag x) := 
  match x return fields_t (tag x) with
  | None => tt
  | Some a => a
  end.

Context (Aeqb : A -> A -> bool).

Definition eqb_fields (t:positive) : fields_t t -> fields_t t -> bool := 
  match t return fields_t t -> fields_t t -> bool with
  | 1 => eq_op
  | 2 => Aeqb
  | _ => eq_op
  end.

Definition eqb (x1 x2:t) := 
  let t1 := tag x1 in
  let t2 := tag x2 in
  match Pos.eq_dec t2 t1 with
  | left heq => 
     let f1 := fields x1 in
     let f2 := fields x2 in
     @eqb_fields t1 f1 (@eq_rect positive t2 fields_t f2 t1 heq) 
  | right _ => false 
  end.

Definition reconstruct (x:t) : option t := 
  construct (fields x).

Definition hrec (PA : A -> Prop) (tag:positive) : fields_t tag -> Prop := 
  match tag return fields_t tag -> Prop with
  | 1 => fun _ => True 
  | 2 => fun n => PA n
  | _ => fun _ => True
  end.

Definition PAL1 
Lemma eqb_fields_correct tag (f1 f2 : fields_t tag) : 
  @hrec PA tag f1 ->
  eqb_fields f1 f2 -> f1 = f2.
Proof.
  move: tag f1 f2.
  repeat (match goal with |- forall (_: positive), _ => case; try by move=> *;apply/eqP end).
  + by move=> [f11 f12] [f21 f22] /= [h1 h2] /andP[] /h1; rewrite L2 => -[->] /h2; rewrite L2 => -[->].
  by move=> f1 f2 /= h1 /h1; rewrite L2 => -[->].
Qed.

Lemma eqb_fields_correct tag (f1 f2 : fields_t tag) : 


reflect (f1 = f2) (eqb_fields f1 f2).
Proof.
  move: tag f1 f2; repeat (case; try by move=> *;apply eqP).
Qed.

(*
Lemma eqb_fields_correct tag (f1 f2 : fields_t tag) : eqb_fields f1 f2 -> f1 = f2.
Proof.
  move: tag f1 f2; repeat (case; try by move=> *;apply/eqP).
Qed.

Lemma eqb_fields_refl tag (f : fields_t tag) : eqb_fields f f.
Proof.
  case: tag f => //.
Admitted.
*)

Lemma L1 x y : eqb x y -> reconstruct x = reconstruct y.
Proof.
  rewrite /eqb /reconstruct.
  case: Pos.eq_dec => // heq.
  move: (fields x) (fields y).
  move: (tag x) heq => tx ?; subst tx => /=.
  by move=> ?? /eqb_fieldsP ->.
Qed.

Lemma L2 x : reconstruct x = Some x.
Proof. by case x. Qed.

Lemma L3 x y : eqb x y -> x = y.
Proof. by move=> /L1; rewrite !L2 => -[<-]. Qed.

Lemma L4 x : eqb x x.
Proof. 
  rewrite /eqb.
  case: Pos.eq_dec => // heq.
  have -> /= := Eqdep_dec.UIP_dec Pos.eq_dec heq erefl.
  by apply/eqb_fieldsP.
Qed.

Lemma L5 x y : reflect (x = y) (eqb x y).
Proof. by apply (iffP idP); [ apply L3 | move=> ->; apply L4]. Qed.

End t.

End Simple.

Module .
