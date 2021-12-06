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

Elpi Accumulate eqb.db lp:{{

  pred  eqb-fields i:term, o:term.

  eqb-for {{ list lp:A }} {{ @list_eqb lp:A lp:F }} :- eqb-for A F.
  eqb-fields {{ list lp:A }} {{ @list_eqb_fields lp:A lp:EA lp:ELA }} :- eqb-for A EA, eqb-for {{ list lp:A }} ELA.
  %eqb-for {{ forall x : lp:S, lp:(T x) }} {{ @prod_eqb lp:A lp:F lp:B lp:G }} :- eqb-for A F, eqb-for B G.
  % eqb-for {{ unit }} {{ true }}.

}}.






Elpi Command eqcorrect.
Elpi Accumulate Db eqb.db.
Elpi Accumulate Db fields.db.
Elpi Accumulate File "src/elpi-ltac.elpi".
Elpi Accumulate lp:{{

  main [str S] :-
    std.assert! (coq.locate S (indt I)) "Not an inductive type",
    Prefix is S ^ "_",
    eqb.main I Prefix _.


pred eqb.main i:inductive, i:string, o:list prop.
eqb.main I Prefix [] :- std.do! [
  coq.env.indt I _ _ N _ Ks KTs,
  KTs = [_,KT],
  Ks = [_,K],
  do-params N KT (global (indc K)) R,
  std.assert-ok! (coq.typecheck R Ty) "R casse",
  /*

  coq.ltac.collect-goals R [G] _,
  coq.ltac.open (coq.ltac.call "eqb_correct_on__solver" []) G [],
  std.assert-ok! (coq.typecheck R Ty) "R casse2",
*/
  Name is Prefix ^ "eqb_correct_on_" ^ {coq.gref->id (indc K)},
  coq.env.add-const Name R Ty @opaque! _,
  
].

% forall T : Type, T -> list T -> list T --->  forall a eqA, ..R..
% T : Type |- T -> list T -> list T ---> 
pred do-params i:int, i:term, i:term, o:term.
do-params NP (prod N T F) K {{ fun (a : lp:T) (eqA : a -> a -> bool) => lp:(R a eqA) }} :- NP > 0, !, NP1 is NP - 1,
  @pi-decl N T a\
  @pi-decl `eqA` {{ lp:a -> lp:a -> bool }} eqA\
  eqb-for a eqA =>
    do-params NP1 (F a) {{ lp:K lp:a }} (R a eqA).
do-params 0 T K R :- do-args T K R.

pred do-args i:term, i:term, o:term.
do-args (prod N T F) K {{ fun (x : lp:T) (Px : eqb_correct_on lp:Cmp x) => lp:(R x Px) }} :- !,
  eqb-for T Cmp,
  @pi-decl N T x\
  @pi-decl `px` {{ eqb_correct_on lp:Cmp lp:x }} px\
     do-args (F x) {{ lp:K lp:x }} (R x px).
do-args T K {{ lp:B : eqb_correct_on lp:Cmp lp:K }} :- std.do! [
  eqb-for T Cmp,
  coq.safe-dest-app T (global (indt I)) Args,
  fields-for I _ _ _ ConstructPC,
  coq.mk-app (global (const ConstructPC)) Args ConstructP,
  eqb-fields T Fields,
  B = {{ @eqb_body_correct _ _ _ _ _ lp:ConstructP lp:Fields lp:K (fun f => _) }},
  coq.typecheck {{ lp:B : eqb_correct_on lp:Cmp lp:K }} _ _,
  coq.ltac.collect-goals B [G] _,
  coq.ltac.open (coq.ltac.call "eqb_correct_on__solver" []) G [],
].

}}.
Elpi Typecheck.

Elpi eqcorrect list.

About list_eqb_correct_on_cons.

Definition eqb_correct_on_cons := list_eqb_correct_on_cons

Lemma eqb_correct_on_nil A (eqA : A -> A -> bool) : eqb_correct_on (list_eqb eqA) nil.
Proof.
  refine (
    @eqb_body_correct (list A) (@list_tag A) (@list_fields_t A) (@list_fields A) (@list_construct A) (@list_constructP A)
      (@list_eqb_fields A eqA (@list_eqb A eqA))
      [::] _).
  eqb_correct_on__solver.
Qed.

(*
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

*)

Ltac eqb_refl_on__solver :=
  rewrite /eqb_fields_refl_on /=;
  repeat
    (reflexivity || apply/andP; split; assumption).

Lemma eqb_refl_on_nil A (eqA : A -> A -> bool) : eqb_refl_on (list_eqb eqA) [::].
Proof.
  refine (
  (@eqb_body_refl _ _ _ _ (@list_eqb_fields A eqA (list_eqb eqA)) _) _).
  eqb_refl_on__solver.
Qed.

Lemma eqb_refl_on_cons A (eqA : A -> A -> bool):
  forall a, eqb_refl_on eqA a -> 
  forall l, eqb_refl_on (list_eqb eqA) l -> 
  eqb_refl_on (list_eqb eqA) (a :: l).
Proof. 
  refine (fun a ha l hl =>
   (@eqb_body_refl _ _ _ _ (@list_eqb_fields A eqA (list_eqb eqA)) _) _).
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


