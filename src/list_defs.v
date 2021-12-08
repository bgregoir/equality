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

From elpi.apps Require Import derive.
#[only(induction,param1_full,param1_trivial)] derive list.



Definition list_eqb A (eqA : A -> A -> bool) := fix eqb (x1 x2 : list A) :=
  match x1 with
  | [::] => @eqb_body (list A) (@list_tag A) (@list_fields_t A) (@list_fields A) (@list_eqb_fields A eqA eqb) (@list_tag A [::]) tt x2
  | a::l => @eqb_body (list A) (@list_tag A) (@list_fields_t A) (@list_fields A) (@list_eqb_fields A eqA eqb) (@list_tag A (a::l)) (a,l) x2
  end.

Ltac eqb_correct_on__solver :=
  by repeat (try case/andP; match reverse goal with H : eqb_correct_on _ _ |- _ => move=> /=/H{H}-> end).

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
Elpi Accumulate Db derive.induction.db.
Elpi Accumulate File "src/elpi-ltac.elpi".

(*
Elpi Db eqb_correct.db lp:{{

% this is how one registers the fields_t, fields and construct[P]
% constants to an inductive and let other elpi commands use that piece of info
pred eqb_correct-for
  o:constructor,   % constructor name XXX of type YYY
  o:constant. % YYY_eq_correct_on_XXX 
}}.
*)
Print list_induction.

Elpi Accumulate lp:{{

  main [str S] :-
    std.assert! (coq.locate S (indt I)) "Not an inductive type",
    Prefix is S ^ "_",
    eqb.main I Prefix _.


pred eqb.main i:inductive, i:string, o:list prop.
eqb.main I Prefix [] :- std.do! [
  % Add error msg if not a inductive ?
  coq.env.indt I _ _ N TI Ks KTs,
  std.map2 KTs Ks (add-decl Prefix N) Lt,
  induction-db I Indu,
  coq.say "TI=", coq.say TI,
  KTs = [TTTT, _],
  coq.say "TTTT=" TTTT,
  add-indu TTTT Indu Lt R,
].

pred add-decl i:string, i:int, i:term, i:constructor, o:term.
add-decl Prefix N KT K (global (const P)) :- std.do![  
  do-params N KT (global (indc K)) R,
  std.assert-ok! (coq.typecheck R Ty) "R casse",
  Name is Prefix ^ "eqb_correct_on_" ^ {coq.gref->id (indc K)},
  coq.env.add-const Name R Ty @opaque! P,
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

pred add-indu i:term, i:term, i:list term, o:term.
add-indu (prod N T F) Indu LS {{ fun (a : lp:T) (eqA : a -> a -> bool) (eqAc : eqb_correct eqA) => lp:(R a eqA eqAc) }} :- !,
  coq.say T,
  @pi-decl N T a\
  @pi-decl `eqA` {{ lp:a -> lp:a -> bool }} eqA\
  @pi-decl `eqAc` {{ eqb_correct lp:eqA }} eqAc\
  % eqb-for a eqA =>
  coq.say "CCC",  
  coq.say LS,
  coq.say "BBB",
 
  % Full' = {{ Full  eqAc }}

  add-indu (F a) {coq.mk-app Indu [a,eqAc]} {std.map LS (t\coq.mk-app t [a, eqA])} (R a eqA eqAc).
add-indu T Indu LS {{ fun x => lp:(R x) }} :-
 @pi-decl N T x\
 % coq.mk-app Indu [_|LS , x , {coq.mk-app Full [x]} ] TOTO, 
 coq.say {coq.term->string TOTO}.
}}.
Elpi Typecheck.

Elpi Trace.
Elpi Query lp:{{

  pi x\ x = A x

}}.

Elpi Print eqcorrect.
Set Printing All.
Elpi eqcorrect list. 



(* Definition eqb_correct_on_cons := list_eqb_correct_on_cons. *)
(*
Lemma eqb_correct_on_nil A (eqA : A -> A -> bool) : eqb_correct_on (list_eqb eqA) nil.
Proof.
  refine (
    @eqb_body_correct (list A) (@list_tag A) (@list_fields_t A) (@list_fields A) (@list_construct A) (@list_constructP A)
      (@list_eqb_fields A eqA (@list_eqb A eqA))
      [::] (fun f => _)).
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




Inductive t (A B :Type):= 
  | C1 of A
  | C2 of B
  | C3 of list (t A B)
  | C4.

#[only(induction,param1_full,param1_trivial)] derive t.
Check t_induction.

Lemma list_eqb_correct (A:Type) (eqA: A -> A -> bool) (eqAc : eqb_correct eqA)
  (x:list A) : eqb_correct_on (list_eqb eqA) x.
Proof.
  refine (@list_induction _ _ _
              (@list_eqb_correct_on_nil A eqA)
              (@list_eqb_correct_on_cons A eqA)
              x (@list_is_list_full _ _ eqAc x)).
Qed.
Set Printing All.
Print list_eqb_correct.

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


