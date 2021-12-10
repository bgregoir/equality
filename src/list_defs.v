From elpi.apps Require Import derive.
Require Import core_defs tag fields eqb.

Set Implicit Arguments.

#[only(induction,param1_full,param1_trivial)] derive list.
Elpi tag     list.
Elpi fields  list.
Elpi eqb     list.

From mathcomp Require Import all_ssreflect.
Require Import PArith.
Open Scope positive_scope.

Ltac eqb_correct_on__solver :=
  by repeat (try case/andP; match reverse goal with H : eqb_correct_on _ _ |- _ => move=> /=/H{H}-> end).

Ltac eqb_refl_on__solver :=
  rewrite /eqb_fields_refl_on /=;
  repeat
    (reflexivity || apply/andP; split; assumption).


(* TODO: move to a file *)
Elpi Command eqcorrect.
Elpi Accumulate Db eqb.db.
Elpi Accumulate Db fields.db.
Elpi Accumulate Db derive.induction.db.
Elpi Accumulate Db derive.param1.trivial.db.
Elpi Accumulate File "src/elpi-ltac.elpi".

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
  %param1-trivial-db (global (indt I)) Is_full,
  %coq.say "IS_full = " Is_full,
  coq.say "TI =" TI, 
  add-indu TI Indu {{@list_is_list_full}} Lt R,
  coq.say "Indu = " Indu,
  coq.say "R = " R, 
  std.assert-ok! (coq.elaborate-skeleton R Ty R2) "fail demande a JC", 
  Name is Prefix ^ "eqb_correct",
  coq.env.add-const Name R2 Ty @opaque! P,
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

pred add-indu i:term, i:term, i:term, i:list term, o:term.
add-indu (prod N T F) Indu Is_full LS {{ fun (a : lp:T) (eqA : a -> a -> bool) (eqAc : eqb_correct eqA) => lp:(R a eqA eqAc) }} :- !,
  coq.say T,
  @pi-decl N T a\
  @pi-decl `eqA` {{ lp:a -> lp:a -> bool }} eqA\
  @pi-decl `eqAc` {{ eqb_correct lp:eqA }} eqAc\
  % eqb-for a eqA =>
  add-indu (F a) 
     {{ lp:Indu lp:a (eqb_correct_on lp:eqA)}} 
     {{ lp:Is_full lp:a (eqb_correct_on lp:eqA) lp:eqAc}}
    {std.map LS (t\coq.mk-app t [a, eqA])} (R a eqA eqAc).

add-indu _T Indu Is_full LS {{ fun x => lp:(R x) }} :- 
  @pi-decl `x` _ x\
  coq.mk-app { coq.mk-app Indu [_|LS] } [x, {{ lp:Is_full lp:x}}] (R x).
  
}}.
Elpi Typecheck.

Set Printing All.
Elpi eqcorrect list.
Print list_eqb_correct.

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

(*
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

*)
