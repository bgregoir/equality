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
Elpi Accumulate Db derive.param1.db.
Elpi Accumulate Db derive.param1.inhab.db.
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
  std.map2 KTs Ks (add-decl-correct Prefix N) Lt-correct,
  std.map2 KTs Ks (add-decl-refl Prefix N) Lt-refl,
  induction-db I Indu,
  reali (global (indt I)) IR, % param1-db, really

  add-indu-correct TI Indu IR Lt-correct R,
  std.assert-ok! (coq.typecheck R Ty) "fail demande a JC", 
  Name is Prefix ^ "eqb_correct",
  coq.env.add-const Name R Ty @opaque! Correct,

  add-indu-refl TI Indu IR Lt-refl Rr,
  std.assert-ok! (coq.typecheck Rr Tyr) "fail demande a JC", 
  Namer is Prefix ^ "eqb_refl",
  coq.env.add-const Namer Rr Tyr @opaque! Refl,

  add-reflect TI (global (const Correct)) (global (const Refl)) Breflect,
  std.assert-ok! (coq.typecheck Breflect Treflect) "fail demande a JC", 
  Namerf is Prefix ^ "eqb_reflect",
  coq.env.add-const Namerf Breflect Treflect @opaque! Reflect,

  add-eqP TI (global (indt I)) (global (const Reflect)) BeqP,
  std.assert-ok! (coq.typecheck BeqP TeqP) "fail demande a JC", 
  NameeqP is Prefix ^ "eqbP",
  coq.env.add-const NameeqP BeqP TeqP @opaque! _EqP,

].

/************************** correct *********************************************/

pred add-decl-correct i:string, i:int, i:term, i:constructor, o:term.
add-decl-correct Prefix N KT K (global (const P)) :- std.do![  
  do-params-correct N KT (global (indc K)) R,
  std.assert-ok! (coq.typecheck R Ty) "R casse",
  Name is Prefix ^ "eqb_correct_on_" ^ {coq.gref->id (indc K)},
  coq.env.add-const Name R Ty @opaque! P,
].

% forall T : Type, T -> list T -> list T --->  forall a eqA, ..R..
% T : Type |- T -> list T -> list T ---> 
pred do-params-correct i:int, i:term, i:term, o:term.
do-params-correct NP (prod N T F) K {{ fun (a : lp:T) (eqA : a -> a -> bool) => lp:(R a eqA) }} :- NP > 0, !, NP1 is NP - 1,
  @pi-decl N T a\
  @pi-decl `eqA` {{ lp:a -> lp:a -> bool }} eqA\
  eqb-for a eqA =>
    do-params-correct NP1 (F a) {{ lp:K lp:a }} (R a eqA).
do-params-correct 0 T K R :- do-args-correct T K R.

pred do-args-correct i:term, i:term, o:term.
do-args-correct (prod N T F) K {{ fun (x : lp:T) (Px : eqb_correct_on lp:Cmp x) => lp:(R x Px) }} :- !,
  eqb-for T Cmp,
  @pi-decl N T x\
  @pi-decl `px` {{ eqb_correct_on lp:Cmp lp:x }} px\
     do-args-correct (F x) {{ lp:K lp:x }} (R x px).
do-args-correct T K {{ lp:B : eqb_correct_on lp:Cmp lp:K }} :- std.do! [
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

pred add-indu-correct i:term, i:term, i:term, i:list term, o:term.
add-indu-correct (prod N T F) Indu IR LS {{ fun (a : lp:T) (eqA : a -> a -> bool) (eqAc : eqb_correct eqA) => lp:(R a eqA eqAc) }} :- !,
  @pi-decl N T a\
  @pi-decl `eqA` {{ lp:a -> lp:a -> bool }} eqA\
  @pi-decl `eqAc` {{ @eqb_correct lp:a lp:eqA }} eqAc\ % super nasty "bug", the _ does not see a, if you write lp:{{ FOO a }} it works. Elaborating the skeleton is also ok, but then param1-inhab-db does not work well :-/
  param1-inhab-db {{ @eqb_correct_on lp:a lp:eqA }} eqAc =>
  add-indu-correct (F a) 
     {{ lp:Indu lp:a (@eqb_correct_on lp:a lp:eqA)}} 
     {{ lp:IR lp:a (@eqb_correct_on lp:a lp:eqA)}} 
     {std.map LS (t\coq.mk-app t [a, eqA])} (R a eqA eqAc).

add-indu-correct _T Indu IR LS {{ fun x => lp:(R x) }} :- 
  std.assert! (param1-inhab-db IR Is_full) "not trivially inhabited",
  @pi-decl `x` _ x\
    std.append LS [x, app[Is_full,x]] (Args x),
    R x = app [Indu, _ | Args x].
  
/******************************** Refl **************************************************************/
pred add-decl-refl i:string, i:int, i:term, i:constructor, o:term.
add-decl-refl Prefix N KT K (global (const P)) :- std.do![  
  do-params-refl N KT (global (indc K)) R,
  std.assert-ok! (coq.typecheck R Ty) "R casse",
  Name is Prefix ^ "eqb_refl_on_" ^ {coq.gref->id (indc K)},
  coq.env.add-const Name R Ty @opaque! P,
].

% forall T : Type, T -> list T -> list T --->  forall a eqA, ..R..
% T : Type |- T -> list T -> list T ---> 
pred do-params-refl i:int, i:term, i:term, o:term.
do-params-refl NP (prod N T F) K {{ fun (a : lp:T) (eqA : a -> a -> bool) => lp:(R a eqA) }} :- NP > 0, !, NP1 is NP - 1,
  @pi-decl N T a\
  @pi-decl `eqA` {{ lp:a -> lp:a -> bool }} eqA\
  eqb-for a eqA =>
    do-params-refl NP1 (F a) {{ lp:K lp:a }} (R a eqA).
do-params-refl 0 T K R :- do-args-refl T K R.

pred do-args-refl i:term, i:term, o:term.
do-args-refl (prod N T F) K {{ fun (x : lp:T) (Px : eqb_refl_on lp:Cmp x) => lp:(R x Px) }} :- !,
  eqb-for T Cmp,
  @pi-decl N T x\
  @pi-decl `px` {{ eqb_refl_on lp:Cmp lp:x }} px\
     do-args-refl (F x) {{ lp:K lp:x }} (R x px).
do-args-refl T K {{ lp:B : eqb_refl_on lp:Cmp lp:K }} :- std.do! [
  eqb-for T Cmp,
  eqb-fields T Fields,
  B = {{ @eqb_body_refl _ _ _ _ lp:Fields lp:K _ }},
  coq.typecheck {{ lp:B : eqb_refl_on lp:Cmp lp:K }} _ _,
  coq.ltac.collect-goals B [G] _,
  coq.ltac.open (coq.ltac.call "eqb_refl_on__solver" []) G [],
].

pred add-indu-refl i:term, i:term, i:term, i:list term, o:term.
add-indu-refl (prod N T F) Indu IR LS {{ fun (a : lp:T) (eqA : a -> a -> bool) (eqAc : eqb_reflexive eqA) => lp:(R a eqA eqAc) }} :- !,
  @pi-decl N T a\
  @pi-decl `eqA` {{ lp:a -> lp:a -> bool }} eqA\
  @pi-decl `eqAr` {{ @eqb_reflexive lp:a lp:eqA }} eqAr\ % super nasty "bug", the _ does not see a, if you write lp:{{ FOO a }} it works. Elaborating the skeleton is also ok, but then param1-inhab-db does not work well :-/
  param1-inhab-db {{ @eqb_refl_on lp:a lp:eqA }} eqAr =>
  add-indu-refl (F a) 
     {{ lp:Indu lp:a (@eqb_refl_on lp:a lp:eqA)}} 
     {{ lp:IR lp:a (@eqb_refl_on lp:a lp:eqA)}} 
     {std.map LS (t\coq.mk-app t [a, eqA])} (R a eqA eqAr).

add-indu-refl _T Indu IR LS {{ fun x => lp:(R x) }} :- 
  std.assert! (param1-inhab-db IR Is_full) "not trivially inhabited",
  @pi-decl `x` _ x\
    std.append LS [x, app[Is_full,x]] (Args x),
    R x = app [Indu, _ | Args x].
 
/***************************** Equality *************************************/

pred add-reflect i:term, i:term, i:term, o:term.
add-reflect (prod N T F) Correct Refl 
   {{fun (a:lp:T) (eqA:a -> a -> bool) (H: forall x1 x2, reflect (x1 = x2) (eqA x1 x2)) => lp:(R a eqA H) }} :- !,
@pi-decl N T a\
@pi-decl `eqA` {{ lp:a -> lp:a -> bool }} eqA\
@pi-decl `H` {{ forall x1 x2, reflect (x1 = x2) (lp:eqA x1 x2)}} H\
add-reflect (F a) 
    {{lp:Correct lp:a lp:eqA (fun (a1 a2 : lp:a) => @elimT (@eq lp:a a1 a2) (lp:eqA a1 a2) (lp:H a1 a2))}}
    {{lp:Refl lp:a lp:eqA (fun (a1: lp:a) => @introT (@eq lp:a a1 a1) (lp:eqA a1 a1) (lp:H a1 a1) (@erefl lp:a a1))}}
    (R a eqA H).

add-reflect _T Correct Refl {{iffP2 lp:Correct lp:Refl}}.

pred add-eqP i:term, i:term, i:term, o:term.
add-eqP (prod N T F) Ty Reflect {{fun (a:eqType) => lp:(R a)}} :- !,
  @pi-decl N {{eqType}} a\
    eqb-for {{Equality.sort lp:a}} {{@eq_op lp:a}} =>
    add-eqP (F a)
        {{lp:Ty (Equality.sort lp:a)}}
        {{lp:Reflect (Equality.sort lp:a) (@eq_op lp:a) (@eqP lp:a)}} (R a).
        
add-eqP _ Ty Reflect {{lp:Reflect : Equality.axiom lp:Cmp}} :- 
 eqb-for Ty Cmp.          

}}.
Elpi Typecheck.

Elpi eqcorrect list.
