Require Import core_defs.
Require Export eqb eqbcorrect.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Elpi Command eqbP.
Elpi Accumulate Db eqcorrect.db.
Elpi Accumulate Db eqb.db.
Elpi Accumulate File "src/eqbP.elpi".
Elpi Accumulate lp:{{
  main [str S] :-
    std.assert! (coq.locate S (indt I)) "Not an inductive type",
    Prefix is S ^ "_",
    eqbP.main I Prefix _.
}}.
Elpi Typecheck.
