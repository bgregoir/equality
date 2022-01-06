From elpi Require Import elpi.
From Coq Require Import PArith.

Require Import core_defs.
Require Export tag fields.

Open Scope positive_scope.
Open Scope bool_scope.

Elpi Db eqb.db lp:{{

pred eqb-for
  o:term, % type
  o:term. % eqb_type

pred eqb-fields
  o:term, % type
  o:term. % eq_fields_type


}}.

Elpi Command eqb.
Elpi Accumulate File "src/fields.elpi".
Elpi Accumulate File "src/eqb.elpi".
Elpi Accumulate Db tag.db.
Elpi Accumulate Db fields.db.
Elpi Accumulate Db eqb.db.
Elpi Accumulate lp:{{

  main [str S] :-
    std.assert! (coq.locate S (indt I)) "Not an inductive type",
    Prefix is S ^ "_",
    eqb.main I Prefix _.

}}.
Elpi Typecheck.
