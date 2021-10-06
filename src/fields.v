From elpi Require Import elpi.
From Coq Require Import PArith.
Require Export tag.
Open Scope positive_scope.

Elpi Db fields.db lp:{{

% this is how one registers the fields_t and fields constants to an inductive
% and let other elpi commands use that piece of info
pred fields-for o:inductive, o:constant, o:constant.

}}.

Elpi Command fields.
Elpi Accumulate File "src/fields.elpi".
Elpi Accumulate Db tag.db.
Elpi Accumulate Db fields.db.
Elpi Accumulate lp:{{

  main [str S] :-
    std.assert! (coq.locate S (indt I)) "Not an inductive type",
    Prefix is S ^ "_",
    fields.main I Prefix _.

}}.
Elpi Typecheck.
