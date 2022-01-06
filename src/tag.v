From elpi Require Import elpi.
From Coq Require Import PArith.
Open Scope positive_scope.

Elpi Db tag.db lp:{{

% this is how one registers the tag function to an inductive and let other
% elpi commands use that piece of info
pred tag-for o:inductive, o:constant.

}}.

Elpi Command tag.
Elpi Accumulate File "src/tag.elpi".
Elpi Accumulate Db tag.db.
Elpi Accumulate lp:{{

  main [str S] :-
    std.assert! (coq.locate S (indt I)) "Not an inductive type",
    Prefix is S ^ "_",
    tag.main I Prefix _.

}}.
Elpi Typecheck.
