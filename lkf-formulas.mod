module lkf-formulas.

isNegAtm (n _).
isPosAtm (p _).

isNegForm f-   &  isNegForm t-.
isNegForm (_ &-& _) & isNegForm (_ !-! _).
isNegForm (d- _)    & isNegForm (all _).
isNeg A :- isNegForm A ; isNegAtm A.

isPosForm f+        & isPosForm t+.
isPosForm (_ &+& _) & isPosForm (_ !+!  _).
isPosForm (d+ _)    & isPosForm (some _).
isPos A :- isPosForm A ; isPosAtm A.

negate f- t+.
negate t+ f-.
negate t- f+.
negate f+ t-.

negate (p A) (n A).
negate (n A) (p A).
negate (A &+& B)  (NA !-! NB) &
negate (A !-! B)  (NA &+& NB) &
negate (A &-& B)  (NA !+! NB) &
negate (A !+! B)  (NA &-& NB) :- negate A NA, negate B NB.
negate (all B)  (some NB) &
negate (some B) (all NB)  :- pi x\ negate (B x) (NB x).

% constructor / destructor for this abstract data type
conj+ B C (B &+& C) & conj- B C (B &-& C).
disj+ B C (B !+! C) & disj- B C (B !-! C).
true+  t+ & true-  t- & false+ f+ & false- f-.
all- B (all B) & some+ B (some B).
lit- A (n A)   & lit+ A  (p A).

ensure+ B B :- isPos B.
ensure+ B C :- isNeg B, conj+ B t+ C.
ensure- B B :- isNeg B.
ensure- B C :- isPos B, disj- B f- C.
