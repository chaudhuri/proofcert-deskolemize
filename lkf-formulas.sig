sig lkf-formulas.

kind form, i, atm                    type. % Formulas, terms, and atoms

type n, p                     atm -> form. % Constructors of literals
type f+, f-, t+, t-                  form. % Units
type d-, d+                  form -> form. % Delays 
type &-&, &+&        form -> form -> form. % Conjunctions
type !-!, !+!        form -> form -> form. % Disjunction
type all, some       (i -> form)  -> form. % Quantifiers

infixr &-&, &+&  6.
infixr !-!, !+!  5.

type isNegForm, isNegAtm, isPosForm, isPosAtm, isNeg, isPos        form -> o. 
type negate                                                form -> form -> o.

% predicates for constructing and deconstructing formulas
type true+, true-, false+, false-     form -> o.
type conj+, conj-                     form -> form -> form -> o.
type disj+, disj-                     form -> form -> form -> o.
type lit-, lit+                       atm -> form -> o.
type all-, some+                      (i -> form) -> form -> o.

% Notice that the definition of ensure satisfies the 
% deMorgan principles:
%  |- ensure+ A B, negate B C   holds if and only if
%  |- negate A D, ensure- D C
type ensure-, ensure+     form -> form -> o.
