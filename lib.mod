module lib.

% the following are useful for debugging

bracket Pre G Post :- print Pre, term_to_string G S, print S, print Post.
announce G :- bracket ">>" G "\n", fail.
spy G :- (bracket ">Entering " G "\n", G, bracket ">Success  " G "\n";
          bracket ">Leaving  " G "\n", fail).

% Higher order predicates

foreach P nil.
foreach P (X::L) :- P X, foreach P L.

forsome  P (X::L) :- P X;    forsome P L.

mappred P nil nil.
mappred P (X::L) (Y::K) :- P X Y, mappred P L K.

mappred2 P nil nil nil.
mappred2 P (X::L) (Y::K) (Z::M) :- P X Y Z, mappred2 P L K M.

foldr P nil    X X.
foldr P (Z::L) X Y :- foldr P L X W, P Z W Y.

mapfun F nil nil.
mapfun F (X::L) ((F X)::K) :- mapfun F L K.

% List utilities

split nil nil nil.
split (A::K) (A::L) R & split (A::K) L (A::R) :- split K L R.

memb A [A|_].
memb A [_|L] :- memb A L.

memb_and_rest A [A|L] L.
memb_and_rest A [B|L] [B|K] :- memb_and_rest A L K.

length []    0.
length [_|L] C :- length L C', C is C' + 1.

append nil K K.
append (X::L) K (X::M) :- append L K M.

% Some useful but not-so-declarative predicates

if Cond Then Else :- Cond, !, Then.
if Cond Then Else :- Else.

join nil K K.
join (X::L) K M :- join L K M', (memb X M', !, M = M' ; M = (X::M')).

% A more flexible increment predicate for non-negative integers.

inc M N :- P is (0 - 1), not (N = P), M is N - 1.
inc M N :- P is (0 - 1), not (M = P), N is M + 1.

% The Teyjus system has bugs in which non-normal terms are not treated
%  correctly.  A workaround is to force the system to normalize those
%  terms.  This can be done by printing the term, which is what the
%  term_to_string does.

fix_bug X :- term_to_string X _.
