module exp-fpc.

orC    (astate Left ((pr Add (eOr E1 E2))::Qs))
       (astate Left ((pr (lf Add) E1)::(pr (rg Add) E2)::Qs)).
andC   (astate Left ((pr Add (eAnd E1 E2))::Qs))
       (astate Left ((pr (lf Add) E1)::Qs))
       (astate Left ((pr (rg Add) E2)::Qs)).
falseC (astate Left ((pr Add eFalse)::Qs))
       (astate Left Qs).
storeC (astate Left ((pr Add ET)::Qs))
       (astate ((pr Add ET)::Left) Qs)
       (idx Add).

% Select Variables in the expansion tree are handled as eigenvariable names
% This automatically works also for Skolem-Expansion Trees
allCx  (astate Left ((pr Add (eAll SVar ET))::Qs))
       (astate Left ((pr (dn Add) ET)::Qs)) SVar.


releaseE (sstate Left (pr Add ET)) (astate Left [pr Add ET]).
initialE (sstate Left (pr Add ET)) (idx Add').
trueE    (sstate Left (pr Add ET)).
someE    (sstate Left (pr Add (eSome [pr Term ET])))
         (dstate Left [pr (dn Add) ET])
         Term.

% A negative delay is emulated using a neg disjunction and neg false

releaseE (dstate Left Neg) (dstate Left Neg).
orC      (dstate Left ((pr Add E)::nil))
         (dstate Left ((pr Add eFalse)::(pr Add E)::nil)).
falseC   (dstate Left ((pr Add eFalse)::(pr Add E)::nil))
         (astate Left ((pr Add E)::nil)).

decideE (astate Left [])
        (sstate Left (pr Add eLit))
        (idx Add) :- 
  memb (pr Add eLit) Left.

decideE (astate Left [])
        (sstate Left' (pr Add (eSome [pr Term ExTree])))
        (idx Add) :-
  memb_and_rest (pr Add (eSome [pr Term ExTree])) Left Left'.

decideE (astate Left [])
        (sstate ((pr Add (eSome SubExp'))::Left') (pr Add (eSome [Pair])))
        (idx Add) :-
  memb_and_rest (pr Add (eSome SubExp)) Left Left', SubExp' = (_::_),
  memb_and_rest Pair SubExp SubExp'.

decideE (astate Left [])
        (sstate Left' (pr Add (eSome [pr Term ExTree])))
        (idx Add) :-
  memb_and_rest (pr Add (eSomeOrd [pr Term ExTree])) Left Left'.

decideE (astate Left [])
        (sstate ((pr Add (eSomeOrd SubExp'))::Left') (pr Add (eSome [Pair])))
        (idx Add) :-
  memb_and_rest (pr Add (eSomeOrd SubExp)) Left Left', SubExp' = (_::_),
  memb_and_rest Pair SubExp SubExp'.

% The generic way to extend an FPC of skolemized proof evidence of a
% skolemized formula so that the skolemized proof evidence can serve
% as proof evidence for the original formula.

allCx  Cert Cert Tm :-
%% This is to separate the case of a certificate that does contain strong quantifiers
Cert = (astate _ ((pr _ ET)::_)), not (ET = eAll _ _).