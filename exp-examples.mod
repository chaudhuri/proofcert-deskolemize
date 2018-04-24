module exp-examples.
accumulate lib.
accumulate classical.
accumulate lkf-formulas.
accumulate lkf-kernel.
accumulate exp-fpc.

%  Declare here the print name and arity of function and predicate
%  systems for the non-logical constants used in this file.

pred_pname q'      "q'" [].
pred_pname (r' X)  "r'" [X].
pred_pname (s X)   "s" [X].

fun_pname  a'      "a'" [].
fun_pname  b'      "b'" [].
fun_pname (f' X)   "f'" [X].
fun_pname (f X)    "f"  [X].

eexample 1 (eC (eOr eLit eLit)) (or (ng q') q').

eexample 2 (eIntro x\ eC (eAll x (eOr eLit eLit)))
          (forall x\ or (r' x) (ng (r' x))).

% The drinker formula
eexample 3 (eIntro y\ eIntro z\ eC
          (eSome [(pr a' (eAll y (eOr eLit eLit))),
                  (pr y  (eAll z (eOr eLit eLit)))]))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).

% Example 3 but with circular dependencies - this should fail to check.
eexample 4 (eIntro y\ eIntro z\ eC
          (eSome [(pr z  (eAll y (eOr eLit eLit))),
                  (pr y  (eAll z (eOr eLit eLit)))]))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).

eexample 5 (eC
  (eOr eLit
  (eOr (eSome [(pr a' (eAnd eLit eLit)),
               (pr (f' a') (eAnd eLit eLit)),
               (pr (f' (f' a')) (eAnd eLit eLit))])
   eLit)))
   (or (ng (r' a')) 
   (or (exists x\ and (r' x) (ng (r' (f' x))))
       (r' (f' (f' (f' a')))))).

% The same as 5 except that one instantiation is deleted (and fails to check).
eexample 6 (eC
  (eOr eLit
  (eOr (eSome [(pr a' (eAnd eLit eLit)),
               (pr (f' (f' a')) (eAnd eLit eLit))])
   eLit)))
   (or (ng (r' a')) 
   (or (exists x\ and (r' x) (ng (r' (f' x))))
       (r' (f' (f' (f' a')))))).

% The drinker formula with order
eexample 7 (eIntro y\ eIntro z\ eC
          (eSomeOrd [(pr a' (eAll y (eOr eLit eLit))),
                     (pr y  (eAll z (eOr eLit eLit)))]))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).

% Example 3 but with circular dependencies and order (fails)
eexample 8 (eIntro y\ eIntro z\ eC
          (eSomeOrd [(pr z  (eAll y (eOr eLit eLit))),
                     (pr y  (eAll z (eOr eLit eLit)))]))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).

% This is example 5 with order.
eexample 9 (eC
  (eOr eLit
  (eOr (eSomeOrd [(pr a' (eAnd eLit eLit)),
                  (pr (f' a') (eAnd eLit eLit)),
                  (pr (f' (f' a')) (eAnd eLit eLit))])
   eLit)))
   (or (ng (r' a')) 
   (or (exists x\ and (r' x) (ng (r' (f' x))))
       (r' (f' (f' (f' a')))))).

% The same as 5 except that one instantiation is deleted but with order (fails).
eexample 10 (eC
  (eOr eLit
  (eOr (eSomeOrd [(pr a' (eAnd eLit eLit)),
                  (pr (f' (f' a')) (eAnd eLit eLit))])
   eLit)))
   (or (ng (r' a')) 
   (or (exists x\ and (r' x) (ng (r' (f' x))))
       (r' (f' (f' (f' a')))))).

eexample 11 (eC
    (eOr eLit
         (eSomeOrd [(pr     a'  (eSomeOrd [(pr     (f' a')  eLit)])),
                    (pr (f' a') (eSomeOrd [(pr (f' (f' a')) eLit)]))])))
     (or (ng (r' (h'    a'  (f' a')))) (exists x\ exists y\ r' (h' x y))).

eexample 12 (eC
    (eOr eLit
         (eSomeOrd [(pr    a'  (eSomeOrd [(pr      (f' a')  eLit)])),
                    (pr (f' a') (eSomeOrd [(pr (f' (f' a')) eLit)]))])))
    (or (ng (r' (h' (f' a') (f' (f' a'))))) (exists x\ exists y\ r' (h' x y))).

% Skolemized versions of the previous examples (run them with :- test N.)
% skexample Tree SkF F

skexample 21 (eC (eOr eLit eLit))
             (or (ng q') q')
             (or (ng q') q').

skexample 22 (eC (eOr eLit eLit))
             (or (r' a') (ng (r' a')))
             (forall x\ or (r' x) (ng (r' x))).
             % (eIntro x\ eC (eAll x (eOr eLit eLit)))

% The drinker formula
skexample 23 (eC
           (eSome [(pr a' (eOr eLit eLit)),
                   (pr (f' a')  (eOr eLit eLit))]))
           (exists x\ or (ng (r' x)) (r' (f' x)))
           (exists x\ forall y\ or (ng (r' x)) (r' y)).

% The drinker formula with order
skexample 27 (eC
          (eSomeOrd [(pr a' (eOr eLit eLit)),
                     (pr (f' a')  (eOr eLit eLit))]))
          (exists x\ or (ng (r' x)) (r' (f' x)))
          (exists x\ forall y\ or (ng (r' x)) (r' y)).

% The drinker formula with inner skolemization
skexample 30 (eC
           (eSome [(pr a' (eOr eLit eLit)),
                   (pr a'  (eOr eLit eLit))]))
           (exists x\ or (ng (r' x)) (r' a'))
           (exists x\ forall y\ or (ng (r' x)) (r' y)).

% The drinker formula with inner skolemization. Doesn't check.
skexample 31 (eC
           (eSome [(pr a' (eOr eLit eLit))]))
           (exists x\ or (ng (r' x)) (r' a'))
           (exists x\ forall y\ or (ng (r' x)) (r' y)).

% The "Double drinker formula". A lot of nondeterminism!
skexample 32
(eC
       (eSome [(pr a' (eSome [(pr b' (eOr (eOr eLit eLit) (eOr eLit eLit))),
                              (pr (h' a' b') (eOr (eOr eLit eLit) (eOr eLit eLit)))])),
          (pr (g a' b') (eSome [(pr b' (eOr (eOr eLit eLit) (eOr eLit eLit))),
                             (pr (h' a' b') (eOr (eOr eLit eLit) (eOr eLit eLit)))]))]))
(exists y\ exists w\ (or (or (ng (r' (g y w))) (r' y)) (or (ng (s (h' y w))) (s w))))
(exists y\ exists w\ forall x\ forall z\ (or (or (ng (r' x)) (r' y)) (or (ng (s z)) (s w)))).


% Double drinker formula with inner skolemization. Checks, but way too much nondeterminism.
skexample 33
(eC
       (eSome [(pr a' (eSome [(pr b' (eOr (eOr eLit eLit) (eOr eLit eLit))),
                              (pr (f' b') (eOr (eOr eLit eLit) (eOr eLit eLit)))])),
          (pr (f a') (eSome [(pr b' (eOr (eOr eLit eLit) (eOr eLit eLit))),
                             (pr (f' b') (eOr (eOr eLit eLit) (eOr eLit eLit)))]))]))
(exists y\ exists w\ (or (or (ng (r' (f y))) (r' y)) (or (ng (s (f' w))) (s w))))
(exists y\ exists w\ forall x\ forall z\ (or (or (ng (r' x)) (r' y)) (or (ng (s z)) (s w)))).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

polarize A                L :- pred_pname A Name Args, lit+ (atom Name Args) L.
polarize (ng A)           L :- pred_pname A Name Args, lit- (atom Name Args) L.
polarize tt               A :- true-  A.
polarize ff               A :- false- A.
polarize (and B C)        A :- polarize B D, polarize C E, conj- D E A.
polarize (or  B C)        A :- polarize B D, polarize C E, disj- D E A.
polarize (imp B C)        A :- polarize (ng B) D, polarize C E, disj- D E A.
polarize (equiv B C)      A :- polarize (imp B C) D, polarize (imp C B) E, conj- D E A.
polarize (ng (ng B))      C :- polarize B C.
polarize (ng (and B C))   A :- polarize (ng B) D, polarize (ng C) E, disj- D E A.
polarize (ng (or  B C))   A :- polarize (ng B) D, polarize (ng C) E, conj- D E A.
polarize (ng (imp B C))   A :- polarize B D,      polarize (ng C) E, conj- D E A.
polarize (ng (equiv B C)) A :- polarize (ng (imp B C)) D, 
                               polarize (ng (imp C B)) E, disj- D E A.
polarize (forall B)      A :- (pi x\ polarize (B x) (D x)),      all-  D A.
polarize (ng (exists B)) A :- (pi x\ polarize (ng (B x)) (D x)), all-  D A.

% The follow uses of delay- breaks up a sequence of existentials.
polarize (exists B)      A :- (pi x\ delay-       (B x)  (D x)), some+ D A.
polarize (ng (forall B)) A :- (pi x\ delay-   (ng (B x)) (D x)), some+ D A.

delay-   B D :- polarize B C, false- False, disj- False C D.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

test I :- eexample I Exp Form, polarize Form B, check_exp Exp B.

test I :- skexample I (eC Exp) SkForm Form,
          polarize Form B, check_exp (eC Exp) B.

check_exp (eC     Exp) B :- lkf_entry (astate nil [pr root Exp]) B.
check_exp (eIntro Exp) B :- pi x\ check_exp (Exp x) B.

test_all :- eexample I Exp Form, polarize Form B, 
            term_to_string I Str, print Str, print "  ", 
            test_spec Exp B, print "\n", fail.

test_all :- skexample I Exp _ Form, not (I = 32), not (I = 33), polarize Form B, 
            term_to_string I Str, print Str, print "  ", 
            test_spec Exp B, print "\n", fail.

test_spec Exp B :- (check_exp Exp B, print "#", fail) ; true.
