module geo-examples.
accumulate lib.
accumulate classical.
accumulate lkf-formulas.
accumulate lkf-kernel.
accumulate geo-fpc.

%  Some geometric axioms: these are Horn clauses
theory ref        (forall x\ r x x).
theory sym        (forall x\ forall y\ imp (r x y) (r y x)).
theory trans      (forall x\ forall y\ forall z\ imp (r x y) (imp (r y z) (r x z))).
theory euclidean  (forall x\ forall y\ forall z\ imp (r x y) (imp (r x z) (r y z))).
theory connected  (forall x\ forall y\ forall z\ imp (r x y) (imp (r x z) (or (r y z) (r z y)))).

%  Some geometric axioms that are not Horn.  These do not use Skolem functions.
theory serial     (forall x\ exists y\ r x y).
theory directed   (forall x\ forall y\ forall z\ imp (r x y) (imp (r x z) (exists w\ and (r y w) (r z w)))).

%  The last two geometric axioms repeated but with Skolem functions.
theory sk1serial   (forall x\ r x (sk1 x)).
theory sk2directed (forall x\ forall y\ forall z\ imp (r x y) (imp (r x z) (and (r y (sk2 y z))   (r z (sk2 y z))))).
theory sk3directed (forall x\ forall y\ forall z\ imp (r x y) (imp (r x z) (and (r y (sk3 x y z)) (r z (sk3 x y z))))).

%% Examples using strong quantifiers in formula and certificates

geothm 1 [serial]
         []
         (exists x\ exists y\ exists z\ and (r a x) (and (r x y) (r y z)))
         (decide serial (inst a (evar w\
         (decide serial (inst w (evar v\ 
         (decide serial (inst v (evar u\
         done))))))))).

geothm 2 [serial, sym, trans]
         []
	 (r a a)
         (decide serial (inst a (evar x\
         (decide sym    (inst a (inst x
	 (decide trans  (inst a (inst x (inst a done)))))))))).

geothm 3 [directed]
         [(r a b),(r a c)]
         (exists X\ and (r b X) (r c X))
	 (decide directed (inst a (inst b (inst c (evar x\ done))))).

geothm 4 [directed, trans]
         [(r a b),(r b c),(r a e)]
         (exists X\ and (r e X) (r c X))
         (decide directed (inst a (inst b (inst e (evar x\
	  decide directed (inst b (inst c (inst x (evar y\
	  decide trans    (inst e (inst x (inst y
	  done)))))))))))).

%% Examples without strong quantifiers in formula and certificates

geothm 11 [sk1serial]
          []
          (exists x\ exists y\ exists z\ and (r a x) (and (r x y) (r y z)))
          (decide serial (inst a 
          (decide serial (inst (sk1 a)
          (decide serial (inst (sk1 (sk1 a))
          done)))))).

geothm 12 [sk1serial, sym, trans] []
          (r a a)
          (decide sk1serial (inst a 
          (decide sym       (inst a (inst (sk1 a)
          (decide trans     (inst a (inst (sk1 a) (inst a done))))))))).

geothm 13 [sk2directed]
          [(r a b),(r a c)]
          (exists X\ and (r b X) (r c X))
	  (decide sk2directed (inst a (inst b (inst c done)))).

geothm 14 [sk2directed, trans]
          [(r a b),(r b c),(r a e)]
          (exists X\ and (r e X) (r c X))
          (decide sk2directed (inst a (inst b (inst e 
          (decide sk2directed (inst b (inst c (inst (sk2 b e) 
	  (decide trans    (inst e (inst (sk2 b e) (inst (sk2 c (sk2 b e))
	   done)))))))))))).

geothm 15 [sk3directed,trans]
          [(r a b),(r b c),(r a e)]
          (exists X\ and (r e X) (r c X))
          (decide sk3directed (inst a (inst b (inst e 
	  (decide sk3directed (inst b (inst c (inst (sk3 a b e) 
	  (decide trans       (inst e (inst (sk3 a b e) (inst (sk3 b c (sk3 a b e))
	  done)))))))))))).

% Hybrid examples:  Formulas with strong quantifiers but proofs with Skolem terms.

geothm 21 [serial]
          [] 
          (exists x\ exists y\ exists z\ and (r a x) (and (r x y) (r y z)))
          (decide serial (inst a 
          (decide serial (inst (sk1 a) 
          (decide serial (inst (sk1 (sk1 a)) 
          done)))))).

geothm 22 [serial, sym, trans]
          []
          (r a a)
          (decide serial    (inst a 
          (decide sym       (inst a (inst (sk1 a)
          (decide trans     (inst a (inst (sk1 a) (inst a done))))))))).

geothm 23 [directed]
          [(r a b),(r a c)]
          (exists X\ and (r b X) (r c X))
	  (decide directed (inst a (inst b (inst c done)))).

geothm 24 [directed, trans]
          [(r a b),(r b c),(r a e)]
          (exists X\ and (r e X) (r c X))
          (decide directed (inst a (inst b (inst e 
	  (decide directed (inst b (inst c (inst (sk2 b e) 
	  (decide trans    (inst e (inst (sk2 b e) (inst (sk2 c (sk2 b e))
	   done)))))))))))).

geothm 25 [directed,trans]
          [(r a b),(r b c),(r a e)]
          (exists X\ and (r e X) (r c X))
          (decide directed (inst a (inst b (inst e 
	  (decide directed (inst b (inst c (inst (sk3 a b e) 
	  (decide trans    (inst e (inst (sk3 a b e) (inst (sk3 b c (sk3 a b e))
	   done)))))))))))).

% Change 25 to replace (sk3 _ _ _) with just sk0.
geothm 26 [directed,trans]
          [(r a b),(r b c),(r a e)]
          (exists X\ and (r e X) (r c X))
          (decide directed (inst a (inst b (inst e 
          (decide directed (inst b (inst c (inst sk0
	  (decide trans    (inst e (inst sk0 (inst sk0
	   done)))))))))))).

% The following is hybrid: formulas with strong quantifiers but proof
% evidence with explicitly offered terms for allC (via the client
% constructor.)

geothm 31 [serial]
          []  
          (exists x\ exists y\ exists z\ and (r a x) (and (r x y) (r y z)))
          (decide serial (inst a (client (sk1 a)
          (decide serial (inst (sk1 a) (client (sk1 (sk1 a))
          (decide serial (inst (sk1 (sk1 a)) (client (sk1 (sk1 (sk1 a)))
           done))))))))).

geothm 32 [serial, sym, trans]
          []
          (r a a)
          (decide serial    (inst a (client (sk1 a)
          (decide sym       (inst a (inst (sk1 a)
          (decide trans     (inst a (inst (sk1 a) (inst a done)))))))))).

geothm 33 [directed]
          [(r a b),(r a c)]
          (exists X\ and (r b X) (r c X))
          (decide directed (inst a (inst b (inst c (client (sk2 b c) done))))).

geothm 34 [directed, trans]
          [(r a b),(r b c),(r a e)]
          (exists X\ and (r e X) (r c X))
          (decide directed (inst a (inst b (inst e (client (sk2 b e)
          (decide directed (inst b (inst c (inst (sk2 b e) (client (sk2 c (sk2 b e))
	  (decide trans    (inst e (inst (sk2 b e) (inst (sk2 c (sk2 b e))
	   done)))))))))))))).

check I :- geothm I Clauses Atoms Goal Cert,
           foldr (z\w\y\ y = (imp z w)) Atoms Goal Mid,
	   foldr (z\w\y\ sigma Clause\ theory z Clause, y = (imp Clause w)) Clauses Mid Theorem,
	   polarize_fc Theorem Polarized,
	   lkf_entry (initialize Clauses Cert) Polarized.

test_all :- geothm I _ _ _ _, term_to_string I Str, print Str, print "  ", 
            test_spec I, print "\n", fail.

test_spec I :- (check I, print "#", fail) ; true.

% This polarization uses the geometric formulas into forward-chaining inferences.
polarize_fc (imp Clause Target) (D !-! S) :- polarize_g Clause D, polarize_fc Target S.
polarize_fc (exists B) (some C)           :- pi x\ polarize_fc (B x) (C x).
polarize_fc (and B1 B2) (C1 &+& C2)       &
polarize_fc (or  B1 B2) (C1 !+! C2)       :- polarize_fc B1 C1, polarize_fc B2 C2.
polarize_fc A (p (coe A)) :- atomic A.

polarize_g (forall C) (some D)            :- pi x\ polarize_g (C x) (D x).
polarize_g (imp A C)  ((p (coe A)) &+& D) :- atomic A, polarize_g C D.
polarize_g C D                            :- polarize_h C D.

polarize_h A (n (coe A))           :- atomic A.
polarize_h (exists B)  (all C)     :- pi x\ polarize_h (B x) (C x).
polarize_h (or  B1 B2) (C1 &-& C2) & 
polarize_h (and B1 B2) (C1 !-! C2) :- polarize_h B1 C1, polarize_h B2 C2.
