sig geo-examples.
accum_sig lib.
accum_sig classical.
accum_sig lkf-formulas.
accum_sig lkf-certificates.
accum_sig lkf-kernel.
accum_sig geo-fpc.

type coe  bool -> atm.

type check   int -> o.
type geothm  int -> list index -> list bool -> bool -> cert -> o.
type theory   index -> bool -> o.
type polarize_fc, polarize_g, polarize_h    bool -> form -> o.

type test_all   o.
type test_spec  int -> o.

% Skolem functions.  No print name declared (thus, no copy clauses).
type sk0    i.
type sk1    i -> i.
type sk2    i -> i -> i.
type sk3    i -> i -> i -> i.

type  trans, directed, ref, sym, euclidean, connected, serial    index.
type  sk1serial, sk2directed, sk3directed index.
