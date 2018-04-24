sig exp-examples.
accum_sig lib.
accum_sig classical.
accum_sig lkf-formulas.
accum_sig lkf-kernel.
accum_sig exp-fpc.

% First-order terms
type a'        i.
type b'        i.
type f'        i -> i.
type f         i -> i.
type h'        i -> i -> i.
type g         i -> i -> i.

% Predicates in the "client space"
type q'        bool.
type s         i -> bool.
type r'        i -> bool.

% Names provided for the internal space of formulas
type qq'       atm.
type rr'       i -> atm.

% Constructors for atoms and polarization
type delay-, polarize  bool -> form -> o.
type atom   string -> list i -> atm.

type eexample   int -> qet -> bool -> o.
type test       int -> o.
type check_exp  qet -> form -> o.

type test_all   o.
type test_spec  qet -> form -> o.

type translate bool -> et -> bool -> bool -> et -> bool -> o.

type skexample  int -> qet -> bool -> bool -> o.

type skolemized    bool -> bool -> o.
type sk_positive   bool -> bool -> o.