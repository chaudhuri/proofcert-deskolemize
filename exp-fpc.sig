sig exp-fpc.

accum_sig lkf-certificates.
accum_sig lib.
accum_sig classical.

kind et       type.  % expansion trees
kind qet      type.  % quantified trees : introducing select vars

type eIntro            (i -> qet) -> qet.
type eC                et -> qet.

type eTrue, eFalse     et.
type eLit              et.
type eAnd, eOr	       et -> et -> et.
type eAll              i  -> et -> et.	
type eSome             list (pair i et) -> et.
type eSomeOrd          list (pair i et) -> et.

kind address  type.
type root     address.
type lf, rg   address -> address.
type dn       address -> address.

type idx      address -> index.

typeabbrev context     list (pair address et).
type astate, dstate    context -> context         -> cert.
type sstate            context -> pair address et -> cert.
