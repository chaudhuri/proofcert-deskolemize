sig lkf-certificates.
accum_sig lkf-formulas.

kind cert, index                         type.
kind choice                              type.
type left, right                       choice.

type allC                  cert -> (i -> cert) -> o.
type andC                  cert -> cert -> cert -> o.
type andE                  cert -> cert -> cert -> o.
type cutE                  cert -> cert -> cert -> form -> o.
type decideE               cert -> cert -> index -> o.
type falseC                cert -> cert -> o.
type initialE              cert -> index -> o.
type orC                   cert -> cert -> o.
type orE                   cert -> cert -> choice -> o.
type releaseE              cert -> cert -> o.
type someE                 cert -> cert -> i -> o.
type storeC                cert -> cert -> index -> o.
type trueE                 cert -> o.

%  Extensions to accommodate translation of client terms to kernel terms
type someEx    cert -> cert      -> o.
type allCx     cert -> cert -> i -> o.
