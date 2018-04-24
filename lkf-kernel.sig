sig lkf-kernel.
accum_sig lib.
accum_sig classical.
accum_sig lkf-certificates.

type lkf_entry      cert -> form -> o.

type async           cert -> list form -> o.
type sync            cert ->      form -> o.
type storage        index ->      form -> o.
