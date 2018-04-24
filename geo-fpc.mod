% This fpc uses skolemized proof evidence in provide a proof with
% eigenvariables. 

module geo-fpc.

orC    (initialize Clauses Cert)         (initialize Clauses Cert).
storeC (initialize [Index|Clauses] Cert) (initialize Clauses Cert) Index.
storeC (initialize [] Cert) (asyn Cert) indx.
storeC (asyn Cert) (asyn Cert) indx.
orC    (asyn Cert) (asyn Cert).

decideE   (asyn (decide Index Cert)) (syn Cert) Index.
decideE   (asyn done) finish indx.

someE     (syn (inst T Cert)) (syn Cert) T.
andE      (syn Cert) immediate (syn Cert).
initialE  immediate indx.

releaseE  (syn Cert) (asyn Cert).

someEx    finish finish.
andE      finish finish finish.
orE       finish finish Choice.
initialE  finish indx.

andC      (asyn (andc Cert Cert')) (asyn Cert) (asyn Cert').

% The generic way to extend an FPC of skolemized proof evidence of a
% skolemized formula so that the skolemized proof evidence can serve
% as proof evidence for the original formula.

allCx Cert Cert Sk.
