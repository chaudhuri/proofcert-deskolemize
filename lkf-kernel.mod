module lkf-kernel.

% Possibily useful for debugging the kernel and an fpc.
% lkf_entry A B :- announce (lkf_entry A B).
% async A B     :- announce (async A B).
% sync  A B     :- announce (sync  A B).

lkf_entry Cert Form :- async Cert [Form].

async Cert nil :-
% spy(cutE Cert CertA CertB F),
  cutE Cert CertA CertB F,
  negate F NF, async CertA [F], async CertB [NF].

async Cert nil            :- 
% spy (decideE Cert Cert' I), 
 decideE Cert Cert' I, 
 storage I P, isPos P, sync Cert' P.

async Cert [t-|_].
async Cert [f-|Rest]        :- falseC Cert Cert', async Cert' Rest.
async Cert [d- A| Rest]     :- async Cert [A|Rest].
async Cert [(A !-! B)|Rest] :- orC Cert Cert', async Cert' [A, B|Rest].
async Cert [(A &-& B)|Rest] :- andC Cert CertA CertB, async CertA [A|Rest], async CertB [B|Rest].
async Cert [all B|Rest]     :- fix_bug Cert,
   allC Cert Cert',      pi w\          async (Cert' w) [B w|Rest].
async Cert [all B|Rest]     :-  
    allCx  Cert Cert' T, pi w\ (copyi T w) => async Cert'     [B w|Rest].
async Cert [C|Rest]         :- (isPos C ; isNegAtm C), 
% spy (storeC Cert Cert' I),
 storeC Cert Cert' I,
 storage I C => async Cert' Rest.

sync Cert t+        :- trueE Cert.
sync Cert (d+ A)    :- sync Cert A.
sync Cert N         :- isNeg N, releaseE Cert Cert', async Cert' [N].
sync Cert (p A)     :- initialE Cert I, storage I (n A).
sync Cert (A &+& B) :- andE Cert CertA CertB, sync CertA A, sync CertB B.
sync Cert (A !+! B) :- orE Cert Cert' C, ((C = left,  sync Cert' A); (C = right, sync Cert' B)).

sync Cert (some B)  :- someE  Cert Cert' T, copyi T T', sync Cert' (B T').
sync Cert (some B)  :- someEx Cert Cert', sync Cert' (B T).

