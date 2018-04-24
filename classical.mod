module classical.

% By specifying print names (pname) for all signature items, we can
% get copy clauses for free.

copyi    T S :- fun_pname T Name L,  fun_pname S Name K,  mappred copyi L K.
copybool T S :- pred_pname T Name L, pred_pname S Name K, mappred copyi L K.

atomic A :- pred_pname A _ _.

% Declare some predicates and functions to be used later in examples.

pred_pname m       "m"  [].
pred_pname q       "q"  [].
pred_pname (s X)   "s"  [X].
pred_pname (r X Y) "r"  [X,Y].

fun_pname  a      "a" [].
fun_pname  b      "b" [].
fun_pname  c      "c" [].
fun_pname  d      "d" [].
fun_pname  e      "e" [].

fun_pname (f X)   "f" [X].

fun_pname (h X Y) "h" [X, Y].
fun_pname (g X Y) "g" [X, Y].
