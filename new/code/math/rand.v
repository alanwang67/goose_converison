(* autogenerated from math/rand *)
From New.golang Require Import defn.

Module rand.
Section code.
Context `{ffi_syntax}.


Axiom ke'init : val.

Axiom we'init : val.

Axiom fe'init : val.

Axiom kn'init : val.

Axiom wn'init : val.

Axiom fn'init : val.

Axiom globalRandGenerator'init : val.

Axiom randautoseed'init : val.

Axiom rngCooked'init : val.

Definition pkg_name' : go_string := "math/rand".

Definition vars' : list (go_string * go_type) := [("ke"%go, arrayT 256 uint32T); ("we"%go, arrayT 256 float32T); ("fe"%go, arrayT 256 float32T); ("kn"%go, arrayT 128 uint32T); ("wn"%go, arrayT 128 float32T); ("fn"%go, arrayT 128 float32T); ("globalRandGenerator"%go, atomic.Pointer Rand); ("randautoseed"%go, ptrT); ("rngCooked"%go, arrayT 607 int64T)].

Definition functions' : list (go_string * val) := [].

Definition msets' : list (go_string * (list (go_string * val))) := [].

End code.
End rand.
