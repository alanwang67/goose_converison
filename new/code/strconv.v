(* autogenerated from strconv *)
From New.golang Require Import defn.

Module strconv.
Section code.
Context `{ffi_syntax}.


Axiom optimize'init : val.

Axiom powtab'init : val.

Axiom float64pow10'init : val.

Axiom float32pow10'init : val.

Axiom ErrRange'init : val.

Axiom ErrSyntax'init : val.

Axiom leftcheats'init : val.

Axiom detailedPowersOfTen'init : val.

Axiom float32info'init : val.

Axiom float64info'init : val.

Axiom uint64pow10'init : val.

Axiom isPrint16'init : val.

Axiom isNotPrint16'init : val.

Axiom isPrint32'init : val.

Axiom isNotPrint32'init : val.

Axiom isGraphic'init : val.

Definition pkg_name' : go_string := "strconv".

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [].

Definition msets' : list (go_string * (list (go_string * val))) := [].

Axiom _'init : val.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' vars' functions' msets' (λ: <>,
      exception_do (do:  (optimize'init #());;;
      do:  (powtab'init #());;;
      do:  (float64pow10'init #());;;
      do:  (float32pow10'init #());;;
      do:  (ErrRange'init #());;;
      do:  (ErrSyntax'init #());;;
      do:  (leftcheats'init #());;;
      do:  (detailedPowersOfTen'init #());;;
      do:  (float32info'init #());;;
      do:  (float64info'init #());;;
      do:  (uint64pow10'init #());;;
      do:  (isPrint16'init #());;;
      do:  (isNotPrint16'init #());;;
      do:  (isPrint32'init #());;;
      do:  (isNotPrint32'init #());;;
      do:  (isGraphic'init #()))
      ).

End code.
End strconv.
