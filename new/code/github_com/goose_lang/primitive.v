(* autogenerated from github.com/goose-lang/primitive *)
From New.golang Require Import defn.

Require Export New.trusted_code.github_com.goose_lang.primitive.
Import primitive.
Module primitive.
Section code.
Context `{ffi_syntax}.


Definition pkg_name' : go_string := "github.com/goose-lang/primitive".

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [("UInt64Put"%go, UInt64Put); ("Assume"%go, Assume)].

Definition msets' : list (go_string * (list (go_string * val))) := [].

Axiom _'init : val.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' vars' functions' msets' (λ: <>,
      exception_do (do:  #())
      ).

End code.
End primitive.
