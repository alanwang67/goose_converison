(* autogenerated from internal/race *)
From New.golang Require Import defn.

Module race.
Section code.
Context `{ffi_syntax}.


Definition Enabled : expr := #false.

Definition pkg_name' : go_string := "internal/race".

Definition vars' : list (go_string * go_type) := [].

Definition functions' : list (go_string * val) := [].

Definition msets' : list (go_string * (list (go_string * val))) := [].

Axiom _'init : val.

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' vars' functions' msets' (λ: <>,
      exception_do (do:  #())
      ).

End code.
End race.
