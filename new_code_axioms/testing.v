(* autogenerated by goose axiom generator; do not modify *)
From New.golang Require Import defn.

Section axioms.
Context `{ffi_syntax}.

Axiom InternalBenchmark : go_type.
Axiom B : go_type.
Axiom BenchmarkResult : go_type.
Axiom PB : go_type.
Axiom CoverBlock : go_type.
Axiom Cover : go_type.
Axiom InternalExample : go_type.
Axiom InternalFuzzTarget : go_type.
Axiom F : go_type.
Axiom TB : go_type.
Axiom T : go_type.
Axiom InternalTest : go_type.
Axiom M : go_type.
Definition pkg_name' : go_string := "testing".
Axiom initialize' : val.

End axioms.
