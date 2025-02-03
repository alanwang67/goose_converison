(* autogenerated by goose proofgen (types); do not modify *)
From New.code Require Import errors.
From New.golang Require Import theory.

Axiom falso : False.

Module errorString.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  s' : go_string;
}.
End def.
End errorString.


Global Instance settable_errorString `{ffi_syntax}: Settable _ :=
  settable! errorString.mk < errorString.s' >.
Global Instance into_val_errorString `{ffi_syntax} : IntoVal errorString.t.
Admitted.

Global Instance into_val_typed_errorString `{ffi_syntax} : IntoValTyped errorString.t errors.errorString :=
{|
  default_val := errorString.mk (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_errorString_s `{ffi_syntax} : IntoValStructField "s" errors.errorString errorString.s'.
Admitted.

Instance wp_struct_make_errorString `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} s':
  PureWp True
    (struct.make errors.errorString (alist_val [
      "s" ::= #s'
    ]))%V
    #(errorString.mk s').
Admitted.

Module joinError.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  errs' : slice.t;
}.
End def.
End joinError.


Global Instance settable_joinError `{ffi_syntax}: Settable _ :=
  settable! joinError.mk < joinError.errs' >.
Global Instance into_val_joinError `{ffi_syntax} : IntoVal joinError.t.
Admitted.

Global Instance into_val_typed_joinError `{ffi_syntax} : IntoValTyped joinError.t errors.joinError :=
{|
  default_val := joinError.mk (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_joinError_errs `{ffi_syntax} : IntoValStructField "errs" errors.joinError joinError.errs'.
Admitted.

Instance wp_struct_make_joinError `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} errs':
  PureWp True
    (struct.make errors.joinError (alist_val [
      "errs" ::= #errs'
    ]))%V
    #(joinError.mk errs').
Admitted.

(* autogenerated by proofgen (names); do not modify *)
Require Import New.code.errors.
Require Export New.proof.proof_prelude.
Module errors.
Section defs.
Class GlobalAddrs :=
{
  ErrUnsupported : loc;
  errorType : loc;
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
    ("ErrUnsupported"%go, ErrUnsupported);
    ("errorType"%go, errorType)
  ].

Definition is_defined := is_global_definitions errors.pkg_name' var_addrs errors.functions' errors.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
  "HErrUnsupported" ∷ ErrUnsupported ↦ (default_val interface.t) ∗
  "HerrorType" ∷ errorType ↦ (default_val interface.t).

Global Instance wp_globals_get_ErrUnsupported : 
  WpGlobalsGet errors.pkg_name' "ErrUnsupported" ErrUnsupported is_defined.
Proof. apply wp_globals_get'. reflexivity. Qed.

Global Instance wp_globals_get_errorType : 
  WpGlobalsGet errors.pkg_name' "errorType" errorType is_defined.
Proof. apply wp_globals_get'. reflexivity. Qed.

Global Instance wp_func_call_New : 
  WpFuncCall errors.pkg_name' "New" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Join : 
  WpFuncCall errors.pkg_name' "Join" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Unwrap : 
  WpFuncCall errors.pkg_name' "Unwrap" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Is : 
  WpFuncCall errors.pkg_name' "Is" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_is : 
  WpFuncCall errors.pkg_name' "is" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_As : 
  WpFuncCall errors.pkg_name' "As" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_as : 
  WpFuncCall errors.pkg_name' "as" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_errorString'ptr_Error : 
  WpMethodCall errors.pkg_name' "errorString'ptr" "Error" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_joinError'ptr_Error : 
  WpMethodCall errors.pkg_name' "joinError'ptr" "Error" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_joinError'ptr_Unwrap : 
  WpMethodCall errors.pkg_name' "joinError'ptr" "Unwrap" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

End defs.
End errors.
