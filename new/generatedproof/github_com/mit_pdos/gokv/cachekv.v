(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.grove_prelude.
Require Export New.generatedproof.sync.
Require Export New.generatedproof.github_com.mit_pdos.gokv.grove_ffi.
Require Export New.generatedproof.github_com.mit_pdos.gokv.kv.
Require Export New.generatedproof.github_com.tchajed.marshal.
Require Export New.code.github_com.mit_pdos.gokv.cachekv.
Require Export New.golang.theory.

Module cachekv.
Axiom falso : False.
Module cacheValue.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  v' : go_string;
  l' : w64;
}.
End def.
End cacheValue.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_cacheValue `{ffi_syntax}: Settable _ :=
  settable! cacheValue.mk < cacheValue.v'; cacheValue.l' >.
Global Instance into_val_cacheValue `{ffi_syntax} : IntoVal cacheValue.t.
Admitted.

Global Instance into_val_typed_cacheValue `{ffi_syntax} : IntoValTyped cacheValue.t cachekv.cacheValue :=
{|
  default_val := cacheValue.mk (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_cacheValue_v `{ffi_syntax} : IntoValStructField "v" cachekv.cacheValue cacheValue.v'.
Admitted.

Global Instance into_val_struct_field_cacheValue_l `{ffi_syntax} : IntoValStructField "l" cachekv.cacheValue cacheValue.l'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_cacheValue `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} v' l':
  PureWp True
    (struct.make cachekv.cacheValue (alist_val [
      "v" ::= #v';
      "l" ::= #l'
    ]))%V
    #(cacheValue.mk v' l').
Admitted.


Global Instance cacheValue_struct_fields_split dq l (v : cacheValue.t) :
  StructFieldsSplit dq l v (
    "Hv" ∷ l ↦s[cachekv.cacheValue :: "v"]{dq} v.(cacheValue.v') ∗
    "Hl" ∷ l ↦s[cachekv.cacheValue :: "l"]{dq} v.(cacheValue.l')
  ).
Admitted.

End instances.
Module CacheKv.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  kv' : kv.KvCput.t;
  mu' : loc;
  cache' : loc;
}.
End def.
End CacheKv.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_CacheKv `{ffi_syntax}: Settable _ :=
  settable! CacheKv.mk < CacheKv.kv'; CacheKv.mu'; CacheKv.cache' >.
Global Instance into_val_CacheKv `{ffi_syntax} : IntoVal CacheKv.t.
Admitted.

Global Instance into_val_typed_CacheKv `{ffi_syntax} : IntoValTyped CacheKv.t cachekv.CacheKv :=
{|
  default_val := CacheKv.mk (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_CacheKv_kv `{ffi_syntax} : IntoValStructField "kv" cachekv.CacheKv CacheKv.kv'.
Admitted.

Global Instance into_val_struct_field_CacheKv_mu `{ffi_syntax} : IntoValStructField "mu" cachekv.CacheKv CacheKv.mu'.
Admitted.

Global Instance into_val_struct_field_CacheKv_cache `{ffi_syntax} : IntoValStructField "cache" cachekv.CacheKv CacheKv.cache'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_CacheKv `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} kv' mu' cache':
  PureWp True
    (struct.make cachekv.CacheKv (alist_val [
      "kv" ::= #kv';
      "mu" ::= #mu';
      "cache" ::= #cache'
    ]))%V
    #(CacheKv.mk kv' mu' cache').
Admitted.


Global Instance CacheKv_struct_fields_split dq l (v : CacheKv.t) :
  StructFieldsSplit dq l v (
    "Hkv" ∷ l ↦s[cachekv.CacheKv :: "kv"]{dq} v.(CacheKv.kv') ∗
    "Hmu" ∷ l ↦s[cachekv.CacheKv :: "mu"]{dq} v.(CacheKv.mu') ∗
    "Hcache" ∷ l ↦s[cachekv.CacheKv :: "cache"]{dq} v.(CacheKv.cache')
  ).
Admitted.

End instances.

Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions cachekv.pkg_name' var_addrs cachekv.functions' cachekv.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_DecodeValue :
  WpFuncCall cachekv.pkg_name' "DecodeValue" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_EncodeValue :
  WpFuncCall cachekv.pkg_name' "EncodeValue" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_max :
  WpFuncCall cachekv.pkg_name' "max" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_Make :
  WpFuncCall cachekv.pkg_name' "Make" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_CacheKv'ptr_Get :
  WpMethodCall cachekv.pkg_name' "CacheKv'ptr" "Get" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_CacheKv'ptr_GetAndCache :
  WpMethodCall cachekv.pkg_name' "CacheKv'ptr" "GetAndCache" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_CacheKv'ptr_Put :
  WpMethodCall cachekv.pkg_name' "CacheKv'ptr" "Put" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

End names.
End cachekv.
