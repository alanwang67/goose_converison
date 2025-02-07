(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.grove_prelude.
Require Export New.generatedproof.github_com.mit_pdos.gokv.grove_ffi.
Require Export New.generatedproof.github_com.mit_pdos.gokv.reconnectclient.
Require Export New.generatedproof.github_com.tchajed.marshal.
Require Export New.generatedproof.log.
Require Export New.generatedproof.sync.
Require Export New.generatedproof.github_com.goose_lang.std.
Require Export New.generatedproof.github_com.mit_pdos.gokv.asyncfile.
Require Export New.generatedproof.github_com.mit_pdos.gokv.urpc.
Require Export New.code.github_com.mit_pdos.gokv.vrsm.paxos.
Require Export New.golang.theory.

Module paxos.
Axiom falso : False.
Module singleClerk.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  cl' : loc;
}.
End def.
End singleClerk.


Global Instance settable_singleClerk `{ffi_syntax}: Settable _ :=
  settable! singleClerk.mk < singleClerk.cl' >.
Global Instance into_val_singleClerk `{ffi_syntax} : IntoVal singleClerk.t.
Admitted.

Global Instance into_val_typed_singleClerk `{ffi_syntax} : IntoValTyped singleClerk.t paxos.singleClerk :=
{|
  default_val := singleClerk.mk (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_singleClerk_cl `{ffi_syntax} : IntoValStructField "cl" paxos.singleClerk singleClerk.cl'.
Admitted.

Global Instance wp_struct_make_singleClerk `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} cl':
  PureWp True
    (struct.make paxos.singleClerk (alist_val [
      "cl" ::= #cl'
    ]))%V
    #(singleClerk.mk cl').
Admitted.


Module Error.
Section def.
Context `{ffi_syntax}.
Definition t := w64.
End def.
End Error.
Module applyAsFollowerArgs.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  epoch' : w64;
  nextIndex' : w64;
  state' : slice.t;
}.
End def.
End applyAsFollowerArgs.


Global Instance settable_applyAsFollowerArgs `{ffi_syntax}: Settable _ :=
  settable! applyAsFollowerArgs.mk < applyAsFollowerArgs.epoch'; applyAsFollowerArgs.nextIndex'; applyAsFollowerArgs.state' >.
Global Instance into_val_applyAsFollowerArgs `{ffi_syntax} : IntoVal applyAsFollowerArgs.t.
Admitted.

Global Instance into_val_typed_applyAsFollowerArgs `{ffi_syntax} : IntoValTyped applyAsFollowerArgs.t paxos.applyAsFollowerArgs :=
{|
  default_val := applyAsFollowerArgs.mk (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_applyAsFollowerArgs_epoch `{ffi_syntax} : IntoValStructField "epoch" paxos.applyAsFollowerArgs applyAsFollowerArgs.epoch'.
Admitted.

Global Instance into_val_struct_field_applyAsFollowerArgs_nextIndex `{ffi_syntax} : IntoValStructField "nextIndex" paxos.applyAsFollowerArgs applyAsFollowerArgs.nextIndex'.
Admitted.

Global Instance into_val_struct_field_applyAsFollowerArgs_state `{ffi_syntax} : IntoValStructField "state" paxos.applyAsFollowerArgs applyAsFollowerArgs.state'.
Admitted.

Global Instance wp_struct_make_applyAsFollowerArgs `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} epoch' nextIndex' state':
  PureWp True
    (struct.make paxos.applyAsFollowerArgs (alist_val [
      "epoch" ::= #epoch';
      "nextIndex" ::= #nextIndex';
      "state" ::= #state'
    ]))%V
    #(applyAsFollowerArgs.mk epoch' nextIndex' state').
Admitted.

Module applyAsFollowerReply.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  err' : Error.t;
}.
End def.
End applyAsFollowerReply.


Global Instance settable_applyAsFollowerReply `{ffi_syntax}: Settable _ :=
  settable! applyAsFollowerReply.mk < applyAsFollowerReply.err' >.
Global Instance into_val_applyAsFollowerReply `{ffi_syntax} : IntoVal applyAsFollowerReply.t.
Admitted.

Global Instance into_val_typed_applyAsFollowerReply `{ffi_syntax} : IntoValTyped applyAsFollowerReply.t paxos.applyAsFollowerReply :=
{|
  default_val := applyAsFollowerReply.mk (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_applyAsFollowerReply_err `{ffi_syntax} : IntoValStructField "err" paxos.applyAsFollowerReply applyAsFollowerReply.err'.
Admitted.

Global Instance wp_struct_make_applyAsFollowerReply `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} err':
  PureWp True
    (struct.make paxos.applyAsFollowerReply (alist_val [
      "err" ::= #err'
    ]))%V
    #(applyAsFollowerReply.mk err').
Admitted.

Module enterNewEpochArgs.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  epoch' : w64;
}.
End def.
End enterNewEpochArgs.


Global Instance settable_enterNewEpochArgs `{ffi_syntax}: Settable _ :=
  settable! enterNewEpochArgs.mk < enterNewEpochArgs.epoch' >.
Global Instance into_val_enterNewEpochArgs `{ffi_syntax} : IntoVal enterNewEpochArgs.t.
Admitted.

Global Instance into_val_typed_enterNewEpochArgs `{ffi_syntax} : IntoValTyped enterNewEpochArgs.t paxos.enterNewEpochArgs :=
{|
  default_val := enterNewEpochArgs.mk (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_enterNewEpochArgs_epoch `{ffi_syntax} : IntoValStructField "epoch" paxos.enterNewEpochArgs enterNewEpochArgs.epoch'.
Admitted.

Global Instance wp_struct_make_enterNewEpochArgs `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} epoch':
  PureWp True
    (struct.make paxos.enterNewEpochArgs (alist_val [
      "epoch" ::= #epoch'
    ]))%V
    #(enterNewEpochArgs.mk epoch').
Admitted.

Module enterNewEpochReply.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  err' : Error.t;
  acceptedEpoch' : w64;
  nextIndex' : w64;
  state' : slice.t;
}.
End def.
End enterNewEpochReply.


Global Instance settable_enterNewEpochReply `{ffi_syntax}: Settable _ :=
  settable! enterNewEpochReply.mk < enterNewEpochReply.err'; enterNewEpochReply.acceptedEpoch'; enterNewEpochReply.nextIndex'; enterNewEpochReply.state' >.
Global Instance into_val_enterNewEpochReply `{ffi_syntax} : IntoVal enterNewEpochReply.t.
Admitted.

Global Instance into_val_typed_enterNewEpochReply `{ffi_syntax} : IntoValTyped enterNewEpochReply.t paxos.enterNewEpochReply :=
{|
  default_val := enterNewEpochReply.mk (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_enterNewEpochReply_err `{ffi_syntax} : IntoValStructField "err" paxos.enterNewEpochReply enterNewEpochReply.err'.
Admitted.

Global Instance into_val_struct_field_enterNewEpochReply_acceptedEpoch `{ffi_syntax} : IntoValStructField "acceptedEpoch" paxos.enterNewEpochReply enterNewEpochReply.acceptedEpoch'.
Admitted.

Global Instance into_val_struct_field_enterNewEpochReply_nextIndex `{ffi_syntax} : IntoValStructField "nextIndex" paxos.enterNewEpochReply enterNewEpochReply.nextIndex'.
Admitted.

Global Instance into_val_struct_field_enterNewEpochReply_state `{ffi_syntax} : IntoValStructField "state" paxos.enterNewEpochReply enterNewEpochReply.state'.
Admitted.

Global Instance wp_struct_make_enterNewEpochReply `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} err' acceptedEpoch' nextIndex' state':
  PureWp True
    (struct.make paxos.enterNewEpochReply (alist_val [
      "err" ::= #err';
      "acceptedEpoch" ::= #acceptedEpoch';
      "nextIndex" ::= #nextIndex';
      "state" ::= #state'
    ]))%V
    #(enterNewEpochReply.mk err' acceptedEpoch' nextIndex' state').
Admitted.

Module applyReply.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  err' : Error.t;
  ret' : slice.t;
}.
End def.
End applyReply.


Global Instance settable_applyReply `{ffi_syntax}: Settable _ :=
  settable! applyReply.mk < applyReply.err'; applyReply.ret' >.
Global Instance into_val_applyReply `{ffi_syntax} : IntoVal applyReply.t.
Admitted.

Global Instance into_val_typed_applyReply `{ffi_syntax} : IntoValTyped applyReply.t paxos.applyReply :=
{|
  default_val := applyReply.mk (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_applyReply_err `{ffi_syntax} : IntoValStructField "err" paxos.applyReply applyReply.err'.
Admitted.

Global Instance into_val_struct_field_applyReply_ret `{ffi_syntax} : IntoValStructField "ret" paxos.applyReply applyReply.ret'.
Admitted.

Global Instance wp_struct_make_applyReply `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} err' ret':
  PureWp True
    (struct.make paxos.applyReply (alist_val [
      "err" ::= #err';
      "ret" ::= #ret'
    ]))%V
    #(applyReply.mk err' ret').
Admitted.

Module paxosState.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  epoch' : w64;
  acceptedEpoch' : w64;
  nextIndex' : w64;
  state' : slice.t;
  isLeader' : bool;
}.
End def.
End paxosState.


Global Instance settable_paxosState `{ffi_syntax}: Settable _ :=
  settable! paxosState.mk < paxosState.epoch'; paxosState.acceptedEpoch'; paxosState.nextIndex'; paxosState.state'; paxosState.isLeader' >.
Global Instance into_val_paxosState `{ffi_syntax} : IntoVal paxosState.t.
Admitted.

Global Instance into_val_typed_paxosState `{ffi_syntax} : IntoValTyped paxosState.t paxos.paxosState :=
{|
  default_val := paxosState.mk (default_val _) (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_paxosState_epoch `{ffi_syntax} : IntoValStructField "epoch" paxos.paxosState paxosState.epoch'.
Admitted.

Global Instance into_val_struct_field_paxosState_acceptedEpoch `{ffi_syntax} : IntoValStructField "acceptedEpoch" paxos.paxosState paxosState.acceptedEpoch'.
Admitted.

Global Instance into_val_struct_field_paxosState_nextIndex `{ffi_syntax} : IntoValStructField "nextIndex" paxos.paxosState paxosState.nextIndex'.
Admitted.

Global Instance into_val_struct_field_paxosState_state `{ffi_syntax} : IntoValStructField "state" paxos.paxosState paxosState.state'.
Admitted.

Global Instance into_val_struct_field_paxosState_isLeader `{ffi_syntax} : IntoValStructField "isLeader" paxos.paxosState paxosState.isLeader'.
Admitted.

Global Instance wp_struct_make_paxosState `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} epoch' acceptedEpoch' nextIndex' state' isLeader':
  PureWp True
    (struct.make paxos.paxosState (alist_val [
      "epoch" ::= #epoch';
      "acceptedEpoch" ::= #acceptedEpoch';
      "nextIndex" ::= #nextIndex';
      "state" ::= #state';
      "isLeader" ::= #isLeader'
    ]))%V
    #(paxosState.mk epoch' acceptedEpoch' nextIndex' state' isLeader').
Admitted.

Module Server.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  mu' : loc;
  ps' : loc;
  storage' : loc;
  clerks' : slice.t;
}.
End def.
End Server.


Global Instance settable_Server `{ffi_syntax}: Settable _ :=
  settable! Server.mk < Server.mu'; Server.ps'; Server.storage'; Server.clerks' >.
Global Instance into_val_Server `{ffi_syntax} : IntoVal Server.t.
Admitted.

Global Instance into_val_typed_Server `{ffi_syntax} : IntoValTyped Server.t paxos.Server :=
{|
  default_val := Server.mk (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Server_mu `{ffi_syntax} : IntoValStructField "mu" paxos.Server Server.mu'.
Admitted.

Global Instance into_val_struct_field_Server_ps `{ffi_syntax} : IntoValStructField "ps" paxos.Server Server.ps'.
Admitted.

Global Instance into_val_struct_field_Server_storage `{ffi_syntax} : IntoValStructField "storage" paxos.Server Server.storage'.
Admitted.

Global Instance into_val_struct_field_Server_clerks `{ffi_syntax} : IntoValStructField "clerks" paxos.Server Server.clerks'.
Admitted.

Global Instance wp_struct_make_Server `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} mu' ps' storage' clerks':
  PureWp True
    (struct.make paxos.Server (alist_val [
      "mu" ::= #mu';
      "ps" ::= #ps';
      "storage" ::= #storage';
      "clerks" ::= #clerks'
    ]))%V
    #(Server.mk mu' ps' storage' clerks').
Admitted.


Section names.

Class GlobalAddrs :=
{
}.

Context `{!GlobalAddrs}.
Context `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
  ].

Definition is_defined := is_global_definitions paxos.pkg_name' var_addrs paxos.functions' paxos.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
True.

Global Instance wp_func_call_MakeSingleClerk :
  WpFuncCall paxos.pkg_name' "MakeSingleClerk" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_encodeApplyAsFollowerArgs :
  WpFuncCall paxos.pkg_name' "encodeApplyAsFollowerArgs" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_decodeApplyAsFollowerArgs :
  WpFuncCall paxos.pkg_name' "decodeApplyAsFollowerArgs" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_decodeApplyAsFollowerReply :
  WpFuncCall paxos.pkg_name' "decodeApplyAsFollowerReply" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_encodeApplyAsFollowerReply :
  WpFuncCall paxos.pkg_name' "encodeApplyAsFollowerReply" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_encodeEnterNewEpochArgs :
  WpFuncCall paxos.pkg_name' "encodeEnterNewEpochArgs" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_decodeEnterNewEpochArgs :
  WpFuncCall paxos.pkg_name' "decodeEnterNewEpochArgs" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_decodeEnterNewEpochReply :
  WpFuncCall paxos.pkg_name' "decodeEnterNewEpochReply" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_encodeEnterNewEpochReply :
  WpFuncCall paxos.pkg_name' "encodeEnterNewEpochReply" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_encodeApplyReply :
  WpFuncCall paxos.pkg_name' "encodeApplyReply" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_decodeApplyReply :
  WpFuncCall paxos.pkg_name' "decodeApplyReply" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_boolToU64 :
  WpFuncCall paxos.pkg_name' "boolToU64" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_encodePaxosState :
  WpFuncCall paxos.pkg_name' "encodePaxosState" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_decodePaxosState :
  WpFuncCall paxos.pkg_name' "decodePaxosState" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_makeServer :
  WpFuncCall paxos.pkg_name' "makeServer" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_StartServer :
  WpFuncCall paxos.pkg_name' "StartServer" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_singleClerk'ptr_TryBecomeLeader : 
  WpMethodCall paxos.pkg_name' "singleClerk'ptr" "TryBecomeLeader" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_singleClerk'ptr_applyAsFollower : 
  WpMethodCall paxos.pkg_name' "singleClerk'ptr" "applyAsFollower" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_singleClerk'ptr_enterNewEpoch : 
  WpMethodCall paxos.pkg_name' "singleClerk'ptr" "enterNewEpoch" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Server'ptr_TryAcquire : 
  WpMethodCall paxos.pkg_name' "Server'ptr" "TryAcquire" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Server'ptr_TryBecomeLeader : 
  WpMethodCall paxos.pkg_name' "Server'ptr" "TryBecomeLeader" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Server'ptr_WeakRead : 
  WpMethodCall paxos.pkg_name' "Server'ptr" "WeakRead" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Server'ptr_applyAsFollower : 
  WpMethodCall paxos.pkg_name' "Server'ptr" "applyAsFollower" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Server'ptr_enterNewEpoch : 
  WpMethodCall paxos.pkg_name' "Server'ptr" "enterNewEpoch" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Server'ptr_withLock : 
  WpMethodCall paxos.pkg_name' "Server'ptr" "withLock" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

End names.
End paxos.
