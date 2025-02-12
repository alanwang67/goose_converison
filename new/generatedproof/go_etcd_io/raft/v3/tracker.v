(* autogenerated by goose proofgen (types); do not modify *)
Require Export New.proof.proof_prelude.
Require Export New.generatedproof.fmt.
Require Export New.generatedproof.sort.
Require Export New.generatedproof.strings.
Require Export New.generatedproof.go_etcd_io.raft.v3.quorum.
Require Export New.generatedproof.go_etcd_io.raft.v3.quorum.slices64.
Require Export New.generatedproof.go_etcd_io.raft.v3.raftpb.
Require Export New.code.go_etcd_io.raft.v3.tracker.
Require Export New.golang.theory.

Module tracker.
Axiom falso : False.
Module inflight.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  index' : w64;
  bytes' : w64;
}.
End def.
End inflight.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_inflight `{ffi_syntax}: Settable _ :=
  settable! inflight.mk < inflight.index'; inflight.bytes' >.
Global Instance into_val_inflight `{ffi_syntax} : IntoVal inflight.t.
Admitted.

Global Instance into_val_typed_inflight `{ffi_syntax} : IntoValTyped inflight.t tracker.inflight :=
{|
  default_val := inflight.mk (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_inflight_index `{ffi_syntax} : IntoValStructField "index" tracker.inflight inflight.index'.
Admitted.

Global Instance into_val_struct_field_inflight_bytes `{ffi_syntax} : IntoValStructField "bytes" tracker.inflight inflight.bytes'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_inflight `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} index' bytes':
  PureWp True
    (struct.make tracker.inflight (alist_val [
      "index" ::= #index';
      "bytes" ::= #bytes'
    ]))%V
    #(inflight.mk index' bytes').
Admitted.


Global Instance inflight_struct_fields_split dq l (v : inflight.t) :
  StructFieldsSplit dq l v (
    "Hindex" ∷ l ↦s[tracker.inflight :: "index"]{dq} v.(inflight.index') ∗
    "Hbytes" ∷ l ↦s[tracker.inflight :: "bytes"]{dq} v.(inflight.bytes')
  ).
Admitted.

End instances.
Module Inflights.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  start' : w64;
  count' : w64;
  bytes' : w64;
  size' : w64;
  maxBytes' : w64;
  buffer' : slice.t;
}.
End def.
End Inflights.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_Inflights `{ffi_syntax}: Settable _ :=
  settable! Inflights.mk < Inflights.start'; Inflights.count'; Inflights.bytes'; Inflights.size'; Inflights.maxBytes'; Inflights.buffer' >.
Global Instance into_val_Inflights `{ffi_syntax} : IntoVal Inflights.t.
Admitted.

Global Instance into_val_typed_Inflights `{ffi_syntax} : IntoValTyped Inflights.t tracker.Inflights :=
{|
  default_val := Inflights.mk (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Inflights_start `{ffi_syntax} : IntoValStructField "start" tracker.Inflights Inflights.start'.
Admitted.

Global Instance into_val_struct_field_Inflights_count `{ffi_syntax} : IntoValStructField "count" tracker.Inflights Inflights.count'.
Admitted.

Global Instance into_val_struct_field_Inflights_bytes `{ffi_syntax} : IntoValStructField "bytes" tracker.Inflights Inflights.bytes'.
Admitted.

Global Instance into_val_struct_field_Inflights_size `{ffi_syntax} : IntoValStructField "size" tracker.Inflights Inflights.size'.
Admitted.

Global Instance into_val_struct_field_Inflights_maxBytes `{ffi_syntax} : IntoValStructField "maxBytes" tracker.Inflights Inflights.maxBytes'.
Admitted.

Global Instance into_val_struct_field_Inflights_buffer `{ffi_syntax} : IntoValStructField "buffer" tracker.Inflights Inflights.buffer'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Inflights `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} start' count' bytes' size' maxBytes' buffer':
  PureWp True
    (struct.make tracker.Inflights (alist_val [
      "start" ::= #start';
      "count" ::= #count';
      "bytes" ::= #bytes';
      "size" ::= #size';
      "maxBytes" ::= #maxBytes';
      "buffer" ::= #buffer'
    ]))%V
    #(Inflights.mk start' count' bytes' size' maxBytes' buffer').
Admitted.


Global Instance Inflights_struct_fields_split dq l (v : Inflights.t) :
  StructFieldsSplit dq l v (
    "Hstart" ∷ l ↦s[tracker.Inflights :: "start"]{dq} v.(Inflights.start') ∗
    "Hcount" ∷ l ↦s[tracker.Inflights :: "count"]{dq} v.(Inflights.count') ∗
    "Hbytes" ∷ l ↦s[tracker.Inflights :: "bytes"]{dq} v.(Inflights.bytes') ∗
    "Hsize" ∷ l ↦s[tracker.Inflights :: "size"]{dq} v.(Inflights.size') ∗
    "HmaxBytes" ∷ l ↦s[tracker.Inflights :: "maxBytes"]{dq} v.(Inflights.maxBytes') ∗
    "Hbuffer" ∷ l ↦s[tracker.Inflights :: "buffer"]{dq} v.(Inflights.buffer')
  ).
Admitted.

End instances.

Module StateType.
Section def.
Context `{ffi_syntax}.
Definition t := w64.
End def.
End StateType.
Module Progress.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Match' : w64;
  Next' : w64;
  sentCommit' : w64;
  State' : StateType.t;
  PendingSnapshot' : w64;
  RecentActive' : bool;
  MsgAppFlowPaused' : bool;
  Inflights' : loc;
  IsLearner' : bool;
}.
End def.
End Progress.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_Progress `{ffi_syntax}: Settable _ :=
  settable! Progress.mk < Progress.Match'; Progress.Next'; Progress.sentCommit'; Progress.State'; Progress.PendingSnapshot'; Progress.RecentActive'; Progress.MsgAppFlowPaused'; Progress.Inflights'; Progress.IsLearner' >.
Global Instance into_val_Progress `{ffi_syntax} : IntoVal Progress.t.
Admitted.

Global Instance into_val_typed_Progress `{ffi_syntax} : IntoValTyped Progress.t tracker.Progress :=
{|
  default_val := Progress.mk (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Progress_Match `{ffi_syntax} : IntoValStructField "Match" tracker.Progress Progress.Match'.
Admitted.

Global Instance into_val_struct_field_Progress_Next `{ffi_syntax} : IntoValStructField "Next" tracker.Progress Progress.Next'.
Admitted.

Global Instance into_val_struct_field_Progress_sentCommit `{ffi_syntax} : IntoValStructField "sentCommit" tracker.Progress Progress.sentCommit'.
Admitted.

Global Instance into_val_struct_field_Progress_State `{ffi_syntax} : IntoValStructField "State" tracker.Progress Progress.State'.
Admitted.

Global Instance into_val_struct_field_Progress_PendingSnapshot `{ffi_syntax} : IntoValStructField "PendingSnapshot" tracker.Progress Progress.PendingSnapshot'.
Admitted.

Global Instance into_val_struct_field_Progress_RecentActive `{ffi_syntax} : IntoValStructField "RecentActive" tracker.Progress Progress.RecentActive'.
Admitted.

Global Instance into_val_struct_field_Progress_MsgAppFlowPaused `{ffi_syntax} : IntoValStructField "MsgAppFlowPaused" tracker.Progress Progress.MsgAppFlowPaused'.
Admitted.

Global Instance into_val_struct_field_Progress_Inflights `{ffi_syntax} : IntoValStructField "Inflights" tracker.Progress Progress.Inflights'.
Admitted.

Global Instance into_val_struct_field_Progress_IsLearner `{ffi_syntax} : IntoValStructField "IsLearner" tracker.Progress Progress.IsLearner'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Progress `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Match' Next' sentCommit' State' PendingSnapshot' RecentActive' MsgAppFlowPaused' Inflights' IsLearner':
  PureWp True
    (struct.make tracker.Progress (alist_val [
      "Match" ::= #Match';
      "Next" ::= #Next';
      "sentCommit" ::= #sentCommit';
      "State" ::= #State';
      "PendingSnapshot" ::= #PendingSnapshot';
      "RecentActive" ::= #RecentActive';
      "MsgAppFlowPaused" ::= #MsgAppFlowPaused';
      "Inflights" ::= #Inflights';
      "IsLearner" ::= #IsLearner'
    ]))%V
    #(Progress.mk Match' Next' sentCommit' State' PendingSnapshot' RecentActive' MsgAppFlowPaused' Inflights' IsLearner').
Admitted.


Global Instance Progress_struct_fields_split dq l (v : Progress.t) :
  StructFieldsSplit dq l v (
    "HMatch" ∷ l ↦s[tracker.Progress :: "Match"]{dq} v.(Progress.Match') ∗
    "HNext" ∷ l ↦s[tracker.Progress :: "Next"]{dq} v.(Progress.Next') ∗
    "HsentCommit" ∷ l ↦s[tracker.Progress :: "sentCommit"]{dq} v.(Progress.sentCommit') ∗
    "HState" ∷ l ↦s[tracker.Progress :: "State"]{dq} v.(Progress.State') ∗
    "HPendingSnapshot" ∷ l ↦s[tracker.Progress :: "PendingSnapshot"]{dq} v.(Progress.PendingSnapshot') ∗
    "HRecentActive" ∷ l ↦s[tracker.Progress :: "RecentActive"]{dq} v.(Progress.RecentActive') ∗
    "HMsgAppFlowPaused" ∷ l ↦s[tracker.Progress :: "MsgAppFlowPaused"]{dq} v.(Progress.MsgAppFlowPaused') ∗
    "HInflights" ∷ l ↦s[tracker.Progress :: "Inflights"]{dq} v.(Progress.Inflights') ∗
    "HIsLearner" ∷ l ↦s[tracker.Progress :: "IsLearner"]{dq} v.(Progress.IsLearner')
  ).
Admitted.

End instances.

Module ProgressMap.
Section def.
Context `{ffi_syntax}.
Definition t := loc.
End def.
End ProgressMap.
Module Config.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Voters' : quorum.JointConfig.t;
  AutoLeave' : bool;
  Learners' : loc;
  LearnersNext' : loc;
}.
End def.
End Config.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_Config `{ffi_syntax}: Settable _ :=
  settable! Config.mk < Config.Voters'; Config.AutoLeave'; Config.Learners'; Config.LearnersNext' >.
Global Instance into_val_Config `{ffi_syntax} : IntoVal Config.t.
Admitted.

Global Instance into_val_typed_Config `{ffi_syntax} : IntoValTyped Config.t tracker.Config :=
{|
  default_val := Config.mk (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_Config_Voters `{ffi_syntax} : IntoValStructField "Voters" tracker.Config Config.Voters'.
Admitted.

Global Instance into_val_struct_field_Config_AutoLeave `{ffi_syntax} : IntoValStructField "AutoLeave" tracker.Config Config.AutoLeave'.
Admitted.

Global Instance into_val_struct_field_Config_Learners `{ffi_syntax} : IntoValStructField "Learners" tracker.Config Config.Learners'.
Admitted.

Global Instance into_val_struct_field_Config_LearnersNext `{ffi_syntax} : IntoValStructField "LearnersNext" tracker.Config Config.LearnersNext'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_Config `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Voters' AutoLeave' Learners' LearnersNext':
  PureWp True
    (struct.make tracker.Config (alist_val [
      "Voters" ::= #Voters';
      "AutoLeave" ::= #AutoLeave';
      "Learners" ::= #Learners';
      "LearnersNext" ::= #LearnersNext'
    ]))%V
    #(Config.mk Voters' AutoLeave' Learners' LearnersNext').
Admitted.


Global Instance Config_struct_fields_split dq l (v : Config.t) :
  StructFieldsSplit dq l v (
    "HVoters" ∷ l ↦s[tracker.Config :: "Voters"]{dq} v.(Config.Voters') ∗
    "HAutoLeave" ∷ l ↦s[tracker.Config :: "AutoLeave"]{dq} v.(Config.AutoLeave') ∗
    "HLearners" ∷ l ↦s[tracker.Config :: "Learners"]{dq} v.(Config.Learners') ∗
    "HLearnersNext" ∷ l ↦s[tracker.Config :: "LearnersNext"]{dq} v.(Config.LearnersNext')
  ).
Admitted.

End instances.
Module ProgressTracker.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  Config' : Config.t;
  Progress' : ProgressMap.t;
  Votes' : loc;
  MaxInflight' : w64;
  MaxInflightBytes' : w64;
}.
End def.
End ProgressTracker.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_ProgressTracker `{ffi_syntax}: Settable _ :=
  settable! ProgressTracker.mk < ProgressTracker.Config'; ProgressTracker.Progress'; ProgressTracker.Votes'; ProgressTracker.MaxInflight'; ProgressTracker.MaxInflightBytes' >.
Global Instance into_val_ProgressTracker `{ffi_syntax} : IntoVal ProgressTracker.t.
Admitted.

Global Instance into_val_typed_ProgressTracker `{ffi_syntax} : IntoValTyped ProgressTracker.t tracker.ProgressTracker :=
{|
  default_val := ProgressTracker.mk (default_val _) (default_val _) (default_val _) (default_val _) (default_val _);
  to_val_has_go_type := ltac:(destruct falso);
  default_val_eq_zero_val := ltac:(destruct falso);
  to_val_inj := ltac:(destruct falso);
  to_val_eqdec := ltac:(solve_decision);
|}.
Global Instance into_val_struct_field_ProgressTracker_Config `{ffi_syntax} : IntoValStructField "Config" tracker.ProgressTracker ProgressTracker.Config'.
Admitted.

Global Instance into_val_struct_field_ProgressTracker_Progress `{ffi_syntax} : IntoValStructField "Progress" tracker.ProgressTracker ProgressTracker.Progress'.
Admitted.

Global Instance into_val_struct_field_ProgressTracker_Votes `{ffi_syntax} : IntoValStructField "Votes" tracker.ProgressTracker ProgressTracker.Votes'.
Admitted.

Global Instance into_val_struct_field_ProgressTracker_MaxInflight `{ffi_syntax} : IntoValStructField "MaxInflight" tracker.ProgressTracker ProgressTracker.MaxInflight'.
Admitted.

Global Instance into_val_struct_field_ProgressTracker_MaxInflightBytes `{ffi_syntax} : IntoValStructField "MaxInflightBytes" tracker.ProgressTracker ProgressTracker.MaxInflightBytes'.
Admitted.


Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.
Global Instance wp_struct_make_ProgressTracker `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} Config' Progress' Votes' MaxInflight' MaxInflightBytes':
  PureWp True
    (struct.make tracker.ProgressTracker (alist_val [
      "Config" ::= #Config';
      "Progress" ::= #Progress';
      "Votes" ::= #Votes';
      "MaxInflight" ::= #MaxInflight';
      "MaxInflightBytes" ::= #MaxInflightBytes'
    ]))%V
    #(ProgressTracker.mk Config' Progress' Votes' MaxInflight' MaxInflightBytes').
Admitted.


Global Instance ProgressTracker_struct_fields_split dq l (v : ProgressTracker.t) :
  StructFieldsSplit dq l v (
    "HConfig" ∷ l ↦s[tracker.ProgressTracker :: "Config"]{dq} v.(ProgressTracker.Config') ∗
    "HProgress" ∷ l ↦s[tracker.ProgressTracker :: "Progress"]{dq} v.(ProgressTracker.Progress') ∗
    "HVotes" ∷ l ↦s[tracker.ProgressTracker :: "Votes"]{dq} v.(ProgressTracker.Votes') ∗
    "HMaxInflight" ∷ l ↦s[tracker.ProgressTracker :: "MaxInflight"]{dq} v.(ProgressTracker.MaxInflight') ∗
    "HMaxInflightBytes" ∷ l ↦s[tracker.ProgressTracker :: "MaxInflightBytes"]{dq} v.(ProgressTracker.MaxInflightBytes')
  ).
Admitted.

End instances.

Module matchAckIndexer.
Section def.
Context `{ffi_syntax}.
Definition t := loc.
End def.
End matchAckIndexer.

Section names.

Class GlobalAddrs :=
{
  prstmap : loc;
}.

Context `{!GlobalAddrs}.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!goGlobalsGS Σ}.

Definition var_addrs : list (go_string * loc) := [
    ("prstmap"%go, prstmap)
  ].

Definition is_defined := is_global_definitions tracker.pkg_name' var_addrs tracker.functions' tracker.msets'.

Definition own_allocated `{!GlobalAddrs} : iProp Σ :=
  "Hprstmap" ∷ prstmap ↦ (default_val (vec go_string 3)).

Global Instance wp_globals_get_prstmap : 
  WpGlobalsGet tracker.pkg_name' "prstmap" prstmap is_defined.
Proof. apply wp_globals_get'. reflexivity. Qed.

Global Instance wp_func_call_NewInflights :
  WpFuncCall tracker.pkg_name' "NewInflights" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_func_call_MakeProgressTracker :
  WpFuncCall tracker.pkg_name' "MakeProgressTracker" _ is_defined :=
  ltac:(apply wp_func_call'; reflexivity).

Global Instance wp_method_call_Inflights'ptr_Add :
  WpMethodCall tracker.pkg_name' "Inflights'ptr" "Add" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Inflights'ptr_Clone :
  WpMethodCall tracker.pkg_name' "Inflights'ptr" "Clone" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Inflights'ptr_Count :
  WpMethodCall tracker.pkg_name' "Inflights'ptr" "Count" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Inflights'ptr_FreeLE :
  WpMethodCall tracker.pkg_name' "Inflights'ptr" "FreeLE" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Inflights'ptr_Full :
  WpMethodCall tracker.pkg_name' "Inflights'ptr" "Full" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Inflights'ptr_grow :
  WpMethodCall tracker.pkg_name' "Inflights'ptr" "grow" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Inflights'ptr_reset :
  WpMethodCall tracker.pkg_name' "Inflights'ptr" "reset" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Progress'ptr_BecomeProbe :
  WpMethodCall tracker.pkg_name' "Progress'ptr" "BecomeProbe" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Progress'ptr_BecomeReplicate :
  WpMethodCall tracker.pkg_name' "Progress'ptr" "BecomeReplicate" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Progress'ptr_BecomeSnapshot :
  WpMethodCall tracker.pkg_name' "Progress'ptr" "BecomeSnapshot" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Progress'ptr_CanBumpCommit :
  WpMethodCall tracker.pkg_name' "Progress'ptr" "CanBumpCommit" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Progress'ptr_IsPaused :
  WpMethodCall tracker.pkg_name' "Progress'ptr" "IsPaused" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Progress'ptr_MaybeDecrTo :
  WpMethodCall tracker.pkg_name' "Progress'ptr" "MaybeDecrTo" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Progress'ptr_MaybeUpdate :
  WpMethodCall tracker.pkg_name' "Progress'ptr" "MaybeUpdate" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Progress'ptr_ResetState :
  WpMethodCall tracker.pkg_name' "Progress'ptr" "ResetState" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Progress'ptr_SentCommit :
  WpMethodCall tracker.pkg_name' "Progress'ptr" "SentCommit" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Progress'ptr_SentEntries :
  WpMethodCall tracker.pkg_name' "Progress'ptr" "SentEntries" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Progress'ptr_String :
  WpMethodCall tracker.pkg_name' "Progress'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ProgressMap_String :
  WpMethodCall tracker.pkg_name' "ProgressMap" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ProgressMap'ptr_String :
  WpMethodCall tracker.pkg_name' "ProgressMap'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_StateType_String :
  WpMethodCall tracker.pkg_name' "StateType" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_StateType'ptr_String :
  WpMethodCall tracker.pkg_name' "StateType'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Config_String :
  WpMethodCall tracker.pkg_name' "Config" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Config'ptr_Clone :
  WpMethodCall tracker.pkg_name' "Config'ptr" "Clone" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_Config'ptr_String :
  WpMethodCall tracker.pkg_name' "Config'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ProgressTracker_String :
  WpMethodCall tracker.pkg_name' "ProgressTracker" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ProgressTracker'ptr_Clone :
  WpMethodCall tracker.pkg_name' "ProgressTracker'ptr" "Clone" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ProgressTracker'ptr_Committed :
  WpMethodCall tracker.pkg_name' "ProgressTracker'ptr" "Committed" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ProgressTracker'ptr_ConfState :
  WpMethodCall tracker.pkg_name' "ProgressTracker'ptr" "ConfState" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ProgressTracker'ptr_IsSingleton :
  WpMethodCall tracker.pkg_name' "ProgressTracker'ptr" "IsSingleton" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ProgressTracker'ptr_LearnerNodes :
  WpMethodCall tracker.pkg_name' "ProgressTracker'ptr" "LearnerNodes" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ProgressTracker'ptr_QuorumActive :
  WpMethodCall tracker.pkg_name' "ProgressTracker'ptr" "QuorumActive" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ProgressTracker'ptr_RecordVote :
  WpMethodCall tracker.pkg_name' "ProgressTracker'ptr" "RecordVote" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ProgressTracker'ptr_ResetVotes :
  WpMethodCall tracker.pkg_name' "ProgressTracker'ptr" "ResetVotes" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ProgressTracker'ptr_String :
  WpMethodCall tracker.pkg_name' "ProgressTracker'ptr" "String" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ProgressTracker'ptr_TallyVotes :
  WpMethodCall tracker.pkg_name' "ProgressTracker'ptr" "TallyVotes" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ProgressTracker'ptr_Visit :
  WpMethodCall tracker.pkg_name' "ProgressTracker'ptr" "Visit" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_ProgressTracker'ptr_VoterNodes :
  WpMethodCall tracker.pkg_name' "ProgressTracker'ptr" "VoterNodes" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_matchAckIndexer_AckedIndex :
  WpMethodCall tracker.pkg_name' "matchAckIndexer" "AckedIndex" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

Global Instance wp_method_call_matchAckIndexer'ptr_AckedIndex :
  WpMethodCall tracker.pkg_name' "matchAckIndexer'ptr" "AckedIndex" _ is_defined :=
  ltac:(apply wp_method_call'; reflexivity).

End names.
End tracker.
