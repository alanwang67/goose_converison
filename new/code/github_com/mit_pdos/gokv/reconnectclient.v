(* autogenerated from github.com/mit-pdos/gokv/reconnectclient *)
From New.golang Require Import defn.
From New.code Require github_com.goose_lang.primitive.
From New.code Require github_com.mit_pdos.gokv.grove_ffi.
From New.code Require github_com.mit_pdos.gokv.urpc.
From New.code Require sync.

From New Require Import grove_prelude.

Definition ReconnectingClient : go_type := structT [
  "mu" :: ptrT;
  "valid" :: boolT;
  "urpcCl" :: ptrT;
  "addr" :: uint64T
].

Definition ReconnectingClient__mset : list (string * val) := [
].

(* go: client.go:30:31 *)
Definition ReconnectingClient__getClient : val :=
  rec: "ReconnectingClient__getClient" "cl" <> :=
    exception_do (let: "cl" := (ref_ty ptrT "cl") in
    do:  ((sync.Mutex__Lock (![ptrT] (struct.field_ref ReconnectingClient "mu" (![ptrT] "cl")))) #());;;
    (if: ![boolT] (struct.field_ref ReconnectingClient "valid" (![ptrT] "cl"))
    then
      let: "ret" := (ref_ty ptrT (zero_val ptrT)) in
      let: "$r0" := (![ptrT] (struct.field_ref ReconnectingClient "urpcCl" (![ptrT] "cl"))) in
      do:  ("ret" <-[ptrT] "$r0");;;
      do:  ((sync.Mutex__Unlock (![ptrT] (struct.field_ref ReconnectingClient "mu" (![ptrT] "cl")))) #());;;
      return: (#(W64 0), ![ptrT] "ret")
    else do:  #());;;
    do:  ((sync.Mutex__Unlock (![ptrT] (struct.field_ref ReconnectingClient "mu" (![ptrT] "cl")))) #());;;
    let: "newRpcCl" := (ref_ty ptrT (zero_val ptrT)) in
    let: "err" := (ref_ty uint64T (zero_val uint64T)) in
    let: ("$ret0", "$ret1") := (let: "$a0" := (![uint64T] (struct.field_ref ReconnectingClient "addr" (![ptrT] "cl"))) in
    urpc.TryMakeClient "$a0") in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("err" <-[uint64T] "$r0");;;
    do:  ("newRpcCl" <-[ptrT] "$r1");;;
    (if: (![uint64T] "err") ≠ #(W64 0)
    then
      do:  (let: "$a0" := #(W64 10000000) in
      primitive.Sleep "$a0")
    else do:  #());;;
    do:  ((sync.Mutex__Lock (![ptrT] (struct.field_ref ReconnectingClient "mu" (![ptrT] "cl")))) #());;;
    (if: (![uint64T] "err") = #(W64 0)
    then
      let: "$r0" := (![ptrT] "newRpcCl") in
      do:  ((struct.field_ref ReconnectingClient "urpcCl" (![ptrT] "cl")) <-[ptrT] "$r0");;;
      let: "$r0" := #true in
      do:  ((struct.field_ref ReconnectingClient "valid" (![ptrT] "cl")) <-[boolT] "$r0")
    else do:  #());;;
    do:  ((sync.Mutex__Unlock (![ptrT] (struct.field_ref ReconnectingClient "mu" (![ptrT] "cl")))) #());;;
    return: (![uint64T] "err", ![ptrT] "newRpcCl")).

(* go: client.go:63:31 *)
Definition ReconnectingClient__Call : val :=
  rec: "ReconnectingClient__Call" "cl" "rpcid" "args" "reply" "timeout_ms" :=
    exception_do (let: "cl" := (ref_ty ptrT "cl") in
    let: "timeout_ms" := (ref_ty uint64T "timeout_ms") in
    let: "reply" := (ref_ty ptrT "reply") in
    let: "args" := (ref_ty sliceT "args") in
    let: "rpcid" := (ref_ty uint64T "rpcid") in
    let: "urpcCl" := (ref_ty ptrT (zero_val ptrT)) in
    let: "err1" := (ref_ty uint64T (zero_val uint64T)) in
    let: ("$ret0", "$ret1") := ((ReconnectingClient__getClient (![ptrT] "cl")) #()) in
    let: "$r0" := "$ret0" in
    let: "$r1" := "$ret1" in
    do:  ("err1" <-[uint64T] "$r0");;;
    do:  ("urpcCl" <-[ptrT] "$r1");;;
    (if: (![uint64T] "err1") ≠ #(W64 0)
    then return: (![uint64T] "err1")
    else do:  #());;;
    let: "err" := (ref_ty uint64T (zero_val uint64T)) in
    let: "$r0" := (let: "$a0" := (![uint64T] "rpcid") in
    let: "$a1" := (![sliceT] "args") in
    let: "$a2" := (![ptrT] "reply") in
    let: "$a3" := (![uint64T] "timeout_ms") in
    (urpc.Client__Call (![ptrT] "urpcCl")) "$a0" "$a1" "$a2" "$a3") in
    do:  ("err" <-[uint64T] "$r0");;;
    (if: (![uint64T] "err") = urpc.ErrDisconnect
    then
      do:  ((sync.Mutex__Lock (![ptrT] (struct.field_ref ReconnectingClient "mu" (![ptrT] "cl")))) #());;;
      let: "$r0" := #false in
      do:  ((struct.field_ref ReconnectingClient "valid" (![ptrT] "cl")) <-[boolT] "$r0");;;
      do:  ((sync.Mutex__Unlock (![ptrT] (struct.field_ref ReconnectingClient "mu" (![ptrT] "cl")))) #())
    else do:  #());;;
    return: (![uint64T] "err")).

Definition ReconnectingClient__mset_ptr : list (string * val) := [
  ("Call", ReconnectingClient__Call%V);
  ("getClient", ReconnectingClient__getClient%V)
].

(* go: client.go:20:6 *)
Definition MakeReconnectingClient : val :=
  rec: "MakeReconnectingClient" "addr" :=
    exception_do (let: "addr" := (ref_ty uint64T "addr") in
    let: "r" := (ref_ty ptrT (zero_val ptrT)) in
    let: "$r0" := (ref_ty ReconnectingClient (zero_val ReconnectingClient)) in
    do:  ("r" <-[ptrT] "$r0");;;
    let: "$r0" := (ref_ty sync.Mutex (zero_val sync.Mutex)) in
    do:  ((struct.field_ref ReconnectingClient "mu" (![ptrT] "r")) <-[ptrT] "$r0");;;
    let: "$r0" := #false in
    do:  ((struct.field_ref ReconnectingClient "valid" (![ptrT] "r")) <-[boolT] "$r0");;;
    let: "$r0" := (![uint64T] "addr") in
    do:  ((struct.field_ref ReconnectingClient "addr" (![ptrT] "r")) <-[uint64T] "$r0");;;
    return: (![ptrT] "r")).

Definition pkg_name' : string := "github.com/mit-pdos/gokv/reconnectclient".

Definition define' : val :=
  rec: "define'" <> :=
    exception_do (do:  #()).

Definition initialize' : val :=
  rec: "initialize'" <> :=
    globals.package_init pkg_name' (λ: <>,
      exception_do (do:  urpc.initialize';;;
      do:  grove_ffi.initialize';;;
      do:  primitive.initialize';;;
      do:  sync.initialize';;;
      do:  (define' #()))
      ).
