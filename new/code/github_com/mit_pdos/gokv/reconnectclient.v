(* autogenerated from github.com/mit-pdos/gokv/reconnectclient *)
From New.golang Require Import defn.
From New.code Require github_com.goose_lang.goose.machine.
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

Definition MakeReconnectingClient : val :=
  rec: "MakeReconnectingClient" "addr" :=
    exception_do (let: "addr" := ref_ty uint64T "addr" in
    let: "r" := ref_ty ptrT (zero_val ptrT) in
    let: "$a0" := ref_ty ReconnectingClient (zero_val ReconnectingClient) in
    do:  "r" <-[ptrT] "$a0";;;
    let: "$a0" := ref_ty sync.Mutex (zero_val sync.Mutex) in
    do:  (struct.field_ref ReconnectingClient "mu" (![ptrT] "r")) <-[ptrT] "$a0";;;
    let: "$a0" := #false in
    do:  (struct.field_ref ReconnectingClient "valid" (![ptrT] "r")) <-[boolT] "$a0";;;
    let: "$a0" := ![uint64T] "addr" in
    do:  (struct.field_ref ReconnectingClient "addr" (![ptrT] "r")) <-[uint64T] "$a0";;;
    return: (![ptrT] "r");;;
    do:  #()).

Definition ReconnectingClient__getClient : val :=
  rec: "ReconnectingClient__getClient" "cl" <> :=
    exception_do (let: "cl" := ref_ty ptrT "cl" in
    do:  (sync.Mutex__Lock (![ptrT] (struct.field_ref ReconnectingClient "mu" (![ptrT] "cl")))) #();;;
    (if: ![boolT] (struct.field_ref ReconnectingClient "valid" (![ptrT] "cl"))
    then
      let: "ret" := ref_ty ptrT (zero_val ptrT) in
      let: "$a0" := ![ptrT] (struct.field_ref ReconnectingClient "urpcCl" (![ptrT] "cl")) in
      do:  "ret" <-[ptrT] "$a0";;;
      do:  (sync.Mutex__Unlock (![ptrT] (struct.field_ref ReconnectingClient "mu" (![ptrT] "cl")))) #();;;
      return: (#0, ![ptrT] "ret");;;
      do:  #()
    else do:  #());;;
    do:  (sync.Mutex__Unlock (![ptrT] (struct.field_ref ReconnectingClient "mu" (![ptrT] "cl")))) #();;;
    let: "newRpcCl" := ref_ty ptrT (zero_val ptrT) in
    let: "err" := ref_ty uint64T (zero_val uint64T) in
    let: ("$a0", "$a1") := urpc.TryMakeClient (![uint64T] (struct.field_ref ReconnectingClient "addr" (![ptrT] "cl"))) in
    do:  "newRpcCl" <-[ptrT] "$a1";;;
    do:  "err" <-[uint64T] "$a0";;;
    (if: (![uint64T] "err") ≠ #0
    then
      do:  machine.Sleep #10000000;;;
      do:  #()
    else do:  #());;;
    do:  (sync.Mutex__Lock (![ptrT] (struct.field_ref ReconnectingClient "mu" (![ptrT] "cl")))) #();;;
    (if: (![uint64T] "err") = #0
    then
      let: "$a0" := ![ptrT] "newRpcCl" in
      do:  (struct.field_ref ReconnectingClient "urpcCl" (![ptrT] "cl")) <-[ptrT] "$a0";;;
      let: "$a0" := #true in
      do:  (struct.field_ref ReconnectingClient "valid" (![ptrT] "cl")) <-[boolT] "$a0";;;
      do:  #()
    else do:  #());;;
    do:  (sync.Mutex__Unlock (![ptrT] (struct.field_ref ReconnectingClient "mu" (![ptrT] "cl")))) #();;;
    return: (![uint64T] "err", ![ptrT] "newRpcCl");;;
    do:  #()).

Definition ReconnectingClient__Call : val :=
  rec: "ReconnectingClient__Call" "cl" "rpcid" "args" "reply" "timeout_ms" :=
    exception_do (let: "cl" := ref_ty ptrT "cl" in
    let: "timeout_ms" := ref_ty uint64T "timeout_ms" in
    let: "reply" := ref_ty ptrT "reply" in
    let: "args" := ref_ty (sliceT byteT) "args" in
    let: "rpcid" := ref_ty uint64T "rpcid" in
    let: "urpcCl" := ref_ty ptrT (zero_val ptrT) in
    let: "err1" := ref_ty uint64T (zero_val uint64T) in
    let: ("$a0", "$a1") := (ReconnectingClient__getClient (![ptrT] "cl")) #() in
    do:  "urpcCl" <-[ptrT] "$a1";;;
    do:  "err1" <-[uint64T] "$a0";;;
    (if: (![uint64T] "err1") ≠ #0
    then
      return: (![uint64T] "err1");;;
      do:  #()
    else do:  #());;;
    let: "err" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := (urpc.Client__Call (![ptrT] "urpcCl")) (![uint64T] "rpcid") (![sliceT byteT] "args") (![ptrT] "reply") (![uint64T] "timeout_ms") in
    do:  "err" <-[uint64T] "$a0";;;
    (if: (![uint64T] "err") = urpc.ErrDisconnect
    then
      do:  (sync.Mutex__Lock (![ptrT] (struct.field_ref ReconnectingClient "mu" (![ptrT] "cl")))) #();;;
      let: "$a0" := #false in
      do:  (struct.field_ref ReconnectingClient "valid" (![ptrT] "cl")) <-[boolT] "$a0";;;
      do:  (sync.Mutex__Unlock (![ptrT] (struct.field_ref ReconnectingClient "mu" (![ptrT] "cl")))) #();;;
      do:  #()
    else do:  #());;;
    return: (![uint64T] "err");;;
    do:  #()).
