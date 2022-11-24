(* autogenerated from github.com/mit-pdos/gokv/fencing/ctr *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.gokv.erpc.
From Goose Require github_com.mit_pdos.gokv.urpc.
From Goose Require github_com.tchajed.marshal.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* 0_marshal.go *)

Definition ENone : expr := #0.

Definition EStale : expr := #1.

Definition PutArgs := struct.decl [
  "epoch" :: uint64T;
  "v" :: uint64T
].

Definition EncPutArgs: val :=
  rec: "EncPutArgs" "args" :=
    let: "enc" := marshal.NewEnc #16 in
    marshal.Enc__PutInt "enc" (struct.loadF PutArgs "v" "args");;
    marshal.Enc__PutInt "enc" (struct.loadF PutArgs "epoch" "args");;
    marshal.Enc__Finish "enc".

Definition DecPutArgs: val :=
  rec: "DecPutArgs" "raw_args" :=
    let: "dec" := marshal.NewDec "raw_args" in
    let: "args" := struct.alloc PutArgs (zero_val (struct.t PutArgs)) in
    struct.storeF PutArgs "v" "args" (marshal.Dec__GetInt "dec");;
    struct.storeF PutArgs "epoch" "args" (marshal.Dec__GetInt "dec");;
    "args".

Definition GetArgs := struct.decl [
  "epoch" :: uint64T
].

Definition EncGetArgs: val :=
  rec: "EncGetArgs" "args" :=
    let: "enc" := marshal.NewEnc #8 in
    marshal.Enc__PutInt "enc" (struct.loadF GetArgs "epoch" "args");;
    marshal.Enc__Finish "enc".

Definition DecGetArgs: val :=
  rec: "DecGetArgs" "raw_args" :=
    let: "dec" := marshal.NewDec "raw_args" in
    let: "args" := struct.alloc GetArgs (zero_val (struct.t GetArgs)) in
    struct.storeF GetArgs "epoch" "args" (marshal.Dec__GetInt "dec");;
    "args".

Definition GetReply := struct.decl [
  "err" :: uint64T;
  "val" :: uint64T
].

Definition EncGetReply: val :=
  rec: "EncGetReply" "reply" :=
    let: "enc" := marshal.NewEnc #16 in
    marshal.Enc__PutInt "enc" (struct.loadF GetReply "err" "reply");;
    marshal.Enc__PutInt "enc" (struct.loadF GetReply "val" "reply");;
    marshal.Enc__Finish "enc".

Definition DecGetReply: val :=
  rec: "DecGetReply" "raw_reply" :=
    let: "dec" := marshal.NewDec "raw_reply" in
    let: "reply" := struct.alloc GetReply (zero_val (struct.t GetReply)) in
    struct.storeF GetReply "err" "reply" (marshal.Dec__GetInt "dec");;
    struct.storeF GetReply "val" "reply" (marshal.Dec__GetInt "dec");;
    "reply".

(* client.go *)

Definition RPC_GET : expr := #0.

Definition RPC_PUT : expr := #1.

Definition RPC_FRESHCID : expr := #2.

Definition Clerk := struct.decl [
  "cl" :: ptrT;
  "e" :: ptrT
].

Definition Clerk__Get: val :=
  rec: "Clerk__Get" "c" "epoch" :=
    let: "enc" := marshal.NewEnc #8 in
    marshal.Enc__PutInt "enc" "epoch";;
    let: "req" := marshal.Enc__Finish "enc" in
    let: "valProph" := NewProph #() in
    let: "reply_ptr" := ref (zero_val (slice.T byteT)) in
    let: "err" := urpc.Client__Call (struct.loadF Clerk "cl" "c") RPC_GET "req" "reply_ptr" #100 in
    (if: "err" ≠ #0
    then
      (* log.Println("ctr: urpc get call failed/timed out") *)
      grove_ffi.Exit #1
    else #());;
    let: "r" := DecGetReply (![slice.T byteT] "reply_ptr") in
    (if: (struct.loadF GetReply "err" "r") ≠ ENone
    then
      (* log.Println("ctr: get() stale epoch number") *)
      grove_ffi.Exit #1
    else #());;
    ResolveProph "valProph" (struct.loadF GetReply "val" "r");;
    struct.loadF GetReply "val" "r".

Definition Clerk__Put: val :=
  rec: "Clerk__Put" "c" "v" "epoch" :=
    let: "args" := struct.new PutArgs [
      "v" ::= "v";
      "epoch" ::= "epoch"
    ] in
    let: "req" := erpc.Client__NewRequest (struct.loadF Clerk "e" "c") (EncPutArgs "args") in
    let: "reply_ptr" := ref (zero_val (slice.T byteT)) in
    let: "err" := urpc.Client__Call (struct.loadF Clerk "cl" "c") RPC_PUT "req" "reply_ptr" #100 in
    (if: "err" ≠ #0
    then
      (* log.Println("ctr: urpc put call failed/timed out") *)
      grove_ffi.Exit #1
    else #());;
    let: "dec" := marshal.NewDec (![slice.T byteT] "reply_ptr") in
    let: "epochErr" := marshal.Dec__GetInt "dec" in
    (if: "epochErr" ≠ ENone
    then
      (* log.Println("ctr: get() stale epoch number") *)
      grove_ffi.Exit #1
    else #());;
    #().

Definition MakeClerk: val :=
  rec: "MakeClerk" "host" :=
    let: "ck" := struct.alloc Clerk (zero_val (struct.t Clerk)) in
    struct.storeF Clerk "cl" "ck" (urpc.MakeClient "host");;
    let: "reply_ptr" := ref (zero_val (slice.T byteT)) in
    let: "err" := urpc.Client__Call (struct.loadF Clerk "cl" "ck") RPC_FRESHCID (NewSlice byteT #0) "reply_ptr" #100 in
    (if: "err" ≠ #0
    then
      (* log.Println("ctr: urpc getcid call failed/timed out") *)
      grove_ffi.Exit #1
    else #());;
    struct.storeF Clerk "e" "ck" (erpc.MakeClient (marshal.Dec__GetInt (marshal.NewDec (![slice.T byteT] "reply_ptr"))));;
    "ck".

(* server.go *)

Definition Server := struct.decl [
  "mu" :: ptrT;
  "e" :: ptrT;
  "v" :: uint64T;
  "lastEpoch" :: uint64T
].

Definition Server__Put: val :=
  rec: "Server__Put" "s" "args" :=
    lock.acquire (struct.loadF Server "mu" "s");;
    (if: (struct.loadF PutArgs "epoch" "args") < (struct.loadF Server "lastEpoch" "s")
    then
      lock.release (struct.loadF Server "mu" "s");;
      EStale
    else
      struct.storeF Server "lastEpoch" "s" (struct.loadF PutArgs "epoch" "args");;
      struct.storeF Server "v" "s" (struct.loadF PutArgs "v" "args");;
      lock.release (struct.loadF Server "mu" "s");;
      ENone).

Definition Server__Get: val :=
  rec: "Server__Get" "s" "epoch" "reply" :=
    lock.acquire (struct.loadF Server "mu" "s");;
    struct.storeF GetReply "err" "reply" ENone;;
    (if: "epoch" < (struct.loadF Server "lastEpoch" "s")
    then
      lock.release (struct.loadF Server "mu" "s");;
      struct.storeF GetReply "err" "reply" EStale;;
      #()
    else
      struct.storeF Server "lastEpoch" "s" "epoch";;
      struct.storeF GetReply "val" "reply" (struct.loadF Server "v" "s");;
      Linearize;;
      lock.release (struct.loadF Server "mu" "s");;
      #()).

Definition StartServer: val :=
  rec: "StartServer" "me" :=
    let: "s" := struct.alloc Server (zero_val (struct.t Server)) in
    struct.storeF Server "mu" "s" (lock.new #());;
    struct.storeF Server "e" "s" (erpc.MakeServer #());;
    struct.storeF Server "v" "s" #0;;
    let: "handlers" := NewMap ((slice.T byteT -> ptrT -> unitT)%ht) #() in
    MapInsert "handlers" RPC_GET ((λ: "raw_args" "raw_reply",
      let: "dec" := marshal.NewDec "raw_args" in
      let: "epoch" := marshal.Dec__GetInt "dec" in
      let: "reply" := struct.alloc GetReply (zero_val (struct.t GetReply)) in
      Server__Get "s" "epoch" "reply";;
      "raw_reply" <-[slice.T byteT] EncGetReply "reply";;
      #()
      ));;
    MapInsert "handlers" RPC_PUT (erpc.Server__HandleRequest (struct.loadF Server "e" "s") ((λ: "raw_args" "reply",
      let: "args" := DecPutArgs "raw_args" in
      let: "err" := Server__Put "s" "args" in
      let: "enc" := marshal.NewEnc #8 in
      marshal.Enc__PutInt "enc" "err";;
      "reply" <-[slice.T byteT] marshal.Enc__Finish "enc";;
      #()
      )));;
    MapInsert "handlers" RPC_FRESHCID ((λ: "raw_args" "reply",
      let: "enc" := marshal.NewEnc #8 in
      marshal.Enc__PutInt "enc" (erpc.Server__GetFreshCID (struct.loadF Server "e" "s"));;
      "reply" <-[slice.T byteT] marshal.Enc__Finish "enc";;
      #()
      ));;
    let: "r" := urpc.MakeServer "handlers" in
    urpc.Server__Serve "r" "me";;
    #().
