(* autogenerated from github.com/mit-pdos/gokv/fencing/ctr *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.mit_dash_pdos.gokv.erpc.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require github_dot_com.mit_dash_pdos.gokv.urpc.
From Goose Require github_dot_com.tchajed.goose.machine.
From Goose Require github_dot_com.tchajed.marshal.
From Goose Require log.
From Goose Require sync.

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
    let: "args" := ref_to ptrT "args" in
    let: "enc" := ref_zero (struct.t marshal.Enc) in
    let: "$a0" := marshal.NewEnc #16 in
    do:  "enc" <-[struct.t marshal.Enc] "$a0";;;
    do:  marshal.Enc__PutInt (![struct.t marshal.Enc] "enc") (struct.loadF PutArgs "v" (![ptrT] "args"));;;
    do:  marshal.Enc__PutInt (![struct.t marshal.Enc] "enc") (struct.loadF PutArgs "epoch" (![ptrT] "args"));;;
    return: (marshal.Enc__Finish (![struct.t marshal.Enc] "enc"));;;
    do:  #().

Definition DecPutArgs: val :=
  rec: "DecPutArgs" "raw_args" :=
    let: "raw_args" := ref_to (slice.T byteT) "raw_args" in
    let: "dec" := ref_zero (struct.t marshal.Dec) in
    let: "$a0" := marshal.NewDec (![slice.T byteT] "raw_args") in
    do:  "dec" <-[struct.t marshal.Dec] "$a0";;;
    let: "args" := ref_zero ptrT in
    let: "$a0" := struct.alloc PutArgs (zero_val (struct.t PutArgs)) in
    do:  "args" <-[ptrT] "$a0";;;
    let: "$a0" := marshal.Dec__GetInt (![struct.t marshal.Dec] "dec") in
    do:  struct.storeF PutArgs "v" (![ptrT] "args") "$a0";;;
    let: "$a0" := marshal.Dec__GetInt (![struct.t marshal.Dec] "dec") in
    do:  struct.storeF PutArgs "epoch" (![ptrT] "args") "$a0";;;
    return: (![ptrT] "args");;;
    do:  #().

Definition GetArgs := struct.decl [
  "epoch" :: uint64T
].

Definition EncGetArgs: val :=
  rec: "EncGetArgs" "args" :=
    let: "args" := ref_to ptrT "args" in
    let: "enc" := ref_zero (struct.t marshal.Enc) in
    let: "$a0" := marshal.NewEnc #8 in
    do:  "enc" <-[struct.t marshal.Enc] "$a0";;;
    do:  marshal.Enc__PutInt (![struct.t marshal.Enc] "enc") (struct.loadF GetArgs "epoch" (![ptrT] "args"));;;
    return: (marshal.Enc__Finish (![struct.t marshal.Enc] "enc"));;;
    do:  #().

Definition DecGetArgs: val :=
  rec: "DecGetArgs" "raw_args" :=
    let: "raw_args" := ref_to (slice.T byteT) "raw_args" in
    let: "dec" := ref_zero (struct.t marshal.Dec) in
    let: "$a0" := marshal.NewDec (![slice.T byteT] "raw_args") in
    do:  "dec" <-[struct.t marshal.Dec] "$a0";;;
    let: "args" := ref_zero ptrT in
    let: "$a0" := struct.alloc GetArgs (zero_val (struct.t GetArgs)) in
    do:  "args" <-[ptrT] "$a0";;;
    let: "$a0" := marshal.Dec__GetInt (![struct.t marshal.Dec] "dec") in
    do:  struct.storeF GetArgs "epoch" (![ptrT] "args") "$a0";;;
    return: (![ptrT] "args");;;
    do:  #().

Definition GetReply := struct.decl [
  "err" :: uint64T;
  "val" :: uint64T
].

Definition EncGetReply: val :=
  rec: "EncGetReply" "reply" :=
    let: "reply" := ref_to ptrT "reply" in
    let: "enc" := ref_zero (struct.t marshal.Enc) in
    let: "$a0" := marshal.NewEnc #16 in
    do:  "enc" <-[struct.t marshal.Enc] "$a0";;;
    do:  marshal.Enc__PutInt (![struct.t marshal.Enc] "enc") (struct.loadF GetReply "err" (![ptrT] "reply"));;;
    do:  marshal.Enc__PutInt (![struct.t marshal.Enc] "enc") (struct.loadF GetReply "val" (![ptrT] "reply"));;;
    return: (marshal.Enc__Finish (![struct.t marshal.Enc] "enc"));;;
    do:  #().

Definition DecGetReply: val :=
  rec: "DecGetReply" "raw_reply" :=
    let: "raw_reply" := ref_to (slice.T byteT) "raw_reply" in
    let: "dec" := ref_zero (struct.t marshal.Dec) in
    let: "$a0" := marshal.NewDec (![slice.T byteT] "raw_reply") in
    do:  "dec" <-[struct.t marshal.Dec] "$a0";;;
    let: "reply" := ref_zero ptrT in
    let: "$a0" := struct.alloc GetReply (zero_val (struct.t GetReply)) in
    do:  "reply" <-[ptrT] "$a0";;;
    let: "$a0" := marshal.Dec__GetInt (![struct.t marshal.Dec] "dec") in
    do:  struct.storeF GetReply "err" (![ptrT] "reply") "$a0";;;
    let: "$a0" := marshal.Dec__GetInt (![struct.t marshal.Dec] "dec") in
    do:  struct.storeF GetReply "val" (![ptrT] "reply") "$a0";;;
    return: (![ptrT] "reply");;;
    do:  #().

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
    let: "epoch" := ref_to uint64T "epoch" in
    let: "c" := ref_to ptrT "c" in
    let: "enc" := ref_zero (struct.t marshal.Enc) in
    let: "$a0" := marshal.NewEnc #8 in
    do:  "enc" <-[struct.t marshal.Enc] "$a0";;;
    do:  marshal.Enc__PutInt (![struct.t marshal.Enc] "enc") (![uint64T] "epoch");;;
    let: "req" := ref_zero (slice.T byteT) in
    let: "$a0" := marshal.Enc__Finish (![struct.t marshal.Enc] "enc") in
    do:  "req" <-[slice.T byteT] "$a0";;;
    let: "valProph" := ref_zero ProphIdT in
    let: "$a0" := machine.NewProph #() in
    do:  "valProph" <-[ProphIdT] "$a0";;;
    let: "reply_ptr" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    do:  "reply_ptr" <-[ptrT] "$a0";;;
    let: "err" := ref_zero uint64T in
    let: "$a0" := urpc.Client__Call (struct.loadF Clerk "cl" (![ptrT] "c")) RPC_GET (![slice.T byteT] "req") (![ptrT] "reply_ptr") #100 in
    do:  "err" <-[uint64T] "$a0";;;
    (if: (![uint64T] "err") ≠ #0
    then
      do:  log.Println #(str "ctr: urpc get call failed/timed out");;;
      do:  machine.Exit #1;;;
      do:  #()
    else #());;;
    let: "r" := ref_zero ptrT in
    let: "$a0" := DecGetReply (![slice.T byteT] (![ptrT] "reply_ptr")) in
    do:  "r" <-[ptrT] "$a0";;;
    (if: (struct.loadF GetReply "err" (![ptrT] "r")) ≠ ENone
    then
      do:  log.Println #(str "ctr: get() stale epoch number");;;
      do:  machine.Exit #1;;;
      do:  #()
    else #());;;
    do:  machine.prophId__ResolveU64 (![ProphIdT] "valProph") (struct.loadF GetReply "val" (![ptrT] "r"));;;
    return: (struct.loadF GetReply "val" (![ptrT] "r"));;;
    do:  #().

Definition Clerk__Put: val :=
  rec: "Clerk__Put" "c" "v" "epoch" :=
    let: "epoch" := ref_to uint64T "epoch" in
    let: "v" := ref_to uint64T "v" in
    let: "c" := ref_to ptrT "c" in
    let: "args" := ref_zero ptrT in
    let: "$a0" := struct.new PutArgs [
      "v" ::= ![uint64T] "v";
      "epoch" ::= ![uint64T] "epoch"
    ] in
    do:  "args" <-[ptrT] "$a0";;;
    let: "req" := ref_zero (slice.T byteT) in
    let: "$a0" := erpc.Client__NewRequest (struct.loadF Clerk "e" (![ptrT] "c")) (EncPutArgs (![ptrT] "args")) in
    do:  "req" <-[slice.T byteT] "$a0";;;
    let: "reply_ptr" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    do:  "reply_ptr" <-[ptrT] "$a0";;;
    let: "err" := ref_zero uint64T in
    let: "$a0" := urpc.Client__Call (struct.loadF Clerk "cl" (![ptrT] "c")) RPC_PUT (![slice.T byteT] "req") (![ptrT] "reply_ptr") #100 in
    do:  "err" <-[uint64T] "$a0";;;
    (if: (![uint64T] "err") ≠ #0
    then
      do:  log.Println #(str "ctr: urpc put call failed/timed out");;;
      do:  machine.Exit #1;;;
      do:  #()
    else #());;;
    let: "dec" := ref_zero (struct.t marshal.Dec) in
    let: "$a0" := marshal.NewDec (![slice.T byteT] (![ptrT] "reply_ptr")) in
    do:  "dec" <-[struct.t marshal.Dec] "$a0";;;
    let: "epochErr" := ref_zero uint64T in
    let: "$a0" := marshal.Dec__GetInt (![struct.t marshal.Dec] "dec") in
    do:  "epochErr" <-[uint64T] "$a0";;;
    (if: (![uint64T] "epochErr") ≠ ENone
    then
      do:  log.Println #(str "ctr: get() stale epoch number");;;
      do:  machine.Exit #1;;;
      do:  #()
    else #());;;
    return: (#());;;
    do:  #().

Definition MakeClerk: val :=
  rec: "MakeClerk" "host" :=
    let: "host" := ref_to uint64T "host" in
    let: "ck" := ref_zero ptrT in
    let: "$a0" := struct.alloc Clerk (zero_val (struct.t Clerk)) in
    do:  "ck" <-[ptrT] "$a0";;;
    let: "$a0" := urpc.MakeClient (![uint64T] "host") in
    do:  struct.storeF Clerk "cl" (![ptrT] "ck") "$a0";;;
    let: "reply_ptr" := ref_zero ptrT in
    let: "$a0" := ref (zero_val (slice.T byteT)) in
    do:  "reply_ptr" <-[ptrT] "$a0";;;
    let: "err" := ref_zero uint64T in
    let: "$a0" := urpc.Client__Call (struct.loadF Clerk "cl" (![ptrT] "ck")) RPC_FRESHCID (NewSlice byteT #0) (![ptrT] "reply_ptr") #100 in
    do:  "err" <-[uint64T] "$a0";;;
    (if: (![uint64T] "err") ≠ #0
    then
      do:  log.Println #(str "ctr: urpc getcid call failed/timed out");;;
      do:  machine.Exit #1;;;
      do:  #()
    else #());;;
    let: "$a0" := erpc.MakeClient (marshal.Dec__GetInt (marshal.NewDec (![slice.T byteT] (![ptrT] "reply_ptr")))) in
    do:  struct.storeF Clerk "e" (![ptrT] "ck") "$a0";;;
    return: (![ptrT] "ck");;;
    do:  #().

(* server.go *)

Definition Server := struct.decl [
  "mu" :: ptrT;
  "e" :: ptrT;
  "v" :: uint64T;
  "lastEpoch" :: uint64T
].

Definition Server__Put: val :=
  rec: "Server__Put" "s" "args" :=
    let: "args" := ref_to ptrT "args" in
    let: "s" := ref_to ptrT "s" in
    do:  sync.Mutex__Lock (struct.loadF Server "mu" (![ptrT] "s"));;;
    (if: (struct.loadF PutArgs "epoch" (![ptrT] "args")) < (struct.loadF Server "lastEpoch" (![ptrT] "s"))
    then
      do:  sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;;
      return: (EStale);;;
      do:  #()
    else #());;;
    let: "$a0" := struct.loadF PutArgs "epoch" (![ptrT] "args") in
    do:  struct.storeF Server "lastEpoch" (![ptrT] "s") "$a0";;;
    let: "$a0" := struct.loadF PutArgs "v" (![ptrT] "args") in
    do:  struct.storeF Server "v" (![ptrT] "s") "$a0";;;
    do:  sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;;
    return: (ENone);;;
    do:  #().

Definition Server__Get: val :=
  rec: "Server__Get" "s" "epoch" "reply" :=
    let: "reply" := ref_to ptrT "reply" in
    let: "epoch" := ref_to uint64T "epoch" in
    let: "s" := ref_to ptrT "s" in
    do:  sync.Mutex__Lock (struct.loadF Server "mu" (![ptrT] "s"));;;
    let: "$a0" := ENone in
    do:  struct.storeF GetReply "err" (![ptrT] "reply") "$a0";;;
    (if: (![uint64T] "epoch") < (struct.loadF Server "lastEpoch" (![ptrT] "s"))
    then
      do:  sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;;
      let: "$a0" := EStale in
      do:  struct.storeF GetReply "err" (![ptrT] "reply") "$a0";;;
      return: (#());;;
      do:  #()
    else #());;;
    let: "$a0" := ![uint64T] "epoch" in
    do:  struct.storeF Server "lastEpoch" (![ptrT] "s") "$a0";;;
    let: "$a0" := struct.loadF Server "v" (![ptrT] "s") in
    do:  struct.storeF GetReply "val" (![ptrT] "reply") "$a0";;;
    do:  machine.Linearize #();;;
    do:  sync.Mutex__Unlock (struct.loadF Server "mu" (![ptrT] "s"));;;
    return: (#());;;
    do:  #().

Definition StartServer: val :=
  rec: "StartServer" "me" :=
    let: "me" := ref_to uint64T "me" in
    let: "s" := ref_zero ptrT in
    let: "$a0" := struct.alloc Server (zero_val (struct.t Server)) in
    do:  "s" <-[ptrT] "$a0";;;
    let: "$a0" := struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex)) in
    do:  struct.storeF Server "mu" (![ptrT] "s") "$a0";;;
    let: "$a0" := erpc.MakeServer #() in
    do:  struct.storeF Server "e" (![ptrT] "s") "$a0";;;
    let: "$a0" := #0 in
    do:  struct.storeF Server "v" (![ptrT] "s") "$a0";;;
    let: "handlers" := ref_zero (mapT (arrowT unitT unitT)) in
    let: "$a0" := NewMap uint64T (arrowT unitT unitT) #() in
    do:  "handlers" <-[mapT (arrowT unitT unitT)] "$a0";;;
    let: "$a0" := (λ: "raw_args" "raw_reply",
      let: "dec" := ref_zero (struct.t marshal.Dec) in
      let: "$a0" := marshal.NewDec (![slice.T byteT] "raw_args") in
      do:  "dec" <-[struct.t marshal.Dec] "$a0";;;
      let: "epoch" := ref_zero uint64T in
      let: "$a0" := marshal.Dec__GetInt (![struct.t marshal.Dec] "dec") in
      do:  "epoch" <-[uint64T] "$a0";;;
      let: "reply" := ref_zero ptrT in
      let: "$a0" := struct.alloc GetReply (zero_val (struct.t GetReply)) in
      do:  "reply" <-[ptrT] "$a0";;;
      do:  Server__Get (![ptrT] "s") (![uint64T] "epoch") (![ptrT] "reply");;;
      let: "$a0" := EncGetReply (![ptrT] "reply") in
      do:  (![ptrT] "raw_reply") <-[slice.T byteT] "$a0";;;
      do:  #()
      ) in
    do:  MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_GET "$a0";;;
    let: "$a0" := erpc.Server__HandleRequest (struct.loadF Server "e" (![ptrT] "s")) (λ: "raw_args" "reply",
      let: "args" := ref_zero ptrT in
      let: "$a0" := DecPutArgs (![slice.T byteT] "raw_args") in
      do:  "args" <-[ptrT] "$a0";;;
      let: "err" := ref_zero uint64T in
      let: "$a0" := Server__Put (![ptrT] "s") (![ptrT] "args") in
      do:  "err" <-[uint64T] "$a0";;;
      let: "enc" := ref_zero (struct.t marshal.Enc) in
      let: "$a0" := marshal.NewEnc #8 in
      do:  "enc" <-[struct.t marshal.Enc] "$a0";;;
      do:  marshal.Enc__PutInt (![struct.t marshal.Enc] "enc") (![uint64T] "err");;;
      let: "$a0" := marshal.Enc__Finish (![struct.t marshal.Enc] "enc") in
      do:  (![ptrT] "reply") <-[slice.T byteT] "$a0";;;
      do:  #()
      ) in
    do:  MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_PUT "$a0";;;
    let: "$a0" := (λ: "raw_args" "reply",
      let: "enc" := ref_zero (struct.t marshal.Enc) in
      let: "$a0" := marshal.NewEnc #8 in
      do:  "enc" <-[struct.t marshal.Enc] "$a0";;;
      do:  marshal.Enc__PutInt (![struct.t marshal.Enc] "enc") (erpc.Server__GetFreshCID (struct.loadF Server "e" (![ptrT] "s")));;;
      let: "$a0" := marshal.Enc__Finish (![struct.t marshal.Enc] "enc") in
      do:  (![ptrT] "reply") <-[slice.T byteT] "$a0";;;
      do:  #()
      ) in
    do:  MapInsert (![mapT (arrowT unitT unitT)] "handlers") RPC_FRESHCID "$a0";;;
    let: "r" := ref_zero ptrT in
    let: "$a0" := urpc.MakeServer (![mapT (arrowT unitT unitT)] "handlers") in
    do:  "r" <-[ptrT] "$a0";;;
    do:  urpc.Server__Serve (![ptrT] "r") (![uint64T] "me");;;
    do:  #().
