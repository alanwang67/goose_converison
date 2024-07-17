(* autogenerated from github.com/mit-pdos/gokv/urpc *)
From New.golang Require Import defn.
From New.code Require github_com.goose_lang.std.
From New.code Require github_com.mit_pdos.gokv.grove_ffi.
From New.code Require github_com.tchajed.goose.machine.
From New.code Require github_com.tchajed.marshal.
From New.code Require log.
From New.code Require sync.

From New Require Import grove_prelude.

Definition Server : go_type := structT [
  "handlers" :: mapT uint64T funcT
].

Definition Server__rpcHandle : val :=
  rec: "Server__rpcHandle" "srv" "conn" "rpcid" "seqno" "data" :=
    exception_do (let: "srv" := ref_ty ptrT "srv" in
    let: "data" := ref_ty (sliceT byteT) "data" in
    let: "seqno" := ref_ty uint64T "seqno" in
    let: "rpcid" := ref_ty uint64T "rpcid" in
    let: "conn" := ref_ty grove_ffi.Connection "conn" in
    let: "replyData" := ref_ty ptrT (zero_val ptrT) in
    let: "$a0" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    do:  "replyData" <-[ptrT] "$a0";;;
    let: "f" := ref_ty funcT (zero_val funcT) in
    let: "$a0" := Fst (map.get (![mapT uint64T funcT] (struct.field_ref Server "handlers" (![ptrT] "srv"))) (![uint64T] "rpcid")) in
    do:  "f" <-[funcT] "$a0";;;
    do:  (![funcT] "f") (![sliceT byteT] "data") (![ptrT] "replyData");;;
    let: "data1" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := slice.make3 byteT #0 (#8 + (slice.len (![sliceT byteT] (![ptrT] "replyData")))) in
    do:  "data1" <-[sliceT byteT] "$a0";;;
    let: "data2" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := marshal.WriteInt (![sliceT byteT] "data1") (![uint64T] "seqno") in
    do:  "data2" <-[sliceT byteT] "$a0";;;
    let: "data3" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := marshal.WriteBytes (![sliceT byteT] "data2") (![sliceT byteT] (![ptrT] "replyData")) in
    do:  "data3" <-[sliceT byteT] "$a0";;;
    do:  grove_ffi.Send (![grove_ffi.Connection] "conn") (![sliceT byteT] "data3");;;
    do:  #()).

Definition MakeServer : val :=
  rec: "MakeServer" "handlers" :=
    exception_do (let: "handlers" := ref_ty (mapT uint64T funcT) "handlers" in
    return: (ref_ty Server (struct.make Server [
       "handlers" ::= ![mapT uint64T funcT] "handlers"
     ]));;;
    do:  #()).

Definition Server__readThread : val :=
  rec: "Server__readThread" "srv" "conn" :=
    exception_do (let: "srv" := ref_ty ptrT "srv" in
    let: "conn" := ref_ty grove_ffi.Connection "conn" in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "r" := ref_ty grove_ffi.ReceiveRet (zero_val grove_ffi.ReceiveRet) in
      let: "$a0" := grove_ffi.Receive (![grove_ffi.Connection] "conn") in
      do:  "r" <-[grove_ffi.ReceiveRet] "$a0";;;
      (if: ![boolT] (struct.field_ref grove_ffi.ReceiveRet "Err" "r")
      then
        break: #();;;
        do:  #()
      else do:  #());;;
      let: "data" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
      let: "$a0" := ![sliceT byteT] (struct.field_ref grove_ffi.ReceiveRet "Data" "r") in
      do:  "data" <-[sliceT byteT] "$a0";;;
      let: "rpcid" := ref_ty uint64T (zero_val uint64T) in
      let: ("$a0", "$a1") := marshal.ReadInt (![sliceT byteT] "data") in
      do:  "data" <-[sliceT byteT] "$a1";;;
      do:  "rpcid" <-[uint64T] "$a0";;;
      let: "seqno" := ref_ty uint64T (zero_val uint64T) in
      let: ("$a0", "$a1") := marshal.ReadInt (![sliceT byteT] "data") in
      do:  "data" <-[sliceT byteT] "$a1";;;
      do:  "seqno" <-[uint64T] "$a0";;;
      let: "req" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
      let: "$a0" := ![sliceT byteT] "data" in
      do:  "req" <-[sliceT byteT] "$a0";;;
      do:  let: "$go" := (λ: <>,
        do:  (Server__rpcHandle (![ptrT] "srv")) (![grove_ffi.Connection] "conn") (![uint64T] "rpcid") (![uint64T] "seqno") (![sliceT byteT] "req");;;
        do:  #()
        ) in
      Fork ("$go" #());;;
      continue: #();;;
      do:  #());;;
    do:  #()).

Definition Server__Serve : val :=
  rec: "Server__Serve" "srv" "host" :=
    exception_do (let: "srv" := ref_ty ptrT "srv" in
    let: "host" := ref_ty uint64T "host" in
    let: "listener" := ref_ty grove_ffi.Listener (zero_val grove_ffi.Listener) in
    let: "$a0" := grove_ffi.Listen (![uint64T] "host") in
    do:  "listener" <-[grove_ffi.Listener] "$a0";;;
    do:  let: "$go" := (λ: <>,
      (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
        let: "conn" := ref_ty grove_ffi.Connection (zero_val grove_ffi.Connection) in
        let: "$a0" := grove_ffi.Accept (![grove_ffi.Listener] "listener") in
        do:  "conn" <-[grove_ffi.Connection] "$a0";;;
        do:  let: "$go" := (λ: <>,
          do:  (Server__readThread (![ptrT] "srv")) (![grove_ffi.Connection] "conn");;;
          do:  #()
          ) in
        Fork ("$go" #());;;
        do:  #());;;
      do:  #()
      ) in
    Fork ("$go" #());;;
    do:  #()).

Definition callbackStateWaiting : expr := #0.

Definition callbackStateDone : expr := #1.

Definition callbackStateAborted : expr := #2.

Definition Callback : go_type := structT [
  "reply" :: ptrT;
  "state" :: ptrT;
  "cond" :: ptrT
].

Definition Client : go_type := structT [
  "mu" :: ptrT;
  "conn" :: grove_ffi.Connection;
  "seq" :: uint64T;
  "pending" :: mapT uint64T ptrT
].

Definition Client__replyThread : val :=
  rec: "Client__replyThread" "cl" :=
    exception_do (let: "cl" := ref_ty ptrT "cl" in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "r" := ref_ty grove_ffi.ReceiveRet (zero_val grove_ffi.ReceiveRet) in
      let: "$a0" := grove_ffi.Receive (![grove_ffi.Connection] (struct.field_ref Client "conn" (![ptrT] "cl"))) in
      do:  "r" <-[grove_ffi.ReceiveRet] "$a0";;;
      (if: ![boolT] (struct.field_ref grove_ffi.ReceiveRet "Err" "r")
      then
        do:  (sync.Mutex__Lock (![ptrT] (struct.field_ref Client "mu" (![ptrT] "cl")))) #();;;
        do:  MapIter (![mapT uint64T ptrT] (struct.field_ref Client "pending" (![ptrT] "cl"))) (λ: <> "cb",
          let: "$a0" := callbackStateAborted in
          do:  (![ptrT] (struct.field_ref Callback "state" (![ptrT] "cb"))) <-[uint64T] "$a0";;;
          do:  (sync.Cond__Signal (![ptrT] (struct.field_ref Callback "cond" (![ptrT] "cb")))) #();;;
          do:  #());;;
        do:  (sync.Mutex__Unlock (![ptrT] (struct.field_ref Client "mu" (![ptrT] "cl")))) #();;;
        break: #();;;
        do:  #()
      else do:  #());;;
      let: "data" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
      let: "$a0" := ![sliceT byteT] (struct.field_ref grove_ffi.ReceiveRet "Data" "r") in
      do:  "data" <-[sliceT byteT] "$a0";;;
      let: "seqno" := ref_ty uint64T (zero_val uint64T) in
      let: ("$a0", "$a1") := marshal.ReadInt (![sliceT byteT] "data") in
      do:  "data" <-[sliceT byteT] "$a1";;;
      do:  "seqno" <-[uint64T] "$a0";;;
      let: "reply" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
      let: "$a0" := ![sliceT byteT] "data" in
      do:  "reply" <-[sliceT byteT] "$a0";;;
      do:  (sync.Mutex__Lock (![ptrT] (struct.field_ref Client "mu" (![ptrT] "cl")))) #();;;
      let: "ok" := ref_ty boolT (zero_val boolT) in
      let: "cb" := ref_ty ptrT (zero_val ptrT) in
      let: ("$a0", "$a1") := Fst (map.get (![mapT uint64T ptrT] (struct.field_ref Client "pending" (![ptrT] "cl"))) (![uint64T] "seqno")) in
      do:  "ok" <-[boolT] "$a1";;;
      do:  "cb" <-[ptrT] "$a0";;;
      (if: ![boolT] "ok"
      then
        do:  MapDelete (![mapT uint64T ptrT] (struct.field_ref Client "pending" (![ptrT] "cl"))) (![uint64T] "seqno");;;
        let: "$a0" := ![sliceT byteT] "reply" in
        do:  (![ptrT] (struct.field_ref Callback "reply" (![ptrT] "cb"))) <-[sliceT byteT] "$a0";;;
        let: "$a0" := callbackStateDone in
        do:  (![ptrT] (struct.field_ref Callback "state" (![ptrT] "cb"))) <-[uint64T] "$a0";;;
        do:  (sync.Cond__Signal (![ptrT] (struct.field_ref Callback "cond" (![ptrT] "cb")))) #();;;
        do:  #()
      else do:  #());;;
      do:  (sync.Mutex__Unlock (![ptrT] (struct.field_ref Client "mu" (![ptrT] "cl")))) #();;;
      continue: #();;;
      do:  #());;;
    do:  #()).

Definition TryMakeClient : val :=
  rec: "TryMakeClient" "host_name" :=
    exception_do (let: "host_name" := ref_ty uint64T "host_name" in
    let: "host" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := ![uint64T] "host_name" in
    do:  "host" <-[uint64T] "$a0";;;
    let: "a" := ref_ty grove_ffi.ConnectRet (zero_val grove_ffi.ConnectRet) in
    let: "$a0" := grove_ffi.Connect (![uint64T] "host") in
    do:  "a" <-[grove_ffi.ConnectRet] "$a0";;;
    let: "nilClient" := ref_ty ptrT (zero_val ptrT) in
    (if: ![boolT] (struct.field_ref grove_ffi.ConnectRet "Err" "a")
    then
      return: (#1, ![ptrT] "nilClient");;;
      do:  #()
    else do:  #());;;
    let: "cl" := ref_ty ptrT (zero_val ptrT) in
    let: "$a0" := ref_ty Client (struct.make Client [
      "conn" ::= ![grove_ffi.Connection] (struct.field_ref grove_ffi.ConnectRet "Connection" "a");
      "mu" ::= ref_ty sync.Mutex (zero_val sync.Mutex);
      "seq" ::= #1;
      "pending" ::= map.make uint64T ptrT #()
    ]) in
    do:  "cl" <-[ptrT] "$a0";;;
    do:  let: "$go" := (λ: <>,
      do:  (Client__replyThread (![ptrT] "cl")) #();;;
      do:  #()
      ) in
    Fork ("$go" #());;;
    return: (#0, ![ptrT] "cl");;;
    do:  #()).

Definition MakeClient : val :=
  rec: "MakeClient" "host_name" :=
    exception_do (let: "host_name" := ref_ty uint64T "host_name" in
    let: "cl" := ref_ty ptrT (zero_val ptrT) in
    let: "err" := ref_ty uint64T (zero_val uint64T) in
    let: ("$a0", "$a1") := TryMakeClient (![uint64T] "host_name") in
    do:  "cl" <-[ptrT] "$a1";;;
    do:  "err" <-[uint64T] "$a0";;;
    (if: (![uint64T] "err") ≠ #0
    then
      do:  log.Printf #(str "Unable to connect to %!!(MISSING)!(MISSING)!(MISSING)!(MISSING)!(MISSING)s(MISSING)") (grove_ffi.AddressToStr (![uint64T] "host_name"));;;
      do:  #()
    else do:  #());;;
    do:  machine.Assume ((![uint64T] "err") = #0);;;
    return: (![ptrT] "cl");;;
    do:  #()).

Definition Error : go_type := uint64T.

Definition ErrNone : expr := #0.

Definition ErrTimeout : expr := #1.

Definition ErrDisconnect : expr := #2.

Definition Client__CallStart : val :=
  rec: "Client__CallStart" "cl" "rpcid" "args" :=
    exception_do (let: "cl" := ref_ty ptrT "cl" in
    let: "args" := ref_ty (sliceT byteT) "args" in
    let: "rpcid" := ref_ty uint64T "rpcid" in
    let: "reply_buf" := ref_ty ptrT (zero_val ptrT) in
    let: "$a0" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    do:  "reply_buf" <-[ptrT] "$a0";;;
    let: "cb" := ref_ty ptrT (zero_val ptrT) in
    let: "$a0" := ref_ty Callback (struct.make Callback [
      "reply" ::= ![ptrT] "reply_buf";
      "state" ::= ref_ty uint64T (zero_val uint64T);
      "cond" ::= sync.NewCond (![ptrT] (struct.field_ref Client "mu" (![ptrT] "cl")))
    ]) in
    do:  "cb" <-[ptrT] "$a0";;;
    let: "$a0" := callbackStateWaiting in
    do:  (![ptrT] (struct.field_ref Callback "state" (![ptrT] "cb"))) <-[uint64T] "$a0";;;
    do:  (sync.Mutex__Lock (![ptrT] (struct.field_ref Client "mu" (![ptrT] "cl")))) #();;;
    let: "seqno" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := ![uint64T] (struct.field_ref Client "seq" (![ptrT] "cl")) in
    do:  "seqno" <-[uint64T] "$a0";;;
    let: "$a0" := std.SumAssumeNoOverflow (![uint64T] (struct.field_ref Client "seq" (![ptrT] "cl"))) #1 in
    do:  (struct.field_ref Client "seq" (![ptrT] "cl")) <-[uint64T] "$a0";;;
    let: "$a0" := ![ptrT] "cb" in
    do:  map.insert (![mapT uint64T ptrT] (struct.field_ref Client "pending" (![ptrT] "cl"))) (![uint64T] "seqno") "$a0";;;
    do:  (sync.Mutex__Unlock (![ptrT] (struct.field_ref Client "mu" (![ptrT] "cl")))) #();;;
    let: "data1" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := slice.make3 byteT #0 ((#8 + #8) + (slice.len (![sliceT byteT] "args"))) in
    do:  "data1" <-[sliceT byteT] "$a0";;;
    let: "data2" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := marshal.WriteInt (![sliceT byteT] "data1") (![uint64T] "rpcid") in
    do:  "data2" <-[sliceT byteT] "$a0";;;
    let: "data3" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := marshal.WriteInt (![sliceT byteT] "data2") (![uint64T] "seqno") in
    do:  "data3" <-[sliceT byteT] "$a0";;;
    let: "reqData" := ref_ty (sliceT byteT) (zero_val (sliceT byteT)) in
    let: "$a0" := marshal.WriteBytes (![sliceT byteT] "data3") (![sliceT byteT] "args") in
    do:  "reqData" <-[sliceT byteT] "$a0";;;
    (if: grove_ffi.Send (![grove_ffi.Connection] (struct.field_ref Client "conn" (![ptrT] "cl"))) (![sliceT byteT] "reqData")
    then
      return: (ref_ty Callback (struct.make Callback [
       ]), ErrDisconnect);;;
      do:  #()
    else do:  #());;;
    return: (![ptrT] "cb", ErrNone);;;
    do:  #()).

Definition Client__CallComplete : val :=
  rec: "Client__CallComplete" "cl" "cb" "reply" "timeout_ms" :=
    exception_do (let: "cl" := ref_ty ptrT "cl" in
    let: "timeout_ms" := ref_ty uint64T "timeout_ms" in
    let: "reply" := ref_ty ptrT "reply" in
    let: "cb" := ref_ty ptrT "cb" in
    do:  (sync.Mutex__Lock (![ptrT] (struct.field_ref Client "mu" (![ptrT] "cl")))) #();;;
    (if: (![uint64T] (![ptrT] (struct.field_ref Callback "state" (![ptrT] "cb")))) = callbackStateWaiting
    then
      do:  machine.WaitTimeout (![ptrT] (struct.field_ref Callback "cond" (![ptrT] "cb"))) (![uint64T] "timeout_ms");;;
      do:  #()
    else do:  #());;;
    let: "state" := ref_ty uint64T (zero_val uint64T) in
    let: "$a0" := ![uint64T] (![ptrT] (struct.field_ref Callback "state" (![ptrT] "cb"))) in
    do:  "state" <-[uint64T] "$a0";;;
    (if: (![uint64T] "state") = callbackStateDone
    then
      let: "$a0" := ![sliceT byteT] (![ptrT] (struct.field_ref Callback "reply" (![ptrT] "cb"))) in
      do:  (![ptrT] "reply") <-[sliceT byteT] "$a0";;;
      do:  (sync.Mutex__Unlock (![ptrT] (struct.field_ref Client "mu" (![ptrT] "cl")))) #();;;
      return: (#0);;;
      do:  #()
    else
      do:  (sync.Mutex__Unlock (![ptrT] (struct.field_ref Client "mu" (![ptrT] "cl")))) #();;;
      (if: (![uint64T] "state") = callbackStateAborted
      then
        return: (ErrDisconnect);;;
        do:  #()
      else
        return: (ErrTimeout);;;
        do:  #());;;
      do:  #());;;
    do:  #()).

Definition Client__Call : val :=
  rec: "Client__Call" "cl" "rpcid" "args" "reply" "timeout_ms" :=
    exception_do (let: "cl" := ref_ty ptrT "cl" in
    let: "timeout_ms" := ref_ty uint64T "timeout_ms" in
    let: "reply" := ref_ty ptrT "reply" in
    let: "args" := ref_ty (sliceT byteT) "args" in
    let: "rpcid" := ref_ty uint64T "rpcid" in
    let: "err" := ref_ty uint64T (zero_val uint64T) in
    let: "cb" := ref_ty ptrT (zero_val ptrT) in
    let: ("$a0", "$a1") := (Client__CallStart (![ptrT] "cl")) (![uint64T] "rpcid") (![sliceT byteT] "args") in
    do:  "err" <-[uint64T] "$a1";;;
    do:  "cb" <-[ptrT] "$a0";;;
    (if: (![uint64T] "err") ≠ #0
    then
      return: (![uint64T] "err");;;
      do:  #()
    else do:  #());;;
    return: ((Client__CallComplete (![ptrT] "cl")) (![ptrT] "cb") (![ptrT] "reply") (![uint64T] "timeout_ms"));;;
    do:  #()).
