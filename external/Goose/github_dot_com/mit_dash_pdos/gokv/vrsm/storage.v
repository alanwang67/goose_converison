(* autogenerated from github.com/mit-pdos/gokv/vrsm/storage *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.goose_dash_lang.std.
From Goose Require github_dot_com.mit_dash_pdos.gokv.aof.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require github_dot_com.mit_dash_pdos.gokv.vrsm.replica.
From Goose Require github_dot_com.tchajed.marshal.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition InMemoryStateMachine := struct.decl [
  "ApplyReadonly" :: ((slice.T byteT) -> (uint64T * (slice.T byteT)))%ht;
  "ApplyVolatile" :: ((slice.T byteT) -> (slice.T byteT))%ht;
  "GetState" :: (unitT -> (slice.T byteT))%ht;
  "SetState" :: ((slice.T byteT) -> uint64T -> unitT)%ht
].

Definition MAX_LOG_SIZE : expr := ((#64 * #1024) * #1024) * #1024.

Definition StateMachine := struct.decl [
  "fname" :: stringT;
  "logFile" :: ptrT;
  "logsize" :: uint64T;
  "sealed" :: boolT;
  "epoch" :: uint64T;
  "nextIndex" :: uint64T;
  "smMem" :: ptrT
].

(* FIXME: better name; this isn't the same as "MakeDurable" *)
Definition StateMachine__makeDurableWithSnap: val :=
  rec: "StateMachine__makeDurableWithSnap" "s" "snap" :=
    let: "snap" := ref_to (slice.T byteT) "snap" in
    let: "s" := ref_to ptrT "s" in
    let: "enc" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 (((#8 + (slice.len (![slice.T byteT] "snap"))) + #8) + #8)) in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (slice.len (![slice.T byteT] "snap")) in
    do:  "enc" <-[slice.T byteT] "$a0";;;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "enc") (![slice.T byteT] "snap") in
    do:  "enc" <-[slice.T byteT] "$a0";;;
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF StateMachine "epoch" (![ptrT] "s")) in
    do:  "enc" <-[slice.T byteT] "$a0";;;
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "enc") (struct.loadF StateMachine "nextIndex" (![ptrT] "s")) in
    do:  "enc" <-[slice.T byteT] "$a0";;;
    (if: struct.loadF StateMachine "sealed" (![ptrT] "s")
    then
      do:  marshal.WriteBytes (![slice.T byteT] "enc") (NewSlice byteT #1);;;
      do:  #()
    else #());;;
    do:  aof.AppendOnlyFile__Close (struct.loadF StateMachine "logFile" (![ptrT] "s"));;;
    do:  grove__ffi.FileWrite (struct.loadF StateMachine "fname" (![ptrT] "s")) (![slice.T byteT] "enc");;;
    let: "$a0" := aof.CreateAppendOnlyFile (struct.loadF StateMachine "fname" (![ptrT] "s")) in
    do:  struct.storeF StateMachine "logFile" (![ptrT] "s") "$a0";;;
    do:  #().

(* XXX: this is not safe to run concurrently with apply()
   requires that the state machine is not sealed *)
Definition StateMachine__truncateAndMakeDurable: val :=
  rec: "StateMachine__truncateAndMakeDurable" "s" :=
    let: "s" := ref_to ptrT "s" in
    let: "snap" := ref_zero (slice.T byteT) in
    let: "$a0" := (struct.loadF InMemoryStateMachine "GetState" (struct.loadF StateMachine "smMem" (![ptrT] "s"))) #() in
    do:  "snap" <-[slice.T byteT] "$a0";;;
    do:  StateMachine__makeDurableWithSnap (![ptrT] "s") (![slice.T byteT] "snap");;;
    do:  #().

Definition StateMachine__apply: val :=
  rec: "StateMachine__apply" "s" "op" :=
    let: "op" := ref_to (slice.T byteT) "op" in
    let: "s" := ref_to ptrT "s" in
    let: "ret" := ref_zero (slice.T byteT) in
    let: "$a0" := (struct.loadF InMemoryStateMachine "ApplyVolatile" (struct.loadF StateMachine "smMem" (![ptrT] "s"))) (![slice.T byteT] "op") in
    do:  "ret" <-[slice.T byteT] "$a0";;;
    let: "$a0" := std.SumAssumeNoOverflow (struct.loadF StateMachine "nextIndex" (![ptrT] "s")) #1 in
    do:  struct.storeF StateMachine "nextIndex" (![ptrT] "s") "$a0";;;
    do:  struct.storeF StateMachine "logsize" (![ptrT] "s") ((struct.loadF StateMachine "logsize" (![ptrT] "s")) + (slice.len (![slice.T byteT] "op")));;;
    let: "opWithLen" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 (#8 + (slice.len (![slice.T byteT] "op")))) in
    let: "$a0" := marshal.WriteInt (![slice.T byteT] "opWithLen") (slice.len (![slice.T byteT] "op")) in
    do:  "opWithLen" <-[slice.T byteT] "$a0";;;
    let: "$a0" := marshal.WriteBytes (![slice.T byteT] "opWithLen") (![slice.T byteT] "op") in
    do:  "opWithLen" <-[slice.T byteT] "$a0";;;
    let: "l" := ref_zero uint64T in
    let: "$a0" := aof.AppendOnlyFile__Append (struct.loadF StateMachine "logFile" (![ptrT] "s")) (![slice.T byteT] "opWithLen") in
    do:  "l" <-[uint64T] "$a0";;;
    let: "f" := ref_zero ptrT in
    let: "$a0" := struct.loadF StateMachine "logFile" (![ptrT] "s") in
    do:  "f" <-[ptrT] "$a0";;;
    let: "waitFn" := ref_zero (arrowT unitT unitT) in
    let: "$a0" := (λ: <>,
      do:  aof.AppendOnlyFile__WaitAppend (![ptrT] "f") (![uint64T] "l");;;
      do:  #()
      ) in
    do:  "waitFn" <-[(arrowT unitT unitT)] "$a0";;;
    return: (![slice.T byteT] "ret", ![(arrowT unitT unitT)] "waitFn");;;
    do:  #().

Definition StateMachine__applyReadonly: val :=
  rec: "StateMachine__applyReadonly" "s" "op" :=
    let: "op" := ref_to (slice.T byteT) "op" in
    let: "s" := ref_to ptrT "s" in
    return: ((struct.loadF InMemoryStateMachine "ApplyReadonly" (struct.loadF StateMachine "smMem" (![ptrT] "s"))) (![slice.T byteT] "op"));;;
    do:  #().

(* TODO: make the nextIndex and epoch argument order consistent with replica.StateMachine *)
Definition StateMachine__setStateAndUnseal: val :=
  rec: "StateMachine__setStateAndUnseal" "s" "snap" "nextIndex" "epoch" :=
    let: "epoch" := ref_to uint64T "epoch" in
    let: "nextIndex" := ref_to uint64T "nextIndex" in
    let: "snap" := ref_to (slice.T byteT) "snap" in
    let: "s" := ref_to ptrT "s" in
    let: "$a0" := ![uint64T] "epoch" in
    do:  struct.storeF StateMachine "epoch" (![ptrT] "s") "$a0";;;
    let: "$a0" := ![uint64T] "nextIndex" in
    do:  struct.storeF StateMachine "nextIndex" (![ptrT] "s") "$a0";;;
    let: "$a0" := #false in
    do:  struct.storeF StateMachine "sealed" (![ptrT] "s") "$a0";;;
    do:  (struct.loadF InMemoryStateMachine "SetState" (struct.loadF StateMachine "smMem" (![ptrT] "s"))) (![slice.T byteT] "snap") (![uint64T] "nextIndex");;;
    do:  StateMachine__makeDurableWithSnap (![ptrT] "s") (![slice.T byteT] "snap");;;
    do:  #().

Definition StateMachine__getStateAndSeal: val :=
  rec: "StateMachine__getStateAndSeal" "s" :=
    let: "s" := ref_to ptrT "s" in
    (if: (~ (struct.loadF StateMachine "sealed" (![ptrT] "s")))
    then
      let: "$a0" := #true in
      do:  struct.storeF StateMachine "sealed" (![ptrT] "s") "$a0";;;
      let: "l" := ref_zero uint64T in
      let: "$a0" := aof.AppendOnlyFile__Append (struct.loadF StateMachine "logFile" (![ptrT] "s")) (NewSlice byteT #1) in
      do:  "l" <-[uint64T] "$a0";;;
      do:  aof.AppendOnlyFile__WaitAppend (struct.loadF StateMachine "logFile" (![ptrT] "s")) (![uint64T] "l");;;
      do:  #()
    else #());;;
    let: "snap" := ref_zero (slice.T byteT) in
    let: "$a0" := (struct.loadF InMemoryStateMachine "GetState" (struct.loadF StateMachine "smMem" (![ptrT] "s"))) #() in
    do:  "snap" <-[slice.T byteT] "$a0";;;
    return: (![slice.T byteT] "snap");;;
    do:  #().

Definition recoverStateMachine: val :=
  rec: "recoverStateMachine" "smMem" "fname" :=
    let: "fname" := ref_to stringT "fname" in
    let: "smMem" := ref_to ptrT "smMem" in
    let: "s" := ref_zero ptrT in
    let: "$a0" := struct.new StateMachine [
      "fname" ::= ![stringT] "fname";
      "smMem" ::= ![ptrT] "smMem"
    ] in
    do:  "s" <-[ptrT] "$a0";;;
    let: "enc" := ref_to (slice.T byteT) (grove__ffi.FileRead (struct.loadF StateMachine "fname" (![ptrT] "s"))) in
    (if: (slice.len (![slice.T byteT] "enc")) = #0
    then
      let: "initState" := ref_zero (slice.T byteT) in
      let: "$a0" := (struct.loadF InMemoryStateMachine "GetState" (![ptrT] "smMem")) #() in
      do:  "initState" <-[slice.T byteT] "$a0";;;
      let: "initialContents" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 (((#8 + (slice.len (![slice.T byteT] "initState"))) + #8) + #8)) in
      let: "$a0" := marshal.WriteInt (![slice.T byteT] "initialContents") (slice.len (![slice.T byteT] "initState")) in
      do:  "initialContents" <-[slice.T byteT] "$a0";;;
      let: "$a0" := marshal.WriteBytes (![slice.T byteT] "initialContents") (![slice.T byteT] "initState") in
      do:  "initialContents" <-[slice.T byteT] "$a0";;;
      let: "$a0" := marshal.WriteInt (![slice.T byteT] "initialContents") #0 in
      do:  "initialContents" <-[slice.T byteT] "$a0";;;
      let: "$a0" := marshal.WriteInt (![slice.T byteT] "initialContents") #0 in
      do:  "initialContents" <-[slice.T byteT] "$a0";;;
      do:  grove__ffi.FileWrite (struct.loadF StateMachine "fname" (![ptrT] "s")) (![slice.T byteT] "initialContents");;;
      let: "$a0" := aof.CreateAppendOnlyFile (![stringT] "fname") in
      do:  struct.storeF StateMachine "logFile" (![ptrT] "s") "$a0";;;
      return: (![ptrT] "s");;;
      do:  #()
    else #());;;
    let: "$a0" := aof.CreateAppendOnlyFile (![stringT] "fname") in
    do:  struct.storeF StateMachine "logFile" (![ptrT] "s") "$a0";;;
    let: "snapLen" := ref (zero_val uint64T) in
    let: "snap" := ref (zero_val (slice.T byteT)) in
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    do:  "enc" <-[slice.T byteT] "$a1";;;
    do:  "snapLen" <-[uint64T] "$a0";;;
    let: "$a0" := SliceSubslice byteT (![slice.T byteT] "enc") #0 (![uint64T] "snapLen") in
    do:  "snap" <-[slice.T byteT] "$a0";;;
    let: "n" := ref_zero intT in
    let: "$a0" := slice.len (![slice.T byteT] "enc") in
    do:  "n" <-[intT] "$a0";;;
    let: "$a0" := SliceSubslice byteT (![slice.T byteT] "enc") (![uint64T] "snapLen") (![intT] "n") in
    do:  "enc" <-[slice.T byteT] "$a0";;;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    do:  "enc" <-[slice.T byteT] "$a1";;;
    do:  struct.storeF StateMachine "epoch" (![ptrT] "s") "$a0";;;
    let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
    do:  "enc" <-[slice.T byteT] "$a1";;;
    do:  struct.storeF StateMachine "nextIndex" (![ptrT] "s") "$a0";;;
    do:  (struct.loadF InMemoryStateMachine "SetState" (struct.loadF StateMachine "smMem" (![ptrT] "s"))) (![slice.T byteT] "snap") (struct.loadF StateMachine "nextIndex" (![ptrT] "s"));;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: (slice.len (![slice.T byteT] "enc")) > #1
      then
        let: "opLen" := ref (zero_val uint64T) in
        let: ("$a0", "$a1") := marshal.ReadInt (![slice.T byteT] "enc") in
        do:  "enc" <-[slice.T byteT] "$a1";;;
        do:  "opLen" <-[uint64T] "$a0";;;
        let: "op" := ref_zero (slice.T byteT) in
        let: "$a0" := SliceSubslice byteT (![slice.T byteT] "enc") #0 (![uint64T] "opLen") in
        do:  "op" <-[slice.T byteT] "$a0";;;
        let: "n" := ref_zero intT in
        let: "$a0" := slice.len (![slice.T byteT] "enc") in
        do:  "n" <-[intT] "$a0";;;
        let: "$a0" := SliceSubslice byteT (![slice.T byteT] "enc") (![uint64T] "opLen") (![intT] "n") in
        do:  "enc" <-[slice.T byteT] "$a0";;;
        do:  (struct.loadF InMemoryStateMachine "ApplyVolatile" (struct.loadF StateMachine "smMem" (![ptrT] "s"))) (![slice.T byteT] "op");;;
        let: "$a0" := std.SumAssumeNoOverflow (struct.loadF StateMachine "nextIndex" (![ptrT] "s")) #1 in
        do:  struct.storeF StateMachine "nextIndex" (![ptrT] "s") "$a0";;;
        do:  #()
      else
        break: #();;;
        do:  #());;;
      do:  #()).

(* XXX: putting this here because MakeServer takes nextIndex, epoch, and sealed
   as input, and the user of simplelog won't have access to the private fields
   index, epoch, etc.

   Maybe we should make those be a part of replica.StateMachine *)
Definition MakePbServer: val :=
  rec: "MakePbServer" "smMem" "fname" "confHosts" :=
    let: "confHosts" := ref_to (slice.T uint64T) "confHosts" in
    let: "fname" := ref_to stringT "fname" in
    let: "smMem" := ref_to ptrT "smMem" in
    let: "s" := ref_zero ptrT in
    let: "$a0" := recoverStateMachine (![ptrT] "smMem") (![stringT] "fname") in
    do:  "s" <-[ptrT] "$a0";;;
    let: "sm" := ref_zero ptrT in
    let: "$a0" := struct.new replica.StateMachine [
      "StartApply" ::= (λ: "op",
        return: (StateMachine__apply (![ptrT] "s") (![slice.T byteT] "op"));;;
        do:  #()
        );
      "ApplyReadonly" ::= (λ: "op",
        return: (StateMachine__applyReadonly (![ptrT] "s") (![slice.T byteT] "op"));;;
        do:  #()
        );
      "SetStateAndUnseal" ::= (λ: "snap" "nextIndex" "epoch",
        do:  StateMachine__setStateAndUnseal (![ptrT] "s") (![slice.T byteT] "snap") (![uint64T] "nextIndex") (![uint64T] "epoch");;;
        do:  #()
        );
      "GetStateAndSeal" ::= (λ: <>,
        return: (StateMachine__getStateAndSeal (![ptrT] "s"));;;
        do:  #()
        )
    ] in
    do:  "sm" <-[ptrT] "$a0";;;
    return: (replica.MakeServer (![ptrT] "sm") (![slice.T uint64T] "confHosts") (struct.loadF StateMachine "nextIndex" (![ptrT] "s")) (struct.loadF StateMachine "epoch" (![ptrT] "s")) (struct.loadF StateMachine "sealed" (![ptrT] "s")));;;
    do:  #().
