(* autogenerated from logging2 *)
From Perennial.go_lang Require Import prelude.

(* disk FFI *)
From Perennial.go_lang Require Import ffi.disk_prelude.

Definition LOGCOMMIT : expr := #0.

Definition LOGSTART : expr := #1.

Definition LOGMAXBLK : expr := #510.

Definition LOGEND : expr := LOGMAXBLK + LOGSTART.

Module Log.
  Definition S := struct.decl [
    "logLock" :: lockRefT;
    "memLock" :: lockRefT;
    "logSz" :: uint64T;
    "memLog" :: refT (slice.T disk.blockT);
    "memLen" :: refT uint64T;
    "memTxnNxt" :: refT uint64T;
    "logTxnNxt" :: refT uint64T
  ].
  Definition T: ty := struct.t S.
  Definition Ptr: ty := struct.ptrT S.
  Section fields.
    Context `{ext_ty: ext_types}.
    Definition get := struct.get S.
    Definition loadF := struct.loadF S.
  End fields.
End Log.

Definition Log__writeHdr: val :=
  λ: "log" "len",
    let: "hdr" := NewSlice byteT #4096 in
    UInt64Put "hdr" "len";;
    disk.Write LOGCOMMIT "hdr".
Theorem Log__writeHdr_t: ⊢ Log__writeHdr : (Log.T -> uint64T -> unitT).
Proof. typecheck. Qed.
Hint Resolve Log__writeHdr_t : types.

Definition Init: val :=
  λ: "logSz",
    let: "log" := struct.mk Log.S [
      "logLock" ::= Data.newLock #();
      "memLock" ::= Data.newLock #();
      "logSz" ::= "logSz";
      "memLog" ::= ref (zero_val (slice.T disk.blockT));
      "memLen" ::= ref (zero_val uint64T);
      "memTxnNxt" ::= ref (zero_val uint64T);
      "logTxnNxt" ::= ref (zero_val uint64T)
    ] in
    Log__writeHdr "log" #0;;
    "log".
Theorem Init_t: ⊢ Init : (uint64T -> Log.T).
Proof. typecheck. Qed.
Hint Resolve Init_t : types.

Definition Log__readHdr: val :=
  λ: "log",
    let: "hdr" := disk.Read LOGCOMMIT in
    let: "disklen" := UInt64Get "hdr" in
    "disklen".
Theorem Log__readHdr_t: ⊢ Log__readHdr : (Log.T -> uint64T).
Proof. typecheck. Qed.
Hint Resolve Log__readHdr_t : types.

Definition Log__readBlocks: val :=
  λ: "log" "len",
    let: "blks" := ref (NewSlice disk.blockT #0) in
    let: "i" := ref #0 in
    (for: (!"i" < "len"); ("i" <- !"i" + #1) :=
      let: "blk" := disk.Read (LOGSTART + !"i") in
      "blks" <- SliceAppend !"blks" "blk";;
      Continue);;
    !"blks".
Theorem Log__readBlocks_t: ⊢ Log__readBlocks : (Log.T -> uint64T -> slice.T disk.blockT).
Proof. typecheck. Qed.
Hint Resolve Log__readBlocks_t : types.

Definition Log__Read: val :=
  λ: "log",
    Data.lockAcquire Writer (Log.get "logLock" "log");;
    let: "disklen" := Log__readHdr "log" in
    let: "blks" := Log__readBlocks "log" "disklen" in
    Data.lockRelease Writer (Log.get "logLock" "log");;
    "blks".
Theorem Log__Read_t: ⊢ Log__Read : (Log.T -> slice.T disk.blockT).
Proof. typecheck. Qed.
Hint Resolve Log__Read_t : types.

Definition Log__memWrite: val :=
  λ: "log" "l",
    let: "n" := slice.len "l" in
    let: "i" := ref #0 in
    (for: (!"i" < "n"); ("i" <- !"i" + #1) :=
      Log.get "memLog" "log" <- SliceAppend (!(Log.get "memLog" "log")) (SliceGet "l" !"i");;
      Continue).
Theorem Log__memWrite_t: ⊢ Log__memWrite : (Log.T -> slice.T disk.blockT -> unitT).
Proof. typecheck. Qed.
Hint Resolve Log__memWrite_t : types.

Definition Log__memAppend: val :=
  λ: "log" "l",
    Data.lockAcquire Writer (Log.get "memLock" "log");;
    (if: !(Log.get "memLen" "log") + slice.len "l" ≥ Log.get "logSz" "log"
    then
      Data.lockRelease Writer (Log.get "memLock" "log");;
      (#false, #0)
    else
      let: "txn" := !(Log.get "memTxnNxt" "log") in
      let: "n" := !(Log.get "memLen" "log") + slice.len "l" in
      Log.get "memLen" "log" <- "n";;
      Log.get "memTxnNxt" "log" <- !(Log.get "memTxnNxt" "log") + #1;;
      Data.lockRelease Writer (Log.get "memLock" "log");;
      (#true, "txn")).
Theorem Log__memAppend_t: ⊢ Log__memAppend : (Log.T -> slice.T disk.blockT -> (boolT * uint64T)).
Proof. typecheck. Qed.
Hint Resolve Log__memAppend_t : types.

(* XXX just an atomic read? *)
Definition Log__readLogTxnNxt: val :=
  λ: "log",
    Data.lockAcquire Writer (Log.get "memLock" "log");;
    let: "n" := !(Log.get "logTxnNxt" "log") in
    Data.lockRelease Writer (Log.get "memLock" "log");;
    "n".
Theorem Log__readLogTxnNxt_t: ⊢ Log__readLogTxnNxt : (Log.T -> uint64T).
Proof. typecheck. Qed.
Hint Resolve Log__readLogTxnNxt_t : types.

Definition Log__diskAppendWait: val :=
  λ: "log" "txn",
    Skip;;
    (for: (#true); (Skip) :=
      let: "logtxn" := Log__readLogTxnNxt "log" in
      (if: "txn" < "logtxn"
      then Break
      else Continue)).
Theorem Log__diskAppendWait_t: ⊢ Log__diskAppendWait : (Log.T -> uint64T -> unitT).
Proof. typecheck. Qed.
Hint Resolve Log__diskAppendWait_t : types.

Definition Log__Append: val :=
  λ: "log" "l",
    let: ("ok", "txn") := Log__memAppend "log" "l" in
    (if: "ok"
    then
      Log__diskAppendWait "log" "txn";;
      #()
    else #());;
    "ok".
Theorem Log__Append_t: ⊢ Log__Append : (Log.T -> slice.T disk.blockT -> boolT).
Proof. typecheck. Qed.
Hint Resolve Log__Append_t : types.

Definition Log__writeBlocks: val :=
  λ: "log" "l" "pos",
    let: "n" := slice.len "l" in
    let: "i" := ref #0 in
    (for: (!"i" < "n"); ("i" <- !"i" + #1) :=
      let: "bk" := SliceGet "l" !"i" in
      disk.Write ("pos" + !"i") "bk";;
      Continue).
Theorem Log__writeBlocks_t: ⊢ Log__writeBlocks : (Log.T -> slice.T disk.blockT -> uint64T -> unitT).
Proof. typecheck. Qed.
Hint Resolve Log__writeBlocks_t : types.

Definition Log__diskAppend: val :=
  λ: "log",
    Data.lockAcquire Writer (Log.get "logLock" "log");;
    let: "disklen" := Log__readHdr "log" in
    Data.lockAcquire Writer (Log.get "memLock" "log");;
    let: "memlen" := !(Log.get "memLen" "log") in
    let: "allblks" := !(Log.get "memLog" "log") in
    let: "blks" := SliceSkip "allblks" "disklen" in
    let: "memnxt" := !(Log.get "memTxnNxt" "log") in
    Data.lockRelease Writer (Log.get "memLock" "log");;
    Log__writeBlocks "log" "blks" "disklen";;
    Log__writeHdr "log" "memlen";;
    Log.get "logTxnNxt" "log" <- "memnxt";;
    Data.lockRelease Writer (Log.get "logLock" "log").
Theorem Log__diskAppend_t: ⊢ Log__diskAppend : (Log.T -> unitT).
Proof. typecheck. Qed.
Hint Resolve Log__diskAppend_t : types.

Definition Log__Logger: val :=
  λ: "log",
    Skip;;
    (for: (#true); (Skip) :=
      Log__diskAppend "log";;
      Continue).
Theorem Log__Logger_t: ⊢ Log__Logger : (Log.T -> unitT).
Proof. typecheck. Qed.
Hint Resolve Log__Logger_t : types.

Module Txn.
  Definition S := struct.decl [
    "log" :: refT Log.T;
    "blks" :: mapT disk.blockT
  ].
  Definition T: ty := struct.t S.
  Definition Ptr: ty := struct.ptrT S.
  Section fields.
    Context `{ext_ty: ext_types}.
    Definition get := struct.get S.
    Definition loadF := struct.loadF S.
  End fields.
End Txn.

(* XXX wait if cannot reserve space in log *)
Definition Begin: val :=
  λ: "log",
    let: "txn" := struct.mk Txn.S [
      "log" ::= "log";
      "blks" ::= NewMap disk.blockT
    ] in
    "txn".
Theorem Begin_t: ⊢ Begin : (refT Log.T -> Txn.T).
Proof. typecheck. Qed.
Hint Resolve Begin_t : types.

Definition Txn__Write: val :=
  λ: "txn" "addr" "blk",
    let: "ret" := ref #true in
    let: (<>, "ok") := MapGet (Txn.get "blks" "txn") "addr" in
    (if: "ok"
    then
      MapInsert (Txn.get "blks" "txn") "addr" !"blk";;
      #()
    else #());;
    (if: ~ "ok"
    then
      (if: "addr" = LOGMAXBLK
      then "ret" <- #false
      else MapInsert (Txn.get "blks" "txn") "addr" !"blk");;
      #()
    else #());;
    !"ret".
Theorem Txn__Write_t: ⊢ Txn__Write : (Txn.T -> uint64T -> refT disk.blockT -> boolT).
Proof. typecheck. Qed.
Hint Resolve Txn__Write_t : types.

Definition Txn__Read: val :=
  λ: "txn" "addr",
    let: ("v", "ok") := MapGet (Txn.get "blks" "txn") "addr" in
    (if: "ok"
    then "v"
    else disk.Read ("addr" + LOGEND)).
Theorem Txn__Read_t: ⊢ Txn__Read : (Txn.T -> uint64T -> disk.blockT).
Proof. typecheck. Qed.
Hint Resolve Txn__Read_t : types.

Definition Txn__Commit: val :=
  λ: "txn",
    let: "blks" := ref (zero_val (slice.T disk.blockT)) in
    Data.mapIter (Txn.get "blks" "txn") (λ: <> "v",
      "blks" <- SliceAppend !"blks" "v");;
    let: "ok" := Log__Append (!(Txn.get "log" "txn")) !"blks" in
    "ok".
Theorem Txn__Commit_t: ⊢ Txn__Commit : (Txn.T -> boolT).
Proof. typecheck. Qed.
Hint Resolve Txn__Commit_t : types.
