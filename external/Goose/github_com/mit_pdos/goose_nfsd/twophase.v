(* autogenerated from github.com/mit-pdos/goose-nfsd/twophase *)
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

From Goose Require github_com.mit_pdos.goose_nfsd.addr.
From Goose Require github_com.mit_pdos.goose_nfsd.buftxn.
From Goose Require github_com.mit_pdos.goose_nfsd.lockmap.
From Goose Require github_com.mit_pdos.goose_nfsd.txn.
From Goose Require github_com.mit_pdos.goose_nfsd.util.

Definition TwoPhasePre := struct.decl [
  "txn" :: struct.ptrT txn.Txn;
  "locks" :: struct.ptrT lockmap.LockMap
].

Definition TwoPhase := struct.decl [
  "buftxn" :: struct.ptrT buftxn.BufTxn;
  "locks" :: struct.ptrT lockmap.LockMap;
  "acquired" :: mapT boolT
].

Definition Init: val :=
  rec: "Init" "d" :=
    let: "twophasePre" := struct.new TwoPhasePre [
      "txn" ::= txn.MkTxn "d";
      "locks" ::= lockmap.MkLockMap #()
    ] in
    "twophasePre".

(* Start a local transaction with no writes from a global Txn manager. *)
Definition Begin: val :=
  rec: "Begin" "twophasePre" :=
    let: "trans" := struct.new TwoPhase [
      "buftxn" ::= buftxn.Begin (struct.loadF TwoPhasePre "txn" "twophasePre");
      "locks" ::= struct.loadF TwoPhasePre "locks" "twophasePre";
      "acquired" ::= NewMap boolT
    ] in
    util.DPrintf #5 (#(str"tp Begin: %v
    ")) #();;
    "trans".

Definition TwoPhase__acquireNoCheck: val :=
  rec: "TwoPhase__acquireNoCheck" "twophase" "addr" :=
    let: "flatAddr" := addr.Addr__Flatid "addr" in
    lockmap.LockMap__Acquire (struct.loadF TwoPhase "locks" "twophase") "flatAddr";;
    MapInsert (struct.loadF TwoPhase "acquired" "twophase") "flatAddr" #true.

Definition TwoPhase__isAlreadyAcquired: val :=
  rec: "TwoPhase__isAlreadyAcquired" "twophase" "addr" :=
    let: "flatAddr" := addr.Addr__Flatid "addr" in
    Fst (MapGet (struct.loadF TwoPhase "acquired" "twophase") "flatAddr").

Definition TwoPhase__Acquire: val :=
  rec: "TwoPhase__Acquire" "twophase" "addr" :=
    let: "already_acquired" := TwoPhase__isAlreadyAcquired "twophase" "addr" in
    (if: ~ "already_acquired"
    then TwoPhase__acquireNoCheck "twophase" "addr"
    else #()).

Definition TwoPhase__ReleaseAll: val :=
  rec: "TwoPhase__ReleaseAll" "twophase" :=
    MapIter (struct.loadF TwoPhase "acquired" "twophase") (λ: "flatAddr" <>,
      lockmap.LockMap__Release (struct.loadF TwoPhase "locks" "twophase") "flatAddr").

Definition TwoPhase__readBufNoAcquire: val :=
  rec: "TwoPhase__readBufNoAcquire" "twophase" "addr" "sz" :=
    let: "s" := util.CloneByteSlice (struct.loadF buf.Buf "Data" (buftxn.BufTxn__ReadBuf (struct.loadF TwoPhase "buftxn" "twophase") "addr" "sz")) in
    "s".

Definition TwoPhase__ReadBuf: val :=
  rec: "TwoPhase__ReadBuf" "twophase" "addr" "sz" :=
    TwoPhase__Acquire "twophase" "addr";;
    TwoPhase__readBufNoAcquire "twophase" "addr" "sz".

(* OverWrite writes an object to addr *)
Definition TwoPhase__OverWrite: val :=
  rec: "TwoPhase__OverWrite" "twophase" "addr" "sz" "data" :=
    TwoPhase__Acquire "twophase" "addr";;
    buftxn.BufTxn__OverWrite (struct.loadF TwoPhase "buftxn" "twophase") "addr" "sz" "data".

Definition TwoPhase__ReadBufBit: val :=
  rec: "TwoPhase__ReadBufBit" "twophase" "addr" :=
    let: "dataByte" := SliceGet byteT (TwoPhase__ReadBuf "twophase" "addr" #1) #0 in
    (#(U8 1) = ("dataByte" ≫ ((struct.get addr.Addr "Off" "addr") `rem` #8) `and` #(U8 1))).

Definition bitToByte: val :=
  rec: "bitToByte" "off" "data" :=
    (if: "data"
    then (#(U8 1)) ≪ "off"
    else #(U8 0)).

Definition TwoPhase__OverWriteBit: val :=
  rec: "TwoPhase__OverWriteBit" "twophase" "addr" "data" :=
    let: "dataBytes" := NewSlice byteT #1 in
    SliceSet byteT "dataBytes" #0 (bitToByte ((struct.get addr.Addr "Off" "addr") `rem` #8) "data");;
    TwoPhase__OverWrite "twophase" "addr" #1 "dataBytes".

(* NDirty reports an upper bound on the size of this transaction when committed.

   The caller cannot rely on any particular properties of this function for
   safety. *)
Definition TwoPhase__NDirty: val :=
  rec: "TwoPhase__NDirty" "twophase" :=
    buftxn.BufTxn__NDirty (struct.loadF TwoPhase "buftxn" "twophase").

(* LogSz returns 511 *)
Definition TwoPhase__LogSz: val :=
  rec: "TwoPhase__LogSz" "twophase" :=
    buftxn.BufTxn__LogSz (struct.loadF TwoPhase "buftxn" "twophase").

(* LogSzBytes returns 511*4096 *)
Definition TwoPhase__LogSzBytes: val :=
  rec: "TwoPhase__LogSzBytes" "twophase" :=
    buftxn.BufTxn__LogSzBytes (struct.loadF TwoPhase "buftxn" "twophase").

Definition TwoPhase__CommitNoRelease: val :=
  rec: "TwoPhase__CommitNoRelease" "twophase" :=
    util.DPrintf #5 (#(str"tp Commit %p
    ")) #();;
    buftxn.BufTxn__CommitWait (struct.loadF TwoPhase "buftxn" "twophase") #true.

Definition TwoPhase__Commit: val :=
  rec: "TwoPhase__Commit" "twophase" :=
    let: "ok" := TwoPhase__CommitNoRelease "twophase" in
    TwoPhase__ReleaseAll "twophase";;
    "ok".
