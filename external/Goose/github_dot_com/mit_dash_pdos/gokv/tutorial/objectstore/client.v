(* autogenerated from github.com/mit-pdos/gokv/tutorial/objectstore/client *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require github_dot_com.mit_dash_pdos.gokv.tutorial.objectstore.chunk.
From Goose Require github_dot_com.mit_dash_pdos.gokv.tutorial.objectstore.dir.
From Goose Require sync.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition Clerk := struct.decl [
  "dCk" :: ptrT;
  "chCk" :: ptrT
].

Definition Writer := struct.decl [
  "writeId" :: uint64T;
  "index" :: uint64T;
  "keyname" :: stringT;
  "wg" :: ptrT;
  "ck" :: ptrT;
  "chunkAddrs" :: slice.T uint64T
].

Definition Clerk__PrepareWrite: val :=
  rec: "Clerk__PrepareWrite" "ck" "keyname" :=
    let: "keyname" := ref_to stringT "keyname" in
    let: "ck" := ref_to ptrT "ck" in
    let: "w" := ref_zero (struct.t dir.PreparedWrite) in
    let: "$a0" := dir.Clerk__PrepareWrite (struct.loadF Clerk "dCk" (![ptrT] "ck")) in
    do:  "w" <-[struct.t dir.PreparedWrite] "$a0";;;
    return: (struct.new Writer [
       "writeId" ::= struct.get dir.PreparedWrite "Id" (![struct.t dir.PreparedWrite] "w");
       "index" ::= #0;
       "keyname" ::= ![stringT] "keyname";
       "chunkAddrs" ::= struct.get dir.PreparedWrite "ChunkAddrs" (![struct.t dir.PreparedWrite] "w")
     ]);;;
    do:  #().

Definition Writer__AppendChunk: val :=
  rec: "Writer__AppendChunk" "w" "data" :=
    let: "data" := ref_to (slice.T byteT) "data" in
    let: "w" := ref_to ptrT "w" in
    do:  sync.WaitGroup__Add (struct.loadF Writer "wg" (![ptrT] "w")) #1;;;
    let: "index" := ref_zero uint64T in
    let: "$a0" := struct.loadF Writer "index" (![ptrT] "w") in
    do:  "index" <-[uint64T] "$a0";;;
    let: "$a0" := (struct.loadF Writer "index" (![ptrT] "w")) + #1 in
    do:  struct.storeF Writer "index" (![ptrT] "w") "$a0";;;
    do:  Fork (let: "addr" := ref_zero uint64T in
          let: "$a0" := SliceGet uint64T (struct.loadF Writer "chunkAddrs" (![ptrT] "w")) ((![uint64T] "index") `rem` (slice.len (struct.loadF Writer "chunkAddrs" (![ptrT] "w")))) in
          do:  "addr" <-[uint64T] "$a0";;;
          let: "args" := ref_zero (struct.t chunk.WriteChunkArgs) in
          let: "$a0" := struct.mk chunk.WriteChunkArgs [
            "WriteId" ::= struct.loadF Writer "writeId" (![ptrT] "w");
            "Chunk" ::= ![slice.T byteT] "data";
            "Index" ::= ![uint64T] "index"
          ] in
          do:  "args" <-[struct.t chunk.WriteChunkArgs] "$a0";;;
          do:  chunk.ClerkPool__WriteChunk (struct.loadF Clerk "chCk" (struct.loadF Writer "ck" (![ptrT] "w"))) (![uint64T] "addr") (![struct.t chunk.WriteChunkArgs] "args");;;
          do:  sync.WaitGroup__Done (struct.loadF Writer "wg" (![ptrT] "w"));;;
          do:  #());;;
    do:  #().

Definition Writer__Done: val :=
  rec: "Writer__Done" "w" :=
    let: "w" := ref_to ptrT "w" in
    do:  sync.WaitGroup__Wait (struct.loadF Writer "wg" (![ptrT] "w"));;;
    do:  dir.Clerk__FinishWrite (struct.loadF Clerk "dCk" (struct.loadF Writer "ck" (![ptrT] "w"))) (struct.mk dir.FinishWriteArgs [
      "WriteId" ::= struct.loadF Writer "writeId" (![ptrT] "w");
      "Keyname" ::= struct.loadF Writer "keyname" (![ptrT] "w")
    ]);;;
    do:  #().

Definition Reader := struct.decl [
  "chunkHandles" :: slice.T (struct.t dir.ChunkHandle);
  "index" :: uint64T;
  "ck" :: ptrT
].

Definition Clerk__PrepareRead: val :=
  rec: "Clerk__PrepareRead" "ck" "keyname" :=
    let: "keyname" := ref_to stringT "keyname" in
    let: "ck" := ref_to ptrT "ck" in
    return: (struct.new Reader [
       "chunkHandles" ::= struct.get dir.PreparedRead "Handles" (dir.Clerk__PrepareRead (struct.loadF Clerk "dCk" (![ptrT] "ck")) (![stringT] "keyname"));
       "index" ::= #0
     ]);;;
    do:  #().

Definition Reader__GetNextChunk: val :=
  rec: "Reader__GetNextChunk" "r" :=
    let: "r" := ref_to ptrT "r" in
    (if: (struct.loadF Reader "index" (![ptrT] "r")) ≥ (slice.len (struct.loadF Reader "chunkHandles" (![ptrT] "r")))
    then
      return: (#false, slice.nil);;;
      do:  #()
    else #());;;
    let: "handle" := ref_zero (struct.t dir.ChunkHandle) in
    let: "$a0" := SliceGet (struct.t dir.ChunkHandle) (struct.loadF Reader "chunkHandles" (![ptrT] "r")) (struct.loadF Reader "index" (![ptrT] "r")) in
    do:  "handle" <-[struct.t dir.ChunkHandle] "$a0";;;
    do:  struct.storeF Reader "index" (![ptrT] "r") ((struct.loadF Reader "index" (![ptrT] "r")) + #1);;;
    return: (#true, chunk.ClerkPool__GetChunk (struct.loadF Clerk "chCk" (struct.loadF Reader "ck" (![ptrT] "r"))) (struct.get dir.ChunkHandle "Addr" (![struct.t dir.ChunkHandle] "handle")) (struct.get dir.ChunkHandle "ContentHash" (![struct.t dir.ChunkHandle] "handle")));;;
    do:  #().
