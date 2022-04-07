(* autogenerated from github.com/mit-pdos/gokv/pb/controller *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.gokv.pb.
From Goose Require github_com.mit_pdos.gokv.urpc.
From Goose Require github_com.tchajed.marshal.

From Perennial.goose_lang Require Import ffi.grove_prelude.

(* clerk.go *)

Definition CONTROLLER_ADD : expr := #0.

Definition ControllerClerk := struct.decl [
  "cl" :: ptrT
].

Definition ControllerClerk__AddNewServer: val :=
  rec: "ControllerClerk__AddNewServer" "ck" "newServer" :=
    let: "enc" := marshal.NewEnc #8 in
    marshal.Enc__PutInt "enc" "newServer";;
    let: "raw_args" := marshal.Enc__Finish "enc" in
    let: "reply" := ref (zero_val (slice.T byteT)) in
    urpc.Client__Call (struct.loadF ControllerClerk "cl" "ck") CONTROLLER_ADD "raw_args" "reply" #100;;
    #().

Definition MakeControllerClerk: val :=
  rec: "MakeControllerClerk" "host" :=
    let: "ck" := struct.alloc ControllerClerk (zero_val (struct.t ControllerClerk)) in
    struct.storeF ControllerClerk "cl" "ck" (urpc.MakeClient "host");;
    "ck".

(* controller.go *)

Definition ControllerServer := struct.decl [
  "mu" :: ptrT;
  "cn" :: uint64T;
  "conf" :: ptrT;
  "hbtimers" :: slice.T ptrT;
  "failed" :: mapT boolT
].

Definition ControllerServer__HandleFailedReplicas: val :=
  rec: "ControllerServer__HandleFailedReplicas" "s" :=
    (* log.Printf("In config %d, %+v failed", s.cn, s.failed) *)
    let: "n" := slice.len (struct.loadF pb.Configuration "Replicas" (struct.loadF ControllerServer "conf" "s")) - MapLen (struct.loadF ControllerServer "failed" "s") in
    let: "newReplicas" := ref_to (slice.T uint64T) (NewSliceWithCap uint64T #0 "n") in
    ForSlice uint64T "i" "r" (struct.loadF pb.Configuration "Replicas" (struct.loadF ControllerServer "conf" "s"))
      (if: ~ (Fst (MapGet (struct.loadF ControllerServer "failed" "s") "i"))
      then "newReplicas" <-[slice.T uint64T] SliceAppend uint64T (![slice.T uint64T] "newReplicas") "r"
      else #());;
    struct.storeF ControllerServer "conf" "s" (struct.new pb.Configuration [
      "Replicas" ::= ![slice.T uint64T] "newReplicas"
    ]);;
    struct.storeF ControllerServer "cn" "s" (struct.loadF ControllerServer "cn" "s" + #1);;
    let: "ck" := pb.MakeReplicaClerk (SliceGet uint64T (![slice.T uint64T] "newReplicas") #0) in
    pb.ReplicaClerk__BecomePrimaryRPC "ck" (struct.new pb.BecomePrimaryArgs [
      "Cn" ::= struct.loadF ControllerServer "cn" "s";
      "Conf" ::= struct.loadF ControllerServer "conf" "s"
    ]);;
    #().

Definition ControllerServer__HeartbeatThread: val :=
  rec: "ControllerServer__HeartbeatThread" "s" :=
    let: "HBTIMEOUT" := #2 * time.Second in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      lock.acquire (struct.loadF ControllerServer "mu" "s");;
      let: "conf" := struct.loadF ControllerServer "conf" "s" in
      let: "cn" := struct.loadF ControllerServer "cn" "s" in
      lock.release (struct.loadF ControllerServer "mu" "s");;
      let: "hbtimers" := NewSlice ptrT (slice.len (struct.loadF pb.Configuration "Replicas" "conf")) in
      let: "clerks" := NewSlice ptrT (slice.len (struct.loadF pb.Configuration "Replicas" "conf")) in
      ForSlice uint64T "i" "r" (struct.loadF pb.Configuration "Replicas" "conf")
        (SliceSet ptrT "clerks" "i" (pb.MakeReplicaClerk "r"));;
      struct.storeF ControllerServer "failed" "s" (NewMap boolT #());;
      ForSlice ptrT "i" <> "clerks"
        (let: "i" := "i" in
        SliceSet ptrT "hbtimers" "i" (time.AfterFunc "HBTIMEOUT" (λ: <>,
          lock.acquire (struct.loadF ControllerServer "mu" "s");;
          (if: (struct.loadF ControllerServer "cn" "s" = "cn")
          then MapInsert (struct.loadF ControllerServer "failed" "s") "i" #true
          else #());;
          lock.release (struct.loadF ControllerServer "mu" "s");;
          #()
          )));;
      Skip;;
      (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
        lock.acquire (struct.loadF ControllerServer "mu" "s");;
        (if: struct.loadF ControllerServer "cn" "s" > "cn"
        then
          lock.release (struct.loadF ControllerServer "mu" "s");;
          Break
        else
          (if: MapLen (struct.loadF ControllerServer "failed" "s") > #0
          then
            ControllerServer__HandleFailedReplicas "s";;
            lock.release (struct.loadF ControllerServer "mu" "s");;
            Break
          else
            lock.release (struct.loadF ControllerServer "mu" "s");;
            ForSlice ptrT "i" "ck" "clerks"
              (let: "i" := "i" in
              let: "ck" := "ck" in
              Fork ((if: pb.ReplicaClerk__HeartbeatRPC "ck"
                    then time.Timer__Reset (SliceGet ptrT "hbtimers" "i") "HBTIMEOUT"
                    else #())));;
            time.Sleep (#500 * time.Millisecond);;
            Continue)));;
      Continue);;
    #().

Definition ControllerServer__AddNewServerRPC: val :=
  rec: "ControllerServer__AddNewServerRPC" "s" "newServer" :=
    lock.acquire (struct.loadF ControllerServer "mu" "s");;
    struct.storeF ControllerServer "cn" "s" (struct.loadF ControllerServer "cn" "s" + #1);;
    struct.storeF ControllerServer "conf" "s" (struct.new pb.Configuration [
      "Replicas" ::= SliceAppend uint64T (struct.loadF pb.Configuration "Replicas" (struct.loadF ControllerServer "conf" "s")) "newServer"
    ]);;
    let: "ck" := pb.MakeReplicaClerk (SliceGet uint64T (struct.loadF pb.Configuration "Replicas" (struct.loadF ControllerServer "conf" "s")) #0) in
    pb.ReplicaClerk__BecomePrimaryRPC "ck" (struct.new pb.BecomePrimaryArgs [
      "Cn" ::= struct.loadF ControllerServer "cn" "s";
      "Conf" ::= struct.loadF ControllerServer "conf" "s"
    ]);;
    lock.release (struct.loadF ControllerServer "mu" "s");;
    #().

(* This should be invoked locally by services to attempt appending op to the
   log *)
Definition StartControllerServer: val :=
  rec: "StartControllerServer" "me" "replicas" :=
    let: "s" := struct.alloc ControllerServer (zero_val (struct.t ControllerServer)) in
    struct.storeF ControllerServer "mu" "s" (lock.new #());;
    struct.storeF ControllerServer "cn" "s" #1;;
    struct.storeF ControllerServer "conf" "s" (struct.new pb.Configuration [
      "Replicas" ::= "replicas"
    ]);;
    let: "ck" := pb.MakeReplicaClerk (SliceGet uint64T "replicas" #0) in
    pb.ReplicaClerk__BecomePrimaryRPC "ck" (struct.new pb.BecomePrimaryArgs [
      "Cn" ::= #1;
      "Conf" ::= struct.loadF ControllerServer "conf" "s"
    ]);;
    Fork (ControllerServer__HeartbeatThread "s");;
    let: "handlers" := NewMap ((slice.T byteT -> ptrT -> unitT)%ht) #() in
    MapInsert "handlers" CONTROLLER_ADD (λ: "raw_args" <>,
      let: "dec" := marshal.NewDec "raw_args" in
      let: "newServer" := marshal.Dec__GetInt "dec" in
      ControllerServer__AddNewServerRPC "s" "newServer";;
      #()
      );;
    let: "r" := urpc.MakeServer "handlers" in
    urpc.Server__Serve "r" "me";;
    #().
