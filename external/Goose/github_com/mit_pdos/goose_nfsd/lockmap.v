(* autogenerated from github.com/mit-pdos/goose-nfsd/lockmap *)
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

Module lockState.
  Definition S := struct.decl [
    "held" :: boolT;
    "cond" :: condvarRefT;
    "waiters" :: uint64T
  ].
End lockState.

Module lockShard.
  Definition S := struct.decl [
    "mu" :: lockRefT;
    "state" :: mapT (struct.ptrT lockState.S)
  ].
End lockShard.

Definition mkLockShard: val :=
  rec: "mkLockShard" <> :=
    let: "state" := NewMap (struct.ptrT lockState.S) in
    let: "mu" := lock.new #() in
    let: "a" := struct.new lockShard.S [
      "mu" ::= "mu";
      "state" ::= "state"
    ] in
    "a".

Definition lockShard__acquire: val :=
  rec: "lockShard__acquire" "lmap" "addr" :=
    lock.acquire (struct.loadF lockShard.S "mu" "lmap");;
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "state" := ref (zero_val (refT (struct.t lockState.S))) in
      let: ("state1", "ok1") := MapGet (struct.loadF lockShard.S "state" "lmap") "addr" in
      (if: "ok1"
      then "state" <-[refT (struct.t lockState.S)] "state1"
      else
        "state" <-[refT (struct.t lockState.S)] struct.new lockState.S [
          "held" ::= #false;
          "cond" ::= lock.newCond (struct.loadF lockShard.S "mu" "lmap");
          "waiters" ::= #0
        ];;
        MapInsert (struct.loadF lockShard.S "state" "lmap") "addr" (![refT (struct.t lockState.S)] "state"));;
      let: "acquired" := ref (zero_val boolT) in
      (if: ~ (struct.loadF lockState.S "held" (![refT (struct.t lockState.S)] "state"))
      then
        struct.storeF lockState.S "held" (![refT (struct.t lockState.S)] "state") #true;;
        "acquired" <-[boolT] #true
      else
        struct.storeF lockState.S "waiters" (![refT (struct.t lockState.S)] "state") (struct.loadF lockState.S "waiters" (![refT (struct.t lockState.S)] "state") + #1);;
        lock.condWait (struct.loadF lockState.S "cond" (![refT (struct.t lockState.S)] "state"));;
        let: ("state2", "ok2") := MapGet (struct.loadF lockShard.S "state" "lmap") "addr" in
        (if: "ok2"
        then struct.storeF lockState.S "waiters" "state2" (struct.loadF lockState.S "waiters" "state2" - #1)
        else #()));;
      (if: ![boolT] "acquired"
      then Break
      else Continue));;
    lock.release (struct.loadF lockShard.S "mu" "lmap").

Definition lockShard__release: val :=
  rec: "lockShard__release" "lmap" "addr" :=
    lock.acquire (struct.loadF lockShard.S "mu" "lmap");;
    let: "state" := Fst (MapGet (struct.loadF lockShard.S "state" "lmap") "addr") in
    struct.storeF lockState.S "held" "state" #false;;
    (if: struct.loadF lockState.S "waiters" "state" > #0
    then lock.condSignal (struct.loadF lockState.S "cond" "state")
    else MapDelete (struct.loadF lockShard.S "state" "lmap") "addr");;
    lock.release (struct.loadF lockShard.S "mu" "lmap").

Definition NSHARD : expr := #43.

Module LockMap.
  Definition S := struct.decl [
    "shards" :: slice.T (struct.ptrT lockShard.S)
  ].
End LockMap.

Definition MkLockMap: val :=
  rec: "MkLockMap" <> :=
    let: "shards" := ref (zero_val (slice.T (refT (struct.t lockShard.S)))) in
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, ![uint64T] "i" < NSHARD); (λ: <>, "i" <-[uint64T] ![uint64T] "i" + #1) := λ: <>,
      "shards" <-[slice.T (refT (struct.t lockShard.S))] SliceAppend (refT (struct.t lockShard.S)) (![slice.T (refT (struct.t lockShard.S))] "shards") (mkLockShard #());;
      Continue);;
    let: "a" := struct.new LockMap.S [
      "shards" ::= ![slice.T (refT (struct.t lockShard.S))] "shards"
    ] in
    "a".

Definition LockMap__Acquire: val :=
  rec: "LockMap__Acquire" "lmap" "flataddr" :=
    let: "shard" := SliceGet (refT (struct.t lockShard.S)) (struct.loadF LockMap.S "shards" "lmap") ("flataddr" `rem` NSHARD) in
    lockShard__acquire "shard" "flataddr".

Definition LockMap__Release: val :=
  rec: "LockMap__Release" "lmap" "flataddr" :=
    let: "shard" := SliceGet (refT (struct.t lockShard.S)) (struct.loadF LockMap.S "shards" "lmap") ("flataddr" `rem` NSHARD) in
    lockShard__release "shard" "flataddr".
