(* autogenerated from github.com/mit-pdos/gokv/aof *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.goose_lang.std.
From Goose Require github_com.tchajed.marshal.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition AppendOnlyFile := struct.decl [
  "mu" :: ptrT;
  "durableCond" :: ptrT;
  "lengthCond" :: ptrT;
  "membuf" :: slice.T byteT;
  "length" :: uint64T;
  "durableLength" :: uint64T;
  "closeRequested" :: boolT;
  "closed" :: boolT;
  "closedCond" :: ptrT
].

Definition CreateAppendOnlyFile: val :=
  rec: "CreateAppendOnlyFile" "fname" :=
    let: "a" := struct.alloc AppendOnlyFile (zero_val (struct.t AppendOnlyFile)) in
    struct.storeF AppendOnlyFile "mu" "a" (lock.new #());;
    struct.storeF AppendOnlyFile "lengthCond" "a" (lock.newCond (struct.loadF AppendOnlyFile "mu" "a"));;
    struct.storeF AppendOnlyFile "durableCond" "a" (lock.newCond (struct.loadF AppendOnlyFile "mu" "a"));;
    struct.storeF AppendOnlyFile "closedCond" "a" (lock.newCond (struct.loadF AppendOnlyFile "mu" "a"));;
    Fork (lock.acquire (struct.loadF AppendOnlyFile "mu" "a");;
          Skip;;
          (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
            (if: ((slice.len (struct.loadF AppendOnlyFile "membuf" "a") = #0)) && (~ (struct.loadF AppendOnlyFile "closeRequested" "a"))
            then
              lock.condWait (struct.loadF AppendOnlyFile "lengthCond" "a");;
              Continue
            else
              (if: struct.loadF AppendOnlyFile "closeRequested" "a"
              then
                grove_ffi.FileAppend "fname" (struct.loadF AppendOnlyFile "membuf" "a");;
                struct.storeF AppendOnlyFile "membuf" "a" (NewSlice byteT #0);;
                struct.storeF AppendOnlyFile "durableLength" "a" (struct.loadF AppendOnlyFile "length" "a");;
                lock.condBroadcast (struct.loadF AppendOnlyFile "durableCond" "a");;
                struct.storeF AppendOnlyFile "closed" "a" #true;;
                lock.condBroadcast (struct.loadF AppendOnlyFile "closedCond" "a");;
                lock.release (struct.loadF AppendOnlyFile "mu" "a");;
                Break
              else
                let: "l" := struct.loadF AppendOnlyFile "membuf" "a" in
                let: "newLength" := struct.loadF AppendOnlyFile "length" "a" in
                struct.storeF AppendOnlyFile "membuf" "a" (NewSlice byteT #0);;
                let: "cond" := struct.loadF AppendOnlyFile "durableCond" "a" in
                struct.storeF AppendOnlyFile "durableCond" "a" (lock.newCond (struct.loadF AppendOnlyFile "mu" "a"));;
                lock.release (struct.loadF AppendOnlyFile "mu" "a");;
                grove_ffi.FileAppend "fname" "l";;
                lock.acquire (struct.loadF AppendOnlyFile "mu" "a");;
                struct.storeF AppendOnlyFile "durableLength" "a" "newLength";;
                lock.condBroadcast "cond";;
                Continue))));;
    "a".

(* NOTE: cannot be called concurrently with Append() *)
Definition AppendOnlyFile__Close: val :=
  rec: "AppendOnlyFile__Close" "a" :=
    lock.acquire (struct.loadF AppendOnlyFile "mu" "a");;
    struct.storeF AppendOnlyFile "closeRequested" "a" #true;;
    lock.condSignal (struct.loadF AppendOnlyFile "lengthCond" "a");;
    Skip;;
    (for: (λ: <>, ~ (struct.loadF AppendOnlyFile "closed" "a")); (λ: <>, Skip) := λ: <>,
      lock.condWait (struct.loadF AppendOnlyFile "closedCond" "a");;
      Continue);;
    lock.release (struct.loadF AppendOnlyFile "mu" "a");;
    #().

(* NOTE: cannot be called concurrently with Close() *)
Definition AppendOnlyFile__Append: val :=
  rec: "AppendOnlyFile__Append" "a" "data" :=
    lock.acquire (struct.loadF AppendOnlyFile "mu" "a");;
    struct.storeF AppendOnlyFile "membuf" "a" (marshal.WriteBytes (struct.loadF AppendOnlyFile "membuf" "a") "data");;
    struct.storeF AppendOnlyFile "length" "a" (std.SumAssumeNoOverflow (struct.loadF AppendOnlyFile "length" "a") (slice.len "data"));;
    let: "r" := struct.loadF AppendOnlyFile "length" "a" in
    lock.condSignal (struct.loadF AppendOnlyFile "lengthCond" "a");;
    lock.release (struct.loadF AppendOnlyFile "mu" "a");;
    "r".

Definition AppendOnlyFile__WaitAppend: val :=
  rec: "AppendOnlyFile__WaitAppend" "a" "length" :=
    lock.acquire (struct.loadF AppendOnlyFile "mu" "a");;
    Skip;;
    (for: (λ: <>, struct.loadF AppendOnlyFile "durableLength" "a" < "length"); (λ: <>, Skip) := λ: <>,
      lock.condWait (struct.loadF AppendOnlyFile "durableCond" "a");;
      Continue);;
    lock.release (struct.loadF AppendOnlyFile "mu" "a");;
    #().
