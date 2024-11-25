(* autogenerated from github.com/mit-pdos/tulip/tuple *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.tulip.tulip.

Section code.
Context `{ext_ty: ext_types}.

Definition Tuple := struct.decl [
  "mu" :: ptrT;
  "tssafe" :: uint64T;
  "vers" :: slice.T (struct.t tulip.Version)
].

(* @findVersion starts from the end of @vers and return the first version whose
   timestamp is less than or equal to @ts, and whether the returned version is
   the latest one. If the returned version is the latest one, the postcondition
   should say something about the length of the history. *)
Definition findVersion: val :=
  rec: "findVersion" "ts" "vers" :=
    let: "ver" := ref (zero_val (struct.t tulip.Version)) in
    let: "length" := slice.len "vers" in
    let: "idx" := ref_to uint64T #0 in
    Skip;;
    (for: (λ: <>, (![uint64T] "idx") < "length"); (λ: <>, Skip) := λ: <>,
      "ver" <-[struct.t tulip.Version] (SliceGet (struct.t tulip.Version) "vers" (("length" - (![uint64T] "idx")) - #1));;
      (if: (struct.get tulip.Version "Timestamp" (![struct.t tulip.Version] "ver")) ≤ "ts"
      then Break
      else
        "idx" <-[uint64T] ((![uint64T] "idx") + #1);;
        Continue));;
    (![struct.t tulip.Version] "ver", ((![uint64T] "idx") = #0) && ("ts" ≠ (struct.get tulip.Version "Timestamp" (![struct.t tulip.Version] "ver")))).

(* Arguments:
   @ts: Index at which lookup of the abstract history is performed.

   Return values:
   @ver: If @ver.Timestamp = 0, then this is a fast-path read---the value at @ts
   has been determined to be @ver.Value. Otherwise, this is a slow-path read,
   the replica promises not to accept prepare requests from transactions that
   modifies this tuple and whose timestamp lies within @ver.Timestamp and @ts.

   @ok: @ver is meaningful iff @ok is true. *)
Definition Tuple__ReadVersion: val :=
  rec: "Tuple__ReadVersion" "tuple" "ts" :=
    Mutex__Lock (struct.loadF Tuple "mu" "tuple");;
    let: ("ver", "slow") := findVersion ("ts" - #1) (struct.loadF Tuple "vers" "tuple") in
    Mutex__Unlock (struct.loadF Tuple "mu" "tuple");;
    ("ver", "slow").

Definition Tuple__AppendVersion: val :=
  rec: "Tuple__AppendVersion" "tuple" "ts" "value" :=
    Mutex__Lock (struct.loadF Tuple "mu" "tuple");;
    let: "ver" := struct.mk tulip.Version [
      "Timestamp" ::= "ts";
      "Value" ::= struct.mk tulip.Value [
        "Present" ::= #true;
        "Content" ::= "value"
      ]
    ] in
    struct.storeF Tuple "vers" "tuple" (SliceAppend (struct.t tulip.Version) (struct.loadF Tuple "vers" "tuple") "ver");;
    Mutex__Unlock (struct.loadF Tuple "mu" "tuple");;
    #().

Definition Tuple__KillVersion: val :=
  rec: "Tuple__KillVersion" "tuple" "ts" :=
    Mutex__Lock (struct.loadF Tuple "mu" "tuple");;
    let: "ver" := struct.mk tulip.Version [
      "Timestamp" ::= "ts";
      "Value" ::= struct.mk tulip.Value [
        "Present" ::= #false
      ]
    ] in
    struct.storeF Tuple "vers" "tuple" (SliceAppend (struct.t tulip.Version) (struct.loadF Tuple "vers" "tuple") "ver");;
    Mutex__Unlock (struct.loadF Tuple "mu" "tuple");;
    #().

Definition MkTuple: val :=
  rec: "MkTuple" <> :=
    let: "tuple" := struct.alloc Tuple (zero_val (struct.t Tuple)) in
    struct.storeF Tuple "mu" "tuple" (newMutex #());;
    let: "vers" := NewSliceWithCap (struct.t tulip.Version) #1 #1 in
    SliceSet (struct.t tulip.Version) "vers" #0 (struct.mk tulip.Version [
      "Timestamp" ::= #0;
      "Value" ::= struct.mk tulip.Value [
        "Present" ::= #false
      ]
    ]);;
    struct.storeF Tuple "vers" "tuple" "vers";;
    "tuple".

End code.
