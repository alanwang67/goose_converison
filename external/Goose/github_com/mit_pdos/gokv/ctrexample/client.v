(* autogenerated from github.com/mit-pdos/gokv/ctrexample/client *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.mit_pdos.gokv.urpc.
From Goose Require github_com.tchajed.marshal.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition FAI_OP : expr := #0.

(* the boot/main() function for the server *)
Definition main: val :=
  rec: "main" <> :=
    let: "cl" := urpc.MakeClient #53021371269120 in
    let: "localBound" := ref_to uint64T #0 in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "rep" := ref (zero_val (slice.T byteT)) in
      let: "err" := urpc.Client__Call "cl" FAI_OP (NewSlice byteT #0) "rep" #100 in
      (if: "err" ≠ #0
      then Continue
      else
        let: "dec" := marshal.NewDec (![slice.T byteT] "rep") in
        let: "v" := marshal.Dec__GetInt "dec" in
        control.impl.Assert ("v" ≥ (![uint64T] "localBound"));;
        "localBound" <-[uint64T] "v";;
        (* fmt.Println("One") *)
        Continue));;
    #().
