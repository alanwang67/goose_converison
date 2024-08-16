From Perennial.goose_lang Require Import lang.
From Perennial.goose_lang Require Export ffi.async_disk_proph.
#[global]
Existing Instances async_disk_syntax.disk_op async_disk_proph.disk_model async_disk_syntax.disk_ty.
#[global]
Existing Instances async_disk_proph.disk_semantics async_disk_proph.disk_interp.
#[global]
Existing Instance goose_diskGS.
(* Now that the TC parameter is fixed, we can make this a coercion. *)
Coercion Var' (s: string) := Var s.


Module disk.
  Notation Disk := async_disk_syntax.Disk.
  Notation Write := async_disk_proph.Write.
  Notation Read := async_disk_proph.Read.
  Notation ReadTo := async_disk_proph.ReadTo.
  Notation Barrier := async_disk_proph.Barrier.
  Notation Size := async_disk_proph.Size.
End disk.

Module async_disk.
  Notation BlockSize := async_disk_syntax.BlockSize.
  Notation Write := async_disk_proph.Write.
  Notation Read := async_disk_proph.Read.
  Notation ReadTo := async_disk_proph.ReadTo.
  Notation Barrier := async_disk_proph.Barrier.
  Notation Size := async_disk_proph.Size.
End async_disk.
