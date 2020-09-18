(* autogenerated from github.com/mit-pdos/goose-nfsd/common *)
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

(* on-disk size *)
Definition INODESZ : expr := #128.

Definition NBITBLOCK : expr := disk.BlockSize * #8.

Definition INODEBLK : expr := disk.BlockSize `quot` INODESZ.

Definition NINODEBITMAP : expr := #1.

(* space for the end position *)
Definition HDRMETA : expr := #8.

Definition HDRADDRS : expr := (disk.BlockSize - HDRMETA) `quot` #8.

(* 2 for log header *)
Definition LOGSIZE : expr := HDRADDRS + #2.

Definition Inum: ty := uint64T.

Definition Bnum: ty := uint64T.

Definition NULLINUM : expr := #0.

Definition ROOTINUM : expr := #1.

Definition NULLBNUM : expr := #0.
