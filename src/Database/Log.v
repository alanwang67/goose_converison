From RecoveryRefinement Require Import Database.Base.
From RecoveryRefinement Require Import Database.BinaryEncoding.

Module Log.
  Import ProcNotations.
  Local Open Scope proc.

  Definition t := Fd.

  Definition addTxn (l:t) (txn: ByteString) : proc _ :=
      let bs := encode (array64 txn) in
      lift (FS.append l bs).

  Definition clear (p:string) : proc _ :=
      lift (FS.truncate p).

  Definition create (p:string) : proc t :=
    fd <- lift (FS.create p);
      Ret fd.

  (* TODO: injection type inference does the wrong thing here, need to debug
  it *)
  Definition recoverTxns (p:string) : proc (Array ByteString) :=
    fd <- lift (FS.open p);
      txns <- Call (inject (Data.NewArray ByteString));
      sz <- lift (FS.size fd);
      log <- lift (FS.readAt fd 0 sz);
      _ <- Loop
        (fun log => match decode Array64 log with
                 | Some (txn, n) =>
                   _ <- Data.arrayAppend txns (getBytes txn);
                     Continue (BS.drop n log)
                 | None => LoopRet tt
                 end) log;
      Ret txns.
End Log.
