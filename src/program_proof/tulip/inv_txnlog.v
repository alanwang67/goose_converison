From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.tulip Require Import base res cmd msg encode.
From Perennial.program_proof.tulip.paxos Require Import base res.

Definition encode_commit_cmd_xkind (ts : nat) (m : dbmap) (data : list u8) :=
  ∃ mdata, data = u64_le (W64 ts) ++ mdata ∧ encode_dbmap m mdata.

Definition encode_commit_cmd (ts : nat) (m : dbmap) (data : list u8) :=
  ∃ cmddata,
    data = u64_le (U64 1) ++ cmddata ∧
    encode_commit_cmd_xkind ts m cmddata.

Definition encode_abort_cmd (ts : nat) (data : list u8) :=
  data = u64_le (U64 0) ++ u64_le (W64 ts).

Definition encode_ccommand (ccmd : ccommand) (s : string) :=
  match ccmd with
  | CmdCommit ts pwrs => encode_commit_cmd ts pwrs (string_to_bytes s)
  | CmdAbort ts => encode_abort_cmd ts (string_to_bytes s)
  end.

Section inv_txnlog.
  Context `{!heapGS Σ, !tulip_ghostG Σ, !paxos_ghostG Σ}.

  Definition tulip_txnlog_inv γ π (gid : u64) : iProp Σ :=
    ∃ tlog tcpool plog pcpool,
      "Htlog"      ∷ own_txn_log_half γ gid tlog ∗
      "Htcpool"    ∷ own_txn_cpool_half γ gid tcpool ∗
      "Hplog"      ∷ own_log_half π plog ∗
      "Hpcpool"    ∷ own_cpool_half π pcpool ∗
      "%Hlogabs"   ∷ ⌜Forall2 (λ tc pc, encode_ccommand tc pc) tlog plog⌝ ∗
      "%Hcpoolabs" ∷ ⌜set_Forall (λ pc, ∃ tc, tc ∈ tcpool ∧ encode_ccommand tc pc) pcpool⌝.

  #[global]
  Instance tulip_txnlog_inv_timeless γ π gid :
    Timeless (tulip_txnlog_inv γ π gid).
  Admitted.

  Definition know_tulip_txnlog_inv γ π gid : iProp Σ :=
    inv txnlogNS (tulip_txnlog_inv γ π gid).

End inv_txnlog.
