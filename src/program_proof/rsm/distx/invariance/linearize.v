From Perennial.program_proof.rsm.distx Require Import prelude.

Lemma conflict_past_inv_linearize {past future tmodas} ts form :
  conflict_cases past future ts form ->
  conflict_past past future tmodas ->
  conflict_past past future (<[ts := form]> tmodas).
Proof. intros Hc Hcp. by apply map_Forall_insert_2. Qed.

Lemma ext_by_lnrz_inv_linearize_abort ts cmtd lnrz kmodl :
  ext_by_lnrz cmtd lnrz kmodl ->
  ext_by_lnrz cmtd (last_extend ts lnrz) kmodl.
Proof.
  intros Hext.
  destruct Hext as (vlast & Hprefix & Hlast & Hlen & Hext).
  exists vlast.
  split.
  { (* Re-establish prefix. *)
    trans lnrz; [apply Hprefix | apply last_extend_prefix].
  }
  split.
  { (* Re-establish last. *)
    done.
  }
  split.
  { (* Re-establish len. *)
    intros n Hn.
    specialize (Hlen _ Hn). simpl in Hlen.
    pose proof (last_extend_length_ge ts lnrz) as Hlenext.
    lia.
  }
  (* Re-establish ext. *)
  intros t u Ht Hu.
  destruct (decide (t < length lnrz)%nat) as [Hlt | Hge].
  { (* Case: before extension [t < length lnrz]. *)
    rewrite /last_extend /extend in Hu.
    destruct (last lnrz) as [x |]; last done.
    rewrite lookup_app_l in Hu; last done.
    by apply Hext.
  }
  (* Case: read-extension [length lnrz ≤ t]. *)
  rewrite Nat.nlt_ge in Hge.
  apply lookup_lt_Some in Hu as Htlen.
  rewrite lookup_last_extend_r in Hu; last first.
  { pose proof (last_extend_length_eq_n_or_same ts lnrz). lia. }
  { lia. }
  rewrite (prev_dbval_ge (pred (length lnrz)) t); last first.
  { intros x Hx. specialize (Hlen _ Hx). simpl in Hlen. lia. }
  { lia. }
  apply Hext; last by rewrite -last_lookup.
  apply Nat.lt_le_pred.
  assert (Hlenc : length cmtd ≠ O); first by destruct cmtd.
  apply prefix_length in Hprefix.
  lia.
Qed.

Lemma ext_by_lnrz_inv_linearize_commit ts v cmtd lnrz kmodl :
  (length lnrz ≤ ts)%nat ->
  ext_by_lnrz cmtd lnrz kmodl ->
  ext_by_lnrz cmtd (last_extend ts lnrz ++ [v]) (<[ts := v]> kmodl).
Proof.
  intros Hts Hext.
  destruct Hext as (vlast & Hprefix & Hlast & Hlen & Hext).
  exists vlast.
  split.
  { (* Re-establish prefix. *)
    trans lnrz; [apply Hprefix | apply prefix_app_r, last_extend_prefix].
  }
  split.
  { (* Re-establish last. *)
    done.
  }
  split.
  { (* Re-establish len. *)
    intros n Hn.
    rewrite length_app /=.
    rewrite dom_insert_L elem_of_union in Hn.
    rewrite last_extend_length; last first.
    { apply (prefix_not_nil _ _ Hprefix). set_solver. }
    destruct Hn as [Hn | Hn]; last first.
    { specialize (Hlen _ Hn). simpl in Hlen. lia. }
    rewrite elem_of_singleton in Hn. subst n.
    apply prefix_length in Hprefix.
    lia.
  }
  (* Re-establish ext. *)
  intros t u Ht Hu.
  (* Obtain [length (last_extend ts lnrz) = ts]. *)
  unshelve epose proof (last_extend_length_eq_n ts lnrz _ _) as Hlenext; [| apply Hts |].
  { apply (prefix_not_nil _ _ Hprefix).
    set_solver.
  }
  destruct (decide (t < ts)%nat) as [Hlt | Hge].
  { (* Case: before write-extension [t < ts]. *)
    rewrite prev_dbval_insert; last first.
    { intros n Hn.
      specialize (Hlen _ Hn). simpl in Hlen.
      (* solved by [Hlen] and [Hts] *)
      lia.
    }
    { (* solved by [Hlt] and [Hts] *) lia. }
    destruct (decide (t < length lnrz)%nat) as [Hltstrong | Hge].
    { (* Case: before extension [t < length lnrz]. *)
      rewrite /last_extend /extend in Hu.
      destruct (last lnrz) as [x |] eqn:Hx; last first.
      { rewrite last_None in Hx. subst lnrz. apply prefix_nil_inv in Hprefix. set_solver. }
      rewrite -app_assoc lookup_app_l in Hu; last done.
      by apply Hext.
    }
    (* Case: read-extension [length lnrz ≤ t < ts]. *)
    rewrite Nat.nlt_ge in Hge.
    (* Obtain [last lnrz = Some u]. *)
    rewrite lookup_app_l in Hu; last lia.
    rewrite lookup_last_extend_r in Hu; [| lia | done].
    (* Extend [prev_dbval] to hold on [t] using [last lnrz] as the anchor. *)
    rewrite (prev_dbval_ge (pred (length lnrz)) t); last first.
    { intros x Hx. specialize (Hlen _ Hx). simpl in Hlen. lia. }
    { lia. }
    apply Hext; last by rewrite -last_lookup.
    apply Nat.lt_le_pred.
    assert (Hlenc : length cmtd ≠ O); first by destruct cmtd.
    apply prefix_length in Hprefix.
    lia.
  }
  (* Case: write-extension [t = ts]. *)
  rewrite Nat.nlt_ge in Hge.
  rewrite lookup_snoc_Some in Hu.
  destruct Hu as [? | [Htts Hvu]]; first lia.
  rewrite Hlenext in Htts.
  erewrite prev_dbval_lookup; first apply Hvu.
  by rewrite Htts lookup_insert.
Qed.

Section inv.
  Context `{!distx_ghostG Σ}.

  Definition key_inv_linearizable_after γ (key : dbkey) (ts : nat) : iProp Σ :=
    ∃ tslb, key_inv_with_tslb γ key tslb ∗ ⌜(tslb ≤ ts)%nat⌝.

  Definition key_inv_no_kmodl_linearizable_after
    γ (key : dbkey) (kmodl : dbkmod) (ts : nat) : iProp Σ :=
    ∃ tslb, key_inv_with_tslb_no_kmodl γ key tslb kmodl ∗ ⌜(tslb ≤ ts)%nat⌝.

  Lemma keys_inv_before_linearize γ ts keys :
    ([∗ set] key ∈ keys, key_inv γ key) -∗
    ts_auth γ ts -∗
    ([∗ set] key ∈ keys, key_inv_linearizable_after γ key ts) ∗
    ts_auth γ ts.
  Proof.
    iIntros "Hkeys Hts".
    iApply (big_sepS_impl_res with "Hkeys Hts").
    iIntros (k Hk) "!> Hkey Hts".
    iNamed "Hkey".
    iDestruct (ts_le with "Htslb Hts") as %Hle.
    iFrame "∗ # %".
  Qed.

  Lemma keys_inv_after_linearize γ ts keys :
    ([∗ set] key ∈ keys, key_inv_linearizable_after γ key ts) -∗
    ([∗ set] key ∈ keys, key_inv γ key).
  Proof.
    iIntros "Hkeys".
    iApply (big_sepS_mono with "Hkeys").
    iIntros (k Hk) "Hkey".
    iDestruct "Hkey" as (tslb) "[Hkey %Htslb]".
    do 2 iNamed "Hkey".
    iFrame "∗ #".
  Qed.

  Lemma keys_inv_witness_hist_lnrz_at γ ts tid rds :
    (ts < tid)%nat ->
    ts_lb γ tid -∗
    db_ptstos γ rds -∗
    ([∗ set] key ∈ dom rds, key_inv_linearizable_after γ key ts) ==∗
    db_ptstos γ rds ∗
    ([∗ set] key ∈ dom rds, key_inv_linearizable_after γ key (pred tid)) ∗
    ([∗ map] key ↦ value ∈ rds, hist_lnrz_at γ key (pred tid) value).
  Proof.
    iIntros (Htid) "#Htid Hpts Hkeys".
    rewrite 2!big_sepS_big_sepM -big_sepM_sep /db_ptstos.
    iCombine "Hpts Hkeys" as "Hptskeys".
    rewrite -2!big_sepM_sep -big_sepM_bupd.
    iApply (big_sepM_impl with "Hptskeys").
    iIntros (k v Hv) "!> [Hpt Hkey]".
    iDestruct "Hkey" as (tslb) "[Hkey %Htslb]".
    do 2 iNamed "Hkey". iNamed "Hprop".
    iDestruct (db_ptsto_agree with "Hpt Hdbv") as %->.
    (* Re-establish [ext_by_lnrz]. *)
    pose proof (ext_by_lnrz_inv_linearize_abort tid _ _ _ Hdiffl) as Hdiffl'.
    set lnrz' := last_extend _ _ in Hdiffl'.
    (* Update [hist_lnrz_auth]. *)
    iMod (hist_lnrz_update lnrz' with "Hlnrz") as "Hlnrz".
    { apply last_extend_prefix. }
    (* Extract a witness that the value of linearized history at [pred tid] is [v]. *)
    iAssert (hist_lnrz_at γ k (pred tid) v)%I as "#Hlb".
    { iDestruct (hist_lnrz_witness with "Hlnrz") as "#Hlb".
      iFrame "Hlb".
      iPureIntro.
      rewrite lookup_last_extend_r.
      { apply Hlast. }
      { lia. }
      { lia. }
    }
    (* Weaken the new [ts_lb] and clear the unneeded one. *)
    iDestruct (ts_lb_weaken (pred tid) with "Htid") as "Htid'"; first lia.
    iClear "Htslb Htid".
    iFrame "∗ # %".
    iPureIntro.
    split; last done.
    split.
    { by rewrite last_last_extend. }
    { rewrite last_extend_length; last first.
      { intros Hnil. by subst lnrz. }
      lia.
    }
  Qed.

  Lemma keys_inv_linearize_commit {γ kmodls rds} wrs ts tid :
    (ts < tid)%nat ->
    dom wrs = dom rds ->
    dom kmodls = dom wrs ->
    ts_lb γ tid -∗
    db_ptstos γ rds -∗
    ([∗ map] key ↦ kmodl ∈ kmodls,
       key_inv_no_kmodl_linearizable_after γ key kmodl ts) ==∗
    db_ptstos γ wrs ∗
    ([∗ map] key ↦ kmodl;v ∈ kmodls;wrs,
       key_inv_no_kmodl γ key (<[tid := v]> kmodl)).
  Proof.
    iIntros (Htid Hdomwrs Hdomkmodls) "#Htid Hpts Hkeys".
    iCombine "Hpts Hkeys" as "Hptskeys".
    rewrite -big_sepM2_sepM; last first.
    { intros k. rewrite -2!elem_of_dom. set_solver. }
    rewrite /db_ptstos.
    rewrite (big_sepM_big_sepM2 _ _ kmodls); last apply Hdomkmodls.
    rewrite (big_sepM2_flip _ wrs kmodls) -big_sepM2_sep -big_sepM2_bupd.
    iApply (big_sepM2_impl_dom_eq with "Hptskeys"); [set_solver | set_solver |].
    iIntros (k x kmodl y kmodl' Hx Hkmodl Hy Hkmodl') "!> [Hpt Hkey]".
    rewrite Hkmodl in Hkmodl'. symmetry in Hkmodl'. inv Hkmodl'.
    iDestruct "Hkey" as (tslb) "[Hkey %Htslb]".
    iNamed "Hkey". iNamed "Hprop".
    (* Re-establish [ext_by_lnrz]. *)
    unshelve epose proof (ext_by_lnrz_inv_linearize_commit tid y _ _ _ _ Hdiffl) as Hdiffl'.
    { (* solved with [Htid, Htslb, Hext] *) lia. }
    set lnrz' := _ ++ _ in Hdiffl'.
    (* Update [hist_lnrz_auth]. *)
    iMod (hist_lnrz_update lnrz' with "Hlnrz") as "Hlnrz".
    { apply prefix_app_r, last_extend_prefix. }
    iMod (db_ptsto_update y with "Hpt Hdbv") as "[Hpt Hdbv]".
    iClear "Htslb".
    iFrame "∗ # %".
    iPureIntro.
    split; first by rewrite last_snoc.
    rewrite length_app /=.
    rewrite last_extend_length_eq_n; last first.
    { lia. }
    { intros Hnil. by subst lnrz. }
    lia.
  Qed.

  Lemma txnsys_inv_linearize_abort γ (Q : dbmap -> dbmap -> Prop) ts tid future rds form :
    let Qr := λ wrs, Q rds wrs ∧ dom wrs ⊆ dom rds in
    dom rds ⊆ keys_all ->
    (ts < tid)%nat ->
    conflict_cases [] future tid form ->
    ts_lb γ tid -∗
    incorrect_fcc γ tid form -∗
    db_ptstos γ rds -∗
    txnsys_inv_with_future_no_ts γ future ts -∗
    ([∗ set] key ∈ keys_all, key_inv_linearizable_after γ key ts) ==∗
    db_ptstos γ rds ∗
    txnsys_inv_with_future_no_ts γ future tid ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    txnwrs_excl γ tid ∗
    txnpost_receipt γ tid Qr ∗
    ([∗ map] key ↦ value ∈ rds, hist_lnrz_at γ key (pred tid) value) ∗
    txns_lnrz_receipt γ tid.
  Proof.
    iIntros (Qr Hdomrds Hts Hcft) "#Htslb #Hfcc Hpts Htxn Hkeys".
    iNamed "Htxn".
    (* Obtain [dom rds] of [hist_lnrz_at]. *)
    iDestruct (big_sepS_subseteq_difference_1 _ _ (dom rds) with "Hkeys") as "[Hkeys HkeysO]".
    { apply Hdomrds. }
    iMod (keys_inv_witness_hist_lnrz_at with "Htslb Hpts Hkeys") as "(Hpts & Hkeys & #Hlbs)".
    { apply Hts. }
    (* Put [dom rds] of [key_inv]. *)
    iDestruct (keys_inv_after_linearize with "Hkeys") as "Hkeys".
    iDestruct (keys_inv_after_linearize with "HkeysO") as "HkeysO".
    iDestruct (big_sepS_subseteq_difference_2 with "Hkeys HkeysO") as "Hkeys".
    { apply Hdomrds. }
    assert (Hnotin : tid ∉ tids).
    { intros Hin. specialize (Htsge _ Hin). simpl in Htsge. lia. }
    (* Update [txns_lnrz_auth] and obtain a witness that [tid] has linearized. *)
    iMod (txns_lnrz_insert _ _ tid with "Htxnsl") as "[Htxnsl #Hlnrzed]".
    { apply Hnotin. }
    (* Update [tids_excl_auth]. *)
    iMod (tids_excl_insert _ _ tid with "Hexcl") as "[Hexcl Hexcltid]".
    { apply Hnotin. }
    (* Allocate [txnwrs_excl]. *)
    assert (Hnotinwrsm : wrsm !! tid = None).
    { rewrite -not_elem_of_dom Hdomw. apply Hnotin. }
    iMod (txnwrs_allocate _ _ tid with "Hwrsm") as "[Hwrsm Hwrsmexcl]".
    { apply Hnotinwrsm. }
    (* Update [txnpost_auth] and obtain a witness. *)
    iMod (txnpost_insert _ _ tid Qr with "Hpost") as "[Hpost #Htp]".
    { rewrite -not_elem_of_dom Hdomq. intros Hin. specialize (Htsge _ Hin). simpl in Htsge. lia. }
    (* Re-establish [ge_all ts ({[tid]} ∪ tids)]. *)
    assert (Htsge' : ge_all tid ({[tid]} ∪ tids)).
    { apply set_Forall_union; first by rewrite set_Forall_singleton.
      intros tidx Htidx.
      specialize (Htsge _ Htidx). simpl in Htsge.
      lia.
    }
    (* Prove [tid ∉ dom wrsm]. *)
    destruct form as [| wrs | wrs]; simpl in Hcft.
    { (* Case: No commit in the entire list of actions. *)
      (* Add [(tid, NC)] to [tmodas]. *)
      iAssert (partitioned_tids γ ({[tid]} ∪ tids) tmodcs (<[tid := NC]> tmodas) resm)%I
        with "[Hpart Hexcltid]" as "Hpart".
      { iNamed "Hpart".
        iDestruct (big_sepS_insert_2 with "Hexcltid Hwabts") as "Hwabts".
        rewrite /partitioned_tids dom_insert_L.
        iFrame.
        iPureIntro.
        set_solver.
      }
      unshelve epose proof (conflict_past_inv_linearize tid NC Hcft Hcp) as Hcp'.
      iFrame "∗ # %".
      iModIntro.
      rewrite wrsm_dbmap_insert_None; last apply Hnotinwrsm.
      iSplit; first done.
      iSplit.
      { by iApply big_sepM_insert_2. }
      by rewrite 2!dom_insert_L Hdomq Hdomw.
    }
    { (* Case: First commit incompatible with some previous actions. *)
      iAssert (partitioned_tids γ ({[tid]} ∪ tids) tmodcs (<[tid := FCI wrs]> tmodas) resm)%I
        with "[Hpart Hexcltid]" as "Hpart".
      { iNamed "Hpart".
        iDestruct (big_sepS_insert_2 with "Hexcltid Hwabts") as "Hwabts".
        rewrite /partitioned_tids dom_insert_L.
        iFrame.
        iPureIntro.
        set_solver.
      }
      unshelve epose proof (conflict_past_inv_linearize tid (FCI wrs) _ Hcp) as Hcp'.
      { destruct Hcft as (lp & ls & Hfc & Hincomp). simpl in Hincomp.
        exists lp, ls.
        split; first apply Hfc.
        rewrite /incompatible_exists Exists_exists in Hincomp.
        destruct Hincomp as (a & Halp & Hincomp).
        rewrite /incompatible_exists Exists_exists.
        exists a.
        split; [set_solver | done].
      }
      iFrame "∗ # %".
      iModIntro.
      rewrite wrsm_dbmap_insert_None; last apply Hnotinwrsm.
      iSplit; first done.
      iSplit.
      { by iApply big_sepM_insert_2. }
      by rewrite 2!dom_insert_L Hdomq Hdomw.
    }
    { (* Case: [Q rds wrs] does not hold. *)
      iAssert (partitioned_tids γ ({[tid]} ∪ tids) tmodcs (<[tid := FCC wrs]> tmodas) resm)%I
        with "[Hpart Hexcltid]" as "Hpart".
      { iNamed "Hpart".
        iDestruct (big_sepS_insert_2 with "Hexcltid Hwabts") as "Hwabts".
        rewrite /partitioned_tids dom_insert_L.
        iFrame.
        iPureIntro.
        set_solver.
      }
      unshelve epose proof (conflict_past_inv_linearize tid (FCC wrs) Hcft Hcp) as Hcp'.
      iFrame "∗ # %".
      iModIntro.
      rewrite wrsm_dbmap_insert_None; last apply Hnotinwrsm.
      iSplit; first done.
      iSplit.
      { by iApply big_sepM_insert_2. }
      by rewrite 2!dom_insert_L Hdomq Hdomw.
    }
  Qed.

  (* Do this at linearization point:
     destruct (decide (Q rds wrs ∧ dom wrs ⊆ dom rds)) as [[_ Hdomwrs] | Hneg]; last first.
   *)

  Lemma txnsys_inv_linearize_commit γ (Q : dbmap -> dbmap -> Prop) ts tid future rds wrs :
    let Qr := λ wrs, Q rds wrs ∧ dom wrs ⊆ dom rds in
    dom wrs ⊆ dom rds ->
    dom rds ⊆ keys_all ->
    (ts < tid)%nat ->
    first_commit_compatible future tid wrs ->
    ts_lb γ tid -∗
    db_ptstos γ rds -∗
    txnsys_inv_with_future_no_ts γ future ts -∗
    ([∗ set] key ∈ keys_all, key_inv_linearizable_after γ key ts) ==∗
    db_ptstos γ (wrs ∪ rds) ∗
    txnsys_inv_with_future_no_ts γ future tid ∗
    ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    txnwrs_excl γ tid ∗
    txnpost_receipt γ tid Qr ∗
    ([∗ map] key ↦ value ∈ rds, hist_lnrz_at γ key (pred tid) value) ∗
    txns_lnrz_receipt γ tid.
  Proof.
    iIntros (Qr Hdomwrs Hdomrds Hts Hfcc) "#Htslb Hpts Htxn Hkeys".
    iNamed "Htxn".
    (* Obtain [dom rds] of [hist_lnrz_at]. *)
    iDestruct (big_sepS_subseteq_difference_1 _ _ (dom rds) with "Hkeys") as "[Hkeys HkeysO]".
    { apply Hdomrds. }
    iMod (keys_inv_witness_hist_lnrz_at with "Htslb Hpts Hkeys") as "(Hpts & Hkeys & #Hlbs)".
    { apply Hts. }
    assert (Hnotin : tid ∉ tids).
    { intros Hin. specialize (Htsge _ Hin). simpl in Htsge. lia. }
    (* Update [txns_lnrz_auth] and obtain a witness that [tid] has linearized. *)
    iMod (txns_lnrz_insert _ _ tid with "Htxnsl") as "[Htxnsl #Hlnrzed]".
    { apply Hnotin. }
    (* Update [tids_excl_auth]. *)
    iMod (tids_excl_insert _ _ tid with "Hexcl") as "[Hexcl Hexcltid]".
    { apply Hnotin. }
    (* Prove [tmodcs !! tid = None]. *)
    iAssert (⌜tmodcs !! tid = None⌝)%I as %Hnotintmodcs.
    { iNamed "Hpart".
      iDestruct (tids_excl_not_elem_of with "Hwcmts Hexcltid") as %Hnotintmodcs.
      by rewrite not_elem_of_dom in Hnotintmodcs.
    }
    (* Allocate [txnwrs_excl]. *)
    assert (Hnotinwrsm : wrsm !! tid = None).
    { rewrite -not_elem_of_dom Hdomw. apply Hnotin. }
    iMod (txnwrs_allocate _ _ tid with "Hwrsm") as "[Hwrsm Hwrsmexcl]".
    { apply Hnotinwrsm. }
    (* Update [txnpost_auth] and obtain a witness. *)
    iMod (txnpost_insert _ _ tid Qr with "Hpost") as "[Hpost #Htp]".
    { rewrite -not_elem_of_dom Hdomq. intros Hin. specialize (Htsge _ Hin). simpl in Htsge. lia. }
    (* Re-establish [ge_all ts ({[tid]} ∪ tids)]. *)
    assert (Htsge' : ge_all tid ({[tid]} ∪ tids)).
    { apply set_Forall_union; first by rewrite set_Forall_singleton.
      intros tidx Htidx.
      specialize (Htsge _ Htidx). simpl in Htsge.
      lia.
    }
    (* Obtain [dom wrs] of [kmod_lnrz_half] from the txnsys invariant. *)
    iDestruct (big_sepS_subseteq_difference_1 _ _ (dom wrs) with "Hkmodls") as "[Hkmodls HkmodlsO]".
    { set_solver. }
    (* Obtain [dom wrs] of [kmod_lnrz_half] from the keys invariant. *)
    iDestruct (big_sepS_subseteq_difference_1 _ _ (dom wrs) with "Hkeys") as "[Hkeys HkeysR]".
    { set_solver. }
    (* Extract [kmod_lnrz_half] out of [key_inv_linearizable_after]. *)
    iDestruct (big_sepS_exists_sepM with "Hkeys") as (tslbm) "[%Hdomtslbm Hkeys]".
    iDestruct (big_sepM_sep with "Hkeys") as "[Hkeys %Htslbm]".
    iDestruct (keys_inv_with_tslb_extract_kmodl with "Hkeys") as (kmodls) "[Hkeys Hkmodls']".
    iDestruct (big_sepM2_dom with "Hkeys") as %Hdomkmodls.
    (* Agreement of [kmod_lnrz_half] between [txnsys_inv] and [key_inv]. *)
    iDestruct (kmod_lnrz_big_agree with "Hkmodls Hkmodls'") as %Hkmodls.
    { set_solver. }
    (* Update [kmod_lnrz_half]. *)
    set tmodcs' := <[tid := wrs]> tmodcs.
    iMod (kmod_lnrz_big_update (λ k, vslice tmodcs' k) with
           "Hkmodls Hkmodls'") as "[Hkmodls Hkmodls']".
    { set_solver. }
    iAssert ([∗ map] k ↦ kmod;v ∈ kmodls;wrs, kmod_lnrz_half γ k (<[tid := v]> kmod))%I
      with "[Hkmodls']" as "Hkmodls'".
    { iApply (big_sepM_sepM2_impl with "Hkmodls'").
      { set_solver. }
      iIntros (k kmod v Hkmod Hv) "!> Hkmods".
      subst tmodcs'.
      specialize (Hkmodls _ _ Hkmod).
      by rewrite (vslice_insert_Some _ _ _ _ _ Hv) Hkmodls.
    }
    (* Update the unmodified part of [kmod_lnrz_half] (from [txnsys_inv]). *)
    iAssert ([∗ set] x ∈ (keys_all ∖ dom wrs), kmod_lnrz_half γ x (vslice tmodcs' x))%I
      with "[HkmodlsO]" as "HkmodlsO".
    { iApply (big_sepS_impl with "HkmodlsO").
      iIntros (k Hk) "!> Hkmod".
      subst tmodcs'.
      assert (Hnotinwrs : wrs !! k = None).
      { rewrite -not_elem_of_dom. set_solver. }
      by rewrite (vslice_insert_None _ _ _ _ Hnotintmodcs Hnotinwrs).
    }
    (* Combine modified and unmodified parts of [kmod_lnrz_half]. *)
    iDestruct (big_sepS_subseteq_difference_2 with "Hkmodls HkmodlsO") as "Hkmodls".
    { set_solver. }
    (* Re-retablish [key_inv_linearizable_after] w.r.t. linearize-commit. *)
    iAssert ([∗ map] k ↦ kmodl ∈ kmodls, key_inv_no_kmodl_linearizable_after γ k kmodl (pred tid))%I
      with "[Hkeys]" as "Hkeys".
    { iApply (big_sepM2_sepM_impl with "Hkeys"); first set_solver.
      iIntros (k tslb kmod kmod' Htslb Hkmod Hkmod') "!> Hkey".
      rewrite Hkmod in Hkmod'. symmetry in Hkmod'. inv Hkmod'.
      specialize (Htslbm _ _ Htslb). simpl in Htslbm.
      iFrame "∗ %".
    }
    iDestruct (big_sepM_subseteq_difference_1 _ (rds ∩ wrs) with "Hpts") as "[Hpts HptsO]".
    { apply map_intersection_subseteq. }
    iMod (keys_inv_linearize_commit wrs _ tid with "Htslb Hpts Hkeys") as "[Hpts Hkeys]".
    { lia. }
    { set_solver. }
    { set_solver. }
    iCombine "Hpts HptsO" as "Hpts".
    rewrite -big_sepM_union; last first.
    { apply map_disjoint_difference_union. }
    rewrite map_intersection_difference_union.
    (* Put [kmod_lnrz_half] back to [key_inv_linearizable_after]. *)
    iAssert ([∗ set] k ∈ dom wrs, key_inv γ k)%I with "[Hkeys Hkmodls']" as "Hkeys".
    { iCombine "Hkeys Hkmodls'" as "Hkeys".
      rewrite -big_sepM2_sep.
      rewrite big_sepS_big_sepM.
      iApply (big_sepM2_sepM_impl with "Hkeys"); first set_solver.
      iIntros (k kmodl v v' Hkmodl Hv _) "!> Hkey". clear v'.
      iDestruct "Hkey" as "[Hkey Hkmodl]".
      do 2 (iNamed "Hkey").
      iFrame "∗ # %".
    }
    iDestruct (keys_inv_after_linearize with "HkeysR") as "HkeysR".
    iDestruct (big_sepS_subseteq_difference_2 with "Hkeys HkeysR") as "Hkeys".
    { apply Hdomwrs. }
    (* Re-establish [paritioned_tids]. *)
    iAssert (partitioned_tids γ ({[tid]} ∪ tids) (<[tid := wrs]> tmodcs) tmodas resm)%I
      with "[Hpart Hexcltid]" as "Hpart".
    { iNamed "Hpart".
      iDestruct (big_sepS_insert_2 with "Hexcltid Hwcmts") as "Hwcmts".
      rewrite /partitioned_tids dom_insert_L.
      iFrame.
      iPureIntro.
      set_solver.
    }
    iDestruct (keys_inv_after_linearize with "HkeysO") as "HkeysO".
    iDestruct (big_sepS_subseteq_difference_2 with "Hkeys HkeysO") as "Hkeys".
    { apply Hdomrds. }
    iFrame "∗ # %".
    iModIntro.
    rewrite wrsm_dbmap_insert_None; last apply Hnotinwrsm.
    iSplit; first done.
    iPureIntro.
    rewrite 2!dom_insert_L Hdomq Hdomw.
    do 3 (split; first done).
    split.
    { rewrite dom_insert_L.
      apply set_Forall_union; last apply Hnz.
      rewrite set_Forall_singleton.
      (* solved with [Hts]. *)
      lia.
    }
    { by apply map_Forall_insert_2. }
  Qed.

End inv.
