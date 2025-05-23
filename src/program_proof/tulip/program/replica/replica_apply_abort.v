From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_terminated replica_release.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__applyAbort rp (tsW : u64) cloga gid rid γ α :
    let ts := uint.nat tsW in
    let cloga' := cloga ++ [CmdAbort ts] in
    not_stuck (apply_cmds cloga') ->
    is_txn_log_lb γ gid cloga' -∗
    {{{ own_replica_with_cloga_no_lsna rp cloga gid rid γ α }}}
      Replica__applyAbort #rp #tsW
    {{{ RET #(); own_replica_with_cloga_no_lsna rp cloga' gid rid γ α }}}.
  Proof.
    iIntros (ts cloga' Hns) "#Hlb'".
    iIntros (Φ) "!> Hrp HΦ".
    wp_rec.
    (* First establish that applying this commit results does not get stuck. *)
    destruct (apply_cmds cloga') as [cm' histm' |] eqn:Happly'; last done.
    (* Also establish connection between executing entire log vs. consistent log. *)
    iNamed "Hrp".
    unshelve epose proof (execute_cmds_apply_cmds cloga ilog cm histm _) as Happly.
    { by eauto 10. }

    (*@ func (rp *Replica) applyAbort(ts uint64) {                              @*)
    (*@     // Query the transaction table. Note that if there's an entry for @ts in @*)
    (*@     // @txntbl, then transaction @ts can only be aborted. That's why we're not @*)
    (*@     // even reading the value of entry.                                 @*)
    (*@     aborted := rp.terminated(ts)                                        @*)
    (*@     if aborted {                                                        @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__terminated with "Hcm").
    iIntros "Hcm".
    case_bool_decide as Hterm; wp_pures.
    { iApply "HΦ".
      apply elem_of_dom in Hterm as [b Hb].
      iFrame "∗ # %".
      iPureIntro. simpl.
      exists ptgsm.
      split.
      { by apply prefix_app_r. }
      rewrite merge_clog_ilog_snoc_clog; last apply Hvicmds.
      split.
      { eapply Forall_impl; first apply Hvicmds. simpl.
        intros nc Hnc.
        rewrite length_app /=.
        clear -Hnc. lia.
      }
      rewrite /execute_cmds foldl_snoc /= execute_cmds_unfold Hexec /= Hb.
      destruct b; last done.
      by rewrite /apply_cmds foldl_snoc /= apply_cmds_unfold /apply_abort Happly Hb in Happly'.
    }
    apply not_elem_of_dom in Hterm.
    (* rewrite /apply_cmds foldl_snoc /= apply_cmds_unfold Happly /= Hterm in Happly'. *)
    (* symmetry in Happly'. inv Happly'. *)

    (*@     rp.txntbl[ts] = false                                               @*)
    (*@                                                                         @*)
    iNamed "Hcm".
    wp_loadField.
    wp_apply (wp_MapInsert with "Htxntbl"); first done.
    iIntros "Htxntbl".

    (*@     // Tuples lock are held iff @prepm[ts] contains something (and so we should @*)
    (*@     // release them by calling @abort).                                 @*)
    (*@     pwrs, prepared := rp.prepm[ts]                                      @*)
    (*@                                                                         @*)
    iNamed "Hcpm".
    wp_loadField.
    wp_apply (wp_MapGet with "HprepmS").
    iIntros (prepS prepared) "[%Hprepared HprepmS]".
    wp_pures.

    (*@     if prepared {                                                       @*)
    (*@         rp.release(pwrs)                                                @*)
    (*@         delete(rp.prepm, ts)                                            @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iDestruct (big_sepM2_dom with "Hprepm") as %Hdomprepm.
    destruct prepared; wp_pures.
    { apply map_get_true in Hprepared.
      assert (is_Some (prepm !! tsW)) as [pwrs Hpwrs].
      { by rewrite -elem_of_dom -Hdomprepm elem_of_dom. }
      iDestruct (big_sepM2_delete with "Hprepm") as "[Hpwrs Hprepm]".
      { apply Hprepared. }
      { apply Hpwrs. }
      iDestruct "Hpwrs" as (pwrsL) "Hpwrs".
      wp_apply (wp_Replica__release with "[$Hpwrs $Hptsmsptsm]").
      { symmetry in Hcpmabs.
        pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcpmabs Hpwrs) as (ts' & Hts' & Hcpmts).
        assert (ts' = ts) as -> by word.
        by specialize (Hvcpm _ _ Hcpmts).
      }
      iIntros "[Hpwrs Hptsmsptsm]".
      wp_loadField.
      wp_apply (wp_MapDelete with "HprepmS").
      iIntros "HprepmS".
      wp_pures.
      iApply "HΦ".
      iAssert ([∗ set] t ∈ dom (delete ts cpm), is_replica_validated_ts γ gid rid t)%I
        as "#Hrpvds'".
      { rewrite dom_delete_L.
        iDestruct (big_sepS_delete _ _ ts with "Hrpvds") as "[_ ?]"; last done.
        symmetry in Hcpmabs.
        pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcpmabs Hpwrs) as (ts' & Hts' & Hcpmts).
        assert (ts' = ts) as -> by word.
        by apply elem_of_dom.
      }
      iClear "Hrpvds".
      iFrame "∗ # %".
      iPureIntro. simpl.
      exists (<[ts := false]> cm), (delete ts ptgsm).
      split.
      { rewrite 2!kmap_insert. f_equal; [word | done]. }
      split.
      { rewrite 2!kmap_delete. f_equal; [word | done]. }
      split.
      { by apply prefix_app_r. }
      { rewrite merge_clog_ilog_snoc_clog; last apply Hvicmds.
        split.
        { by apply map_Forall_delete. }
        split.
        { eapply Forall_impl; first apply Hvicmds. simpl.
          intros nc Hnc.
          rewrite length_app /=.
          clear -Hnc. lia.
        }
        symmetry in Hcpmabs.
        pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcpmabs Hpwrs) as (ts' & Hts' & Hcpmts).
        assert (ts' = ts) as -> by word.
        by rewrite /execute_cmds foldl_snoc /= execute_cmds_unfold Hexec /= Hterm Hcpmts.
      }
    }
    iApply "HΦ".
    iFrame "∗ # %".
    iPureIntro. simpl.
    exists (<[ts := false]> cm), ptgsm.
    split.
    { rewrite 2!kmap_insert. f_equal; [word | done]. }
    split.
    { by apply prefix_app_r. }
    { rewrite merge_clog_ilog_snoc_clog; last apply Hvicmds.
      split.
      { eapply Forall_impl; first apply Hvicmds. simpl.
        intros nc Hnc.
        rewrite length_app /=.
        clear -Hnc. lia.
      }
      apply map_get_false in Hprepared as [Hnone _].
      rewrite -not_elem_of_dom Hdomprepm not_elem_of_dom in Hnone.
      symmetry in Hcpmabs.
      pose proof (lookup_kmap_eq_None _ _ _ _ _  Hcpmabs Hnone) as Hcpmnone.
      specialize (Hcpmnone ts).
      unshelve epose proof (Hcpmnone _) as Hcpmts; first word.
      by rewrite /execute_cmds foldl_snoc /= execute_cmds_unfold Hexec /= Hterm Hcpmts.
    }
  Qed.

End program.
