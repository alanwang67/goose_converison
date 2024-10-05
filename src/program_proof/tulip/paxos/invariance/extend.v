From Perennial.program_proof.tulip.paxos Require Import prelude.

Section extend.
  Context `{!paxos_ghostG Σ}.

  Lemma node_inv_extend {γ nid term v} v' :
    prefix v v' ->
    is_proposal_lb γ term v' -∗
    own_current_term_half γ nid term -∗
    own_node_ledger_half γ nid v -∗
    node_inv γ nid term ==∗
    own_current_term_half γ nid term ∗
    own_node_ledger_half γ nid v' ∗
    node_inv γ nid term ∗
    is_accepted_proposal_lb γ nid term v'.
  Proof.
    iIntros (Hprefix) "#Hpslb HtermcX HlognX Hnode".
    iNamed "Hnode".
    (* Agreements. *)
    iDestruct (current_term_agree with "HtermcX Htermc") as %->.
    iDestruct (node_ledger_agree with "HlognX Hlogn") as %->.
    (* Update the node-local ledger. *)
    iMod (node_ledger_update v' with "HlognX Hlogn") as "[HlognX Hlogn]".
    iDestruct (accepted_proposal_lookup with "Hacpt Hpsa") as %Hv.
    (* Update the accepted ledger at [term]. *)
    iMod (accepted_proposal_update v' with "Hacpt Hpsa") as "[Hacpt Hpsa]".
    { apply Hprefix. }
    iDestruct (accepted_proposal_witness with "Hacpt") as "#Hacptlb".
    iFrame "∗ # %".
    iModIntro.
    iSplit.
    { (* Re-establish [prefix_base_ledger]. *)
      iDestruct (big_sepM_lookup with "Hpsalbs") as (vlb) "[#Hlb %Hprefixv]"; first apply Hv.
      iApply big_sepM_insert_2; last done.
      iFrame "Hlb".
      iPureIntro.
      by trans v.
    }
    iSplit.
    { (* Re-establish [prefix_growing_ledger]. *)
      iApply big_sepM_insert_2; last done.
      by iFrame "Hpslb".
    }
    iPureIntro.
    split.
    { (* Re-establish [fixed_proposals]. *)
      intros t d Hd.
      specialize (Hfixed _ _ Hd).
      destruct (decide (t = term)) as [-> | Hne]; last by rewrite lookup_insert_ne.
      exfalso.
      apply lookup_lt_Some in Hd.
      clear -Hd Hlends. lia.
    }
    { (* Re-establish [free_terms_after]. *)
      apply elem_of_dom_2 in Hv.
      rewrite dom_insert_L.
      by replace (_ ∪ dom psa) with (dom psa) by set_solver.
    }
  Qed.

  Lemma paxos_inv_extend {γ nids nid term v} vapp :
    let v' := v ++ vapp in
    nid ∈ nids ->
    proposed_cmds γ vapp -∗
    own_proposal γ term v -∗
    own_current_term_half γ nid term -∗
    own_ledger_term_half γ nid term -∗
    own_node_ledger_half γ nid v -∗
    paxos_inv γ nids ==∗
    own_proposal γ term v' ∗
    own_current_term_half γ nid term ∗
    own_ledger_term_half γ nid term ∗
    own_node_ledger_half γ nid v' ∗
    paxos_inv γ nids ∗
    is_accepted_proposal_lb γ nid term v'.
  Proof.
    iIntros (v' Hnid) "#Hpcs Hp Htermc Hterml Hlogn Hinv".
    iNamed "Hinv".
    iDestruct (proposal_lookup with "Hp Hps") as %Hv.
    (* Re-establish [proposed_cmds] on the new log [v ++ vapp]. *)
    iAssert (proposed_cmds γ (v ++ vapp))%I as "Hsubsume'".
    { iDestruct (big_sepM_lookup with "Hsubsume") as "Hpcsv"; first apply Hv.
      iFrame "#".
    }
    (* Extend the growing proposal to [v'] and extract a witness. *)
    iMod (proposal_update (v ++ vapp) with "Hp Hps") as "[Hp Hps]"; first by apply prefix_app_r.
    iDestruct (proposal_witness with "Hp") as "#Hplb".
    (* Update the node-local ledger. *)
    rewrite -Hdomtermlm elem_of_dom in Hnid.
    destruct Hnid as [terml Hterml].
    iDestruct (big_sepM_lookup_acc _ _ nid with "Hnodes") as "[Hnode HnodesC]".
    { apply Hterml. }
    iDestruct (own_ledger_term_node_inv_terml_eq with "Hterml Hnode") as %->.
    iMod (node_inv_extend v' with "Hplb Htermc Hlogn Hnode")
      as "(Htermc & Hlogn & Hnode & #Hacpted)".
    { by apply prefix_app_r. }
    iDestruct ("HnodesC" with "Hnode") as "Hnodes".
    iFrame "∗ # %".
    iModIntro.
    iSplit; first by iApply big_sepM_insert_2.
    iPureIntro.
    intros t.
    destruct (decide (t = term)) as [-> | Hne]; last by rewrite lookup_insert_ne.
    rewrite lookup_insert.
    specialize (Hvp term).
    inversion Hvp as [loglb y Hprefix Heq1 Heq2|]; subst; [ simpl | ].
    - constructor.
      (* XXX: need to unfold this type for congruence to work *)
      unfold proposals in *.
      assert (y = v) by congruence; subst.
      trans v; [ | apply prefix_app_r ]; auto.
    - unfold proposals in *. congruence.
  Qed.

End extend.
