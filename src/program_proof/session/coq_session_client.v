From Perennial.program_proof.session Require Export session_prelude definitions coq_session.
From Perennial.program_proof.session Require versionVector.

Definition Ev : Z := 0.
Definition Wfr : Z := 1.
Definition Mw : Z := 2.
Definition Mr : Z := 3.
Definition Ryw : Z := 4.
Definition Ca : Z := 5.

Module CoqSessionClient.

  Include Goose.github_com.session.client.

  Definition coq_read (c: Client.t) (serverId: u64) : Message.t :=
    match uint.Z c.(Client.SessionSemantic) with
    | 0 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 1 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 2 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 3 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 4 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (c.(Client.WriteVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 5 => Message.mk 0 (c.(Client.Id)) serverId 0 0 (coq_maxTS c.(Client.WriteVersionVector) c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | _ => Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0
    end.

  Definition coq_write (c: Client.t) (serverId: u64) (value: u64) : Message.t :=
    match uint.Z c.(Client.SessionSemantic) with
    | 0 => Message.mk 0 (c.(Client.Id)) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 1 => Message.mk 0 (c.(Client.Id)) serverId 1 value (c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 2 => Message.mk 0 (c.(Client.Id)) serverId 1 value (c.(Client.WriteVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 3 => Message.mk 0 (c.(Client.Id)) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 4 => Message.mk 0 (c.(Client.Id)) serverId 1 value (replicate (uint.nat c.(Client.NumberOfServers)) (W64 0)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | 5 => Message.mk 0 (c.(Client.Id)) serverId 1 value (coq_maxTS c.(Client.WriteVersionVector) c.(Client.ReadVersionVector)) 0 0 [] 0 0 0 0 0 0 [] 0 0
    | _ => Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0
    end.

  Definition coq_processRequest (c: Client.t) (requestType: u64) (serverId: u64) (value: u64) (ackMessage: Message.t) : Client.t * Message.t :=
    match uint.Z requestType with
    | 0 => (c, coq_read c serverId)
    | 1 => (c, coq_write c serverId value)
    | 2 =>
      match uint.Z ackMessage.(Message.S2C_Client_OperationType) with
      | 0 => (Client.mk c.(Client.Id) c.(Client.NumberOfServers) c.(Client.WriteVersionVector) ackMessage.(Message.S2C_Client_VersionVector) c.(Client.SessionSemantic), Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
      | 1 => (Client.mk c.(Client.Id) c.(Client.NumberOfServers) (ackMessage.(Message.S2C_Client_VersionVector)) c.(Client.ReadVersionVector) c.(Client.SessionSemantic), Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
      | _ => (c, Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
      end
    | _ => (c, Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0)
    end.

End CoqSessionClient.

Export CoqSessionClient.

Section heap.

  Context `{hG: !heapGS Σ}.

  Lemma wp_maxTS (x: Slice.t) (xs: list w64) (y: Slice.t) (ys: list w64) (dx: dfrac) (dy: dfrac) :
    {{{
        own_slice_small x uint64T dx xs ∗
        own_slice_small y uint64T dy ys ∗
        ⌜length xs = length ys⌝
    }}}
      CoqSessionClient.maxTS (slice_val x) (slice_val y)
    {{{
        ns, RET (slice_val ns);
        own_slice_small x uint64T dx xs ∗
        own_slice_small y uint64T dy ys ∗
        own_slice ns uint64T (DfracOwn 1) (coq_maxTS xs ys)
    }}}.
  Proof.
    replace (maxTS x y) with (CoqSessionServer.maxTS (slice_val x) (slice_val y)) by reflexivity.
    iIntros "%Φ H_precondition HΦ".
    wp_apply (versionVector.wp_maxTS with "[$H_precondition]").
    iIntros "%ns (H_ns & H_xs & H_ys)". iApply "HΦ". iFrame.
  Qed.

  Lemma wp_read (c: Client.t) (serverId: u64) (n: nat) cv :
    {{{
        is_client cv c n ∗
        ⌜n = uint.nat c.(Client.NumberOfServers)⌝
    }}}
      CoqSessionClient.read (client_val cv) (#serverId)
    {{{
        msgv, RET (message_val msgv);
        is_client cv c n ∗
        is_message msgv (coq_read c serverId) n n 0%nat
    }}}.
  Proof. (**
    rewrite redefine_client_val redefine_message_val. TypeVector.des cv. iIntros "%Φ (H_is_client & ->) HΦ".
    iDestruct "H_is_client" as "(%H1 & %H2 & H3 & %H4 & H5 & %H6 & %H7)".
    simplNotation; simpl; subst; rewrite /CoqSessionClient.read.
    iPoseProof (own_slice_small_sz with "[$H3]") as "%LENGTH1".
    iPoseProof (own_slice_small_sz with "[$H5]") as "%LENGTH2".
    wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%reply H_reply".
    wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 0))) as [ | ] eqn: Heqb.
    { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1".
      iPoseProof (own_slice_sz with "[$H_s1]") as "%LENGTH3". rewrite length_replicate in LENGTH3.
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_load.
      apply bool_decide_eq_true in Heqb.
      assert (c .(Client.SessionSemantic) = W64 0) as EQ by congruence.
      replace (Φ (#(W64 0), (#c .(Client.Id), (#serverId, (#(W64 0), (#(W64 0), (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, c.(Client.Id), serverId, W64 0, W64 0, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
      iModIntro. simpl. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - unfold coq_read. rewrite -> EQ. replace (uint.Z (W64 0)) with 0%Z by word.
        unfold is_message; iFrame; simplNotation; simpl.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
        iSplitL "". { rewrite length_replicate. done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iApply own_slice_small_nil; eauto. }
        iSplitL "". { iPureIntro. word. }
        done.
    }
    wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 1))) as [ | ] eqn: Heqb0.
    { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1".
      iPoseProof (own_slice_sz with "[$H_s1]") as "%LENGTH3". rewrite length_replicate in LENGTH3.
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_load.
      apply bool_decide_eq_true in Heqb0.
      assert (c .(Client.SessionSemantic) = W64 1) as EQ by congruence.
      replace (Φ (#(W64 0), (#c .(Client.Id), (#serverId, (#(W64 0), (#(W64 0), (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, c.(Client.Id), serverId, W64 0, W64 0, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
      iModIntro. simpl. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - unfold coq_read. rewrite -> EQ. replace (uint.Z (W64 1)) with 1%Z by word.
        unfold is_message; iFrame; simplNotation; simpl.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
        iSplitL "". { rewrite length_replicate. done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iApply own_slice_small_nil; eauto. }
        iSplitL "". { iPureIntro. word. }
        done.
    }
    wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 2))) as [ | ] eqn: Heqb1.
    { wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_apply (wp_NewSlice). iIntros "%s1 H_s1".
      iPoseProof (own_slice_sz with "[$H_s1]") as "%LENGTH3". rewrite length_replicate in LENGTH3.
      wp_pures. wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iFrame. } iIntros "H_reply".
      wp_pures. wp_load.
      apply bool_decide_eq_true in Heqb1.
      assert (c .(Client.SessionSemantic) = W64 2) as EQ by congruence.
      replace (Φ (#(W64 0), (#c .(Client.Id), (#serverId, (#(W64 0), (#(W64 0), (s1, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #()))))))))))))))))))%V) with (Φ (message_val (W64 0, c.(Client.Id), serverId, W64 0, W64 0, s1, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)%core)) by reflexivity.
      iModIntro. simpl. iApply "HΦ".
      iSplitL "H3 H5".
      - iFrame. simplNotation; simpl; done.
      - unfold coq_read. rewrite -> EQ. replace (uint.Z (W64 2)) with 2%Z by word.
        unfold is_message; iFrame; simplNotation; simpl.
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "H_s1". { iApply (own_slice_to_small with "[$H_s1]"). }
        iSplitL "". { rewrite length_replicate. done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iExists []. simpl; iSplitR ""; try done. iApply (own_slice_nil); eauto. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { done. }
        iSplitL "". { iApply own_slice_small_nil; eauto. }
        iSplitL "". { iPureIntro. word. }
        done.
    }
    wp_pures. destruct (bool_decide (#c .(Client.SessionSemantic) = #(W64 3))) as [ | ] eqn: Heqb2.
    { admit. }
    admit.
  Qed. *) Admitted.

  Lemma wp_write (c: Client.t) (serverId: u64) (value: u64) (n: nat) cv :
    {{{
        is_client cv c n ∗
        ⌜n = uint.nat c.(Client.NumberOfServers)⌝
    }}}
      CoqSessionClient.write (client_val cv) (#serverId) (#value)
    {{{
        msgv, RET (message_val msgv);
        is_client cv c n ∗
        is_message msgv (coq_write c serverId value) n n 0%nat
    }}}.
  Proof.
  Admitted.

  Lemma wp_processRequest (c: Client.t) (requestType: u64) (serverId: u64) (value: u64) (ackMessage: Message.t) (n: nat) cv msgv :
    {{{
        is_client cv c n ∗
        is_message msgv ackMessage n n n ∗
        ⌜n = uint.nat c.(Client.NumberOfServers)⌝
    }}}
      CoqSessionClient.processRequest (client_val cv) (#requestType) (#serverId) (#value) (message_val msgv)
    {{{
        cv' msgv', RET (client_val cv', message_val msgv');
        is_client cv' (coq_processRequest c requestType serverId value ackMessage).1 n ∗
        is_message msgv' (coq_processRequest c requestType serverId value ackMessage).2 n (if (uint.Z requestType =? 0) || (uint.Z requestType =? 1) then n else 0%nat) 0%nat ∗
        is_message msgv ackMessage n n n ∗
        ⌜n = uint.nat (coq_processRequest c requestType serverId value ackMessage).1.(Client.NumberOfServers)⌝
    }}}.
  Proof.
  Admitted.

End heap.
