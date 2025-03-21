From Perennial.program_proof.session Require Export session_prelude coq_session.
From Perennial.program_proof.session Require Export versionVector processClientRequest gossip.

Section heap.

  Context `{hG: !heapGS Σ}.

  Definition coq_processClientRequest (s: Server.t) (r: Message.t) :
    (bool * Server.t * Message.t) :=
    if (negb (coq_compareVersionVector s.(Server.VectorClock) r.(Message.C2S_Client_VersionVector))) then
      (false, s, (Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0))
    else
      if (uint.nat r.(Message.C2S_Client_OperationType) =? 0) then
        let S2C_Client_Data : u64 := coq_getDataFromOperationLog s.(Server.OperationsPerformed) in
        let S2C_Client_VersionVector : (list u64) := s.(Server.VectorClock) in
        let S2C_Client_Number : u64 := r.(Message.C2S_Client_Id) in
        let S2C_Server_Id : u64 := s.(Server.Id) in
        (true, s, (Message.mk 4 0 0 0 0 [] 0 0 [] 0 0 0 0 0 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number))
      else
        let v : nat := uint.nat (list_lookup_total (uint.nat s.(Server.Id)) s.(Server.VectorClock)) in
        let VectorClock : list u64 := <[(uint.nat s.(Server.Id))%nat := (W64 (v + 1))]>s.(Server.VectorClock) in
        let OperationsPerformed : list Operation.t := s.(Server.OperationsPerformed) ++ [Operation.mk VectorClock r.(Message.C2S_Client_Data)] in
        let MyOperations : list Operation.t := s.(Server.MyOperations) ++ [Operation.mk VectorClock r.(Message.C2S_Client_Data)] in
        let S2C_Client_OperationType := 1 in
        let S2C_Client_Data := 0 in
        let S2C_Client_VersionVector := VectorClock in
        let S2C_Client_Number := r.(Message.C2S_Client_Id) in
        let S2C_Server_Id : u64 := s.(Server.Id) in
        (true, Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) VectorClock OperationsPerformed MyOperations s.(Server.PendingOperations) s.(Server.GossipAcknowledgements), (Message.mk 4 0 0 0 0 [] 0 0 [] 0 0 0 0 1 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number)).

  Lemma wp_processClientRequest sv s msgv msg (n: nat)
    len_vc len_op len_mo len_po len_ga len_c2s len_s2c :
    {{{
        is_server sv s n len_vc len_op len_mo len_po len_ga ∗
        is_message msgv msg n len_c2s len_s2c ∗
        ⌜len_vc = len_c2s /\ (uint.nat s .(Server.Id) < length s .(Server.VectorClock))%nat⌝
    }}}
      processClientRequest (server_val sv) (message_val msgv)
    {{{
        (b: bool) ns nm, RET (#b, server_val ns, message_val nm);
        ∃ len_c2s', ∃ len_s2c',
        ⌜b = (coq_processClientRequest s msg).1.1⌝ ∗
        is_server ns (coq_processClientRequest s msg).1.2 n len_vc len_op len_mo len_po len_ga ∗
        is_message nm (coq_processClientRequest s msg).2 n len_c2s' len_s2c' ∗
        is_message msgv msg n len_c2s len_s2c ∗
        ⌜if b then len_c2s' = 0%nat /\ len_s2c' = len_c2s else len_c2s' = 0%nat /\ len_s2c' = 0%nat⌝
    }}}.
  Proof.
    rewrite redefine_server_val redefine_message_val. TypeVector.des sv. TypeVector.des msgv. iIntros "%Φ (H_server & H_message & %H1_precondition & %H2_precondition) HΦ".
    iDestruct "H_server" as "(%H1 & %H2 & H3 & H4 & %H5 & H6 & H7 & H8 & H9 & %H10)".
    iDestruct "H_message" as "(%H11 & %H12 & %H13 & %H14 & %H15 & H16 & %H17 & %H18 & %H19 & H20 & %H21 & %H22 & %H23 & %H24 & %H25 & %H26 & H27 & %H28 & %H29 & %H30)".
    simplNotation. subst. rewrite /processClientRequest.
    wp_pures. wp_pures. wp_apply wp_ref_to. { repeat econstructor; eauto. }
    iIntros "%reply H_reply". wp_pures. wp_apply (wp_compareVersionVector with "[$H4 $H16]"); auto.
    iIntros "%r (-> & H4 & [H16 %TMP])". clear TMP. wp_if_destruct.
    - wp_load. wp_pures. iModIntro.
      pose (b := false).
      set (ns := (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)).
      set (nm := (W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0)).
      replace (Φ (#false, (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #())))))))), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, #())))))))))))))))))))%V) with (Φ (#b, (#ns.1.1.1.1.1.1.1, (#ns.1.1.1.1.1.1.2, (ns.1.1.1.1.1.2, (ns.1.1.1.1.2, (ns.1.1.1.2, (ns.1.1.2, (ns.1.2, (ns.2, #())))))))), (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.1.1.2, (nm.1.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.1.1.2, (nm.1.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.1.2, (#nm.1.1.1.1.1.2, (#nm.1.1.1.1.2, (#nm.1.1.1.2, (nm.1.1.2, (#nm.1.2, (#nm.2, #())))))))))))))))))))%V) by f_equal.
      unfold tuple_of. simpl TypeVector.tuple_of. iApply "HΦ". subst b ns nm.
      iExists 0%nat. iExists 0%nat. unfold coq_processClientRequest. rewrite Heqb. simpl. iFrame.
      unfold is_message; simplNotation; simpl. iClear "H_reply". repeat (iSplit; try done).
      iSplitL "". { iApply own_slice_small_nil. done. } repeat (iSplit; try done).
      iSplitL "".
      { iExists []. iSplit.
        - iApply own_slice_nil; done.
        - simpl. done.
      }
      repeat (iSplit; try done).
      iApply own_slice_small_nil. done.
    - wp_pures. wp_if_destruct.
      + wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
        wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
        wp_apply (wp_getDataFromOperationLog with "[$H6]"). iIntros "%r (-> & H6)".
        wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
        wp_apply (wp_NewSlice). iIntros "%s1 H_s1". replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with (@nil u64) by reflexivity.
        wp_apply (wp_SliceAppendSlice with "[$H_s1 $H4]"); auto. clear s1. iIntros "%s1 [H_s1 H4]". simpl.
        wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
        wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
        wp_apply (wp_storeField_struct with "[H_reply]"). { repeat econstructor; eauto. } { iExact "H_reply". } iIntros "H_reply". wp_pures.
        wp_load. wp_pures. iModIntro. simpl.
        pose (b := true).
        set (ns := (s .(Server.Id), s .(Server.NumberOfServers), t4, t3, t2, t1, t0, t)).
        set (nm := (W64 4, W64 0, W64 0, W64 0, W64 0, Slice.nil, W64 0, W64 0, Slice.nil, W64 0, W64 0, W64 0, W64 0, W64 0, coq_getDataFromOperationLog s .(Server.OperationsPerformed), s1, s .(Server.Id), msg .(Message.C2S_Client_Id))).
        replace (Φ (#true, (#s .(Server.Id), (#s .(Server.NumberOfServers), (t4, (t3, (t2, (t1, (t0, (t, #())))))))), (#(W64 4), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T uint64T), (zero_val uint64T, (zero_val uint64T, (zero_val (slice.T (slice.T uint64T * (uint64T * unitT)%ht)), (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (zero_val uint64T, (#(W64 0), (#(coq_getDataFromOperationLog s .(Server.OperationsPerformed)), (s1, (#s .(Server.Id), (#msg .(Message.C2S_Client_Id), #())))))))))))))))))))%V) with (Φ (#b, server_val ns, message_val nm)%V) by f_equal.
        unfold server_val, message_val. iApply "HΦ". subst b ns nm.
        iExists 0%nat. iExists (length s .(Server.VectorClock)).
        unfold coq_processClientRequest; rewrite Heqb; simpl.
        assert ((uint.nat msg .(Message.C2S_Client_OperationType) =? 0) = true) as H_OBS1.
        { rewrite Z.eqb_eq. word. }
        rewrite H_OBS1; simpl. unfold is_message; simplNotation; simpl. rewrite Z.eqb_eq in H_OBS1.
        iSplitL "". { done. }
        iSplitL "H3 H7 H8 H9 H6 H4".
        { iFrame. done. }
        { iSplitL "H_s1".
          - repeat (iSplit; try done). iSplitL "".
            { iApply own_slice_small_nil. reflexivity. }
            repeat (iSplit; try done). iSplitL "".
            { iExists []; simpl; iSplit.
              - iApply own_slice_nil; reflexivity.
              - iPureIntro. tauto.
            }
            repeat (iSplit; try done). iApply (own_slice_to_small with "[$H_s1]").
          - iFrame. done.
        }
      + wp_apply wp_ref_to. { repeat econstructor; eauto. } iIntros "%s1 H_s1". wp_pures.
        iAssert ⌜is_Some (s .(Server.VectorClock) !! uint.nat s .(Server.Id))⌝%I as "[%x %H_x]".
        { iPoseProof (own_slice_small_sz with "[$H4]") as "%LEN".
          iPureIntro. eapply lookup_lt_is_Some_2. word.
        }
        wp_load. wp_pures. wp_apply (wp_SliceGet with "[$H4]"); auto. iIntros "H4".
        wp_load. wp_pures. wp_apply (wp_SliceSet with "[$H4]"); auto. iIntros "H4".
        wp_pures. wp_apply (wp_NewSlice). iIntros "%s2 H_s2". wp_apply (wp_SliceAppendSlice with "[$H_s2 $H4]"); auto.
        clear s2. iIntros "%s2 [H_s2 H4]". replace (replicate (uint.nat (W64 0)) u64_IntoVal .(IntoVal_def w64)) with (@nil w64) by reflexivity. simpl.
        wp_pures. wp_load. wp_pures. admit.
  Admitted.

  Definition coq_processRequest (s: Server.t) (r: Message.t) : (Server.t * list Message.t) :=
    match (uint.nat r.(Message.MessageType))%nat with
    | 0%nat =>
        let '(succeeded, server, reply) := coq_processClientRequest s r in
        if succeeded then
          (server, [reply])
        else
          let UnsatisfiedRequests := s.(Server.UnsatisfiedRequests) ++ [r] in 
          let server := Server.mk s.(Server.Id) s.(Server.NumberOfServers) UnsatisfiedRequests s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements) in
          (server, [])
    | 1%nat =>
        let s := coq_receiveGossip s r in
        let outGoingRequests := [Message.mk 0 0 0 0 0 [] 0 0 [] 0 (s.(Server.Id)) (r.(Message.S2S_Gossip_Sending_ServerId)) (r.(Message.S2S_Gossip_Index)) 0 0 [] 0 0] in
        let '(_, deletedIndex, outGoingRequests) := fold_left (fun (acc: nat * list nat * list Message.t) element =>
                                            let '(index, deletedIndex, acc) := acc in
                                            let '(succeeded, server, reply) := coq_processClientRequest s r in
                                            if succeeded then
                                              ((index + 1)%nat, deletedIndex ++ [index], acc ++ [reply])
                                            else
                                              ((index + 1)%nat, deletedIndex, acc)) s.(Server.UnsatisfiedRequests) (0%nat, [], outGoingRequests) in
        let remainingIndexes := list_difference (seq 0 (length s.(Server.UnsatisfiedRequests))) deletedIndex in 
        let UnsatisfiedRequests := 
          fold_left (fun acc index =>
                      match (s.(Server.UnsatisfiedRequests) !! index) with
                      | Some v => acc ++ [v]
                      | None => acc
                      end
            ) remainingIndexes [] in
        let s := Server.mk s.(Server.Id) s.(Server.NumberOfServers) UnsatisfiedRequests s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements) in
        (s, outGoingRequests)
    | 2%nat =>
        let s := coq_acknowledgeGossip s r in
        (s, [])
    | 3%nat =>
        let outGoingRequests := fold_left (fun acc (index: nat) =>
                                            if (negb (index =? (uint.nat s.(Server.Id)))) then
                                              let S2S_Gossip_Sending_ServerId := s.(Server.Id) in
                                                let S2S_Gossip_Receiving_ServerId := index in
                                                let S2S_Gossip_Operations := coq_getGossipOperations s index in
                                                let S2S_Gossip_Index := length (s.(Server.MyOperations)) in
                                                let message := Message.mk 1 0 0 0 0 [] S2S_Gossip_Sending_ServerId S2S_Gossip_Receiving_ServerId S2S_Gossip_Operations S2S_Gossip_Index 0 0 0 0 0 [] 0 0 in acc ++ [message]
                                              else
                                                acc) (seq 0 (uint.nat s.(Server.NumberOfServers)))  [] in
        (s, outGoingRequests)
          
    | _ => (s, [])
    end.

(*
  Lemma wp_processRequest
*)

End heap.
