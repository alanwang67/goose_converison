From Perennial.program_proof.session Require Export session_prelude.
From Perennial.program_proof.session Require Export definitions.

Module CoqSession.

  Fixpoint coq_compareVersionVector (v1: list u64) (v2: list u64) : bool :=
    match v1 with
    | [] => true
    | cons h1 t1 => match v2 with
                    | [] => true
                    | cons h2 t2 => if (uint.nat h1 <? uint.nat h2) then false else
                                      (coq_compareVersionVector t1 t2)
                    end
    end.

  Fixpoint coq_lexicographicCompare (v1: list u64) (v2: list u64) : bool :=
    match v1 with
    | [] => false 
    | cons h1 t1 => match v2 with
                    | [] => false 
                    | cons h2 t2 => if (uint.Z h1) =? (uint.Z h2) then
                                      (coq_lexicographicCompare t1 t2) else (uint.Z h1) >? (uint.Z h2)
                    end
    end.

  Definition coq_maxTwoInts (x: u64) (y: u64) : u64 :=
    if uint.Z x >? uint.Z y then x else y. 

  Fixpoint coq_maxTS (t1: list u64) (t2: list u64) : list u64 :=
    match t1 with
    | [] => []
    | cons hd1 tl1 => match t2 with
                      | [] => [] 
                      | cons hd2 tl2 => (cons (coq_maxTwoInts hd1 hd2) (coq_maxTS tl1 tl2))
                      end
    end.

  Definition coq_oneOffVersionVector (v1: list u64) (v2: list u64) : bool :=
    let (output, canApply) :=
      fold_left (fun (acc: bool * bool) (element: u64 * u64) =>
                  let (e1, e2) := element in
                  let (output, canApply) := acc in
                  if (canApply && (uint.Z (w64_word_instance.(word.add) e1 (W64 1)) =? uint.Z e2)) then
                    (output && true, false)
                  else
                    if uint.Z e1 >=? uint.Z e2 then
                      (output && true, canApply)
                    else 
                      (false, canApply)) (zip v1 v2) (true, true) in
    output && (negb canApply).

  Fixpoint coq_equalSlices (s1: list u64) (s2: list u64) : bool :=
    match s1 with
    | [] => true
    | cons h1 t1 => match s2 with
                    | [] => true
                    | cons h2 t2 => if (negb ((uint.Z h1) =? (uint.Z h2)))
                                    then false else (coq_equalSlices t1 t2)
                    end
    end.

  Definition coq_equalOperations (o1: Operation.t) (o2: Operation.t) : bool :=
    (coq_equalSlices o1.(Operation.VersionVector) o2.(Operation.VersionVector)) && ((uint.nat o1.(Operation.Data)) =? (uint.nat (o2.(Operation.Data)))).

  Fixpoint coq_sortedInsert (l: list Operation.t) (i: Operation.t) : list Operation.t :=
    match l with
    | [] => [i]
    | cons h t => if (orb (coq_lexicographicCompare h.(Operation.VersionVector) i.(Operation.VersionVector))
                      (coq_equalSlices h.(Operation.VersionVector) i.(Operation.VersionVector)))
                  then (i :: h :: t)%list else (h :: coq_sortedInsert t i)%list
    end.

  Definition coq_mergeOperations (l1: list Operation.t) (l2: list Operation.t) : list Operation.t :=
      let output := fold_left (fun acc element => coq_sortedInsert acc element) l2 l1 in
      snd (fold_left (fun (acc: nat * list Operation.t) element =>
                        let (index, acc) := acc in
                        match (output !! (index + 1)%nat) with
                        | Some v => if (coq_equalOperations element v) then
                                      ((index + 1)%nat, acc)
                                    else
                                      ((index + 1)%nat, acc ++ [element])
                        | None => ((index + 1)%nat, acc ++ [element])
                        end)
          output (0%nat, [])).

  Definition coq_deleteAtIndexOperation (o: list Operation.t) (index: nat) : list Operation.t :=
    (take index o) ++ (drop (index + 1) o).

  Definition coq_deleteAtIndexMessage (m: list Message.t) (index: nat) : list Message.t :=
    (take index m) ++ (drop (index + 1) m).

  Definition coq_getDataFromOperationLog (l: list Operation.t) : u64 :=
    match list_lookup (uint.nat ((length l) - 1)) l with
    | Some v => v.(Operation.Data)
    | None => 0
    end.

  Definition coq_receiveGossip (s: Server.t) (r: Message.t) : Server.t :=
    if length (r.(Message.S2S_Gossip_Operations)) =? 0 then
      s
    else
      let focus := coq_mergeOperations s.(Server.PendingOperations) r.(Message.S2S_Gossip_Operations) in
      let loop_init : nat * Server.t :=
        (0%nat, Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) focus s.(Server.GossipAcknowledgements))
      in
      let loop_step (acc: nat * Server.t) (e: Operation.t) : nat * Server.t :=
        let '(i, s) := acc in
        if coq_oneOffVersionVector s.(Server.VectorClock) e.(Operation.VersionVector) then
          let OperationsPerformed := coq_mergeOperations s.(Server.OperationsPerformed) [e] in
          let VectorClock := coq_maxTS s.(Server.VectorClock) e.(Operation.VersionVector) in
          let PendingOperations := coq_deleteAtIndexOperation s.(Server.PendingOperations) i in
          (i, Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) VectorClock OperationsPerformed s.(Server.MyOperations) PendingOperations s.(Server.GossipAcknowledgements))
        else ((i + 1)%nat, s)
      in
      snd (fold_left loop_step focus loop_init).

  Definition coq_acknowledgeGossip (s: Server.t) (r: Message.t) :=
    let i := r.(Message.S2S_Acknowledge_Gossip_Sending_ServerId) in
    let l : (list u64) := s.(Server.GossipAcknowledgements) in
    if (uint.Z i >=? length l) then s else 
    let prevGossipAcknowledgementsValue : u64 := match s.(Server.GossipAcknowledgements) !! (uint.nat i) with
                                              | Some x => x
                                              | None => 0
                                              end in
    let newGossipAcknowledgements : u64 := coq_maxTwoInts prevGossipAcknowledgementsValue r.(Message.S2S_Acknowledge_Gossip_Index) in
    let gossipAcknowledgements: (list u64) := (<[uint.nat i := newGossipAcknowledgements]> l) in
    Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) gossipAcknowledgements.

  Definition coq_getGossipOperations (s: Server.t) (serverId: u64) : (list Operation.t) :=
    match s.(Server.GossipAcknowledgements) !! uint.nat serverId with
    | Some v => drop (uint.nat v) (s .(Server.MyOperations))
    | None => []
    end.

  Definition coq_processClientRequest (s: Server.t) (r: Message.t) : bool * Server.t * Message.t :=
    if (negb (coq_compareVersionVector s.(Server.VectorClock) r.(Message.C2S_Client_VersionVector))) then
      (false, s, (Message.mk 0 0 0 0 0 [] 0 0 [] 0 0 0 0 0 0 [] 0 0))
    else
      if (uint.nat r.(Message.C2S_Client_OperationType) =? 0) then
        let S2C_Client_Data := coq_getDataFromOperationLog s.(Server.OperationsPerformed) in
        let S2C_Client_VersionVector := s.(Server.VectorClock) in
        let S2C_Client_Number := r.(Message.C2S_Client_Id) in
        let S2C_Server_Id := s.(Server.Id) in
        (true, s, (Message.mk 4 0 0 0 0 [] 0 0 [] 0 0 0 0 0 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number))
      else
        let v := uint.nat (list_lookup_total (uint.nat s.(Server.Id)) s.(Server.VectorClock)) in
        let VectorClock := <[uint.nat s.(Server.Id) := W64 (v + 1)]> s.(Server.VectorClock) in
        let OperationsPerformed := coq_sortedInsert s.(Server.OperationsPerformed) (Operation.mk VectorClock r.(Message.C2S_Client_Data)) in
        let MyOperations := coq_sortedInsert s.(Server.MyOperations) (Operation.mk VectorClock r.(Message.C2S_Client_Data)) in
        let S2C_Client_OperationType := 1 in
        let S2C_Client_Data := 0 in
        let S2C_Client_VersionVector := VectorClock in
        let S2C_Client_Number := r.(Message.C2S_Client_Id) in
        let S2C_Server_Id := s.(Server.Id) in
        (true, Server.mk s.(Server.Id) s.(Server.NumberOfServers) s.(Server.UnsatisfiedRequests) VectorClock OperationsPerformed MyOperations s.(Server.PendingOperations) s.(Server.GossipAcknowledgements), (Message.mk 4 0 0 0 0 [] 0 0 [] 0 0 0 0 1 S2C_Client_Data S2C_Client_VersionVector S2C_Server_Id S2C_Client_Number)).

  Definition coq_processRequest (server: Server.t) (request: Message.t) : Server.t * list Message.t :=
    match uint.nat request.(Message.MessageType) with
    | 0%nat =>
        let '(succeeded, server, reply) := coq_processClientRequest server request in
        if succeeded then
          (server, [reply])
        else
          let UnsatisfiedRequests := server.(Server.UnsatisfiedRequests) ++ [request] in 
          let server := Server.mk server.(Server.Id) server.(Server.NumberOfServers) UnsatisfiedRequests server.(Server.VectorClock) server.(Server.OperationsPerformed) server.(Server.MyOperations) server.(Server.PendingOperations) server.(Server.GossipAcknowledgements) in
          (server, [])
    | 1%nat =>
        let server := coq_receiveGossip server request in
        let focus := server.(Server.UnsatisfiedRequests) in
        let loop_init : nat * (Server.t * list Message.t) :=
          (0%nat, (server, [Message.mk 0 0 0 0 0 [] 0 0 [] 0 (server.(Server.Id)) (request.(Message.S2S_Gossip_Sending_ServerId)) (request.(Message.S2S_Gossip_Index)) 0 0 [] 0 0]))
        in
        let loop_step (acc: nat * (Server.t * list Message.t)) (element: Message.t) : nat * (Server.t * list Message.t) :=
          let '(i, (s, outGoingRequests)) := acc in
          let '(succeeded, s, reply) := coq_processClientRequest s element in
          if succeeded then
            let UnsatisfiedRequests := coq_deleteAtIndexMessage s.(Server.UnsatisfiedRequests) i in
            (i, (Server.mk s.(Server.Id) s.(Server.NumberOfServers) UnsatisfiedRequests s.(Server.VectorClock) s.(Server.OperationsPerformed) s.(Server.MyOperations) s.(Server.PendingOperations) s.(Server.GossipAcknowledgements), outGoingRequests ++ [reply]))
          else
            ((i + 1)%nat, (s, outGoingRequests))
        in
        snd (fold_left loop_step focus loop_init)
    | 2%nat => (coq_acknowledgeGossip server request, [])
    | 3%nat =>
      let loop_init : list Message.t :=
        []
      in
      let loop_step (acc: list Message.t) (index: nat) : list Message.t :=
        if (negb (index =? (uint.nat server.(Server.Id)))) then
          let S2S_Gossip_Sending_ServerId := server.(Server.Id) in
          let S2S_Gossip_Receiving_ServerId := index in
          let S2S_Gossip_Operations := coq_getGossipOperations server index in
          let S2S_Gossip_Index := length (server.(Server.MyOperations)) in
          let message := Message.mk 1 0 0 0 0 [] S2S_Gossip_Sending_ServerId S2S_Gossip_Receiving_ServerId S2S_Gossip_Operations S2S_Gossip_Index 0 0 0 0 0 [] 0 0 in
          acc ++ [message]
        else
          acc
      in
      (server, fold_left loop_step (seq 0%nat (uint.nat server.(Server.NumberOfServers))) loop_init)
    | _ => (server, [])
    end.

End CoqSession.

Export CoqSession.

Section properties.

  Import SessionPrelude.

  Lemma redefine_coq_lexicographicCompare :
    coq_lexicographicCompare = vectorGt.
  Proof.
    reflexivity.
  Defined.

  Lemma redefine_coq_equalSlices :
    coq_equalSlices = vectorEq.
  Proof.
    reflexivity.
  Defined.

  Definition Operation_wf (len : nat) : Operation.t -> Prop :=
    fun o => Forall (fun _ => True) (o .(Operation.VersionVector)) /\ length (o .(Operation.VersionVector)) = len.

  #[global]
  Instance hsEq_Operation (len : nat) : hsEq Operation.t (well_formed := Operation_wf len) :=
    hsEq_preimage _.

  #[global]
  Instance hsOrd_Operation (len : nat) : hsOrd Operation.t (hsEq := hsEq_Operation len) :=
    hsOrd_preimage _.

  Lemma redefine_coq_sortedInsert (len : nat) :
    coq_sortedInsert = sortedInsert (hsOrd := hsOrd_Operation len).
  Proof.
    reflexivity.
  Defined.

  #[local] Hint Resolve @Forall_True : core.

  Lemma aux0_lexicographicCompare (l1 l2 l3: list u64) :
    coq_lexicographicCompare l2 l1 = true ->
    coq_lexicographicCompare l3 l2 = true ->
    coq_lexicographicCompare l3 l1 = true.
  Proof.
    rewrite redefine_coq_lexicographicCompare. 
    intros. eapply vectorGt_transitive; eauto.
  Qed.

  Lemma aux1_lexicographicCompare (l1 l2: list u64) :
    length l1 = length l2 -> 
    l1 ≠ l2 ->
    (coq_lexicographicCompare l2 l1 = false <-> coq_lexicographicCompare l1 l2 = true).
  Proof.
    rewrite redefine_coq_lexicographicCompare. remember (length l1) as len eqn: len_eq.
    pose proof (ltProp_trichotomy (hsOrd := hsOrd_vector len) l1 l2) as claim. simpl in claim.
    symmetry in len_eq. intros len_eq'. symmetry in len_eq'.
    specialize (claim (conj (Forall_True _) len_eq) (conj (Forall_True _) len_eq')).
    destruct claim as [H_lt | [H_eq | H_gt]].
    - rewrite H_lt. intros NE. split.
      + congruence.
      + intros l1_gt_l2. contradiction (ltProp_irreflexivity (hsOrd := hsOrd_vector len) l1 l1); eauto.
        * eapply eqProp_reflexivity; eauto.
        * eapply ltProp_transitivity with (y := l2); eauto.
    - intros NE. contradiction NE. clear NE. rewrite <- vectorEq_true_iff; eauto 2.
      change (eqb (hsEq := hsEq_vector len) l1 l2 = true). rewrite eqb_eq; eauto 2.
    - rewrite H_gt. intros NE. split.
      + congruence.
      + intros _. change (ltb (hsOrd := hsOrd_vector len) l1 l2 = false).
        rewrite ltb_nlt; eauto 2. intros NLT. change (ltb (hsOrd := hsOrd_vector len) l2 l1 = true) in H_gt.
        rewrite ltb_lt in H_gt; eauto 2. contradiction (ltProp_irreflexivity (hsOrd := hsOrd_vector len) l1 l1); eauto.
        * eapply eqProp_reflexivity; eauto.
        * eapply ltProp_transitivity with (y := l2); eauto.
  Qed.

  Lemma aux3_lexicographicCompare (l1 l2: list u64) :
    length l1 = length l2 -> 
    coq_lexicographicCompare l2 l1 = false ->
    coq_lexicographicCompare l1 l2 = false ->
    l1 = l2.
  Proof.
    rewrite redefine_coq_lexicographicCompare. intros. rewrite <- vectorEq_true_iff; eauto 2.
    change (eqb (hsEq := hsEq_vector (length l1)) l1 l2 = true). rewrite eqb_eq; eauto 2.
    pose proof (ltProp_trichotomy (hsOrd := hsOrd_vector (length l1)) l1 l2) as [H_lt | [H_eq | H_gt]]; eauto.
    - rewrite <- ltb_lt in H_lt; eauto 2. simpl in *. congruence.
    - rewrite <- ltb_lt in H_gt; eauto 2. simpl in *. congruence.
  Qed.

  Lemma aux4_lexicographicCompare (l1 l2: list u64) :
    coq_lexicographicCompare l1 l2 = true ->
    coq_equalSlices l1 l2 = false.
  Proof.
    rewrite redefine_coq_lexicographicCompare. rewrite redefine_coq_equalSlices.
    intros. eapply vectorGt_implies_not_vectorEq; eauto 2.
  Qed.

  Lemma aux5_lexicographicCompare (l1 l2: list u64) :
    coq_equalSlices l1 l2 = true ->
    coq_lexicographicCompare l1 l2 = false.
  Proof.
    rewrite redefine_coq_lexicographicCompare. rewrite redefine_coq_equalSlices.
    intros. eapply vectorEq_implies_not_vectorGt; eauto 2.
  Qed.

  Lemma aux0_equalSlices (l1 l2: list u64) :
    length l1 = length l2 ->
    coq_equalSlices l1 l2 = true ->
    l1 = l2.
  Proof.
    rewrite redefine_coq_equalSlices. intros. rewrite <- vectorEq_true_iff; eauto 2.
  Qed.

  Lemma aux1_equalSlices (l1 l2: list u64) :
    length l1 = length l2 ->
    coq_equalSlices l1 l2 = false ->
    l1 ≠ l2.
  Proof.
    rewrite redefine_coq_equalSlices. intros. rewrite <- vectorEq_true_iff; eauto 2.
    rewrite H0; congruence.
  Qed.

  Lemma aux2_equalSlices (l1 l2: list u64) (b: bool) :
    length l1 = length l2 ->
    coq_equalSlices l1 l2 = b ->
    coq_equalSlices l2 l1 = b.
  Proof.
    rewrite redefine_coq_equalSlices. intros. subst b. eapply (eqb_comm (hsEq_A := hsEq_vector (length l1))); eauto.
  Qed.

  Lemma aux3_equalSlices (l: list u64) :
    coq_equalSlices l l = true.
  Proof.
    change (coq_equalSlices l l) with (eqb (hsEq := hsEq_vector (length l)) l l).
    rewrite eqb_eq; eauto 2. eapply eqProp_reflexivity; eauto 2.
  Qed.

  Lemma coq_equalOperations_comm o1 o2
    : coq_equalOperations o1 o2 = coq_equalOperations o2 o1.
  Proof.
    unfold coq_equalOperations. replace Z.eqb with (SessionPrelude.eqb (hsEq := hsEq_Z)) by reflexivity. rewrite eqb_comm; eauto.
    destruct (hsEq_Z .(eqb) (uint.nat o2 .(Operation.Data)) (uint.nat o1 .(Operation.Data))) as [ | ] eqn: H_obs; rewrite eqb_obs in H_obs; eauto.
    - do 2 rewrite andb_true_r. simpl in H_obs. generalize (o1 .(Operation.VersionVector)) as v1. generalize (o2 .(Operation.VersionVector)) as v2.
      induction v2 as [ | v2_hd v2_tl IH], v1 as [ | v1_hd v1_tl]; simpl; eauto.
      rewrite IH. replace Z.eqb with (SessionPrelude.eqb (hsEq := hsEq_Z)) by reflexivity. rewrite eqb_comm; eauto.
    - do 2 rewrite andb_false_r. reflexivity.
  Qed.

  Definition is_sorted (l: list Operation.t) : Prop :=
    ∀ i j, (i < j)%nat -> ∀ o1 o2, l !! i = Some o1 -> l !! j = Some o2 ->
    coq_lexicographicCompare (o2.(Operation.VersionVector)) (o1.(Operation.VersionVector)) = true \/ coq_equalSlices (o2.(Operation.VersionVector)) (o1.(Operation.VersionVector)) = true.

End properties.

Module INVARIANT.

  Record SERVER (s: Server.t) : Prop :=
    SERVER_INVARIANT_INTRO
    { PendingOperations_isSorted: is_sorted s.(Server.PendingOperations)
    ; OperationsPerformed_isSorted: is_sorted s.(Server.OperationsPerformed)
    ; MyOperations_isSorted: is_sorted s.(Server.MyOperations)
    ; Id_inRange: (uint.Z s.(Server.Id) >= 0)%Z /\ (uint.nat s.(Server.Id) < length s.(Server.VectorClock))%nat
    }.

End INVARIANT.

Notation SERVER_INVARIANT := INVARIANT.SERVER.

Section heap.

  Context `{hG: !heapGS Σ}.

  Lemma Forall_Operation_wf l ops (n : nat)
    : ([∗ list] opv;o ∈ ops;l, is_operation opv o n)%I ⊢@{iProp Σ} (⌜Forall (Operation_wf n) l⌝)%I.
  Proof.
    revert ops. induction l as [ | hd tl IH]; intros ops.
    - iIntros "H_big_sepL2". iPureIntro. eauto.
    - iIntros "H_big_sepL2". iPoseProof (big_sepL2_cons_inv_r with "H_big_sepL2") as "(%hd' & %tl' & -> & H_hd & H_tl)".
      iDestruct "H_hd" as "(%H1 & %H2 & H3)". iClear "H3".
      iAssert ⌜Forall (Operation_wf n) tl⌝%I as "%YES1".
      { iApply IH. iExact "H_tl". }
      iPureIntro. econstructor.
      + split.
        * eapply SessionPrelude.Forall_True.
        * done.
      + exact YES1.
  Qed.

  Lemma pers_big_sepL2_is_operation l ops (n : nat)
    : ([∗ list] opv;o ∈ ops;l, is_operation opv o n)%I ⊢@{iProp Σ} (<pers> ([∗ list] opv;o ∈ ops;l, is_operation opv o n))%I.
  Proof.
    iIntros "H_big_sepL2". iApply (big_sepL2_persistently). iApply (big_sepL2_mono (λ k, λ y1, λ y2, is_operation y1 y2 n)%I).
    - intros. iIntros "#H". iApply intuitionistically_into_persistently_1. iModIntro. done.
    - done.
  Qed.

  Lemma pers_is_operation opv o (n : nat)
    : (is_operation opv o n)%I ⊢@{iProp Σ} (<pers> (is_operation opv o n))%I.
  Proof.
    iIntros "#H". done.
  Qed.

  Lemma pers_emp
    : emp ⊢@{iProp Σ} <pers> emp.
  Proof.
    iIntros "#H". done.
  Qed.

  Lemma big_sepL2_is_operation_elim l ops (n: nat) (i: nat) l_i ops_i
    (H_l_i: l !! i = Some l_i)
    (H_ops_i: ops !! i = Some ops_i)
    : ([∗ list] opv;o ∈ ops;l, is_operation opv o n)%I ⊢@{iProp Σ} (is_operation ops_i l_i n)%I.
  Proof.
    rewrite <- take_drop with (l := l) (i := i). rewrite <- take_drop with (l := ops) (i := i). iIntros "H". 
    assert (i < length l)%nat as H1_i by now eapply lookup_lt_is_Some_1.
    assert (i < length ops)%nat as H2_i by now eapply lookup_lt_is_Some_1.  
    iAssert (([∗ list] opv;o ∈ take i ops;take i l, is_operation opv o n) ∗ ([∗ list] opv;o ∈ drop i ops;drop i l, is_operation opv o n))%I with "[H]" as "[H1 H2]".
    { iApply (big_sepL2_app_equiv with "H"). do 2 rewrite length_take. word. }
    destruct (drop i ops) as [ | ops_i' ops_suffix] eqn: H_ops_suffix.
    { apply f_equal with (f := length) in H_ops_suffix. simpl in *. rewrite length_drop in H_ops_suffix. word. }
    iPoseProof (big_sepL2_cons_inv_l with "[$H2]") as "(%l_i' & %l_suffix & %H_l_suffix & H3 & H4)".
    rewrite <- take_drop with (l := l) (i := i) in H_l_i. rewrite <- take_drop with (l := ops) (i := i) in H_ops_i.
    rewrite H_l_suffix in H_l_i. rewrite H_ops_suffix in H_ops_i.
    assert (i = length (take i l)) as H3_i.
    { rewrite length_take. word. }
    assert (i = length (take i ops)) as H4_i.
    { rewrite length_take. word. }
    pose proof (list_lookup_middle (take i l) l_suffix l_i' i H3_i) as EQ_l_i.
    pose proof (list_lookup_middle (take i ops) ops_suffix ops_i' i H4_i) as EQ_ops_i.
    assert (l_i = l_i') as <- by congruence.
    assert (ops_i = ops_i') as <- by congruence.
    iExact "H3".
  Qed.

  Lemma big_sepL2_is_operation_intro (l: list Operation.t) (ops: list (Slice.t * w64)) (n: nat)
    (LENGTH: length l = length ops)
    : (∀ i : nat, ∀ l_i, ∀ ops_i, ⌜(l !! i = Some l_i) /\ (ops !! i = Some ops_i)⌝ -∗ is_operation ops_i l_i n)%I ⊢@{iProp Σ} ([∗ list] opv;o ∈ ops;l, is_operation opv o n)%I.
  Proof.
    revert ops n LENGTH. induction l as [ | l_hd l_tl IH], ops as [ | ops_hd ops_tl]; intros; simpl in *; try congruence.
    - iIntros "#H". iClear "H". done.
    - iIntros "#H". iSplit.
      + iApply "H". instantiate (1 := 0%nat). done.
      + iApply IH. { word. }
        iIntros "%i %l_i %ops_i [%H_l_i %H_ops_i]". iApply "H". instantiate (1 := S i). done.
  Qed.

  Lemma big_sepL2_middle_split {A: Type} {B: Type} {Φ: A -> B -> iProp Σ} {xs: list A} {ys: list B} (i: nat) (x0: A)
    (LOOKUP: xs !! i = Some x0)
    : ([∗ list] x;y ∈ xs;ys, Φ x y)%I ⊢@{iProp Σ} (∃ y0, ∃ ys1, ∃ ys2, ⌜ys = (ys1 ++ y0 :: ys2)%list /\ ys !! i = Some y0⌝ ∗ Φ x0 y0 ∗ ([∗ list] x;y ∈ take i xs;ys1, Φ x y) ∗ ([∗ list] x;y ∈ drop (i + 1)%nat xs;ys2, Φ x y))%I.
  Proof.
    pose proof (take_drop_middle xs i x0 LOOKUP) as claim1.
    assert (i < length xs)%nat as claim2.
    { now eapply lookup_lt_is_Some_1. }
    iIntros "H_big_sepL2".
    iPoseProof (big_sepL2_length with "[$H_big_sepL2]") as "%LENGTH".
    rewrite <- take_drop with (l := xs) (i := i).
    rewrite <- take_drop with (l := ys) (i := i).
    iPoseProof (big_sepL2_app_equiv with "H_big_sepL2") as "[H_prefix H_suffix]".
    { (do 2 rewrite length_take); word. }
    assert (is_Some (ys !! i)) as [y0 H_y0].
    { eapply lookup_lt_is_Some_2; word. }
    iExists y0. iExists (take i ys). iExists (drop (S i) ys).
    pose proof (take_drop_middle ys i y0 H_y0) as claim3.
    iSplitL "".
    { iPureIntro; split; [rewrite claim3; eapply take_drop | rewrite take_drop; trivial]. }
    rewrite <- take_drop with (l := ys) (i := i) in claim3 at -1.
    apply SessionPrelude.app_cancel_l in claim3; rewrite take_drop in claim3.
    rewrite <- claim3.
    iPoseProof (big_sepL2_cons_inv_r with "[$H_suffix]") as "(%x0' & %xs2 & %EQ & H_middle & H_suffix)".
    rewrite <- take_drop with (l := xs) (i := i) in claim1 at -1.
    apply SessionPrelude.app_cancel_l in claim1; rewrite take_drop in claim1.
    assert (x0' = x0) as -> by congruence.
    iSplitL "H_middle".
    { iExact "H_middle". }
    rewrite take_drop; iSplitL "H_prefix".
    { iExact "H_prefix". }
    { rewrite <- drop_drop with (l := xs) (n1 := 1%nat) (n2 := i). rewrite -> EQ. iExact "H_suffix". }
  Qed.

  Lemma big_sepL2_middle_merge {A: Type} {B: Type} {Φ: A -> B -> iProp Σ} {xs: list A} {i: nat} {x0: A} (y0: B) (ys1: list B) (ys2: list B)
    (LOOKUP: xs !! i = Some x0)
    : (Φ x0 y0 ∗ ([∗ list] x;y ∈ take i xs;ys1, Φ x y) ∗ ([∗ list] x;y ∈ drop (i + 1)%nat xs;ys2, Φ x y))%I ⊢@{iProp Σ} ([∗ list] x;y ∈ xs;(ys1 ++ y0 :: ys2)%list, Φ x y)%I.
  Proof.
    pose proof (take_drop_middle xs i x0 LOOKUP) as claim1.
    assert (i < length xs)%nat as claim2.
    { now eapply lookup_lt_is_Some_1. }
    iIntros "(H_middle & H_prefix & H_suffix)".
    replace ([∗ list] x;y ∈ xs;(ys1 ++ y0 :: ys2), Φ x y)%I with ([∗ list] x;y ∈ take i xs ++ x0 :: drop (S i) xs;(ys1 ++ y0 :: ys2), Φ x y)%I by now rewrite claim1.
    rewrite <- drop_drop with (l := xs) (n1 := 1%nat) (n2 := i).
    rewrite <- take_drop with (l := xs) (i := i) in claim1 at -1.
    apply SessionPrelude.app_cancel_l in claim1; rewrite take_drop in claim1.
    rewrite <- claim1; simpl; replace (drop 0 (drop (S i) xs)) with (drop (S i) xs) by reflexivity.
    iApply (big_sepL2_app with "[$H_prefix] [H_middle H_suffix]"); simpl; iFrame.
  Qed.

End heap.
