From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import merkle.

From Perennial.program_proof.pav Require Import classes misc cryptoffi cryptoutil.
From Perennial.program_proof Require Import std_proof.

Section internal.
Context `{!heapGS Σ}.

Inductive tree : Type :=
  (* Cut only exists for proof checking trees. *)
  | Cut : list w8 → tree
  | Empty : tree
  | Leaf : list w8 → tree
  | Interior : list tree → tree.

Fixpoint has_entry (tr : tree) (id : list w8) (node : tree) : Prop :=
  match tr with
  | Cut _ => False
  | Empty => id = [] ∧ tr = node
  | Leaf val => id = [] ∧ tr = node
  | Interior children =>
    match id with
    | [] => False
    | pos :: rest =>
      ∃ child, children !! Z.to_nat (word.unsigned pos) = Some child ∧ has_entry child rest node
    end
  end.

(* The core invariant that defines the recursive hashing structure of merkle trees. *)
Fixpoint is_node_hash (tr : tree) (hash : list w8) : iProp Σ :=
  match tr with
  | Cut hash' => ⌜hash = hash' ∧ length hash' = 32%nat⌝
  | Empty => is_hash [W8 0] hash
  | Leaf val => is_hash (val ++ [W8 1]) hash
  | Interior children =>
    ∃ (child_hashes : list (list w8)),
    let map_fn := (λ c h, is_node_hash c h) in
    ([∗ list] child_fn;hash' ∈ (map_fn <$> children);child_hashes,
      child_fn hash') ∗
    is_hash (concat child_hashes ++ [W8 2]) hash
  end%I.

#[global]
Instance is_node_hash_timeless tr hash : Timeless (is_node_hash tr hash).
Proof. Admitted.

#[global]
Instance is_node_hash_persistent tr hash : Persistent (is_node_hash tr hash).
Proof. Admitted.

Lemma node_hash_len tr hash :
  is_node_hash tr hash -∗ ⌜length hash = 32%nat⌝.
Proof.
  iIntros "Htree".
  destruct tr.
  { iDestruct "Htree" as "[%Heq %Hlen]". naive_solver. }
  1-2: iDestruct (is_hash_len with "Htree") as "%Hlen"; naive_solver.
  {
    iDestruct "Htree" as (ch) "[_ Htree]".
    by iDestruct (is_hash_len with "Htree") as "%Hlen".
  }
Qed.

Lemma concat_len_eq {A : Type} sz (l1 l2 : list (list A)) :
  concat l1 = concat l2 →
  (Forall (λ l, length l = sz) l1) →
  (Forall (λ l, length l = sz) l2) →
  0 < sz →
  l1 = l2.
Proof.
  intros Heq_concat Hlen_l1 Hlen_l2 Hsz.
  apply (f_equal length) in Heq_concat as Heq_concat_len.
  do 2 rewrite concat_length in Heq_concat_len.
  generalize dependent l2.
  induction l1 as [|a1]; destruct l2 as [|a2]; simpl;
    intros Heq_concat Hlen_l2 Heq_concat_len;
    decompose_Forall; eauto with lia.
  apply (f_equal (take (length a1))) in Heq_concat as Htake_concat.
  apply (f_equal (drop (length a1))) in Heq_concat as Hdrop_concat.
  rewrite <-H in Htake_concat at 2.
  rewrite <-H in Hdrop_concat at 2.
  do 2 rewrite take_app_length in Htake_concat.
  do 2 rewrite drop_app_length in Hdrop_concat.
  rewrite Htake_concat.
  apply (app_inv_head_iff [a2]).
  apply IHl1; eauto with lia.
Qed.

(* TODO: is this necessary? can we just apply node_hash_len when necessary? *)
Lemma sep_node_hash_len ct ch :
  ([∗ list] t;h ∈ ct;ch, is_node_hash t h) -∗
  ⌜Forall (λ l, length l = 32%nat) ch⌝.
Proof.
  iIntros "Htree".
  iDestruct (big_sepL2_impl _ (λ _ _ h, ⌜length h = 32%nat⌝%I) with "Htree []") as "Hlen_sepL2".
  {
    iIntros "!>" (???) "_ _ Hhash".
    by iDestruct (node_hash_len with "Hhash") as "Hlen".
  }
  iDestruct (big_sepL2_const_sepL_r with "Hlen_sepL2") as "[_ %Hlen_sepL1]".
  iPureIntro.
  by apply Forall_lookup.
Qed.

Lemma disj_empty_leaf digest v :
  is_node_hash Empty digest -∗
  is_node_hash (Leaf v) digest -∗
  False.
Proof.
  iIntros "Hempty Hleaf".
  iDestruct (is_hash_inj with "Hempty Hleaf") as "%Heq".
  iPureIntro.
  destruct v as [|a]; [naive_solver|].
  (* TODO: why doesn't list_simplifier or solve_length take care of this? *)
  apply (f_equal length) in Heq.
  rewrite length_app in Heq.
  simpl in *.
  lia.
Qed.

(* Ownership of a logical merkle tree. *)
Definition own_node_except' (recur : option (list w8) -d> loc -d> tree -d> iPropO Σ) : option (list w8) -d> loc -d> tree -d> iPropO Σ :=
  (λ path ptr_tr tr,
    match tr with
    (* We should never have cuts in in-memory trees. *)
    | Cut _ => False
    | Empty => True
    | Leaf val =>
      ∃ sl_val hash sl_hash,
      "Hval" ∷ own_slice_small sl_val byteT (DfracOwn 1) val ∗
      "Hptr_val" ∷ ptr_tr ↦[node :: "val"] (slice_val sl_val) ∗
      "Hhash" ∷ own_slice_small sl_hash byteT (DfracOwn 1) hash ∗
      "Hsl_hash" ∷ ptr_tr ↦[node :: "hash"] (slice_val sl_hash) ∗
      "#His_hash" ∷ match path with
        | None => is_node_hash tr hash
        | _ => True
        end
    | Interior children =>
      ∃ hash sl_hash sl_children ptr_children sl_val,
      "Hhash" ∷ own_slice_small sl_hash byteT (DfracOwn 1) hash ∗
      "Hsl_children" ∷ own_slice_small sl_children ptrT (DfracOwn 1) ptr_children ∗
      "Hptr_val" ∷ ptr_tr ↦[node :: "val"] (slice_val sl_val) ∗  (* XXX: keeping this to ensure ptr_tr is not null *)
      "Hptr_children" ∷ ptr_tr ↦[node :: "Children"] (slice_val sl_children) ∗
      "Hchildren" ∷
        ([∗ list] idx ↦ child;ptr_child ∈ children;ptr_children,
           match path with
           | Some (a :: path) => if decide (uint.nat a = idx) then ▷ recur (Some path) ptr_child child
                               else ▷ recur None ptr_child child
           | None => ▷ recur None ptr_child child
           | Some [] => ▷ recur None ptr_child child
           end
        ) ∗
      "#His_hash" ∷ match path with
      | None => is_node_hash tr hash
      | _ => True
      end
    end)%I.

Local Instance own_node_except'_contractive : Contractive own_node_except'.
Proof. Admitted.

Definition own_node_except : option (list w8) → loc → tree → iProp Σ := fixpoint own_node_except'.

Lemma own_node_except_unfold path ptr obj :
  own_node_except path ptr obj ⊣⊢ (own_node_except' own_node_except) path ptr obj.
Proof.
  apply (fixpoint_unfold own_node_except').
Qed.

Definition tree_to_map (tr : tree) : gmap (list w8) (list w8) :=
  let fix traverse (tr : tree) (acc : gmap (list w8) (list w8)) (id : list w8) :=
    match tr with
    | Cut _ => acc
    | Empty => acc
    | Leaf val => <[id:=val]>acc
    | Interior children =>
      (* Grab all entries from the children, storing the ongoing id. *)
      (foldr
        (λ child (pIdxAcc:(Z * gmap (list w8) (list w8))),
          let acc' := traverse child pIdxAcc.2 (id ++ [W8 pIdxAcc.1])
          in (pIdxAcc.1 + 1, acc'))
        (0, acc) children
      ).2
    end
  in traverse tr ∅ [].

Lemma own_node_except_mono path2 path1 root tr :
  match path1, path2 with
  | Some a, Some b => prefix a b
  | None, _ => True
  | _, _ => False
  end →
  own_node_except path1 root tr -∗
  own_node_except path2 root tr.
Proof.
Admitted.

End internal.

Section external.
Context `{!heapGS Σ}.

(* own_merkle denotes ownership of a merkle tree containing some entries. *)
Definition own_merkle ptr_tr entries : iProp Σ :=
  ∃ tr root,
  "%Htree" ∷ ⌜tree_to_map tr = entries⌝ ∗
  "Hnode" ∷ own_node_except None root tr ∗
  "Hroot" ∷ ptr_tr ↦[Tree :: "root"] #root.

(* is_dig says that the tree with these entries has this digest. *)
Definition is_dig entries dig : iProp Σ :=
  ∃ tr,
  "%Htree" ∷ ⌜tree_to_map tr = entries⌝ ∗
  "#Hdig" ∷ is_node_hash tr dig.

Global Instance is_dig_func : Func is_dig.
Proof. Admitted.
Global Instance is_dig_inj : InjRel is_dig.
Proof. Admitted.

(* is_merkle_entry says that (id, val) is contained in the tree with this digest.
we use (val : option string) instead of (val : tree) bc there are really
only two types of nodes we want to allow. *)
Definition is_merkle_entry id val digest : iProp Σ :=
  ∃ tr,
  is_node_hash tr digest ∧
  ⌜has_entry tr id
    match val with
    | None => Empty
    | Some val' => Leaf val'
    end⌝.

(* is_merkle_entry_with_map says that if you know an entry as well
as the underlying map, you can combine those to get a pure map fact. *)
Lemma is_merkle_entry_with_map id val dig m :
  is_merkle_entry id val dig -∗ is_dig m dig -∗ ⌜ m !! id = val ⌝.
Proof. Admitted.

Lemma is_merkle_entry_inj' pos rest val1 val2 digest :
  is_merkle_entry (pos :: rest) val1 digest -∗
  is_merkle_entry (pos :: rest) val2 digest -∗
  ∃ digest',
  is_merkle_entry rest val1 digest' ∗
  is_merkle_entry rest val2 digest'.
Proof.
  iIntros "Hval1 Hval2".
  rewrite /is_merkle_entry.
  iDestruct "Hval1" as (tr1) "[Htree1 %Hcont1]".
  iDestruct "Hval2" as (tr2) "[Htree2 %Hcont2]".
  destruct tr1 as [| | |ct1], tr2 as [| | |ct2]; try naive_solver.

  (* Get contains pred and is_node_hash for children. *)
  destruct Hcont1 as [child1 [Hlist1 Hcont1]].
  destruct Hcont2 as [child2 [Hlist2 Hcont2]].
  iDestruct "Htree1" as (ch1) "[Htree1 Hdig1]".
  iDestruct "Htree2" as (ch2) "[Htree2 Hdig2]".
  iDestruct (big_sepL2_fmap_l (λ c h, is_node_hash c h) with "Htree1") as "Htree1".
  iDestruct (big_sepL2_fmap_l (λ c h, is_node_hash c h) with "Htree2") as "Htree2".

  (* Use is_hash ch1/ch2 digest to prove that child hashes are same. *)
  iDestruct (sep_node_hash_len with "Htree1") as "%Hlen_ch1".
  iDestruct (sep_node_hash_len with "Htree2") as "%Hlen_ch2".

  iDestruct (is_hash_inj with "Hdig1 Hdig2") as "%Heq".
  apply app_inv_tail in Heq.
  assert (ch1 = ch2) as Hch.
  { apply (concat_len_eq 32); eauto with lia. }
  subst ch1.

  (* Finish up. *)
  iDestruct (big_sepL2_lookup_1_some with "Htree1") as (h1) "%Hlook1"; [done|].
  iDestruct (big_sepL2_lookup_1_some with "Htree2") as (h2) "%Hlook2"; [done|].
  iDestruct (big_sepL2_lookup with "Htree1") as "Hhash1"; [done..|].
  iDestruct (big_sepL2_lookup with "Htree2") as "Hhash2"; [done..|].
  clear Hlook1 Hlook2.

  iFrame "%∗".
Qed.

Lemma is_merkle_entry_inj id val1 val2 digest :
  is_merkle_entry id val1 digest -∗
  is_merkle_entry id val2 digest -∗
  ⌜val1 = val2⌝.
Proof.
  iInduction (id) as [|a] "IH" forall (digest);
    iIntros "Hpath1 Hpath2".
  {
    rewrite /is_merkle_entry.
    iDestruct "Hpath1" as (tr1) "[Htree1 %Hcont1]".
    iDestruct "Hpath2" as (tr2) "[Htree2 %Hcont2]".
    destruct tr1 as [| | |ct1], tr2 as [| | |ct2], val1, val2; try naive_solver.
    { iExFalso. iApply (disj_empty_leaf with "[$] [$]"). }
    { iExFalso. iApply (disj_empty_leaf with "[$] [$]"). }
    destruct Hcont1 as [_ Hleaf1].
    destruct Hcont2 as [_ Hleaf2].
    inversion Hleaf1; subst l; clear Hleaf1.
    inversion Hleaf2; subst l0; clear Hleaf2.
    iDestruct (is_hash_inj with "[$Htree1] [$Htree2]") as "%Heq".
    by list_simplifier.
  }
  {
    iDestruct (is_merkle_entry_inj' with "[$Hpath1] [$Hpath2]") as (digest') "[Hval1 Hval2]".
    by iSpecialize ("IH" $! digest' with "[$Hval1] [$Hval2]").
  }
Qed.

End external.

Module pathProof.
Record t :=
  mk {
    id: list w8;
    nodeHash: list w8;
    digest: list w8;
    childHashes: list (list (list w8));
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_id sl_nodeHash sl_digest sl_childHashes,
  "Hid" ∷ own_slice_small sl_id byteT (DfracOwn 1) obj.(id) ∗
  "Hptr_id" ∷ ptr ↦[pathProof :: "id"] (slice_val sl_id) ∗
  "HnodeHash" ∷ own_slice_small sl_nodeHash byteT (DfracOwn 1) obj.(nodeHash) ∗
  "Hptr_nodeHash" ∷ ptr ↦[pathProof :: "nodeHash"] (slice_val sl_nodeHash) ∗
  "Hdigest" ∷ own_slice_small sl_digest byteT (DfracOwn 1) obj.(digest) ∗
  "Hptr_digest" ∷ ptr ↦[pathProof :: "digest"] (slice_val sl_digest) ∗
  "#HchildHashes" ∷ is_Slice3D sl_childHashes obj.(childHashes) ∗
  "Hptr_childHashes" ∷ ptr ↦[pathProof :: "childHashes"] (slice_val sl_childHashes) ∗
  "%Hlen_id_depth" ∷ ⌜length obj.(id) = length obj.(childHashes)⌝ ∗
  "%Hlen_id_ub" ∷ ⌜length obj.(id) ≤ 32⌝.
End local_defs.
End pathProof.

Module GetReply.
Record t :=
  mk {
    Val: list w8;
    Digest: list w8;
    ProofTy: bool;
    Proof: list (list (list w8));
    Error: bool;
  }.

Section local_defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_Val sl_Dig sl_Proof,
  "HVal" ∷ ptr ↦[GetReply :: "val"] (slice_val sl_Val) ∗
  "Hptr_Val" ∷ own_slice_small sl_Val byteT (DfracOwn 1) obj.(Val) ∗
  "HDig" ∷ ptr ↦[GetReply :: "Digest"] (slice_val sl_Dig) ∗
  "Hptr_Dig" ∷ own_slice_small sl_Dig byteT (DfracOwn 1) obj.(Digest) ∗
  "HProofTy" ∷ ptr ↦[GetReply :: "ProofTy"] #obj.(ProofTy) ∗
  "HProof" ∷ ptr ↦[GetReply :: "Proof"] (slice_val sl_Proof) ∗
  "Hsl_Proof" ∷ is_Slice3D sl_Proof obj.(Proof) ∗
  "HErr" ∷ ptr ↦[GetReply :: "Error"] #obj.(Error).
End local_defs.
End GetReply.

Section wps.
Context `{!heapGS Σ}.

Lemma wp_Tree_Digest ptr_tr entries :
  {{{
    "Htree" ∷ own_merkle ptr_tr entries
  }}}
  Tree__Digest #ptr_tr
  {{{
    sl_dig dig, RET (slice_val sl_dig);
    "Htree" ∷ own_merkle ptr_tr entries ∗
    "Hdig" ∷ own_slice_small sl_dig byteT (DfracOwn 1) dig ∗
    "#HisDig" ∷ is_dig entries dig
  }}}.
Proof. Admitted.

Lemma wp_Tree_Put ptr_tr entries sl_id id sl_val val d0 d1 :
  {{{
    "Htree" ∷ own_merkle ptr_tr entries ∗
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "Hval" ∷ own_slice_small sl_val byteT d1 val
  }}}
  Tree__Put #ptr_tr (slice_val sl_id) (slice_val sl_val)
  {{{
    sl_dig dig sl_proof proof (err : bool),
    RET ((slice_val sl_dig), (slice_val sl_proof), #err);
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "%Hvalid_id" ∷ ⌜ length id = hash_len → err = false ⌝ ∗
    "Herr" ∷
      if negb err then
        "Htree" ∷ own_merkle ptr_tr (<[id:=val]>entries) ∗
        "Hdig" ∷ own_slice_small sl_dig byteT (DfracOwn 1) dig ∗
        "#HisDig" ∷ is_dig (<[id:=val]>entries) dig ∗
        "Hproof" ∷ is_Slice3D sl_proof proof
      else
        "Htree" ∷ own_merkle ptr_tr entries
  }}}.
Proof.
  iIntros (?) "H HΦ". iNamed "H".
  wp_rec.
  wp_pures.
  iDestruct (own_slice_small_sz with "Hid") as %Hsz_id.
  wp_apply wp_slice_len.
  wp_pures.
  wp_if_destruct.
  { (* return an error. *)
    wp_pures.
    replace (slice.nil) with (slice_val Slice.nil) by done.
    iApply "HΦ".
    iModIntro. iFrame. iPureIntro.
    word.
  }
  wp_rec.
  wp_pures.
  iNamed "Htree".
  wp_loadField.
  wp_pures.

  (* weaken to loop invariant. *)
  iDestruct (own_node_except_mono (Some id) with "[$]") as "Hnode".
  { done. }

  wp_bind (if: _ then _ else _)%E.
  wp_apply (wp_wand _ _ _ (λ _,
                             ∃ (root : loc) tr,
                               "Hroot" ∷ ptr_tr ↦[Tree::"root"] #root ∗
                               "Hnode" ∷ own_node_except (Some id) root tr ∗
                               "%Htree" ∷ ⌜ tree_to_map tr = entries ⌝
              )%I
             with "[Hnode Hroot]").
  {
    wp_if_destruct.
    2:{ iModIntro. iFrame "∗%". }
    wp_rec.
    wp_apply wp_NewSlice.
    iIntros (?) "Hsl".
    wp_pures. wp_apply wp_allocStruct.
    { val_ty. }

    (* establish that tr = Empty *)
    iDestruct (own_node_except_unfold with "Hnode") as "Hnode".
    rewrite /own_node_except'.
    destruct tr.
    { done. }
    2:{ iNamed "Hnode".
        by iDestruct (struct_field_pointsto_not_null with "Hptr_val") as %Hn.
    }
    2:{ iNamed "Hnode".
        by iDestruct (struct_field_pointsto_not_null with "Hptr_val") as %Hn.
    }
    iClear "Hnode".
    iIntros (?) "Hnode".
    iDestruct (struct_fields_split with "Hnode") as "Hnode".
    iNamed "Hnode".
    wp_storeField.
    iFrame.
    iExists Empty.
    iSplitL; last done.
    by iApply own_node_except_unfold.
  }
  iIntros (?) "HifInv".
  wp_pures. clear v.
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (nodePath_ptr) "HnodePath_ptr".
  wp_pures.
  iNamed "HifInv".
  wp_loadField.
  wp_load.
  rewrite zero_slice_val.
  wp_apply (wp_SliceAppend (V:=loc) with "[]").
  { iApply own_slice_zero. }
  iIntros (?) "HnodePath".
  simpl.
  wp_store.
  wp_apply wp_ref_to.
  { val_ty. }
  iIntros (pathIdx_ptr) "HpathIdx".
  wp_pures.
  wp_apply (wp_forUpto' with "[$HpathIdx]").
Admitted.

Lemma wp_Tree_Get ptr_tr entries sl_id id d0 :
  {{{
    "Htree" ∷ own_merkle ptr_tr entries ∗
    "Hid" ∷ own_slice_small sl_id byteT d0 id
  }}}
  Tree__Get #ptr_tr (slice_val sl_id)
  {{{
    ptr_reply reply, RET #ptr_reply;
    "Hreply" ∷ GetReply.own ptr_reply reply ∗
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "%Hvalid_id" ∷ ⌜ length id = hash_len → reply.(GetReply.Error) = false ⌝ ∗
    "Herr" ∷
      if negb reply.(GetReply.Error) then
        "Htree" ∷ own_merkle ptr_tr (<[id:=reply.(GetReply.Val)]>entries) ∗
        "#HisDig" ∷ is_dig (<[id:=reply.(GetReply.Val)]>entries) reply.(GetReply.Digest)
      else
        "Htree" ∷ own_merkle ptr_tr entries
  }}}.
Proof. Admitted.

Lemma wp_Tree_DeepCopy ptr_tr entries :
  {{{
    "Htree" ∷ own_merkle ptr_tr entries
  }}}
  Tree__DeepCopy #ptr_tr
  {{{
    ptr_new, RET #ptr_new;
    "Htree" ∷ own_merkle ptr_tr entries ∗
    "HnewTree" ∷ own_merkle ptr_new entries
  }}}.
Proof. Admitted.

Lemma wp_node_getHash_null :
  {{{ True }}}
  node__getHash #null
  {{{
    sl_hash hash, RET (slice_val sl_hash);
    "Hhash" ∷ own_slice_small sl_hash byteT (DfracOwn 1) hash ∗
    "#His_hash" ∷ is_node_hash Empty hash
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  rewrite /node__getHash.
  wp_apply wp_SliceSingleton; [val_ty|];
    iIntros (sl_data) "Hdata".
  wp_apply (wp_Hash with "[Hdata]").
  {
    iDestruct (slice.own_slice_to_small with "Hdata") as "Hdata".
    rewrite /own_slice_small.
    instantiate (1:=[_]).
    iFrame.
  }
  iIntros (??) "H"; iNamed "H".
  iApply "HΦ".
  iFrame "#∗".
Qed.

Lemma wp_isValidHashSl sl_data data :
  {{{
    "#Hdata" ∷ is_Slice2D sl_data data
  }}}
  isValidHashSl (slice_val sl_data)
  {{{
    (ok : bool), RET #ok;
    if bool_decide ok then
      "%Hlen" ∷ ([∗ list] l ∈ data, ⌜length l = 32%nat⌝)
    else True%I
  }}}.
Proof. Admitted.

Lemma wp_pathProof_check ptr_proof proof val :
  {{{
    "Hproof" ∷ pathProof.own ptr_proof proof ∗
    let node := match val with
    | None => Empty
    | Some val' => Leaf val'
    end in
    "Hhash" ∷ is_node_hash node proof.(pathProof.nodeHash)
  }}}
  pathProof__check #ptr_proof
  {{{
    (err : bool), RET #err;
    if negb err then
      "Hpath" ∷ is_merkle_entry proof.(pathProof.id) val proof.(pathProof.digest)
    else True%I
  }}}.
Proof.
  iIntros (Φ) "H HΦ"; iNamed "H"; iNamed "Hproof".
  rewrite /pathProof__check.
  wp_apply wp_ref_to; [val_ty|];
    iIntros (ptr_err) "Hptr_err".
  wp_loadField.
  wp_apply wp_ref_to; [val_ty|]. iIntros (ptr_currHash) "HcurrHash".
  wp_loadField.
  wp_apply wp_slice_len.
  wp_apply wp_ref_to; [val_ty|]; iIntros (ptr_loopIdx) "HloopIdx".
  iDestruct ("HchildHashes") as (?) "H"; iNamed "H".
  iMod (own_slice_small_persist with "HnodeHash") as "#HnodeHash".
  iDestruct (big_sepL2_length with "Hsep_dim0") as "%Hlen_childHashes".
  iDestruct (own_slice_small_sz with "Hsl_dim0") as "%Hlen_list_dim0".

  (* Entering the main loop. *)
  set for_inv :=
    (λ loopIdx, ∃ sl_currHash currHash (err : bool),
      "Hid" ∷ own_slice_small sl_id byteT (DfracOwn 1) proof.(pathProof.id) ∗
      "Hptr_id" ∷ ptr_proof ↦[pathProof :: "id"] sl_id ∗
      "Hptr_childHashes" ∷ ptr_proof ↦[pathProof :: "childHashes"] sl_childHashes ∗
      "#Hsl_currHash" ∷ own_slice_small sl_currHash byteT DfracDiscarded currHash ∗
      "Hptr_currHash" ∷ ptr_currHash ↦[slice.T byteT] sl_currHash ∗
      "Hptr_err" ∷ ptr_err ↦[boolT] #err ∗
      "Herr_pred" ∷ if negb err then
        "Hpath_val" ∷ is_merkle_entry
          (drop (length proof.(pathProof.id) - (Z.to_nat (word.unsigned loopIdx)))
          proof.(pathProof.id)) val currHash
      else True)%I : w64 → iProp Σ.
  wp_apply (wp_forUpto for_inv with "[] [$Hid $Hptr_id $Hptr_childHashes $HloopIdx $HcurrHash $HnodeHash $Hptr_err Hhash]"); [word|..].
  2: {
    assert ((length proof.(pathProof.id) - 0%nat)%nat = length proof.(pathProof.id)) as H by word;
      iEval (rewrite H); clear H.
    iEval (rewrite drop_all).
    iFrame.
    destruct val; done.
  }
  {
    iEval (rewrite /for_inv); clear for_inv.
    iIntros (loopIdx Φ2) "!> (Hinv & HloopIdx & %HloopBound) HΦ2";
      iNamed "Hinv".
    wp_load.
    wp_apply (wp_loadField with "[$Hptr_childHashes]");
      iIntros "Hptr_childHashes".

    (* Note: move all the sep fetches into one block, like this. *)
    (* TODO: change all uint out of backwords compat thing *)
    assert (∃ (sl_dim1' : Slice.t),
      list_dim0 !! uint.nat (length list_dim0 - 1 - uint.nat loopIdx) =
      Some sl_dim1') as [sl_dim1' Hlook_sl_dim1'].
    { apply lookup_lt_is_Some. word. }
    iDestruct (big_sepL2_lookup_1_some with "Hsep_dim0") as %[obj_dim1' Hlook_obj_dim1']; [done|].
    iDestruct (big_sepL2_lookup with "Hsep_dim0") as (list_dim1') "H";
      [done..|]; iNamed "H".
    iDestruct (own_slice_small_sz with "Hsl_dim1") as "%Hlen_list_dim1'".
    iDestruct (big_sepL2_length with "Hsep_dim1") as "%Hlen_obj_dim1'".
    iDestruct (own_slice_small_sz with "Hid") as "%Hlen_id".

    (* Rewrite this early since it appears in multiple sub-terms. *)
    replace (word.sub (word.sub sl_childHashes.(Slice.sz) 1) loopIdx) with
      (W64 (length list_dim0 - 1 - uint.nat loopIdx)) by word.

    wp_apply (wp_SliceGet with "[$Hsl_dim0]"); [done|]; iIntros "_".
    wp_apply wp_slice_len.

    wp_if_destruct.
    { wp_store. iApply "HΦ2". by iFrame "#∗". }
    replace (word.sub 256 1) with (W64 255) in Heqb;
      [|word]; rename Heqb into Hsz_sl_dim1'.
    wp_apply (wp_isValidHashSl with "[$Hsl_dim1 $Hsep_dim1]").
      iIntros (ok) "H".
    wp_if_destruct.
    { wp_store. iApply "HΦ2". by iFrame "#∗". }
    iSimpl in "H"; iNamed "H"; rename Hlen into Hhash_len_obj_dim1'.

    wp_apply (wp_loadField with "[$Hptr_id]");
      iIntros "Hptr_id".
    assert (∃ (pos : w8),
      proof.(pathProof.id) !! uint.nat (length list_dim0 - 1 - uint.nat loopIdx) =
      Some pos) as [pos Hlook_pos].
    { apply lookup_lt_is_Some. word. }
    wp_apply (wp_SliceGet with "[$Hid]"); [done|];
      iIntros "Hid".

    (* TODO: word should know this. *)
    assert (length list_dim1' = 255%nat) as H255_list_dim1'.
    { rewrite Hlen_list_dim1'. rewrite Hsz_sl_dim1'. word. }
    (* Note: this slows down word for some reason. *)
    pose proof (word.unsigned_range pos) as Hpos_bound.

    (* The complicated slice splitting logic. *)
    iDestruct (own_slice_small_wf with "Hsl_dim1") as "%Hwf_sl_dim1".
    iDestruct (slice_small_split _ (W64 (word.unsigned pos)) with "Hsl_dim1") as "[Hsl_before Hsl_after]".
    (* TODO: word should know this. *)
    { rewrite u8_to_u64_Z. lia. }
    wp_apply wp_SliceTake.
    { rewrite u8_to_u64_Z. lia. }
    wp_apply wp_SliceSkip.
    { rewrite u8_to_u64_Z. lia. }
    iEval (rewrite u8_to_u64_Z) in "Hsl_before".
    iEval (rewrite u8_to_u64_Z) in "Hsl_after".

    wp_apply wp_ref_of_zero; [done|];
      iIntros (ptr_hr) "Hptr_hr".
    iEval (rewrite zero_slice_val) in "Hptr_hr".
    iDestruct (own_slice_small_nil byteT (DfracOwn 1) (Slice.nil)) as "Hnil"; [done|].
    wp_apply (wp_HasherWriteSl with "[$Hptr_hr $Hnil $Hsl_before]").
    {
      iApply big_sepL2_prefix.
      4: iFrame "#".
      1: apply prefix_take.
      1: apply (prefix_take _ (uint.nat pos)).
      { do 2 rewrite length_take. lia. }
    }
    iIntros (sl_hr) "H"; iNamed "H".
    wp_load.
    wp_apply (wp_HasherWrite with "[$Hptr_hr $Hhr $Hsl_currHash]");
      clear sl_hr; iIntros (sl_hr) "H"; iNamed "H".
    wp_apply (wp_HasherWriteSl with "[$Hptr_hr $Hhr $Hsl_after]").
    {
      iApply big_sepL2_suffix.
      4: iFrame "#".
      1: apply suffix_drop.
      1: apply (suffix_drop _ (uint.nat pos)) .
      { do 2 rewrite length_drop. lia. }
    }
    clear sl_hr; iIntros (sl_hr) "H"; iNamed "H".
    wp_apply wp_SliceSingleton; [val_ty|];
      iIntros (sl_tag) "H";
      iDestruct (slice.own_slice_to_small with "H") as "Hsl_tag".
    iAssert (own_slice_small _ _ _ [W8 2]) with "Hsl_tag" as "Hsl_tag".
    iMod (own_slice_small_persist with "Hsl_tag") as "#Hsl_tag".
    wp_apply (wp_HasherWrite with "[$Hptr_hr $Hhr $Hsl_tag]").
    clear sl_hr; iIntros (sl_hr) "H"; iNamed "H".
    wp_load.
    wp_apply (wp_HasherSumNil with "Hhr");
      iIntros (sl_hash hash) "H"; iNamed "H".
    wp_store.
    iMod (own_slice_small_persist with "Hsl_hash") as "#Hsl_hash".
    iClear (sl_tag) "HnodeHash Hsl_before Hsl_after Hnil Hsl_tag".

    (* Done with code, now re-establish loop inv. *)

    destruct err; iNamed "Herr_pred"; iApply "HΦ2"; iFrame "#∗"; [done|].
    rewrite /is_merkle_entry.
    iDestruct "Herr_pred" as "[Htr_hash %Htr_contains]".
    iExists (Interior (
      ((λ h, Cut h) <$> (take (uint.nat pos) obj_dim1')) ++
      [tr] ++
      ((λ h, Cut h) <$> (drop (uint.nat pos) obj_dim1')))).
    iIntros "!>".
    iSplit.
    {
      iExists (
        (take (uint.nat pos) obj_dim1') ++
        [currHash] ++
        (drop (uint.nat pos) obj_dim1')).
      iSplit.
      {
        iEval (rewrite fmap_app).
        iApply big_sepL2_app.
        {
          iEval (rewrite <-list_fmap_compose).
          iApply big_sepL2_fmap_l.
          iApply big_sepL_sepL2_diag.
          iApply big_sepL_take.
          iPureIntro.
          naive_solver.
        }
        iEval (rewrite fmap_cons).
        iApply big_sepL2_cons.
        iFrame.
        {
          iEval (rewrite <-list_fmap_compose).
          iApply big_sepL2_fmap_l.
          iApply big_sepL_sepL2_diag.
          iApply (big_sepL_drop (λ _ _, _)).
          iPureIntro.
          naive_solver.
        }
      }
      iEval (do 2 rewrite concat_app).
      by list_simplifier.
    }
    iPureIntro.
    clear Hpos_bound.
    rewrite (drop_S _ pos _ _).
    2: { rewrite <-Hlook_pos. f_equal. word. }
    (* TODO: is there a good way of extracting this goal automatically? *)
    replace (S (length proof.(pathProof.id) - uint.nat (word.add loopIdx 1))) with
      ((length proof.(pathProof.id) - uint.nat loopIdx)%nat) by word.
    exists tr.
    split; [|done].
    rewrite (lookup_app_r _ _ _ _).
    2: {
      rewrite length_fmap.
      rewrite (length_take_le _ _ _); [done|].
      pose proof (word.unsigned_range pos) as Hpos_bound.
      lia.
    }
    rewrite length_fmap.
    rewrite (length_take_le _ _ _).
    2: { pose proof (word.unsigned_range pos) as Hpos_bound. lia. }
    replace ((uint.nat pos - uint.nat pos)%nat) with (0%nat) by lia.
    naive_solver.
  }

  (* Last chunk of code after for loop. *)
  iEval (rewrite /for_inv); clear for_inv.
  iIntros "[H _]"; iNamed "H".
  wp_load.
  wp_if_destruct; [by iApply "HΦ"|]; clear err Heqb.
  iSimpl in "Herr_pred"; iNamed "Herr_pred".
  wp_apply (wp_loadField with "Hptr_digest");
    iIntros "Hptr_digest".
  wp_load.
  (* TODO: framing doesn't work here. $Hsl_currHash frames this persis thing twice. *)
  wp_apply (wp_BytesEqual with "[Hdigest]"); [iFrame "#∗"|];
    iIntros "[_ Hdigest]".
  wp_if_destruct; [by iApply "HΦ"|]; rename Heqb into Heq_currHash.
  iEval (replace ((length proof.(pathProof.id) - uint.nat sl_childHashes.(Slice.sz))%nat)
    with (0%nat) by word) in "Hpath_val".
  iEval (rewrite drop_0 Heq_currHash) in "Hpath_val".
  by iApply "HΦ".
Qed.

(* is_merkle_proof says that the merkle proof gives rise to a cut tree
that has digest dig. and is_merkle_entry id val dig.
the cut tree is the existential tree in is_merkle_entry. *)
Definition is_merkle_proof (proof : list (list (list w8))) (id : list w8)
    (val : option (list w8)) (dig : list w8) : iProp Σ.
Proof. Admitted.

Global Instance is_merkle_proof_persis proof id val dig :
  Persistent (is_merkle_proof proof id val dig).
Proof. Admitted.

Lemma is_merkle_proof_to_entry proof id val dig :
  is_merkle_proof proof id val dig -∗ is_merkle_entry id val dig.
Proof. Admitted.

Definition wp_CheckProof sl_id sl_val sl_dig (proofTy : bool) sl_proof proof (id val dig : list w8) d0 d1 d2 :
  {{{
    "#Hsl_proof" ∷ is_Slice3D sl_proof proof ∗
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "Hval" ∷ own_slice_small sl_val byteT d1 val ∗
    "Hdig" ∷ own_slice_small sl_dig byteT d2 dig
  }}}
  CheckProof #proofTy (slice_val sl_proof) (slice_val sl_id) (slice_val sl_val) (slice_val sl_dig)
  {{{
    (err : bool), RET #err;
    "Hid" ∷ own_slice_small sl_id byteT d0 id ∗
    "Hval" ∷ own_slice_small sl_val byteT d1 val ∗
    "Hdig" ∷ own_slice_small sl_dig byteT d2 dig ∗
    let expected_val := (if proofTy then Some val else None) in
    "Hgenie" ∷ (is_merkle_proof proof id expected_val dig ∗-∗ ⌜ err = false ⌝)
  }}}.
Proof. Admitted.

End wps.
