From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import environments.
From Perennial.program_logic Require Import weakestpre.
From Perennial.goose_lang Require Import proofmode.
From Perennial.new_goose_lang Require Export typed_mem.impl struct.impl slice.
Require Import Coq.Program.Equality.

Set Default Proof Using "Type".

Section goose_lang.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
  Context {ext_ty: ext_types ext}.

  Inductive has_go_type_aux (F : val → go_type → Prop) : val → go_type → Prop :=
  | has_go_type_aux_bool (b : bool) : has_go_type_aux F #b boolT
  | has_go_type_aux_uint64 (x : w64) : has_go_type_aux F #x uint64T
  | has_go_type_aux_uint32 (x : w32) : has_go_type_aux F #x uint32T
  | has_go_type_aux_uint16 : has_go_type_aux F nil uint16T
  | has_go_type_aux_uint8 (x : w8) : has_go_type_aux F #x uint8T

  | has_go_type_aux_int64 (x : w64) : has_go_type_aux F #x int64T
  | has_go_type_aux_int32 (x : w32) : has_go_type_aux F #x int32T
  | has_go_type_aux_int16 : has_go_type_aux F nil int16T
  | has_go_type_aux_int8 (x : w8) : has_go_type_aux F #x int8T

  | has_go_type_aux_string (s : string) : has_go_type_aux F #(str s) stringT
  | has_go_type_aux_slice elem (s : slice.t) : has_go_type_aux F (slice_val s) (sliceT elem)
  | has_go_type_aux_slice_nil elem : has_go_type_aux F slice_nil (sliceT elem)

  (* This avoids requiring (NoDup d) so we can avoid having to require that for zero_val.
     So, the Hfields statement is a Forall over decls, to deal with the fact
     that decls might include the same field name multiple times.
   *)
  | has_go_type_aux_struct
      (d : descriptor) fvs
      (Hfields : Forall (λ '(f, t),
                     match (assocl_lookup fvs f) with
                     | None => True
                     | Some v => F v t
                     end
                  ) d)
    : has_go_type_aux F (struct.mk_f d fvs) (structT d)
  | has_go_type_aux_ptr (l : loc) : has_go_type_aux F #l ptrT
  | has_go_type_aux_func f e v : has_go_type_aux F (RecV f e v) funcT
  | has_go_type_aux_func_nil : has_go_type_aux F nil funcT

  (* FIXME: interface_val *)
  | has_go_type_aux_interface (s : slice.t) : has_go_type_aux F (slice_val s) interfaceT
  | has_go_type_aux_interface_nil : has_go_type_aux F interface_nil interfaceT

  | has_go_type_aux_mapT kt vt (l : loc) : has_go_type_aux F #l (mapT kt vt)
  | has_go_type_aux_chanT t (l : loc) : has_go_type_aux F #l (chanT t)
  .

  Definition has_go_type_step_indexed (n : nat) : val → go_type → Prop :=
    fold_right (λ _ f, has_go_type_aux f) (λ _ _, False) (replicate n unit).

  Definition has_go_type (v : val) (t : go_type) : Prop :=
    ∃ n, has_go_type_step_indexed n v t
  .

  Inductive has_go_abstract_type : val → go_abstract_type → Prop :=
  | has_go_abstract_type_bool (b : bool) : has_go_abstract_type #b cellT
  | has_go_abstract_type_uint64 (x : w64) : has_go_abstract_type #x cellT
  | has_go_abstract_type_uint32 (x : w32) : has_go_abstract_type #x cellT
  (* | has_go_abstract_type_uint16 (x : w16) : has_go_abstract_type #x cellT *)
  | has_go_abstract_type_uint8 (x : w8) : has_go_abstract_type #x cellT
  | has_go_abstract_type_int64 (x : w64) : has_go_abstract_type #x cellT
  | has_go_abstract_type_int32 (x : w32) : has_go_abstract_type #x cellT
  (* | has_go_abstract_type_int16 (x : w16) : has_go_abstract_type #x cellT *)
  | has_go_abstract_type_int8 (x : w8) : has_go_abstract_type #x cellT
  | has_go_abstract_type_string (x : string) : has_go_abstract_type #(str x) cellT
  | has_go_abstract_type_ptr (x : loc) : has_go_abstract_type #x cellT
  | has_go_abstract_type_func f x e : has_go_abstract_type (RecV f x e) cellT
  | has_go_abstract_type_nil : has_go_abstract_type nil cellT
  | has_go_abstract_type_unit : has_go_abstract_type #() unitT
  | has_go_abstract_type_prod
      (v1 v2 : val) (t1 t2 : go_abstract_type)
      (Ht1 : has_go_abstract_type v1 t1)
      (Ht2 : has_go_abstract_type v2 t2)
    : has_go_abstract_type (v1, v2) (prodT t1 t2)
  .

  Lemma zero_val_has_go_type t :
    has_go_type (zero_val t) t.
  Proof.
    dependent induction t; simpl.
    all: try (exists 1%nat; econstructor).
    replace (foldr PairV _ _) with (struct.mk_f decls []).
    { exists 1%nat. econstructor. simpl in *. apply Forall_true. intros. destruct x. done. }
    induction decls.
    { done. }
    {
      destruct a.
      simpl.
      rewrite IHdecls.
      simpl. done.
    }
  Qed.

  Fixpoint type_depth (t : go_type) : nat :=
    match t with
    | structT decls => S (fold_right max O (type_depth ∘ snd <$> decls))
    | _ => O
    end
  .

  Local Lemma has_go_type_to_abstract_inductive :
    ∀ (n : nat), ∀ t, (type_depth t <= n)%nat → ∀ v, has_go_type v t → has_go_abstract_type v (go_type_interp t).
  Proof.
    intros n. induction n as [| n IH]; intros ? Hdepth ? Hty.
    + (* type depth 0 case *)
      inversion Hty as [n Hty_si].
      destruct n; first by exfalso.
      destruct t; simpl in *; try (inversion Hty_si; subst; repeat constructor).
      lia.
    + (* type depth (n+1) case *)
      inversion Hty as [m Hty_si].
      destruct m; first by exfalso.
      destruct t; cbn in *; try (inversion Hty_si; subst; repeat constructor).

      (* structT case *)
      clear Hty_si.
      induction decls; first constructor.
      destruct a. simpl.
      apply Forall_cons in Hfields as [Hfield Hfields].
      constructor.
      ++ clear IHdecls.
         destruct assocl_lookup; cbn in *.
         - apply IH; [lia| eexists _; apply Hfield ] .
         - apply IH; [ lia | apply zero_val_has_go_type ].
      ++ apply IHdecls.
         +++ cbn in *. etransitivity; [|exact Hdepth].
             apply le_n_S. lia.
         +++ exists (S m)%nat. econstructor.
             apply Hfields.
         +++ done.
  Qed.
  Lemma has_go_type_to_abstract v t :
    has_go_type v t → has_go_abstract_type v (go_type_interp t).
  Proof. eapply has_go_type_to_abstract_inductive. done. Qed.

  Definition typed_pointsto_def l (dq : dfrac) (t : go_type) (v : val): iProp Σ :=
    (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j) ↦{dq} vj) ∗ ⌜ has_go_type v t ⌝)%I.
  Definition typed_pointsto_aux : seal (@typed_pointsto_def). Proof. by eexists. Qed.
  Definition typed_pointsto := typed_pointsto_aux.(unseal).
  Definition typed_pointsto_eq : @typed_pointsto = @typed_pointsto_def := typed_pointsto_aux.(seal_eq).

  Notation "l ↦[ t ] dq v" := (typed_pointsto l dq t v%V)
                                   (at level 20, dq custom dfrac at level 1, t at level 50,
                                    format "l  ↦[ t ] dq  v") : bi_scope.

  Ltac unseal := rewrite ?typed_pointsto_eq /typed_pointsto_def.

  Global Instance typed_pointsto_timeless l t q v: Timeless (l ↦[t]{q} v).
  Proof. unseal. apply _. Qed.

  Global Instance typed_pointsto_fractional l t v: fractional.Fractional (λ q, l ↦[t]{#q} v)%I.
  Proof. unseal. apply _. Qed.

  Global Instance typed_pointsto_as_fractional l t v q: fractional.AsFractional
                                                     (l ↦[t]{#q} v)
                                                     (λ q, l ↦[t]{#q} v)%I q.
  Proof. constructor; auto. apply _. Qed.

  Local Lemma has_go_abstract_type_len {v t} :
    has_go_abstract_type v t ->
    length (flatten_struct v) = (go_abstract_type_size t).
  Proof.
    unfold go_type_size.
    induction 1; simpl; auto.
    rewrite app_length. lia.
  Qed.

  Local Lemma wp_AllocAt t stk E v :
    has_go_type v t ->
    {{{ True }}}
      ref v @ stk; E
    {{{ l, RET #l; l ↦[t] v }}}.
  Proof.
    iIntros (Hty Φ) "_ HΦ".
    wp_apply wp_allocN_seq; first by word.
    change (uint.nat 1) with 1%nat; simpl.
    iIntros (l) "[Hl _]".
    iApply "HΦ".
    unseal.
    iSplitL; auto.
    rewrite Z.mul_0_r loc_add_0.
    iFrame.
  Qed.

  Lemma wp_ref_to t stk E v :
    has_go_type v t ->
    {{{ True }}}
      ref_to t v @ stk; E
    {{{ l, RET #l; l ↦[t] v }}}.
  Proof.
    iIntros (Hty Φ) "_ HΦ".
    wp_call.
    wp_apply (wp_AllocAt t); auto.
  Qed.


  Lemma wp_ref_of_zero stk E t :
    {{{ True }}}
      ref (zero_val t) @ stk; E
    {{{ l, RET #l; l ↦[t] (zero_val t) }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_apply (wp_AllocAt t); eauto.
    apply zero_val_has_go_type.
  Qed.

  Lemma wp_typed_load stk E q l t v :
    {{{ ▷ l ↦[t]{q} v }}}
      load_ty t #l @ stk; E
    {{{ RET v; l ↦[t]{q} v }}}.
  Proof.
    iIntros (Φ) ">Hl HΦ".
    unseal.
    iDestruct "Hl" as "[Hl %]".
    iAssert (▷ (([∗ list] j↦vj ∈ flatten_struct v, (l +ₗ j)↦{q} vj) -∗ Φ v))%I with "[HΦ]" as "HΦ".
    { iIntros "!> HPost".
      iApply "HΦ".
      iSplit; eauto. }
    unfold load_ty.
    apply has_go_type_to_abstract in H.
    hnf in H.
    iInduction H as [ | | | | | | | | | | | | ] "IH" forall (l Φ);
      subst; simpl; wp_pures; rewrite ?loc_add_0 ?right_id.
    1-11: wp_apply (wp_load with "[$]"); auto.
    + by iApply "HΦ".
    + rewrite big_opL_app.
      iDestruct "Hl" as "[Hv1 Hv2]".
      wp_apply ("IH" with "Hv1"); iIntros "Hv1".
      wp_apply ("IH1" with "[Hv2]"); [ | iIntros "Hv2" ].
      { erewrite has_go_abstract_type_len; [|done].
        setoid_rewrite Z.mul_1_r.
        setoid_rewrite Nat2Z.inj_add.
        setoid_rewrite loc_add_assoc.
        iFrame. }
      wp_pures.
      iApply "HΦ"; iFrame.
      erewrite has_go_abstract_type_len; [|done].
      setoid_rewrite Z.mul_1_r.
      setoid_rewrite Nat2Z.inj_add.
      setoid_rewrite loc_add_assoc.
      by iFrame.
  Qed.

End goose_lang.
