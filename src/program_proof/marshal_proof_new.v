From Perennial.Helpers Require Import List.

From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.

From Goose.github_com.tchajed Require Import marshal.
From Perennial.goose_lang.lib Require Import encoding.

From iris_string_ident Require Import ltac2_string_ident.

Inductive encodable :=
| EncUInt64 (x:u64)
| EncUInt32 (x:u32)
| EncBytes (bs:list u8)
.

Local Definition Rec := list encodable.

Local Definition encode1 (e:encodable) : list u8 :=
  match e with
  | EncUInt64 x => u64_le x
  | EncUInt32 x => u32_le x
  | EncBytes bs => bs
  end.

Local Definition encode (es:Rec): list u8 := concat (encode1 <$> es).

Notation encoded_length r := (length (encode r)).

Theorem encode_app es1 es2 :
  encode (es1 ++ es2) = encode es1 ++ encode es2.
Proof.
  rewrite /encode.
  rewrite fmap_app.
  rewrite concat_app //.
Qed.

Theorem encode_singleton x :
  encode [x] = encode1 x.
Proof.
  rewrite /encode /=.
  rewrite app_nil_r //.
Qed.

Theorem encode_cons x xs :
  encode (x::xs) = encode1 x ++ encode xs.
Proof.
  change (?x::?xs) with ([x] ++ xs).
  rewrite encode_app encode_singleton //.
Qed.

Theorem encoded_length_singleton x :
  encoded_length [x] = length (encode1 x).
Proof. rewrite encode_singleton //. Qed.

Theorem encoded_length_app (r1 r2:Rec) :
  encoded_length (r1 ++ r2) = (encoded_length r1 + encoded_length r2)%nat.
Proof. rewrite encode_app; len. Qed.

Theorem encoded_length_app1 (r:Rec) (x:encodable) :
  encoded_length (r ++ [x]) = (encoded_length r + length (encode1 x))%nat.
Proof. rewrite encoded_length_app encoded_length_singleton //. Qed.

Section goose_lang.
Context `{!heapG Σ}.
Implicit Types Φ : val → iProp Σ.
Implicit Types (v:val).

Definition has_encoding (data: list u8) (r:Rec) :=
  take (encoded_length r) data = encode r.

Lemma has_encoding_length {data r} :
  has_encoding data r →
  (encoded_length r ≤ length data)%nat.
Proof.
  intros H%(f_equal length).
  move: H; len.
Qed.

Lemma has_encoding_app_characterization data r :
  has_encoding data r ↔
  ∃ extra, data = encode r ++ extra.
Proof.
  split; intros.
  - rewrite /has_encoding in H.
    exists (drop (encoded_length r) data).
    rewrite -[data in data = _](take_drop (encoded_length r)) H //.
  - destruct H as [extra ->].
    rewrite /has_encoding.
    rewrite take_app_le //.
    rewrite take_ge //.
Qed.

Lemma has_encoding_inv data r :
  has_encoding data r →
  ∃ extra, data = encode r ++ extra ∧
           (encoded_length r + length extra = length data)%nat.
Proof.
  intros [extra ->]%has_encoding_app_characterization.
  exists extra; intuition.
  len.
Qed.

Lemma has_encoding_from_app data extra r :
  data = encode r ++ extra →
  has_encoding data r.
Proof.
  intros ->.
  apply has_encoding_app_characterization; eauto.
Qed.

Definition is_enc (enc_v:val) (sz:Z) (r: Rec) (remaining: Z) : iProp Σ :=
  ∃ (s: Slice.t) (off_l: loc) (data: list u8),
    let off := encoded_length r in
    "->" ∷ ⌜enc_v = (slice_val s, (#off_l, #()))%V⌝ ∗
    "Hs" ∷ is_slice_small s byteT 1 data ∗
    "Hs_cap" ∷ is_slice_cap s byteT ∗
    "%Hsz" ∷ ⌜length data = Z.to_nat sz⌝ ∗
    "%Hremaining" ∷ ⌜(off + remaining)%Z = sz⌝ ∗
    "Hoff" ∷ off_l ↦[uint64T] #off ∗
    "%Hoff" ∷ ⌜0 ≤ off ≤ length data⌝ ∗
    "%Hencoded" ∷ ⌜has_encoding data r⌝
.

Theorem wp_new_enc stk E (sz: u64) :
  {{{ True }}}
    NewEnc #sz @ stk; E
  {{{ (enc_v:val), RET enc_v; is_enc enc_v (int.val sz) [] (int.val sz) }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  wp_apply (wp_NewSlice (V:=u8)).
  iIntros (s) "Hs".
  iDestruct (is_slice_split with "Hs") as "[Hs Hcap]".
  wp_apply (typed_mem.wp_AllocAt uint64T); eauto.
  iIntros (off_l) "Hoff".
  wp_pures.
  iApply "HΦ".
  iExists _, _, _; iFrame.
  iPureIntro.
  split_and!; auto; len.
  rewrite /has_encoding //.
Qed.

Lemma has_encoding_app data r data' r' :
  has_encoding data r →
  has_encoding data' r' →
  has_encoding (take (encoded_length r) data ++ data')
                (r ++ r').
Proof.
  intros.
  rewrite H.
  apply has_encoding_inv in H0 as [extra' [-> _]].
  rewrite app_assoc.
  eapply has_encoding_from_app.
  rewrite encode_app -!app_assoc //.
Qed.

Theorem wp_Enc__PutInt stk E enc_v sz r (x:u64) remaining :
  8 ≤ remaining →
  {{{ is_enc enc_v sz r remaining }}}
    Enc__PutInt enc_v #x @ stk; E
  {{{ RET #(); is_enc enc_v sz (r ++ [EncUInt64 x]) (remaining - 8) }}}.
Proof.
  iIntros (Hspace Φ) "Hpre HΦ"; iNamed "Hpre".
  set (off:=encoded_length r) in *.
  wp_call.
  wp_load.
  wp_pures.
  iDestruct (is_slice_small_sz with "Hs") as %Hslice_len.
  wp_apply wp_SliceSkip'.
  { iPureIntro.
    word. }
  iDestruct (is_slice_small_take_drop _ _ _ (U64 off) with "Hs") as "[Hs2 Hs1]".
  { word. }
  replace (int.nat (U64 off)) with off by word.
  wp_apply (wp_UInt64Put with "[$Hs2]").
  { iPureIntro.
    len. }
  iIntros "Hs2".
  iDestruct (is_slice_combine with "Hs1 Hs2") as "Hs"; first len.
  wp_pures.
  wp_load; wp_store.
  rewrite drop_drop.
  iApply "HΦ".
  iExists _, _, _; iFrame.
  rewrite -fmap_take -fmap_drop.
  change (u64_le_bytes x) with (into_val.to_val (V:=u8) <$> u64_le x).
  rewrite -!fmap_app.
  iSplitR; first eauto.
  iFrame "Hs".
  rewrite encoded_length_app1.
  change (length (encode1 (EncUInt64 x))) with 8%nat.
  iSplitR; first by iPureIntro; len.
  iSplitR; first by iPureIntro; len.
  iSplitL "Hoff".
  { iExactEq "Hoff".
    rewrite /named.
    repeat (f_equal; try word). }
  iPureIntro; split.
  - len.
  - subst off.
    apply has_encoding_app; auto.
    eapply has_encoding_from_app; eauto.
Qed.

Theorem wp_Enc__PutInts stk E enc_v sz r (x_s: Slice.t) q (xs:list u64) remaining :
  8*(Z.of_nat $ length xs) ≤ remaining →
  {{{ is_enc enc_v sz r remaining ∗ is_slice_small x_s uint64T q xs }}}
    Enc__PutInts enc_v (slice_val x_s) @ stk; E
  {{{ RET #(); is_enc enc_v sz (r ++ (EncUInt64 <$> xs)) (remaining - 8*(Z.of_nat $ length xs)) ∗
               is_slice_small x_s uint64T q xs }}}.
Proof.
  iIntros (Hbound Φ) "[Henc Hxs] HΦ".
  wp_rec; wp_pures.
  wp_apply (wp_forSlicePrefix
              (λ done todo,
                "Henc" ∷ is_enc enc_v sz
                        (r ++ (EncUInt64 <$> done))
                        (remaining - 8*(Z.of_nat $ length done)))%I
           with "[] [$Hxs Henc]").
  - clear Φ.
    iIntros (???? Hdonetodo) "!>".
    iIntros (Φ) "HI HΦ"; iNamed "HI".
    wp_pures.
    wp_apply (wp_Enc__PutInt with "Henc").
    { apply (f_equal length) in Hdonetodo; move: Hdonetodo; len. }
    iIntros "Henc".
    iApply "HΦ".
    iExactEq "Henc".
    rewrite /named; f_equal; len.
    rewrite fmap_app.
    rewrite -!app_assoc.
    reflexivity.
  - iExactEq "Henc".
    rewrite /named; f_equal; len.
    rewrite app_nil_r //.
  - iIntros "(Hs&HI)"; iNamed "HI".
    iApply "HΦ"; iFrame.
Qed.

Theorem wp_Enc__Finish stk E enc_v r sz remaining :
  {{{ is_enc enc_v sz r remaining }}}
    Enc__Finish enc_v @ stk; E
  {{{ s data, RET slice_val s; is_slice s byteT 1 data ∗ ⌜has_encoding data r⌝ }}}.
Proof.
  iIntros (Φ) "Henc HΦ"; iNamed "Henc"; subst.
  wp_call.
  iApply "HΦ"; iFrame "∗ %".
Qed.

Definition is_dec (dec_v:val) (r:Rec) : iProp Σ :=
  ∃ (s:Slice.t) (off_l:loc) (off: u64) (q:Qp) (data: list u8),
    "->" ∷ ⌜dec_v = (slice_val s, (#off_l, #()))%V⌝ ∗
    "Hoff" ∷ off_l ↦[uint64T] #off ∗
    "%Hoff" ∷ ⌜int.nat off ≤ length data⌝ ∗
    "Hs" ∷ is_slice_small s byteT q data ∗
    "%Henc" ∷ ⌜has_encoding (drop (int.nat off) data) r⌝.

Theorem wp_new_dec stk E s q data r :
  has_encoding data r →
  {{{ is_slice_small s byteT q data }}}
    NewDec (slice_val s) @ stk; E
  {{{ dec_v, RET dec_v; is_dec dec_v r }}}.
Proof.
  iIntros (Henc Φ) "Hs HΦ".
  wp_call.
  wp_apply (typed_mem.wp_AllocAt uint64T); eauto.
  iIntros (off_l) "Hoff".
  wp_pures.
  iApply "HΦ".
  iExists _, _, _, _, _; iFrame.
  iPureIntro.
  split_and!; auto; len.
Qed.

Hint Rewrite encoded_length_singleton : len.

Lemma encoded_length_cons x r :
  encoded_length (x::r) = (length (encode1 x) + encoded_length r)%nat.
Proof. rewrite encode_cons; len. Qed.

Theorem wp_Dec__GetInt stk E dec_v (x: u64) r :
  {{{ is_dec dec_v (EncUInt64 x :: r) }}}
    Dec__GetInt dec_v @ stk; E
  {{{ RET #x; is_dec dec_v r }}}.
Proof.
  iIntros (Φ) "Hdec HΦ"; iNamed "Hdec".
  wp_call.
  wp_load; wp_pures.
  wp_load; wp_store.
  iDestruct (is_slice_small_sz with "Hs") as %Hsz.
  wp_apply wp_SliceSkip'.
  { iPureIntro; word. }
  iDestruct (slice_small_split _ off with "Hs") as "[Hs1 Hs2]".
  { len. }
  wp_apply (wp_UInt64Get_unchanged with "Hs2").
  { eapply has_encoding_inv in Henc as [extra [Henc ?]].
    rewrite -fmap_drop -fmap_take.
    rewrite Henc.
    reflexivity. }
  iIntros "Hs2".
  iDestruct (is_slice_small_take_drop_1 with "[$Hs1 $Hs2]") as "Hs"; first by word.
  iApply "HΦ".
  iExists _, _, _, _, data; iFrame.
  iSplitR; first by auto.
  pose proof (has_encoding_length Henc).
  autorewrite with len in H.
  rewrite encoded_length_cons in H.
  change (length (encode1 _)) with 8%nat in H.
  iSplitR; first iPureIntro.
  { word. }
  iPureIntro.
  replace (int.nat (word.add off 8)) with (int.nat off + 8)%nat by word.
  rewrite -drop_drop.
  apply has_encoding_inv in Henc as [extra [Henc ?]].
  rewrite Henc.
  rewrite encode_cons.
  eapply has_encoding_from_app.
  rewrite -app_assoc.
  rewrite drop_app_ge //.
Qed.

(* TODO: use this to replace list_lookup_lt (it's much easier to remember) *)
Local Tactic Notation "list_elem" constr(l) constr(i) "as" simple_intropattern(x) :=
  let H := fresh "H" x "_lookup" in
  let i := lazymatch type of i with
           | nat => i
           | Z => constr:(Z.to_nat i)
           | u64 => constr:(int.nat i)
           end in
  destruct (list_lookup_lt _ l i) as [x H];
  [ try solve [ len ]
  | ].

(* TODO: upstream to stdpp (which has drop_) *)
Lemma take_0 {A} (l: list A) : take 0%nat l = [].
Proof. reflexivity. Qed.

Theorem wp_Dec__GetInts stk E dec_v (xs: list u64) r (n: u64) :
  length xs = int.nat n →
  {{{ is_dec dec_v ((EncUInt64 <$> xs) ++ r) }}}
    Dec__GetInts dec_v #n @ stk; E
  {{{ (s:Slice.t), RET slice_val s; is_dec dec_v r ∗ is_slice s uint64T 1 xs }}}.
Proof.
  iIntros (Hlen Φ) "Hdec HΦ".
  wp_rec; wp_pures.
  wp_apply (typed_mem.wp_AllocAt (slice.T uint64T)).
  { apply zero_val_ty', has_zero_slice_T. }
  iIntros (s_l) "Hsptr".
  wp_pures.
  wp_apply wp_ref_to; auto.
  iIntros (i_l) "Hi".
  wp_pures.
  wp_apply (wp_forUpto (λ i,
                        let done := take (int.nat i) xs in
                        let todo := drop (int.nat i) xs in
                        "Hdec" ∷ is_dec dec_v ((EncUInt64 <$> todo) ++ r) ∗
                        "*" ∷ ∃ s, "Hsptr" ∷ s_l ↦[slice.T uint64T] (slice_val s) ∗
                                   "Hdone" ∷ is_slice s uint64T 1 done
           )%I with "[] [$Hi Hsptr Hdec]").
  - word.
  - clear Φ.
    iIntros (?) "!>".
    iIntros (Φ) "(HI&Hi&%Hlt) HΦ"; iNamed "HI".
    wp_pures.
    list_elem xs i as x.
    rewrite (drop_S _ _ _ Hx_lookup) /=.
    wp_apply (wp_Dec__GetInt with "Hdec"); iIntros "Hdec".
    wp_load.
    wp_apply (wp_SliceAppend' with "Hdone"); iIntros (s') "Hdone".
    wp_store.
    iApply "HΦ"; iFrame.
    replace (int.nat (word.add i 1)) with (S (int.nat i)) by word.
    iFrame "Hdec".
    iExists _; iFrame.
    erewrite take_S_r; eauto.
  - rewrite drop_0; iFrame "Hdec".
    iExists Slice.nil.
    iFrame.
    rewrite take_0.
    iApply is_slice_nil; auto.
  - iIntros "(HI&Hi)"; iNamed "HI".
    wp_load.
    iApply "HΦ"; iFrame.
    rewrite -> take_ge, drop_ge by len.
    iFrame.
Qed.

End goose_lang.
