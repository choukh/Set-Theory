(** Based on "Elements of Set Theory" Chapter 5 Part 4 **)
(** Coq coding by choukh, July 2020 **)

Require Export ZFC.EST5_3.

Local Ltac nz := try (apply nzIntE1; assumption).
Local Ltac mr := apply intMul_ran; nauto.
Local Ltac ar := apply intAdd_ran; nauto.
Local Ltac amr := apply intAdd_ran; apply intMul_ran; nauto.
Local Ltac nzmr := apply nzIntMul_ranI; nauto.

(*** EST第五章4：有理数的序，整数嵌入，关于逆元的运算律 ***)

Close Scope Rat_scope.
Open Scope Int_scope.

Lemma intPos_sn : ∀ n, intPos (Int (S n)).
Proof with nauto.
  intros. apply intLt...
  rewrite add_0_r, add_0_r... apply suc_has_0. apply ωI.
Qed.
Hint Immediate intPos_sn : number_hint.

Lemma intNeg_sn : ∀ n, intNeg (-Int (S n)).
Proof. intros. apply int_pos_neg. nauto. Qed.
Hint Immediate intNeg_sn : number_hint.

Lemma intMul_pos_prod : ∀a b ∈ ℤ,
  intPos a → intPos b → intPos (a ⋅ b).
Proof with nauto.
  intros a Ha b Hb Hpa Hpb. unfold intPos.
  rewrite <- (intMul_0_l b)...
  apply intLt_both_side_mul...
Qed.

Lemma intMul_pos_factor : ∀a b ∈ ℤ,
  intPos b → intPos (a ⋅ b) → intPos a.
Proof with neauto.
  intros a Ha b Hb Hpb Hpp.
  destruct (classic (a = Int 0)).
  - subst a. exfalso. rewrite intMul_0_l in Hpp...
    eapply intLt_not_refl; revgoals...
  - apply intLt_connected in H as []... exfalso.
    eapply intLt_both_side_mul in H...
    rewrite intMul_0_l in H...
    eapply intLt_not_refl; revgoals.
    eapply intLt_tranr... mr.
Qed.

Lemma intMul_neg_factor : ∀a b ∈ ℤ,
  intPos b → intNeg (a ⋅ b) → intNeg a.
Proof with neauto.
  intros a Ha b Hb Hpb Hpp.
  destruct (classic (a = Int 0)).
  - subst a. exfalso. rewrite intMul_0_l in Hpp...
    eapply intLt_not_refl; revgoals...
  - apply intLt_connected in H as []... exfalso.
    eapply intLt_both_side_mul in H.
    apply H in Hpb as Hc.
    rewrite (intMul_comm b), intMul_0_l in Hc...
    eapply intLt_not_refl; revgoals.
    eapply intLt_tranr... mr. nauto. auto. auto.
Qed.

Lemma pQuotE_ratPosDenom : ∀r ∈ ℚ, ∃a ∈ ℤ, ∃b ∈ ℤ',
  r = [<a, b>]~ ∧ intPos b.
Proof with nauto.
  intros r Hr.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst.
  apply nzIntE0 in Hb as Hb0.
  apply intLt_connected in Hb0 as [Hnb|Hpb]; nz...
  - assert (Hnaz: -a ∈ ℤ) by (apply intAddInv_int; auto).
    assert (Hnbz: -b ∈ ℤ') by (apply intAddInv_inzInt; auto).
    exists (-a). split... exists (-b). split...
    split. apply rat_ident... rewrite intMul_addInv_lr; nz...
    apply int_neg_pos...
  - exists a. split... exists b. split...
Qed.

(** 有理数的序 **)

Lemma rat_orderable : ∀ a b a' b' c d c' d',
  intPos b → intPos d → intPos b' → intPos d' →
  <a, b> ~ <a', b'> → <c, d> ~ <c', d'> →
  a ⋅ d <𝐳 c ⋅ b ↔ a' ⋅ d' <𝐳 c' ⋅ b'.
Proof.
  intros * Hpb Hpd Hpb' Hpd' H1 H2.
  apply planeEquivE2 in H1 as [H1 [Ha [Hb [Ha' Hb']]]].
  apply planeEquivE2 in H2 as [H2 [Hc [Hd [Hc' Hd']]]].
  assert (Had: a⋅d ∈ ℤ) by (mr;nz).
  assert (Hcb: c⋅b ∈ ℤ) by (mr;nz).
  assert (Hb'd': b'⋅d' ∈ ℤ) by (mr;nz).
  assert (Hpb'd': intPos (b'⋅d')) by (apply intMul_pos_prod; auto; nz).
  rewrite (intLt_both_side_mul _ Had _ Hcb _ Hb'd' Hpb'd').
  rewrite (intMul_assoc a), (intMul_comm d), (intMul_assoc b'),
    <- (intMul_assoc a), (intMul_assoc c), (intMul_comm b),
    (intMul_comm b'), (intMul_assoc d'), <- (intMul_assoc c),
    H1, H2, (intMul_assoc a'), (intMul_comm b), (intMul_assoc d'),
    <- (intMul_assoc a'), (intMul_comm d), (intMul_assoc c'),
    (intMul_comm d), (intMul_assoc b'), <- (intMul_assoc c');
    [|auto;nz;mr;nz..].
  assert (Ha'd': a'⋅d' ∈ ℤ) by (mr;nz).
  assert (Hc'b': c'⋅b' ∈ ℤ) by (mr;nz).
  assert (Hbd: b⋅d ∈ ℤ) by (mr;nz).
  assert (Hpbd: intPos (b⋅d)) by (apply intMul_pos_prod; auto; nz).
  erewrite <- (intLt_both_side_mul _ Ha'd' _ Hc'b' _ Hbd Hpbd).
  reflexivity.
Qed.

(* 有理数的小于关系 *)
Definition RatLt : set := Relation ℚ ℚ (λ r s,
  let u := RatProj r in let v := RatProj s in
  let a := π1 u in let b := π2 u in
  let c := π1 v in let d := π2 v in
  a ⋅ d <𝐳 c ⋅ b
).
Notation "a <𝐪 b" := (<a, b> ∈ RatLt) (at level 70).

Lemma ratLtI : ∀a ∈ ℤ, ∀b ∈ ℤ', ∀c ∈ ℤ, ∀d ∈ ℤ',
  intPos b → intPos d → 
  a ⋅ d <𝐳 c ⋅ b → [<a, b>]~ <𝐪 [<c, d>]~.
Proof with eauto.
  intros a Ha b Hb c Hc d Hd Hpb Hpd Hlt.
  apply SepI. apply CProdI; apply pQuotI... zfcrewrite.
  pose proof (ratProj a Ha b Hb)
    as [a' [Ha' [b' [Hb' [H11 [H12 [_ Hpb']]]]]]].
  pose proof (ratProj c Hc d Hd)
    as [c' [Hc' [d' [Hd' [H21 [H22 [_ Hpd']]]]]]].
  pose proof ratEquiv_equiv as [_ [_ [Hsym _]]].
  rewrite H11, H21. simpl. zfcrewrite.
  eapply rat_orderable; revgoals...
Qed.

Lemma ratLtE : ∀ r s, r <𝐪 s → ∃a ∈ ℤ, ∃b ∈ ℤ', ∃c ∈ ℤ, ∃d ∈ ℤ',
  intPos b ∧ intPos d ∧
  r = [<a, b>]~ ∧ s = [<c, d>]~ ∧ a ⋅ d <𝐳 c ⋅ b.
Proof with eauto.
  intros r s Hlt. apply SepE in Hlt as [H1 H2].
  apply CProdE1 in H1 as [Hr Hs]; zfcrewrite.
  apply pQuotE_ratPosDenom in Hr as [a [Ha [b [Hb [Hr Hpb]]]]].
  apply pQuotE_ratPosDenom in Hs as [c [Hc [d [Hd [Hs Hpd]]]]]. subst.
  exists a. split... exists b. split...
  exists c. split... exists d. split... repeat split...
  pose proof (ratProj a Ha b Hb)
    as [a' [Ha' [b' [Hb' [H11 [H12 [_ Hpb']]]]]]].
  pose proof (ratProj c Hc d Hd)
    as [c' [Hc' [d' [Hd' [H21 [H22 [_ Hpd']]]]]]].
  rewrite H11, H21 in H2. simpl in H2. zfcrewrite.
  eapply rat_orderable; revgoals...
Qed.

Lemma ratLt : ∀a ∈ ℤ, ∀b ∈ ℤ', ∀c ∈ ℤ, ∀d ∈ ℤ',
  intPos b → intPos d →
  [<a, b>]~ <𝐪 [<c, d>]~ ↔ a ⋅ d <𝐳 c ⋅ b.
Proof with eauto.
  intros a Ha b Hb c Hc d Hd Hpb Hpd. split; intros.
  - apply SepE in H as [H1 H2].
    apply CProdE1 in H1 as [Hr Hs]; zfcrewrite.
    pose proof (ratProj a Ha b Hb)
      as [a' [Ha' [b' [Hb' [H11 [H12 [_ Hpb']]]]]]].
    pose proof (ratProj c Hc d Hd)
      as [c' [Hc' [d' [Hd' [H21 [H22 [_ Hpd']]]]]]].
    rewrite H11, H21 in H2. simpl in H2. zfcrewrite.
    eapply rat_orderable; revgoals...
  - apply ratLtI...
Qed.

Lemma ratLt_not_refl : ∀r ∈ ℚ, r <𝐪 r → ⊥.
Proof with eauto.
  intros r Hr Hc.
  apply pQuotE_ratPosDenom in Hr as [a [Ha [b [Hb [Hr Hpb]]]]]. subst r.
  apply ratLt in Hc... eapply intLt_not_refl; revgoals... mr;nz.
Qed.

Lemma ratNeqE : ∀a ∈ ℤ, ∀b ∈ ℤ', ∀c ∈ ℤ, ∀d ∈ ℤ',
  [<a, b>]~ ≠ [<c, d>]~ → a ⋅ d ≠ c ⋅ b.
Proof with auto.
  intros a Ha b Hb c Hc d Hd Hnq Heq.
  apply Hnq. apply rat_ident...
Qed.

Lemma ratLt_rel : rel RatLt ℚ.
Proof with auto.
  intros x Hx. apply SepE in Hx as []...
Qed.

Lemma ratLt_tranr : tranr RatLt.
Proof with auto.
  intros x y z H1 H2.
  assert (H1' := H1). assert (H2' := H2).
  apply ratLtE in H1' as [a [Ha [b [Hb [c [Hc [d [Hd
    [Hpb [Hpd [Hx [Hy _]]]]]]]]]]]].
  apply ratLtE in H2' as [_ [_ [_ [_ [e [He [f [Hf
    [_ [Hpf [_ [Hz _]]]]]]]]]]]]. subst x y z.
  apply ratLt in H1... apply ratLt in H2... apply ratLt...
  assert (H1': a ⋅ d ⋅ f <𝐳 c ⋅ b ⋅ f)
    by (apply intLt_both_side_mul; auto; nz; mr; nz).
  assert (H2': c ⋅ f ⋅ b <𝐳 e ⋅ d ⋅ b)
    by (apply intLt_both_side_mul; auto; nz; mr; nz).
  rewrite
    (intMul_assoc a), (intMul_comm d), <- (intMul_assoc a),
    (intMul_assoc c), (intMul_comm b), <- (intMul_assoc c)
    in H1'; nz...
  rewrite
    (intMul_assoc e), (intMul_comm d), <- (intMul_assoc e)
    in H2'; nz...
  eapply intLt_both_side_mul; revgoals.
  eapply intLt_tranr; revgoals; eauto. apply Hpd. nz. mr;nz. mr;nz.
Qed.

Lemma ratLt_irreflexive : irreflexive RatLt ℚ.
Proof with auto.
  intros [x [Hx Hlt]]. apply ratLtE in Hlt
    as [a [Ha [b [Hb [c [Hc [d [Hd [Hpb [Hpd [H1 [H2 Hlt]]]]]]]]]]]].
  subst x. apply rat_ident in H2... rewrite H2 in Hlt.
  eapply intLt_not_refl; revgoals; eauto; mr; nz.
Qed.

Lemma ratLt_connected : connected RatLt ℚ.
Proof with auto.
  intros x Hx y Hy Hnq.
  apply pQuotE_ratPosDenom in Hx as [a [Ha [b [Hb [Hx Hpb]]]]].
  apply pQuotE_ratPosDenom in Hy as [c [Hc [d [Hd [Hy Hpd]]]]].
  subst x y. apply ratNeqE in Hnq...
  apply intLt_connected in Hnq as []; [| |mr;nz..].
  + left. apply ratLtI...
  + right. apply ratLtI...
Qed.

Lemma ratLt_trich : trich RatLt ℚ.
Proof with auto.
  eapply trich_iff. apply ratLt_rel. apply ratLt_tranr. split.
  apply ratLt_irreflexive. apply ratLt_connected.
Qed.

Theorem ratLt_totalOrd : totalOrd RatLt ℚ.
Proof with auto.
  split. apply ratLt_rel. split. apply ratLt_tranr.
  apply ratLt_trich.
Qed.

Close Scope Int_scope.
Open Scope Rat_scope.

Definition ratPos : set → Prop := λ r, Rat 0 <𝐪 r.
Definition ratNeg : set → Prop := λ r, r <𝐪 Rat 0.

Lemma rat_pos_neg : ∀ r, ratPos r → ratNeg (-r).
Proof with nauto.
  intros. apply ratLtE in H
    as [a [Ha [b [Hb [c [Hc [d [Hd [Hpb [Hpd [H1 [H2 Hlt]]]]]]]]]]]].
  apply rat_ident in H1...
  rewrite intMul_0_l, intMul_ident in H1; nz...
  subst r a. rewrite intMul_0_l in Hlt; nz.
  assert (Hnc: (-c)%z ∈ ℤ) by (apply intAddInv_int; auto).
  rewrite ratAddInv... apply ratLt...
  rewrite intMul_0_l, intMul_ident; nz... apply int_pos_neg.
  eapply intMul_pos_factor; revgoals; eauto; nz.
Qed.

Lemma rat_neg_pos : ∀ r, ratNeg r → ratPos (-r).
Proof with nauto.
  intros. apply ratLtE in H
    as [a [Ha [b [Hb [c [Hc [d [Hd [Hpb [Hpd [H1 [H2 Hlt]]]]]]]]]]]].
  apply rat_ident in H2...
  rewrite intMul_0_l, intMul_ident in H2; nz...
  subst r c. rewrite intMul_0_l in Hlt; nz.
  assert (Hna: (-a)%z ∈ ℤ) by (apply intAddInv_int; auto).
  rewrite ratAddInv... apply ratLt...
  rewrite intMul_0_l, intMul_ident; nz... apply int_neg_pos.
  eapply intMul_neg_factor; revgoals; eauto; nz.
Qed.

Lemma ratPos_sm_sn : ∀ m n, ratPos ([<Int (S m), Int (S n)>]~).
Proof with nauto.
  intros. apply ratLt...
  rewrite intMul_0_l, intMul_ident... apply intPos_sn.
Qed.
Hint Immediate ratPos_sm_sn : number_hint.

Lemma ratPos_sn : ∀ n, ratPos (Rat (S n)).
Proof. intros. unfold Rat. nauto. Qed.
Hint Immediate ratPos_sn : number_hint.

Lemma ratNeg_sn : ∀ n, ratNeg (-Rat (S n)).
Proof. intros. apply rat_pos_neg. nauto. Qed.
Hint Immediate ratNeg_sn : number_hint.

Lemma ratPos_r_sn : ∀ n, ratPos (Rat (S n))⁻¹.
Proof. intros n. unfold Rat. rewrite ratMulInv; nauto. Qed.
Hint Immediate ratPos_r_sn : number_hint.

Definition RatAbs : set → set := λ r,
  match (ixm (ratPos (-r))) with
  | inl _ => -r
  | inr _ => r
  end.

Notation "| r |" := (RatAbs r) (at level 60) : Rat_scope.
Notation " r ≥ s " := (r = s ∨ s <𝐪 r) (at level 70): Rat_scope.

Lemma ratAbs_leq_0 : ∀r ∈ ℚ, |r| ≥ Rat 0.
Proof with nauto.
  intros r Hr. unfold RatAbs.
  destruct (ixm (ratPos (-r)))...
  destruct (classic (r = Rat 0))...
  apply ratLt_connected in H as []...
  apply rat_neg_pos in H. exfalso. auto.
Qed.

Close Scope Rat_scope.
Open Scope Int_scope.

Theorem ratLt_both_side_add : ∀ r s t ∈ ℚ,
  r <𝐪 s ↔ (r + t <𝐪 s + t)%q.
Proof with auto.
  intros r Hr s Hs t Ht.
  apply pQuotE_ratPosDenom in Hr as [a [Ha [b [Hb [Hr Hpb]]]]].
  apply pQuotE_ratPosDenom in Hs as [c [Hc [d [Hd [Hs Hpd]]]]].
  apply pQuotE_ratPosDenom in Ht as [e [He [f [Hf [Ht Hpf]]]]].
  subst r s t. rewrite (ratLt a Ha b Hb c Hc d Hd Hpb Hpd).
  rewrite ratAdd_a_b_c_d, ratAdd_a_b_c_d...
  assert (Hz1: a⋅f + e⋅b ∈ ℤ) by (amr;nz).
  assert (Hz2: b⋅f ∈ ℤ') by nzmr.
  assert (Hz3: c⋅f + e⋅d ∈ ℤ) by (amr;nz).
  assert (Hz4: d⋅f ∈ ℤ') by nzmr.
  assert (Hpbf: intPos (b⋅f)) by (apply intMul_pos_prod; nz; auto).
  assert (Hpdf: intPos (d⋅f)) by (apply intMul_pos_prod; nz; auto).
  rewrite (ratLt _ Hz1 _ Hz2 _ Hz3 _ Hz4 Hpbf Hpdf).
  rewrite intMul_distr', intMul_distr'; [|mr;nz..].
  assert (Hzf: f ∈ ℤ) by nz.
  rewrite
    (intMul_assoc a), (intMul_comm f),
    (intMul_assoc d), <- (intMul_assoc a),
    (intMul_assoc c), (intMul_comm f Hzf (b⋅f)),
    (intMul_assoc b), <- (intMul_assoc c),
    (intMul_assoc e), (intMul_comm b),
    (intMul_assoc d), <- (intMul_assoc e), (intMul_comm b);
      nz; auto; [|mr;nz..].
  assert (Hz5: (a⋅d)⋅(f⋅f) ∈ ℤ) by (mr;mr;nz).
  assert (Hz6: (c⋅b)⋅(f⋅f) ∈ ℤ) by (mr;mr;nz).
  assert (Hz7: (e⋅d)⋅(f⋅b) ∈ ℤ) by (mr;mr;nz).
  rewrite <- (intLt_both_side_add _ Hz5 _ Hz6 _ Hz7).
  apply intLt_both_side_mul; revgoals; [|mr;nz..].
  apply intMul_pos_prod...
Qed.

Theorem ratLt_both_side_mul : ∀ r s t ∈ ℚ,
  ratPos t → r <𝐪 s ↔ (r ⋅ t <𝐪 s ⋅ t)%q.
Proof with nauto.
  cut (∀ r s t ∈ ℚ, ratPos t → r <𝐪 s → (r ⋅ t <𝐪 s ⋅ t)%q).
  intros Hright r Hr s Hs t Ht Hpt. split; intros Hlt.
  apply Hright... destruct (classic (r = s)).
  subst. exfalso. eapply ratLt_not_refl; revgoals.
  apply Hlt. apply ratMul_ran...
  apply ratLt_connected in H as []... exfalso.
  eapply (Hright s Hs r Hr t Ht Hpt) in H.
  eapply ratLt_not_refl; revgoals.
  eapply ratLt_tranr; eauto. apply ratMul_ran...
  intros r Hr s Hs t Ht Hpt Hlt.
  apply pQuotE_ratPosDenom in Hr as [a [Ha [b [Hb [Hr Hpb]]]]].
  apply pQuotE_ratPosDenom in Hs as [c [Hc [d [Hd [Hs Hpd]]]]].
  apply pQuotE_ratPosDenom in Ht as [e [He [f [Hf [Ht Hpf]]]]]. subst.
  apply ratLt in Hpt... rewrite intMul_0_l, intMul_ident in Hpt; nz...
  apply ratLt in Hlt... rewrite ratMul_a_b_c_d, ratMul_a_b_c_d...
  apply ratLt. mr. nzmr. mr. nzmr.
  apply intMul_pos_prod; nz... apply intMul_pos_prod; nz...
  rewrite
    (intMul_assoc a), (intMul_comm e),
    (intMul_assoc d), <- (intMul_assoc a),
    (intMul_assoc c), (intMul_comm e),
    (intMul_assoc b), <- (intMul_assoc c);
      nz; auto; [|mr;nz..].
  apply intLt_both_side_mul... mr;nz. mr;nz. mr;nz.
  apply intMul_pos_prod; nz...
Qed.

Close Scope Int_scope.
Open Scope Rat_scope.

Corollary ratLt_both_side_add_tran : ∀ q r s t ∈ ℚ,
  q <𝐪 r → s <𝐪 t → q + s <𝐪 r + t.
Proof with auto.
  intros q Hq r Hr s Hs t Ht H1 H2.
  apply (ratLt_both_side_add q Hq r Hr s Hs) in H1.
  apply (ratLt_both_side_add s Hs t Ht r Hr) in H2.
  rewrite (ratAdd_comm s), (ratAdd_comm t) in H2...
  eapply ratLt_tranr; eauto.
Qed.

Theorem ratAdd_cancel : ∀ r s t ∈ ℚ, r + t = s + t → r = s.
Proof with eauto.
  intros r Hr s Hs t Ht Heq.
  assert (r + t - t = s + t - t) by congruence.
  rewrite (ratAdd_assoc r), (ratAdd_assoc s) in H...
  rewrite ratAddInv_annih, ratAdd_ident, ratAdd_ident in H...
  apply ratAddInv_rat... apply ratAddInv_rat...
Qed.

Corollary ratAdd_cancel' : ∀ r s t ∈ ℚ, t + r = t + s → r = s.
Proof with eauto.
  intros r Hr s Hs t Ht Heq.
  eapply ratAdd_cancel...
  rewrite ratAdd_comm, (ratAdd_comm s)...
Qed.

Theorem ratMul_cancel : ∀ r s t ∈ ℚ, t ≠ Rat 0 → r ⋅ t = s ⋅ t → r = s.
Proof with eauto.
  intros r Hr s Hs t Ht Hnq0 Heq.
  assert (r ⋅ t / t = s ⋅ t / t) by congruence.
  assert (Ht': t ∈ ℚ') by (apply nzRatI0; auto).
  rewrite (ratMul_assoc r), (ratMul_assoc s) in H...
  rewrite ratMulInv_annih, ratMul_ident, ratMul_ident in H...
  apply nzRatE1. apply ratMulInv_rat...
  apply nzRatE1. apply ratMulInv_rat...
Qed.

Corollary ratMul_cancel' : ∀ r s t ∈ ℚ, t ≠ Rat 0 → t ⋅ r = t ⋅ s → r = s.
Proof with eauto.
  intros r Hr s Hs t Ht Hnq0 Heq.
  eapply ratMul_cancel...
  rewrite ratMul_comm, (ratMul_comm s)...
Qed.

Lemma ratMul_pos_prod : ∀ p q ∈ ℚ,
  ratPos p → ratPos q → ratPos (p ⋅ q).
Proof with nauto.
  intros p Hp q Hq Hpp Hpq. unfold ratPos.
  rewrite <- (ratMul_0_r q)...
  apply ratLt_both_side_mul...
Qed.

Lemma ratMul_neg_prod : ∀ p q ∈ ℚ,
  ratPos p → ratNeg q → ratNeg (p ⋅ q).
Proof with nauto.
  intros p Hp q Hq Hpp Hnq.
  unfold ratNeg. rewrite ratMul_comm, <- (ratMul_0_r p)...
  apply ratLt_both_side_mul...
Qed.

(** 整数嵌入 **)
Definition IntEmbed := Relation ℤ ℚ (λ a r, r = [<a, Int 1>]~).

Theorem intEmbed_maps_into : IntEmbed: ℤ ⇒ ℚ.
Proof with nauto.
  repeat split.
  - intros x Hx. apply SepE in Hx as [Hx _].
    apply CProdE2 in Hx...
  - apply domE in H...
  - intros y1 y2 H1 H2.
    apply SepE in H1 as [_ H1].
    apply SepE in H2 as [_ H2]. zfcrewrite.
  - apply ExtAx. intros x. split; intros Hx.
    + apply domE in Hx as [y Hp]. apply SepE in Hp as [Hx _].
      apply CProdE1 in Hx as [Hx _]. zfcrewrite.
    + eapply domI. apply SepI; revgoals.
      zfcrewrite. reflexivity. apply CProdI... apply pQuotI...
  - intros y Hy. apply ranE in Hy as [x Hp].
    apply SepE in Hp as [Hp _].
    apply CProdE1 in Hp as [_ Hy]. zfcrewrite.
Qed.

Corollary intEmbed_rat : ∀a ∈ ℤ, IntEmbed[a] ∈ ℚ.
Proof with auto.
  pose proof intEmbed_maps_into as [Hf [Hd Hr]].
  intros a Ha. apply Hr. eapply ranI.
  apply func_correct... rewrite Hd...
Qed. 

Theorem intEmbed_injective : injective IntEmbed.
Proof with nauto.
  split. destruct intEmbed_maps_into...
  split. apply ranE in H...
  intros x1 x2 H1 H2. clear H.
  apply SepE in H1 as [Hx1 H1]. apply CProdE1 in Hx1 as [Hx1 _].
  apply SepE in H2 as [Hx2 H2]. apply CProdE1 in Hx2 as [Hx2 _].
  zfcrewrite. subst x. apply rat_ident in H2...
  rewrite intMul_ident, intMul_ident in H2...
Qed.

Lemma intEmbed_a : ∀a ∈ ℤ, IntEmbed[a] = [<a, Int 1>]~.
Proof with nauto.
  intros n Hn. apply func_ap. destruct intEmbed_maps_into...
  apply SepI. apply CProdI... apply pQuotI... zfcrewrite.
Qed.

Lemma intEmbed_addInv : ∀a ∈ ℤ, IntEmbed[(-a)%z] = -[<a, Int 1>]~.
Proof with nauto.
  intros n Hn. rewrite intEmbed_a, ratAddInv...
  apply intAddInv_int...
Qed.

Theorem intEmbed_add : ∀ a b ∈ ℤ,
  IntEmbed[(a + b)%z] = IntEmbed[a] + IntEmbed[b].
Proof with nauto.
  intros a Ha b Hb.
  repeat rewrite intEmbed_a; [|auto;ar..].
  rewrite ratAdd_a_b_c_d...
  rewrite intMul_ident, intMul_ident, intMul_ident...
Qed.

Theorem intEmbed_mul : ∀ a b ∈ ℤ,
  IntEmbed[(a ⋅ b)%z] = IntEmbed[a] ⋅ IntEmbed[b].
Proof with nauto.
  intros a Ha b Hb.
  repeat rewrite intEmbed_a; [|auto;mr..].
  rewrite ratMul_a_b_c_d, intMul_ident...
Qed.

Theorem intEmbed_0 : IntEmbed[Int 0] = Rat 0.
Proof. rewrite intEmbed_a; nauto. Qed.

Theorem intEmbed_1 : IntEmbed[Int 1] = Rat 1.
Proof. rewrite intEmbed_a; nauto. Qed.

Theorem intEmbed_lt : ∀ a b ∈ ℤ,
  a <𝐳 b ↔ IntEmbed[a] <𝐪 IntEmbed[b].
Proof with auto.
  intros a Ha b Hb.
  repeat rewrite intEmbed_a...
  pose proof (int_sn 0) as Hz1.
  pose proof (intPos_sn 0) as Hp1.
  rewrite (ratLt a Ha (Int 1) Hz1 b Hb (Int 1) Hz1 Hp1 Hp1).
  rewrite intMul_ident, intMul_ident... reflexivity.
Qed.

Theorem intEmbed_div : ∀a ∈ ℤ, ∀b ∈ ℤ',
  [<a, b>]~ = IntEmbed[a] / IntEmbed[b].
Proof with nauto.
  intros a Ha b Hb.
  repeat rewrite intEmbed_a; nz...
  rewrite ratMulInv, ratMul_a_b_c_d...
  rewrite intMul_ident, intMul_ident'; nz...
Qed.

Close Scope Rat_scope.
Open Scope Int_scope.

(** 关于逆元的运算律 **)

Lemma intAddInv_sum : ∀ a b ∈ ℤ, -(a + b) = -a - b.
Proof with auto.
  intros a Ha b Hb.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply pQuotE in Hb as [p [Hp [q [Hq Hd]]]]. subst b.
  rewrite intAddInv, intAddInv, intAdd_m_n_p_q,
    intAdd_m_n_p_q, intAddInv; auto; apply add_ran...
Qed.

Lemma intAddInv_diff : ∀ a b ∈ ℤ, -(a - b) = b - a.
Proof with auto.
  intros a Ha b Hb.
  rewrite intAddInv_sum, intAddInv_double, intAdd_comm;
    auto; apply intAddInv_int...
Qed.

Lemma ratAddInv_sum : ∀ r s ∈ ℚ, (-(r + s) = -s - r)%q.
Proof with auto.
  intros r Hr s Hs.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  apply pQuotE in Hs as [c [Hc [d [Hd Hs]]]]. subst s.
  assert (H1: a ⋅ d + c ⋅ b ∈ ℤ) by (amr;nz).
  assert (H2: b ⋅ d ∈ ℤ') by nzmr.
  assert (H3: d ⋅ b ∈ ℤ') by nzmr.
  assert (H4: -a ∈ ℤ) by (apply intAddInv_int; auto).
  assert (H5: -c ∈ ℤ) by (apply intAddInv_int; auto).
  rewrite ratAddInv, ratAddInv, ratAdd_a_b_c_d,
    ratAdd_a_b_c_d, ratAddInv...
  apply rat_ident... apply intAddInv_int... amr;nz.
  assert (H6: a ⋅ d ∈ ℤ) by (mr;nz).
  assert (H7: c ⋅ b ∈ ℤ) by (mr;nz).
  rewrite intMul_addInv_l, intMul_distr', intMul_distr',
    intAddInv_sum, (intMul_comm d), intAdd_comm, intMul_addInv_l,
    intMul_addInv_l, intMul_addInv_l, intMul_addInv_l; nz...
  apply intAddInv_int; mr;nz.
  apply intAddInv_int; mr;nz. mr;nz. mr;nz.
  rewrite intMul_addInv_l; nz... apply intAddInv_int...
  rewrite intMul_addInv_l; nz... apply intAddInv_int...
Qed.

Lemma ratAddInv_diff : ∀ r s ∈ ℚ, (-(r - s) = s - r)%q.
Proof with auto.
  intros r Hr s Hs.
  rewrite ratAddInv_sum, ratAddInv_double, ratAdd_comm;
    auto; apply ratAddInv_rat...
Qed.

Lemma nzIntMul_ran : ∀ a b ∈ ℤ', a ⋅ b ∈ ℤ'.
Proof with neauto.
  intros a Ha' b Hb'.
  apply nzIntE1 in Ha' as Ha. apply nzIntE1 in Hb' as Hb.
  apply nzIntI0. apply intMul_ran; nz...
  apply nzIntE0 in Ha' as Ha0. apply nzIntE0 in Hb' as Hb0.
  intros H0. apply int_no_0_div in H0 as []...
Qed.

Lemma ratMulInv_prod : ∀ r s ∈ ℚ', ((r ⋅ s)⁻¹ = r⁻¹ ⋅ s⁻¹)%q.
Proof with auto.
  intros r Hr s Hs.
  apply nzRatE2 in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  apply nzRatE2 in Hs as [c [Hc [d [Hd Hs]]]]. subst s.
  rewrite ratMulInv, ratMulInv, ratMul_a_b_c_d,
    ratMul_a_b_c_d, ratMulInv; nz...
  apply nzIntMul_ran... apply nzIntMul_ran...
Qed.

Lemma ratMulInv_quot : ∀ r s ∈ ℚ', ((r / s)⁻¹ = s / r)%q.
Proof with auto.
  intros r Hr s Hs.
  rewrite ratMulInv_prod, ratMulInv_double, ratMul_comm...
  apply nzRatE1. apply ratMulInv_rat...
  apply nzRatE1... apply ratMulInv_rat...
Qed.
