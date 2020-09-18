(** Solutions to "Elements of Set Theory" Chapter 5 **)
(** Coq coding by choukh, June 2020 **)

Require Export ZFC.EST5_4.

Local Ltac nz := try (apply nzIntE1; assumption).
Local Ltac mr := apply intMul_ran; nauto.
Local Ltac amr := apply intAdd_ran; apply intMul_ran; nauto.
Local Ltac nzmr := apply nzIntMul_ranI; nauto.

(* ch5_4 see EST5_1 Theorem intAdd_assoc *)
(* ch5_5 see EST5_1 Definition IntInv *)
(* ch5_6 see EST5_2 Lemma intMul_a_0 *)
(* ch5_7 see EST5_2 Lemma int_eq_mul_inv_0, 1 *)
(* ch5_8 see EST5_2 Theorem ω_embed_add, mul, lt *)
(* ch5_9 see EST5_2 Theorem ω_embed_subtr *)
(* ch5_10 see EST5_3 Lemma ratMul_0_l *)

Example ch5_11: ∀ r s ∈ ℚ,
  r ⋅ s = Rat 0 → r = Rat 0 ∨ s = Rat 0.
Proof with nauto.
  intros r Hr s Hs H.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]].
  apply pQuotE in Hs as [c [Hc [d [Hd Hs]]]].
  subst r s. rewrite ratMul_a_b_c_d in H...
  apply rat_ident in H; nauto; [|mr|nzmr]...
  rewrite intMul_ident, intMul_0_l in H; [|mr;nz..].
  apply int_no_0_div in H as []; subst; auto; [left|right];
    apply rat_ident; nauto; rewrite intMul_0_l, intMul_0_l; nz...
Qed.

Example ch5_12: ∀r ∈ ℚ, ratNeg r ↔ ratPos (-r).
Proof with auto.
  intros r Hr. split. apply ratNeg_pos. intros Hp.
  apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]]. subst r.
  rewrite ratAddInv in Hp... apply ratPos_neg in Hp.
  rewrite ratAddInv in Hp... rewrite intAddInv_double in Hp...
  apply intAddInv_ran...
Qed.

Close Scope Rat_scope.
Open Scope Int_scope.

Example ch5_13: ∀ a b c ∈ ℤ, a + c = b + c → a = b.
Proof with eauto.
  intros a Ha b Hb c Hc Heq.
  assert (a + c - c = b + c - c) by congruence.
  rewrite (intAdd_assoc a), (intAdd_assoc b) in H...
  rewrite intAddInv_annih, intAdd_ident, intAdd_ident in H...
  apply intAddInv_ran... apply intAddInv_ran...
Qed.

Close Scope Int_scope.
Open Scope Nat_scope.

Lemma add_1_1 : 1 + 1 = 2.
Proof with auto.
  rewrite pred, add_m_n, add_m_n', add_ident;
    auto; repeat apply ω_inductive.
Qed.

Lemma mul_2_l : ∀m ∈ ω, 2 ⋅ m = m + m.
Proof with nauto.
  intros n Hn.
  set {n ∊ ω | λ n, 2 ⋅ n = n + n} as N.
  ω_induction N Hn.
  - rewrite mul_0_r, add_ident...
  - rewrite mul_m_n, IH...
    assert (Hmm: m + m ∈ ω) by (apply add_ran; auto).
    rewrite add_m_n, add_m_n', add_suc, add_suc...
    rewrite (add_assoc (m + m)), (add_comm 2), add_1_1...
    apply ω_inductive... apply ω_inductive...
Qed.

Close Scope Nat_scope.
Open Scope Int_scope.

Lemma intMul_2_a : ∀a ∈ ℤ, Int 2 ⋅ a = a + a.
Proof with nauto.
  intros a Ha. unfold Int.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  rewrite intMul_m_n_p_q, intAdd_m_n_p_q...
  rewrite mul_0_l, mul_0_l, add_ident, add_ident...
  rewrite mul_2_l, mul_2_l...
  apply mul_ran... apply mul_ran...
Qed.

Example ch5_14: ∀ p s ∈ ℚ, p <𝐪 s → ∃r ∈ ℚ, p <𝐪 r ∧ r <𝐪 s.
Proof with neauto.
  intros p Hp s Hs Hlt.
  apply pQuotE_ratPosDenom in Hp as [a [Ha [b [Hb [Hp Hpb]]]]].
  apply pQuotE_ratPosDenom in Hs as [c [Hc [d [Hd [Hs Hpd]]]]].
  subst p s. apply ratLt in Hlt...
  exists ([<a⋅d + c⋅b, Int 2 ⋅ b ⋅ d>]~). split.
  apply pQuotI; [amr;nz|nzmr; nzmr].
  assert (Hpp: intPos ((Int 2 ⋅ b) ⋅ d)). {
    apply intMul_pos_prod; nz... mr;nz.
    apply intMul_pos_prod; nz...
  }
  split; (apply ratLt; auto; [amr;nz|nzmr; nzmr|]).
  rewrite
    <- (intMul_assoc a), <- (intMul_assoc a), (intMul_comm a),
    (intMul_assoc (Int 2)), (intMul_assoc (Int 2)),
    (intMul_assoc a), (intMul_comm b), <- (intMul_assoc a),
    (intAdd_comm (a⋅d)), intMul_distr', intMul_2_a;
    nz; nauto; [|mr;nz..]; [|mr;nz].
  apply intAdd_preserve_lt; revgoals; [|mr;[mr;nz|nz]..].
  apply intMul_preserve_lt; nz; auto; mr; nz.
  rewrite
    <- (intMul_assoc c), <- (intMul_assoc c),
    (intMul_comm c Hc (Int 2)),
    (intMul_assoc (Int 2)), (intMul_assoc (Int 2)),
    intMul_distr', intMul_2_a; nz; nauto; [|mr;nz..]; [|mr;nz].
  apply intAdd_preserve_lt; revgoals; [|mr;[mr;nz|nz]..].
  apply intMul_preserve_lt; nz; auto; mr; nz.
Qed.

(* ch5_15 see EST5_5 Theorem reals_bounded_has_sup *)
(* ch5_16 see EST5_5 Lemma realAdd_ran *)

Example ch5_17: ∀ a b ∈ ℤ, intPos a →
  ∃k ∈ ω, b <𝐳 a ⋅ ω_Embed[k].
Proof with neauto.
  intros a Ha b Hb Hpa.
  destruct (classic (b = Int 0));
    [|apply intLt_connected in H as [|Hpb]]...
  - exists 1. split... rewrite H, ω_embed_n, intMul_ident...
  - exists 1. split... rewrite ω_embed_n, intMul_ident...
    eapply intLt_tranr...
  - assert (Hb' := Hb).
    apply pQuotE in Hb' as [m [Hm [n [Hn Heq]]]].
    apply intLt_iff_leq_suc in Hpa as H1...
    rewrite intAdd_ident' in H1...
    assert (H2: Int 1 ⋅ b ≤ a ⋅ b)
      by (apply intMul_preserve_leq; nauto). clear H1.
    rewrite intMul_ident' in H2...
    assert (Hm1: (m + 1)%n ∈ ω) by (apply add_ran; nauto).
    assert (Hm1z: ω_Embed [(m + 1)%n] ∈ ℤ)
      by (apply ω_embed_ran; auto).
    assert (H3: b <𝐳 ω_Embed[(m + 1)%n]). {
      rewrite Heq, ω_embed_n... apply intLt...
      rewrite add_ident... apply lt_add_enlarge...
      rewrite <- add_suc...
    }
    assert (H4: a ⋅ b <𝐳 a ⋅ ω_Embed[(m + 1)%n]). {
      rewrite intMul_comm, (intMul_comm a)...
      apply intMul_preserve_lt...
    } clear H3.
    exists (m + 1)%n. split...
    destruct H2. eapply intLt_tranr... rewrite H...
Qed.

Lemma intPos_natPos : ∀a ∈ ℤ, intPos a →
  ∃m ∈ ω, a = [<m, 0>]~%pz ∧ ∅ ∈ m.
Proof with nauto.
  intros a Ha Hpa.
  apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
  apply intLt in Hpa... rewrite add_ident', add_ident in Hpa...
  apply diff_exists in Hpa as [d [Hd [Heq Hpd]]]...
  exists d. split... split. apply int_ident...
  rewrite add_ident, add_comm... apply nq_0_gt_0...
Qed.

Close Scope Int_scope.
Open Scope Nat_scope.

Example ch5_18: ∀ p r ∈ ℚ, ratPos p →
  ∃k ∈ ω, r <𝐪 (p ⋅ IntEmbed[ω_Embed[k]])%q.
Proof with neauto.
  intros p Hp r Hr Hpp.
  assert (Hemb: IntEmbed[ω_Embed[1]] = Rat 1). {
    rewrite ω_embed_n, intEmbed_a...
  }
  destruct (classic (r = Rat 0));
    [|apply ratLt_connected in H as [|Hpr]]...
  - exists 1. split... rewrite H, Hemb, ratMul_ident...
  - exists 1. split... rewrite Hemb, ratMul_ident...
    eapply ratLt_tranr...
  - apply pQuotE_ratPosDenom in Hr as [a [Ha [b [Hb [Hr Hpb]]]]].
    apply pQuotE_ratPosDenom in Hp as [c [Hc [d [Hd [Hp Hpd]]]]].
    subst r p. assert (Hpb' := Hpb). assert (Hpd' := Hpd).
    apply ratPos_intPos in Hpr as Hpa...
    apply ratPos_intPos in Hpp as Hpc...
    apply intPos_natPos in Hpa as [m [Hm [Ham Hpm]]]...
    apply intPos_natPos in Hpb' as [n [Hn [Hbn Hpn]]]; nz...
    apply intPos_natPos in Hpc as [s [Hs [Hcs Hps]]]...
    apply intPos_natPos in Hpd' as [t [Ht [Hdt Hpt]]]; nz...
    assert (H0: m⁺ ∈ ω) by (apply ω_inductive; auto).
    assert (H1: m⋅t ∈ ω) by (apply mul_ran; auto).
    assert (H2: m⁺⋅t ∈ ω) by (apply mul_ran; auto).
    assert (H3: ω_Embed[m⁺⋅t] ∈ ℤ) by (apply ω_embed_ran; auto).
    assert (H4: s⋅(m⁺⋅t) ∈ ω) by (apply mul_ran; auto).
    assert (H5: (s⋅(m ⁺⋅t))⋅n ∈ ω) by (apply mul_ran; auto).
    assert (H6: s⋅m⁺ ∈ ω) by (apply mul_ran; auto).
    assert (H7: (s⋅m⁺)⋅n ∈ ω) by (apply mul_ran; auto).
    exists (m⁺⋅t). split...
    rewrite intEmbed_a, ratMul_a_b_c_d,
      intMul_ident, Hcs, ω_embed_n, intMul_m_n_p_q,
      mul_0_r, mul_0_r, mul_0_l, add_ident, add_ident; nauto; [|nz].
    apply ratLt... apply pQuotI...
    rewrite Ham, Hbn, Hdt, intMul_m_n_p_q, intMul_m_n_p_q,
      mul_0_r, mul_0_r, mul_0_r, mul_0_l, mul_0_l,
      add_ident, add_ident, add_ident...
    apply intLt... rewrite add_ident, add_ident...
    rewrite <- mul_assoc, mul_assoc, (mul_comm t), <- mul_assoc...
    apply mul_preserve_lt... apply nq_0_gt_0...
    clear Ha Hb Hc Hd Hpr Hpp Hpb Hpd Ham Hbn Hcs Hdt a b c d
      Hemb H1 H2 H3 H4 H5 H6 H7.
    rewrite (mul_comm s), mul_assoc...
    assert (H8: s ⋅ n ∈ ω) by (apply mul_ran; auto).
    assert (H9: ∅ ∈ s ⋅ n). {
      rewrite <- (mul_0_l n)...
      apply mul_preserve_lt... apply nq_0_gt_0...
    }
    cut (m ⋅ (s ⋅ n) ∈ m⁺ ⋅ (s ⋅ n)). intros H10.
    cut (m ≤ m ⋅ (s ⋅ n)). intros [].
    + eapply nat_trans... apply mul_ran...
    + rewrite H at 1...
    + rewrite <- (mul_ident m) at 1 3...
      rewrite (mul_comm m), (mul_comm m)...
      apply mul_preserve_leq... apply nq_0_gt_0...
      apply lt_iff_leq_suc...
    + apply mul_preserve_lt... apply nq_0_gt_0...
Qed.

Corollary ch5_18_1: ∀ p r ∈ ℚ, ratPos p →
  ∃a ∈ ℤ, r <𝐪 (p ⋅ IntEmbed[a])%q.
Proof with auto.
  intros p Hp r Hr Hpp.
  pose proof (ch5_18 p Hp r Hr Hpp) as [k [Hk Hlt]].
  exists (ω_Embed [k]). split... apply ω_embed_ran...
Qed.

Close Scope Nat_scope.
Open Scope Rat_scope.

Example ch5_18_2: ∀ p r ∈ ℚ, ratPos p →
  ∃a ∈ ℤ, p ⋅ IntEmbed[a] <𝐪 r.
Proof with neauto.
  intros p Hp r Hr Hpp.
  destruct (classic (r = Rat 0));
    [|apply ratLt_connected in H as [Hnr|];revgoals]...
  - exists (-Int 1)%z. split...
    rewrite intEmbed_addInv, ratMul_addInv_r, ratMul_ident, H...
    apply ratPos_neg...
  - exists (-Int 1)%z. split...
    rewrite intEmbed_addInv, ratMul_addInv_r, ratMul_ident...
    eapply ratLt_tranr... apply ratPos_neg...
  - apply ratNeg_pos in Hnr.
    assert (Hr': -r ∈ ℚ) by (apply ratAddInv_ran; auto).
    pose proof (ch5_18 p Hp (-r) Hr' Hpp) as [k [Hk Hlt]].
    remember (ω_Embed [k]) as a.
    assert (H2: a ∈ ℤ) by (subst a; apply ω_embed_ran; auto).
    assert (H3: (-a)%z ∈ ℤ) by (apply intAddInv_ran; auto).
    assert (H4: [<(-a)%z, Int 1>]~ ∈ ℚ) by (apply pQuotI; nauto).
    rewrite <- (intAddInv_double a), intEmbed_addInv,
      ratMul_addInv_r in Hlt... apply ratLt_addInv in Hlt...
    exists (-a)%z. split. apply intAddInv_ran...
    rewrite intEmbed_a... apply ratMul_ran...
Qed.

(* ch5_19 see EST5_5 Lemma ch5_19 *)
(* ch5_20 see EST5_6 Theorem realAbs_nonNeg *)
(* ch5_21 see EST5_7 Theorem realDense *)
(* ch5_22 see EST5_6 Lemma realAbs_ran *)

Lemma ratDense : ∀ p s ∈ ℚ, p <𝐪 s → ∃r ∈ ℚ, p <𝐪 r ∧ r <𝐪 s.
Proof. exact ch5_14. Qed.

Lemma ratArchimedean : ∀q ∈ ℚ, ∃r ∈ ℚ, q <𝐪 r.
Proof with nauto.
  intros q Hq. exists (q + Rat 1). split. apply ratAdd_ran...
  rewrite <- (ratAdd_ident q) at 1...
  apply ratAdd_preserve_lt'... apply ratPos_sn.
Qed.

Lemma ratArchimedean' : ∀q ∈ ℚ, ∃r ∈ ℚ, r <𝐪 q.
Proof with nauto.
  intros q Hq. exists (q - Rat 1). split. apply ratAdd_ran...
  rewrite <- (ratAdd_ident q) at 2...
  apply ratAdd_preserve_lt'... apply ratNeg_sn.
Qed.
