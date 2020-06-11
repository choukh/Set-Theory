(** Based on "Elements of Set Theory" Chapter 4 Part 3 **)
(** Coq coding by choukh, May 2020 **)

Require Export ZFC.EST4_2.

(*** EST第四章3：自然数上的全序和良序，强归纳原理 ***)

Notation "a ≤ b" := (a ∈ b ∨ a = b) (at level 70).

Lemma n_in_s : ∀n ∈ ω, n ∈ n⁺.
Proof.
  intros n Hn. apply BUnionI2. apply SingI.
Qed.

Lemma ineq_leq_iff_lt : ∀ p k ∈ ω, p ≤ k ↔ p ∈ k⁺.
Proof with auto.
  intros p Hp k Hk. split.
  - intros []. apply BUnionI1... subst. apply n_in_s...
  - intros H. apply BUnionE in H as []. left...
    right. apply SingE in H...
Qed.

(* 自然数上的∈构成全序关系 *)
Definition εω := {p ∊ ω × ω | λ p, π1 p ∈ π2 p}.

Lemma rel_εω : rel εω ω.
Proof. intros x Hx. apply SepE in Hx as []; auto. Qed.

Lemma tranr_εω : tranr εω.
Proof with eauto.
  intros x y z H1 H2.
  apply SepE in H1 as [H11 H12]. apply CProdE1 in H11 as [Hx Hy].
  apply SepE in H2 as [H21 H22]. apply CProdE1 in H21 as [_  Hz].
  apply SepI; zfcrewrite. apply CProdI... eapply nat_trans...
Qed.

Lemma ineq_both_side_s : ∀ m n ∈ ω, m ∈ n ↔ m⁺ ∈ n⁺.
Proof with try apply ω_inductive; eauto.
  intros m Hm n Hn. split; intros H.
  - generalize dependent m.
    set {n ∊ ω | λ n, ∀ m, m ∈ ω → m ∈ n → m ⁺ ∈ n ⁺} as N.
    ω_induction N Hn; intros k Hk1 Hk2. exfalso0.
    apply ineq_leq_iff_lt in Hk2 as []...
    + apply IH in H... apply BUnionI1...
    + subst. apply BUnionI2... apply SingI.
  - apply ineq_leq_iff_lt in H as []...
    + eapply nat_trans; revgoals...
    + subst...
Qed.

Lemma nat_reg : ∀n ∈ ω, n ∉ n.
Proof with auto.
  intros n Hn.
  set {n ∊ ω | λ n, n ∉ n} as N.
  ω_induction N Hn; intros Hc. exfalso0.
  apply IH. apply ineq_both_side_s...
Qed.

Lemma empty_in_s : ∀n ∈ ω, 0 ∈ n⁺.
Proof with auto.
  intros n Hn.
  set {n ∊ ω | λ n, 0 ∈ n⁺} as N.
  ω_induction N Hn...
  apply ineq_leq_iff_lt... apply ω_inductive...
Qed.

Theorem trich_εω : trich εω ω.
Proof with eauto.
  eapply trich_iff. apply rel_εω. apply tranr_εω. split.
  - intros [k [Hk Hp]]. apply SepE in Hp as [_ Hp].
    zfcrewrite. eapply nat_reg...
  - intros n Hn.
    set {n ∊ ω | λ n, ∀ m, m ∈ ω →
      n ≠ m → < n, m > ∈ εω ∨ < m, n > ∈ εω} as N.
    ω_induction N Hn; intros k Hk Hnq.
    + assert (k ≠ 0) by congruence.
      apply SI in H as [p [Hp Heq]]... left. subst.
      apply SepI; zfcrewrite. apply CProdI... apply empty_in_s...
    + ω_destruct k.
      * subst. right. apply SepI; zfcrewrite. apply CProdI...
        apply ω_inductive... apply empty_in_s...
      * subst. assert (m ≠ n') by congruence.
        apply IH in H as []...
        left. apply SepE in H as [Hm1 Hm2]; zfcrewrite.
        apply CProdE1 in Hm1 as [Hm1 _]; zfcrewrite.
        apply SepI; zfcrewrite. apply CProdI... apply ω_inductive...
        rewrite <- (ineq_both_side_s m Hm1 n' Hn')...
        right. apply SepE in H as [Hm1 Hm2]; zfcrewrite.
        apply CProdE1 in Hm1 as [_ Hm1]; zfcrewrite.
        apply SepI; zfcrewrite. apply CProdI... apply ω_inductive...
        rewrite <- (ineq_both_side_s n' Hn' m Hm1)...
Qed.

Theorem totalOrd_εω : totalOrd εω ω.
Proof.
   split. apply rel_εω. split. apply tranr_εω. apply trich_εω.
Qed.

Notation "A ⊂ B" := (A ⊆ B ∧ A ≠ B) (at level 70).

Lemma ω_connected : ∀ m n ∈ ω, m ≠ n → m ∈ n ∨ n ∈ m.
Proof with auto.
  intros m Hm n Hn Hnq0.
  pose proof (totalOrd_connected _ _ totalOrd_εω).
  apply H in Hnq0 as []...
  left. apply SepE in H0 as [_ H0]; zfcrewrite.
  right. apply SepE in H0 as [_ H0]; zfcrewrite.
Qed.

Corollary lt_iff_sub : ∀ m n ∈ ω, m ∈ n ↔ m ⊂ n.
Proof with eauto.
  intros m Hm n Hn. split.
  - intros H. split. intros x Hx. eapply nat_trans...
    intros Heq. subst. eapply nat_reg...
  - intros [H Hnq].
    apply ω_connected in Hnq as []...
    apply H in H0. exfalso. eapply nat_reg...
Qed.

Corollary leq_iff_subeq : ∀ m n ∈ ω, m ≤ n ↔ m ⊆ n.
Proof with eauto.
  intros m Hm n Hn. split.
  - intros [].
    + intros x Hx. eapply nat_trans...
    + subst. apply sub_refl.
  - intros H. destruct (classic (m = n)). right...
    left. apply ω_connected in H0 as []...
    apply H in H0. exfalso. eapply nat_reg...
Qed.

Theorem ineq_both_side_add : ∀ m n p ∈ ω, m ∈ n ↔ m + p ∈ n + p.
Proof with eauto.
  assert (Hright: ∀ m n p ∈ ω, m ∈ n → m + p ∈ n + p). {
    intros m Hm n Hn p Hp.
    generalize dependent n. generalize dependent m.
    set {p ∊ ω | λ p, ∀ m, m ∈ ω → ∀ n, n ∈ ω →
      m ∈ n → m + p ∈ n + p} as N.
    ω_induction N Hp; intros n Hn k Hk H.
    + repeat rewrite add_m_0...
    + repeat rewrite add_m_n...
      assert (Hnm: n + m ∈ ω) by (apply add_ran; auto).
      assert (Hkm: k + m ∈ ω) by (apply add_ran; auto).
      rewrite <- (ineq_both_side_s (n + m) Hnm (k + m) Hkm).
      apply IH...
  }
  intros m Hm n Hn p Hp. split. apply Hright...
  intros H. destruct (classic (m = n)).
  - subst. exfalso. eapply nat_reg; revgoals.
    apply H. apply add_ran...
  - apply ω_connected in H0 as []...
    pose proof (Hright n Hn m Hm p Hp H0).
    assert (n + p ∈ n + p). {
      eapply nat_trans... apply add_ran...
    }
    exfalso. eapply nat_reg; revgoals. apply H2. apply add_ran...
Qed.

Theorem ineq_both_side_mult : ∀ m n p ∈ ω, p ≠ 0 →
  m ∈ n ↔ m ⋅ p ∈ n ⋅ p.
Proof with eauto.
  assert (Hright: ∀ m n p ∈ ω, p ≠ 0 → m ∈ n → m ⋅ p ∈ n ⋅ p). {
    intros m Hm n Hn p Hp Hnq0 H.
    apply SI in Hnq0 as [k [Hk Hkeq]]... subst p. clear Hp.
    generalize dependent n. generalize dependent m.
    set {k ∊ ω | λ k, ∀ m, m ∈ ω → ∀ n, n ∈ ω →
      m ∈ n → m ⋅ k⁺ ∈ n ⋅ k⁺} as N.
    ω_induction N Hk; intros n Hn p Hp H.
    + repeat rewrite mult_n_1...
    + Ltac finish := try apply mult_ran; try apply ω_inductive; auto.
      eapply nat_trans. finish. finish.
      rewrite mult_m_n; [|auto|finish].
      apply ineq_both_side_add... finish. 
      rewrite (mult_m_n p); [|auto|finish].
      rewrite add_comm; [|auto|finish].
      rewrite (add_comm p); [|auto|finish].
      apply (ineq_both_side_add (n⋅m⁺)); finish.
  }
  intros m Hm n Hn p Hp Hnq0. split. apply Hright...
  intros H. destruct (classic (m = n)).
  - subst. exfalso. eapply nat_reg; revgoals.
    apply H. apply mult_ran...
  - apply ω_connected in H0 as []...
    pose proof (Hright n Hn m Hm p Hp Hnq0 H0).
    assert (n ⋅ p ∈ n ⋅ p). {
      eapply nat_trans... apply mult_ran...
    }
    exfalso. eapply nat_reg; revgoals. apply H2. apply mult_ran...
Qed.

Corollary add_elim : ∀ m n p ∈ ω, m + p = n + p → m = n.
Proof with eauto.
  intros m Hm n Hn p Hp Heq.
  destruct (classic (m = n))... exfalso.
  apply ω_connected in H as []...
  - eapply ineq_both_side_add in H... rewrite Heq in H.
    eapply nat_reg; revgoals... apply add_ran...
  - eapply ineq_both_side_add in H... rewrite Heq in H.
    eapply nat_reg; revgoals... apply add_ran...
Qed.

Corollary mult_elim : ∀ m n p ∈ ω, p ≠ 0 → m ⋅ p = n ⋅ p → m = n.
Proof with eauto.
  intros m Hm n Hn p Hp Hnq0 Heq.
  destruct (classic (m = n))... exfalso.
  apply ω_connected in H as []...
  - eapply ineq_both_side_mult in H... rewrite Heq in H.
    eapply nat_reg; revgoals... apply mult_ran...
  - eapply ineq_both_side_mult in H... rewrite Heq in H.
    eapply nat_reg; revgoals... apply mult_ran...
Qed.

Definition well_ordering : set → Prop := λ X,
  ∀ A, A ≠ 0 → A ⊆ X → ∃m ∈ A, ∀n ∈ A, m ≤ n.

(* 自然数上的≤构成良序关系 *)
Theorem ω_well_ordering : well_ordering ω.
Proof with eauto.
  intros A Hnq0 HA.
  destruct (classic (∃m ∈ A, ∀n ∈ A, m ≤ n))... exfalso.
  apply Hnq0. apply EmptyI. intros x Hx.
  cut (∀n ∈ ω, ∀m ∈ ω, m ∈ n → m ∉ A). intros.
  apply HA in Hx as Hxω.
  assert (x ∈ x⁺) by (apply BUnionI2; apply SingI).
  eapply (H0 x⁺)... apply ω_inductive...
  intros n Hn. clear Hnq0 x Hx.
  set {n ∊ ω | λ n, ∀m ∈ ω, m ∈ n → m ∉ A} as N.
  ω_induction N Hn; intros k Hk H0. exfalso0.
  apply ineq_leq_iff_lt in H0 as []... apply IH...
  subst k. intros Hma. apply H. clear H n Hn N Hk. 
  exists m. split... intros n Hn. apply HA in Hn as Hnω.
  destruct (classic (m = n))... left.
  apply ω_connected in H as []... exfalso. eapply IH...
Qed.

Corollary f_ran_well_ordering : ¬ ∃ f, f: ω ⇒ ω ∧
  ∀n ∈ ω, f[n⁺] ∈ f[n].
Proof with eauto.
  intros [f [[Hff [Hfd Hfr]] H]].
  assert (Hnq0: ran f ≠ 0). {
    apply EmptyNI. exists (f[0]). eapply ranI.
    apply func_correct... rewrite Hfd...
  }
  eapply ω_well_ordering in Hnq0 as [m [Hm Hmin]]...
  apply Hfr in Hm as Hf0.
  apply ranE in Hm as [x Hp].
  apply func_ap in Hp as Hap... subst m.
  apply domI in Hp as Hx. rewrite Hfd in Hx.
  apply H in Hx as Hlt.
  assert (Hr: f[x⁺] ∈ ran f). {
    eapply ranI. apply func_correct...
    rewrite Hfd. apply ω_inductive...
  }
  apply Hmin in Hr as [].
  - eapply nat_reg. apply Hf0. eapply nat_trans...
  - eapply nat_reg. apply Hf0. congruence.
Qed.

(* 强归纳原理 *)
Theorem ω_ind_2 : ∀ A, A ⊆ ω →
  (∀n ∈ ω, (∀m ∈ ω, m ∈ n → m ∈ A) → n ∈ A) → 
  A = ω.
Proof with eauto.
  intros A HA Hind.
  destruct (classic (A = ω))... exfalso.
  assert (Hnq0: ω - A ≠ 0). {
    intros H0. apply H. apply sub_asym... intros x Hx.
    destruct (classic (x ∈ A))... exfalso.
    eapply EmptyE in H0. apply H0. apply CompI...
  }
  assert (Hsub: ω - A ⊆ ω). {
    intros x Hx. apply CompE in Hx as []...
  }
  apply ω_well_ordering in Hsub as [m [Hm Hmin]]...
  apply CompE in Hm as [Hmw Hma].
  apply Hma. apply Hind... intros k Hkw Hkm.
  destruct (classic (k ∈ A))... exfalso.
  assert (Hk: k ∈ ω - A) by (apply CompI; auto).
  apply Hmin in Hk as [].
  - eapply nat_reg... eapply nat_trans...
  - subst. eapply nat_reg...
Qed.

Theorem ω_ind_2_0 : ∀ C, C ⊆ ω →
  (∀n ∈ C, ∃m ∈ C, m ∈ n) →
  C = 0.
Proof with eauto.
  intros C HC Hincr.
  destruct (classic (C = 0)) as [H0|H0]... exfalso.
  pose proof (ω_well_ordering C H0 HC) as [m [Hm Hmin]]...
  pose proof (Hincr m Hm) as [n [Hnc Hnm]]. apply HC in Hnc as Hn.
  pose proof (Hmin n Hnc) as [].
  - eapply nat_reg. apply Hn. eapply nat_trans; revgoals...
  - subst. eapply nat_reg...
Qed.

Lemma ineq_nq_0_gt_0 : ∀n ∈ ω, n ≠ 0 ↔ 0 ∈ n.
Proof with auto.
  intros n Hn. split; intros.
  - apply ω_connected in H as []... exfalso0.
  - destruct (classic (n = 0))... subst. exfalso0.
Qed.

Lemma ineq_leq_iff_neg_lt : ∀ a b ∈ ω, a ≤ b ↔ b ∉ a.
Proof with eauto.
  intros a Ha b Hb. split; intros.
  - intros Hc. destruct H.
    apply (nat_reg a)... eapply nat_trans...
    apply (nat_reg a)... subst...
  - destruct (classic (a = b)). right... left.
    apply ω_connected in H0 as []... exfalso...
Qed.

Lemma ineq_leq_add_enlarge : ∀ a b ∈ ω, a ≤ a + b.
Proof with eauto.
  intros a Ha b Hb. generalize dependent a.
  set {b ∊ ω | λ b, ∀ a, a ∈ ω → a ≤ a + b} as N.
  ω_induction N Hb; intros a Ha.
  - rewrite add_m_0...
  - rewrite add_m_n... assert (Ha' := Ha).
    apply IH in Ha' as []; left.
    apply ineq_leq_iff_lt... apply add_ran...
    rewrite <- H...
Qed.

Lemma ineq_lt_add_enlarge : ∀ a b ∈ ω, ∀ x ∈ a, x ∈ a + b.
Proof with eauto.
  intros a Ha b Hb. generalize dependent a.
  set {b ∊ ω | λ b, ∀ a, a ∈ ω → ∀ x ∈ a, x ∈ a + b} as N.
  ω_induction N Hb; intros a Ha x Hx.
  - rewrite add_m_0...
  - assert (Hxw: x ∈ ω) by (eapply ω_trans; eauto).
    rewrite add_m_n... apply ineq_leq_iff_lt...
    apply add_ran... left. apply IH...
Qed.

Lemma ineq_lt_add_shrink : ∀ a b c ∈ ω, a + b ∈ c → a ∈ c.
Proof with eauto.
  intros a Ha b Hb.
  set {b ∊ ω | λ b, ∀ c ∈ ω, a + b ∈ c → a ∈ c} as N.
  ω_induction N Hb; intros c Hc H.
  - rewrite add_m_0 in H...
  - rewrite add_m_n in H... apply IH...
    eapply nat_trans; revgoals...
Qed.

Lemma ineq_leq_mult_enlarge : ∀ a b ∈ ω, a ≤ a ⋅ b⁺.
Proof with eauto.
  intros a Ha b Hb. apply ineq_leq_iff_neg_lt...
  apply mult_ran... apply ω_inductive... intros Hc.
  rewrite mult_m_n in Hc...
  apply ineq_lt_add_shrink in Hc; try apply mult_ran...
  eapply nat_reg; revgoals...
Qed.

Lemma S_has_0 : ∀n ∈ ω, 0 ∈ n⁺.
Proof with auto.
  intros n Hn. apply ineq_nq_0_gt_0.
  apply ω_inductive... apply S_neq_0.
Qed.

Lemma not_lt_gt : ∀ a b ∈ ω, a ∈ b → b ∈ a → ⊥.
Proof.
  intros a Ha b Hb Hlt Hgt. eapply nat_reg. apply Ha.
  eapply nat_trans; eauto.
Qed.

Lemma not_lt_self : ∀ a b ∈ ω, a = b → b ∈ a → ⊥.
Proof.
  intros a Ha b Hb Heq Hlt. subst. eapply nat_reg; eauto.
Qed.

Lemma not_leq_gt : ∀ a b ∈ ω, a ≤ b → b ∈ a → ⊥.
Proof with eauto.
  intros a Ha b Hb Hleq Hgt. destruct Hleq.
  - eapply not_lt_gt; revgoals...
  - eapply not_lt_self; revgoals...
Qed.
