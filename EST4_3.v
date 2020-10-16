(** Based on "Elements of Set Theory" Chapter 4 Part 3 **)
(** Coq coding by choukh, May 2020 **)

Require Export ZFC.EST4_2.

(*** EST第四章3：自然数全序，自然数良序，强归纳原理 ***)

Notation "a ≤ b" := (a ∈ b ∨ a = b) (at level 70) : Nat_scope.

Lemma leq_iff_lt_suc : ∀ m n ∈ ω, m ≤ n ↔ m ∈ n⁺.
Proof with nauto.
  intros m Hm n Hn. split.
  - intros []. apply BUnionI1... subst...
  - intros H. apply BUnionE in H as []. left...
    right. apply SingE in H...
Qed.

Lemma suc_preserve_lt : ∀ m n ∈ ω, m ∈ n ↔ m⁺ ∈ n⁺.
Proof with try apply ω_inductive; neauto.
  intros m Hm n Hn. split; intros H.
  - generalize dependent m.
    set {n ∊ ω | λ n, ∀ m, m ∈ ω → m ∈ n → m ⁺ ∈ n ⁺} as N.
    ω_induction N Hn; intros k Hk1 Hk2. exfalso0.
    apply leq_iff_lt_suc in Hk2 as []...
    + apply IH in H... apply BUnionI1...
    + subst. apply BUnionI2...
  - apply leq_iff_lt_suc in H as []...
    + eapply nat_trans; revgoals...
    + subst...
Qed.

Lemma lt_iff_leq_suc : ∀ m n ∈ ω, m ∈ n ↔ m⁺ ≤ n.
Proof with auto.
  intros m Hm n Hn. split.
  - intros H. apply suc_preserve_lt in H...
    apply leq_iff_lt_suc in H... apply ω_inductive...
  - intros H. apply leq_iff_lt_suc in H...
    apply suc_preserve_lt... apply ω_inductive...
Qed.

Lemma lt_irrefl : ∀n ∈ ω, n ∉ n.
Proof with auto.
  intros n Hn.
  set {n ∊ ω | λ n, n ∉ n} as N.
  ω_induction N Hn; intros Hc. exfalso0.
  apply IH. apply suc_preserve_lt...
Qed.

Lemma suc_has_0 : ∀n ∈ ω, 0 ∈ n⁺.
Proof with nauto.
  intros n Hn.
  set {n ∊ ω | λ n, 0 ∈ n⁺} as N.
  ω_induction N Hn...
  apply leq_iff_lt_suc... apply ω_inductive...
Qed.

(* 任意自然数不等于其后继 *)
Lemma suc_neq_n : ∀n ∈ ω, n ≠ n⁺.
Proof.
  intros n Hn. pose proof (suc_has_n n). intros Heq.
  rewrite <- Heq in H at 1. apply (lt_irrefl n); auto.
Qed.

(* 自然数与其单集不交 *)
Corollary nat_and_its_single_disjoint : ∀n ∈ ω, disjoint n ⎨n⎬.
Proof.
  intros n Hn. apply disjointI. intros [m [Hm Heq]].
  apply SingE in Heq; subst. eapply lt_irrefl; eauto.
Qed.

(* 自然数的小于关系 *)
Definition ωLt := {p ∊ ω × ω | λ p, π1 p ∈ π2 p}.

Lemma ωLtI : ∀ m n ∈ ω, m ∈ n → <m, n> ∈ ωLt.
Proof with auto.
  intros m Hm n Hn Hmn.
  apply SepI. apply CProdI... zfcrewrite.
Qed.

Lemma ωLtE : ∀ m n, <m, n> ∈ ωLt → m ∈ ω ∧ n ∈ ω ∧ m ∈ n.
Proof with auto.
  intros. apply SepE in H as [H1 H2].
  apply CProdE1 in H1 as [Hm Hn]. zfcrewrite. split...
Qed.

Lemma ωLt_iff : ∀ m n ∈ ω, m ∈ n ↔ <m, n> ∈ ωLt.
Proof with auto.
  intros m Hm n Hn. split; intros.
  apply ωLtI... apply ωLtE...
Qed.

Lemma ωLt_rel : binRel ωLt ω.
Proof. intros x Hx. apply SepE in Hx as []; auto. Qed.

Lemma ωLt_tranr : tranr ωLt.
Proof with eauto.
  intros m n p H1 H2.
  apply ωLtE in H1 as [Hm [Hn Hmn]].
  apply ωLtE in H2 as [_  [Hp Hnp]].
  apply SepI. apply CProdI... zfcrewrite. eapply nat_trans...
Qed.

Lemma ωLt_irreflexive : irreflexive ωLt ω.
Proof with eauto.
  intros [k [Hk Hp]]. apply SepE in Hp as [_ Hp].
  zfcrewrite. eapply lt_irrefl...
Qed.

Lemma ωLt_connected : connected ωLt ω.
Proof with nauto.
  intros n Hn.
  set {n ∊ ω | λ n, ∀ m, m ∈ ω →
    n ≠ m → < n, m > ∈ ωLt ∨ < m, n > ∈ ωLt} as N.
  ω_induction N Hn; intros k Hk Hnq.
  + assert (k ≠ ∅) by congruence.
    apply pred_exists in H as [p [Hp Heq]]... left. subst.
    apply SepI; zfcrewrite. apply CProdI... apply suc_has_0...
  + ω_destruct k.
    * subst. right. apply SepI; zfcrewrite. apply CProdI...
      apply ω_inductive... apply suc_has_0...
    * subst. assert (m ≠ n') by congruence.
      apply IH in H as []...
      left. apply ωLtE in H as [_ [_ Hmn]].
      apply SepI; zfcrewrite. apply CProdI... apply ω_inductive...
      rewrite <- (suc_preserve_lt m Hm n' Hn')...
      right. apply ωLtE in H as [_ [_ Hmn]].
      apply SepI; zfcrewrite. apply CProdI... apply ω_inductive...
      rewrite <- (suc_preserve_lt n' Hn' m Hm)...
Qed.

Lemma lt_connected : ∀ m n ∈ ω, m ≠ n → m ∈ n ∨ n ∈ m.
Proof with auto.
  intros m Hm n Hn Hnq0.
  apply ωLt_connected in Hnq0 as []; auto; [left|right];
    apply SepE in H as []; zfcrewrite.
Qed.

Lemma ωLt_trich : trich ωLt ω.
Proof with auto.
  eapply trich_iff. apply ωLt_rel. apply ωLt_tranr. split.
  apply ωLt_irreflexive. apply ωLt_connected.
Qed.

(* 自然数的小于关系是全序关系 *)
Theorem ωLt_totalOrd : totalOrd ωLt ω.
Proof.
   split. apply ωLt_rel. split. apply ωLt_tranr. apply ωLt_trich.
Qed.

Corollary nq_0_gt_0 : ∀n ∈ ω, n ≠ 0 ↔ 0 ∈ n.
Proof with nauto.
  intros n Hn. split; intros.
  - apply lt_connected in H as []... exfalso0.
  - destruct (classic (n = 0))... subst. exfalso0.
Qed.

Corollary lt_iff_psub : ∀ m n ∈ ω, m ∈ n ↔ m ⊂ n.
Proof with eauto.
  intros m Hm n Hn. split.
  - intros H. split. intros x Hx. eapply nat_trans...
    intros Heq. subst. eapply lt_irrefl...
  - intros [H Hnq].
    apply lt_connected in Hnq as []...
    apply H in H0. exfalso. eapply lt_irrefl...
Qed.

Corollary lt_iff_not_sub : ∀ m n ∈ ω, m ∈ n ↔ n ⊈ m.
Proof with auto.
  intros m Hm n Hn. split; intros H.
  - intros Hsub. apply Hsub in H. apply (lt_irrefl m)...
  - destruct (classic (m = n)) as [Heq|Hnq].
    + exfalso. apply H. subst...
    + apply lt_connected in Hnq as [|Hnm]... exfalso.
      apply H. apply lt_iff_psub in Hnm as []...
Qed.

Corollary leq_iff_sub : ∀ m n ∈ ω, m ≤ n ↔ m ⊆ n.
Proof with eauto.
  intros m Hm n Hn. split.
  - intros [].
    + intros x Hx. eapply nat_trans...
    + subst. apply sub_refl.
  - intros H. destruct (classic (m = n)). right...
    left. apply lt_connected in H0 as []...
    apply H in H0. exfalso. eapply lt_irrefl...
Qed.

Corollary lt_suc_iff_sub : ∀ m n ∈ ω, m ∈ n⁺ ↔ m ⊆ n.
Proof.
  intros m Hm n Hn. rewrite <- (leq_iff_lt_suc m Hm n Hn).
  exact (leq_iff_sub m Hm n Hn).
Qed.

Corollary leq_iff_neg_lt : ∀ m n ∈ ω, m ≤ n ↔ n ∉ m.
Proof with eauto.
  intros m Hm n Hn.
  rewrite (leq_iff_sub _ Hm _ Hn).
  split; intros H.
  - intros Hnm. apply lt_iff_not_sub in Hnm...
  - destruct (classic (m ⊆ n))...
    exfalso. apply H. apply lt_iff_not_sub...
Qed.

Theorem add_preserve_lt : ∀ m n p ∈ ω, m ∈ n ↔ m + p ∈ n + p.
Proof with eauto.
  assert (Hright: ∀ m n p ∈ ω, m ∈ n → m + p ∈ n + p). {
    intros m Hm n Hn p Hp.
    generalize dependent n. generalize dependent m.
    set {p ∊ ω | λ p, ∀ m, m ∈ ω → ∀ n, n ∈ ω →
      m ∈ n → m + p ∈ n + p} as N.
    ω_induction N Hp; intros n Hn k Hk H.
    + repeat rewrite add_ident...
    + repeat rewrite add_m_n...
      assert (Hnm: n + m ∈ ω) by (apply add_ran; auto).
      assert (Hkm: k + m ∈ ω) by (apply add_ran; auto).
      rewrite <- (suc_preserve_lt (n + m) Hnm (k + m) Hkm).
      apply IH...
  }
  intros m Hm n Hn p Hp. split. apply Hright...
  intros H. destruct (classic (m = n)).
  - subst. exfalso. eapply lt_irrefl; revgoals.
    apply H. apply add_ran...
  - apply lt_connected in H0 as []...
    pose proof (Hright n Hn m Hm p Hp H0).
    assert (n + p ∈ n + p). {
      eapply nat_trans... apply add_ran...
    }
    exfalso. eapply lt_irrefl; revgoals. apply H2. apply add_ran...
Qed.

Theorem mul_preserve_lt : ∀ m n p ∈ ω, p ≠ 0 →
  m ∈ n ↔ m ⋅ p ∈ n ⋅ p.
Proof with eauto.
  assert (Hright: ∀ m n p ∈ ω, p ≠ 0 → m ∈ n → m ⋅ p ∈ n ⋅ p). {
    intros m Hm n Hn p Hp Hnq0 H.
    apply pred_exists in Hnq0 as [k [Hk Hkeq]]... subst p. clear Hp.
    generalize dependent n. generalize dependent m.
    set {k ∊ ω | λ k, ∀ m, m ∈ ω → ∀ n, n ∈ ω →
      m ∈ n → m ⋅ k⁺ ∈ n ⋅ k⁺} as N.
    ω_induction N Hk; intros n Hn p Hp H.
    + repeat rewrite mul_ident...
    + Local Ltac finish := try apply mul_ran; try apply ω_inductive; auto.
      eapply nat_trans. finish. finish.
      rewrite mul_m_n; [|auto|finish].
      apply add_preserve_lt... finish. 
      rewrite (mul_m_n p); [|auto|finish].
      rewrite add_comm; [|auto|finish].
      rewrite (add_comm p); [|auto|finish].
      apply (add_preserve_lt (n⋅m⁺)); finish.
  }
  intros m Hm n Hn p Hp Hnq0. split. apply Hright...
  intros H. destruct (classic (m = n)).
  - subst. exfalso. eapply lt_irrefl; revgoals.
    apply H. apply mul_ran...
  - apply lt_connected in H0 as []...
    pose proof (Hright n Hn m Hm p Hp Hnq0 H0).
    assert (n ⋅ p ∈ n ⋅ p). {
      eapply nat_trans... apply mul_ran...
    }
    exfalso. eapply lt_irrefl; revgoals. apply H2. apply mul_ran...
Qed.

Corollary add_preserve_lt_tran : ∀ m n p q ∈ ω,
  m ∈ n → p ∈ q → m + p ∈ n + q.
Proof with eauto.
  intros m Hm n Hn p Hp q Hq H1 H2.
  apply (add_preserve_lt m Hm n Hn p Hp) in H1.
  apply (add_preserve_lt p Hp q Hq n Hn) in H2.
  rewrite (add_comm p), (add_comm q) in H2...
  eapply nat_trans... apply add_ran...
Qed.

Corollary add_cancel : ∀ m n p ∈ ω, m + p = n + p → m = n.
Proof with eauto.
  intros m Hm n Hn p Hp Heq.
  destruct (classic (m = n))... exfalso.
  apply lt_connected in H as []...
  - eapply add_preserve_lt in H... rewrite Heq in H.
    eapply lt_irrefl; revgoals... apply add_ran...
  - eapply add_preserve_lt in H... rewrite Heq in H.
    eapply lt_irrefl; revgoals... apply add_ran...
Qed.

Corollary add_cancel' : ∀ m n p ∈ ω, p + m = p + n → m = n.
Proof with eauto.
  intros m Hm n Hn p Hp Heq.
  eapply add_cancel... rewrite add_comm, (add_comm n)...
Qed.

Corollary mul_cancel : ∀ m n p ∈ ω, p ≠ 0 → m ⋅ p = n ⋅ p → m = n.
Proof with eauto.
  intros m Hm n Hn p Hp Hnq0 Heq.
  destruct (classic (m = n))... exfalso.
  apply lt_connected in H as []...
  - eapply mul_preserve_lt in H... rewrite Heq in H.
    eapply lt_irrefl; revgoals... apply mul_ran...
  - eapply mul_preserve_lt in H... rewrite Heq in H.
    eapply lt_irrefl; revgoals... apply mul_ran...
Qed.

Corollary mul_cancel' : ∀ m n p ∈ ω, p ≠ 0 → p ⋅ m = p ⋅ n → m = n.
Proof with eauto.
  intros m Hm n Hn p Hp Hnq0 Heq.
  eapply mul_cancel... rewrite mul_comm, (mul_comm n)...
Qed.

Corollary mul_preserve_leq : ∀ m n p ∈ ω,
  p ≠ 0 → m ≤ n ↔ m ⋅ p ≤ n ⋅ p.
Proof with eauto.
  intros m Hm n Hn p Hp Hnq0. split; intros [].
  - left. apply mul_preserve_lt...
  - right. congruence.
  - left. apply mul_preserve_lt in H...
  - right. apply mul_cancel in H...
Qed.

(* 良序关系 *)
Definition wellOrder : set → set → Prop := λ Ord X,
  totalOrd Ord X ∧
  ∀ A, A ≠ ∅ → A ⊆ X →
  ∃x ∈ A, ∀y ∈ A, <x, y> ∈ Ord ∨ x = y.

(* 自然数的小于关系是良序关系 *)
Theorem ωLt_wellOrder : wellOrder ωLt ω.
Proof with eauto.
  split. apply ωLt_totalOrd.
  intros A Hnq0 Hsub. apply EmptyNE in Hnq0 as [a Ha].
  destruct (classic (∃m ∈ A, ∀n ∈ A, <m, n> ∈ ωLt ∨ m = n))... exfalso.
  cut (∀ n m ∈ ω, m ∈ n → m ∉ A). {
    intros. apply Hsub in Ha as Haω.
    assert (a ∈ a⁺) by (apply BUnionI2; apply SingI).
    eapply (H0 a⁺)... apply ω_inductive...
  }
  intros n Hn. clear a Ha.
  set {n ∊ ω | λ n, ∀m ∈ ω, m ∈ n → m ∉ A} as N.
  ω_induction N Hn; intros k Hk H0. exfalso0.
  apply leq_iff_lt_suc in H0 as []... apply IH...
  subst k. intros Hma. apply H. clear H n Hn N Hk. 
  exists m. split... intros n Hn. apply Hsub in Hn as Hnω.
  destruct (classic (m = n))... left.
  apply lt_connected in H as []...
  apply ωLtI... exfalso. eapply IH...
Qed.

Theorem ω_wellOrder : ∀ A, A ≠ ∅ → A ⊆ ω → 
  ∃m ∈ A, ∀n ∈ A, m ≤ n.
Proof with auto.
  intros A Hnq0 Hsub. assert (Hsub' := Hsub).
  apply ωLt_wellOrder in Hsub' as [m [Hm Hlt]]...
  exists m. split... intros n Hn. assert (Hn' := Hn).
  apply Hlt in Hn' as []. left. apply ωLt_iff...
  apply Hsub... apply Hsub... right...
Qed.

Corollary f_ran_wellOrder : ¬ ∃ f, f: ω ⇒ ω ∧
  ∀n ∈ ω, f[n⁺] ∈ f[n].
Proof with neauto.
  intros [f [[Hff [Hfd Hfr]] H]].
  assert (Hnq0: ran f ≠ 0). {
    apply EmptyNI. exists (f[0]). eapply ranI.
    apply func_correct... rewrite Hfd...
  }
  eapply ω_wellOrder in Hnq0 as [m [Hm Hmin]]...
  apply Hfr in Hm as Hf0.
  apply ranE in Hm as [x Hp].
  apply func_ap in Hp as Hap... subst m.
  apply domI in Hp as Hx. rewrite Hfd in Hx.
  apply H in Hx as Hlt.
  assert (Hr: f[x⁺] ∈ ran f). {
    eapply ap_ran. split... apply ω_inductive...
  }
  apply Hmin in Hr as [].
  - eapply lt_irrefl. apply Hf0. eapply nat_trans...
  - eapply lt_irrefl. apply Hf0. congruence.
Qed.

(* 强归纳原理 *)
Theorem ω_ind_strong : ∀ A, A ⊆ ω →
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
  apply ω_wellOrder in Hsub as [m [Hm Hmin]]...
  apply CompE in Hm as [Hmw Hma].
  apply Hma. apply Hind... intros k Hkw Hkm.
  destruct (classic (k ∈ A))... exfalso.
  assert (Hk: k ∈ ω - A) by (apply CompI; auto).
  apply Hmin in Hk as [].
  - eapply lt_irrefl... eapply nat_trans...
  - subst. eapply lt_irrefl...
Qed.

Theorem ω_ind_strong_0 : ∀ C, C ⊆ ω →
  (∀n ∈ C, ∃m ∈ C, m ∈ n) →
  C = 0.
Proof with eauto.
  intros C HC Hincr.
  destruct (classic (C = 0)) as [H0|H0]... exfalso.
  pose proof (ω_wellOrder C H0 HC) as [m [Hm Hmin]]...
  pose proof (Hincr m Hm) as [n [Hnc Hnm]]. apply HC in Hnc as Hn.
  pose proof (Hmin n Hnc) as [].
  - eapply lt_irrefl. apply Hn. eapply nat_trans; revgoals...
  - subst. eapply lt_irrefl...
Qed.

Lemma leq_add_enlarge : ∀ m n ∈ ω, m ≤ m + n.
Proof with neauto.
  intros k Hk n Hn. generalize dependent k.
  set {n ∊ ω | λ n, ∀ k, k ∈ ω → k ≤ k + n} as N.
  ω_induction N Hn; intros k Hk.
  - rewrite add_ident...
  - rewrite add_m_n... assert (Hk' := Hk).
    apply IH in Hk' as []; left.
    apply leq_iff_lt_suc... apply add_ran...
    rewrite <- H...
Qed.

Lemma lt_add_enlarge : ∀ m n ∈ ω, ∀ p ∈ m, p ∈ m + n.
Proof with eauto.
  intros k Hk n Hn. generalize dependent k.
  set {n ∊ ω | λ n, ∀ k, k ∈ ω → ∀ p ∈ k, p ∈ k + n} as N.
  ω_induction N Hn; intros k Hk p Hp.
  - rewrite add_ident...
  - assert (Hpw: p ∈ ω) by (eapply ω_trans; eauto).
    rewrite add_m_n... apply leq_iff_lt_suc...
    apply add_ran... left. apply IH...
Qed.

Lemma lt_add_shrink : ∀ m n p ∈ ω, m + n ∈ p → m ∈ p.
Proof with neauto.
  intros k Hk n Hn.
  set {n ∊ ω | λ n, ∀ p ∈ ω, k + n ∈ p → k ∈ p} as N.
  ω_induction N Hn; intros p Hp H.
  - rewrite add_ident in H...
  - rewrite add_m_n in H... apply IH...
    eapply nat_trans; revgoals...
Qed.

Lemma leq_mul_enlarge : ∀ m n ∈ ω, m ≤ m ⋅ n⁺.
Proof with eauto.
  intros m Hm n Hn. apply leq_iff_neg_lt...
  apply mul_ran... apply ω_inductive... intros Hc.
  rewrite mul_m_n in Hc...
  apply lt_add_shrink in Hc; try apply mul_ran...
  eapply lt_irrefl; revgoals...
Qed.

Lemma not_lt_gt : ∀ m n ∈ ω, m ∈ n → n ∈ m → ⊥.
Proof.
  intros m Hm n Hn Hlt Hgt. eapply lt_irrefl. apply Hm.
  eapply nat_trans; eauto.
Qed.

Lemma not_lt_self : ∀ m n ∈ ω, m = n → n ∈ m → ⊥.
Proof.
  intros m Hm n Hn Heq Hlt. subst. eapply lt_irrefl; eauto.
Qed.

Lemma not_leq_gt : ∀ m n ∈ ω, m ≤ n → n ∈ m → ⊥.
Proof with eauto.
  intros m Hm n Hn Hleq Hgt. destruct Hleq.
  - eapply not_lt_gt; revgoals...
  - eapply not_lt_self; revgoals...
Qed.

Lemma ω_not_dense : ∀m ∈ ω, ¬∃n ∈ ω, m ∈ n ∧ n ∈ m⁺.
Proof with eauto.
  intros m Hm [n [Hn [Hmn Hnm]]].
  apply BUnionE in Hnm as [Hnm|Heq].
  - eapply lt_irrefl... eapply nat_trans...
  - apply SingE in Heq. subst. eapply lt_irrefl...
Qed.
