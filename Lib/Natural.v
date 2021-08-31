(** Coq coding by choukh, Aug 2020 **)

Require Export ZFC.Theory.EX4.

Definition woset := λ A R, wellOrder R A.

(* 0不等于1 *)
Lemma contra_0_1 : Embed 0 ≠ 1.
Proof. intros H. eapply suc_neq_0. eauto. Qed.
Global Hint Immediate contra_0_1 : core.

(* 1不等于0 *)
Lemma contra_1_0 : Embed 1 ≠ 0.
Proof. apply suc_neq_0. Qed.
Global Hint Immediate contra_1_0 : core.

(* 1不等于2 *)
Lemma contra_1_2 : Embed 1 ≠ 2.
Proof with neauto.
  intros Heq. assert (1 ∈ 2). apply BUnionI2...
  rewrite Heq in H. eapply nat_irrefl; revgoals...
Qed.

(* 3里有0，1，2 *)
Lemma three_iff : ∀ n, n ∈ 3 ↔ n = 0 ∨ n = 1 ∨ n = 2.
Proof with auto.
  split.
  - intros Hn. apply BUnionE in Hn as [].
    + apply BUnionE in H as [].
      * apply BUnionE in H as []. exfalso0.
        apply SingE in H...
      * apply SingE in H...
    + apply SingE in H...
  - intros [|[]]; subst.
    + do 2 apply BUnionI1...
    + apply BUnionI1. apply BUnionI2...
    + apply BUnionI2...
Qed.

(* 2的幂集 *)
Lemma power_two : 𝒫 2 = 3 ∪ {{1,},}.
Proof with nauto.
  ext Hx.
  - destruct (empty_or_not x) as [|[a Ha]]. {
      subst. do 3 apply BUnionI1...
    }
    destruct (classic (x = 1)) as [|H1]. {
      subst. apply BUnionI1. apply BUnionI1...
    }
    destruct (classic (x = 2)) as [|H2]. {
      subst. apply BUnionI1. apply BUnionI2...
    }
    destruct (classic (x = {1,})) as [|Hs]. {
      subst. apply BUnionI2...
    }
    exfalso. apply PowerAx in Hx.
    apply Hx in Ha as Ha2. rewrite two in Ha2.
    apply TwoE in Ha2 as []; subst. {
      destruct (classic (1 ∈ x)).
      - apply H2. ext w Hw.
        + apply Hx...
        + rewrite two in Hw.
          apply TwoE in Hw as []; subst... rewrite <- one...
      - apply H1. ext w Hw.
        + apply Hx in Hw as Hw2. rewrite two in Hw2.
          apply TwoE in Hw2 as []; subst. apply BUnionI2...
          exfalso. apply H. rewrite one...
        + rewrite one in Hw. apply SingE in Hw; subst...
    } {
      destruct (classic (0 ∈ x)).
      - apply H2. ext w Hw.
        + apply Hx...
        + rewrite two in Hw.
          apply TwoE in Hw as []; subst...
      - apply Hs. ext w Hw.
        + apply Hx in Hw as Hw2. rewrite two in Hw2.
          apply TwoE in Hw2 as []; subst.
          exfalso... rewrite one...
        + apply SingE in Hw; subst. rewrite one...
    }
  - apply PowerAx. intros y Hy.
    apply BUnionE in Hx as [].
    + apply three_iff in H as [|[]]; subst...
      exfalso0. rewrite one in Hy.
      apply SingE in Hy; subst. apply BUnionI1...
    + apply SingE in H; subst.
      apply SingE in Hy; subst. apply BUnionI2...
Qed.

Lemma suc_comp : ∀n ∈ ω, n⁺ - n = {n,}.
Proof with auto.
  intros n Hn. ext Hx.
  - apply SepE in Hx as [H1 H2].
    apply BUnionE in H1 as []... exfalso...
  - apply SingE in Hx; subst. apply SepI.
    apply BUnionI2... apply nat_irrefl...
Qed.

(* 自然数减法 *)
Lemma nat_subtr : ∀ m n ∈ ω, m ⋸ n → ∃d ∈ ω, m + d = n.
Proof with nauto.
  intros k Hk n Hn.
  ω_induction n; intros [].
  - exfalso0.
  - subst. exists ∅. split... rewrite add_0_r...
  - apply le_iff_lt_suc in H...
    apply IH in H as [d [Hd H]].
    exists d⁺. split. apply ω_inductive...
    rewrite <- H, suc, suc, add_assoc... apply add_ran...
  - exists 0. split... subst. rewrite add_0_r...
Qed.

Lemma nat_subtr' : ∀ m n ∈ ω, m ∈ n → ∃d ∈ ω, m + d = n ∧ d ≠ 0.
Proof with nauto.
  intros k Hk n Hn.
  ω_induction n; intros Hlt. exfalso0.
  apply le_iff_lt_suc in Hlt as []...
  - apply IH in H as [d [Hd [H1 H2]]].
    exists d⁺. split. apply ω_inductive...
    split. rewrite add_suc... subst... apply suc_neq_0.
  - exists 1. split. apply ω_inductive...
    split. rewrite suc... subst... apply suc_neq_0.
Qed.

(* 自然数是奇数或偶数 *)
Lemma even_or_odd : ∀n ∈ ω, even n ∨ odd n.
Proof. intros n Hn. apply ex4_14. apply Hn. Qed.

(* 自然数不能同时是奇数和偶数 *)
Lemma no_even_and_odd : ∀n ∈ ω, ¬ (even n ∧ odd n).
Proof. intros n Hn. apply ex4_14. apply Hn. Qed.

(* 自然数是偶数当且仅当其后继是奇数 *)
Lemma even_iff_suc_odd : ∀n ∈ ω, even n ↔ odd n⁺.
Proof with nauto.
  intros n Hn. split; intros [m [Hm H]].
  - exists m. split... rewrite <- H. apply suc...
  - exists m. split... rewrite suc in H...
    apply add_cancel in H... apply mul_ran...
Qed.

(* 自然数是奇数当且仅当其后继是偶数 *)
Lemma odd_iff_suc_even : ∀n ∈ ω, odd n ↔ even n⁺.
Proof with neauto.
  intros n Hn. split; intros [m [Hm H]].
  - exists m⁺. split. apply ω_inductive...
    assert (H2m: 2 ⋅ m ∈ ω). apply mul_ran...
    rewrite H, suc, add_assoc, add_1_1...
    rewrite add_comm, mul_suc... apply add_ran...
  - ω_destruct m; subst m.
    + rewrite mul_0_r in H... exfalso. eapply suc_neq_0...
    + rename n' into k. exists k. split...
      assert (H2k: 2 ⋅ k ∈ ω). apply mul_ran...
      rewrite mul_suc, add_comm in H...
      rewrite <- add_1_1 in H at 2...
      rewrite suc, <- add_assoc in H...
      apply add_cancel in H... apply add_ran...
Qed.

(* 两个自然数的二元并等于它们中较大的一个 *)
Lemma bunion_of_nats_eq_l : ∀ m n ∈ ω, m ⋸ n → m ∪ n = n.
Proof with auto.
  intros m Hm n Hn Hle.
  apply le_iff_sub in Hle...
  ext Hx.
  - apply BUnionE in Hx as []...
  - apply BUnionI2...
Qed.

Lemma bunion_of_nats_eq_r : ∀ m n ∈ ω, n ⋸ m → m ∪ n = m.
Proof with auto.
  intros m Hm n Hn Hle.
  apply le_iff_sub in Hle...
  ext Hx.
  - apply BUnionE in Hx as []...
  - apply BUnionI1...
Qed.

(* 自然数集子集最小元的两种定义等价 *)
Lemma nat_ε_minimum_iff_sub_minimum : ∀ m N, N ⊆ ω →
  ε_minimum m N ↔ sub_minimum m N.
Proof with auto.
  split; intros [Hm Hmin]; split; auto; intros n Hn;
  apply Hmin in Hn as Hle; (apply le_iff_sub; [apply H..|])...
Qed.

(* 自然数集子集最大元的两种定义等价 *)
Lemma nat_ε_maximum_iff_sub_maximum : ∀ m N, N ⊆ ω →
  ε_maximum m N ↔ sub_maximum m N.
Proof with auto.
  split; intros [Hm Hmax]; split; auto; intros n Hn;
  apply Hmax in Hn as Hle; (apply le_iff_sub; [apply H..|])...
Qed.

(* 自然数集子集的阿基米德性 *)
Definition nat_archimedean := λ N, ∀n ∈ ω, ∃m ∈ N, n ∈ m.

(* 具有阿基米德性的自然数集子集没有最大元 *)
Lemma nat_archimedean_impl_no_maximum : ∀ N, N ⊆ ω →
  nat_archimedean N → ¬∃m, sub_maximum m N.
Proof.
  intros N Hsub Hnmax [m [Hm Hmax]].
  apply Hsub in Hm.
  pose proof (Hnmax _ Hm) as [p [Hp Hpm]]. apply Hmax in Hp.
  apply Hp in Hpm. apply (nat_irrefl m); auto.
Qed.

(* m < p < q → m + 1 < q *)
Lemma lt_lt_impl_suc_lt : ∀ m p q ∈ ω, m ∈ p → p ∈ q → m⁺ ∈ q.
Proof with auto.
  intros m Hm p Hp q Hq Hmp Hpq.
  ω_destruct q. subst q. exfalso0. subst q.
  apply (suc_preserve_lt _ Hm _ Hn').
  apply le_iff_lt_suc in Hpq...
  apply le_iff_sub in Hpq...
Qed.

(* 没有最大元的自然数非空子集具有阿基米德性 *)
Lemma nat_archimedean_if_no_maximum : ∀ N, ⦿ N → N ⊆ ω →
  (¬∃m, sub_maximum m N) → nat_archimedean N.
Proof with neauto.
  intros N [k Hk] Hsub Hnmax.
  assert (Larger: ∀n ∈ N, ∃m ∈ N, n ∈ m). {
    intros n Hn. eapply not_ex_all_not in Hnmax.
    apply not_and_or in Hnmax as []. exfalso...
    apply set_not_all_ex_not in H as [m [Hm Hnm]].
    apply lt_iff_not_sub in Hnm; [|apply Hsub..]...
  }
  clear Hnmax. apply Hsub in Hk as Hkw.
  intros n Hn. destruct (classic (n ∈ N)). apply Larger...
  ω_induction n.
  - apply Larger in Hk as [m [Hm Hkm]].
    exists m. split... apply neq_0_gt_0.
    apply Hsub... intros H0. subst m. exfalso0.
  - destruct IH as [p [Hp Hmp]].
    pose proof (Larger _ Hp) as [q [Hq Hpq]].
    apply Hsub in Hp. apply Hsub in Hq as Hqw.
    exists q. split... apply (lt_lt_impl_suc_lt _ Hm _ Hp _ Hqw)...
Qed.

(* 自然数非空子集具有阿基米德性当且仅当它没有最大元 *)
Theorem nat_archimedean_iff_no_maximum : ∀ N, ⦿ N → N ⊆ ω →
  nat_archimedean N ↔ ¬∃m, sub_maximum m N.
Proof with auto.
  intros N Hne Hsub. split; intros H.
  - apply nat_archimedean_impl_no_maximum...
  - apply nat_archimedean_if_no_maximum...
Qed.

(* 递归单射 *)
Theorem injective_recursion : ∀ f A a, f: A ⇔ A → a ∈ A - ran f →
  ∃! h, h: ω ⇔ A ∧ h[∅] = a ∧ ∀n ∈ ω, h[n⁺] = f[h[n]].
Proof with eauto.
  intros f A a Hf Ha.
  apply injection_is_func in Hf as [Hf Hi].
  assert (Ha' := Ha). apply SepE in Ha' as [Ha' _].
  pose proof (ω_recursion_uniqueness f A a Hf Ha') as [h [[Hh [Hh0 Hhn]] H]].
  exists h. split.
  - split... apply injection_is_func. split... eapply ex4_8...
  - intros h' [Hh' [Hh'0 Hh'n]]. apply H. split...
    apply injection_is_func...
Qed.

Definition ω_recursionᵢₙⱼ_spec := λ F A a h,
  h: ω ⇔ A ∧ h[∅] = a ∧ ∀n ∈ ω, h[n⁺] = F[h[n]].

Definition ω_Recursionᵢₙⱼ := λ F A a,
  describe (ω_recursionᵢₙⱼ_spec F A a).

Lemma ω_recursionᵢₙⱼ_spec_intro : ∀ F A a,
  F: A ⇔ A → a ∈ A - ran F →
  ω_recursionᵢₙⱼ_spec F A a (ω_Recursionᵢₙⱼ F A a).
Proof.
  intros. apply (desc_spec (ω_recursionᵢₙⱼ_spec F A a)).
  apply injective_recursion; auto.
Qed.
