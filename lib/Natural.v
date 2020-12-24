(** Coq coding by choukh, Aug 2020 **)

Require Export ZFC.EX4.

(* 递归单射 *)
Lemma injective_recursion : ∀ f A a, f: A ⇔ A → a ∈ A - ran f →
  ∃ h, h: ω ⇔ A ∧ h[∅] = a ∧ ∀n ∈ ω, h[n⁺] = f[h[n]].
Proof with eauto.
  intros f A a Hf Ha.
  apply injection_is_func in Hf as [Hf Hi].
  assert (Ha' := Ha). apply SepE in Ha' as [Ha' _].
  pose proof (ω_recursion f A a Hf Ha') as [h [Hh [Hh0 Hhn]]].
  exists h. split... apply injection_is_func.
  split... eapply ex4_8...
Qed.

(* 自然数集子集最小元的两种定义等价 *)
Lemma nat_ε_minimum_iff_sub_minimum : ∀ m N, N ⊆ ω →
  ε_minimum m N ↔ sub_minimum m N.
Proof with auto.
  split; intros [Hm Hmin]; split; auto; intros n Hn;
  apply Hmin in Hn as Hle; (apply leq_iff_sub; [apply H..|])...
Qed.

(* 自然数集子集最大元的两种定义等价 *)
Lemma nat_ε_maximum_iff_sub_maximum : ∀ m N, N ⊆ ω →
  ε_maximum m N ↔ sub_maximum m N.
Proof with auto.
  split; intros [Hm Hmax]; split; auto; intros n Hn;
  apply Hmax in Hn as Hle; (apply leq_iff_sub; [apply H..|])...
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
  apply leq_iff_lt_suc in Hpq...
  apply leq_iff_sub in Hpq... apply Hpq...
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
    exists m. split...
  }
  clear Hnmax. apply Hsub in Hk as Hkw.
  intros n Hn. destruct (classic (n ∈ N)). apply Larger...
  set {n ∊ ω | λ n, ∃m ∈ N, n ∈ m} as M.
  ω_induction M Hn.
  - apply Larger in Hk as [m [Hm Hkm]].
    exists m. split... apply nq_0_gt_0.
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
