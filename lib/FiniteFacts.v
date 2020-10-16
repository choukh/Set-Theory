(** Coq coding by choukh, Oct 2020 **)

Require Import ZFC.EST6_2.
Require Import Coq.Logic.FinFun.

(* 有限集添加一个元素仍是有限集 *)
Lemma finite_set_adding_one_still_finite : ∀ A a,
  finite A → finite (A ∪ ⎨a⎬).
Proof with auto.
  intros * Hfa.
  destruct (classic (disjoint A ⎨a⎬)).
  - destruct Hfa as [m [Hm HA]].
    exists m⁺. split. apply ω_inductive...
    apply cardAdd_well_defined... apply disjoint_nat_single...
  - apply EmptyNE in H as [a' Ha].
    apply BInterE in Ha as [Ha Heq].
    apply SingE in Heq. subst a'.
    replace (A ∪ ⎨ a ⎬) with A...
    apply ExtAx. split; intros Hx.
    + apply BUnionI1...
    + apply BUnionE in Hx as []... apply SingE in H. subst x...
Qed.

(* 等势的集合分别除去一个元素仍然等势 *)
Lemma eqnum_sets_removing_one_element_still_eqnum :
  ∀ A B a b, A ∪ ⎨a⎬ ≈ B ∪ ⎨b⎬ →
  disjoint A ⎨a⎬ → disjoint B ⎨b⎬ → A ≈ B.
Proof with eauto; try congruence.
  intros * [f Hf] Hdja Hdjb. assert (Hf' := Hf).
  destruct Hf' as [Hi [Hd Hr]].
  set (FuncSwapValue f a f⁻¹[b]) as g.
  assert (Ha: a ∈ A ∪ ⎨a⎬) by (apply BUnionI2; auto).
  assert (Hbr: b ∈ ran f). { rewrite Hr. apply BUnionI2... }
  assert (Hb: f⁻¹[b] ∈ A ∪ ⎨a⎬). {
    destruct Hi as [Hff Hs].
    rewrite <- Hd, <- inv_ran. eapply ap_ran. split...
    apply inv_func_iff_sr... rewrite inv_dom...
  }
  apply (bijection_swap_value _ _ _ _ Ha _ Hb) in Hf as Hg.
  assert (Hga: g[a] = b). {
    apply func_ap... destruct Hg as [[Hg _] _]...
    apply SepI. apply CProdI... zfcrewrite.
    destruct (ixm (a = a))... rewrite inv_ran_reduction... 
  }
  clear Hf Hi Hd Hr Ha Hbr Hb.
  destruct Hg as [Hi [Hd Hr]]. assert (Hi' := Hi).
  destruct Hi as [Hg Hs].
  exists (g ↾ A). split; [|split].
  - apply restr_injective...
  - apply restr_dom... intros x Hx. subst g.
    rewrite Hd. apply BUnionI1...
  - apply ExtAx. intros y. split; intros Hy.
    + apply ranE in Hy as [x Hp].
      apply restrE2 in Hp as [Hp Hx].
      apply ranI in Hp as Hy. subst g. rewrite Hr in Hy.
      apply BUnionE in Hy as []...
      apply SingE in H. subst y. apply func_ap in Hp...
      rewrite <- Hp in Hga. cut (a = x).
      * intros H. subst x. exfalso. eapply disjointE.
        apply Hdja. apply Hx. apply SingI.
      * eapply injectiveE...
        rewrite Hd. apply BUnionI2...
        rewrite Hd. apply BUnionI1...
    + assert (y ∈ ran g). { subst g. rewrite Hr. apply BUnionI1... }
      apply ranE in H as [x Hp]. apply domI in Hp as Hx.
      subst g. rewrite Hd in Hx. apply BUnionE in Hx as [].
      * eapply ranI. apply restrI...
      * apply SingE in H. subst x. apply func_ap in Hp...
        rewrite <- Hp, Hga in Hy. exfalso. eapply disjointE.
        apply Hdjb. apply Hy. apply SingI.
Qed.

(* 与后继数等势的集合非空 *)
Lemma set_eqnum_suc_nonempty : ∀ A, ∀n ∈ ω, A ≈ n⁺ → ⦿ A.
Proof with eauto.
  intros A n Hn HA. apply EmptyNE.
  destruct (classic (A = ∅))... exfalso. subst A.
  symmetry in HA. apply eqnum_empty in HA. eapply suc_neq_0...
Qed.

(* 从集合中取出一个元素组成单集，它与取完元素后的集合的并等于原集合 *)
Lemma split_one_element : ∀ A a, a ∈ A → A = (A - ⎨a⎬) ∪ ⎨a⎬.
Proof with auto.
  intros. apply ExtAx. split; intros Hx.
  - destruct (classic (x = a)).
    + subst x. apply BUnionI2...
    + apply BUnionI1. apply SepI...
      intros contra. apply SingE in contra...
  - apply BUnionE in Hx as [].
    + apply SepE in H0 as []...
    + apply SingE in H0. subst x...
Qed.

(* 从有限集中取出一个元素则基数减1 *)
Lemma finite_set_remove_one_element : ∀ A a, ∀n ∈ ω,
  (A - ⎨a⎬) ∪ ⎨a⎬ ≈ n⁺ → A - ⎨a⎬ ≈ n.
Proof with eauto.
  intros * n Hn Hqn.
  eapply eqnum_sets_removing_one_element_still_eqnum...
  apply disjointI. intros [x [H1 H2]]. apply SepE in H1 as []...
  apply disjoint_nat_single...
Qed.

(* 有限集里的补集是有限集 *)
Lemma comp_finite : ∀ A B, finite A → finite (A - B).
Proof with auto.
  intros * [n [Hn Hqn]]. generalize dependent A.
  set {n ∊ ω | λ n, ∀ A, A ≈ n → finite (A -B)} as N.
  ω_induction N Hn; intros A Hqn.
  - apply eqnum_empty in Hqn. subst A.
    rewrite empty_comp. apply empty_finite.
  - apply set_eqnum_suc_nonempty in Hqn as Hne...
    destruct Hne as [a Ha].
    apply split_one_element in Ha. rewrite Ha in *.
    apply finite_set_remove_one_element in Hqn... rewrite union_comp.
    apply bunion_finite. apply IH...
    destruct (classic (a ∈ B)).
    + replace (⎨a⎬ - B) with ∅. apply empty_finite.
      apply ExtAx. split; intros Hx. exfalso0. exfalso.
      apply SepE in Hx as [Hx Hx']. apply SingE in Hx; subst...
    + replace (⎨a⎬ - B) with (⎨a⎬)...
      apply ExtAx. split; intros Hx.
      * apply SingE in Hx; subst. apply SepI...
      * apply SepE in Hx as []...
Qed.

(* 二元并的替代等于替代的二元并 *)
Lemma bunion_of_repl_eq_repl_of_bunion : ∀ F A B,
  {F | x ∊ A ∪ B} = {F | x ∊ A} ∪ {F | x ∊ B}.
Proof with auto.
  intros; apply ExtAx; intros y; split; intros Hy.
  - apply ReplAx in Hy as [x [Hx Heq]];
    apply BUnionE in Hx as [];
    [apply BUnionI1|apply BUnionI2];
    apply ReplAx; exists x; split...
  - apply BUnionE in Hy as [];
    apply ReplAx in H as [x [Hx Heq]];
    apply ReplAx; exists x; split; auto;
    [apply BUnionI1|apply BUnionI2]...
Qed.

(* 任意集合与其一对一的替代等势 *)
Lemma eqnum_repl : ∀ F A, Injective F → A ≈ {F | x ∊ A}.
Proof with auto.
  intros. set (Func A {F | x ∊ A} (λ x, F x)) as f.
  exists f. apply meta_bijective.
  - intros x Hx. apply ReplAx. exists x. split...
  - intros x1 H1 x2 H2 Heq. apply H...
  - intros y Hy. apply ReplAx in Hy...
Qed.

(* 任意单集与其任意替代等势 *)
Lemma eqnum_repl_single : ∀ F a, ⎨a⎬ ≈ {F | x ∊ ⎨a⎬}.
Proof with auto.
  intros. set (Func ⎨a⎬ {F | x ∊ ⎨a⎬} (λ x, F x)) as f.
  exists f. apply meta_bijective.
  - intros x Hx. apply ReplAx. exists x. split...
  - intros x1 H1 x2 H2 _.
    apply SingE in H1. apply SingE in H2. congruence.
  - intros y Hy. apply ReplAx in Hy...
Qed.

(* 任意单集的任意替代是有限集 *)
Lemma repl_single_finite : ∀ F a, finite {F | x ∊ ⎨a⎬}.
Proof with auto.
  intros. exists 1. split. nauto.
  rewrite <- eqnum_repl_single. apply eqnum_single_one.
Qed.

(* 有限集的替代仍是有限集 *)
Lemma repl_finite : ∀ F A, finite A → finite {F | x ∊ A}.
Proof with auto.
  intros * [n [Hn Hqn]].
  generalize dependent A.
  set {n ∊ ω | λ n, ∀ A, A ≈ n → finite {F | x ∊ A}} as N.
  ω_induction N Hn; intros A Hqn.
  - apply eqnum_empty in Hqn. subst A.
    rewrite repl_empty. apply empty_finite.
  - apply set_eqnum_suc_nonempty in Hqn as Hne...
    destruct Hne as [a Ha].
    apply split_one_element in Ha. rewrite Ha in *.
    apply finite_set_remove_one_element in Hqn...
    rewrite bunion_of_repl_eq_repl_of_bunion.
    apply bunion_finite. apply IH... apply repl_single_finite.
Qed.

(* 有限集与任意集合的交是有限集 *)
Lemma binter_finite_r : ∀ A B, finite B → finite (A ∩ B).
Proof with auto.
  intros * [n [Hn Hqn]].
  generalize dependent B.
  set {n ∊ ω | λ n, ∀ B, B ≈ n → finite (A ∩ B)} as N.
  ω_induction N Hn; intros B Hqn.
  - apply eqnum_empty in Hqn. subst B.
    rewrite binter_empty. apply empty_finite.
  - apply set_eqnum_suc_nonempty in Hqn as Hne...
    destruct Hne as [a Ha].
    apply split_one_element in Ha. rewrite Ha in *.
    apply finite_set_remove_one_element in Hqn...
    rewrite binter_bunion_distr.
    apply bunion_finite. apply IH...
    destruct (classic (a ∈ A)).
    + replace (A ∩ ⎨a⎬) with ⎨a⎬. apply single_finite.
      apply ExtAx. split; intros Hx.
      * apply SingE in Hx; subst. apply BInterI...
      * apply BInterE in Hx as []...
    + replace (A ∩ ⎨a⎬) with ∅. apply empty_finite.
      apply ExtAx. split; intros Hx. exfalso0. exfalso.
      apply BInterE in Hx as []. apply SingE in H1; subst...
Qed.

Corollary binter_finite_l : ∀ A B, finite A → finite (A ∩ B).
Proof.
  intros. rewrite binter_comm. apply binter_finite_r. apply H.
Qed.

(** properties about finite subset of ω **)

(* 自然数集子集里存在极大元 *)
Definition max_number : set → set → Prop := λ m N,
  m ∈ N ∧ ∀n ∈ N, n ⊆ m.

(* 自然数集子集的阿基米德性 *)
Definition archimedean : set → Prop := λ N,
  ∀n ∈ ω, ∃m ∈ N, n ∈ m.

(* 具有阿基米德性的自然数集子集没有极大元 *)
Lemma archimedean_impl_no_max_number : ∀ N, N ⊆ ω →
  archimedean N → ¬∃m, max_number m N.
Proof.
  intros N Hsub Hnmax [m [Hm Hmax]].
  apply Hsub in Hm.
  pose proof (Hnmax _ Hm) as [p [Hp Hpm]]. apply Hmax in Hp.
  apply Hp in Hpm. apply (lt_irrefl m); auto.
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

(* 没有极大元的自然数集子集具有阿基米德性 *)
Lemma archimedean_if_no_max_number : ∀ N, ⦿ N → N ⊆ ω →
  (¬∃m, max_number m N) → archimedean N.
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

(* 自然数集非空子集具有阿基米德性当且仅当它没有极大元 *)
Theorem archimedean_iff_no_max_number : ∀ N, ⦿ N → N ⊆ ω →
  archimedean N ↔ ¬∃m, max_number m N.
Proof with auto.
  intros N Hne Hsub. split; intros H.
  - apply archimedean_impl_no_max_number...
  - apply archimedean_if_no_max_number...
Qed.

(* 自然数集的非空有限子集有极大元 *)
Lemma finite_subset_of_ω_is_bounded : ∀ N, ⦿ N → N ⊆ ω →
  finite N → ∃ m, max_number m N.
Proof with auto; try congruence.
  intros N Hne Hsub [n [Hn Hqn]].
  generalize dependent N.
  set {n ∊ ω | λ n, ∀ N, ⦿ N → N ⊆ ω → N ≈ n → ∃ m, max_number m N} as M.
  ω_induction M Hn; intros N Hne Hsub Hcd. {
    apply eqnum_empty in Hcd. apply EmptyNI in Hne. exfalso...
  }
  clear M Hn n. destruct Hne as [k Hk].
  destruct (classic (max_number k N)). exists k...
  apply not_and_or in H as []. exfalso...
  apply set_not_all_ex_not in H as [p [Hp Hkp]].
  apply Hsub in Hk as Hkw. apply Hsub in Hp as Hpw.
  apply lt_iff_not_sub in Hkp...
  apply split_one_element in Hk as HeqN. rewrite HeqN in Hcd.
  apply finite_set_remove_one_element in Hcd...
  specialize IH with (N - ⎨k⎬) as [q [Hq Hmax]]...
  { exists p. apply SepI... apply SingNI...
    intros Heq. apply (lt_irrefl k)...
  } {
    eapply sub_tran...
  }
  apply SepE in Hq as [Hq _]... apply Hsub in Hq as Hqw.
  destruct (classic (p ⊆ q)) as [Hpq|Hqp].
  - exists q. split... intros n Hn.
    destruct (classic (n = k)).
    + rewrite H. apply lt_iff_psub... apply Hpq...
    + apply Hmax. apply SepI... apply SingNI...
  - exists p. split... intros n Hn.
    apply lt_iff_not_sub in Hqp...
    destruct (classic (n = k)).
    + rewrite H. apply lt_iff_psub...
    + eapply sub_tran.
      * apply Hmax. apply SepI... apply SingNI...
      * apply lt_iff_psub...
Qed.

(* 自然数集的没有极大元的非空子集是无限集 *)
Corollary unbound_subset_of_ω_is_infinite : ∀ N, ⦿ N → N ⊆ ω →
  archimedean N → infinite N.
Proof with eauto.
  intros N Hne Hsub Harc Hfin.
  eapply archimedean_iff_no_max_number...
  apply finite_subset_of_ω_is_bounded...
Qed.

(* 集合除去自身的一个元素再放回去，集合不变 *)
Lemma remove_one_member_then_return : ∀ A a, a ∈ A → A - ⎨a⎬ ∪ ⎨a⎬ = A.
Proof with auto.
  intros. apply ExtAx. split; intros Hx.
  - apply BUnionE in Hx as [].
    + apply SepE in H0 as []...
    + apply SingE in H0. subst...
  - destruct (classic (x = a)).
    + subst. apply BUnionI2...
    + apply BUnionI1. apply SepI... apply SingNI...
Qed.

(* 集合加入一个不是自身的元素再去掉，集合不变 *)
Lemma add_one_member_then_remove : ∀ A a, a ∉ A → A ∪ ⎨a⎬ - ⎨a⎬ = A.
Proof with auto.
  intros. apply ExtAx. split; intros Hx.
  - apply SepE in Hx as [].
    apply BUnionE in H0 as []... exfalso...
  - apply SepI. apply BUnionI1...
    apply SingNI. intros Heq. congruence.
Qed.

(* 自然数集的有极大元的子集是非空有限集 *)
Lemma bounded_subset_of_ω_is_finite : ∀ N, N ⊆ ω →
  (∃ m, max_number m N) → ⦿ N ∧ finite N.
Proof with nauto.
  intros N Hsub [n [Hn Hmax]]. split. exists n...
  apply Hsub in Hn as Hnw. generalize dependent N.
  set {n ∊ ω | λ n, ∀ N, N ⊆ ω → n ∈ N → (∀ k ∈ N, k ⊆ n) → finite N} as M.
  ω_induction M Hnw; intros N Hsub Hn Hmax.
  - exists 1. split... cut (N = ⎨∅⎬). {
      intros H. rewrite H. apply eqnum_single_one.
    }
    apply ExtAx. split; intros Hx.
    + apply Hmax in Hx. apply sub_empty in Hx. subst x...
    + apply SingE in Hx. subst x...
  - pose proof (suc_neq_n m Hm) as Hnq.
    assert (Hstar: ∀k ∈ N, k ∉ ⎨m⁺⎬ → k ⊆ m). {
      intros k Hk Hk'. apply Hsub in Hk as Hkw. apply SingNE in Hk'.
      destruct (classic (k ⊆ m)) as [|Hmk]... exfalso.
      apply lt_iff_not_sub in Hmk; [|auto|apply Hsub]...
      apply lt_iff_leq_suc in Hmk...
      apply leq_iff_sub in Hmk; [|apply ω_inductive|]...
      apply Hk'. apply sub_asym... apply Hmax...
    }
    destruct (classic (m ∈ N)) as [HmN|HmN].
    + replace N with (N - ⎨m⁺⎬ ∪ ⎨m⁺⎬).
      apply bunion_finite... apply IH.
      * eapply sub_tran...
      * apply SepI... apply SingNI...
      * intros k Hk. apply SepE in Hk as [Hk Hk']. apply Hstar...
      * apply remove_one_member_then_return...
    + replace N with (N ∪ ⎨m⎬ - ⎨m⁺⎬ - ⎨m⎬ ∪ ⎨m⁺⎬).
      apply bunion_finite... apply comp_finite. apply IH.
      * eapply sub_tran... eapply sub_tran...
        intros x Hx. apply BUnionE in Hx as [].
        apply Hsub... apply SingE in H. subst...
      * apply SepI. apply BUnionI2... apply SingNI...
      * intros k Hk. apply SepE in Hk as [Hk Hk'].
        apply BUnionE in Hk as [Hk|Hk]. apply Hstar...
        apply SingE in Hk; subst...
      * rewrite union_comp.
        replace (⎨m⎬ - ⎨m⁺⎬) with ⎨m⎬. {
          rewrite add_one_member_then_remove.
          - rewrite remove_one_member_then_return...
          - intros H. apply SepE in H as []...
        }
        apply ExtAx. split; intros Hx.
        apply SepI... apply SingE in Hx; subst. apply SingNI...
        apply SepE in Hx as []...
Qed.

(* 自然数集的无限子集没有极大元 *)
Corollary infinite_subset_of_ω_is_unbound : ∀ N, N ⊆ ω →
  infinite N → (⦿ N ∧ archimedean N).
Proof with auto.
  intros N Hsub Hinf.
  apply infinite_set_nonempty in Hinf as Hne. split...
  apply archimedean_iff_no_max_number...
  intros Hmax. apply Hinf.
  apply bounded_subset_of_ω_is_finite...
Qed.

(* 自然数集的子集是非空有限集当且仅当其有极大元 *)
Theorem subset_of_ω_is_finite_iff_bounded : ∀ N, N ⊆ ω →
  (⦿ N ∧ finite N) ↔ ∃ m, max_number m N.
Proof with auto.
  intros N Hsub. split.
  - intros [Hne Hfin].
    apply finite_subset_of_ω_is_bounded...
  - apply bounded_subset_of_ω_is_finite...
Qed.

(* 自然数集的子集是无限集当且仅当其非空且没有极大元 *)
Theorem subset_of_ω_is_infinite_iff_unbound : ∀ N, N ⊆ ω →
  infinite N ↔ (⦿ N ∧ archimedean N).
Proof with auto.
  intros N Hsub. split.
  - apply infinite_subset_of_ω_is_unbound...
  - intros []. apply unbound_subset_of_ω_is_infinite...
Qed.
