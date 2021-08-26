(** Adapted from "Elements of Set Theory" Chapter 6 **)
(** Coq coding by choukh, Sep 2020 **)

Require ZFC.Lib.Choice.
Require Import ZFC.Lib.ChoiceFacts.
Require Import ZFC.Lib.IndexedFamilyUnion.
Require Export ZFC.Theory.EST6_3.

(*** EST第六章4
  - 选择公理的系统考察
    + 单值化原则，选择函数，势的可比较性，佐恩引理，
  - 阿列夫零是最小的无限基数，戴德金无穷，
  - 基数的无限累加和，基数的无限累乘积 ***)

(* axiom of choice see lib/Choice *)

(* ==需要选择公理== *)
(* 基数具有可比较性 *)
Theorem card_comparability : AC_V →
  ∀ 𝜅 𝜆 ⋵ 𝐂𝐃, 𝜅 ≤ 𝜆 ∨ 𝜆 ≤ 𝜅.
Proof.
  intros AC5 𝜅 H𝜅 𝜆 H𝜆.
  pose proof (AC5 𝜅 𝜆) as []; [left|right]; split; auto.
Qed.

(* ==需要选择公理== *)
(* 基数具有连通性 *)
Corollary card_connected : AC_V →
  ∀ 𝜅 𝜆 ⋵ 𝐂𝐃, 𝜅 ≠ 𝜆 → 𝜅 <𝐜 𝜆 ∨ 𝜆 <𝐜 𝜅.
Proof.
  intros AC5 𝜅 H𝜅 𝜆 H𝜆 Hnq.
  destruct (card_comparability AC5 𝜅 H𝜅 𝜆) as [];
  auto; [left|right]; split; auto.
Qed.

(* 有限集在无限集里的补集是无限集 *)
Lemma comp_of_finite_is_infinite : ∀ A B, B ⊆ A →
  infinite A → finite B → infinite (A - B).
Proof with auto.
  intros A B Hsub Hinf [n [Hn H1]].
  intros [m [Hm H2]]. apply Hinf.
  exists (n + m). split. apply fin_cardAdd_ran...
  rewrite <- (bunion_comp_parent B A)...
  unfold CardAdd. rewrite <- CardAx0.
  apply cardAdd_well_defined.
  - rewrite <- eqnum_cprod_single...
  - rewrite <- eqnum_cprod_single...
  - apply disjointI. intros [x [Hx1 Hx2]].
    apply SepE2 in Hx2...
  - apply disjointify_0_1.
Qed.

(* 所有自然数都被无限集支配 *)
Lemma nat_dominated_by_infinite : ∀ A, ∀n ∈ ω, infinite A → n ≺ A.
Proof with eauto; try congruence.
  intros A n Hn Hinf.
  ω_induction n. {
    split. apply empty_dominated...
    intros Hqn. symmetry in Hqn. apply eqnum_empty in Hqn.
    apply infinite_set_nonempty in Hinf. apply EmptyNI in Hinf...
  }
  split; revgoals. {
    intros Hqn. apply Hinf. exists m⁺. split.
    apply ω_inductive... symmetry...
  }
  destruct IH as [[f [Hf [Hd Hr]]] Hnq].
  assert (Hinf': infinite (A - ran f)). {
    apply comp_of_finite_is_infinite...
    exists m. split... symmetry. exists f. split...
  }
  apply infinite_set_nonempty in Hinf' as [a Ha].
  exists (f ∪ ⎨<m, a>⎬). split; [|split].
  - apply bunion_injective...
    apply single_pair_injective. split.
    + intros x Hx. exfalso.
      apply BInterE in Hx as [H1 H2].
      apply domE in H2 as [y H2].
      apply SingE in H2. apply op_iff in H2 as [H2 _].
      rewrite H2, Hd in H1. eapply nat_irrefl...
    + intros y Hy. exfalso.
      apply BInterE in Hy as [H1 H2].
      apply ranE in H2 as [x H2].
      apply SingE in H2. apply op_iff in H2 as [_ H2].
      rewrite H2 in H1. apply SepE in Ha as [_ Ha]...
  - ext Hx.
    + apply domE in Hx as [y Hp]. apply BUnionE in Hp as [].
      * apply domI in H. rewrite Hd in H. apply BUnionI1...
      * apply SingE in H. apply op_iff in H as [Hx _].
        apply BUnionI2. rewrite Hx...
    + destruct Hf as [Hf _].
      apply BUnionE in Hx as [].
      * eapply domI. apply BUnionI1. apply func_correct...
      * apply SingE in H. rewrite H.
        eapply domI. apply BUnionI2. apply SingI. 
  - intros y Hy. apply ranE in Hy as [x Hp].
    apply BUnionE in Hp as [].
    + apply ranI in H. apply Hr...
    + apply SingE in H. apply op_iff in H as [_ H].
      subst y. apply SepE1 in Ha...
Qed.

(* 所有自然数都小于无限基数 *)
Corollary cardLt_infcard_n : ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, ∀n ∈ ω, n <𝐜 𝜅.
Proof with auto.
  intros 𝜅 [Hcd Hinf] n Hn.
  rewrite (card_of_card 𝜅), (card_of_nat n)...
  apply cardLt_iff. apply nat_dominated_by_infinite...
Qed.

(* ==需要选择公理== *)
(* ω是最小的无限集 *)
Theorem ω_is_the_least_infinite_set : AC_III → ∀ A, infinite A → ω ≼ A.
Proof with neauto; try congruence.
  intros AC3 A Hinf.
  pose proof (AC3 A) as [F [_ [_ Hch]]].
  set {B ∊ 𝒫 A | finite B} as 𝒜.
  set (Func 𝒜 𝒜 (λ B, B ∪ ⎨F[A - B]⎬)) as ℋ.
  assert (Hℋ: ℋ: 𝒜 ⇒ 𝒜). {
    apply meta_function. intros B HB.
    apply SepE in HB as [Hsub Hfin].
    apply PowerAx in Hsub. apply SepI.
    - apply PowerAx. intros x Hx.
      apply BUnionE in Hx as [Hx|Hx]. apply Hsub...
      apply SingE in Hx. subst. assert (A - B ⊆ A) by auto.
      apply H. apply Hch... apply infinite_set_nonempty.
      apply comp_of_finite_is_infinite...
    - apply add_one_still_finite_2...
  }
  pose proof (ω_recursion ℋ 𝒜 ∅) as [h [Hh [Hh0 Hhn]]]... {
    apply SepI... apply empty_in_all_power.
  }
  assert (Hne: ∀n ∈ ω, ⦿ (A - h[n])). {
    intros n Hn. apply infinite_set_nonempty.
    apply comp_of_finite_is_infinite...
    + intros x Hx. ω_destruct n; subst n.
      * rewrite Hh0 in Hx. exfalso0.
      * rewrite Hhn in Hx...
        assert (ℋ[h[n']] ∈ 𝒜). { eapply ap_ran... eapply ap_ran... }
        apply SepE in H as [H _]. apply PowerAx in H. apply H...
    + assert (h[n] ∈ 𝒜) by (eapply ap_ran; eauto).
      apply SepE2 in H...
  }
  set (Func ω A (λ n, F[A - h[n]])) as g.
  exists g. apply meta_injection.
  - intros n Hn. assert (Hsub: A - h[n] ⊆ A) by auto.
    apply Hsub. apply Hch...
  - cut (∀ m n ∈ ω, m ∈ n → F [A - h[m]] ≠ F [A - h[n]]). {
      intros Hcut. intros m Hm n Hn Heq.
      contra.
      apply nat_connected in H as []; auto;
      [|symmetry in Heq]; eapply Hcut; revgoals...
    }
    intros m Hm n Hn Hmn Heq.
    assert (Hgm: F[A - h[m]] ∈ h[m⁺]). {
      rewrite Hhn... unfold ℋ.
      rewrite meta_func_ap; [|auto|eapply ap_ran]... apply BUnionI2...
    }
    assert (Hgn: F[A - h[n]] ∈ A - h[n]). apply Hch...
    cut (h[m⁺] ⊆ h[n]). {
      intros Hcut. apply Hcut in Hgm. apply SepE2 in Hgn...
    }
    clear Heq Hgm Hgn g. generalize dependent m.
    ω_induction n; intros k Hk Hlt. exfalso0.
    intros x Hx. apply BUnionE in Hlt as [].
    + apply IH in Hx... rewrite Hhn... unfold ℋ.
      rewrite meta_func_ap; [|auto|eapply ap_ran]... apply BUnionI1...
    + apply SingE in H. subst...
Qed.

(* ==需要选择公理== *)
(* 阿列夫零是最小的无限基数 *)
Corollary aleph0_is_the_least_infinite_card : AC_III →
  ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, ℵ₀ ≤ 𝜅.
Proof with auto.
  intros AC3 𝜅 [Hcd Hinf]. rewrite (card_of_card 𝜅)...
  apply cardLeq_iff. apply ω_is_the_least_infinite_set...
Qed.

(* ==使用选择公理的代替证法== *)
Module AlternativeProofWithAC.
Import ZFC.Lib.Choice.

(* Check EST6_3.dominated_by_ω_iff_mapped_onto_by_ω *)
(* 任意非空集合被ω支配当且仅当它被ω满射 *)
Corollary dominated_by_ω_iff_mapped_onto_by_ω :
  ∀ B, ⦿ B → (∃ F, F: ω ⟹ B) ↔ B ≼ ω.
Proof.
  intros. apply dominated_iff_mapped_onto.
  apply ac1. apply H.
Qed.

(* Check EST6_3.infinite_subset_of_ω_eqnum_ω *)
(* ω的任意无限子集与ω等势 *)
Corollary infinite_subset_of_ω_eqnum_ω :
  ∀ N, N ⊆ ω → infinite N → N ≈ ω.
Proof.
  intros N Hsub Hinf.
  apply dominate_sub in Hsub.
  apply (ω_is_the_least_infinite_set ac3) in Hinf.
  apply Schröeder_Bernstein; auto.
Qed.

(* Check EST6_3.cardLt_aleph0_iff_finite *)
(* 基数是有限基数当且仅当它小于阿列夫零 *)
Corollary cardLt_aleph0_iff_finite :
  ∀𝜅 ⋵ 𝐂𝐃, 𝜅 <𝐜 ℵ₀ ↔ finite 𝜅.
Proof with auto.
  intros 𝜅 Hcd. split.
  - intros [Hleq Hnq]. contra.
    apply Hnq. apply cardLeq_antisym...
    apply aleph0_is_the_least_infinite_card. apply ac3. split...
  - intros [k [Hk Hqn]]. apply CardAx1 in Hqn.
    rewrite <- card_of_card, <- card_of_nat in Hqn... rewrite Hqn.
    apply cardLt_aleph0_if_finite...
Qed.

(* Check EST6_3.dominated_by_finite_is_finite *)
(* 被有限集支配的集合是有限集 *)
Corollary dominated_by_finite_is_finite :
  ∀ A B, A ≼ B → finite B → finite A.
Proof with auto.
  intros * Hdm Hfin.
  rewrite set_finite_iff_card_finite.
  apply cardLt_aleph0_iff_finite...
  eapply cardLeq_lt_tran. apply cardLeq_iff. apply Hdm.
  apply cardLt_aleph0_iff_finite...
  rewrite <- set_finite_iff_card_finite...
Qed.

(* Check EST6_1.subset_of_finite_is_finite *)
(* 有限集的子集是有限集 *)
Corollary subset_of_finite_is_finite :
  ∀ A B, A ⊆ B → finite B → finite A.
Proof.
  intros * Hsub Hfin.
  eapply dominated_by_finite_is_finite.
  apply dominate_sub. apply Hsub. apply Hfin.
Qed.

End AlternativeProofWithAC.

(* 戴德金无穷：与自身的真子集等势的集合 *)
Definition dedekind_infinite := λ A, ∃ B, B ⊂ A ∧ A ≈ B.

(* ==需要选择公理== *)
(* 集合是无限集当且仅当它与自身的真子集等势 *)
Theorem infinite_iff_eqnum_proper_subset : AC_III → ∀ A,
  dedekind_infinite A ↔ infinite A.
Proof with neauto; try congruence.
  intros AC3. split. {
    intros [B [H1 H2]].
    eapply infinite_if_eqnum_proper_sub...
  }
  intros Hinf.
  apply (ω_is_the_least_infinite_set AC3) in Hinf as [f Hf].
  apply injection_is_func in Hf as [Hf Hif]...
  assert (Hf' := Hf). destruct Hf' as [Hff [Hdf Hrf]].
  assert (Hf': f⁻¹: ran f ⇒ ω). {
    split. apply inv_func_iff_sr. destruct Hif...
    split. apply inv_dom. rewrite inv_ran...
  }
  assert (Hif': injective f⁻¹) by (apply inv_injective; auto).
  set (Func A (A - ⎨f[0]⎬) (λ x, match (ixm (x ∈ ran f)) with
    | inl _ => f[f⁻¹[x]⁺]
    | inr _ => x
  end)) as g.
  exists (A - ⎨f[0]⎬). split. {
    split... intros Heq.
    assert (Hf0: f[0] ∈ A)by (eapply ap_ran; neauto).
    rewrite <- Heq in Hf0. apply SepE in Hf0 as [_ H]. apply H...
  }
  exists g. apply meta_bijection.
  - intros x Hx. destruct (ixm (x ∈ ran f)).
    + apply SepI.
      * eapply ap_ran... apply ω_inductive. eapply ap_ran...
      * intros Hap. apply SingE in Hap.
        apply (suc_neq_0 (f⁻¹[x])). apply (injectiveE f)...
        rewrite Hdf. apply ω_inductive. eapply ap_ran... rewrite Hdf...
    + apply SepI... intros Heqx. apply SingE in Heqx. apply n.
      rewrite Heqx. eapply ranI. apply func_correct... rewrite Hdf...
  - intros x1 Hx1 x2 Hx2 Heq.
    assert (Hap: ∀x ∈ ran f, f⁻¹[x]⁺ ∈ dom f). {
      intros x Hx. rewrite Hdf. apply ω_inductive. eapply ap_ran...
    }
    destruct (ixm (x1 ∈ ran f)); destruct (ixm (x2 ∈ ran f))...
    + apply injectiveE in Heq; [|auto|apply Hap..]...
      apply suc_injective in Heq. apply (injectiveE f⁻¹)...
      rewrite inv_dom... rewrite inv_dom...
      eapply ap_ran... eapply ap_ran...
    + exfalso. apply n. rewrite <- Heq.
      eapply ranI. apply func_correct...
    + exfalso. apply n. rewrite Heq.
      eapply ranI. apply func_correct...
  - intros y Hy. apply SepE in Hy as [Hy Hy'].
    destruct (classic (y ∈ ran f)); revgoals. {
      exists y. split... destruct (ixm (y ∈ ran f))...
    }
    set (f⁻¹[y]) as n. ω_destruct n; subst n; [| |eapply ap_ran]...
    + exfalso. assert (Heqy: y = f[0]). {
        rewrite zero, <- H0, inv_ran_reduction...
      }
      apply Hy'. rewrite Heqy...
    + exists (f[n']). split. eapply ap_ran...
      destruct (ixm (f[n'] ∈ ran f)).
      * rewrite inv_dom_reduction... rewrite <- Hn'eq.
        rewrite inv_ran_reduction...
      * exfalso. apply n. eapply ranI. apply func_correct...
Qed.

(* 基数的无限累加和 *)
Definition CardInfSum : set → (set → set) → set := λ I ℱ,
  |⋃{ℱ i × ⎨i⎬ | i ∊ I}|.
Notation "∑" := (CardInfSum) : Card_scope.
Notation "∑ᵢ" := (CardInfSum ω) : Card_scope.

(* 基数的无限累乘积 *)
Definition CardInfProd : set → (set → set) → set := λ I ℱ,
  |InfCProd I ℱ|.
Notation "∏" := (CardInfProd) : Card_scope.
Notation "∏ᵢ" := (CardInfProd ω) : Card_scope.

(* 函数不交化：给定任意函数和单集，可以构造一个新的函数，使得
  (1) 新函数的定义域是原函数的定义域与给定单集的笛卡尔积 且
  (2) 新函数的值域是原函数的值域与给定单集的笛卡尔积 *)
Definition FuncDisjointify := λ i F,
  Func (dom F × ⎨i⎬) (ran F × ⎨i⎬) (λ x, <F[π1 x], i>).

Lemma bijection_disjointify : ∀ F i, injective F →
  (FuncDisjointify i F): dom F × ⎨i⎬ ⟺ ran F × ⎨i⎬.
Proof with eauto; try congruence.
  intros. apply meta_bijection.
  - intros x Hx. apply CProdI... eapply ap_ran.
    split. destruct H... split... apply CProdE0 in Hx as [H1 _]...
  - intros p1 Hp1 p2 Hp2 Heq.
    apply CProdE1 in Hp1 as [a [Ha [b [Hb H1]]]].
    apply CProdE1 in Hp2 as [c [Hc [d [Hd H2]]]].
    apply SingE in Hb. apply SingE in Hd. subst. zfc_simple.
    apply op_iff in Heq as [Heq _]. apply op_iff.
    split... eapply injectiveE...
  - intros y Hy. destruct H as [Hf _].
    apply CProdE1 in Hy as [a [Ha [b [Hb Hy]]]].
    apply ranE in Ha as [x Hp].
    apply domI in Hp as Hx. apply func_ap in Hp as Hap...
    exists <x, b>. split. apply CProdI... subst y. zfc_simple.
    apply op_iff. apply SingE in Hb. split...
Qed.

(* 如果不交化后的函数相等那么原函数相等 *)
Lemma funcDisjointify_injective : ∀ i f g,
  is_function f → is_function g →
  FuncDisjointify i f = FuncDisjointify i g → f = g.
Proof with eauto.
  cut (∀ i f g, is_function f → is_function g →
      FuncDisjointify i f = FuncDisjointify i g → f ⊆ g). {
    intros H * Hf Hg Heq. apply sub_antisym; eapply H...
  }
  intros * Hf Hg Heq p Hpf.
  apply func_pair in Hpf as Heqp... rewrite Heqp in Hpf.
  apply domI in Hpf as Hdf. apply ranI in Hpf as Hrf.
  assert (<<π1 p, i>, <π2 p, i>> ∈ FuncDisjointify i f). {
    apply SepI. apply CProdI; apply CProdI... zfc_simple.
    apply op_iff. split... symmetry. apply func_ap...
  }
  rewrite Heq in H. apply SepE in H as [Hpg Hap].
  apply CProdE2 in Hpg as [Hdg Hrg].
  apply CProdE2 in Hdg as [Hdg _].
  apply CProdE2 in Hrg as [Hrg _]. zfc_simple.
  apply op_iff in Hap as [Hap _]. symmetry in Hap.
  rewrite Heqp. apply func_point...
Qed.

(* ==需要选择公理== *)
(* 基数的无限累加和良定义 *)
Theorem cardInfSum_well_defined : AC_III' → ∀ I A B,
  (∀i ∈ I, |A i| = |B i|) → ∑ I A = ∑ I B.
Proof with eauto; try congruence.
  intros AC3' * Heqcd. unfold AC_III' in AC3'.
  set (λ i, {f ∊ A i ⟶ B i | f: A i ⟺ B i}) as F_.
  set (λ i, {FuncDisjointify i f | f ∊ F_ i}) as F'_.
  set {F'_ i | i ∊ I} as ℱ.
  specialize AC3' with ℱ as [g [Hfg [Hdg Hrg]]]. {
    intros x Hx. apply ReplAx in Hx as [i [Hi HFi]]. subst x.
    apply Heqcd in Hi. apply CardAx1 in Hi as [f Hf].
    exists (FuncDisjointify i f). apply ReplAx.
    exists f. split... apply SepI... apply arrowI.
    apply bijection_is_func...
  }
  set {g[F] | F ∊ ℱ} as G.
  assert (HpUG: ∀p ∈ ⋃G, ∃i ∈ I, p ∈ g[F'_ i]). {
    intros p Hp. apply UnionAx in Hp as [f [Hf Hp]].
    apply ReplAx in Hf as [F [HF Heqf]].
    apply ReplAx in HF as [i [Hi HeqF]].
    subst F f. exists i. split...
  }
  assert (HgF: ∀i ∈ I, ∃ f, f: A i ⟺ B i ∧ g[F'_ i] = FuncDisjointify i f). {
    intros i Hi.
    assert (HFi: F'_ i ∈ ℱ). { apply ReplAx. exists i. split... }
    apply Hrg in HFi. apply ReplAx in HFi as [f [Hf Heq]].
    apply SepE in Hf as [_ Hf]. exists f. split...
  }
  apply CardAx1. exists (⋃ G). split; split.
  - repeat split.
    + intros p Hp. apply HpUG in Hp as [i [Hi Hp]].
      apply HgF in Hi as [f [Hf Heq]]. rewrite Heq in Hp.
      apply SepE in Hp as [Hp _]. apply cprod_is_pairs in Hp...
    + intros x H. rewrite <- unique_existence.
      split. apply domE in H...
      intros y1 y2 H1 H2.
      apply HpUG in H1 as [i1 [Hi1 Hp1]].
      apply HpUG in H2 as [i2 [Hi2 Hp2]].
      apply HgF in Hi1 as [f1 [Hf1 Heq1]]. rewrite Heq1 in Hp1.
      apply HgF in Hi2 as [f2 [Hf2 Heq2]]. rewrite Heq2 in Hp2.
      apply SepE in Hp1 as [Hp1 H1]. apply CProdE2 in Hp1 as [Hx1 _].
      apply SepE in Hp2 as [Hp2 H2]. apply CProdE2 in Hp2 as [Hx2 _].
      zfc_simple. destruct (classic (i1 = i2)). {
        cut (f1 = f2). { intros Heqf. subst. apply op_iff... }
        apply (funcDisjointify_injective i1)...
        destruct Hf1 as [[]]... destruct Hf2 as [[]]...
      }
      exfalso. eapply disjointE; revgoals.
      apply Hx1. apply Hx2. apply cprod_disjointify...
  - intros y Hy. rewrite <- unique_existence.
    split. apply ranE in Hy...
    intros x1 x2 H1 H2.
    apply HpUG in H1 as [i1 [Hi1 Hp1]].
    apply HpUG in H2 as [i2 [Hi2 Hp2]].
    apply HgF in Hi1 as [f1 [Hf1 Heq1]]. rewrite Heq1 in Hp1.
    apply HgF in Hi2 as [f2 [Hf2 Heq2]]. rewrite Heq2 in Hp2.
    apply SepE in Hp1 as [Hp1 H1]. apply CProdE2 in Hp1 as [Hx1 Hy1].
    apply SepE in Hp2 as [Hp2 H2]. apply CProdE2 in Hp2 as [Hx2 Hy2].
    apply CProdE1 in Hx1 as [a [Ha [b [Hb Hx1]]]].
    apply CProdE1 in Hx2 as [c [Hc [d [Hd Hx2]]]].
    apply SingE in Hb. apply SingE in Hd. zfc_simple. subst x1 x2.
    zfc_simple. destruct (classic (i1 = i2)). {
      cut (f1 = f2). {
        intros Heqf. subst. apply op_iff in H2 as [Hap Hi].
        apply op_iff. split... eapply injectiveE... destruct Hf2...
      }
      apply (funcDisjointify_injective i1)...
      destruct Hf1 as [[]]... destruct Hf2 as [[]]...
    }
    exfalso. eapply disjointE; revgoals.
    apply Hy1. apply Hy2. apply cprod_disjointify...
  - ext Hx.
    + apply domE in Hx as [y Hp].
      apply HpUG in Hp as [i [Hi Hp]].
      apply UnionAx. exists (A i × ⎨i⎬). split...
      apply ReplAx. exists i. split...
      apply HgF in Hi as [f [Hf Heq]]. rewrite Heq in Hp.
      apply SepE in Hp as [Hp _]. apply CProdE2 in Hp as [Hx _].
      destruct Hf as [_ [Hdf _]]...
    + apply UnionAx in Hx as [X [HX Hx]].
      apply ReplAx in HX as [i [Hi Heq]]. subst X.
      apply CProdE1 in Hx as [a [Ha [b [Hb Heq]]]].
      apply SingE in Hb. subst.
      cut (<<a, i>, g[F'_ i][<a, i>]> ∈ ⋃G). { eapply domI... }
      apply UnionAx. exists (g[F'_ i]). split.
      apply ReplAx. exists (F'_ i). split...
      apply ReplAx. exists i. split...
      apply HgF in Hi as [f [Hf Heq]]. rewrite Heq.
      destruct Hf as [Hif [Hdf _]].
      pose proof (bijection_disjointify f i) as [[Hfd _] [Hdd _]]...
      apply func_correct... rewrite Hdd. apply CProdI...
  - ext y Hy.
    + apply ranE in Hy as [x Hp].
      apply HpUG in Hp as [i [Hi Hp]].
      apply UnionAx. exists (B i × ⎨i⎬). split...
      apply ReplAx. exists i. split...
      apply HgF in Hi as [f [Hf Heq]]. rewrite Heq in Hp.
      apply SepE in Hp as [Hp _]. apply CProdE2 in Hp as [_ Hy].
      destruct Hf as [_ [_ Hrf]]...
    + apply UnionAx in Hy as [Y [HY Hy]].
      apply ReplAx in HY as [i [Hi Heq]]. subst Y.
      apply CProdE1 in Hy as [a [Ha [b [Hb Heq]]]].
      apply SingE in Hb. subst.
      cut (<g[F'_ i]⁻¹[<a, i>], <a, i>> ∈ ⋃G). { eapply ranI... }
      apply UnionAx. exists (g[F'_ i]). split.
      apply ReplAx. exists (F'_ i). split...
      apply ReplAx. exists i. split...
      apply HgF in Hi as [f [Hf Heq]]. rewrite Heq.
      destruct Hf as [Hif [_ Hrf]].
      pose proof (bijection_disjointify f i) as [[Hfd Hsd] [_ Hrd]]...
      rewrite inv_op. apply func_correct. apply inv_func_iff_sr...
      rewrite inv_dom. rewrite Hrd. apply CProdI...
Qed.

(* ==需要选择公理== *)
(* 基数的无限累乘积良定义 *)
Theorem cardInfProd_well_defined : AC_III' → ∀ I A B,
  (∀i ∈ I, |A i| = |B i|) → ∏ I A = ∏ I B.
Proof with eauto; try congruence.
  intros AC3' * Heqcd. unfold AC_III' in AC3'.
  set (λ i, {f ∊ A i ⟶ B i | f: A i ⟺ B i}) as F_.
  set {F_ i | i ∊ I} as ℱ.
  specialize AC3' with ℱ as [g [Hfg [Hdg Hrg]]]. {
    intros x Hx. apply ReplAx in Hx as [i [Hi HFi]]. subst x.
    apply Heqcd in Hi. apply CardAx1 in Hi as [f Hf].
    exists f. apply SepI... apply arrowI. apply bijection_is_func...
  }
  set (⋃{B i | i ∊ I}) as ℬ.
  set (⋃{A i | i ∊ I}) as 𝒜.
  set (λ x, Func I ℬ (λ i, g[F_ i][x[i]])) as G.
  set (λ y, Func I 𝒜 (λ i, g[F_ i]⁻¹[y[i]])) as G'.
  assert (HFi: ∀i ∈ I, F_ i ∈ ℱ). {
    intros i Hi. apply ReplAx. exists i. split...
  }
  assert (HgF: ∀i ∈ I, g[F_ i]: A i ⟺ B i). {
    intros i Hi. apply HFi in Hi.
    apply Hrg in Hi. apply SepE in Hi as [_ HgF]...
  }
  assert (HgFx: ∀i ∈ I, ∀x ∈ InfCProd I A, g[F_ i][x[i]] ∈ B i). {
    intros i Hi x Hx. eapply ap_ran.
    apply bijection_is_func... eapply InfCProdE...
  }
  assert (HgFy: ∀i ∈ I, ∀y ∈ InfCProd I B, g[F_ i]⁻¹[y[i]] ∈ A i). {
    intros i Hi x Hx. eapply ap_ran. apply bijection_is_func...
    apply inv_bijection. apply HgF... eapply InfCProdE...
  }
  assert (HBi: ∀i ∈ I, B i ⊆ ℬ). {
    intros i Hi b Hb. apply UnionAx. exists (B i). split...
    apply ReplAx. exists i. split...
  }
  assert (HgFx': ∀i ∈ I, ∀x ∈ InfCProd I A, g[F_ i][x[i]] ∈ ℬ). {
    intros i Hi x Hx. eapply HBi...
  }
  assert (HG: ∀x ∈ InfCProd I A, G x: I ⇒ ℬ). {
    intros x Hx. apply meta_function. intros i Hi. eapply HBi...
  }
  assert (HAi: ∀i ∈ I, A i ⊆ 𝒜). {
    intros i Hi a Ha. apply UnionAx. exists (A i). split...
    apply ReplAx. exists i. split...
  }
  assert (HgFy': ∀i ∈ I, ∀y ∈ InfCProd I B, g[F_ i]⁻¹[y[i]] ∈ 𝒜). {
    intros i Hi x Hx. eapply HAi...
  }
  assert (HG': ∀y ∈ InfCProd I B, G' y: I ⇒ 𝒜). {
    intros y Hy. apply meta_function. intros i Hi. eapply HAi...
  }
  set (Func (InfCProd I A) (InfCProd I B) G) as h.
  apply CardAx1. exists h. apply meta_bijection.
  - intros x Hx. apply SepI.
    + apply arrowI. apply HG...
    + intros i Hi. unfold G. rewrite meta_func_ap...
  - intros x1 Hx1 x2 Hx2 Heq.
    assert (∀i ∈ I, g[F_ i][x1[i]] = g[F_ i][x2[i]]). {
      intros i Hi. eapply func_sv. apply HG... rewrite <- Heq.
      - apply SepI. apply CProdI... zfc_simple.
      - apply SepI. apply CProdI... zfc_simple.
    }
    apply InfCProdE in Hx1 as [Hx1 Hxi1].
    apply InfCProdE in Hx2 as [Hx2 Hxi2].
    destruct Hx1 as [Hf1 [Hd1 Hr1]].
    destruct Hx2 as [Hf2 [Hd2 Hr2]].
    apply func_ext_intro... intros i Hi. rewrite Hd1 in Hi.
    pose proof (HgF _ Hi) as [Hinj [Hd _]].
    eapply injectiveE...
    + rewrite Hd. apply Hxi1...
    + rewrite Hd. apply Hxi2...
  - intros y Hy. assert (Hx: G' y ∈ InfCProd I A). {
      apply InfCProdI. apply HG'...
      intros i Hi. unfold G'. rewrite meta_func_ap...
    }
    assert (Heqd: dom (G (G' y)) = I). {
      ext i Hi.
      - apply domE in Hi as [f Hp].
        apply SepE in Hp as [Hp _].
        apply CProdE2 in Hp as [Hi _]...
      - eapply domI. apply SepI. apply CProdI... zfc_simple.
    }
    exists (G' y). split... apply func_ext_intro...
    + apply meta_function. intros i Hi. apply HgFx'...
    + apply InfCProdE in Hy as [[]]...
    + apply InfCProdE in Hy as [[_ [Hd _]]]...
    + intros i Hi. rewrite Heqd in Hi. unfold G, G'.
      pose proof (HgF _ Hi) as [Hinj [Hd Hr]].
      rewrite meta_func_ap... rewrite meta_func_ap...
      rewrite inv_ran_reduction...
      rewrite Hr. eapply InfCProdE...
Qed.

(* ==需要选择公理== *)
(* 基数的无限累加保持序关系 *)
Theorem cardInfSum_preserve_leq : AC_III' → ∀ I A B,
  (∀i ∈ I, |A i| ≤ |B i|) → ∑ I A ≤ ∑ I B.
Proof with eauto; try congruence.
  intros AC3' * Heqcd. unfold AC_III' in AC3'.
  set (λ i, {f ∊ A i ⟶ B i | f: A i ⇔ B i}) as F_.
  set (λ i, {FuncDisjointify i f | f ∊ F_ i}) as F'_.
  set {F'_ i | i ∊ I} as ℱ.
  specialize AC3' with ℱ as [g [Hfg [Hdg Hrg]]]. {
    intros x Hx. apply ReplAx in Hx as [i [Hi HFi]]. subst x.
    apply Heqcd in Hi. apply cardLeq_iff in Hi as [f Hf].
    exists (FuncDisjointify i f). apply ReplAx.
    exists f. split... apply SepI... apply arrowI.
    apply injection_is_func...
  }
  set {g[F] | F ∊ ℱ} as G.
  assert (HpUG: ∀p ∈ ⋃G, ∃i ∈ I, p ∈ g[F'_ i]). {
    intros p Hp. apply UnionAx in Hp as [f [Hf Hp]].
    apply ReplAx in Hf as [F [HF Heqf]].
    apply ReplAx in HF as [i [Hi HeqF]].
    subst F f. exists i. split...
  }
  assert (HgF: ∀i ∈ I, ∃ f, f: A i ⇔ B i ∧ g[F'_ i] = FuncDisjointify i f). {
    intros i Hi.
    assert (HFi: F'_ i ∈ ℱ). { apply ReplAx. exists i. split... }
    apply Hrg in HFi. apply ReplAx in HFi as [f [Hf Heq]].
    apply SepE in Hf as [_ Hf]. exists f. split...
  }
  apply cardLeq_iff. exists (⋃ G). split; split.
  - repeat split.
    + intros p Hp. apply HpUG in Hp as [i [Hi Hp]].
      apply HgF in Hi as [f [Hf Heq]]. rewrite Heq in Hp.
      apply SepE in Hp as [Hp _]. apply cprod_is_pairs in Hp...
    + intros x H. rewrite <- unique_existence.
      split. apply domE in H...
      intros y1 y2 H1 H2.
      apply HpUG in H1 as [i1 [Hi1 Hp1]].
      apply HpUG in H2 as [i2 [Hi2 Hp2]].
      apply HgF in Hi1 as [f1 [Hf1 Heq1]]. rewrite Heq1 in Hp1.
      apply HgF in Hi2 as [f2 [Hf2 Heq2]]. rewrite Heq2 in Hp2.
      apply SepE in Hp1 as [Hp1 H1]. apply CProdE2 in Hp1 as [Hx1 _].
      apply SepE in Hp2 as [Hp2 H2]. apply CProdE2 in Hp2 as [Hx2 _].
      zfc_simple. destruct (classic (i1 = i2)). {
        cut (f1 = f2). { intros Heqf. subst. apply op_iff... }
        apply (funcDisjointify_injective i1)...
        destruct Hf1 as [[]]... destruct Hf2 as [[]]...
      }
      exfalso. eapply disjointE; revgoals.
      apply Hx1. apply Hx2. apply cprod_disjointify...
  - intros y Hy. rewrite <- unique_existence.
    split. apply ranE in Hy...
    intros x1 x2 H1 H2.
    apply HpUG in H1 as [i1 [Hi1 Hp1]].
    apply HpUG in H2 as [i2 [Hi2 Hp2]].
    apply HgF in Hi1 as [f1 [Hf1 Heq1]]. rewrite Heq1 in Hp1.
    apply HgF in Hi2 as [f2 [Hf2 Heq2]]. rewrite Heq2 in Hp2.
    apply SepE in Hp1 as [Hp1 H1]. apply CProdE2 in Hp1 as [Hx1 Hy1].
    apply SepE in Hp2 as [Hp2 H2]. apply CProdE2 in Hp2 as [Hx2 Hy2].
    apply CProdE1 in Hx1 as [a [Ha [b [Hb Hx1]]]].
    apply CProdE1 in Hx2 as [c [Hc [d [Hd Hx2]]]].
    apply SingE in Hb. apply SingE in Hd. zfc_simple. subst x1 x2.
    zfc_simple. destruct (classic (i1 = i2)). {
      cut (f1 = f2). {
        intros Heqf. subst. apply op_iff in H2 as [Hap Hi].
        apply op_iff. split... eapply injectiveE... destruct Hf2...
      }
      apply (funcDisjointify_injective i1)...
      destruct Hf1 as [[]]... destruct Hf2 as [[]]...
    }
    exfalso. eapply disjointE; revgoals.
    apply Hy1. apply Hy2. apply cprod_disjointify...
  - ext Hx.
    + apply domE in Hx as [y Hp].
      apply HpUG in Hp as [i [Hi Hp]].
      apply UnionAx. exists (A i × ⎨i⎬). split...
      apply ReplAx. exists i. split...
      apply HgF in Hi as [f [Hf Heq]]. rewrite Heq in Hp.
      apply SepE in Hp as [Hp _]. apply CProdE2 in Hp as [Hx _].
      destruct Hf as [_ [Hdf _]]...
    + apply UnionAx in Hx as [X [HX Hx]].
      apply ReplAx in HX as [i [Hi Heq]]. subst X.
      apply CProdE1 in Hx as [a [Ha [b [Hb Heq]]]].
      apply SingE in Hb. subst.
      cut (<<a, i>, g[F'_ i][<a, i>]> ∈ ⋃G). { eapply domI... }
      apply UnionAx. exists (g[F'_ i]). split.
      apply ReplAx. exists (F'_ i). split...
      apply ReplAx. exists i. split...
      apply HgF in Hi as [f [Hf Heq]]. rewrite Heq.
      destruct Hf as [Hif [Hdf _]].
      pose proof (bijection_disjointify f i) as [[Hfd _] [Hdd _]]...
      apply func_correct... rewrite Hdd. apply CProdI...
  - intros y Hy.
    apply ranE in Hy as [x Hp].
    apply HpUG in Hp as [i [Hi Hp]].
    apply UnionAx. exists (B i × ⎨i⎬). split...
    apply ReplAx. exists i. split...
    apply HgF in Hi as [f [Hf Heq]]. rewrite Heq in Hp.
    apply SepE in Hp as [Hp _].
    apply CProdE2 in Hp as [_ Hy].
    apply CProdE1 in Hy as [a [Ha [b [Hb Hy]]]]. subst y.
    apply CProdI... destruct Hf as [_ [_ Hrf]]. apply Hrf...
Qed.

(* ==需要选择公理== *)
(* 基数的无限累乘保持序关系 *)
Theorem cardInfProd_preserve_leq : AC_III' → ∀ I A B,
  (∀i ∈ I, |A i| ≤ |B i|) → ∏ I A ≤ ∏ I B.
Proof with eauto; try congruence.
  intros AC3' * Heqcd. unfold AC_III' in AC3'.
  set (λ i, {f ∊ A i ⟶ B i | f: A i ⇔ B i}) as F_.
  set {F_ i | i ∊ I} as ℱ.
  specialize AC3' with ℱ as [g [Hfg [Hdg Hrg]]]. {
    intros x Hx. apply ReplAx in Hx as [i [Hi HFi]]. subst x.
    apply Heqcd in Hi. apply cardLeq_iff in Hi as [f Hf].
    exists f. apply SepI... apply arrowI. apply injection_is_func...
  }
  set (⋃{B i | i ∊ I}) as ℬ.
  set (⋃{A i | i ∊ I}) as 𝒜.
  set (λ x, Func I ℬ (λ i, g[F_ i][x[i]])) as G.
  set (λ y, Func I 𝒜 (λ i, g[F_ i]⁻¹[y[i]])) as G'.
  assert (HFi: ∀i ∈ I, F_ i ∈ ℱ). {
    intros i Hi. apply ReplAx. exists i. split...
  }
  assert (HgF: ∀i ∈ I, g[F_ i]: A i ⇔ B i). {
    intros i Hi. apply HFi in Hi.
    apply Hrg in Hi. apply SepE in Hi as [_ HgF]...
  }
  assert (HgFx: ∀i ∈ I, ∀x ∈ InfCProd I A, g[F_ i][x[i]] ∈ B i). {
    intros i Hi x Hx. eapply ap_ran.
    apply injection_is_func... eapply InfCProdE...
  }
  assert (HBi: ∀i ∈ I, B i ⊆ ℬ). {
    intros i Hi b Hb. apply UnionAx. exists (B i). split...
    apply ReplAx. exists i. split...
  }
  assert (HgFx': ∀i ∈ I, ∀x ∈ InfCProd I A, g[F_ i][x[i]] ∈ ℬ). {
    intros i Hi x Hx. eapply HBi...
  }
  assert (HG: ∀x ∈ InfCProd I A, G x: I ⇒ ℬ). {
    intros x Hx. apply meta_function. intros i Hi. eapply HBi...
  }
  set (Func (InfCProd I A) (InfCProd I B) G) as h.
  apply cardLeq_iff. exists h. apply meta_injection.
  - intros x Hx. apply SepI.
    + apply arrowI. apply HG...
    + intros i Hi. unfold G. rewrite meta_func_ap...
  - intros x1 Hx1 x2 Hx2 Heq.
    assert (∀i ∈ I, g[F_ i][x1[i]] = g[F_ i][x2[i]]). {
      intros i Hi. eapply func_sv. apply HG... rewrite <- Heq.
      - apply SepI. apply CProdI... zfc_simple.
      - apply SepI. apply CProdI... zfc_simple.
    }
    apply InfCProdE in Hx1 as [Hx1 Hxi1].
    apply InfCProdE in Hx2 as [Hx2 Hxi2].
    destruct Hx1 as [Hf1 [Hd1 Hr1]].
    destruct Hx2 as [Hf2 [Hd2 Hr2]].
    apply func_ext_intro... intros i Hi. rewrite Hd1 in Hi.
    pose proof (HgF _ Hi) as [Hinj [Hd _]].
    eapply injectiveE...
    + rewrite Hd. apply Hxi1...
    + rewrite Hd. apply Hxi2...
Qed.

(* 相同基数的无限累加和等价于基数乘法 *)
Theorem cardInfSum_of_same_card :
  ∀ I, ∀𝜅 ⋵ 𝐂𝐃, ∑ I (λ _, 𝜅) = |I| ⋅ 𝜅.
Proof with auto; try congruence.
  intros I 𝜅 Hcd.
  rewrite (card_of_card 𝜅) at 1...
  rewrite cardMul_comm, cardMul. apply CardAx1.
  replace (⋃ (Repl (λ i, 𝜅 × ⎨i⎬) I)) with (𝜅 × I). easy.
  ext p Hp.
  - apply CProdE1 in Hp as [k [Hk [i [Hi Hp]]]]. subst p.
    apply UnionAx. exists (𝜅 × ⎨i⎬). split...
    apply ReplAx. exists i. split... apply CProdI...
  - apply UnionAx in Hp as [P [HP Hp]].
    apply ReplAx in HP as [i [Hi HP]]. subst P.
    apply CProdE1 in Hp as [k [Hk [j [Hj Hp]]]]. subst p.
    apply SingE in Hj; subst. apply CProdI...
Qed.

(* 不交集的无限累加和 *)
Lemma cardInfSum_of_disjoint : ∀ I ℱ,
  (∀ i j ∈ I, i ≠ j → disjoint (ℱ i) (ℱ j)) →
  ∑ I ℱ = |⋃{ℱ i | i ∊ I}|.
Proof with eauto.
  intros * Hdj. apply CardAx1.
  set (⋃{ℱ i × ⎨i⎬ | i ∊ I}) as X.
  set (⋃{ℱ i | i ∊ I}) as Y.
  set (Func X Y π1) as f.
  exists f. apply meta_bijection.
  - intros x Hx. apply FUnionE in Hx as [i [Hi Hx]].
    apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]].
    subst x. zfc_simple. eapply FUnionI...
  - intros x1 H1 x2 H2 Heq.
    apply FUnionE in H1 as [i [Hi H1]].
    apply FUnionE in H2 as [j [Hj H2]].
    apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]].
    apply CProdE1 in H2 as [c [Hc [d [Hd H2]]]].
    apply SingE in Hb. apply SingE in Hd.
    subst. zfc_simple. apply op_iff. split...
    contra.
    apply Hdj in H... eapply disjointE... congruence.
  - intros y Hy. apply FUnionE in Hy as [i [Hi Hx]].
    exists <y, i>. split; zfc_simple.
    eapply FUnionI... apply CProdI...
Qed.

Fact cardInfSum_0_pow : ∑ᵢ (λ i, 0 ^ i) = 1.
Proof with nauto.
  rewrite (card_of_nat 1)... apply CardAx1.
  set (⋃ᵢ λ i, 0 ^ i × ⎨i⎬) as A.
  set (Func A 1 (λ _, 0)) as f.
  exists f. apply meta_bijection.
  - intros _ _. apply suc_has_0...
  - intros x1 H1 x2 H2 _.
    apply IFUnionE in H1 as [n [Hn H1]].
    apply IFUnionE in H2 as [m [Hm H2]].
    destruct (classic (n = 0)); destruct (classic (m = 0)).
    + subst. rewrite cardExp_0_r in H1, H2.
      apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]].
      apply CProdE1 in H2 as [c [Hc [d [Hd H2]]]].
      rewrite one in Ha, Hc.
      apply SingE in Ha. apply SingE in Hc.
      apply SingE in Hb. apply SingE in Hd. congruence.
    + rewrite cardExp_0_l in H2...
      apply CProdE1 in H2 as [a [Ha _]]. exfalso0.
    + rewrite cardExp_0_l in H1...
      apply CProdE1 in H1 as [a [Ha _]]. exfalso0.
    + rewrite cardExp_0_l in H1...
      apply CProdE1 in H1 as [a [Ha _]]. exfalso0.
  - intros y Hy. rewrite one in Hy. apply SingE in Hy.
    exists <0, 0>. split... apply (IFUnionI _ 0)...
    apply CProdI... rewrite cardExp_0_0... apply suc_has_0...
Qed.
