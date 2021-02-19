(** Based on "Elements of Set Theory" Chapter 6 Part 3 **)
(** Coq coding by choukh, Sep 2020 **)

Require Export ZFC.lib.NaturalFacts.
Require Export ZFC.lib.Dominate.
Require Export ZFC.EX6_1.

(*** EST第六章3：支配关系，施罗德-伯恩斯坦定理，基数的序，阿列夫零 ***)

(* dominate and Schröeder-Bernstein theorem see lib/Dominate *)

(* 基数的序 *)
Definition CardLeq : set → set → Prop := λ 𝜅 𝜆,
  is_card 𝜅 ∧ is_card 𝜆 ∧ 𝜅 ≼ 𝜆.
Notation "𝜅 ≤ 𝜆" := (CardLeq 𝜅 𝜆) (at level 70) : Card_scope.

(* 两个集合的基数有序关系当且仅当这两个集合有支配关系 *)
Lemma cardLeq_iff : ∀ A B, |A| ≤ |B| ↔ A ≼ B.
Proof with eauto; try congruence.
  intros. split.
  - intros [_ [_ Hdm]].
    apply dominate_iff in Hdm as [C [Hsub H1]].
    rewrite <- CardAx0 in H1.
    pose proof (CardAx0 B) as H2. symmetry in H2.
    destruct H1 as [f [Hif [Hdf Hrf]]].
    destruct H2 as [g [Hig [Hdg Hrg]]].
    exists (g ∘ f). split; [|split].
    + apply compo_injective...
    + destruct Hif as [Hff _].
      destruct Hig as [Hfg _]. rewrite compo_dom...
      apply ExtAx. split; intros Hx.
      * apply SepE1 in Hx...
      * apply SepI... rewrite Hdg. apply Hsub.
        eapply ap_ran... split... split...
    + destruct Hif as [Hff _]. rewrite compo_ran...
      intros x Hx. apply SepE1 in Hx...
  - intros [f Hf]. split; [|split]...
    pose proof (CardAx0 A) as Hg.
    symmetry in Hg. destruct Hg as [g Hg].
    pose proof (CardAx0 B) as [h Hh].
    exists (h ∘ f ∘ g). eapply compo_injection.
    apply bijection_is_injection. apply Hg.
    eapply compo_injection. apply Hf.
    apply bijection_is_injection. apply Hh.
Qed.

Lemma cardLeq : ∀ 𝜅 𝜆, 𝜅 ≤ 𝜆 → |𝜅| ≤ |𝜆|.
Proof. intros * [_ [_ H]]. apply cardLeq_iff. apply H. Qed.

(* 基数的序关系良定义 *)
Lemma cardLeq_well_defined : ∀ K₁ K₂ L₁ L₂,
  K₁ ≈ K₂ → L₁ ≈ L₂ → K₁ ≼ L₁ ↔ K₂ ≼ L₂.
Proof with eauto.
  cut (∀ K₁ K₂ L₁ L₂, K₁ ≈ K₂ → L₁ ≈ L₂ → K₁ ≼ L₁ → K₂ ≼ L₂). {
    intros Hstar * Hk Hl. split; intros.
    eapply Hstar... eapply Hstar.
    symmetry... symmetry... apply H.
  }
  intros * Hf [g Hg] [h Hh].
  symmetry in Hf. destruct Hf as [f Hf].
  exists (g ∘ h ∘ f). eapply compo_injection.
  apply bijection_is_injection. apply Hf.
  eapply compo_injection. apply Hh.
  apply bijection_is_injection. apply Hg.
Qed.

(* 基数的小于关系 *)
Definition CardLt : set → set → Prop := λ 𝜅 𝜆, 𝜅 ≤ 𝜆 ∧ 𝜅 ≠ 𝜆.
Notation "𝜅 <𝐜 𝜆" := (CardLt 𝜅 𝜆) (at level 70) : Card_scope.

(* 两个集合的基数有小于关系当且仅当这两个集合有真支配关系 *)
Lemma cardLt_iff : ∀ A B, |A| <𝐜 |B| ↔ A ≺ B.
Proof with auto.
  intros. split.
  - intros [Hleq Hnq]. apply cardLeq_iff in Hleq.
    split... intros Hqn. apply Hnq. apply CardAx1...
  - intros [Hdm Hnq]. split. apply cardLeq_iff...
    intros Heq. apply Hnq. apply CardAx1...
Qed.

Lemma cardLt : ∀ 𝜅 𝜆, 𝜅 <𝐜 𝜆 → |𝜅| <𝐜 |𝜆|.
Proof with auto.
  intros * [[Hk [Hl H]] Hnq].
  apply cardLt_iff. split... intros Hqn. apply Hnq.
  rewrite card_of_card, (card_of_card 𝜅)... apply CardAx1...
Qed.

Lemma cardLeq_iff_lt_or_eq : ∀ 𝜅 𝜆, 𝜅 ≤ 𝜆 ↔ 𝜅 <𝐜 𝜆 ∨
  (is_card 𝜅 ∧ is_card 𝜆 ∧ 𝜅 = 𝜆).
Proof with auto.
  intros. split.
  - intros. destruct (classic (𝜅 = 𝜆)).
    right. destruct H as [Hk [Hl _]]. split... left. split...
  - intros [[]|[Hk [Hl Heq]]]... split... split... subst...
Qed.

(* 如果两个集合有子集关系，那么这两个集合的基数有序关系 *)
Lemma cardLeq_sub : ∀ A B, A ⊆ B → |A| ≤ |B|.
Proof.
  intros. apply cardLeq_iff. apply dominate_sub. apply H.
Qed.

(* 如果两个基数有序关系，那么存在有子集关系的集合，它们分别与这两个基数等势 *)
Lemma cardLeq_sub_exists : ∀ 𝜅 𝜆, 𝜅 ≤ 𝜆 →
  ∃ K L, K ≈ 𝜅 ∧ L ≈ 𝜆 ∧ K ⊆ L.
Proof with auto; try easy.
  intros * [Hk [Hl [f [Hf [Hd Hr]]]]].
  exists (ran f), 𝜆. repeat split...
  rewrite <- Hd. symmetry. exists f. split...
Qed.

(* 如果两个基数有序关系，那么存在有子集关系的集合，它们的基数就是这两个基数 *)
Lemma cardLeq_sub_exists_eq : ∀ 𝜅 𝜆, 𝜅 ≤ 𝜆 →
  ∃ K L, |K| = 𝜅 ∧ |L| = 𝜆 ∧ K ⊆ L.
Proof with auto.
  intros * Hleq. assert (H := Hleq). destruct H as [Hk [Hl _]].
  apply cardLeq_sub_exists in Hleq as [K [L [H1 [H2 H]]]].
  exists K, L. repeat split...
  rewrite card_of_card... apply CardAx1...
  rewrite card_of_card... apply CardAx1...
Qed.

(* 任意基数大于等于零 *)
Fact cardLeq_0 : ∀ 𝜅, is_card 𝜅 → 0 ≤ 𝜅.
Proof.
  intros 𝜅 Hcd. split; [|split]; nauto. apply empty_dominated.
Qed.

(* 非零基数大于等于1 *)
Fact cardLeq_1 : ∀ 𝜅, is_card 𝜅 → 𝜅 ≠ 0 → 1 ≤ 𝜅.
Proof with nauto.
  intros 𝜅 Hcd. split; [|split]...
  apply EmptyNE in H as [k Hk].
  set (Func 1 𝜅 (λ x, k)) as f.
  exists f. apply meta_injective. intros _ _...
  intros x1 H1 x2 H2 _. rewrite one in H1, H2.
  apply SingE in H1. apply SingE in H2. congruence.
Qed.

(* 有限基数的序关系与支配关系等价 *)
Lemma fin_cardLeq_iff_dominate : ∀ m n ∈ ω, m ≤ n ↔ m ≼ n.
Proof with auto.
  intros m Hm n Hn. split; intros.
  - apply cardLeq in H. apply cardLeq_iff in H...
  - apply cardLeq_iff in H.
    rewrite <- card_of_nat, <- card_of_nat in H...
Qed.

(* 有限基数的序关系与自然数序关系等价 *)
Lemma fin_cardLeq_iff_leq : ∀ m n ∈ ω, m ≤ n ↔ m ⋸ n.
Proof with auto.
  intros m Hm n Hn. split; intros.
  - apply fin_cardLeq_iff_dominate in H...
    destruct (classic (m = n))... left.
    apply nat_connected in H0 as []... exfalso.
    apply lt_iff_psub in H0 as []... apply dominate_sub in H0.
    apply H1. apply nat_eqnum_eq... apply Schröeder_Bernstein...
  - apply leq_iff_sub in H... apply dominate_sub in H.
    apply fin_cardLeq_iff_dominate...
Qed.

Lemma fin_cardLt_iff_lt : ∀ m n ∈ ω, m <𝐜 n ↔ m ∈ n.
Proof with eauto.
  intros m Hm n Hn. split; intros.
  - destruct H as [Hleq Hnq]. apply fin_cardLeq_iff_leq in Hleq...
    apply leq_iff_sub in Hleq... apply lt_iff_psub...
  - split. apply fin_cardLeq_iff_leq...
    intros Heq. subst. eapply nat_irrefl...
Qed.

(* 任意基数都小于自身的幂集的基数 *)
Lemma cardLt_power : ∀ 𝜅, is_card 𝜅 → 𝜅 <𝐜 2 ^ 𝜅.
Proof with auto.
  intros. rewrite (card_of_card 𝜅), <- card_of_power...
  apply cardLt_iff. split; [|apply Cantor's].
  set (Func 𝜅 (𝒫 𝜅) (λ x, ⎨x⎬)) as f.
  exists f. apply meta_injective.
  - intros x Hx. apply PowerAx. intros y Hy.
    apply SingE in Hy. subst...
  - intros x1 Hx1 x2 Hx2 Heq. assert (x1 ∈ ⎨x1⎬) by auto.
    rewrite Heq in H0. apply SingE in H0...
Qed.

(* 基数的序关系是自反的 *)
Lemma cardLeq_refl : ∀ 𝜅, is_card 𝜅 → 𝜅 ≤ 𝜅.
Proof with auto.
  intros. rewrite (card_of_card 𝜅)... apply cardLeq_iff...
Qed.

(* 相等的基数满足序关系 *)
Lemma eq_cardLeq : ∀ 𝜅 𝜆, is_card 𝜅 → 𝜅 = 𝜆 → 𝜅 ≤ 𝜆.
Proof.
  intros. subst. apply cardLeq_refl. apply H.
Qed.

(* 基数的序关系是传递的 *)
Lemma cardLeq_tran : ∀ 𝜅 𝜆 𝜇, 𝜅 ≤ 𝜆 → 𝜆 ≤ 𝜇 → 𝜅 ≤ 𝜇.
Proof with eauto.
  intros * [Hk [_ H1]] [_ [Hm H2]].
  repeat split... eapply dominate_tran...
Qed.

Lemma cardLeq_rewrite_l : ∀ 𝜅 𝜆 𝜇, 𝜆 = 𝜅 → 𝜆 ≤ 𝜇 → 𝜅 ≤ 𝜇.
Proof with eauto.
  intros * Heq Hle. eapply cardLeq_tran; revgoals...
  apply eq_cardLeq... destruct Hle as []... congruence.
Qed.

Lemma cardLeq_rewrite_r : ∀ 𝜅 𝜆 𝜇, 𝜇 = 𝜅 → 𝜆 ≤ 𝜇 → 𝜆 ≤ 𝜅.
Proof with eauto.
  intros * Heq Hle. eapply cardLeq_tran; revgoals...
  apply eq_cardLeq... destruct Hle as [_ []]...
Qed.

(* 基数的序关系是反对称的 *)
Lemma cardLeq_antisym : ∀ 𝜅 𝜆, 𝜅 ≤ 𝜆 → 𝜆 ≤ 𝜅 → 𝜅 = 𝜆.
Proof with auto.
  intros * [Hk [Hl H1]] [_ [_ H2]].
  rewrite (card_of_card 𝜅), (card_of_card 𝜆)...
  apply CardAx1. apply Schröeder_Bernstein...
Qed.

Corollary cardLeq_to_not_gt : ∀ 𝜅 𝜆,
  𝜅 ≤ 𝜆 → ¬ 𝜆 <𝐜 𝜅.
Proof.
  intros 𝜅 𝜆 Hleq [Hgeq Hnq].
  apply Hnq. apply cardLeq_antisym; auto.
Qed.

Corollary cardLeq_lt_tran : ∀ 𝜅 𝜆 𝜇, 𝜅 ≤ 𝜆 → 𝜆 <𝐜 𝜇 → 𝜅 <𝐜 𝜇.
Proof with eauto.
  intros * H1 [H2 Hnq]. split. eapply cardLeq_tran...
  intros Heq. apply Hnq. rewrite Heq in H1. eapply cardLeq_antisym...
Qed.

Corollary cardLt_leq_tran : ∀ 𝜅 𝜆 𝜇, 𝜅 <𝐜 𝜆 → 𝜆 ≤ 𝜇 → 𝜅 <𝐜 𝜇.
Proof with eauto.
  intros * [H1 Hnq] H2. split. eapply cardLeq_tran...
  intros Heq. apply Hnq. rewrite <- Heq in H2. eapply cardLeq_antisym...
Qed.

(* 基数加法保持等势关系 *)
Lemma cardAdd_preserve_eqnum : ∀ 𝜅 𝜆 𝜇, 𝜅 ≈ 𝜆 → 𝜅 + 𝜇 ≈ 𝜆 + 𝜇.
Proof with auto.
  intros. unfold CardAdd. rewrite <- CardAx0, <- CardAx0.
  apply cardAdd_well_defined.
  apply cardMul_well_defined... now apply cardMul_well_defined...
  apply disjointify_0_1. apply disjointify_0_1.
Qed.

(* 基数加法保持序关系 *)
Theorem cardAdd_preserve_leq : ∀ 𝜅 𝜆 𝜇, 𝜅 ≤ 𝜆 → 𝜅 + 𝜇 ≤ 𝜆 + 𝜇.
Proof with auto.
  intros * Hleq.
  apply cardLeq_sub_exists in Hleq as [K [L [Hk [Hl H]]]].
  repeat split... eapply cardLeq_well_defined.
  symmetry. apply cardAdd_preserve_eqnum. apply Hk.
  symmetry. apply cardAdd_preserve_eqnum. apply Hl.
  apply cardLeq_sub. apply sub_mono_bunion. apply sub_mono_cprod...
Qed.

(* 基数乘法保持序关系 *)
Theorem cardMul_preserve_leq : ∀ 𝜅 𝜆 𝜇, 𝜅 ≤ 𝜆 → 𝜅 ⋅ 𝜇 ≤ 𝜆 ⋅ 𝜇.
Proof with auto.
  intros * Hleq.
  apply cardLeq_sub_exists in Hleq as [K [L [H1 [H2 H]]]].
  apply cardLeq_iff. eapply cardLeq_well_defined.
  apply cardMul_well_defined. symmetry. apply H1. reflexivity.
  apply cardMul_well_defined. symmetry. apply H2. reflexivity.
  apply dominate_sub. apply sub_mono_cprod...
Qed.

Corollary cardAdd_preserve_leq' : ∀ 𝜅 𝜆 𝜇, 𝜅 ≤ 𝜆 → 𝜇 + 𝜅 ≤ 𝜇 + 𝜆.
Proof.
  intros * Hleq. rewrite cardAdd_comm, (cardAdd_comm 𝜇).
  apply cardAdd_preserve_leq. apply Hleq.
Qed.

Corollary cardMul_preserve_leq' : ∀ 𝜅 𝜆 𝜇, 𝜅 ≤ 𝜆 → 𝜇 ⋅ 𝜅 ≤ 𝜇 ⋅ 𝜆.
Proof.
  intros * Hleq. rewrite cardMul_comm, (cardMul_comm 𝜇).
  apply cardMul_preserve_leq. apply Hleq.
Qed.

Corollary cardAdd_enlarge : ∀ 𝜅 𝜆, is_card 𝜅 → is_card 𝜆 → 𝜅 ≤ 𝜅 + 𝜆.
Proof with auto.
  intros * Hk Hl. rewrite <- cardAdd_ident at 1...
  apply cardAdd_preserve_leq'. apply cardLeq_0...
Qed.

Corollary cardMul_enlarge : ∀ 𝜅 𝜆, is_card 𝜅 → is_card 𝜆 → 𝜆 ≠ 0 → 𝜅 ≤ 𝜅 ⋅ 𝜆.
Proof with auto.
  intros * Hk Hl H0. rewrite <- cardMul_ident at 1...
  apply cardMul_preserve_leq'. apply cardLeq_1...
Qed.

Lemma sub_mono_arrow : ∀ A B C, A ⊆ B → C ⟶ A ⊆ C ⟶ B.
Proof with auto.
  intros * Hsub f Hf.
  apply arrow_iff in Hf as [Hf [Hd Hr]].
  apply arrow_iff. split; [|split]...
  intros x Hx. apply Hsub. apply Hr...
Qed.

(* 基数乘方保持底数的序关系 *)
Theorem cardExp_preserve_base_leq : ∀ 𝜅 𝜆 𝜇, 𝜅 ≤ 𝜆 → 𝜅 ^ 𝜇 ≤ 𝜆 ^ 𝜇.
Proof with auto.
  intros * Hleq.
  apply cardLeq_sub_exists in Hleq as [K [L [H1 [H2 H]]]].
  apply cardLeq_iff. eapply cardLeq_well_defined.
  apply cardExp_well_defined. symmetry. apply H1. reflexivity.
  apply cardExp_well_defined. symmetry. apply H2. reflexivity.
  apply dominate_sub. apply sub_mono_arrow...
Qed.

(* 基数乘方保持指数的序关系 *)
Theorem cardExp_preserve_exponent_leq : ∀ 𝜅 𝜆 𝜇, (𝜅 ≠ ∅ ∨ 𝜇 ≠ ∅) →
  𝜅 ≤ 𝜆 → 𝜇 ^ 𝜅 ≤ 𝜇 ^ 𝜆.
Proof with neauto.
  intros * Hnq Hleq.
  destruct (classic (𝜇 = ∅)) as [|Hi]. destruct Hnq; [|exfalso]... {
    subst. rewrite cardExp_0_l... rewrite card_of_nat...
    apply cardLeq_sub. apply empty_sub_all.
  }
  apply EmptyNE in Hi as [m Hm].
  apply cardLeq_sub_exists in Hleq as [K [L [Hk [Hl Hsub]]]].
  apply cardLeq_iff. eapply cardLeq_well_defined.
  apply cardExp_well_defined. reflexivity. symmetry. apply Hk.
  apply cardExp_well_defined. reflexivity. symmetry. apply Hl.
  set (Func (K ⟶ 𝜇) (L ⟶ 𝜇) (λ f, f ∪ ((L - K) × ⎨m⎬))) as G.
  exists G. apply meta_injective.
  - intros f Hf.
    apply SepE in Hf as [Hf [Hff [Hdf Hrf]]].
    apply SepI. {
      apply PowerAx. intros x Hx. apply BUnionE in Hx as [].
      - apply PowerAx in Hf. apply Hf in H. eapply sub_mono_cprod...
      - apply CProdE1 in H as [a [Ha [b [Hb H]]]]. subst x.
        apply CProdI. apply SepE1 in Ha...
        apply SingE in Hb. subst b...
    }
    split; [|split].
    + apply bunion_is_func... {
        repeat split.
        - apply cprod_is_rel.
        - apply domE in H...
        - intros y1 y2 Hp1 Hp2.
          apply CProdE1 in Hp1 as [a [Ha [b [Hb H1]]]].
          apply CProdE1 in Hp2 as [c [Hc [d [Hd H2]]]].
          apply op_iff in H1 as []; subst x y1.
          apply op_iff in H2 as []; subst y2.
          apply SingE in Hb. apply SingE in Hd. congruence.
      }
      apply EmptyI. intros x Hx.
      apply BInterE in Hx as [H1 H2].
      apply domE in H2 as [y H2].
      apply CProdE1 in H2 as [a [Ha [b [_ H2]]]].
      apply op_iff in H2 as [H _]; subst x.
      apply SepE in Ha as [_ H]. congruence.
    + apply ExtAx. split; intros Hx. {
        apply domE in Hx as [y Hp]. apply BUnionE in Hp as [].
        - apply Hsub. rewrite <- Hdf. eapply domI...
        - apply CProdE1 in H as [a [Ha [b [_ H]]]].
          apply op_iff in H as [H _]; subst x.
          apply SepE1 in Ha...
      } {
        destruct (classic (x ∈ K)).
        - rewrite <- Hdf in H. apply domE in H as [y Hp].
          eapply domI. apply BUnionI1...
        - eapply domI. apply BUnionI2...
          apply CProdI... apply SepI...
      }
    + intros y Hy. apply ranE in Hy as [x Hp].
      apply BUnionE in Hp as [].
      * apply ranI in H. apply Hrf...
      * apply CProdE2 in H as [_ Hy].
        apply SingE in Hy. subst y...
  - intros f1 Hf1 f2 Hf2 Heq. eapply ex2_20'...
    apply ExtAx. split; intros Hx.
    + apply BInterE in Hx as [H1 H2].
      apply SepE in Hf1 as [Hf1 _]. apply PowerAx in Hf1.
      apply Hf1 in H1. apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]].
      subst x. apply CProdE2 in H2 as [H _].
      apply SepE in H as [_ H]. exfalso...
    + apply BInterE in Hx as [H1 H2].
      apply SepE in Hf2 as [Hf2 _]. apply PowerAx in Hf2.
      apply Hf2 in H1. apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]].
      subst x. apply CProdE2 in H2 as [H _].
      apply SepE in H as [_ H]. exfalso...
Qed.

(** 阿列夫零 **)
Notation ℵ₀ := (|ω|).

Lemma aleph0_is_card : is_card ℵ₀.
Proof. exists ω. reflexivity. Qed.

Fact card_of_power_ω : |𝒫 ω| = 2 ^ ℵ₀.
Proof. apply card_of_power. Qed.

Fact aleph0_neq_power : ℵ₀ ≠ 2 ^ ℵ₀.
Proof. apply card_neq_exp. apply aleph0_is_card. Qed.

(* 有限基数不等于阿列夫零 *)
Lemma fin_card_neq_aleph0 : ∀n ∈ ω, |n| ≠ ℵ₀.
Proof with nauto.
  intros n Hn.
  set {n ∊ ω | λ n, |n| ≠ ℵ₀} as N.
  ω_induction N Hn; intros H.
  - apply CardAx1 in H. symmetry in H.
    apply eqnum_empty in H. rewrite H in Hn. exfalso0.
  - assert (Heqw: ω = (ω - ⎨∅⎬) ∪ ⎨∅⎬) by (apply split_one_element; nauto).
    apply CardAx1 in H. rewrite Heqw in H. symmetry in H.
    apply finite_set_remove_one_element in H...
    apply IH. apply CardAx1. rewrite <- H. symmetry.
    exists σ. apply σ_bijective.
Qed.

(* 有限基数小于阿列夫零 *)
Lemma cardLt_aleph0_if_finite : ∀n ∈ ω, n <𝐜 ℵ₀.
Proof with eauto.
  intros n Hn. rewrite card_of_nat... apply cardLt_iff.
  split. apply ω_dominate... intros Hqn.
  apply CardAx1 in Hqn. eapply fin_card_neq_aleph0...
Qed.

(* 小于阿列夫零的基数是有限基数 *)
Lemma cardLt_aleph0_is_finite : ∀ 𝜅,
  is_card 𝜅 → 𝜅 <𝐜 ℵ₀ → finite 𝜅.
Proof with auto.
  intros 𝜅 [A Heq𝜅] Hlt. subst 𝜅.
  apply cardLt_iff in Hlt as [Hdm Hqn].
  rewrite <- set_finite_iff_card_finite.
  destruct (classic (finite A)) as [|Hinf]... exfalso.
  apply Hqn. apply infinite_set_dominated_by_ω_eqnum_ω...
Qed.

(* 基数是有限基数当且仅当它小于阿列夫零 *)
Lemma cardLt_aleph0_iff_finite : ∀ 𝜅,
  is_card 𝜅 → 𝜅 <𝐜 ℵ₀ ↔ finite 𝜅.
Proof with auto.
  intros 𝜅 Hcd. split.
  - apply cardLt_aleph0_is_finite...
  - intros Hfin. apply cardLt_aleph0_if_finite.
    apply nat_iff_fincard... split...
Qed.

(* 大于等于阿列夫零的基数是无限基数 *)
Corollary cardGeq_aleph0_infinite : ∀ 𝜅,
  is_card 𝜅 → ℵ₀ ≤ 𝜅 → infinite 𝜅.
Proof with auto.
  intros AC3 𝜅 Hcd Hfin.
  apply cardLt_aleph0_iff_finite in Hfin as [Hle Hnq]...
  apply Hnq. apply cardLeq_antisym...
Qed.

(* 阿列夫零是无限基数 *)
Corollary aleph0_infinite : infinite ℵ₀.
Proof with auto.
  apply cardGeq_aleph0_infinite... split...
Qed.
Hint Resolve aleph0_infinite : core.

Corollary aleph0_is_infcard : infcard ℵ₀.
Proof. split; auto. Qed.
Hint Resolve aleph0_is_infcard : core.

Fact cardAdd_aleph0_aleph0 : ℵ₀ + ℵ₀ = ℵ₀.
Proof with neauto; try congruence.
  apply CardAx1. eapply Equivalence_Transitive.
  apply cardAdd_well_defined.
  apply cardMul_well_defined. symmetry. apply CardAx0. reflexivity.
  apply cardMul_well_defined. symmetry. apply CardAx0. reflexivity.
  apply disjointify_0_1. apply disjointify_0_1.
  set (Func (ω × ⎨0⎬ ∪ ω × ⎨1⎬) ω (λ x,
    match (ixm (π2 x = 0)) with
    | inl _ => (2 ⋅ (π1 x))%n
    | inr _ => (2 ⋅ (π1 x) + 1)%n
  end)) as f.
  exists f. apply meta_bijective.
  - intros x Hx. apply BUnionE in Hx as [].
    + apply CProdE1 in H as [n [Hn [b [Hb H]]]].
      subst x. zfcrewrite. apply SingE in Hb.
      destruct (ixm (b = 0))... apply mul_ran...
    + apply CProdE1 in H as [n [Hn [b [Hb H]]]].
      subst x. zfcrewrite. apply SingE in Hb.
      destruct (ixm (b = 0)).
      * subst b. exfalso. eapply suc_neq_0...
      * apply add_ran... apply mul_ran...
  - intros x1 H1 x2 H2 Heq.
    assert (H20: Embed 2 ≠ Embed 0). { intros H. eapply suc_neq_0... }
    apply BUnionE in H1 as [H1|H1];
    apply BUnionE in H2 as [H2|H2];
    apply CProdE1 in H1 as [m [Hm [n [Hn H1]]]];
    apply CProdE1 in H2 as [p [Hp [q [Hq H2]]]];
    apply SingE in Hn; apply SingE in Hq;
    subst x1 x2 n q; zfcrewrite; apply op_iff.
    + destruct (ixm (Embed 0 = Embed 0))...
      split... apply mul_cancel' in Heq...
    + destruct (ixm (Embed 0 = Embed 0))...
      destruct (ixm (Embed 1 = Embed 0)).
      split... apply mul_cancel' in Heq...
      assert (H2m: (2 ⋅ m)%n ∈ ω) by (apply mul_ran; nauto).
      exfalso. apply (no_even_and_odd (2 ⋅ m)%n H2m).
      split. exists m. split...
      rewrite Heq. exists p. split...
    + destruct (ixm (Embed 0 = Embed 0))...
      destruct (ixm (Embed 1 = Embed 0)).
      split... apply mul_cancel' in Heq...
      assert (H2p: (2 ⋅ p)%n ∈ ω) by (apply mul_ran; nauto).
      exfalso. apply (no_even_and_odd (2 ⋅ p)%n H2p).
      split. exists p. split...
      rewrite <- Heq. exists m. split...
    + destruct (ixm (Embed 1 = Embed 0)).
      * exfalso. eapply suc_neq_0...
      * assert (H2m: (2 ⋅ m)%n ∈ ω) by (apply mul_ran; nauto).
        assert (H2p: (2 ⋅ p)%n ∈ ω) by (apply mul_ran; nauto).
        split... rewrite <- add_suc, <- add_suc in Heq...
        apply suc_injective in Heq... apply mul_cancel' in Heq...
  - intros y Hy. destruct (even_or_odd y Hy).
    + destruct H as [n [Hn Heqy]].
      exists <n, 0>. split. apply BUnionI1. apply CProdI...
      zfcrewrite. destruct (ixm (Embed 0 = Embed 0))...
    + destruct H as [n [Hn Heqy]].
      exists <n, 1>. split. apply BUnionI2. apply CProdI...
      zfcrewrite. destruct (ixm (Embed 1 = Embed 0))...
      exfalso. eapply suc_neq_0...
Qed.

Fact cardMul_expAleph0_expAleph0 :
  ∀ 𝜅, 𝜅 ^ ℵ₀ ⋅ 𝜅 ^ ℵ₀ = 𝜅 ^ ℵ₀.
Proof.
  intros. rewrite <- cardExp_id_1.
  rewrite cardAdd_aleph0_aleph0. reflexivity.
Qed.

Fact cardMul_aleph0_expAleph0 :
  ∀ 𝜅, 2 ≤ 𝜅 → ℵ₀ ⋅ 𝜅 ^ ℵ₀ = 𝜅 ^ ℵ₀.
Proof with auto.
  intros. eapply cardLeq_antisym.
  - rewrite <- cardMul_expAleph0_expAleph0 at 2.
    apply cardMul_preserve_leq.
    eapply cardLeq_tran; revgoals.
    apply cardExp_preserve_base_leq. apply H.
    apply cardLt_power. apply aleph0_is_card.
  - rewrite <- (cardMul_ident (𝜅 ^ ℵ₀)) at 1...
    rewrite cardMul_comm. apply cardMul_preserve_leq.
    pose proof (cardLt_aleph0_if_finite 1) as []; nauto.
Qed.

Fact cardExp_expAleph0_expAleph0 : ∀ 𝜅 𝜆, 2 ≤ 𝜆 →
  (𝜅 ^ ℵ₀) ^ (𝜆 ^ ℵ₀) = 𝜅 ^ (𝜆 ^ ℵ₀).
Proof with auto.
  intros AC6 * H2.
  rewrite cardExp_id_3, cardMul_aleph0_expAleph0...
Qed.

Fact cardMul_aleph0_aleph0 : ℵ₀ ⋅ ℵ₀ = ℵ₀.
Proof with auto.
  apply CardAx1. eapply Equivalence_Transitive.
  apply cardMul_well_defined; rewrite <- CardAx0; reflexivity.
  symmetry. apply ω_eqnum_ω_cp_ω.
Qed.

Fact cardExp_aleph0_n : ∀n ∈ ω, n ≠ ∅ → ℵ₀ ^ n = ℵ₀.
Proof with auto.
  intros n Hn.
  set {n ∊ ω | λ n, n ≠ ∅ → ℵ₀ ^ n = ℵ₀} as N.
  ω_induction N Hn.
  - intros. exfalso...
  - intros _. destruct (classic (m = 0)).
    + subst m. rewrite cardExp_1_r...
    + apply IH in H. rewrite <- card_suc, cardExp_suc, H...
      apply cardMul_aleph0_aleph0.
Qed.

(* 阿列夫零的自乘方等于2的幂 *)
Theorem cardExp_aleph0_aleph0 : ℵ₀ ^ ℵ₀ = 2 ^ ℵ₀.
Proof with nauto.
  apply cardLeq_antisym.
  - rewrite <- cardMul_aleph0_aleph0 at 3.
    rewrite <- cardExp_id_3.
    apply cardExp_preserve_base_leq.
    apply cardLt_power...
  - apply cardExp_preserve_base_leq.
    eapply cardLt_leq_tran.
    apply cardLt_aleph0_if_finite...
    apply cardLeq_refl...
Qed.
