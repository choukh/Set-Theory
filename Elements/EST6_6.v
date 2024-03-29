(** Adapted from "Elements of Set Theory" Chapter 6 **)
(** Coq coding by choukh, Oct 2020 **)

Require Import ZFC.Lib.ChoiceFacts.
Require Export ZFC.Elements.EST6_5.

(*** EST第六章6：无限基数的运算律：自乘等于自身，加法和乘法的吸收律 ***)

(* finite_union的引理 *)
Local Lemma finite_repl : ∀ a 𝒜,
  finite {X - {a,} | X ∊ 𝒜} → finite 𝒜.
Proof with auto.
  intros * [n [Hn Hrpl]].
  generalize dependent 𝒜.
  ω_induction n; intros 𝒜 Hqn. {
    apply eqnum_empty in Hqn. apply repl_eq_empty in Hqn. subst...
  }
  apply set_eqnum_suc_nonempty in Hqn as Hne...
  destruct Hne as [A HA].
  apply split_one_element in HA as HeqA. rewrite HeqA in Hqn.
  apply finite_set_remove_one_member in Hqn...
  destruct (classic (a ∈ A)).
  - replace ({X - {a,} | X ∊ 𝒜} - {A,})
    with {X - {a,} | X ∊ 𝒜} in Hqn. {
      apply IH in Hqn...
    }
    ext Hx.
    + apply ReplAx in Hx as [X [HX Hx]].
      apply SepI. apply ReplAx. exists X. split...
      apply SingNI. intros Heq. subst x. rewrite <- Heq in H.
      apply SepE in H as [_ Ha]. apply Ha...
    + apply SepE in Hx as [Hx _].
      apply ReplAx in Hx as [X [HX Hx]].
      apply ReplAx. exists X. split...
  - replace ({X - {a,} | X ∊ 𝒜} - {A,})
    with {X - {a,} | X ∊ 𝒜 - {A,} - {A ∪ {a,},}} in Hqn. {
      apply IH in Hqn. eapply add_one_still_finite_1.
      eapply add_one_still_finite_1. apply Hqn.
    }
    ext Hx.
    + apply ReplAx in Hx as [X [HX Hx]].
      apply SepE in HX as [HX H1].
      apply SepE in HX as [HX H2].
      apply SepI. apply ReplAx. exists X. split...
      destruct (classic (a ∈ X)).
      * apply SingNI. intros Heq. apply SingNE in H1. apply H1.
        rewrite <- Heq, <- Hx, remove_one_member_then_return...
      * rewrite <- Hx, remove_no_member...
    + apply SepE in Hx as [Hx Hx'].
      apply ReplAx in Hx as [X [HX Hx]].
      apply ReplAx. exists X. split...
      destruct (classic (a ∈ X)) as [Ha|Ha].
      * apply SepI. apply SepI... apply SingNI.
        intros Heq. subst X... apply SingNI.
        intros Heq. apply Hx'.
        rewrite <- Hx, Heq, add_one_member_then_remove...
      * rewrite remove_no_member in Hx... subst x.
        apply SepI. apply SepI... apply SingNI.
        intros Heq. apply Ha. rewrite Heq. apply BUnionI2...
Qed.

(* 如果一个集合的并集是有限集，那么该集合及其所有成员都是有限集 *)
Lemma finite_union : ∀ A, finite ⋃A → finite A ∧ (∀a ∈ A, finite a).
Proof with nauto.
  intros 𝒜 [n [Hn Hu]].
  generalize dependent 𝒜.
  ω_induction n; intros 𝒜 Hu.
  - apply eqnum_empty in Hu.
    apply union_eq_empty in Hu as []; subst.
    + split... intros a Ha. exfalso0.
    + split. apply nat_finite... rewrite <- one...
      intros a Ha. apply SingE in Ha. subst...
  - apply set_eqnum_suc_nonempty in Hu as Hne...
    destruct Hne as [a Ha].
    apply split_one_element in Ha as Hequ. rewrite Hequ in Hu.
    apply finite_set_remove_one_member in Hu...
    apply UnionAx in Ha as [A [HA Ha]].
    set {X - {a,} | X ∊ 𝒜} as 𝒜'.
    assert (Hequ': ⋃𝒜' = ⋃𝒜 - {a,}). {
      ext Hx.
      - apply UnionAx in Hx as [B [HB Hx]].
        apply ReplAx in HB as [C [HC Heq]]. subst B.
        apply SepE in Hx as [Hx Hx'].
        apply SepI... apply UnionAx. exists C. split...
      - apply SepE in Hx as [Hx Hx'].
        apply UnionAx in Hx as [B [HB Hx]].
        apply UnionAx. exists (B - {a,}). split...
        apply ReplAx. exists B. split... apply SepI...
    }
    rewrite <- Hequ' in Hu.
    apply IH in Hu as [H1 H2]. split.
    + apply finite_repl in H1...
    + intros B HB.
      assert (HB': B - {a,} ∈ 𝒜'). { apply ReplAx. exists B. split... }
      apply H2 in HB'. destruct (classic (a ∈ B)).
      * rewrite <- (remove_one_member_then_return _ a)...
        apply bunion_finite...
      * replace B with (B - {a,})...
        ext Hx.
        apply SepE1 in Hx...
        apply SepI... apply SingNI. intros Heq. subst...
Qed.

(* 如果两个集合的二元并是有限集，那么这两个集合都是有限集 *)
Lemma finite_bunion : ∀ A B, finite (A ∪ B) → finite A ∧ finite B.
Proof with auto.
  intros * Hfin.
  specialize finite_union with {A, B} as [_ H].
  - replace (⋃{A, B}) with (A ∪ B)...
  - split; apply H; [apply PairI1|apply PairI2].
Qed.

(* 两个集合的二元并是有限集当且仅当这两个集合都是有限集 *)
Theorem bunion_finite_iff : ∀ A B, finite A ∧ finite B ↔ finite (A ∪ B).
Proof.
  split.
  - intros [Ha Hb]. apply bunion_finite; auto.
  - apply finite_bunion.
Qed.

(* 两个集合的二元并是无限集当且仅当这两个集合中至少有一个是无限集 *)
Corollary bunion_infinite_iff : ∀ A B,
  infinite A ∨ infinite B ↔ infinite (A ∪ B).
Proof.
  intros. unfold infinite. rewrite <- bunion_finite_iff. tauto.
Qed.

(* 如果集合A与非空集合B的笛卡尔积是有限集，那么A是有限集 *)
Lemma finite_cprd_l : ∀ A B, ⦿ B → finite (A × B) → finite A.
Proof with auto.
  intros * [b Hb] Hfin.
  apply (dominated_by_finite_is_finite _ (A × B))...
  set (Func A (A × B) (λ x, <x, b>)) as f.
  exists f. apply meta_injection.
  - intros x Hx. apply CPrdI...
  - intros x1 H1 x2 H2 Heq.
    apply op_iff in Heq as []; subst...
Qed.

(* 如果集合B与非空集合A的笛卡尔积是有限集，那么B是有限集 *)
Lemma finite_cprd_r : ∀ A B, ⦿ A → finite (A × B) → finite B.
Proof with auto.
  intros * [a Ha] Hfin.
  apply (dominated_by_finite_is_finite _ (A × B))...
  set (Func B (A × B) (λ x, <a, x>)) as f.
  exists f. apply meta_injection.
  - intros x Hx. apply CPrdI...
  - intros x1 H1 x2 H2 Heq.
    apply op_iff in Heq as []; subst...
Qed.

(* 如果两个非空集合的笛卡尔积是有限集，那么这两个集合都是有限集 *)
Lemma finite_cprd : ∀ A B, ⦿ A → ⦿ B →
  finite (A × B) → finite A ∧ finite B.
Proof with auto.
  intros * Ha Hb Hfin. split.
  apply (finite_cprd_l A B)...
  apply (finite_cprd_r A B)...
Qed.

(* 两个非空集合的笛卡尔积是有限集当且仅当这两个集合都是有限集 *)
Theorem cprd_finite_iff : ∀ A B, ⦿ A → ⦿ B →
  finite A ∧ finite B ↔ finite (A × B).
Proof with auto.
  intros * Hnea Hneb. split.
  - intros [Ha Hb]. apply cprd_finite...
  - apply finite_cprd...
Qed.

(* 如果两个集合的笛卡尔积是无限集那么这两个集合中至少有一个是无限集 *)
Corollary infinite_cprd : ∀ A B,
  infinite (A × B) → infinite A ∨ infinite B.
Proof.
  intros. apply not_and_or. intros [Ha Hb].
  apply H. apply cprd_finite; auto.
Qed.

(* 无限集与任意非空集合的笛卡尔积是无限集 *)
Corollary cprd_infinite_l : ∀ A B, ⦿ B → infinite A → infinite (A × B).
Proof.
  intros * Hne Hinf Hfin. apply Hinf. eapply finite_cprd_l; eauto.
Qed.

(* 任意非空集合与无限集的笛卡尔积是无限集 *)
Corollary cprd_infinite_r : ∀ A B, ⦿ A → infinite B → infinite (A × B).
Proof.
  intros * Hne Hinf Hfin. apply Hinf. eapply finite_cprd_r; eauto.
Qed.

(* 两个非空集合的笛卡尔积是无限集当且仅当这两个集合中至少有一个是无限集 *)
Corollary cprd_infinite_iff : ∀ A B, ⦿ A → ⦿ B →
  infinite A ∨ infinite B ↔ infinite (A × B).
Proof.
  intros. unfold infinite. rewrite <- cprd_finite_iff; tauto.
Qed.

(* 如果集合A到至少包含两个元素的集合B的函数空间是有限集，那么A是有限集 *)
Lemma finite_arrow_l : ∀ A B, 2 ≤ |B| → finite (A ⟶ B) → finite A.
Proof with nauto.
  intros * H2 Hfin.
  rewrite (card_of_nat 2), cardLe_iff, two in H2...
  assert (H02: 0 ∈ 2%zfc1) by apply PairI1.
  assert (H12: 1 ∈ 2%zfc1) by (rewrite one; apply PairI2).
  destruct H2 as [f [Hif [Hdf Hrf]]].
  assert (Hif' := Hif). destruct Hif' as [Hff _].
  apply (dominated_by_finite_is_finite _ (A ⟶ B))...
  set (λ a, Func A B (λ x, match (ixm (x = a)) with
    | inl _ => f[0]
    | inr _ => f[1]
  end)) as G.
  set (Func A (A ⟶ B) (λ a, G a)) as g.
  assert (HG: ∀a ∈ A, G a: A ⇒ B). {
    intros a Ha. apply meta_function. intros x Hx.
    destruct (ixm (x = a)); apply Hrf; eapply ranI;
    apply func_correct; auto; rewrite Hdf...
  }
  exists g. apply meta_injection.
  - intros a Ha. apply SepI.
    + apply PowerAx. intros p Hp. apply SepE1 in Hp...
    + apply HG...
  - intros x1 H1 x2 H2 Heq.
    assert ((G x1)[x1] = (G x2)[x1]) by congruence. unfold G in H.
    do 2 (rewrite meta_func_ap in H; [|apply HG|])...
    destruct (ixm (x1 = x1)); destruct (ixm (x1 = x2))...
    + exfalso. apply injectiveE in H; auto; rewrite Hdf...
    + exfalso...
Qed.

(* 如果非空集合A到集合B的函数空间是有限集，那么B是有限集 *)
Lemma finite_arrow_r : ∀ A B, ⦿ A → finite (A ⟶ B) → finite B.
Proof with auto.
  intros * [a Ha] Hfin.
  apply (dominated_by_finite_is_finite _ (A ⟶ B))...
  set (λ b, Func A B (λ x, b)) as F.
  set (Func B (A ⟶ B) (λ b, F b)) as f.
  assert (HF: ∀b ∈ B, F b: A ⇒ B). {
    intros b Hb. apply meta_function. intros _ _...
  }
  exists f. apply meta_injection.
  - intros b Hb. apply SepI.
    + apply PowerAx. intros p Hp. apply SepE1 in Hp...
    + apply HF...
  - intros x1 H1 x2 H2 Heq.
    assert ((F x1)[a] = (F x2)[a]) by congruence. unfold F in H.
    do 2 (rewrite meta_func_ap in H; [|apply HF|])...
Qed.

(* 如果非空集合A到至少包含两个元素的集合B的函数空间是有限集，那么A和B都是有限集 *)
Lemma finite_arrow : ∀ A B, ⦿ A → 2 ≤ |B| →
  finite (A ⟶ B) → finite A ∧ finite B.
Proof with eauto.
  intros * Ha Hb Hfin. split.
  - eapply finite_arrow_l...
  - eapply finite_arrow_r...
Qed.

(* 非空集合A到至少包含两个元素的集合B的函数空间是有限集当且仅当A和B都是有限集 *)
Theorem arrow_finite_iff : ∀ A B, ⦿ A → 2 ≤ |B| →
  finite A ∧ finite B ↔ finite (A ⟶ B).
Proof with eauto.
  intros * Ha Hb. split.
  - intros [Hfina Hfinb]. apply arrow_finite...
  - intros Hfin. split.
    eapply finite_arrow_l... eapply finite_arrow_r...
Qed.

(* 如果两个集合张起的函数空间是无限集那么这两个集合中至少有一个是无限集 *)
Corollary infinite_arrow : ∀ A B,
  infinite (A ⟶ B) → infinite A ∨ infinite B.
Proof.
  intros. apply not_and_or. intros [Ha Hb].
  apply H. apply arrow_finite; auto.
Qed.

(* 无限集到至少包含两个元素的集合的函数空间是无限集 *)
Corollary cprd_arrow_l : ∀ A B, 2 ≤ |B| → infinite A → infinite (A ⟶ B).
Proof.
  intros * Hne Hinf Hfin. apply Hinf. eapply finite_arrow_l; eauto.
Qed.

(* 非空集合到无限集的函数空间是无限集 *)
Corollary cprd_arrow_r : ∀ A B, ⦿ A → infinite B → infinite (A ⟶ B).
Proof.
  intros * Hne Hinf Hfin. apply Hinf. eapply finite_arrow_r; eauto.
Qed.

(* 非空集合到至少包含两个元素的集合的函数空间是无限集当且仅当这两个集合中至少有一个是无限集 *)
Corollary cprd_arrow_iff : ∀ A B, ⦿ A → 2 ≤ |B| →
  infinite A ∨ infinite B ↔ infinite (A ⟶ B).
Proof.
  intros. unfold infinite. rewrite <- arrow_finite_iff; tauto.
Qed.

(* 有限基数的和是有限基数 *)
Lemma cardAdd_finite : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃ᶠⁱⁿ, finite (𝜅 + 𝜆).
Proof with auto.
  intros 𝜅 Hfck 𝜆 Hfcl.
  assert (Hk: 𝜅 ∈ ω). { apply nat_iff_fincard... }
  assert (Hl: 𝜆 ∈ ω). { apply nat_iff_fincard... }
  apply nat_iff_fincard. rewrite fin_cardAdd_eq_add... apply add_ran...
Qed.

(* 如果两个基数的和是有限基数那么这两个基数都是有限基数 *)
Lemma finite_cardAdd : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃,
  finite (𝜅 + 𝜆) → finite 𝜅 ∧ finite 𝜆.
Proof with eauto.
  intros 𝜅 Hcdk 𝜆 Hcdl Hfin.
  apply cardLt_aleph0_iff_finite in Hfin... split.
  - apply cardLt_aleph0_iff_finite...
    eapply cardLe_lt_trans... rewrite <- cardAdd_0_r at 1...
    apply cardAdd_preserve_le'. apply cardLe_0...
  - apply cardLt_aleph0_iff_finite...
    eapply cardLe_lt_trans... rewrite <- cardAdd_0_r at 1...
    rewrite cardAdd_comm. apply cardAdd_preserve_le. apply cardLe_0...
Qed.

(* 两个基数的和是有限基数当且仅当这两个基数都是有限基数 *)
Theorem cardAdd_finite_iff : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃,
  finite 𝜅 ∧ finite 𝜆 ↔ finite (𝜅 + 𝜆).
Proof with auto.
  intros 𝜅 Hcdk 𝜆 Hcdl. split.
  - intros [Hfink Hfinl]. apply cardAdd_finite; split...
  - apply finite_cardAdd...
Qed.

(* 如果两个基数的和是无限基数那么这两个基数中至少有一个是无限基数 *)
Corollary infinite_cardAdd : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃,
  infinite (𝜅 + 𝜆) → infinite 𝜅 ∨ infinite 𝜆.
Proof.
  intros 𝜅 Hcdk 𝜆 Hcdl Hinf. apply not_and_or.
  intros [Hfink Hfinl]. apply Hinf.
  apply cardAdd_finite; split; auto.
Qed.

(* 无限基数与任意基数的和是无限基数 *)
Corollary cardAdd_infinite : ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, ∀𝜆 ⋵ 𝐂𝐃, infinite (𝜅 + 𝜆).
Proof.
  intros 𝜅 [Hcdk Hinf] 𝜆 Hcdl Hfin. apply Hinf.
  apply (finite_cardAdd 𝜅 Hcdk 𝜆); auto.
Qed.

Corollary cardAdd_infinite' : ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, ∀𝜆 ⋵ 𝐂𝐃, infinite (𝜆 + 𝜅).
Proof with auto.
  intros 𝜅 [Hcdk Hinf] 𝜆 Hcdl Hfin. apply Hinf.
  apply (finite_cardAdd 𝜆 Hcdl 𝜅); auto.
Qed.

(* 两个基数的和是无限基数当且仅当这两个基数中至少有一个是无限基数 *)
Corollary cardAdd_infinite_iff : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃,
  infinite 𝜅 ∨ infinite 𝜆 ↔ infinite (𝜅 + 𝜆).
Proof.
  intros 𝜅 Hcdk 𝜆 Hcdl. unfold infinite.
  rewrite <- (cardAdd_finite_iff 𝜅 Hcdk 𝜆 Hcdl); tauto.
Qed.

(* 有限基数的积是有限基数 *)
Lemma cardMul_finite : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃ᶠⁱⁿ, 𝜅 ⋅ 𝜆 ⋵ 𝐂𝐃ᶠⁱⁿ.
Proof with auto.
  intros 𝜅 Hk 𝜆 Hl.
  apply nat_iff_fincard in Hk.
  apply nat_iff_fincard in Hl.
  apply nat_iff_fincard. rewrite fin_cardMul_eq_mul... apply mul_ran...
Qed.

(* 如果基数𝜅与非零基数的积是有限基数那么𝜅是有限基数 *)
Lemma finite_cardMul_l : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃, 𝜆 ≠ 0 →
  finite (𝜅 ⋅ 𝜆) → finite 𝜅.
Proof with eauto.
  intros 𝜅 Hcdk 𝜆 Hcdl Hnel Hfin.
  apply cardLt_aleph0_iff_finite in Hfin...
  apply cardLt_aleph0_iff_finite...
  eapply cardLe_lt_trans... rewrite <- cardMul_1_r at 1...
  apply cardMul_preserve_le'. apply cardLe_1...
Qed.

(* 如果非零基数与基数𝜆的积是有限基数那么𝜆是有限基数 *)
Lemma finite_cardMul_r : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃, 𝜅 ≠ 0 →
  finite (𝜅 ⋅ 𝜆) → finite 𝜆.
Proof with eauto.
  intros 𝜅 Hcdk 𝜆 Hcdl Hnek Hfin.
  rewrite cardMul_comm in Hfin.
  apply (finite_cardMul_l 𝜆 Hcdl 𝜅)...
Qed.

(* 如果两个非零基数的积是有限基数那么这两个基数都是有限基数 *)
Lemma finite_cardMul : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃, 𝜅 ≠ 0 → 𝜆 ≠ 0 →
  finite (𝜅 ⋅ 𝜆) → finite 𝜅 ∧ finite 𝜆.
Proof with auto.
  intros 𝜅 Hcdk 𝜆 Hcdl Hnek Hnel Hfin. split.
  apply (finite_cardMul_l 𝜅 Hcdk 𝜆)...
  apply (finite_cardMul_r 𝜅 Hcdk 𝜆)...
Qed.

(* 两个非零基数的积是有限基数当且仅当这两个基数都是有限基数 *)
Theorem cardMul_finite_iff : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃, 𝜅 ≠ 0 → 𝜆 ≠ 0 →
  finite 𝜅 ∧ finite 𝜆 ↔ finite (𝜅 ⋅ 𝜆).
Proof with auto.
  intros 𝜅 Hcdk 𝜆 Hcdl Hnek Hnel. split.
  - intros [Hfink Hfinl]. apply cardMul_finite; split...
  - apply finite_cardMul...
Qed.

(* 如果两个基数的积是无限基数那么这两个基数中至少有一个是无限基数 *)
Corollary infinite_cardMul : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃,
  infinite (𝜅 ⋅ 𝜆) → infinite 𝜅 ∨ infinite 𝜆.
Proof.
  intros 𝜅 Hcdk 𝜆 Hcdl Hinf. apply not_and_or.
  intros [Hfink Hfinl]. apply Hinf.
  apply cardMul_finite; split; auto.
Qed.

(* 无限基数与非零基数的积是无限基数 *)
Corollary cardMul_infinite :
  ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, ∀𝜆 ⋵ 𝐂𝐃, 𝜆 ≠ 0 → infinite (𝜅 ⋅ 𝜆).
Proof.
  intros 𝜅 [Hcdk Hinf] 𝜆 Hcdl H0 Hfin. apply Hinf.
  apply (finite_cardMul_l 𝜅 Hcdk 𝜆); auto.
Qed.

Corollary cardMul_infinite' :
  ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, ∀𝜆 ⋵ 𝐂𝐃, 𝜆 ≠ 0 → infinite (𝜆 ⋅ 𝜅).
Proof.
  intros 𝜅 [Hcdk Hinf] 𝜆 Hcdl H0 Hfin. apply Hinf.
  apply (finite_cardMul_r 𝜆 Hcdl 𝜅); auto.
Qed.

(* 两个非空基数的积是无限基数当且仅当这两个基数中至少有一个是无限基数 *)
Corollary cardMul_infinite_iff : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃, 𝜅 ≠ 0 → 𝜆 ≠ 0 →
  infinite 𝜅 ∨ infinite 𝜆 ↔ infinite (𝜅 ⋅ 𝜆).
Proof.
  intros 𝜅 Hcdk 𝜆 Hcdl Hnek Hnel. unfold infinite.
  rewrite <- (cardMul_finite_iff 𝜅 Hcdk 𝜆 Hcdl Hnek Hnel); tauto.
Qed.

(* 有限基数的幂是有限基数 *)
Lemma cardExp_finite : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃ᶠⁱⁿ, 𝜅 ^ 𝜆 ⋵ 𝐂𝐃ᶠⁱⁿ.
Proof with auto.
  intros 𝜅 Hk 𝜆 Hl.
  apply nat_iff_fincard in Hk.
  apply nat_iff_fincard in Hl.
  apply nat_iff_fincard. rewrite fin_cardExp_eq_exp... apply exp_ran...
Qed.

(* 如果基数𝜅的非零基数次幂是有限基数那么𝜅是有限基数 *)
Lemma finite_cardExp_l : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃, 𝜆 ≠ 0 →
  finite (𝜅 ^ 𝜆) → finite 𝜅.
Proof with eauto.
  intros 𝜅 Hcdk 𝜆 Hcdl H0 Hfin.
  apply cardLt_aleph0_iff_finite in Hfin...
  apply cardLt_aleph0_iff_finite...
  eapply cardLe_lt_trans... rewrite <- cardExp_1_r at 1...
  apply cardExp_preserve_exponent_le.
  - left. apply suc_neq_0.
  - apply cardLe_1...
Qed.

(* 如果不小于2的基数的𝜆次幂是有限基数那么𝜆是有限基数 *)
Lemma finite_cardExp_r : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃, Embed 2 ≤ 𝜅 →
  finite (𝜅 ^ 𝜆) → finite 𝜆.
Proof with eauto.
  intros 𝜅 Hcdk 𝜆 Hcdl H0 Hfin.
  apply cardLt_aleph0_iff_finite in Hfin...
  apply cardLt_aleph0_iff_finite...
  eapply cardLe_lt_trans... eapply cardLt_le_trans...
  apply cardLt_power... apply cardExp_preserve_base_le...
Qed.

(* 如果不小于2的基数𝜅的非零基数𝜆次幂是有限基数那么𝜅和𝜆都是有限基数 *)
Lemma finite_cardExp : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃, Embed 2 ≤ 𝜅 → 𝜆 ≠ 0 →
finite (𝜅 ^ 𝜆) → finite 𝜅 ∧ finite 𝜆.
Proof with auto.
  intros 𝜅 Hcdk 𝜆 Hcdl H0 H2 Hfin. split.
  - apply (finite_cardExp_l 𝜅 Hcdk 𝜆)...
  - apply (finite_cardExp_r 𝜅 Hcdk 𝜆)...
Qed.

(* 如果𝜅是非零基数且𝜆是大于1的基数，那么𝜅的𝜆次幂是有限基数当且仅当𝜅和𝜆都是有限基数 *)
Theorem cardExp_finite_iff : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃, Embed 2 ≤ 𝜅 → 𝜆 ≠ 0 →
  finite 𝜅 ∧ finite 𝜆 ↔ finite (𝜅 ^ 𝜆).
Proof with auto.
  intros 𝜅 Hcdk 𝜆 Hcdl H0 H2. split.
  - intros [Hfink Hfinl]. apply cardExp_finite; split...
  - apply finite_cardExp...
Qed.

(* 如果两个基数的幂是无限基数那么这两个基数中至少有一个是无限基数 *)
Corollary infinite_cardExp : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃,
  infinite (𝜅 ^ 𝜆) → infinite 𝜅 ∨ infinite 𝜆.
Proof.
  intros 𝜅 Hcdk 𝜆 Hcdl Hinf. apply not_and_or.
  intros [Hfink Hfinl]. apply Hinf.
  apply cardExp_finite; split; auto.
Qed.

(* 无限基数的非零基数次幂是无限基数 *)
Corollary cardExp_infinite_base : ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, ∀𝜆 ⋵ 𝐂𝐃,
  𝜆 ≠ 0 → infinite (𝜅 ^ 𝜆).
Proof.
  intros 𝜅 [Hcdk Hinf] 𝜆 Hcdl H0 Hfin. apply Hinf.
  apply (finite_cardExp_l 𝜅 Hcdk 𝜆); auto.
Qed.

(* 不小于2的基数的无限基数次幂是无限基数 *)
Corollary cardExp_infinite_exponent : ∀𝜅 ⋵ 𝐂𝐃, ∀𝜆 ⋵ 𝐂𝐃ⁱⁿᶠ,
  Embed 2 ≤ 𝜅 → infinite (𝜅 ^ 𝜆).
Proof.
  intros 𝜅 Hcdk 𝜆 [Hcdl Hinf] H2 Hfin. apply Hinf.
  apply (finite_cardExp_r 𝜅 Hcdk 𝜆); auto.
Qed.

(* 不小于2的基数的非零基数次幂是无限基数当且仅当这两个基数中至少有一个是无限基数 *)
Corollary cardExp_infinite_iff : ∀ 𝜅 𝜆 ⋵ 𝐂𝐃,
  Embed 2 ≤ 𝜅 → 𝜆 ≠ 0 →
  infinite 𝜅 ∨ infinite 𝜆 ↔ infinite (𝜅 ^ 𝜆).
Proof.
  intros 𝜅 Hcdk 𝜆 Hcdl Hnek Hnel. unfold infinite.
  rewrite <- (cardExp_finite_iff 𝜅 Hcdk 𝜆 Hcdl Hnek Hnel); tauto.
Qed.

(* 无限集的幂集是无限集 *)
Corollary power_infinite : ∀ A, infinite A → infinite 𝒫 A.
Proof with nauto.
  intros. apply set_infinite_iff_card_infinite.
  rewrite card_of_power. apply cardExp_infinite_exponent...
  split... rewrite <- set_infinite_iff_card_infinite...
  apply cardLe_refl...
Qed.

(* ==需要选择公理== *)
(* 无限基数自乘等于自身 *)
Theorem cardMul_infcard_self : AC_VI → ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, 𝜅 ⋅ 𝜅 = 𝜅.
Proof with neauto; try congruence.
  intros AC6 𝜅 [[B Heq𝜅] Hinf].
  assert (AC3: AC_III). { apply AC_VI_to_III... }
  assert (AC5: AC_V). { apply AC_VI_to_V... }
  set (λ f, f = ∅ ∨ ∃ A, infinite A ∧ A ⊆ B ∧ f: A × A ⟺ A) as P.
  set {f ∊ 𝒫 ((B × B) × B) | P f} as ℋ.
  pose proof (AC6 ℋ) as [f₀ [Hf₀ Hmax]]. {
    intros 𝒞 Hchn Hsub.
    apply SepI. {
      apply PowerAx. intros p Hp.
      apply UnionAx in Hp as [f [Hf Hp]].
      apply Hsub in Hf. apply SepE in Hf as [Hf _].
      apply PowerAx in Hf. apply Hf...
    }
    destruct (classic (∀f ∈ 𝒞, f = ∅)) as [|Hne]. {
      left. ext p Hp.
      - apply UnionAx in Hp as [f [Hf Hp]].
        apply H in Hf. subst f. exfalso0.
      - exfalso0.
    }
    right. set (⋃{ran f | f ∊ 𝒞}) as A.
    exists A. split; [|split]. {
      apply set_not_all_ex_not in Hne as [f [Hf Hnef]].
      apply Hsub in Hf as Hf'. apply SepE in Hf' as [_ []]. exfalso...
      destruct H as [C [HinfC [_ [_ [_ Hr]]]]].
      intros Hfin. apply finite_union in Hfin as [_ Hfin].
      apply HinfC. apply Hfin. apply ReplAx. exists f. split...
    } {
      intros x Hx. unfold A in Hx.
      rewrite <- ex3_8_b in Hx.
      apply ranE in Hx as [w Hp].
      apply UnionAx in Hp as [C [HC Hp]].
      apply Hsub in HC. apply SepE in HC as [HC _].
      apply PowerAx in HC. apply HC in Hp.
      apply CPrdE2 in Hp as [_ Hx]...
    } {
      split; split; [| | |rewrite ex3_8_b]...
      - apply ex3_15.
        + intros f Hf. apply Hsub in Hf.
          apply SepE in Hf as [_ []]. subst f. apply empty_is_func.
          destruct H as [C [_ [_ [[] _]]]]...
        + intros f Hf g Hg. apply Hchn...
      - intros y H. rewrite <- unique_existence.
        split. apply ranE... intros x1 x2 H1 H2.
        apply UnionAx in H1 as [f [Hf H1]].
        apply UnionAx in H2 as [g [Hg H2]].
        pose proof (Hchn _ Hf _ Hg) as [].
        + apply H0 in H1. apply Hsub in Hg.
          apply SepE in Hg as [_ []]. subst g. exfalso0.
          destruct H3 as [C [_ [_ [[_ Hsr] _]]]]. eapply singrE...
        + apply H0 in H2. apply Hsub in Hf.
          apply SepE in Hf as [_ []]. subst f. exfalso0.
          destruct H3 as [C [_ [_ [[_ Hsr] _]]]]. eapply singrE...
      - assert (Hsubr: ∀f ∈ 𝒞, ran f ⊆ A). {
          intros f Hf y Hy.
          apply UnionAx. exists (ran f). split...
          apply ReplAx. exists f. split...
        }
        assert (HA: ∀x ∈ A, ∃f ∈ 𝒞, x ∈ ran f). {
          intros x Hx. apply UnionAx in Hx as [C [HC Hx]].
          apply ReplAx in HC as [f [Hf HC]]. subst C.
          exists f. split...
        }
        assert (Hdr: ∀f ∈ 𝒞, dom f = ran f × ran f). {
          intros f Hf. apply Hsub in Hf.
          apply SepE in Hf as [_ []].
          - subst f. ext Hx.
            + apply domE in Hx as [y Hp]. exfalso0.
            + apply CPrdE1 in Hx as [a [Ha _]].
              apply ranE in Ha as [w Hp]. exfalso0.
          - destruct H as [C [_ [_ [_ [Hd Hr]]]]]...
        }
        ext Hx.
        + apply domE in Hx as [y Hp].
          apply UnionAx in Hp as [f [Hf Hx]].
          apply domI in Hx. rewrite Hdr in Hx...
          apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]]. subst x.
          apply CPrdI; eapply Hsubr...
        + apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]]. subst x.
          apply HA in Ha as [f [Hf Ha]].
          apply HA in Hb as [g [Hg Hb]].
          rewrite ex3_8_a. apply UnionAx.
          pose proof (Hchn _ Hf _ Hg) as [].
          * apply ranE in Ha as [y Hp].
            exists (dom g). split. apply ReplAx. exists g. split...
            rewrite Hdr... apply CPrdI... eapply ranI. apply H...
          * apply ranE in Hb as [y Hp].
            exists (dom f). split. apply ReplAx. exists f. split...
            rewrite Hdr... apply CPrdI... eapply ranI. apply H...
    }
  }
  (* if f₀ = ∅ *)
  apply SepE in Hf₀ as [Hsubf₀ []]. {
    cut (∃g ∈ ℋ, g ≠ ∅). {
      intros [g [Hg Hg']]. exfalso.
      apply Hmax in Hg as []; subst f₀...
      apply H0. apply empty_sub_all.
    }
    rewrite Heq𝜅 in Hinf.
    apply set_infinite_iff_card_infinite in Hinf.
    apply ω_is_the_least_infinite_set in Hinf as Hdm; [|apply AC3].
    apply dominate_iff in Hdm as [A [HsubA Hqn]].
    assert (HinfA: infinite A). {
      intros Hfin. apply ω_infinite.
      apply (dominated_by_finite_is_finite _ A)...
      apply eqnum_dominate. now rewrite Hqn.
    }
    assert (Hg: A × A ≈ A). {
      rewrite <- Hqn at 3. eapply Equivalence_Transitive.
      apply cardMul_well_defined; symmetry; apply Hqn.
      symmetry. apply ω_eqnum_ω_cp_ω.
    }
    destruct Hg as [g Hg].
    exists g. split.
    - apply SepI.
      + destruct Hg as [[Hg _] [Hd Hr]].
        apply PowerAx. intros p Hp.
        apply func_pair' in Hp as [x [y [Hp Heqp]]]... subst p.
        apply domI in Hp as Hx. rewrite Hd in Hx.
        apply ranI in Hp as Hy. rewrite Hr in Hy.
        apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]]. subst x.
        apply CPrdI. apply CPrdI; apply HsubA... apply HsubA...
      + right. exists A. split... 
    - destruct Hg as [[Hg _] [Hd _]].
      apply infinite_set_nonempty in HinfA as [a Ha].
      apply EmptyNI. exists <<a, a>, g[<a, a>]>.
      apply func_correct... rewrite Hd. apply CPrdI...
  }
  (* if f₀ ≠ ∅ *)
  destruct H as [A₀ [HinfA₀ [HsubA₀ Hf₀]]].
  apply set_infinite_iff_card_infinite in HinfA₀...
  set (|A₀|) as 𝜆. fold 𝜆 in HinfA₀.
  assert (Hcd: 𝜆 ⋵ 𝐂𝐃). { exists A₀... }
  assert (Hmul: 𝜆 ⋅ 𝜆 = 𝜆). {
    apply CardAx1. eapply Equivalence_Transitive.
    apply cardMul_well_defined; symmetry; apply CardAx0.
    exists f₀...
  }
  replace 𝜅 with 𝜆...
  apply cardLe_antisym. {
    rewrite Heq𝜅. apply cardLe_iff. apply dominate_sub...
  }
  (* Goal: 𝜅 ≤ 𝜆 *)
  rewrite <- Hmul.
  eapply cardLe_trans; revgoals. {
    apply cardMul_preserve_le.
    apply cardLt_infcard_n. split...
    apply (embed_ran 2).
  }
  rewrite <- cardAdd_k_k.
  assert (Heq: |A₀| + |B - A₀| = |B|). {
    rewrite cardAdd_disjoint.
    - replace (A₀ ∪ (B - A₀)) with B... rewrite ex2_11_2.
      ext Hx. apply BUnionI2...
      apply BUnionE in Hx as []...
    - apply disjointI. intros [x [H1 H2]].
      apply SepE in H2 as [_ H2]...
  }
  rewrite Heq𝜅, <- Heq... clear Heq.
  pose proof (card_comparability AC5 (|B - A₀|)) as []... {
    eapply cardLe_trans; revgoals. {
      apply cardAdd_preserve_le'. apply H.
    }
    apply cardLe_refl. apply cardAdd_is_card.
  }
  (* Goal: 𝜆 ≰ |B - A₀| *)
  exfalso. unfold 𝜆 in H. rewrite cardLe_iff in H.
  apply dominate_iff in H as [D [HsubD HqnD]].
  assert (Heq𝜆: 𝜆 = |D|). { apply CardAx1... }
  assert (Hdj: disjoint A₀ D). {
    apply disjointI. intros [x [H1 H2]].
    apply HsubD in H2. apply SepE2 in H2...
  }
  assert (Hqn: (A₀ × D) ∪ (D × A₀) ∪ (D × D) ≈ D). {
    apply cardAdd_disjoint_iff. {
      apply disjointI. intros [x [H1 H2]]. apply BUnionE in H1 as [].
      - eapply disjointE. apply cprd_disjoint_l... apply H. apply H2.
      - eapply disjointE. apply cprd_disjoint_r... apply H. apply H2.
    }
    rewrite <- cardAdd_disjoint; revgoals. {
      apply disjointI. intros [x [H1 H2]].
      eapply disjointE. apply cprd_disjoint_l... apply H1. apply H2.
    }
    do 3 rewrite <- cardMul.
    fold 𝜆. rewrite <- Heq𝜆, Hmul.
    apply cardLe_antisym; revgoals. {
      rewrite cardAdd_assoc. apply cardAdd_enlarge...
    }
    (* Goal: 𝜆 + 𝜆 + 𝜆 ≤ 𝜆 *)
    rewrite <- Hmul at 4.
    replace (𝜆 + 𝜆 + 𝜆) with (3 ⋅ 𝜆). {
      apply cardMul_preserve_le.
      apply cardLt_infcard_n. split...
      apply (embed_ran 3).
    }
    rewrite pred, <- card_suc...
    rewrite cardMul_comm, cardMul_distr, cardMul_1_r...
    rewrite cardMul_comm, cardAdd_k_k...
  }
  destruct Hqn as [g [Hig [Hdg Hrg]]].
  destruct Hf₀ as [Hif [Hdf₀ Hrf₀]].
  assert (Hig' := Hig). destruct Hig' as [Hfg _].
  assert (Hif' := Hif). destruct Hif' as [Hff _].
  cut (f₀ ∪ g ∈ ℋ). {
    intros H. apply Hmax in H as [].
    - apply H. intros p Hp. apply BUnionI1...
    - rewrite Heq𝜆 in HinfA₀.
      apply set_infinite_iff_card_infinite in HinfA₀...
      apply infinite_set_nonempty in HinfA₀ as [d Hd].
      assert (Hp: <<d, d>, g[<d, d>]> ∈ f₀ ∪ g). {
        apply BUnionI2. apply func_correct...
        rewrite Hdg. apply BUnionI2. apply CPrdI...
      }
      rewrite <- H in Hp. apply domI in Hp.
      rewrite Hdf₀ in Hp. apply CPrdE2 in Hp as [Hd' _].
      apply HsubD in Hd. apply SepE2 in Hd...
  }
  (* Goal: f₀ ∪ g ∈ ℋ *)
  assert (HsubD': D ⊆ B). {
    intros x Hx. apply HsubD in Hx. apply SepE1 in Hx...
  }
  apply SepI.
  - apply PowerAx. intros p Hp. apply BUnionE in Hp as [].
    + apply PowerAx in Hsubf₀. apply Hsubf₀...
    + apply func_pair' in H as [x [y [H Heqp]]]... subst p.
      apply domI in H as Hx. rewrite Hdg in Hx.
      apply ranI in H as Hy. rewrite Hrg in Hy.
      apply BUnionE in Hx as [Hx|Hx]; [apply BUnionE in Hx as [Hx|Hx]|].
      * apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]]. subst x.
        apply CPrdI; [apply CPrdI|].
        apply HsubA₀... apply HsubD'... apply HsubD'...
      * apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]]. subst x.
        apply CPrdI; [apply CPrdI|].
        apply HsubD'... apply HsubA₀... apply HsubD'...
      * apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]]. subst x.
        apply CPrdI; [apply CPrdI|]; apply HsubD'...
  - right. exists (A₀ ∪ D). split; [|split].
    + intros Hfin. apply finite_bunion in Hfin as [Hfin _].
      apply set_finite_iff_card_finite in Hfin. apply HinfA₀...
    + intros x Hx. apply BUnionE in Hx as [].
      apply HsubA₀... apply HsubD'...
    + rewrite ex3_2_a, ex3_2_a', ex3_2_a', <- bunion_assoc,
        (bunion_assoc (D × A₀)), (bunion_comm (D × A₀)).
      split; [|split].
      * apply bunion_injective... split. {
          intros x Hx. exfalso. apply BInterE in Hx as [H1 H2].
          rewrite Hdf₀ in H1. rewrite Hdg in H2.
          apply BUnionE in H2 as []; [apply BUnionE in H as []|].
          - eapply disjointE. apply cprd_disjoint_r... apply H1. apply H.
          - eapply disjointE. apply cprd_disjoint_l... apply H1. apply H.
          - eapply disjointE. apply cprd_disjoint_r... apply H1. apply H.
        } {
          intros y Hy. exfalso. apply BInterE in Hy as [H1 H2].
          rewrite Hrf₀ in H1. rewrite Hrg in H2. eapply disjointE...
        }
      * ext Hx. {
          apply domE in Hx as [y Hp]. apply BUnionE in Hp as [].
          - apply domI in H. rewrite Hdf₀ in H. apply BUnionI1...
          - apply domI in H. rewrite Hdg in H. apply BUnionI2...
        } {
          apply BUnionE in Hx as [].
          - rewrite <- Hdf₀ in H. apply domE in H as [y Hp].
            eapply domI. apply BUnionI1...
          - rewrite <- Hdg in H. apply domE in H as [y Hp].
            eapply domI. apply BUnionI2...
        }
      * ext y Hy. {
          apply ranE in Hy as [x Hp]. apply BUnionE in Hp as [].
          - apply ranI in H. rewrite Hrf₀ in H. apply BUnionI1...
          - apply ranI in H. rewrite Hrg in H. apply BUnionI2...
        } {
          apply BUnionE in Hy as [].
          - rewrite <- Hrf₀ in H. apply ranE in H as [x Hp].
            eapply ranI. apply BUnionI1...
          - rewrite <- Hrg in H. apply ranE in H as [x Hp].
            eapply ranI. apply BUnionI2...
        }
Qed.

(* ==需要选择公理== *)
(* 无限基数的非零有限次幂等于自身 *)
Corollary cardExp_infcard_id : AC_VI →
  ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, ∀n ∈ ω, n ≠ ∅ → 𝜅 ^ n = 𝜅.
Proof with auto.
  intros AC6 𝜅 [Hinf Hcd] n Hn.
  ω_induction n.
  - intros. exfalso...
  - intros _. destruct (classic (m = 0)).
    + subst m. rewrite cardExp_1_r...
    + apply IH in H. rewrite <- card_suc, cardExp_suc, H...
      apply cardMul_infcard_self... split...
Qed.

(* ==需要选择公理== *)
(* 无限基数的有限次幂不大于自身 *)
Corollary cardExp_infcard_le : AC_VI →
  ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, ∀n ∈ ω, 𝜅 ^ n ≤ 𝜅.
Proof with nauto.
  intros AC6 𝜅 [Hinf Hcd] n Hn.
  destruct (classic (n = 0)). {
    subst n. rewrite cardExp_0_r.
    apply cardLt_infcard_n... split...
  }
  rewrite cardExp_infcard_id... apply cardLe_refl... split...
Qed.

(* ==需要选择公理== *)
(* 无限基数自加等于自身 *)
Theorem cardAdd_infcard_self : AC_VI → ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, 𝜅 + 𝜅 = 𝜅.
Proof with nauto.
  intros AC6 𝜅 Hic. apply cardLe_antisym.
  - rewrite cardAdd_k_k. eapply cardLe_trans.
    apply cardMul_preserve_le. apply (cardLt_infcard_n 𝜅)...
    rewrite cardMul_infcard_self... apply cardLe_refl. apply Hic.
  - apply cardAdd_enlarge; apply Hic.
Qed.

(* ==需要选择公理== *)
(* 无限基数加1等于自身 *)
Theorem cardAdd_infcard_1 : AC_VI → ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, 𝜅 + 1 = 𝜅.
Proof with nauto.
  intros AC6 𝜅 Hic. apply cardLe_antisym.
  - rewrite <- (cardAdd_infcard_self AC6 𝜅) at 2...
    rewrite cardAdd_comm... apply cardAdd_preserve_le.
    apply (cardLt_infcard_n 𝜅)...
  - apply cardAdd_enlarge... apply Hic.
Qed.

(* ==需要选择公理== *)
(* 基数加法的吸收律 *)
Theorem cardAdd_absorption : AC_VI → ∀ 𝜅 𝜆,
  infinite 𝜅 → 𝜆 ≤ 𝜅 → 𝜅 + 𝜆 = 𝜅.
Proof.
  intros AC6 * Hinf Hle. apply cardLe_antisym.
  - eapply cardLe_trans. apply cardAdd_preserve_le'. apply Hle.
    rewrite cardAdd_infcard_self; [|auto|split; auto; apply Hle].
    apply cardLe_refl. apply Hle.
  - apply cardAdd_enlarge; apply Hle.
Qed.

(* ==需要选择公理== *)
(* 基数乘法的吸收律 *)
Theorem cardMul_absorption : AC_VI → ∀ 𝜅 𝜆,
  infinite 𝜅 → 𝜆 ≤ 𝜅 → 𝜆 ≠ 0 → 𝜅 ⋅ 𝜆 = 𝜅.
Proof.
  intros AC6 * Hinf Hle H0. apply cardLe_antisym.
  - eapply cardLe_trans. apply cardMul_preserve_le'. apply Hle.
    rewrite cardMul_infcard_self; [|auto|split; auto; apply Hle].
    apply cardLe_refl. apply Hle.
- apply cardMul_enlarge; auto; apply Hle.
Qed.

(* ==需要选择公理== *)
(* 无限基数自乘方等于2的幂 *)
Theorem cardExp_infcard_self : AC_VI → ∀𝜅 ⋵ 𝐂𝐃ⁱⁿᶠ, 𝜅 ^ 𝜅 = 2 ^ 𝜅.
Proof with nauto.
  intros AC6 𝜅 [Hinf Hcd]. apply cardLe_antisym.
  - rewrite <- (cardMul_infcard_self AC6 𝜅) at 3; [|split]...
    rewrite <- cardExp_exp.
    apply cardExp_preserve_base_le. apply cardLt_power...
  - apply cardExp_preserve_base_le.
    eapply cardLt_le_trans.
    apply cardLt_aleph0_if_finite...
    apply aleph0_is_the_least_infinite_card.
    apply AC_VI_to_III... split...
Qed.
