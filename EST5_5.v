(** Based on "Elements of Set Theory" Chapter 5 Part 5 **)
(** Coq coding by choukh, July 2020 **)

Require Export ZFC.EX5.

(*** EST第五章5：实数的定义(戴德金分割)，实数的序，实数的完备性，
  实数算术：加法，加法逆元 ***)

(* 柯西序列 *)
Module CauchyReal.

Open Scope Rat_scope.

Definition CauchySeq : set :=
  {s ∊ ω ⟶ ℚ | λ s,
    ∀ε ∈ ℚ, ratPos ε → ∃k ∈ ω, ∀ m n ∈ ω, k ∈ m → k ∈ n →
    |s[m] - s[n]| <𝐪 ε
  }.

Definition CauchyEquiv : set :=
  Rel CauchySeq CauchySeq (λ r s,
    ∀ε ∈ ℚ, ratPos ε → ∃k ∈ ω, ∀n ∈ ω, k ∈ n →
    |r[n] - s[n]| <𝐪 ε
  ).

Declare Scope CauchyReal_scope.
Open Scope CauchyReal_scope.

Notation "~" := CauchyEquiv : CauchyReal_scope.
Notation "r ~ s" := (<r, s> ∈ CauchyEquiv)
  (at level 10) : CauchyReal_scope.

Definition ℝ : set := (CauchySeq/~)%zfc.

End CauchyReal.

(** 戴德金分割 **)
Definition is_DedekindCut : set → Prop := λ x,
  (* a. 非平凡 *) (x ≠ ∅ ∧ x ≠ ℚ) ∧
  (* b. 向下封闭 *) (∀ p q ∈ ℚ, q ∈ x → p <𝐪 q → p ∈ x) ∧
  (* c. 无最大数 *) ∀p ∈ x, ∃q ∈ x, p <𝐪 q.

Definition ℝ : set := {x ∊ 𝒫 ℚ | is_DedekindCut}.

Lemma reals_sub_power_rat : ℝ ⊆ 𝒫 ℚ.
Proof. intros x Hx. apply SepE in Hx as []; auto. Qed.

Lemma real_sub_rat : ∀x ∈ ℝ, x ⊆ ℚ.
Proof.
  intros x Hx. apply reals_sub_power_rat in Hx.
  apply PowerAx in Hx. apply Hx.
Qed.

(* 左集存在有理数 *)
Lemma realE0 : ∀x ∈ ℝ, ∃r ∈ ℚ, r ∈ x.
Proof with auto.
  intros x Hx. apply real_sub_rat in Hx as Hsub.
  apply SepE in Hx as [_ [[H _] _]]. apply EmptyNE in H as [r Hr].
  exists r. split... apply Hsub...
Qed.

(* 右集也存在有理数 *)
Lemma realE1 : ∀x ∈ ℝ, ∃r ∈ ℚ, r ∉ x.
Proof with auto.
  intros x Hx.
  apply real_sub_rat in Hx as Hxsub.
  apply SepE in Hx as [_ [[_ H] _]].
  pose proof (comp_nonempty x ℚ) as [r Hr]. split...
  apply CompE in Hr as [Hrq Hrx]. exists r. split...
Qed.

(* 小于左集的都在左集 *)
Lemma realE2 : ∀x ∈ ℝ, ∀ p q ∈ ℚ, q ∈ x → p <𝐪 q → p ∈ x.
Proof. intros x Hx. apply SepE in Hx as [_ [_ [H _]]]. auto. Qed.

(* 左集里无最大 *)
Lemma realE3 : ∀x ∈ ℝ, ∀p ∈ x, ∃q ∈ ℚ, q ∈ x ∧ p <𝐪 q.
Proof with eauto.
  intros x Hx p Hp. assert (Hx' := Hx).
  apply SepE in Hx' as [_ [_ [_ H]]].
  apply H in Hp as [r [Hr Hqr]].
  exists r. split. eapply real_sub_rat... split...
Qed.

(* 右集的比左集的都大 *)
Lemma realE2_1 : ∀x ∈ ℝ, ∀ p q ∈ ℚ, p ∈ x → q ∉ x → p <𝐪 q.
Proof with auto.
  intros x Hx p Hp q Hq Hpx Hqx.
  destruct (classic (p = q)). subst. exfalso...
  apply ratLt_connected in H as []...
  apply realE2 in Hx. apply Hx in H... exfalso...
Qed.

(* 大于右集的都在右集 *)
Lemma realE2_2 : ∀x ∈ ℝ, ∀ p q ∈ ℚ, p ∉ x → p <𝐪 q → q ∉ x.
Proof with eauto.
  intros x Hx p Hp q Hq Hpx Hpq.
  destruct (classic (q ∈ x))... exfalso.
  eapply realE2 in H...
Qed.

(* 存在比左集的都大的（在右集） *)
Lemma realE1' : ∀x ∈ ℝ, ∃r ∈ ℚ, ∀q ∈ x, q <𝐪 r.
Proof with eauto.
  intros x Hx. assert (Hx' := Hx).
  apply realE1 in Hx' as [r [Hrq Hrx]].
  exists r. split... intros q Hq.
  eapply realE2_1... eapply real_sub_rat...
Qed.

Close Scope Rat_scope.
Open Scope Int_scope.

(** 实数的序 **)
Definition RealLt : set := SubsetRel ℝ.
Notation "x <𝐫 y" := (<x, y> ∈ RealLt) (at level 70).

Lemma realLt_connected : connected RealLt ℝ.
Proof with eauto.
  intros x Hx y Hy Hnq.
  destruct (classic (x ⊆ y)).
  left. apply binRelI...
  right. apply binRelI... split... intros q Hqy.
  rewrite sub_iff_no_comp in H. apply EmptyNE in H as [r Hr].
  apply CompE in Hr as [Hrx Hry].
  assert (Hrq: r ∈ ℚ) by (eapply real_sub_rat; revgoals; eauto).
  assert (Hqq: q ∈ ℚ) by (eapply real_sub_rat; revgoals; eauto).
  eapply realE2; revgoals... eapply realE2_1...
Qed.

Theorem realLt_linearOrder : linearOrder RealLt ℝ.
Proof.
  apply loset_iff_connected_poset. split.
  apply realLt_connected. apply subsetRel_poset.
Qed.

Lemma realLt_irrefl : irrefl RealLt.
Proof. eapply lo_irrefl. apply realLt_linearOrder. Qed.

Lemma realLt_tranr : tranr RealLt.
Proof. destruct realLt_linearOrder as [_ [H _]]. apply H. Qed.

Lemma realLt_trich : trich RealLt ℝ.
Proof. destruct realLt_linearOrder as [_ [_ H]]. apply H. Qed.

Close Scope Int_scope.
Declare Scope Real_scope.
Open Scope Real_scope.
Delimit Scope Real_scope with r.

Notation "x ≤ y" := (x <𝐫 y ∨ x = y) (at level 70) : Real_scope.

Lemma realLeqI : ∀ x y ∈ ℝ, x ⊆ y → x ≤ y.
Proof with auto.
  intros x Hx y Hy Hsub.
  destruct (classic (x = y))...
  left. apply binRelI...
Qed.

Lemma realLeqE : ∀ x y, x ≤ y → x ⊆ y.
Proof with auto.
  intros x y [Hlt|Heq].
  apply binRelE3 in Hlt as []...
  subst. apply sub_refl.
Qed.

Lemma realLeq : ∀ x y ∈ ℝ, x ≤ y ↔ x ⊆ y.
Proof with auto.
  intros x Hx y Hy. split. apply realLeqE. apply realLeqI...
Qed.

Lemma realLeq_tranr : ∀ x y z ∈ ℝ, x ≤ y → y ≤ z → x ≤ z.
Proof with eauto.
  intros x Hx y Hy z Hz H1 H2.
  apply realLeq in H1... apply realLeq in H2...
  apply realLeq... eapply sub_tran...
Qed.

Lemma union_reals_sub_rat : ∀ A, A ⊆ ℝ → ⋃A ∈ 𝒫 ℚ.
Proof with auto.
  intros A H1. pose proof reals_sub_power_rat as H2.
  assert (H3: A ⊆ 𝒫 ℚ) by (eapply sub_tran; eauto).
  apply ex2_4 in H3. rewrite ex2_6_a in H3. apply PowerAx...
Qed.

Lemma union_reals_sub_upperBound : ∀ A z,
  (∀x ∈ A, x ≤ z) → ⋃A ⊆ z.
Proof.
  intros A z Hle. apply ex2_5.
  intros x Hx. apply realLeqE. apply Hle. apply Hx.
Qed.

Lemma union_reals_boundedAbove_is_real : ∀ A,
  A ≠ ∅ → A ⊆ ℝ → boundedAbove A ℝ RealLt → ⋃A ∈ ℝ.
Proof with eauto.
  intros A Hne Hsub [z [Hz Hle]]. apply SepI.
  apply union_reals_sub_rat... repeat split.
  - apply EmptyNE in Hne as [x Hx]. apply Hsub in Hx as Hxr.
    apply realE0 in Hxr as [w [_ Hw]]. apply EmptyNI.
    exists w. apply UnionAx. exists x. split...
  - apply real_sub_rat in Hz as Hzsub.
    apply union_reals_sub_upperBound in Hle.
    intros Heq. rewrite Heq in Hle.
    apply SepE in Hz as [_ [[_ Hznq] _]].
    apply Hznq. apply sub_antisym...
  - intros p Hpq q Hqq Hq Hlt.
    apply UnionAx in Hq as [x [Hx Hq]].
    apply UnionAx. exists x. split...
    apply Hsub in Hx. apply realE2 in Hx. eapply Hx...
  - intros p Hp. apply UnionAx in Hp as [x [Hx Hp]].
    apply Hsub in Hx as Hxr. apply realE3 in Hp as [q [_ [Hq Hlt]]]...
    exists q. split... apply UnionAx. exists x. split...
Qed.

(** 实数的戴德金完备性（上确界性） **)
Theorem reals_boundedAbove_has_supremum : ∀ A,
  A ≠ ∅ → A ⊆ ℝ → boundedAbove A ℝ RealLt →
  ∃ s, supremum s A ℝ RealLt.
Proof with eauto.
  intros A Hne Hsub Hbnd.
  apply union_reals_boundedAbove_is_real in Hbnd as Hur...
  exists (⋃A). split.
  - repeat split...
    intros x Hxa. apply realLeq... apply Hsub... apply ex2_3...
  - intros y Hub. apply realLeqI... apply Hub.
    apply union_reals_sub_upperBound... apply Hub.
Qed.

Close Scope Real_scope.
Open Scope Int_scope.

Lemma ω_embeddable : ∀a ∈ ℤ, Int 0 ≤ a ↔ ∃n ∈ ω, a = ω_Embed[n].
Proof with nauto.
  intros a Ha. split.
  - intros [Hpa|H0]. 
    + apply intPos_natPos in Hpa as [m [Hm [Heq _]]]...
      exists m. split... rewrite ω_embed_n...
    + exists 0. split... rewrite ω_embed_n...
  - intros [n [Hn Heq]]. subst a. rewrite ω_embed_n...
    destruct (classic (n = ∅)). right. subst...
    apply nat_connected in H as []... exfalso0.
    left. apply intLt... rewrite add_ident, add_ident...
Qed.

(* 整数的向上封闭的非空子集具有良序性 *)
Lemma ints_boundedBelow_has_min : ∀ A,
  A ≠ ∅ → A ⊆ ℤ → boundedBelow A ℤ IntLt →
  ∃a ∈ A, ∀b ∈ A, a ≤ b.
Proof with auto.
  intros A Hne Hsub [b [Hbz Hle]].
  set {λ a, a - b | a ∊ A} as A'.
  set {n ∊ ω | λ n, ω_Embed[n] ∈ A'} as N.
  assert (Hnb: -b ∈ ℤ) by (apply intAddInv_ran; auto).
  assert (Hnn: ∀a' ∈ A', Int 0 ≤ a'). {
    intros a' Ha'. apply ReplAx in Ha' as [a [Ha Heq]]. subst a'.
    apply Hsub in Ha as Haz. apply Hle in Ha as [].
    - left. rewrite <- (intAddInv_annih b)...
      apply intAdd_preserve_lt...
    - right. rewrite H, intAddInv_annih...
  }
  assert (HA': ∀a ∈ A, a - b ∈ A'). {
    intros a Ha. apply ReplAx. exists a. split...
  }
  assert (Hemb: ∀a ∈ A, ∃n ∈ ω, a - b = ω_Embed[n]). {
    intros a Ha. apply Hsub in Ha as Haz. apply ω_embeddable.
    apply intAdd_ran... apply Hnn. apply HA'...
  }
  assert (H0: ⦿ N). {
    apply EmptyNE in Hne as [c Hc]. assert (Hc' := Hc).
    apply Hemb in Hc' as [k [Hk Heqk]]...
    exists k. apply SepI... rewrite <- Heqk... apply HA'...
  }
  assert (H1: N ⊆ ω). {
    intros n Hn. apply SepE1 in Hn...
  }
  apply ω_well_ordered in H1 as [m [Hm Hmin]]...
  apply SepE in Hm as [Hmw Hm].
  assert (Hmz: ω_Embed[m] ∈ ℤ) by (apply ω_embed_ran; auto).
  exists (ω_Embed[m] + b). split.
  - apply ReplAx in Hm as [a [Ha Heq]]. apply Hsub in Ha as Haz.
    assert (Heqa: a - b + b = ω_Embed[m] + b) by congruence.
    rewrite <- Heqa, intAdd_assoc, (intAdd_comm (-b)),
      intAddInv_annih, intAdd_ident...
  - intros c Hc. apply Hsub in Hc as Hcz.
    apply HA' in Hc as Hcb. apply Hemb in Hc as [n [Hnw Heq]].
    eapply intAdd_preserve_leq. apply intAdd_ran... auto. apply Hnb.
    rewrite intAdd_assoc, intAddInv_annih, intAdd_ident, Heq...
    assert (Hn: n ∈ N) by (apply SepI; congruence).
    apply Hmin in Hn as [].
    left. apply ω_embed_lt in H... right. congruence.
Qed.

Corollary ints_boundedBelow_has_min' : ∀ A,
  A ≠ ∅ → A ⊆ ℤ → boundedBelow A ℤ IntLt →
  ∃a ∈ A, (a - Int 1) ∉ A.
Proof with neauto.
  intros A Hne Hsub Hlow.
  pose proof ints_boundedBelow_has_min as [a [Ha Hmin]]...
  apply Hsub in Ha as Haz. exists a. split...
  destruct (classic (a - Int 1 ∈ A))... exfalso.
  apply Hmin in H. eapply intAdd_preserve_leq in H; revgoals.
  apply (int_n 1). apply intAdd_ran... auto.
  rewrite intAdd_assoc, (intAdd_comm (-Int 1)),
    intAddInv_annih, intAdd_ident in H...
  apply intLt_iff_leq_suc in H... eapply intLt_irrefl...
Qed.

Close Scope Int_scope.
Open Scope Rat_scope.

Lemma ex5_19 : ∀x ∈ ℝ, ∀p ∈ ℚ, ratPos p →
  ∃q ∈ ℚ, q ∈ x ∧ p + q ∉ x.
Proof with neauto.
  intros x Hx p Hp Hpp.
  pose proof (realE0 x Hx) as [r [Hrq Hrx]].
  pose proof (realE1 x Hx) as [s [Hsq Hsx]].
  pose proof (ex5_18_2 p Hp r Hrq Hpp) as [b [Hb Hlo]].
  pose proof (ex5_18_1 p Hp s Hsq Hpp) as [d [Hd Hup]].
  assert (Hbq: IntEmbed[b] ∈ ℚ) by (apply intEmbed_ran; auto).
  assert (Hdq: IntEmbed[d] ∈ ℚ) by (apply intEmbed_ran; auto).
  set {a ∊ ℤ | λ a, p ⋅ IntEmbed[a] ∉ x} as A.
  pose proof (ints_boundedBelow_has_min' A) as [c [Hc Hc']].
  - apply EmptyNI. exists d. apply SepI...
    eapply realE2_2; revgoals... apply ratMul_ran...
  - intros a Ha. apply SepE1 in Ha...
  - exists b. split... 
    intros a Ha. apply SepE in Ha as [Haz Hax].
    assert (Haq: IntEmbed[a] ∈ ℚ) by (apply intEmbed_ran; auto).
    destruct (classic (a = b)). right... left.
    apply intLt_connected in H as [Hlt|]... exfalso.
    apply intEmbed_lt in Hlt...
    apply (ratMul_preserve_lt' _ Haq _ Hbq p) in Hlt...
    assert (p ⋅ IntEmbed [a] <𝐪 r) by (eapply ratLt_tranr; eauto).
    apply Hax. eapply realE2; revgoals... apply ratMul_ran...
  - apply SepE in Hc as [Hcz Hleft].
    assert (Hc'z: (c - Int 1)%z ∈ ℤ) by (apply intAdd_ran; nauto).
    exists (p ⋅ IntEmbed[(c - Int 1)%z]). repeat split.
    + apply ratMul_ran... apply intEmbed_ran...
    + destruct (classic (p ⋅ IntEmbed[(c - Int 1)%z] ∈ x))...
      exfalso. apply Hc'. apply SepI...
    + assert (Hcq: IntEmbed[c] ∈ ℚ) by (apply intEmbed_ran; auto).
      assert (Hpcq: p ⋅ IntEmbed[c] ∈ ℚ) by (apply ratMul_ran; auto).
      assert (Hnp: -p ∈ ℚ) by (apply ratAddInv_ran; auto).
      assert (Hemb: IntEmbed [(- Int 1)%z] ∈ ℚ) by (apply intEmbed_ran; nauto).
      assert (Hadd: p ⋅ IntEmbed [c] - p ∈ ℚ) by (apply ratAdd_ran; nauto).
      rewrite intEmbed_add, ratMul_distr, intEmbed_addInv,
        ratMul_addInv_r, <- intEmbed_a, intEmbed, ratMul_ident,
        ratAdd_comm, ratAdd_assoc, (ratAdd_comm (-p)),
        ratAddInv_annih, ratAdd_ident; [auto|nauto..].
Qed.

Close Scope Rat_scope.
Open Scope Real_scope.

(** 实数加法 **)
Definition RealAdd : set → set → set := λ x y,
  {λ p, (π1 p + π2 p)%q | p ∊ x × y}.
Notation "x + y" := (RealAdd x y) : Real_scope.

Lemma realAddI1 : ∀ p, ∀ x y ∈ ℝ,
  ∀q ∈ x, ∀r ∈ y, (q + r)%q = p → p ∈ x + y.
Proof with auto.
  intros p x Hx y Hy q Hqx r Hry Heq.
  apply ReplAx. exists <q, r>. split.
  apply CProdI... zfc_simple.
Qed.

Lemma realAddI2 : ∀ x y ∈ ℝ,
  ∀q ∈ x, ∀r ∈ y, (q + r)%q ∈ x + y.
Proof with auto.
  intros x Hx y Hy q Hqx r Hry.
  apply ReplAx. exists <q, r>. split.
  apply CProdI... zfc_simple.
Qed.

Lemma realAddE : ∀ x y ∈ ℝ, ∀q ∈ x + y,
  ∃ r s ∈ ℚ, (r ∈ x ∧ s ∈ y) ∧ (r + s)%q = q.
Proof with eauto.
  intros x Hx y Hy q Hq.
  apply ReplAx in Hq as [t [Ht Heq]].
  apply CProdE1 in Ht as [r [Hr [s [Hs Ht]]]].
  exists r. split. eapply real_sub_rat; revgoals...
  exists s. split. eapply real_sub_rat; revgoals...
  subst. zfc_simple. split...
Qed.

Lemma realAdd_sub_rat : ∀ x y ∈ ℝ, x + y ∈ 𝒫 ℚ.
Proof with auto.
  intros x Hx y Hy. apply PowerAx. intros s Hs.
  apply ReplAx in Hs as [p [Hp Hs]].
  apply CProdE1 in Hp as [q [Hq [r [Hr Hp]]]].
  subst. zfc_simple. apply ratAdd_ran.
  apply (real_sub_rat _ Hx)... apply (real_sub_rat _ Hy)...
Qed.

Lemma realAdd_ran : ∀ x y ∈ ℝ, x + y ∈ ℝ.
Proof with eauto.
  intros x Hx y Hy.
  apply SepI. apply realAdd_sub_rat... repeat split.
  - apply realE0 in Hx as [q [_ Hq]].
    apply realE0 in Hy as [r [_ Hr]].
    apply EmptyNI. exists (q + r)%q. apply ReplAx.
    exists <q, r>. split. apply CProdI... zfc_simple.
  - assert (Hx' := Hx). assert (Hy' := Hy).
    apply realE1' in Hx' as [q [Hq H1]]...
    apply realE1' in Hy' as [r [Hr H2]]...
    assert (Hqr : (q + r)%q ∈ ℚ) by (apply ratAdd_ran; auto).
    apply ExtNI. exists (q + r)%q. split... intros H.
    apply (ratLt_irrefl (q + r)%q)...
    cut (∀p ∈ x + y, p <𝐪 (q + r)%q). intros Hlt. apply Hlt...
    intros p Hp. apply realAddE in Hp
      as [s [Hs [t [Ht [[Hsx Hty] Hst]]]]]... subst.
    eapply ratAdd_preserve_lt_tran... apply H1... apply H2...
  - intros p Hp s Hs H Hlt. apply realAddE in H
      as [q [Hq [r [Hr [[Hqx Hry] Hqr]]]]]... subst s.
    assert (Hnq: (-q)%q ∈ ℚ) by (apply ratAddInv_ran; auto).
    eapply ratAdd_preserve_lt in Hlt;
      try assumption; revgoals. apply Hnq.
    rewrite ratAdd_assoc, (ratAdd_comm r),
      <- ratAdd_assoc, ratAddInv_annih, ratAdd_ident' in Hlt...
    cut ((p - q)%q ∈ y). intros Hd.
    cut ((q + (p - q))%q = p). intros Heq.
    + eapply realAddI1; revgoals...
    + rewrite (ratAdd_comm p), <- ratAdd_assoc,
        ratAddInv_annih, ratAdd_ident'...
    + eapply realE2; revgoals... apply ratAdd_ran...
  - intros p Hp. apply realAddE in Hp
      as [q [Hq [r [Hr [[Hqx Hry] Hqr]]]]]... subst.
    apply realE3 in Hx as Hx3. apply Hx3 in Hqx as [s [_ [Hs H1]]].
    apply realE3 in Hy as Hy3. apply Hy3 in Hry as [t [_ [Ht H2]]].
    exists (s + t)%q. split. apply realAddI2...
    apply ratAdd_preserve_lt_tran; auto;
      eapply real_sub_rat; revgoals...
Qed.

Theorem realAdd_comm : ∀ x y ∈ ℝ, x + y = y + x.
Proof with auto.
  intros x Hx y Hy.
  apply ExtAx. intros p. split; intros Hp.
  - apply realAddE in Hp as [q [Hq [r [Hr [[Hqx Hry] Hqr]]]]]...
    subst. rewrite (ratAdd_comm)... apply realAddI2...
  - apply realAddE in Hp as [q [Hq [r [Hr [[Hqx Hry] Hqr]]]]]...
    subst. rewrite (ratAdd_comm)... apply realAddI2...
Qed.

Theorem realAdd_assoc : ∀ x y z ∈ ℝ, (x + y) + z = x + (y + z).
Proof with auto.
  intros x Hx y Hy z Hz.
  assert (Hxy: x + y ∈ ℝ) by (apply realAdd_ran; auto).
  assert (Hyz: y + z ∈ ℝ) by (apply realAdd_ran; auto).
  apply ExtAx. intros p. split; intros Hp.
  - apply realAddE in Hp as [q [Hq [r [Hr [[Hqx Hry] Hqr]]]]]...
    apply realAddE in Hqx as [s [Hs [t [Ht [[Hsx Hty] Hst]]]]]...
    subst. rewrite ratAdd_assoc...
    apply realAddI2... apply realAddI2...
  - apply realAddE in Hp as [q [Hq [r [Hr [[Hqx Hry] Hqr]]]]]...
    apply realAddE in Hry as [s [Hs [t [Ht [[Hsx Hty] Hst]]]]]...
    subst. rewrite <- ratAdd_assoc...
    apply realAddI2... apply realAddI2...
Qed.

Definition Realq: set → set := λ q, {r ∊ ℚ | λ r, r <𝐪 q}.
Definition Real : nat → set := λ n, Realq (Rat n).

Lemma real_q : ∀q ∈ ℚ, Realq q ∈ ℝ.
Proof with neauto.
  intros q Hq. assert (Hsubq: Realq q ⊆ ℚ). {
    intros r Hr. apply SepE1 in Hr...
  }
  apply SepI. apply PowerAx... repeat split.
  - pose proof (rat_archimedean' _ Hq) as [r [Hr Hlt]].
    apply EmptyNI. exists r. apply SepI...
  - apply ExtNI. exists q. split...
    intros H. apply SepE in H as [_ H].
    eapply ratLt_irrefl...
  - intros s Hs t Ht Htq Hlt. apply SepE in Htq as [_ Htq].
    apply SepI... eapply ratLt_tranr...
  - intros s Hsq. apply SepE in Hsq as [Hs Hsq].
    apply rat_dense in Hsq as [r [Hr [Hsr Hrq]]]...
    exists r. split... apply SepI...
Qed.

Corollary real_n : ∀ n, Real n ∈ ℝ.
Proof. intros. apply real_q; nauto. Qed.
Global Hint Immediate real_n : number_hint.

Theorem realAdd_ident : ∀ x ∈ ℝ, x + Real 0 = x.
Proof with nauto.
  intros x Hx. apply ExtAx. intros p. split; intros Hp.
  - apply realAddE in Hp as [q [Hq [r [Hr [[Hqx Hr0] Hqr]]]]]...
    subst. apply SepE in Hr0 as [_ Hr0].
    eapply realE2; revgoals; eauto; revgoals. apply ratAdd_ran...
    rewrite <- (ratAdd_ident q) at 2...
    apply ratAdd_preserve_lt'... 
  - apply real_sub_rat in Hp as Hpq... assert (Hp' := Hp).
    apply realE3 in Hp' as [r [Hrq [Hr Hpr]]]...
    assert (Hnrq : (-r)%q ∈ ℚ) by (apply ratAddInv_ran; auto).
    eapply realAddI1... apply Hr. apply SepI.
    eapply ratAdd_ran. apply Hpq. apply Hnrq.
    rewrite (ratAdd_preserve_lt p Hpq r Hrq _ Hnrq) in Hpr.
    rewrite ratAddInv_annih in Hpr... rewrite (ratAdd_comm p),
      <- ratAdd_assoc, ratAddInv_annih, ratAdd_ident'...
Qed.

Corollary realAdd_ident' : ∀ x ∈ ℝ, Real 0 + x = x.
Proof with nauto.
  intros x Hx. rewrite realAdd_comm, realAdd_ident...
Qed.

(** 实数加法逆元 **)
Definition RealAddInv : set → set := λ x,
  {r ∊ ℚ | λ r, ∃s ∈ ℚ, r <𝐪 s ∧ (-s)%q ∉ x}.
Notation "- x" := (RealAddInv x) : Real_scope.
Notation "x - y" := (x + (-y)) : Real_scope.

Lemma realAddInv_sub_rat : ∀x ∈ ℝ, -x ∈ 𝒫 ℚ.
Proof with auto.
  intros x Hx. apply PowerAx. intros p Hp.
  apply SepE1 in Hp...
Qed.

Theorem realAddInv_ran : ∀x ∈ ℝ, -x ∈ ℝ.
Proof with neauto.
  intros x Hx. apply SepI.
  apply realAddInv_sub_rat... repeat split.
  - pose proof (realE1 _ Hx) as [t [Htq Htx]].
    assert (Hntq : (-t)%q ∈ ℚ) by (apply ratAddInv_ran; auto).
    pose proof (rat_archimedean' _ Hntq) as [s [Hsq Hsnt]].
    apply EmptyNI. exists s. apply SepI... exists (-t)%q.
    repeat split... rewrite ratAddInv_double...
  - pose proof (realE0 _ Hx) as [p [Hp Hpx]]. apply ExtNI.
    assert (Hnpq : (-p)%q ∈ ℚ) by (apply ratAddInv_ran; auto).
    exists (-p)%q. split... intros H.
    apply SepE in H as [_ [s [Hsq [Hlt Hsx]]]].
    assert (Hnsq : (-s)%q ∈ ℚ) by (apply ratAddInv_ran; auto).
    apply Hsx. clear Hsx. cut ((-s)%q <𝐪 p). intros Hlt'.
    eapply realE2; revgoals; [apply Hlt'|..]; try assumption.
    rewrite (ratAdd_preserve_lt _ Hnpq _ Hsq _ Hp) in Hlt.
    rewrite ratAdd_comm, ratAddInv_annih,
      <- (ratAddInv_annih s) in Hlt; try assumption.
    apply ratAdd_preserve_lt' in Hlt; try assumption.
  - intros p Hp q Hq Hqx Hpq.
    apply SepE in Hqx as [_ [s [Hs [Hqs Hsx]]]]. apply SepI...
    exists s. split... split... eapply ratLt_tranr...
  - intros p Hp. apply SepE in Hp as [Hp [s [Hs [Hps Hsx]]]].
    apply rat_dense in Hps as [r [Hr [Hpr Hrs]]]...
    exists r. split... apply SepI... exists s. split...
Qed.

Lemma ratLt_r2_1 : (Rat 2)⁻¹%q <𝐪 Rat 1.
Proof with nauto.
  unfold Rat.
  rewrite ratMulInv... apply ratLt...
  rewrite intMul_ident', intMul_ident'...
  apply intLt... rewrite add_ident, add_ident, (pred 2)...
Qed.

Theorem realAddInv_annih : ∀x ∈ ℝ, x - x = Real 0.
Proof with neauto.
  intros x Hx.
  assert (Hnx: -x ∈ ℝ) by (apply realAddInv_ran; auto).
  apply ExtAx. intros p. split; intros Hp.
  - apply realAddE in Hp as [q [Hq [r [Hr [[Hqx Hrx] Heq]]]]]...
    apply SepE in Hrx as [_ [s [Hs [Hrs Hsx]]]].
    subst p. apply SepI. apply ratAdd_ran...
    rewrite ratAdd_comm, <- (ratAddInv_annih s)...
    Close Scope Real_scope. Open Scope Rat_scope.
    assert (Hns: -s ∈ ℚ) by (apply ratAddInv_ran; auto).
    apply ratAdd_preserve_lt_tran...
    eapply realE2_1; revgoals...
  - apply SepE in Hp as [Hp Hnp]. apply ratNeg_pos in Hnp.
    assert (Hnpq: -p ∈ ℚ) by (apply ratAddInv_ran; auto).
    assert (H2q: p / Rat 2 ∈ ℚ) by (apply ratMul_ran; nauto).
    assert (Hp2: ratPos (-p / Rat 2))
      by (eapply ratMul_pos_prod; neauto).
    apply (ex5_19 x) in Hp2 as [q [Hqq [Hq Hleft]]];
      [|auto|apply ratMul_ran; nauto].
    assert (Hnqq: -q ∈ ℚ) by (apply ratAddInv_ran; auto).
    assert (Heq: q + (p - q) = p). {
      rewrite (ratAdd_comm p), <- ratAdd_assoc,
        ratAddInv_annih, ratAdd_ident'; auto.
    }
    eapply realAddI1... apply SepI.
    apply ratAdd_ran; try assumption.
    exists (p / Rat 2 - q). split.
    apply ratAdd_ran; try assumption. split.
    + apply ratAdd_preserve_lt; try assumption.
      apply ratLt_addInv...
      rewrite <- ratMul_addInv_l...
      rewrite <- (ratMul_ident (-p)) at 2; try assumption.
      apply ratMul_preserve_lt'; try assumption...
      apply ratLt_r2_1.
    + rewrite ratAddInv_diff, ratAdd_comm, <- ratMul_addInv_l...
      apply ratAddInv_ran...
Qed.

Close Scope Rat_scope.
Open Scope Real_scope.

Corollary realAddInv_double : ∀x ∈ ℝ, --x = x.
Proof with auto.
  intros x Hx.
  assert (Hn: -x ∈ ℝ) by (apply realAddInv_ran; auto).
  assert (Hnn: --x ∈ ℝ) by (apply realAddInv_ran; auto).
  rewrite <- (realAdd_ident (--x)), <- (realAddInv_annih x),
    realAdd_comm, realAdd_assoc, realAddInv_annih, realAdd_ident...
  apply realAdd_ran...
Qed.

Corollary realAdd_cancel : ∀ x y z ∈ ℝ, x + z = y + z → x = y.
Proof with auto.
  intros x Hx y Hy z Hz Heq.
  assert (x + z - z = y + z - z) by congruence.
  rewrite realAdd_assoc, (realAdd_assoc y) in H...
  rewrite realAddInv_annih, realAdd_ident, realAdd_ident in H...
  apply realAddInv_ran... apply realAddInv_ran...
Qed.

Corollary realAdd_cancel' : ∀ x y z ∈ ℝ, z + x = z + y → x = y.
Proof with eauto.
  intros x Hx y Hy z Hz Heq.
  eapply realAdd_cancel...
  rewrite realAdd_comm, (realAdd_comm y)...
Qed.

Corollary realAddInv_0 : -Real 0 = Real 0.
Proof with nauto.
  eapply realAdd_cancel.
  apply realAddInv_ran... nauto. apply (real_n 0).
  rewrite realAdd_comm, realAddInv_annih, realAdd_ident...
  apply realAddInv_ran...
Qed.

Corollary realAddInv_eq_0 : ∀x ∈ ℝ, -x = Real 0 → x = Real 0.
Proof with auto.
  intros x Hx Hnx0. rewrite <- realAddInv_double, Hnx0, realAddInv_0...
Qed.

Lemma realAddInv_sum : ∀ x y ∈ ℝ, -(x + y) = -x - y.
Proof with nauto.
  intros x Hx y Hy.
  assert (Hsum: x + y ∈ ℝ) by (apply realAdd_ran; auto).
  assert (Hnx: -x ∈ ℝ) by (apply realAddInv_ran; auto).
  assert (Hny: -y ∈ ℝ) by (apply realAddInv_ran; auto).
  assert (Real 0 = Real 0) by auto.
  rewrite <- realAdd_ident in H at 2...
  rewrite <- (realAddInv_annih (x + y)) in H at 1...
  rewrite <- (realAddInv_annih x) in H at 1...
  rewrite <- (realAddInv_annih y) in H...
  rewrite <- (realAdd_assoc (x - x)), (realAdd_assoc x Hx (-x)),
    (realAdd_comm (-x)), <- realAdd_assoc, (realAdd_assoc (x + y)) in H...
  apply realAdd_cancel' in H... apply realAddInv_ran...
  apply realAdd_ran... apply realAdd_ran...
Qed.

Lemma realAddInv_diff : ∀ x y ∈ ℝ, -(x - y) = y - x.
Proof with auto.
  intros x Hx y Hy. rewrite realAddInv_sum, realAddInv_double,
    realAdd_comm; auto; apply realAddInv_ran...
Qed.

Theorem realAdd_preserve_leq : ∀ x y z ∈ ℝ,
  x ≤ y → x + z ≤ y + z.
Proof with eauto.
  intros x Hx y Hy z Hz Hleq.
  apply realLeqE in Hleq. apply realLeqI.
  apply realAdd_ran... apply realAdd_ran...
  intros p Hp. apply realAddE in Hp
    as [q [Hq [r [Hr [[Hqx Hrz] Heq]]]]]...
  eapply realAddI1... apply Hleq...
Qed.

Theorem realAdd_preserve_lt : ∀ x y z ∈ ℝ,
  x <𝐫 y → x + z <𝐫 y + z.
Proof with eauto.
  intros x Hx y Hy z Hz Hlt.
  destruct (classic (x = y)).
  - exfalso. subst. eapply realLt_irrefl...
  - assert (Hleq: x ≤ y) by auto.
    apply (realAdd_preserve_leq _ Hx _ Hy _ Hz) in Hleq as []...
    exfalso. apply H. eapply realAdd_cancel...
Qed.

Theorem realSubtr_preserve_lt : ∀ x y z ∈ ℝ,
  x + z <𝐫 y + z → x <𝐫 y.
Proof with eauto.
  intros x Hx y Hy z Hz Hlt.
  destruct (classic (x = y)). subst. exfalso.
  eapply realLt_irrefl...
  apply realLt_connected in H as []... exfalso.
  eapply realAdd_preserve_lt in H...
  eapply realLt_irrefl. eapply realLt_tranr...
Qed.

Theorem realSubtr_preserve_leq : ∀ x y z ∈ ℝ,
  x + z ≤ y + z → x ≤ y.
Proof with eauto.
  intros x Hx y Hy z Hz [].
  left. apply realSubtr_preserve_lt in H...
  right. apply realAdd_cancel in H...
Qed.

Corollary realAdd_preserve_leq_tran : ∀ w x y z ∈ ℝ,
  w ≤ x → y ≤ z → w + y ≤ x + z.
Proof with auto.
  intros w Hw x Hx y Hy z Hz H1 H2.
  apply (realAdd_preserve_leq w Hw x Hx y Hy) in H1...
  apply (realAdd_preserve_leq y Hy z Hz x Hx) in H2...
  rewrite (realAdd_comm y), (realAdd_comm z) in H2...
  eapply realLeq_tranr; revgoals; eauto; apply realAdd_ran...
Qed.

Corollary realAdd_preserve_lt_tran : ∀ w x y z ∈ ℝ,
  w <𝐫 x → y <𝐫 z → w + y <𝐫 x + z.
Proof with auto.
  intros w Hw x Hx y Hy z Hz H1 H2.
  apply (realAdd_preserve_lt w Hw x Hx y Hy) in H1...
  apply (realAdd_preserve_lt y Hy z Hz x Hx) in H2...
  rewrite (realAdd_comm y), (realAdd_comm z) in H2...
  eapply realLt_tranr; revgoals; eauto; apply realAdd_ran...
Qed.

Lemma realLt_addInv : ∀ x y ∈ ℝ, x <𝐫 y → -y <𝐫 -x.
Proof with auto.
  intros x Hx y Hy Hlt.
  apply binRelE3 in Hlt as [Hsub Hnq]. apply binRelI...
  apply realAddInv_ran... apply realAddInv_ran... split.
  - intros q Hq. apply SepE in Hq as [Hq [s [Hs [Hlt Hout]]]].
    apply SepI... exists s. repeat split...
    intros Hin. apply Hout. apply Hsub...
  - intros Heq. apply Hnq. assert (--y = --x) by congruence.
    rewrite realAddInv_double, realAddInv_double in H...
Qed.

Lemma realLt_addInv' : ∀ x y ∈ ℝ, -y <𝐫 -x → x <𝐫 y.
Proof with eauto.
  intros x Hx y Hy Hlt. destruct (classic (x = y)).
  - exfalso. subst.
    eapply realLt_irrefl...
  - apply realLt_connected in H as []...
    exfalso. apply realLt_addInv in H...
    eapply realLt_irrefl.
    eapply realLt_tranr; revgoals...
Qed.

Lemma realLeq_addInv : ∀ x y ∈ ℝ, x ≤ y → -y ≤ -x.
Proof with auto.
  intros x Hx y Hy [Hlt|Heq].
  - left. apply realLt_addInv...
  - right. congruence.
Qed.

Lemma realLeq_addInv' : ∀ x y ∈ ℝ, -y ≤ -x → x ≤ y.
Proof with eauto.
  intros x Hx y Hy [Hlt|Heq].
  - left. apply realLt_addInv'...
  - right. assert (--y = --x) by congruence.
    rewrite realAddInv_double, realAddInv_double in H...
Qed.

(* 更多关于实数的序的引理 *)

Lemma realLt_realq : ∀x ∈ ℝ, ∀q ∈ ℚ, Realq q <𝐫 x ↔ q ∈ x.
Proof with neauto.
  intros x Hx q Hq. split; intros.
  - apply binRelE2 in H as [H0 [_ [Hsub Hnq]]].
    destruct (classic (q ∈ x))... exfalso.
    apply Hnq. apply ExtAx. intros p. split; intros Hp.
    + apply Hsub in Hp as Hpx. apply SepE in Hp as [Hpq _].
      apply realE3 in Hpx as [r [Hrq [Hr Hlt]]]...
      eapply realE2; revgoals...
    + assert (Hpq: p ∈ ℚ) by (apply (real_sub_rat _ Hx); auto).
      apply SepI... eapply realE2_1; revgoals...
  - apply binRelI... apply real_q... split.
    + intros p Hp. apply SepE in Hp as [Hpq Hlt].
      eapply realE2; revgoals...
    + intros H0. subst. apply SepE in H as [_ H].
      eapply ratLt_irrefl...
Qed.

Corollary realLt_realn : ∀ n, ∀x ∈ ℝ, Real n <𝐫 x ↔ Rat n ∈ x.
Proof. intros n x Hx. apply realLt_realq; nauto. Qed.

Lemma realLt_realq' : ∀x ∈ ℝ, ∀q ∈ ℚ, x ≤ Realq q ↔ q ∉ x.
Proof with neauto.
  intros x Hx q Hq. split; intros.
  - intros Hqx. apply realLeq in H...
    apply H in Hqx. apply SepE in Hqx as [_ Hlt].
    eapply ratLt_irrefl... apply real_q...
  - apply realLeq... apply real_q... intros r Hr.
    assert (Hrq: r ∈ ℚ) by (apply (real_sub_rat _ Hx); auto).
    apply SepI... eapply realE2_1...
Qed.

Corollary realLt_realn' : ∀ n, ∀x ∈ ℝ, x ≤ Real n ↔ Rat n ∉ x.
Proof. intros n x Hx. apply realLt_realq'; nauto. Qed.

Definition realPos : set → Prop := λ x, Real 0 <𝐫 x.
Definition realNeg : set → Prop := λ x, x <𝐫 Real 0.

Lemma real_neq_0 : ∀x ∈ ℝ, realPos x ∨ realNeg x → x ≠ Real 0.
Proof.
  intros x Hx [Hpx|Hnx]; intros H; subst;
  eapply realLt_irrefl; eauto.
Qed.

Lemma realPos_rat0 : ∀x ∈ ℝ, realPos x ↔ Rat 0 ∈ x.
Proof. 
  intros x Hx. split; intros; apply (realLt_realn 0 _ Hx); auto.
Qed.

Lemma realPos_neg : ∀ x, realPos x → realNeg (-x).
Proof with neauto.
  intros. apply realLt_addInv in H... rewrite realAddInv_0 in H...
  apply binRelE2 in H as [_ [Hx _]]...
Qed.

Lemma realNeg_pos : ∀ x, realNeg x → realPos (-x).
Proof with nauto.
  intros. apply realLt_addInv in H... rewrite realAddInv_0 in H...
  apply binRelE2 in H as [Hx _]...
Qed.

Lemma real_suc_neq_0 : ∀ n, Real (S n) ≠ Real 0.
Proof with neauto.
  intros n H. rewrite ExtAx in H.
  assert (Rat 0 ∈ Real (S n)). {
    apply SepI... apply ratPos_sn.
  }
  apply H in H0. apply SepE in H0 as [_ H0].
  eapply ratLt_irrefl...
Qed.
Global Hint Immediate real_suc_neq_0 : number_hint.

Lemma realPos_sn : ∀ n, realPos (Real (S n)).
Proof with nauto.
  intros. apply binRelI... split.
  - intros p Hp. apply SepE in Hp as [Hpq Hlt].
    apply SepI... eapply ratLt_tranr. apply Hlt. apply ratPos_sn.
  - intros H. eapply real_suc_neq_0. rewrite H. reflexivity.
Qed.
Global Hint Immediate realPos_sn : number_hint.

Lemma realNeg_sn : ∀ n, realNeg (-Real (S n)).
Proof. intros. apply realPos_neg. nauto. Qed.
Global Hint Immediate realNeg_sn : number_hint.

Notation " x ≥ y " := (y ≤ x) (only parsing, at level 70): Real_scope.

Definition realNonNeg : set → Prop := λ x, x ≥ Real 0.
Definition realNonPos : set → Prop := λ x, x ≤ Real 0.

Lemma realNonNeg_nonPos : ∀x ∈ ℝ, realNonNeg x → realNonPos (-x).
Proof with nauto.
  intros x Hx [Hp|Hnq].
  - left. apply realLt_addInv in Hp...
    rewrite realAddInv_0 in Hp...
  - right. assert (-x = -Real 0) by congruence.
    rewrite realAddInv_0 in H...
Qed.

Lemma realNonPos_nonNeg : ∀x ∈ ℝ, realNonPos x → realNonNeg (-x).
Proof with nauto.
  intros x Hx [Hn|Hnq].
  - left. apply realLt_addInv in Hn...
    rewrite realAddInv_0 in Hn...
  - right. assert (-x = -Real 0) by congruence.
    rewrite realAddInv_0 in H...
Qed.

Lemma realPos_nonNeg : ∀ x ∈ ℝ, realPos x → realNonNeg x.
Proof with neauto.
  intros x Hx Hn. destruct (classic (x = Real 0)).
  exfalso. subst. eapply realLt_irrefl... left...
Qed.

Lemma realNeg_nonPos : ∀ x ∈ ℝ, realNeg x → realNonPos x.
Proof with neauto.
  intros x Hx Hn. destruct (classic (x = Real 0)).
  exfalso. subst. eapply realLt_irrefl... left...
Qed.

Lemma realNonNeg_not_neg : ∀x ∈ ℝ, ¬ realNeg x ↔ realNonNeg x.
Proof with neauto.
  intros x Hx. split; intros.
  - destruct (classic (realNonNeg x))... exfalso.
    apply not_or_and in H0 as [].
    apply realLt_connected in H1 as []...
  - intros Hn. destruct H.
    + eapply realLt_irrefl. eapply realLt_tranr...
    + subst. eapply realLt_irrefl...
Qed.

Lemma realNeg_not_nonNeg : ∀x ∈ ℝ, ¬ realNonNeg x ↔ realNeg x.
Proof with neauto.
  intros x Hx. split; intros.
  - destruct (classic (realNeg x))... exfalso.
    apply realNonNeg_not_neg in H0...
  - intros Hnn. eapply realNonNeg_not_neg...
Qed.

Lemma realNonPos_not_pos : ∀x ∈ ℝ, ¬ realPos x ↔ realNonPos x.
Proof with neauto.
  intros x Hx. split; intros.
  - destruct (classic (realNonPos x))... exfalso.
    apply not_or_and in H0 as [].
    apply realLt_connected in H1 as []...
  - intros Hp. destruct H.
    + eapply realLt_irrefl. eapply realLt_tranr...
    + subst. eapply realLt_irrefl...
Qed.

Lemma realPos_not_nonPos : ∀x ∈ ℝ, ¬ realNonPos x ↔ realPos x.
Proof with neauto.
  intros x Hx. split; intros.
  - destruct (classic (realPos x))... exfalso.
    apply realNonPos_not_pos in H0...
  - intros Hnp. eapply realNonPos_not_pos...
Qed.

Lemma realAdd_nonNeg_sum : ∀ x y ∈ ℝ,
  realNonNeg x → realNonNeg y → realNonNeg (x + y).
Proof with nauto.
  intros x Hx y Hy Hnnx Hnny.
  unfold realNonNeg. rewrite <- (realAdd_ident (Real 0))...
  apply realAdd_preserve_leq_tran...
Qed.

Lemma realAdd_neg_sum : ∀ x y ∈ ℝ,
  realNeg x → realNeg y → realNeg (x + y).
Proof with nauto.
  intros x Hx y Hy Hnnx Hnny. unfold realNeg.
  rewrite <- (realAdd_ident (Real 0))...
  apply realAdd_preserve_lt_tran...
Qed.
