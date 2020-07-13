(** Based on "Elements of Set Theory" Chapter 5 Part 5 **)
(** Coq coding by choukh, July 2020 **)

Require Export ZFC.CH5_1.

(*** EST第五章5：实数的定义(戴德金分割)，实数的序，实数的完备性，
  实数运算：加法，加法逆元，减法 ***)

(* 柯西序列 *)
Module CauchyReal.

Open Scope Rat_scope.

Definition CauchySeq : set :=
  {s ∊ ω ⟶ ℚ | λ s,
    ∀ε ∈ ℚ, ratPos ε → ∃k ∈ ω, ∀ m n ∈ ω, k ∈ m → k ∈ n →
    |s[m] - s[n]| <𝐪 ε
  }.

Definition CauchyEquiv : set :=
  Relation CauchySeq CauchySeq (λ r s,
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
  (* b. 向下封闭 *) (∀ p q ∈ ℚ, p <𝐪 q → q ∈ x → p ∈ x) ∧
  (* c. 无最大数 *) ∀p ∈ x, ∃q ∈ x, p <𝐪 q.

Definition ℝ : set := {x ∊ 𝒫 ℚ | is_DedekindCut}.

Lemma reals_sub_power_rat : ℝ ⊆ 𝒫 ℚ.
Proof. intros x Hx. apply SepE in Hx as []; auto. Qed.

Lemma real_sub_rat : ∀x ∈ ℝ, x ⊆ ℚ.
Proof.
  intros x Hx. apply reals_sub_power_rat in Hx.
  apply PowerAx in Hx. apply Hx.
Qed.

Lemma realE1 : ∀x ∈ ℝ, x ≠ ∅ ∧ x ≠ ℚ.
Proof. intros x Hx. apply SepE in Hx as [_ [H _]]. auto. Qed.

Lemma realE2 : ∀x ∈ ℝ, ∀ p q ∈ ℚ, p <𝐪 q → q ∈ x → p ∈ x.
Proof. intros x Hx. apply SepE in Hx as [_ [_ [H _]]]. auto. Qed.

Lemma realE3 : ∀x ∈ ℝ, ∀p ∈ x, ∃q ∈ x, p <𝐪 q.
Proof. intros x Hx. apply SepE in Hx as [_ [_ [_ H]]]. auto. Qed.

(** 实数的序 **)
Definition RealLt : set := Relation ℝ ℝ (λ x y, x ⊂ y).
Notation "x <𝐫 y" := (<x, y> ∈ RealLt) (at level 70).

Lemma realLtI : ∀ x y ∈ ℝ, x ⊂ y → x <𝐫 y.
Proof with auto.
  intros x Hx y Hy Hsub.
  apply SepI. apply CProdI... zfcrewrite.
Qed.

Lemma realLtE : ∀ x y, x <𝐫 y → x ∈ ℝ ∧ y ∈ ℝ ∧ x ⊂ y.
Proof with auto.
  intros * Hsub.
  apply SepE in Hsub as [H1 H2].
  apply CProdE1 in H1 as [Hx Hy]. zfcrewrite...
Qed.

Lemma realLt : ∀ x y ∈ ℝ, x <𝐫 y ↔ x ⊂ y.
Proof with auto.
  intros x Hx y Hy. split. apply realLtE. apply realLtI...
Qed.

Lemma realLt_rel : rel RealLt ℝ.
Proof with auto.
  intros x Hx. apply SepE in Hx as []...
Qed.

Lemma realLt_tranr : tranr RealLt.
Proof with eauto.
  intros x y z H1 H2.
  apply realLtE in H1 as [Hx [Hy [Hxy1 Hxy2]]].
  apply realLtE in H2 as [_  [Hz [Hyz1 Hyz2]]].
  apply realLtI... split. eapply sub_tran...
  intros Heq. subst x. apply Hyz2. apply sub_asym...
Qed.

Lemma realLt_irreflexive : irreflexive RealLt ℝ.
Proof with auto.
  intros [x [Hx Hlt]].
  apply realLt in Hlt as [Hsub Hnq]...
Qed.

Lemma realLt_connected : connected RealLt ℝ.
Proof with auto.
  intros x Hx y Hy Hnq.
  destruct (classic (x ⊆ y)).
  left. apply realLtI...
  right. apply realLtI... split... intros q Hqy.
  rewrite ch2_17_1_2 in H. apply EmptyNE in H as [r Hr].
  apply CompE in Hr as [Hrx Hry].
  assert (Hrq: r ∈ ℚ) by (eapply real_sub_rat; revgoals; eauto).
  assert (Hqq: q ∈ ℚ) by (eapply real_sub_rat; revgoals; eauto).
  destruct (classic (r = q)). subst. exfalso...
  apply ratLt_connected in H as []...
  apply realE2 in Hy. apply Hy in H... exfalso...
  apply realE2 in Hx. apply Hx in H...
Qed.

Lemma realLt_trich : trich RealLt ℝ.
Proof with auto.
  eapply trich_iff. apply realLt_rel. apply realLt_tranr. split.
  apply realLt_irreflexive. apply realLt_connected.
Qed.

Theorem realLt_totalOrd : totalOrd RealLt ℝ.
Proof with auto.
  split. apply realLt_rel. split. apply realLt_tranr.
  apply realLt_trich.
Qed.

Close Scope Int_scope.
Declare Scope Real_scope.
Open Scope Real_scope.
Delimit Scope Real_scope with r.

Notation "x ≤ y" := (x <𝐫 y ∨ x = y) (at level 70) : Real_scope.

Lemma realLeqI : ∀ x y ∈ ℝ, x ⊆ y → x ≤ y.
Proof with auto.
  intros x Hx y Hy Hsub.
  destruct (classic (x = y))...
  left. apply realLt...
Qed.

Lemma realLeqE : ∀ x y, x ≤ y → x ⊆ y.
Proof with auto.
  intros x y [Hlt|Heq].
  apply realLtE in Hlt as [_ [_ []]]...
  subst. apply sub_refl.
Qed.

Lemma realLeq : ∀ x y ∈ ℝ, x ≤ y ↔ x ⊆ y.
Proof with auto.
  intros x Hx y Hy. split. apply realLeqE. apply realLeqI...
Qed.

Definition upper : set → set → Prop :=
  λ A x, ∀y ∈ A, y ≤ x.

Definition bounded : set → Prop :=
  λ A, ∃ x, upper A x.

Definition sup : set → set → Prop :=
  λ A x, upper A x ∧ ∀ y, upper A y → x ≤ y.

Lemma union_reals_sub_rat : ∀ A, A ⊆ ℝ → ⋃A ∈ 𝒫 ℚ.
Proof with auto.
  intros A H1. pose proof reals_sub_power_rat as H2.
  assert (H3: A ⊆ 𝒫 ℚ) by (eapply sub_tran; eauto).
  apply ch2_4 in H3. rewrite ch2_6_a in H3. apply PowerAx...
Qed.

Lemma union_reals_sub_upper : ∀ A z, upper A z → ⋃A ⊆ z.
Proof.
  intros A z Hupz. apply ch2_5.
  intros x Hx. apply realLeqE. apply Hupz. apply Hx.
Qed.

Lemma reals_has_upper : ∀ A x,
  A ≠ ∅ → A ⊆ ℝ → upper A x → x ∈ ℝ.
Proof with auto.
  intros A x Hi Hsubr Hupx. apply EmptyNE in Hi as [a Ha].
  apply Hupx in Ha as Hleq. destruct Hleq as [Hlt|Heq].
  - apply realLtE in Hlt as [_ [Hx _]]...
  - subst. apply Hsubr...
Qed.

Lemma reals_bounded_has_union_reals : ∀ A,
  A ≠ ∅ → A ⊆ ℝ → bounded A → ⋃A ∈ ℝ.
Proof with eauto.
  intros A Hi Hsubr [z Hupz]. apply SepI.
  apply union_reals_sub_rat... repeat split...
  - apply EmptyNE in Hi as [x Hx]. apply Hsubr in Hx as Hxr.
    apply realE1 in Hxr as [Hxr _]. apply EmptyNE in Hxr as [w Hw].
    apply EmptyNI. exists w. apply UnionAx. exists x. split...
  - apply reals_has_upper in Hupz as Hz...
    apply real_sub_rat in Hz as Hzsub.
    apply realE1 in Hz as [_ Hznq].
    apply union_reals_sub_upper in Hupz.
    intros Heq. rewrite Heq in Hupz.
    apply Hznq. apply sub_asym...
  - intros p Hpq q Hqq Hlt Hq.
    apply UnionAx in Hq as [x [Hx Hq]].
    apply UnionAx. exists x. split...
    apply Hsubr in Hx. apply realE2 in Hx. eapply Hx...
  - intros p Hp. apply UnionAx in Hp as [x [Hx Hp]].
    apply Hsubr in Hx as Hxr. apply realE3 in Hp as [q [Hq Hlt]]...
    exists q. split... apply UnionAx. exists x. split...
Qed.

(** 戴德金完备性（上确界性） **)
Theorem reals_bounded_has_sup : ∀ A,
  A ≠ ∅ → A ⊆ ℝ → bounded A → ∃ s, sup A s.
Proof with eauto.
  intros A Hi Hsubr Hbnd.
  apply reals_bounded_has_union_reals in Hbnd as Huar...
  exists (⋃A). split.
  - intros x Hxa. apply realLeq...
    apply Hsubr... apply ch2_3...
  - intros y Hupy. apply realLeqI...
    eapply reals_has_upper... apply union_reals_sub_upper...
Qed.

(** 实数加法 **)
Definition RealAdd : set → set → set := λ x y,
  {λ p, (π1 p + π2 p)%q | p ∊ x × y}.
Notation "x + y" := (RealAdd x y) : Real_scope.

Lemma realAddI1 : ∀ p, ∀ x y ∈ ℝ,
  ∀q ∈ x, ∀r ∈ y, (q + r)%q = p → p ∈ x + y.
Proof with auto.
  intros p x Hx y Hy q Hqx r Hry Heq.
  apply ReplAx. exists <q, r>. split.
  apply CProdI... zfcrewrite.
Qed.

Lemma realAddI2 : ∀ x y ∈ ℝ,
  ∀q ∈ x, ∀r ∈ y, (q + r)%q ∈ x + y.
Proof with auto.
  intros x Hx y Hy q Hqx r Hry.
  apply ReplAx. exists <q, r>. split.
  apply CProdI... zfcrewrite.
Qed.

Lemma realAddE : ∀ x y ∈ ℝ, ∀z ∈ x + y,
  ∃ q r ∈ ℚ, (q ∈ x ∧ r ∈ y) ∧ (q + r)%q = z.
Proof with eauto.
  intros x Hx y Hy z Hz. assert (Hz' := Hz).
  apply ReplE in Hz' as [s [Hs Heq]].
  apply CProd_correct in Hs as [q [Hq [r [Hr Hs]]]].
  exists q. split. eapply real_sub_rat; revgoals...
  exists r. split. eapply real_sub_rat; revgoals...
  subst. zfcrewrite. split...
Qed.

Lemma realAdd_sub_rat : ∀ x y ∈ ℝ, x + y ∈ 𝒫 ℚ.
Proof with auto.
  intros x Hx y Hy. apply PowerAx. intros s Hs.
  apply ReplAx in Hs as [p [Hp Hs]].
  apply CProd_correct in Hp as [q [Hq [r [Hr Hp]]]].
  subst. zfcrewrite. apply ratAdd_ran.
  apply real_sub_rat in Hx. apply Hx...
  apply real_sub_rat in Hy. apply Hy...
Qed.

Lemma comp_inh : ∀ a A, a ⊂ A → ⦿ (A - a)%zfc.
Proof with auto.
  intros * [Hsub Hnq]. apply EmptyNE.
  intros H0. apply ch2_17_1_2 in H0.
  apply Hnq. apply sub_asym...
Qed.

Lemma ex_rat_gt_in_real : ∀x ∈ ℝ, ∃r ∈ ℚ, ∀q ∈ x, q <𝐪 r.
Proof with auto.
  intros x Hx. assert (Hx' := Hx).
  apply real_sub_rat in Hx as Hxsub.
  apply realE1 in Hx' as [_ Hxnq].
  pose proof (comp_inh x ℚ) as [r Hr]. split...
  apply CompE in Hr as [Hrq Hrx].
  exists r. split... intros q Hq.
  apply real_sub_rat in Hx as Hxq. apply Hxq in Hq as Hqq.
  destruct (classic (q = r)). subst. exfalso...
  apply ratLt_connected in H as []... exfalso.
  eapply realE2 in Hq; eauto.
Qed.

Lemma realAdd_ran : ∀ x y ∈ ℝ, x + y ∈ ℝ.
Proof with eauto.
  intros x Hx y Hy.
  apply SepI. apply realAdd_sub_rat... repeat split...
  - apply realE1 in Hx as [Hx0 _]. apply EmptyNE in Hx0 as [q Hq].
    apply realE1 in Hy as [Hy0 _]. apply EmptyNE in Hy0 as [r Hr].
    apply EmptyNI. exists (q + r)%q. apply ReplAx.
    exists <q, r>. split. apply CProdI... zfcrewrite.
  - assert (Hx' := Hx). assert (Hy' := Hy).
    apply ex_rat_gt_in_real in Hx' as [q [Hq H1]]...
    apply ex_rat_gt_in_real in Hy' as [r [Hr H2]]...
    assert (Hqr : (q + r)%q ∈ ℚ) by (apply ratAdd_ran; auto).
    intros Hext. rewrite ExtAx in Hext.
    apply (ratLt_not_refl (q + r)%q)...
    cut (∀p ∈ x + y, p <𝐪 (q + r)%q). intros Hlt. apply Hlt.
    apply Hext... intros p Hp. apply realAddE in Hp
      as [s [Hs [t [Ht [[Hsx Hty] Hst]]]]]... subst.
    eapply rat_ineq_both_side_add_lt... apply H1... apply H2...
  - intros p Hp s Hs Hlt H. apply realAddE in H
      as [q [Hq [r [Hr [[Hqx Hry] Hqr]]]]]... subst s.
    assert (Hnq: (-q)%q ∈ ℚ) by (apply ratAddInv_is_rat; auto).
    eapply rat_ineq_both_side_add in Hlt;
      try assumption; revgoals. apply Hnq.
    rewrite ratAdd_assoc, (ratAdd_comm r),
      <- ratAdd_assoc, ratAdd_inv, ratAdd_ident' in Hlt...
    eapply realE2 in Hry; revgoals... apply ratAdd_ran...
    cut ((q + (p - q))%q = p). intros Heq.
    eapply realAddI1; revgoals... rewrite (ratAdd_comm p),
      <- ratAdd_assoc, ratAdd_inv, ratAdd_ident'...
  - intros p Hp. apply realAddE in Hp
      as [q [Hq [r [Hr [[Hqx Hry] Hqr]]]]]... subst.
    apply realE3 in Hx as Hx3. apply Hx3 in Hqx as [s [Hs H1]].
    apply realE3 in Hy as Hy3. apply Hy3 in Hry as [t [Ht H2]].
    exists (s + t)%q. split. apply realAddI2...
    apply rat_ineq_both_side_add_lt; auto;
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

Definition Real : nat → set := λ n, {r ∊ ℚ | λ r, r <𝐪 Rat n}.

Theorem real_n : ∀ n, Real n ∈ ℝ.
Proof with eauto.
  intros. assert (Hsubq: Real n ⊆ ℚ). {
    intros q Hq. apply SepE in Hq as []...
  }
  apply SepI. apply PowerAx... repeat split...
  - apply EmptyNI. exists (Rat n - Rat 1)%q.
    apply SepI. apply ratAdd_ran... rewrite ratAdd_comm...
    rewrite <- (ratAdd_ident' (Rat n)) at 2...
    apply rat_ineq_both_side_add...
    pose proof intPos_1 as Hp1.
    unfold Rat. rewrite ratAddInv... apply ratLt...
    rewrite intMul_ident, intMul_ident...
    unfold Int. rewrite intAddInv... apply intLt...
    rewrite add_0_l, add_0_l... apply suc_has_0...
  - intros Hext. rewrite ExtAx in Hext.
    pose proof (rat_n n). apply Hext in H.
    apply SepE in H as [_ H]. eapply ratLt_not_refl; revgoals...
  - intros p Hp q Hq Hlt Hqn. apply SepE in Hqn as [_ Hqn].
    apply SepI... eapply ratLt_tranr...
  - intros p Hpn. apply SepE in Hpn as [Hp Hpn].
    apply ch5_14 in Hpn as [q [Hq [Hpq Hqn]]]...
    exists q. split... apply SepI...
Qed.
Hint Immediate real_n : core.

Theorem realAdd_ident : ∀ x ∈ ℝ, x + Real 0 = x.
Proof with auto.
  intros x Hx. apply ExtAx. intros p. split; intros Hp.
  - apply realAddE in Hp as [q [Hq [r [Hr [[Hqx Hr0] Hqr]]]]]...
    subst. apply SepE in Hr0 as [_ Hr0]. eapply realE2 in Hx.
    eapply Hx. apply ratAdd_ran... apply Hq.
    rewrite ratAdd_comm... rewrite <- (ratAdd_ident' q) at 2...
    apply rat_ineq_both_side_add... apply Hqx.
  - apply real_sub_rat in Hp as Hpq... assert (Hp' := Hp).
    apply realE3 in Hp' as [r [Hr Hpr]]...
    apply real_sub_rat in Hr as Hrq...
    assert (Hnrq : (-r)%q ∈ ℚ) by (apply ratAddInv_is_rat; auto).
    eapply realAddI1... apply Hr. apply SepI.
    eapply ratAdd_ran. apply Hpq. apply Hnrq.
    rewrite (rat_ineq_both_side_add p Hpq r Hrq _ Hnrq) in Hpr.
    rewrite ratAdd_inv in Hpr... rewrite (ratAdd_comm p),
      <- ratAdd_assoc, ratAdd_inv, ratAdd_ident'...
Qed.

Corollary realAdd_ident' : ∀ x ∈ ℝ, Real 0 + x = x.
Proof with auto.
  intros x Hx. rewrite realAdd_comm, realAdd_ident...
Qed.

(** 实数加法逆元 **)
Definition RealAddInv : set → set := λ x,
  {r ∊ ℚ | λ r, ∃ s, r <𝐪 s ∧ (-s)%q ∉ x}.
Notation "- x" := (RealAddInv x) : Real_scope.
Notation "x - y" := (x + (-y)) : Real_scope.















