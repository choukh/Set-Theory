(** Coq coding by choukh, Feb 2021 **)

Require Import ZFC.Theory.EST7_6.
Require Import ZFC.Theory.EX7_3.
Require Import ZFC.Theory.EST8_2.
Require Import ZFC.Theory.EST8_4.
Require Import ZFC.Lib.LoStruct.

Section EX8_1_and_2.
Import 𝐎𝐍Operation.
Close Scope Card_scope.
Open Scope omega_scope.

Definition t := Operation 5 Suc.

Example ex8_2_a : ∀α ∈ ω, t α = 5 + α.
Proof with nauto.
  intros α Hα.
  ω_induction α; unfold t in *.
  - rewrite operation_0, add_0_r...
  - rewrite operation_suc, IH; [|apply ω_is_ords]...
    rewrite suc, suc, add_assoc... apply add_ran...
Qed.

Example ex8_2_b : ∀α ⋵ 𝐎𝐍, ω ⋸ α → t α = α.
Proof with neauto.
  ord_induction. intros α Hoα IH Hle. unfold t.
  ord_destruct α.
  - subst. destruct Hle. exfalso0. exfalso. apply ω_neq_0...
  - destruct Hsuc as [β [Hoβ Heq]]. subst.
    destruct Hle as [Hlt|Heq].
    + rewrite operation_suc... f_equal.
      apply IH... apply ord_leq_iff_lt_suc...
    + exfalso. apply (limord_iff_not_sucord ω)...
      exists β. split...
  - rewrite operation_limit...
    ext Hx.
    + apply FUnionE in Hx as [n [Hn Hx]].
      assert (Hon: n ⋵ 𝐎𝐍). eapply ord_is_ords...
      destruct (classic (ω ⋸ n)) as [Hω|Hω]. {
        rewrite IH in Hx... eapply ord_trans...
      }
      assert (Hnω: n ∈ ω). {
        contra.
        apply Hω. apply ord_leq_iff_not_gt...
      }
      rewrite ex8_2_a in Hx...
      apply ord_leq_iff_sub in Hle... apply Hle.
      eapply ord_trans... apply add_ran...
    + assert (Hox: x ⋵ 𝐎𝐍). eapply ord_is_ords...
      destruct (classic (ω ⋸ x⁺)) as [Hω|Hω]. {
        eapply FUnionI. apply sucord_in_limord...
        rewrite IH... apply sucord_in_limord...
      }
      assert (Hxpω: x⁺ ∈ ω). {
        contra.
        apply Hω. apply ord_leq_iff_not_gt...
      }
      assert (Hxω: x ∈ ω). eapply ω_trans; revgoals...
      eapply FUnionI... rewrite ex8_2_a...
      rewrite <- add_0_r at 1...
      rewrite add_comm... apply add_preserve_lt...
      repeat rewrite pred. do 4 apply BUnionI1. apply BUnionI2...
Qed.

End EX8_1_and_2.

(* ex8_3_a see EST8_2 Fact monotone_operation_preserve_order *)
(* ex8_3_b see EST8_1 Lemma monotone_operation_injective *)
(* ex8_4 see EST8_2 Fact normal_operation_limit_is_limit *)
(* ex8_5 see EST8_2 Lemma monotone_operation_leq *)
(* ex8_6_a see EST8_1 Lemma monotone_operation_range_unbounded *)
(* ex8_6_b see EST8_1 Lemma normal_operation_range_closed *)
(* ex8_7 see EST8_2 Corollary ex_least_fixed_point *)
(* ex8_8 see EST8_2 Theorem fixed_point_normal *)

Section EX8_9.
Import OrderedStruct.

(* ex8_9 不存在包含所有同构结构的集合 *)
Fact no_set_of_all_isomorphic_struct :
  ∀ S, A S ≠ ∅ → ¬ ∃ X, ∀ T, S ≅ T → <A T, R T> ∈ X.
Proof with auto; try congruence.
  intros S Hne [X Hall].
  apply no_set_of_all_set. exists (⋃⋃⋃ X). intros xₒ.
  apply EmptyNE in Hne as [a₀ Ha₀].
  destruct (classic (xₒ ∈ A S)) as [|Hout]. {
    apply UnionAx. exists (A S). split...
    apply UnionAx. exists ⎨A S⎬. split...
    apply UnionAx. exists <A S, R S>. split.
    apply Hall. reflexivity. apply PairI1.
  }
  set (λ x, match (ixm (x = a₀)) with
    | inl _ => xₒ
    | inr _ => x
  end) as ReplA.
  set {ReplA x | x ∊ A S} as A'.
  set (λ p, match (ixm (π1 p = a₀)) with
    | inl _ =>
      match (ixm (π2 p = a₀)) with
      | inl _ => <xₒ, xₒ>
      | inr _ => <xₒ, π2 p>
      end
    | inr _ =>
      match (ixm (π2 p = a₀)) with
      | inl _ => <π1 p, xₒ>
      | inr _ => p
  end end) as ReplR.
  set {ReplR x | x ∊ R S} as R'.
  assert (Hbr: is_binRel R' A'). {
    intros x Hx. apply ReplAx in Hx as [p [Hp Hx]]. subst x.
    apply ordered_struct in Hp.
    apply CPrdE1 in Hp as [a [Ha [b [Hb Hp]]]]. subst p.
    unfold ReplR. zfc_simple.
    destruct (ixm (a = a₀)); destruct (ixm (b = a₀));
    apply CPrdI; apply ReplAx; unfold ReplA.
    - exists a₀. split... destruct (ixm (a₀ = a₀))...
    - exists b. split... destruct (ixm (b = a₀))...
    - exists a. split... destruct (ixm (a = a₀))...
    - exists b. split... destruct (ixm (b = a₀))...
    - exists a. split... destruct (ixm (a = a₀))...
    - exists b. split... destruct (ixm (b = a₀))...
    - exists a. split... destruct (ixm (a = a₀))...
    - exists b. split... destruct (ixm (b = a₀))...
  }
  set (constr A' R' Hbr) as T.
  set (Func (A S) (A T) ReplA) as f.
  assert (Hbi: f: A S ⟺ A T). {
    apply meta_bijection.
    - intros x Hx. eapply ReplI...
    - intros x1 H1 x2 H2 Heq. unfold ReplA in Heq.
      destruct (ixm (x1 = a₀)); destruct (ixm (x2 = a₀))...
    - intros y Hy. apply ReplAx...
  }
  apply bijection_is_func in Hbi as Hf. destruct Hf as [Hf _].
  assert (Hiso: S ≅ T). {
    exists f. split...
    intros x Hx y Hy. split; intros.
    - apply ReplAx. exists <x, y>. split...
      unfold ReplR. zfc_simple.
      destruct (ixm (x = a₀)); destruct (ixm (y = a₀));
      apply op_iff; split; unfold f;
      rewrite meta_func_ap; auto; unfold ReplA;
      destruct (ixm (x = a₀)); destruct (ixm (y = a₀))...
    - apply ReplAx in H as [p [Hp Heq]].
      apply ordered_struct in Hp as H.
      apply CPrdE1 in H as [a [Ha [b [Hb H]]]]. subst p.
      unfold ReplR in Heq. zfc_simple.
      destruct (ixm (a = a₀)); destruct (ixm (b = a₀));
      apply op_iff in Heq as [Hfx Hfy]; unfold f in Hfx, Hfy;
      rewrite meta_func_ap in Hfx, Hfy; auto; unfold ReplA in Hfx, Hfy;
      destruct (ixm (x = a₀)) in Hfx; destruct (ixm (y = a₀)) in Hfy; subst...
  }
  apply UnionAx. exists A'. split.
  apply UnionAx. exists ⎨A'⎬. split...
  apply UnionAx. exists <A T, R T>. split...
  apply PairI1. apply ReplAx. exists a₀. split...
  unfold ReplA. destruct (ixm (a₀ = a₀))...
Qed.

End EX8_9.

Section EX8_10.
Import Kard.
Import RegularityConsequences.
Hint Resolve all_grounded : core.

Example kard_0 : kard 0 = ⎨0⎬.
Proof with auto.
  ext Hx.
  - apply kard_elim in Hx as [Hx _].
    apply eqnum_empty in Hx. subst x...
  - apply SingE in Hx. subst x.
    apply kard_intro. reflexivity.
    intros x Hx. symmetry in Hx.
    apply eqnum_empty in Hx. subst x...
Qed.

Example kard_1 : kard 1 = ⎨1⎬.
Proof with neauto.
  ext Hx.
  - apply kard_elim in Hx as [Hqn Hle].
    apply Hle in Hqn as Hx.
    rewrite (rank_of_ord 1) in Hx...
    apply ord_leq_iff_lt_suc in Hx...
    apply BUnionE in Hx as [Hx|Hx].
    + rewrite one in Hx. apply SingE in Hx.
      apply rank_0 in Hx. subst x. symmetry in Hqn.
      apply eqnum_empty in Hqn. exfalso. eapply suc_neq_0...
    + apply SingE in Hx. apply rank_1 in Hx. subst x...
  - apply SingE in Hx. subst x.
    apply kard_intro. reflexivity.
    intros x Hx. symmetry in Hx.
    apply eqnum_one_iff in Hx as [a Hx]. subst x.
    rewrite rank_of_single, rank_of_ord...
    apply ord_leq_iff_sub... intros x Hx.
    rewrite one in Hx. apply SingE in Hx. subst x.
    apply ord_suc_has_0...
Qed.

Example kard_2 : kard 2 = ⎨2⎬.
Proof with neauto; try congruence.
  assert (Hnqn: 1 ≉ 2). {
    intros Hqn. apply CardAx1 in Hqn.
    rewrite <- card_of_nat, <- card_of_nat in Hqn...
    apply contra_1_2...
  }
  ext Hx.
  - apply kard_elim in Hx as [Hqn Hle].
    apply Hle in Hqn as Hx.
    rewrite (rank_of_ord 2) in Hx...
    apply ord_leq_iff_lt_suc in Hx...
    apply BUnionE in Hx as [Hx|Hx].
    + rewrite two in Hx.
      apply TwoE in Hx as [Hx|Hx]; exfalso.
      * apply rank_0 in Hx. subst x. symmetry in Hqn.
        apply eqnum_empty in Hqn. eapply suc_neq_0...
      * rewrite <- one in Hx. apply rank_1 in Hx. subst x...
    + apply SingE in Hx. apply rank_2 in Hx as []; subst x...
      rewrite eqnum_single in Hqn...
  - apply SingE in Hx. subst x.
    apply kard_intro. reflexivity.
    intros x Hx. symmetry in Hx.
    apply eqnum_two_iff in Hx as [a [b [Hnq Hx]]]. subst x.
    assert (Ho: rank a ∪ rank b ⋵ 𝐎𝐍). {
      apply union_of_ords_is_ord.
      intros x Hx. apply PairE in Hx as []; subst...
    }
    rewrite rank_of_pair, rank_of_ord...
    apply ord_leq_iff_sub... intros x Hx. rewrite two in Hx.
    apply TwoE in Hx as []; subst. eapply ord_suc_has_0...
    rewrite <- one. apply ord_lt_suc_iff_sub...
    intros x Hx. rewrite one in Hx. apply SingE in Hx; subst.
    destruct (classic (rank a = 0)).
    + apply BUnionI2. apply ord_neq_0_gt_0...
      intros H0. apply rank_0 in H. apply rank_0 in H0...
    + apply BUnionI1. apply ord_neq_0_gt_0...
Qed.

(* kard 3 = {3, {0, 1, {1}}, {0, {1}, 2}, {1, {1}, 2}} *)

End EX8_10.

(* ex8_11 see EST8_3 Lemma ot_disjointifiable *)

(* ex8_12 *)
Module AlternativeOtAdd.
Import OrderType.
Open Scope LoStruct_scope.

(* 字典序 *)
Definition LoAdd_R := λ S T, BinRel (A S × ⎨0⎬ ∪ A T × ⎨1⎬) (λ p1 p2,
  (π2 p1 <ᵣ π2 p2) (MemberRel 2) ∨
  π2 p1 = π2 p2 ∧ (
    π2 p1 = 0 ∧ (π1 p1 <ᵣ π1 p2) (R S) ∨
    π2 p1 = 1 ∧ (π1 p1 <ᵣ π1 p2) (R T)
  )
).
Notation "S ⨁' T" := (LoAdd_R S T) (at level 70) : LoStruct_scope.

Lemma loAdd_is_binRel : ∀ S T,
  is_binRel (S ⨁' T) (A S × ⎨0⎬ ∪ A T × ⎨1⎬).
Proof with auto.
  intros * x Hx.
  apply binRelE1 in Hx as [s [Hs [t [Ht [Hx _]]]]];
  apply BUnionE in Hs as [Hs|Hs];
  apply BUnionE in Ht as [Ht|Ht];
  apply CPrdE1 in Hs as [a [Ha [b [Hb Hs]]]];
  apply CPrdE1 in Ht as [c [Hc [d [Hd Ht]]]];
  apply SingE in Hb; apply SingE in Hd;
  subst; zfc_simple; apply CPrdI; solve [
    apply BUnionI1; apply CPrdI; auto|
    apply BUnionI2; apply CPrdI; auto].
Qed.

Local Lemma lt_0_0 : (0 <ᵣ 0) (MemberRel 2) → False.
Proof.
  intros H. apply binRelE3 in H. exfalso0.
Qed.

Local Lemma lt_0_1 : (0 <ᵣ 1) (MemberRel 2).
Proof with auto.
  apply binRelI. apply BUnionI1. apply BUnionI2...
  apply BUnionI2... apply BUnionI2...
Qed.

Local Lemma lt_1_0 : (1 <ᵣ 0) (MemberRel 2) → False.
Proof.
  intros H. apply binRelE3 in H. exfalso0.
Qed.

Local Lemma lt_1_1 : (1 <ᵣ 1) (MemberRel 2) → False.
Proof.
  intros H. apply binRelE3 in H.
  eapply nat_irrefl; revgoals; neauto.
Qed.

Lemma loAdd_tranr : ∀ S T, tranr (S ⨁' T).
Proof with eauto.
  intros S T x y z Hxy Hyz.
  pose proof lt_0_0 as H00.
  pose proof lt_0_1 as H01.
  pose proof lt_1_0 as H10.
  pose proof lt_1_1 as H11.
  apply binRelE2 in Hxy as [Hx [Hy [Hxy|[Heq1 [[H0 Hxy]|[H0 Hxy]]]]]];
  apply binRelE2 in Hyz as [_  [Hz [Hyz|[Heq2 [[H1 Hyz]|[H1 Hyz]]]]]];
  apply BUnionE in Hx as [Hx|Hx];
  apply BUnionE in Hy as [Hy|Hy];
  apply BUnionE in Hz as [Hz|Hz];
  apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]];
  apply CPrdE1 in Hy as [c [Hc [d [Hd Hy]]]];
  apply CPrdE1 in Hz as [e [He [f [Hf Hz]]]];
  apply SingE in Hb; apply SingE in Hd; apply SingE in Hf;
  subst; zfc_simple; (apply binRelI; zfc_simple; [
    solve [
      apply BUnionI1; apply CPrdI; auto|
      apply BUnionI2; apply CPrdI; auto
    ]|
    solve [
      apply BUnionI1; apply CPrdI; auto|
      apply BUnionI2; apply CPrdI; auto
    ]|
  ]).
  left... left...
  right; split... left; split...
  eapply relLt_tranr; revgoals... apply lo.
  right; split... right; split...
  eapply relLt_tranr; revgoals... apply lo.
Qed.

Lemma loAdd_irrefl : ∀ S T, irrefl (S ⨁' T).
Proof with neauto.
  intros S T x H.
  apply binRelE2 in H as [Hx [_ [Hlt|[Heq [[H0 Hlt]|[H1 Hlt]]]]]].
  - apply binRelE3 in Hlt. eapply nat_irrefl; revgoals...
    apply BUnionE in Hx as []; apply CPrdE0 in H as [_ H];
    apply SingE in H; rewrite H...
  - eapply relLt_irrefl; revgoals... eapply lo_irrefl. apply lo.
  - eapply relLt_irrefl; revgoals... eapply lo_irrefl. apply lo.
Qed.

Lemma loAdd_connected : ∀ S T,
  connected (S ⨁' T) (A S × ⎨0⎬ ∪ A T × ⎨1⎬).
Proof with eauto; try congruence.
  intros S T x Hx y Hy Hnq.
  apply BUnionE in Hx as [Hx|Hx];
  apply BUnionE in Hy as [Hy|Hy];
  apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]];
  apply CPrdE1 in Hy as [c [Hc [d [Hd Hy]]]];
  apply SingE in Hb; apply SingE in Hd; subst; zfc_simple.
  - destruct (classic (a = c)). subst...
    eapply lo_connected in H; revgoals... apply lo.
    destruct H; [left|right]; (
      apply binRelI; [apply BUnionI1; apply CPrdI; auto..|]
    ); zfc_simple...
  - left. apply binRelI.
    apply BUnionI1. apply CPrdI...
    apply BUnionI2. apply CPrdI...
    zfc_simple. left. apply lt_0_1.
  - right. apply binRelI.
    apply BUnionI1. apply CPrdI...
    apply BUnionI2. apply CPrdI...
    zfc_simple. left. apply lt_0_1.
  - destruct (classic (a = c)). subst...
      eapply lo_connected in H; revgoals... apply lo.
    destruct H; [left|right]; (
      apply binRelI; [apply BUnionI2; apply CPrdI; auto..|]
    ); zfc_simple...
Qed.

Theorem loAdd_loset : ∀ S T,
  loset (A S × ⎨0⎬ ∪ A T × ⎨1⎬) (S ⨁' T).
Proof.
  intros S T.
  apply loset_iff_connected_poset. repeat split.
  - apply loAdd_connected.
  - apply loAdd_is_binRel.
  - eapply binRel_is_rel. apply loAdd_is_binRel.
  - apply loAdd_tranr.
  - apply loAdd_irrefl.
Qed.

Definition LoAdd := λ S T,
  constr (A S × ⎨0⎬ ∪ A T × ⎨1⎬) (S ⨁' T) (loAdd_loset S T).
Notation "S +' T" := (LoAdd S T) (at level 50): LoStruct_scope.

Lemma alternative_loAdd_R_correct : ∀ S T,
  (S ⨁' T) = (LoDisj S 0 ⨁ LoDisj T 1).
Proof with auto.
  intros.
  pose proof lt_0_0 as H00.
  pose proof lt_0_1 as H01.
  pose proof lt_1_0 as H10.
  pose proof lt_1_1 as H11.
  ext Hx.
  - apply binRelE1 in Hx as [a [Ha [b [Hb [Hx [Hlt|[Heq [[H0 Hlt]|[H1 Hlt]]]]]]]]];
    apply BUnionE in Ha as [Ha|Ha];
    apply BUnionE in Hb as [Hb|Hb];
    apply CPrdE1 in Ha as [s [Hs [t [Ht Ha]]]];
    apply CPrdE1 in Hb as [u [Hu [v [Hv Hb]]]];
    apply SingE in Ht; apply SingE in Hv; subst; zfc_simple.
    + apply BUnionI2. apply CPrdI; apply CPrdI...
    + apply BUnionI1. apply BUnionI1. apply ReplAx.
      exists <s, u>. split; zfc_simple...
    + apply BUnionI1. apply BUnionI2. apply ReplAx.
      exists <s, u>. split; zfc_simple...
  - apply BUnionE in Hx as [Hx|Hx].
    + destruct (lo S) as [HbrS _].
      destruct (lo T) as [HbrT _].
      apply BUnionE in Hx as [Hx|Hx];
      apply ReplAx in Hx as [p [Hp Heq]];
      [apply HbrS in Hp as H|apply HbrT in Hp as H];
      apply CPrdE1 in H as [a [Ha [b [Hb H]]]];
      subst; zfc_simple; apply binRelI; zfc_simple...
      * apply BUnionI1; apply CPrdI...
      * apply BUnionI1; apply CPrdI...
      * apply BUnionI2; apply CPrdI...
      * apply BUnionI2; apply CPrdI...
    + apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]].
      apply CPrdE1 in Ha as [s [Hs [t [Ht Ha]]]].
      apply CPrdE1 in Hb as [u [Hu [v [Hv Hb]]]].
      apply SingE in Ht. apply SingE in Hv.
      subst. zfc_simple. apply binRelI; zfc_simple...
      apply BUnionI1; apply CPrdI...
      apply BUnionI2; apply CPrdI...
Qed.

Lemma alternative_loAdd_correct : ∀ S T, S + T ≅ S +' T.
Proof with auto.
  intros. replace (S + T) with (S +' T). reflexivity.
  apply eq_intro... simpl. apply alternative_loAdd_R_correct.
Qed.

(* ex8_12 *)
Lemma alternative_otAdd_correct : ∀ S T,
  (ot S + ot T)%ot = ot (S +' T).
Proof with auto.
  intros. rewrite (otAdd_eq_ot_of_loAdd S T).
  apply ot_correct. apply alternative_loAdd_correct.
Qed.

Lemma loAdd_well_defined : ∀ S S' T T',
  S ≅ S' → T ≅ T' → S +' T ≅ S' +' T'.
Proof.
  intros * HS HT. do 2 rewrite <- alternative_loAdd_correct.
  apply EST8_3.loAdd_well_defined; auto.
Qed.

Definition otAdd_spec := λ ρ σ τ,
  ∀ S T, ρ = ot S → σ = ot T → τ = ot (S +' T).
Definition OtAdd := λ ρ σ, describe (otAdd_spec ρ σ).
Notation "ρ +' σ" := (OtAdd ρ σ) : OrderType_scope.

Open Scope OrderType_scope.

Lemma otAdd_spec_intro : ∀ ρ σ ⋵ 𝐎𝐓, otAdd_spec ρ σ (ρ +' σ).
Proof.
  intros ρ [S HS] σ [T HT]. apply (desc_spec (otAdd_spec ρ σ)).
  rewrite <- unique_existence. split.
  - exists (ot (S +' T)%lo). intros S' T' H1 H2. subst.
    apply ot_correct in H1. apply ot_correct in H2.
    apply ot_correct. apply loAdd_well_defined; auto.
  - intros τ1 τ2 H1 H2.
    pose proof (H1 S T HS HT).
    pose proof (H2 S T HS HT). congruence.
Qed.

Lemma otAdd_eq_ot_of_loAdd : ∀ S T, ot S +' ot T = ot (S +' T)%lo.
Proof. intros. erewrite otAdd_spec_intro; auto. Qed.

Theorem otAdd_well_defined : ∀ S S' T T',
  S ≅ S' → T ≅ T' → ot S +' ot T = ot S' +' ot T'.
Proof.
  intros * HisoS HisoT. do 2 rewrite otAdd_eq_ot_of_loAdd.
  apply ot_correct. apply loAdd_well_defined; auto.
Qed.

End AlternativeOtAdd.

(* ex8_13 see EST8_3 Theorem otAdd_well_defined and
  EST8_4 Theorem otMul_well_defined *)

Import OrderType.
Import StructureCasting.

Example ex8_14 : ∀ ρ σ ⋵ 𝐎𝐓,
  ρ ⋅ σ = otⁿ 0 → ρ = otⁿ 0 ∨ σ = otⁿ 0.
Proof with auto.
  intros ρ [S HS] σ [T HT] H0. subst.
  rewrite otMul_eq_ot_of_loMul in H0. unfold otⁿ in H0.
  apply ot_correct in H0 as [f [Hf _]]. simpl in Hf.
  apply bijection_to_empty in Hf.
  apply cprd_to_0 in Hf as []; [left|right];
  apply ot_correct.
  - replace (LOⁿ 0) with S. reflexivity.
    apply eq_intro... ext Hx.
    + destruct (lo S) as [Hbr _].
      apply Hbr in Hx. rewrite H, cprd_0_l in Hx. exfalso0.
    + apply binRelE1 in Hx as [a [Ha _]]. exfalso0.
  - replace (LOⁿ 0) with T. reflexivity.
    apply eq_intro... ext Hx.
    + destruct (lo T) as [Hbr _].
      apply Hbr in Hx. rewrite H, cprd_0_l in Hx. exfalso0.
    + apply binRelE1 in Hx as [a [Ha _]]. exfalso0.
Qed.

(* ex8_15 (ℕ̅ + 1) ⋅ 2 = ℕ̅ 0 ℕ̅ 0 ≠ ℕ̅ ℕ̅ 0 0 = (ℕ̅ ⋅ 2) + (1 ⋅ 2) *)
(* ex8_16 see EST8_4 Theorem otAdd_0_r, otMul_1_r, otMul_0_r *)
