(** Coq coding by choukh, Feb 2021 **)

Require Import ZFC.EST7_6.
Require Import ZFC.EX7_3.
Require Import ZFC.EST8_3.

Section EX8_1_and_2.
Import 𝐎𝐍Operation.
Close Scope Card_scope.
Open Scope Nat_scope.

Definition t := Operation 5 Suc.

Example ex8_2_a : ∀α ∈ ω, t α = 5 + α.
Proof with nauto.
  intros α Hα.
  set {α ∊ ω | λ α, t α = 5 + α} as N.
  ω_induction N Hα; unfold t in *.
  - rewrite operation_0, add_ident...
  - rewrite operation_suc, IH; [|apply nat_is_ord]...
    rewrite add_suc, add_suc, add_assoc... apply add_ran...
Qed.

Example ex8_2_b : ∀ α, is_ord α → ω ⋸ α → t α = α.
Proof with neauto.
  set (λ α, ω ⋸ α → t α = α) as ϕ.
  apply (transfinite_induction_schema_on_ordinals ϕ).
  intros α Hoα IH Hle. unfold t.
  destruct (ord_is_suc_or_limit α) as [|Hlim]...
  - destruct H as [β [Hoβ Heq]]. subst.
    destruct Hle as [Hlt|Heq].
    + rewrite operation_suc... f_equal.
      apply IH... apply ord_leq_iff_lt_suc...
    + exfalso. apply (ord_is_limit_iff_not_suc ω)...
      exists β. split...
  - destruct (classic (α = ∅)). {
      subst. destruct Hle. exfalso0. exfalso. apply ω_neq_0...
    }
    rewrite operation_limit...
    apply ExtAx. split; intros Hx.
    + apply FUnionE in Hx as [n [Hn Hx]].
      assert (Hon: is_ord n). eapply ord_is_ords...
      destruct (classic (ω ⋸ n)) as [Hω|Hω]. {
        rewrite IH in Hx... eapply ord_trans...
      }
      assert (Hnω: n ∈ ω). {
        destruct (classic (n ∈ ω))... exfalso.
        apply Hω. apply ord_leq_iff_not_gt...
      }
      rewrite ex8_2_a in Hx...
      apply ord_leq_iff_sub in Hle... apply Hle.
      eapply ord_trans... apply add_ran...
    + assert (Hox: is_ord x). eapply ord_is_ords...
      destruct (classic (ω ⋸ x⁺)) as [Hω|Hω]. {
        eapply FUnionI. apply suc_in_limit...
        rewrite IH... apply suc_in_limit...
      }
      assert (Hxpω: x⁺ ∈ ω). {
        destruct (classic (x⁺ ∈ ω))... exfalso.
        apply Hω. apply ord_leq_iff_not_gt...
      }
      assert (Hxω: x ∈ ω). eapply ω_trans; revgoals...
      eapply FUnionI... rewrite ex8_2_a...
      rewrite <- add_ident at 1...
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
  set {ReplA | x ∊ A S} as A'.
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
  set {ReplR | x ∊ R S} as R'.
  assert (Hbr: is_binRel R' A'). {
    intros x Hx. apply ReplAx in Hx as [p [Hp Hx]]. subst x.
    apply ordered_struct in Hp.
    apply CProdE1 in Hp as [a [Ha [b [Hb Hp]]]]. subst p.
    unfold ReplR. zfcrewrite.
    destruct (ixm (a = a₀)); destruct (ixm (b = a₀));
    apply CProdI; apply ReplAx; unfold ReplA.
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
    apply meta_bijective.
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
      unfold ReplR. zfcrewrite.
      destruct (ixm (x = a₀)); destruct (ixm (y = a₀));
      apply op_iff; split; unfold f;
      rewrite meta_func_ap; auto; unfold ReplA;
      destruct (ixm (x = a₀)); destruct (ixm (y = a₀))...
    - apply ReplAx in H as [p [Hp Heq]].
      apply ordered_struct in Hp as H.
      apply CProdE1 in H as [a [Ha [b [Hb H]]]]. subst p.
      unfold ReplR in Heq. zfcrewrite.
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
  apply ExtAx. split; intros Hx.
  - apply kard_elim in Hx as [Hx _].
    apply eqnum_empty in Hx. subst x...
  - apply SingE in Hx. subst x.
    apply kard_intro. reflexivity.
    intros x Hx. symmetry in Hx.
    apply eqnum_empty in Hx. subst x...
Qed.

Example kard_1 : kard 1 = ⎨1⎬.
Proof with neauto.
  apply ExtAx. split; intros Hx.
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
    apply one_neq_two...
  }
  apply ExtAx. split; intros Hx.
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
    assert (Ho: is_ord (rank a ∪ rank b)). {
      apply union_of_ords_is_ord.
      intros x Hx. apply PairE in Hx as []; subst...
    }
    rewrite rank_of_pair, rank_of_ord...
    apply ord_leq_iff_sub... intros x Hx. rewrite two in Hx.
    apply TwoE in Hx as []; subst. eapply ord_suc_has_0...
    rewrite <- one. apply ord_lt_suc_iff_sub...
    intros x Hx. rewrite one in Hx. apply SingE in Hx; subst.
    destruct (classic (rank a = 0)).
    + apply BUnionI2. apply ord_nq_0_gt_0...
      intros H0. apply rank_0 in H. apply rank_0 in H0...
    + apply BUnionI1. apply ord_nq_0_gt_0...
Qed.

(* kard 3 = {3, {0, 1, {1}}, {0, {1}, 2}, {1, {1}, 2}} *)

End EX8_10.
