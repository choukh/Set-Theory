(** Based on "Elements of Set Theory" Chapter 8 Part 3 **)
(** Coq coding by choukh, Mar 2021 **)

Global Set Warnings "-unrecognized-unicode".

Require Export ZFC.EST8_2.
Require Import ZFC.lib.LoStruct.
Require Import ZFC.lib.ScottsTrick.

Require ZFC.EX7_1.
Require ZFC.lib.Real.
Require ZFC.lib.NatIsomorphism.
Require Coq.micromega.Lia.

(*** EST第八章3：序类型，序类型加法 ***)

Module Import OrderType.
Import ScottsTrick.ForAnyType.

Declare Scope OrderType_scope.
Delimit Scope OrderType_scope with ot.
Open Scope OrderType_scope.

(* 序类型：线序结构的同构类型 *)
Definition ot := λ S, scott (λ S, <A S, R S>) isomorphic S.

Fact ot_nonempty : ∀ S, ot S ≠ ∅.
Proof.
  intros. unfold ot. apply scott_nonempty. apply iso_equiv.
Qed.

Theorem ot_correct : ∀ S T, ot S = ot T ↔ S ≅ T.
Proof.
  intros. unfold ot. apply scott_correct.
  intros U V Heq. apply op_iff in Heq as [].
  apply eq_intro; auto. apply iso_equiv.
Qed.

(* 结构投射 *)
Definition proj :=
  λ x, epsilon (inhabits EmptyStruct) (λ S, ot S = x).

Definition is_ot := λ ρ, ∃ S, ρ = ot S.

Lemma ot_is_ot : ∀ S, is_ot (ot S).
Proof. intros. exists S. auto. Qed.
Global Hint Immediate ot_is_ot : core.

Lemma ot_proj_id : ∀ ρ, is_ot ρ → ot (proj ρ) = ρ.
Proof.
  intros ρ [S Heqρ]. unfold proj.
  apply epsilon_spec. exists S. auto.
Qed.

Lemma proj_ot_id : ∀ S, proj (ot S) ≅ S.
Proof.
  intros S. apply ot_correct. rewrite ot_proj_id; auto.
Qed.

Lemma inv_loset : ∀ S, loset (A S) (R S)⁻¹.
Proof. intros. apply ex3_43. apply lo. Qed.

(* 逆序 *)
Definition LoInv :=
  λ S, constr (A S) (R S)⁻¹ (inv_loset S).
Definition OtInv :=
  λ ρ, ot (LoInv (proj ρ)).
Notation "- ρ" := (OtInv ρ) : OrderType_scope.

Lemma otInv_struct : ∀ S,
  -ot S = ot (constr (A S) (R S)⁻¹ (inv_loset S)).
Proof with auto.
  intros. apply ot_correct. unfold LoInv.
  pose proof (proj_ot_id S) as [f [Hf Hopf]].
  exists f. split; simpl...
  intros x Hx y Hy. split; intros Hxy.
  - apply inv_op in Hxy. apply Hopf in Hxy...
    apply inv_op in Hxy...
  - apply inv_op in Hxy. apply Hopf in Hxy...
    apply inv_op in Hxy...
Qed.

Import ZFC.lib.Real.

Lemma Lt_linearOrder : linearOrder Lt ω.
Proof. apply Lt_wellOrder. Qed.

Notation "ℕ̅" := (ot (constr ω Lt Lt_linearOrder)).
Notation "ℤ̅" := (ot (constr ℤ IntLt intLt_linearOrder)).
Notation "ℚ̅" := (ot (constr ℚ RatLt ratLt_linearOrder)).
Notation "ℝ̅" := (ot (constr ℝ RealLt realLt_linearOrder)).

End OrderType.

(* 结构不交化 *)
Definition LoDisj_A :=
  λ S i, (A S × ⎨i⎬).
Definition LoDisj_R :=
  λ S i, {λ p, <<π1 p, i>, <π2 p, i>> | p ∊ R S}.

Lemma loDisj_is_binRel :
  ∀ S i, is_binRel (LoDisj_R S i) (LoDisj_A S i).
Proof.
  intros S i x Hx. destruct (lo S) as [Hbr _].
  apply ReplAx in Hx as [p [Hp Hx]]. apply Hbr in Hp.
  apply CProdE1 in Hp as [a [Ha [b [Hb Hp]]]].
  subst. zfc_simple. apply CProdI; apply CProdI; auto.
Qed.

Lemma loDisj_tranr : ∀ S i, tranr (LoDisj_R S i).
Proof.
  intros S i x y z Hxy Hyz.
  destruct (lo S) as [Hbr [Htr _]].
  apply ReplAx in Hxy as [p [Hp Hxy]]. apply Hbr in Hp as H1.
  apply ReplAx in Hyz as [q [Hq Hyz]]. apply Hbr in Hq as H2.
  apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]].
  apply CProdE1 in H2 as [c [Hc [d [Hd H2]]]].
  apply op_iff in Hxy as []; subst.
  apply op_iff in Hyz as []; subst. zfc_simple.
  apply op_iff in H as []; subst.
  apply ReplAx. exists <a, d>. split; zfc_simple. eapply Htr; eauto.
Qed.

Lemma loDisj_irrefl : ∀ S i, irrefl (LoDisj_R S i).
Proof.
  intros S i x Hp. destruct (lo S) as [Hbr _].
  apply ReplAx in Hp as [p [Hp Heq]]. apply Hbr in Hp as H.
  apply CProdE1 in H as [a [Ha [b [Hb H]]]]. subst. zfc_simple.
  apply op_iff in Heq as []; subst.
  apply op_iff in H0 as []; subst.
  eapply lo_irrefl; eauto. apply lo.
Qed.

Lemma loDisj_connected : ∀ S i,
  connected (LoDisj_R S i) (LoDisj_A S i).
Proof with auto.
  intros S i x Hx y Hy Hnq.
  apply CProdE1 in Hx as [a [Ha [b [Hb Heqx]]]].
  apply CProdE1 in Hy as [c [Hc [d [Hd Heqy]]]].
  apply SingE in Hb; apply SingE in Hd; subst.
  destruct (classic (a = c)) as [|Hnq']. subst. exfalso...
  eapply (lo_connected _ _ (lo S)) in Hnq' as []...
  left. apply ReplAx. exists <a, c>. split; zfc_simple.
  right. apply ReplAx. exists <c, a>. split; zfc_simple.
Qed.

Lemma loDisj_loset :
  ∀ S i, loset (LoDisj_A S i) (LoDisj_R S i).
Proof with eauto.
  intros S i.
  apply loset_iff_connected_poset. repeat split.
  apply loDisj_connected. apply loDisj_is_binRel.
  eapply binRel_is_rel. apply loDisj_is_binRel.
  apply loDisj_tranr. apply loDisj_irrefl.
Qed.

Definition LoDisj :=
  λ S i, constr (LoDisj_A S i) (LoDisj_R S i) (loDisj_loset S i).

Lemma loDisj_iso : ∀ S i, S ≅ LoDisj S i.
Proof with auto.
  intros S i.
  set (Func (A S) (LoDisj_A S i) (λ x, <x, i>)) as f.
  assert (Hbi: f : A S ⟺ A (LoDisj S i)). {
    apply meta_bijective.
    - intros x Hx. apply CProdI...
    - intros x1 H1 x2 H2. apply op_iff.
    - intros y Hy. apply CProdE1 in Hy as [a [Ha [b [Hb Hy]]]].
      apply SingE in Hb. subst. exists a. split...
  }
  apply bijection_is_func in Hbi as Hf. destruct Hf as [Hf _].
  exists f. split... intros x Hx y Hy. split; intros Hlt.
  - apply ReplAx. exists <x, y>. split... zfc_simple.
    unfold f. rewrite meta_func_ap, meta_func_ap...
  - apply ReplAx in Hlt as [p [Hp Heq]].
    unfold f in Heq. rewrite meta_func_ap, meta_func_ap in Heq...
    apply op_iff in Heq as [H1 H2].
    apply op_iff in H1 as []; subst.
    apply op_iff in H2 as []; subst.
    destruct (lo S) as [Hbr _]. apply Hbr in Hp as H.
    apply CProdE1 in H as [a [Ha [b [Hb H]]]].
    subst. zfc_simple...
Qed.

Lemma loDisj_disjoint : ∀ S T i j, i ≠ j →
  disjoint (A (LoDisj S i)) (A (LoDisj T j)).
Proof. intros S T i j Hnq. apply cprod_disjointify; auto. Qed.

(* ex8_11 任意两个序类型可以不交化 *)
Lemma ot_disjointifiable : ∀ ρ σ, is_ot ρ → is_ot σ →
  ∃ S T, ρ = ot S ∧ σ = ot T ∧ disjoint (A S) (A T).
Proof.
  intros ρ σ [S Heqρ] [T Heqσ].
  exists (LoDisj S 0), (LoDisj T 1). repeat split.
  - subst. apply ot_correct. apply loDisj_iso.
  - subst. apply ot_correct. apply loDisj_iso.
  - apply loDisj_disjoint. auto.
Qed.

Definition LoAdd_R := λ S T,
  R S ∪ R T ∪ (A S × A T).
Notation "S ⨁ T" := (LoAdd_R S T) (at level 70) : LoStruct_scope.

Lemma loAdd_is_binRel : ∀ S T, is_binRel (S ⨁ T) (A S ∪ A T).
Proof with auto.
  intros S T x Hx.
  destruct (lo S) as [HbrS _].
  destruct (lo T) as [HbrT _].
  apply BUnionE in Hx as [].
  - apply BUnionE in H as []; [apply HbrS in H|apply HbrT in H];
    apply CProdE1 in H as [a [Ha [b [Hb H]]]]; subst.
    apply CProdI; apply BUnionI1...
    apply CProdI; apply BUnionI2...
  - apply CProdE1 in H as [a [Ha [b [Hb H]]]]; subst;
    apply CProdI; [apply BUnionI1|apply BUnionI2]...
Qed.

Lemma loAdd_tranr : ∀ S T, disjoint (A S) (A T) → tranr (S ⨁ T).
Proof with eauto.
  intros S T Hdj x y z Hxy Hyz.
  destruct (lo S) as [HbrS [HtrS _]].
  destruct (lo T) as [HbrT [HtrT _]].
  apply BUnionE in Hxy as [Hxy|Hxy];
  apply BUnionE in Hyz as [Hyz|Hyz].
  - apply BUnionE in Hxy as [Hxy|Hxy];
    apply BUnionE in Hyz as [Hyz|Hyz].
    + apply BUnionI1. apply BUnionI1. eapply HtrS...
    + apply HbrS in Hxy. apply CProdE2 in Hxy as [Hx _].
      apply HbrT in Hyz. apply CProdE2 in Hyz as [_ Hz].
      apply BUnionI2. apply CProdI...
    + apply HbrT in Hxy. apply CProdE2 in Hxy as [_ H1].
      apply HbrS in Hyz. apply CProdE2 in Hyz as [H2 _].
      exfalso. eapply disjointE...
    + apply BUnionI1. apply BUnionI2. eapply HtrT...
  - apply BUnionE in Hxy as [Hxy|Hxy].
    + apply HbrS in Hxy. apply CProdE2 in Hxy as [Hx _].
      apply CProdE2 in Hyz as [_ Hz].
      apply BUnionI2. apply CProdI...
    + apply HbrT in Hxy. apply CProdE2 in Hxy as [_ H1].
      apply CProdE2 in Hyz as [H2 _].
      exfalso. eapply disjointE...
  - apply BUnionE in Hyz as [Hyz|Hyz].
    + apply HbrS in Hyz. apply CProdE2 in Hyz as [H1 _].
      apply CProdE2 in Hxy as [_ H2].
      exfalso. eapply disjointE...
    + apply HbrT in Hyz. apply CProdE2 in Hyz as [_ Hz].
      apply CProdE2 in Hxy as [Hx _].
      apply BUnionI2. apply CProdI...
  - apply CProdE2 in Hxy as [_ H1].
    apply CProdE2 in Hyz as [H2 _].
    exfalso. eapply disjointE...
Qed.

Lemma loAdd_irrefl : ∀ S T, disjoint (A S) (A T) → irrefl (S ⨁ T).
Proof with eauto.
  intros S T Hdj x H.
  apply BUnionE in H as [].
  - apply BUnionE in H as [].
    + eapply lo_irrefl... apply lo.
    + eapply lo_irrefl... apply lo.
  - apply CProdE1 in H as [a [Ha [b [Hb Heq]]]].
    apply op_iff in Heq as []; subst.
    exfalso. eapply disjointE...
Qed.

Lemma loAdd_connected : ∀ S T, connected (S ⨁ T) (A S ∪ A T).
Proof with auto.
  intros S T x Hx y Hy Hnq.
  apply BUnionE in Hx as [Hx|Hx];
  apply BUnionE in Hy as [Hy|Hy].
  - eapply (lo_connected _ _ (lo S)) in Hnq as []...
    left. apply BUnionI1. apply BUnionI1...
    right. apply BUnionI1. apply BUnionI1...
  - left. apply BUnionI2. apply CProdI...
  - right. apply BUnionI2. apply CProdI...
  - eapply (lo_connected _ _ (lo T)) in Hnq as []...
    left. apply BUnionI1. apply BUnionI2...
    right. apply BUnionI1. apply BUnionI2...
Qed.

Theorem loAdd_loset : ∀ S T,
  let S' := LoDisj S 0 in
  let T' := LoDisj T 1 in
  loset (A S' ∪ A T') (S' ⨁ T').
Proof.
  intros S T.
  apply loset_iff_connected_poset. repeat split.
  - apply loAdd_connected.
  - apply loAdd_is_binRel.
  - eapply binRel_is_rel. apply loAdd_is_binRel.
  - apply loAdd_tranr. apply loDisj_disjoint. auto.
  - apply loAdd_irrefl. apply loDisj_disjoint. auto.
Qed.

Definition LoAdd := λ S T,
  let S' := LoDisj S 0 in
  let T' := LoDisj T 1 in
  constr (A S' ∪ A T') (S' ⨁ T') (loAdd_loset S T).
Notation "S + T" := (LoAdd S T) : LoStruct_scope.

Lemma loAdd_well_defined : ∀ S S' T T',
  S ≅ S' → T ≅ T' → S + T ≅ S' + T'.
Proof with eauto; try congruence.
  intros * [f [Hf Hopf]] [g [Hg Hopg]].
  apply inv_bijection in Hf as Hf'.
  apply inv_bijection in Hg as Hg'.
  apply bijection_is_func in Hf' as [Hf' _].
  apply bijection_is_func in Hg' as [Hg' _].
  apply bijection_is_func in Hf as [Hf [Hinjf Hrf]].
  apply bijection_is_func in Hg as [Hg [Hinjg Hrg]].
  assert (H := Hf). destruct H as [_ [Hdf _]].
  assert (H := Hg). destruct H as [_ [Hdg _]].
  destruct (lo S) as [HbrS _]. destruct (lo S') as [HbrS' _].
  destruct (lo T) as [HbrT _]. destruct (lo T') as [HbrT' _].
  set (LoDisj_A S 0 ∪ LoDisj_A T 1) as Dom.
  set (LoDisj_A S' 0 ∪ LoDisj_A T' 1) as Ran.
  set (Func Dom Ran (λ x, match (ixm (π2 x = 0)) with
    | inl _ => <f[π1 x], 0>
    | inr _ => <g[π1 x], 1>
  end)) as F.
  pose proof contra_1_0 as H10.
  assert (Hbi: F: Dom ⟺ Ran). {
    apply meta_bijective.
    - intros x Hx.
      apply BUnionE in Hx as []; destruct (ixm (π2 x = 0));
      apply CProdE1 in H as [a [Ha [b [Hb Heq]]]];
      apply SingE in Hb; subst; zfc_simple.
      + apply BUnionI1. apply CProdI... eapply ap_ran...
      + apply BUnionI2. apply CProdI... eapply ap_ran...
    - intros x1 H1 x2 H2 Heq.
      destruct (ixm (π2 x1 = 0)) as [Hx1|Hx1];
      destruct (ixm (π2 x2 = 0)) as [Hx2|Hx2];
      apply op_iff in Heq as []; subst; try congruence;
      apply BUnionE in H1 as [H1|H1];
      apply BUnionE in H2 as [H2|H2];
      apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]];
      apply CProdE1 in H2 as [c [Hc [d [Hd H2]]]];
      apply SingE in Hb; apply SingE in Hd; subst; zfc_simple;
      apply injectiveE in H...
    - intros y Hy. apply BUnionE in Hy as [];
      apply CProdE1 in H as [a [Ha [b [Hb Hy]]]];
      apply SingE in Hb; subst.
      + exists <f⁻¹[a], 0>. split. apply BUnionI1.
        apply CProdI... eapply ap_ran... zfc_simple.
        destruct (ixm (Embed 0 = 0))... rewrite inv_ran_reduction...
      + exists <g⁻¹[a], 1>. split. apply BUnionI2.
        apply CProdI... eapply ap_ran... zfc_simple.
        destruct (ixm (Embed 1 = 0))... rewrite inv_ran_reduction...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split... unfold LoAdd. simpl.
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  split; intros Hxy;
  destruct (ixm (π2 x = 0));
  destruct (ixm (π2 y = 0));
  apply BUnionE in Hx as [Hx|Hx];
  apply BUnionE in Hy as [Hy|Hy];
  apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]];
  apply CProdE1 in Hy as [c [Hc [d [Hd Hy]]]];
  apply SingE in Hb; apply SingE in Hd; subst; zfc_simple;
  (apply BUnionE in Hxy as [Hxy|Hxy]; [
    apply BUnionE in Hxy as [Hxy|Hxy];
    apply ReplAx in Hxy as [p [Hp H]]; 
    apply op_iff in H as [H1 H2];
    apply op_iff in H1 as [H1 H1'];
    apply op_iff in H2 as [H2 H2']; subst; zfc_simple
  |]).
  - apply HbrS in Hp as H.
    apply CProdE1 in H as [s [Hs [t [Ht H]]]]. subst.
    apply BUnionI1. apply BUnionI1. apply ReplAx.
    exists <f[s], f[t]>. split; zfc_simple. apply Hopf...
  - apply CProdE2 in Hxy as [_ H];
    apply CProdE2 in H as [_ H]; apply SingE in H...
  - apply BUnionI2. apply CProdI; apply CProdI...
    eapply ap_ran... eapply ap_ran...
  - apply CProdE2 in Hxy as [_ H];
    apply CProdE2 in H as [_ H]; apply SingE in H...
  - apply HbrT in Hp as H.
    apply CProdE1 in H as [s [Hs [t [Ht H]]]]. subst.
    apply BUnionI1. apply BUnionI2. apply ReplAx.
    exists <g[s], g[t]>. split; zfc_simple. apply Hopg...
  - apply CProdE2 in Hxy as [H _];
    apply CProdE2 in H as [_ H]; apply SingE in H...
  - apply HbrS' in Hp as H.
    apply CProdE1 in H as [s [Hs [t [Ht H]]]].
    subst. zfc_simple. subst.
    apply BUnionI1. apply BUnionI1. apply ReplAx.
    exists <a, c>. split; zfc_simple. apply Hopf...
  - apply CProdE2 in Hxy as [_ H];
    apply CProdE2 in H as [_ H]; apply SingE in H...
  - apply BUnionI2. apply CProdI; apply CProdI...
  - apply CProdE2 in Hxy as [_ H];
    apply CProdE2 in H as [_ H]; apply SingE in H...
  - apply HbrT' in Hp as H.
    apply CProdE1 in H as [s [Hs [t [Ht H]]]].
    subst. zfc_simple. subst.
    apply BUnionI1. apply BUnionI2. apply ReplAx.
    exists <a, c>. split; zfc_simple. apply Hopg...
  - apply CProdE2 in Hxy as [H _];
    apply CProdE2 in H as [_ H]; apply SingE in H...
Qed.

Definition OtAdd :=
  λ ρ σ, ot (proj ρ + proj σ).
Notation "ρ + σ" := (OtAdd ρ σ) : OrderType_scope.

Lemma otAdd_eq_ot_of_loAdd : ∀ S T, ot S + ot T = ot (S + T)%lo.
Proof.
  intros. apply ot_correct.
  apply loAdd_well_defined; apply proj_ot_id.
Qed.

Theorem otAdd_well_defined : ∀ S S' T T',
  S ≅ S' → T ≅ T' → ot S + ot T = ot S' + ot T'.
Proof.
  intros * HisoS HisoT. do 2 rewrite otAdd_eq_ot_of_loAdd.
  apply ot_correct. apply loAdd_well_defined; auto.
Qed.

Module Import StructureCasting.
Import WoStruct.

Lemma woset_impl_loset : ∀ S : WoStruct, loset (A S) (R S).
Proof. intros. apply wo. Qed.

Lemma ord_loset : ∀ α, is_ord α → loset α (MemberRel α).
Proof. intros α Ho. apply ord_woset. apply Ho. Qed.

Definition OSˡ := LoStruct.parent.
Definition OSʷ := WoStruct.parent.

Definition LOʷ := λ S: WoStruct,
  LoStruct.constr (A S) (R S) (woset_impl_loset S).
Definition WOᵒ := λ α (Ho: is_ord α),
  WoStruct.constr α (MemberRel α) (ord_woset α Ho).
Definition LOᵒ := λ α (Ho: is_ord α),
  LoStruct.constr α (MemberRel α) (ord_loset α Ho).
Definition LOⁿ := λ n : nat, LOᵒ n (embed_is_ord n).

Definition otʷ := λ S: WoStruct, ot (LOʷ S) .
Definition otᵒ := λ α (Ho: is_ord α), ot (LOᵒ α Ho).
Definition otⁿ := λ n : nat, ot (LOⁿ n).

Lemma LOʷ_iso_iff : ∀ S T, (LOʷ S ≅ LOʷ T)%lo ↔ S ≅ T.
Proof. split; intros [f Hf]; exists f; apply Hf. Qed.

Fact otʷ_iff_ord : ∀ S T, otʷ S = otʷ T ↔ ord S = ord T.
Proof.
  intros S T.
  rewrite <- ord_well_defined.
  rewrite <- LOʷ_iso_iff. apply ot_correct.
Qed.

End StructureCasting.

Section OtAddExample.
Import Coq.micromega.Lia.
Import ZFC.lib.NatIsomorphism.

Lemma loAdd_n_m : ∀ n m : nat, (LOⁿ n + LOⁿ m)%lo ≅ LOⁿ (n + m)%nat.
Proof with neauto; try congruence.
  intros. unfold LoAdd. simpl. rewrite add_isomorphic_n.
  assert (Hcontra: ∀ a b ∈ ω, (a + b)%n ∉ a). {
    intros a Ha b Hb. apply leq_iff_not_gt... apply add_ran...
    apply leq_add_enlarge...
  }
  unfold LoDisj_A. simpl.
  set (n × ⎨0⎬ ∪ m × ⎨1⎬) as Dom.
  set (n + m)%n as Ran.
  set (Func Dom Ran (λ x, match (ixm (π2 x = 0)) with
    | inl _ => π1 x
    | inr _ => (n + π1 x)%n
  end)) as F.
  pose proof contra_0_1 as H01.
  assert (Hbi: F: Dom ⟺ Ran). {
    apply meta_bijective.
    - intros x Hx.
      apply BUnionE in Hx as []; destruct (ixm (π2 x = 0));
      apply CProdE1 in H as [a [Ha [b [Hb Heq]]]];
      apply SingE in Hb; subst; zfc_simple; simpl in Ha.
      + apply lt_add_enlarge...
      + apply add_preserve_lt'... eapply ω_trans...
    - intros x1 H1 x2 H2 Heq.
      destruct (ixm (π2 x1 = 0)) as [Hx1|Hx1];
      destruct (ixm (π2 x2 = 0)) as [Hx2|Hx2];
      apply BUnionE in H1 as [H1|H1];
      apply BUnionE in H2 as [H2|H2];
      apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]];
      apply CProdE1 in H2 as [c [Hc [d [Hd H2]]]]; simpl in *;
      apply SingE in Hb; apply SingE in Hd; subst; zfc_simple;
      assert (Haw: a ∈ ω) by (eapply ω_trans; neauto);
      assert (Hcw: c ∈ ω) by (eapply ω_trans; neauto).
      + exfalso. rewrite Heq in Ha. eapply Hcontra; revgoals...
      + exfalso. rewrite <- Heq in Hc. eapply Hcontra; revgoals...
      + apply add_cancel' in Heq...
    - intros y Hy. destruct (classic (y ∈ n)).
      + exists <y, 0>. split. apply BUnionI1. apply CProdI...
        zfc_simple. destruct (ixm (Embed 0 = 0))...
      + assert (Hyw: y ∈ ω). eapply ω_trans... apply add_ran...
        apply leq_iff_not_gt in H...
        apply nat_subtr in H as [d [Hd H]]... subst y.
        apply add_preserve_lt' in Hy...
        exists <d, 1>. split. apply BUnionI2. apply CProdI...
        zfc_simple. destruct (ixm (Embed 1 = 0))...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split; simpl; (rewrite proj_embed_id; [|apply add_ran])...
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  split; intros Hxy;
  destruct (ixm (π2 x = 0));
  destruct (ixm (π2 y = 0));
  apply BUnionE in Hx as [Hx|Hx];
  apply BUnionE in Hy as [Hy|Hy];
  apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]];
  apply CProdE1 in Hy as [c [Hc [d [Hd Hy]]]]; simpl in *;
  apply SingE in Hb; apply SingE in Hd; subst; zfc_simple;
  [(apply BUnionE in Hxy as [Hxy|Hxy]; [
    apply BUnionE in Hxy as [Hxy|Hxy];
    apply ReplAx in Hxy as [p [Hp H]]; 
    apply op_iff in H as [H1 H2];
    apply op_iff in H1 as [H1 H1'];
    apply op_iff in H2 as [H2 H2']; subst; zfc_simple
  |])..| | | |].
  - apply binRelE1 in Hp as [s [Hs [t [Ht [Hp Hst]]]]]. subst. zfc_simple.
    apply binRelI; [apply lt_add_enlarge..|]...
  - apply CProdE2 in Hxy as [_ H].
    apply CProdE2 in H as [_ H]. apply SingE in H...
  - assert (Hcw: c ∈ ω). eapply ω_trans...
    subst. zfc_simple. apply binRelI. apply lt_add_enlarge...
    apply add_preserve_lt'... apply lt_add_enlarge...
  - apply CProdE2 in Hxy as [_ H].
    apply CProdE2 in H as [_ H]. apply SingE in H...
  - apply binRelE1 in Hp as [s [Hs [t [Ht [Hp Hst]]]]]. subst. zfc_simple.
    assert (Htw: t ∈ ω). eapply ω_trans...
    assert (Hsw: s ∈ ω). eapply ω_trans...
    apply binRelI; apply add_preserve_lt'...
  - apply CProdE2 in Hxy as [H _].
    apply CProdE2 in H as [_ H]. apply SingE in H...
  - apply binRelE3 in Hxy. apply BUnionI1. apply BUnionI1.
    apply ReplAx. exists <a, c>. split; zfc_simple. apply binRelI...
  - apply binRelE3 in Hxy. apply BUnionI2. apply CProdI; apply CProdI...
  - apply binRelE3 in Hxy. assert ((n + a)%n ∈ n). eapply nat_trans...
      exfalso. eapply Hcontra; revgoals... eapply ω_trans...
  - apply binRelE3 in Hxy. apply BUnionI1. apply BUnionI2.
    apply ReplAx. exists <a, c>. split; zfc_simple.
    apply add_preserve_lt' in Hxy... apply binRelI...
    eapply ω_trans... eapply ω_trans...
Qed.

Open Scope OrderType_scope.

Example otAdd_1_3 : otⁿ 1 + otⁿ 3 = otⁿ 4.
Proof.
  apply ot_correct. unfold otⁿ.
  erewrite loAdd_well_defined; revgoals.
  apply proj_ot_id. apply proj_ot_id. rewrite loAdd_n_m.
  replace (1 + 3)%nat with 4. reflexivity. lia.
Qed.

Example otAdd_1_ω : otⁿ 1 + ℕ̅ = ℕ̅.
Proof with neauto; try congruence.
  apply ot_correct. unfold otⁿ.
  erewrite loAdd_well_defined; revgoals.
  apply proj_ot_id. apply proj_ot_id.
  unfold LoAdd. simpl. unfold LoDisj_A. simpl.
  set (1 × ⎨0⎬ ∪ ω × ⎨1⎬) as Dom.
  set (Func Dom ω (λ x, match (ixm (π2 x = 0)) with
    | inl _ => 0
    | inr _ => (π1 x)⁺
  end)) as F.
  pose proof contra_0_1 as H01.
  assert (Hbi: F: Dom ⟺ ω). {
    apply meta_bijective.
    - intros x Hx.
      apply BUnionE in Hx as []; destruct (ixm (π2 x = 0));
      apply CProdE1 in H as [a [Ha [b [Hb Heq]]]];
      apply SingE in Hb; subst; zfc_simple; simpl in Ha...
      apply ω_inductive...
    - intros x1 H1 x2 H2 Heq.
      destruct (ixm (π2 x1 = 0)) as [Hx1|Hx1];
      destruct (ixm (π2 x2 = 0)) as [Hx2|Hx2];
      apply BUnionE in H1 as [H1|H1];
      apply BUnionE in H2 as [H2|H2];
      apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]];
      apply CProdE1 in H2 as [c [Hc [d [Hd H2]]]]; simpl in *;
      apply SingE in Hb; apply SingE in Hd; subst; zfc_simple.
      + rewrite one in Ha, Hc.
        apply SingE in Ha; apply SingE in Hc...
      + exfalso. eapply suc_neq_0...
      + exfalso. eapply suc_neq_0...
      + apply suc_injective in Heq...
    - intros y Hy. destruct (classic (y = 0)).
      + exists <0, 0>. split.
        * apply BUnionI1. apply CProdI... apply BUnionI2...
        * zfc_simple. destruct (ixm (Embed 0 = 0))...
      + ω_destruct y. exfalso... exists <n', 1>. split.
        * apply BUnionI2. apply CProdI...
        * zfc_simple. destruct (ixm (Embed 1 = 0))...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split; simpl...
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  split; intros Hxy;
  destruct (ixm (π2 x = 0));
  destruct (ixm (π2 y = 0));
  apply BUnionE in Hx as [Hx|Hx];
  apply BUnionE in Hy as [Hy|Hy];
  apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]];
  apply CProdE1 in Hy as [c [Hc [d [Hd Hy]]]]; simpl in *;
  apply SingE in Hb; apply SingE in Hd; subst; zfc_simple;
  [(apply BUnionE in Hxy as [Hxy|Hxy]; [
    apply BUnionE in Hxy as [Hxy|Hxy];
    apply ReplAx in Hxy as [p [Hp H]]; 
    apply op_iff in H as [H1 H2];
    apply op_iff in H1 as [H1 H1'];
    apply op_iff in H2 as [H2 H2']; subst; zfc_simple
  |])..| | | |].
  - apply binRelE1 in Hp as [s [Hs [t [Ht [Hp Hst]]]]].
    rewrite one in Hs, Ht.
    apply SingE in Hs; apply SingE in Ht; subst.
    exfalso. eapply nat_irrefl; revgoals...
  - apply CProdE2 in Hxy as [_ H].
    apply CProdE2 in H as [_ H]. apply SingE in H...
  - apply binRelI... apply ω_inductive... apply suc_has_0...
  - apply CProdE2 in Hxy as [_ H].
    apply CProdE2 in H as [_ H]. apply SingE in H...
  - apply binRelE1 in Hp as [s [Hs [t [Ht [Hp Hst]]]]]. subst. zfc_simple.
    apply binRelI; [apply ω_inductive..|]...
    apply suc_preserve_lt in Hst...
  - apply CProdE2 in Hxy as [H _].
    apply CProdE2 in H as [_ H]. apply SingE in H...
  - apply binRelE3 in Hxy. exfalso. eapply nat_irrefl...
  - apply binRelE3 in Hxy. apply BUnionI2. apply CProdI; apply CProdI...
  - apply binRelE3 in Hxy. exfalso0.
  - apply binRelE3 in Hxy. apply BUnionI1. apply BUnionI2.
    apply ReplAx. exists <a, c>. split; zfc_simple.
    apply binRelI... apply suc_preserve_lt in Hxy...
Qed.

Example otAdd_ω_1 : ℕ̅ + otⁿ 1 = otᵒ ω⁺ (ord_suc_is_ord ω ω_is_ord).
Proof with neauto; try congruence.
  apply ot_correct. unfold otⁿ.
  erewrite loAdd_well_defined; revgoals.
  apply proj_ot_id. apply proj_ot_id.
  unfold LoAdd. simpl. unfold LoDisj_A. simpl.
  set (ω × ⎨0⎬ ∪ 1 × ⎨1⎬) as Dom.
  set (Func Dom ω⁺ (λ x, match (ixm (π2 x = 0)) with
    | inl _ => π1 x
    | inr _ => ω
  end)) as F.
  pose proof contra_0_1 as H01.
  assert (Hbi: F: Dom ⟺ ω⁺). {
    apply meta_bijective.
    - intros x Hx.
      apply BUnionE in Hx as []; destruct (ixm (π2 x = 0));
      apply CProdE1 in H as [a [Ha [b [Hb Heq]]]];
      apply SingE in Hb; subst; zfc_simple; simpl in Ha...
      apply BUnionI1...
    - intros x1 H1 x2 H2 Heq.
      destruct (ixm (π2 x1 = 0)) as [Hx1|Hx1];
      destruct (ixm (π2 x2 = 0)) as [Hx2|Hx2];
      apply BUnionE in H1 as [H1|H1];
      apply BUnionE in H2 as [H2|H2];
      apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]];
      apply CProdE1 in H2 as [c [Hc [d [Hd H2]]]]; simpl in *;
      apply SingE in Hb; apply SingE in Hd; subst; zfc_simple.
      + subst. exfalso. eapply ord_irrefl; revgoals...
      + subst. exfalso. eapply ord_irrefl; revgoals...
      + rewrite one in Ha, Hc.
        apply SingE in Ha; apply SingE in Hc...
    - intros y Hy. apply BUnionE in Hy as [].
      + exists <y, 0>. split.
        * apply BUnionI1. apply CProdI...
        * zfc_simple. destruct (ixm (Embed 0 = 0))...
      + apply SingE in H. subst. exists <0, 1>. split.
        * apply BUnionI2. apply CProdI... apply BUnionI2...
        * zfc_simple. destruct (ixm (Embed 1 = 0))...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split; simpl...
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  split; intros Hxy;
  destruct (ixm (π2 x = 0));
  destruct (ixm (π2 y = 0));
  apply BUnionE in Hx as [Hx|Hx];
  apply BUnionE in Hy as [Hy|Hy];
  apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]];
  apply CProdE1 in Hy as [c [Hc [d [Hd Hy]]]]; simpl in *;
  apply SingE in Hb; apply SingE in Hd; subst; zfc_simple;
  [(apply BUnionE in Hxy as [Hxy|Hxy]; [
    apply BUnionE in Hxy as [Hxy|Hxy];
    apply ReplAx in Hxy as [p [Hp H]]; 
    apply op_iff in H as [H1 H2];
    apply op_iff in H1 as [H1 H1'];
    apply op_iff in H2 as [H2 H2']; subst; zfc_simple
  |])..| | | |].
  - apply binRelE1 in Hp as [s [Hs [t [Ht [Hp Hst]]]]].
    subst. zfc_simple. apply binRelI; [apply BUnionI1..|]...
  - apply CProdE2 in Hxy as [_ H].
    apply CProdE2 in H as [_ H]. apply SingE in H...
  - apply binRelI... apply BUnionI1...
  - apply CProdE2 in Hxy as [_ H].
    apply CProdE2 in H as [_ H]. apply SingE in H...
  - apply binRelE1 in Hp as [s [Hs [t [Ht [Hp Hst]]]]].
    rewrite one in Hs, Ht.
    apply SingE in Hs; apply SingE in Ht; subst.
    exfalso. eapply nat_irrefl; revgoals...
  - apply CProdE2 in Hxy as [H _].
    apply CProdE2 in H as [_ H]. apply SingE in H...
  - apply binRelE3 in Hxy. apply BUnionI1. apply BUnionI1.
    apply ReplAx. exists <a, c>. split; zfc_simple. apply binRelI...
  - apply binRelE3 in Hxy. apply BUnionI2. apply CProdI; apply CProdI...
  - apply binRelE3 in Hxy. exfalso.
    eapply ord_not_lt_gt; revgoals... eapply ord_is_ords...
  - apply binRelE3 in Hxy. exfalso. eapply ord_irrefl; revgoals...
Qed.

End OtAddExample.

Section OtInvExample.
Import ZFC.EX7_1.
Import ZFC.lib.Real.
Import OrderType.

Fact otInv_finord_id : ∀ ρ, is_ot ρ →
  finite (A (proj ρ)) → -ρ = ρ.
Proof.
  intros ρ [S HS] Hfin. subst. apply ot_correct.
  eapply iso_tran; revgoals. apply proj_ot_id.
  apply parent_iso. apply ex7_19; auto. apply lo. apply lo.
Qed.

Fact otInv_nat_not_id : -ℕ̅ ≠ ℕ̅.
Proof with auto.
  intros H. rewrite otInv_struct in H.
  apply ot_correct in H as [f [Hf Hopf]]. simpl in *.
  eapply woset_no_descending_chain. apply Lt_wellOrder.
  exists f. split. apply bijection_is_func...
  intros n Hn. assert (Hnp: n⁺ ∈ ω). apply ω_inductive...
  apply Hopf... unfold relLt.
  rewrite <- inv_op. apply binRelI...
Qed.

Fact otInv_int_id : -ℤ̅ = ℤ̅.
Proof with auto.
  rewrite otInv_struct. apply ot_correct. simpl.
  exists (Func ℤ ℤ IntAddInv).
  split. apply intAddInv_bijective.
  simpl. intros x Hx y Hy.
  rewrite meta_func_ap, meta_func_ap; revgoals; auto;
  [apply bijection_is_func; apply intAddInv_bijective..|].
  split; intros Hxy.
  - apply inv_op in Hxy. apply intLt_addInv in Hxy...
  - apply intLt_addInv in Hxy... apply inv_op in Hxy...
Qed.

Fact otInv_rat_id : -ℚ̅ = ℚ̅.
Proof with auto.
  rewrite otInv_struct. apply ot_correct. simpl.
  exists (Func ℚ ℚ RatAddInv).
  split. apply ratAddInv_bijective.
  simpl. intros x Hx y Hy.
  rewrite meta_func_ap, meta_func_ap; revgoals; auto;
  [apply bijection_is_func; apply ratAddInv_bijective..|].
  split; intros Hxy.
  - apply inv_op in Hxy. apply ratLt_addInv in Hxy...
  - apply ratLt_addInv in Hxy... apply inv_op in Hxy...
Qed.

Fact otInv_real_id : -ℝ̅ = ℝ̅.
Proof with auto.
  rewrite otInv_struct. apply ot_correct. simpl.
  exists (Func ℝ ℝ RealAddInv).
  split. apply realAddInv_bijective.
  simpl. intros x Hx y Hy.
  rewrite meta_func_ap, meta_func_ap; revgoals; auto;
  [apply bijection_is_func; apply realAddInv_bijective..|].
  split; intros Hxy.
  - apply inv_op in Hxy. apply realLt_addInv in Hxy...
  - apply realLt_addInv in Hxy; [|apply realAddInv_ran..]...
    do 2 rewrite realAddInv_double in Hxy... apply inv_op in Hxy...
Qed.

Fact otAdd_otInv_ℕ : -ℕ̅ + ℕ̅ = ℤ̅.
Proof with neauto; try congruence.
  rewrite otInv_struct. apply ot_correct.
  erewrite loAdd_well_defined; revgoals.
  apply proj_ot_id. apply proj_ot_id.
  unfold LoAdd, LoDisj, LoDisj_A. simpl.
  set (Func (ω × ⎨0⎬ ∪ ω × ⎨1⎬) ℤ (λ x,
    match (ixm (π2 x = 0)) with
    | inl _ => (-ω_Embed[π1 x])%z
    | inr _ => ω_Embed[(π1 x + 1)%n]
    end
  )) as F.
  pose proof contra_0_1 as H01.
  pose proof ω_embed_injective as Hinj.
  pose proof ω_embed_maps_into as [_ [Hωd _]].
  assert (Hcontra: ∀ n m ∈ ω, (-ω_Embed [n])%z ≠ ω_Embed[(m + 1)%n]). {
    intros n Hn m Hm. intros H.
    rewrite ω_embed_n, ω_embed_n, intAddInv in H; nauto; [|apply add_ran]...
    apply int_ident in H; nauto; [|apply add_ran]...
    rewrite add_ident, add_comm, <- add_assoc in H; nauto; [|apply add_ran]...
    rewrite <- add_suc in H; [|apply add_ran]...
    eapply suc_neq_0...
  }
  assert (Hbi: F: ω × ⎨0⎬ ∪ ω × ⎨1⎬ ⟺ ℤ). {
    apply meta_bijective.
    - intros x Hx.
      apply BUnionE in Hx as []; destruct (ixm (π2 x = 0));
      apply CProdE1 in H as [a [Ha [b [Hb Heq]]]];
      apply SingE in Hb; subst; zfc_simple.
      + apply intAddInv_ran. apply ω_embed_ran...
      + apply ω_embed_ran... apply add_ran...
    - intros x1 H1 x2 H2 Heq.
      destruct (ixm (π2 x1 = 0)) as [Hx1|Hx1];
      destruct (ixm (π2 x2 = 0)) as [Hx2|Hx2];
      apply BUnionE in H1 as [H1|H1];
      apply BUnionE in H2 as [H2|H2];
      apply CProdE1 in H1 as [a [Ha [b [Hb H1]]]];
      apply CProdE1 in H2 as [c [Hc [d [Hd H2]]]];
      apply SingE in Hb; apply SingE in Hd; subst; zfc_simple.
      + apply intAddInv_injective in Heq;
        [apply injectiveE in Heq|apply ω_embed_ran..]...
      + exfalso. eapply Hcontra; revgoals...
      + exfalso. eapply Hcontra; revgoals...
      + apply injectiveE in Heq; [| |rewrite Hωd; apply add_ran..]...
        apply add_cancel in Heq...
    - intros y Hy.
      apply pQuotE in Hy as [m [Hm [n [Hn Hy]]]]. subst y.
      destruct (classic (m ⋸ n)).
      + apply nat_subtr in H as [d [Hd Hsubtr]]...
        exists <d, 0>. split. apply BUnionI1. apply CProdI...
        zfc_simple. destruct (ixm (Embed 0 = 0))...
        rewrite ω_embed_n, intAddInv...
        apply int_ident... rewrite add_ident'...
      + destruct (classic (n ∈ m)); [|apply leq_iff_not_gt in H0]...
        apply nat_subtr' in H0 as [d [Hd [Hsubstr H0]]]...
        ω_destruct d. exfalso...
        exists <n', 1>. split. apply BUnionI2. apply CProdI...
        zfc_simple. destruct (ixm (Embed 1 = 0))...
        rewrite ω_embed_n; [|apply add_ran]...
        apply int_ident... apply add_ran...
        rewrite add_ident, <- add_suc, add_comm...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split; simpl...
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  split; intros Hxy;
  destruct (ixm (π2 x = 0));
  destruct (ixm (π2 y = 0));
  apply BUnionE in Hx as [Hx|Hx];
  apply BUnionE in Hy as [Hy|Hy];
  apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]];
  apply CProdE1 in Hy as [c [Hc [d [Hd Hy]]]]; simpl in *;
  apply SingE in Hb; apply SingE in Hd; subst; zfc_simple;
  [(apply BUnionE in Hxy as [Hxy|Hxy]; [
    apply BUnionE in Hxy as [Hxy|Hxy];
    apply ReplAx in Hxy as [p [Hp H]]; 
    apply op_iff in H as [H1 H2];
    apply op_iff in H1 as [H1 H1'];
    apply op_iff in H2 as [H2 H2']; subst; zfc_simple
  |])..| | | |].
  - apply SepE in Hp as [_ [_ Hp]]. apply binRelE3 in Hp.
    rewrite ω_embed_n, ω_embed_n...
    apply intLt_addInv; [apply intAddInv_ran; apply pQuotI..|]...
    rewrite intAddInv_double, intAddInv_double; [|apply pQuotI..]...
    apply intLt... rewrite add_ident, add_ident...
  - apply CProdE2 in Hxy as [_ H].
    apply CProdE2 in H as [_ H]. apply SingE in H...
  - assert (Hc': (c + 1)%n ∈ ω). apply add_ran...
    assert (Hsum: (a + c)%n ∈ ω). apply add_ran...
    rewrite ω_embed_n, ω_embed_n, intAddInv...
    apply intLt... rewrite add_ident, add_comm,
      <- add_assoc, <- add_suc... apply suc_has_0...
  - apply CProdE2 in Hxy as [_ H].
    apply CProdE2 in H as [_ H]. apply SingE in H...
  - apply binRelE1 in Hp as [s [Hs [t [Ht [Hp Hst]]]]].
    assert (Hs': (s + 1)%n ∈ ω). apply add_ran...
    assert (Ht': (t + 1)%n ∈ ω). apply add_ran...
    subst. zfc_simple. rewrite ω_embed_n, ω_embed_n...
    apply intLt... rewrite add_ident, add_ident...
    apply add_preserve_lt...
  - apply CProdE2 in Hxy as [H _].
    apply CProdE2 in H as [_ H]. apply SingE in H...
  - rewrite ω_embed_n, ω_embed_n, intAddInv, intAddInv in Hxy...
    apply intLt in Hxy... rewrite add_ident', add_ident' in Hxy...
    apply BUnionI1. apply BUnionI1. apply ReplAx.
    exists <a, c>. split; zfc_simple.
    simpl. rewrite <- inv_op. apply binRelI...
  - apply BUnionI2. apply CProdI; apply CProdI...
  - assert (Ha': (a + 1)%n ∈ ω). apply add_ran...
    assert (Hsum: (c + a)%n ∈ ω). apply add_ran...
    rewrite ω_embed_n, ω_embed_n, intAddInv in Hxy...
    apply intLt in Hxy... rewrite add_ident, add_comm,
      <- add_assoc, <- add_suc in Hxy...
    exfalso. eapply nat_not_lt_gt; revgoals. apply Hxy.
    apply suc_has_0... apply ω_inductive... nauto.
  - assert (Ha': (a + 1)%n ∈ ω). apply add_ran...
    assert (Hc': (c + 1)%n ∈ ω). apply add_ran...
    rewrite ω_embed_n, ω_embed_n in Hxy...
    apply intLt in Hxy... rewrite add_ident, add_ident in Hxy...
    apply add_preserve_lt in Hxy...
    apply BUnionI1. apply BUnionI2. apply ReplAx.
    exists <a, c>. split; zfc_simple. apply binRelI...
Qed.

End OtInvExample.
