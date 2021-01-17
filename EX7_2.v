(** Solutions to "Elements of Set Theory" Chapter 7 Part 2 **)
(** Coq coding by choukh, Dec 2020 **)

Require Export ZFC.EST7_4.
Require Import ZFC.lib.FuncFacts.
Require Import ZFC.lib.Real.
Require Import ZFC.lib.NatIsomorphism.
Close Scope Real_scope.

(* ex7_10 see EST7_3 Example α_nat, α_ω *)

Module EX7_11.
Open Scope Int_scope.

Definition IntLtWo := BinRel ℤ (λ a b,
  match (ixm (intNeg a)) with
    | inl _ =>
      match (ixm (intNeg b)) with
        | inl _ => b <𝐳 a
        | inr _ => ⊥
      end
    | inr _ =>
      match (ixm (intNeg b)) with
        | inl _ => ⊤
        | inr _ => a <𝐳 b
      end
  end
).

Lemma intLtWo_irrefl : irrefl IntLtWo.
Proof.
  intros a Haa.
  apply binRelE3 in Haa.
  destruct (ixm (intNeg a));
  eapply intLt_irrefl; eauto.
Qed.

Lemma intLtWo_tranr : tranr IntLtWo.
Proof.
  intros a b c Hab Hbc.
  apply binRelE2 in Hab as [Ha [Hb Hab]].
  apply binRelE2 in Hbc as [_  [Hc Hbc]].
  apply binRelI; auto;
  destruct (ixm (intNeg a));
  destruct (ixm (intNeg b));
  destruct (ixm (intNeg c)); try tauto;
  eapply intLt_tranr; eauto.
Qed.

Lemma intLtWo_connected : connected IntLtWo ℤ.
Proof with auto; try congruence.
  intros a Ha b Hb Hnq.
  destruct (classic (intNeg a)) as [Hna|Hpa];
  destruct (classic (intNeg b)) as [Hnb|Hpb].
  - apply intLt_connected in Hnq as []...
    + right. apply binRelI...
      destruct (ixm (intNeg a)); destruct (ixm (intNeg b))...
    + left. apply binRelI...
      destruct (ixm (intNeg a)); destruct (ixm (intNeg b))...
  - right. apply binRelI...
    destruct (ixm (intNeg a)); destruct (ixm (intNeg b))...
  - left. apply binRelI...
    destruct (ixm (intNeg a)); destruct (ixm (intNeg b))...
  - apply intLt_connected in Hnq as []...
    + left. apply binRelI...
      destruct (ixm (intNeg a)); destruct (ixm (intNeg b))...
    + right. apply binRelI...
      destruct (ixm (intNeg a)); destruct (ixm (intNeg b))...
Qed.

Lemma intLtWo_trich : trich IntLtWo ℤ.
Proof.
  eapply trich_iff. apply binRel_is_binRel.
  apply intLtWo_tranr. split.
  apply intLtWo_irrefl. apply intLtWo_connected.
Qed.

Lemma intLtWo_loset : loset ℤ IntLtWo.
Proof.
  split. apply binRel_is_binRel. split.
  apply intLtWo_tranr. apply intLtWo_trich.
Qed.

Definition NonNegInt := {a ∊ ℤ | λ a, Int 0 ≤ a}.
Notation "ℤ⁰⁺" := NonNegInt.

Definition PosInt := {a ∊ ℤ | intPos}.
Notation "ℤ⁺" := PosInt.

Definition NegInt := {a ∊ ℤ | intNeg}.
Notation "ℤ⁻" := NegInt.

Section ImportOrderedStruct.
Import OrderedStruct.

Definition LtStruct :=
  constr ω Lt (memberRel_is_binRel _).
Definition NonNegIntLtStruct := 
  constr ℤ⁰⁺ (IntLt ⥏ ℤ⁰⁺) (subRel_is_binRel _ _).

Definition PosIntLtStruct := 
  constr ℤ⁺ (IntLt ⥏ ℤ⁺) (subRel_is_binRel _ _).
Definition NegIntLtStruct := 
  constr ℤ⁻ (IntLt ⥏ ℤ⁻)⁻¹ (inv_is_binRel _ _ (subRel_is_binRel _ _)).

Lemma ω_embed_ran_nn : ∀n ∈ ω, ω_Embed[n] ∈ ℤ⁰⁺.
Proof with eauto.
  intros n Hn. apply SepI.
  - eapply ap_ran... apply ω_embed_maps_into.
  - ω_destruct n; subst n.
    + right. rewrite <- zero, ω_embed...
    + left. rewrite suc_isomorphic_ω, ω_embed... apply intPos_sn.
Qed.

Lemma ω_embed_bijective : ω_Embed: ω ⟺ ℤ⁰⁺.
Proof with neauto; try congruence.
  apply bijection_is_func.
  destruct ω_embed_maps_into as [Hf [Hd Hr]].
  assert (Hrz: ran ω_Embed ⊆ ℤ⁰⁺). {
    intros a Ha.
    apply ranE in Ha as [n Hp]. apply domI in Hp as Hn.
    apply func_ap in Hp... subst a. rewrite Hd in Hn.
    apply ω_embed_ran_nn...
  }
  split. split... split. apply ω_embed_injective.
  apply sub_antisym... intros a Ha.
  apply SepE in Ha as [Ha [Hp|H0]].
  + apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]]. subst a.
    rewrite ω_embed_subtr in Hp...
    rewrite <- (intAddInv_annih (ω_Embed[n])) in Hp;
      [|apply ω_embed_ran]...
    apply intAdd_preserve_lt in Hp;
      [..|apply intAddInv_ran]; [|apply ω_embed_ran..]...
    apply ω_embed_lt in Hp...
    apply nat_subtr in Hp as [d [Hdz [Hsum _]]]...
    apply (ranI _ d). apply func_point...
    rewrite ω_embed_n... apply int_ident...
    rewrite add_comm, add_ident...
  + subst a. apply (ranI _ 0). apply func_point...
    rewrite Hd... rewrite ω_embed...
Qed.

Lemma iso_Lt_nonNegIntLt : LtStruct ≅ NonNegIntLtStruct.
Proof with auto.
  exists ω_Embed. simpl. split. apply ω_embed_bijective.
  intros n Hn m Hm. split; intros Hlt.
  - apply SepI. apply binRelE3 in Hlt.
    apply ω_embed_lt in Hlt...
    apply CProdI; apply ω_embed_ran_nn...
  - apply binRelI... apply ω_embed_lt...
    apply SepE1 in Hlt...
Qed.

Lemma nonNegInt_woset : woset ℤ⁰⁺ (IntLt ⥏ ℤ⁰⁺).
Proof.
  cut (wo NonNegIntLtStruct). auto.
  eapply iso_wo. apply iso_Lt_nonNegIntLt.
  apply Lt_wellOrder.
Qed.

Lemma posInt_woset : woset ℤ⁺ (IntLt ⥏ ℤ⁺).
Proof with auto.
  assert (Hsub: ℤ⁺ ⊆ ℤ⁰⁺). {
    intros a Ha. apply SepE in Ha as [Ha Hpa]. apply SepI...
  }
  replace (IntLt ⥏ ℤ⁺) with (IntLt ⥏ ℤ⁰⁺ ⥏ ℤ⁺).
  eapply subRel_woset. apply nonNegInt_woset. apply Hsub.
  rewrite subRel_absorption...
Qed.

Lemma intAddInv_bijective : (Func ℤ⁺ ℤ⁻ IntAddInv): ℤ⁺ ⟺ ℤ⁻.
Proof with auto; try congruence.
  apply meta_bijective.
  - intros a Ha. apply SepE in Ha as [Ha Hpos].
    apply SepI. apply intAddInv_ran... apply intPos_neg...
  - intros a Ha b Hb Heq.
    apply SepE1 in Ha. apply SepE1 in Hb.
    rewrite <- intAddInv_double, <- (intAddInv_double b)...
  - intros b Hb. apply SepE in Hb as [Hb Hneg].
    exists (-b). split. apply SepI. apply intAddInv_ran...
    apply intNeg_pos... apply intAddInv_double...
Qed.

Lemma iso_posIntLt_negIntLt : PosIntLtStruct ≅ NegIntLtStruct.
Proof with auto; try congruence.
  set (Func ℤ⁺ ℤ⁻ IntAddInv) as f.
  pose proof intAddInv_bijective as Hf.
  exists f. simpl. split...
  intros a Ha b Hb. split; intros Hlt.
  - apply SepE in Hlt as [Hlt _].
    unfold relLt, NegIntLtStruct.
    simpl. rewrite <- inv_op.
    unfold f. rewrite meta_func_ap, meta_func_ap;
      auto; [|apply bijection_is_func..]...
    apply SepE in Ha as [Ha Hpa].
    apply SepE in Hb as [Hb Hpb].
    apply SepI. apply intLt_addInv in Hlt...
    apply CProdI; (apply SepI;
      [apply intAddInv_ran|apply intPos_neg])...
  - unfold relLt, NegIntLtStruct in Hlt.
    simpl in Hlt. rewrite <- inv_op in Hlt.
    apply SepE in Hlt as [Hlt _].
    unfold f in Hlt. rewrite meta_func_ap, meta_func_ap in Hlt;
      auto; [|apply bijection_is_func..]...
    apply SepE in Ha as [Ha Hpa].
    apply SepE in Hb as [Hb Hpb].
    apply SepI. apply intLt_addInv...
    apply CProdI; apply SepI...
Qed.

Lemma negInt_woset : woset ℤ⁻ (IntLt ⥏ ℤ⁻)⁻¹.
Proof with auto.
  cut (wo NegIntLtStruct)...
  eapply iso_wo. apply iso_posIntLt_negIntLt.
  apply posInt_woset.
Qed.

Theorem intLtWo_woset : woset ℤ IntLtWo.
Proof with neauto; try congruence.
  split. apply intLtWo_loset.
  intros Z Hne Hsub.
  set {a ∊ Z | λ a, Int 0 ≤ a} as Z'.
  destruct (classic (⦿ Z')) as [Hne'|He].
  - destruct nonNegInt_woset as [_ Hmin].
    specialize Hmin with Z' as [m [Hm Hmin]]... {
      intros a Ha. apply SepE in Ha as [Ha Hnn].
      apply Hsub in Ha. apply SepI...
    }
    apply SepE in Hm as [Hm Hnn].
    exists m. split... intros a Ha.
    apply Hsub in Hm as Hmz. apply Hsub in Ha as Haz.
    destruct (classic (m = a)) as [Heqm|Hnqm]. right... left.
    apply binRelI; [apply Hsub..|]...
    destruct (ixm (intNeg m));
    destruct (ixm (intNeg a))...
    + exfalso. apply intNonNeg_iff in Hnn...
    + apply intNonNeg_iff in Hnn...
    + assert (a ∈ Z'). { apply SepI... apply intNonNeg_iff... }
      apply Hmin in H as []... apply SepE1 in H...
  - assert (Hneg: Z ⊆ ℤ⁻). {
      intros a Ha. apply Hsub in Ha as Haz.
      destruct (classic (intNeg a))... apply SepI...
      exfalso. apply He. exists a. apply SepI... apply intNonNeg_iff...
    }
    destruct negInt_woset as [_ Hmin].
    specialize Hmin with Z as [m [Hm Hmin]]...
    exists m. split... intros a Ha.
    apply Hsub in Hm as Hmz. apply Hsub in Ha as Haz.
    apply Hneg in Ha as Ha'. apply SepE2 in Ha'.
    destruct (classic (m = a)) as [Heqm|Hnqm]. right... left.
    apply binRelI; [apply Hsub..|]...
    destruct (ixm (intNeg m));
    destruct (ixm (intNeg a))...
    apply Hmin in Ha as []...
    rewrite <- inv_op in H. apply SepE1 in H...
Qed.

End ImportOrderedStruct.

Lemma int_0_not_neg : intNeg (Int 0) → ⊥.
Proof. intros. eapply intLt_irrefl; eauto. Qed.

Lemma int_1_not_neg : intNeg (Int 1) → ⊥.
Proof.
  intros. assert (intPos (Int 1)) by apply intPos_sn.
  eapply intLt_irrefl; eapply intLt_tranr; eauto.
Qed.

Lemma int_sn_not_neg : ∀ n, intNeg (Int (S n)) → ⊥.
Proof.
  intros. assert (intPos (Int (S n))) by apply intPos_sn.
  eapply intLt_irrefl; eapply intLt_tranr; eauto.
Qed.

Lemma int_n_not_neg : ∀ n, intNeg (Int n) → ⊥.
Proof with eauto.
  intros. destruct n.
  apply int_0_not_neg... eapply int_sn_not_neg...
Qed.

Lemma int_0_minimum : ∀a ∈ ℤ, ¬ (a <ᵣ Int 0) IntLtWo.
Proof.
  intros a Ha Hlt.
  apply binRelE3 in Hlt.
  destruct (ixm (intNeg a)); destruct (ixm (intNeg (Int 0)));
  auto; apply int_0_not_neg; auto.
Qed.

Import WOStruct.
Import WOStruct.EpsilonImage.

Definition ℤWoS := constr ℤ IntLtWo intLtWo_woset.
Definition E := E ℤWoS.

Fact e_int_0 : E[Int 0] = 0.
Proof with neauto.
  apply ExtAx. split; intros Hx; [|exfalso0].
  apply e_elim in Hx...
  destruct Hx as [s [Hs [Hlt _]]].
  exfalso. eapply int_0_minimum...
Qed.

Fact e_int_1 : E[Int 1] = 1.
Proof with neauto; try congruence.
  pose proof int_0_not_neg as H0nn.
  pose proof int_1_not_neg as H1nn.
  apply ExtAx. split; intros Hx.
  - apply e_elim in Hx...
    destruct Hx as [s [Hs [Hlt [Heq _]]]].
    destruct (classic (s = Int 0)). {
      subst. fold E. rewrite e_int_0. apply BUnionI2...
    }
    apply intLtWo_connected in H as []... {
      exfalso. eapply int_0_minimum...
    }
    apply binRelE2 in H. apply binRelE2 in Hlt.
    destruct (ixm (intNeg (Int 0)));
    destruct (ixm (intNeg (Int 1)));
    destruct (ixm (intNeg s))... tauto.
    destruct Hlt as [_ [_ H1]]. destruct H as [_ [_ H2]].
    exfalso. apply intLt_iff_leq_suc in H2...
    rewrite intAdd_ident' in H2...
    destruct H2; eapply intLt_irrefl.
    eapply intLt_tranr... subst...
  - apply BUnionE in Hx as []. exfalso0.
    apply SingE in H. subst x.
    eapply (e_intro _ _ (Int 0))...
    + apply binRelI...
      destruct (ixm (intNeg (Int 0)));
      destruct (ixm (intNeg (Int 1)))... apply intPos_sn.
    + fold E. rewrite e_int_0...
Qed.

Fact e_int_n : ∀ n, E[Int n] = n.
Proof with neauto; try congruence; try tauto.
  induction n. apply e_int_0.
  pose proof (int_n_not_neg n) as Hnnn.
  pose proof (int_sn_not_neg n) as Hnnsn.
  apply ExtAx. split; intros Hx.
  - apply e_elim in Hx...
    destruct Hx as [s [Hs [Hlt [Heq _]]]]. subst x. fold E.
    apply binRelE3 in Hlt.
    destruct (ixm (intNeg s));
    destruct (ixm (intNeg (Int (S n))))...
    destruct ω_embed_bijective as [[Hf _] [Hd Hr]].
    assert (Hsr: s ∈ ran ω_Embed). {
      rewrite Hr. apply SepI... apply intNonNeg_iff...
    }
    apply ranE in Hsr as [m Hp].
    apply domI in Hp as Hm. apply func_ap in Hp... subst s.
    rewrite <- ω_embed in Hlt... apply ω_embed_lt in Hlt...
    rewrite suc_isomorphic_n, proj_embed_id in *;
      [|apply ω_inductive; apply embed_ran..].
    apply BUnionE in Hlt as [].
    + apply BUnionI1.
      rewrite <- (proj_embed_id m), ω_embed, <- IHn...
      apply e_ap_order... apply binRelI...
      destruct (ixm (intNeg (Int m)));
      destruct (ixm (intNeg (Int n)))...
      eapply int_n_not_neg... eapply intLtI...
      rewrite add_ident, add_ident, (proj_embed_id m)...
    + apply SingE in H. rewrite H, ω_embed, IHn...
  - assert (Hnsn: Int n <𝐳 Int (S n)). {
      apply intLtI... rewrite add_ident, add_ident...
      rewrite suc_isomorphic_n, proj_embed_id...
      apply ω_inductive. apply embed_ran.
    }
    rewrite suc_isomorphic_n, proj_embed_id in Hx;
      [|apply ω_inductive; apply embed_ran].
    apply BUnionE in Hx as [].
    + rewrite <- IHn in H.
      apply e_elim in H...
      destruct H as [s [Hs [Hlt [Heq _]]]].
      eapply e_intro...
      apply binRelE3 in Hlt.
      apply binRelI...
      destruct (ixm (intNeg s));
      destruct (ixm (intNeg (Int n)));
      destruct (ixm (intNeg (Int (S n))))...
      eapply intLt_tranr...
    + apply SingE in H. subst x. rewrite <- IHn.
      apply (e_intro _ _ (Int n))...
      apply binRelI...
      destruct (ixm (intNeg (Int n)));
      destruct (ixm (intNeg (Int (S n))))...
Qed.

Fact e_int_n1 : E[-Int 1] = ω.
Proof with neauto.
  apply ExtAx. split; intros Hx.
  - apply e_elim in Hx...
    destruct Hx as [s [Hs [Hlt [Heq _]]]]. fold E in Heq.
    apply binRelE3 in Hlt.
    destruct (ixm (intNeg s)) as [Hns|Hnns];
    destruct (ixm (intNeg (-Int 1))) as [Hnn1|Hnnn1].
    + apply intLt_iff_leq_suc in Hlt...
      rewrite intAdd_comm, intAddInv_annih in Hlt...
      apply intNonNeg_iff in Hlt...
      apply intNonNeg_ex_nat in Hlt as [n Heqs]... subst s.
      rewrite e_int_n in Heq. subst x...
    + tauto.
    + apply intNonNeg_ex_nat in Hnns as [n Heqs]... subst s.
      rewrite e_int_n in Heq. subst x...
    + exfalso. assert (intNeg (-Int 1)) by nauto...
  - eapply (e_intro _ _ (Int x))...
    + apply binRelI...
      destruct (ixm (intNeg (Int x))) as [Hnx|Hnnx];
      destruct (ixm (intNeg (-Int 1))) as [Hnn1|Hnnn1]...
      * exfalso. apply intLt in Hnx...
        rewrite add_ident, add_ident in Hnx... exfalso0.
      * exfalso. assert (intNeg (-Int 1)) by nauto...
    + rewrite e_int_n, proj_embed_id...
Qed.

Lemma intAdd_n2_n : - Int 2 + Int 1 = - Int 1.
Proof with nauto.
  unfold Int. rewrite intAddInv, intAddInv, 
    intAdd_m_n_p_q, add_ident, add_ident'...
  apply int_ident... rewrite add_ident', add_1_1...
Qed.

Fact e_int_n2 : E[-Int 2] = ω⁺.
Proof with neauto; try congruence.
  pose proof intLtWo_woset as Hwo.
  apply ExtAx. split; intros Hx.
  - apply e_elim in Hx...
    destruct Hx as [s [Hs [Hlt [Heq _]]]]. fold E in Heq.
    apply binRelE3 in Hlt.
    destruct (ixm (intNeg s)) as [Hns|Hnns];
    destruct (ixm (intNeg (-Int 2))) as [Hnn2|Hnnn2].
    + apply intLt_iff_leq_suc in Hlt as []; nauto;
      rewrite intAdd_n2_n in H.
      * apply intLt_iff_leq_suc in H...
        rewrite intAdd_comm, intAddInv_annih in H...
        apply intNonNeg_iff in H...
      * subst s x. rewrite e_int_n1...
    + tauto.
    + apply intNonNeg_ex_nat in Hnns as [n Heqs]...
      subst s x. rewrite e_int_n. apply BUnionI1...
    + assert (intNeg (- Int 2))...
  - apply BUnionE in Hx as [Hx|Hx].
    + eapply (e_intro _ _ (Int x)); revgoals...
      fold E. rewrite e_int_n, proj_embed_id... apply binRelI...
      destruct (ixm (intNeg (Int x))) as [Hnx|Hnnx];
      destruct (ixm (intNeg (-Int 2))) as [Hnn2|Hnnn2]...
      * exfalso. eapply int_n_not_neg...
      * assert (intNeg (- Int 2))...
    + apply SingE in Hx. subst x.
      eapply (e_intro _ _ (-Int 1)); revgoals...
      fold E. rewrite e_int_n1... apply binRelI...
      destruct (ixm (intNeg (-Int 1))) as [Hnn1|Hnnn1];
      destruct (ixm (intNeg (-Int 2))) as [Hnn2|Hnnn2]...
      * unfold Int. rewrite intAddInv, intAddInv...
        apply intLt... rewrite add_ident', add_ident'...
        apply suc_has_n.
      * assert (intNeg (- Int 2))...
Qed.

End EX7_11.

(* ex7_12 see EST7_3 Module ImageRel *)
(* ex7_13 see EST7_3 Theorem wo_iso_unique *)

Section EX7_14.
Import OrderedStruct.

Let head := λ x S, head x (A S) (R S).

Example ex7_14 : ∀ S, po S →
  let F := Func (A S) (𝒫 (A S)) (λ x, head x S) in
  let T := constr (ran F) (SubsetRel (ran F)) (subsetRel_is_binRel _) in
  F:ₒₑ S ⟺ T.
Proof with eauto.
  intros * [_ [_ [Htr Hir]]] F T.
  assert (HfP: F: A S ⇔ (𝒫 (A S))). {
    apply meta_injective.
    + intros x Hx. apply PowerAx. intros t Ht.
      apply SepE1 in Ht...
    + intros x1 Hx1 x2 Hx2 Heq.
      assert (H1: x1 ∈ head x1 S). { apply SepI... right... }
      assert (H2: x2 ∈ head x2 S). { apply SepI... right... }
      rewrite Heq in H1. apply SepE2 in H1 as []...
      rewrite <- Heq in H2. apply SepE2 in H2 as []...
      exfalso. eapply Hir. eapply Htr...
  }
  assert (HfS: F: A S ⟺ A T). {
    destruct HfP as [Hif [Hd _]]. split...
  }
  split...
  apply bijection_is_func in HfS as [HfS _].
  apply injection_is_func in HfP as [HfP _].
  intros x Hx y Hy. split; intros Hxy.
  - apply binRelI. eapply ap_ran... eapply ap_ran... split.
    + intros a Ha. unfold F.
      rewrite meta_func_ap... apply SepI.
      * destruct HfP as [Hf [Hd Hr]]. rewrite <- Hd in Hx.
        apply func_correct in Hx... apply ranI in Hx.
        apply Hr in Hx. apply PowerAx in Hx. apply Hx...
      * unfold F in Ha. rewrite meta_func_ap in Ha...
        apply SepE2 in Ha. left. eapply relLe_lt_tranr...
    + unfold F. rewrite meta_func_ap, meta_func_ap... intros Heq.
      assert (y ∈ head y S). { apply SepI... right... }
      rewrite <- Heq in H. apply SepE2 in H as []...
      * eapply Hir. eapply Htr...
      * eapply Hir. subst...
  - apply binRelE3 in Hxy as [Hsub Hnq].
    assert (x ∈ F[x]). {
      unfold F. rewrite meta_func_ap...
      apply SepI... right...
    }
    apply Hsub in H.
    unfold F in H. rewrite meta_func_ap in H...
    apply SepE in H as [_ []]... exfalso. congruence.
Qed.

End EX7_14.

Import WOStruct.
Import WOStruct.EpsilonImage.

(* ex7_15_a 良序结构不与自身的任意前节同构 *)
Lemma wo_not_iso_seg : ∀ S, ∀t ∈ A S, S ≇ Seg t S.
Proof with eauto.
  intros S t Ht Hiso.
  apply ord_well_defined in Hiso.
  apply (ord_irrefl (ord S))...
  rewrite Hiso at 1. eapply ordI...
  symmetry. apply seg_α...
Qed.

(* ex7_15_b 良序结构的同构关系具有至多三歧性 *)
Theorem wo_iso_at_most_trich : ∀ S T,
  at_most_trich (∃t ∈ A S, Seg t S ≅ T) (S ≅ T) (∃t ∈ A T, S ≅ Seg t T).
Proof with eauto.
  repeat split.
  - intros [[t [Ht H1]] H2].
    eapply wo_not_iso_seg... rewrite H1...
  - intros [[t [Ht H1]] H2].
    eapply wo_not_iso_seg... rewrite <- H1. symmetry...
  - intros [[s [Hs H1]] [t [Ht H2]]].
    apply ord_well_defined in H1.
    apply ord_well_defined in H2.
    rewrite seg_α in H1, H2...
    apply ordI in H1... symmetry in H2.
    apply ordI in H2...
    apply (ord_irrefl (ord S))... eapply ord_trans...
Qed.

(* ex7_16_1 see EST7_4 Lemma ord_suc_preserve_lt *)
(* ex7_16_2 see EST7_4 Lemma ord_suc_injective *)

(* ex7_17 子结构的序数小于等于原结构的序数 *)
Theorem ord_of_sub_struct_leq : ∀ S T, S ⊑ T → ord S ≤ ord T.
Proof with eauto.
  intros * [Has Hrs].
  destruct (classic (ord S = ord T))...
  apply ord_connected in H as []... exfalso.
  apply ord_lt_elim in H as [t [Ht [f [Hf Hoe]]]].
  apply bijection_is_func in Hf as [Hf _].
  destruct (wo S) as [Hlo Hmin].
  set {x ∊ A S | λ x, (f[x] <ᵣ x) (R S)} as B.
  pose proof (Hmin B) as [m [Hm Hle]].
  - exists t. apply SepI...
    assert (Hft: f[t] ∈ A (Seg t S)). {
      eapply ap_ran... apply Has...
    }
    apply SepE2 in Hft...
  - intros x Hx. apply SepE1 in Hx...
  - apply SepE in Hm as [Hm Hlt]. apply Has in Hm.
    assert (Hsub: A (Seg t S) ⊆ A S). {
      intros x Hx. apply SepE1 in Hx...
    }
    assert (Hfm: f[m] ∈ A S). {
      apply Hsub. eapply ap_ran...
    }
    assert (Hfmb: f[m] ∈ B). {
      apply SepI... rewrite Hrs in Hlt. apply SepE1 in Hlt.
      apply Hoe in Hlt... apply SepE1 in Hlt... apply Has...
    }
    apply Hle in Hfmb. eapply lo_not_leq_gt...
Qed.

(* ex7_18 see EST7_4 limit ordinal *)
(* ex7_19 see EX7_1 Section EX7_19 *)
(* ex7_20 see EX7_1 Section EX7_20 *)
(* ex7_21 see lib/ZornsLemma *)
(* ex7_22 see lib/ZornsLemma *)
