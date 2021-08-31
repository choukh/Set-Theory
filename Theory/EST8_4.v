(** Adapted from "Elements of Set Theory" Chapter 8 **)
(** Coq coding by choukh, Mar 2021 **)

Require ZFC.Lib.NatIsomorphism.
Require Coq.micromega.Lia.

Require Export ZFC.Theory.EST8_3.
Require Import ZFC.Lib.LoStruct.
Import StructureCasting.

(*** EST第八章4：序类型乘法，序类型算术定律 ***)

(* 字典序 *)
Definition LoMul_R := λ S T, BinRel (A S × A T) (λ p1 p2,
  (π2 p1 <ᵣ π2 p2) (R T) ∨
  (π1 p1 <ᵣ π1 p2) (R S) ∧ π2 p1 = π2 p2
).
Notation "S * T" := (LoMul_R S T) : LoStruct_scope.

Lemma loMul_is_binRel : ∀ S T, is_binRel (S * T) (A S × A T).
Proof.
  intros S T x Hx.
  apply binRelE1 in Hx as [a [Ha [b [Hb [Hx _]]]]].
  subst x. apply CPrdI; auto.
Qed.

Lemma loMul_trans : ∀ S T, tranr (S * T).
Proof with eauto.
  intros S T x y z Hxy Hyz.
  destruct (lo S) as [_ [HtrS _]].
  destruct (lo T) as [_ [HtrT _]].
  apply binRelE2 in Hxy as [Hx [Hy [Hxy|[Hxy H1]]]];
  apply binRelE2 in Hyz as [_  [Hz [Hyz|[Hyz H2]]]]; apply binRelI...
  - left. eapply HtrT...
  - left. congruence.
  - left. congruence.
  - right. split. eapply HtrS... congruence.
Qed.

Lemma loMul_irrefl : ∀ S T, irrefl (S * T).
Proof.
  intros S T x H.
  apply binRelE2 in H as [Hx [_ [H|[H _]]]];
  (eapply lo_irrefl; [apply lo|]); eauto.
Qed.

Lemma loMul_connected : ∀ S T, connected (S * T) (A S × A T).
Proof with auto.
  intros S T x Hx y Hy Hnq.
  apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]].
  apply CPrdE1 in Hy as [c [Hc [d [Hd Hy]]]]. subst.
  destruct (classic (a = c)); destruct (classic (b = d)).
  - exfalso. apply Hnq. apply op_iff...
  - eapply (lo_connected _ _ (lo T)) in H0 as []; auto;
    [left|right]; (apply binRelI; [apply CPrdI..|zfc_simple])...
  - eapply (lo_connected _ _ (lo S)) in H as []; auto;
    [left|right]; (apply binRelI; [apply CPrdI..|zfc_simple])...
  - eapply (lo_connected _ _ (lo T)) in H0 as []; auto;
    [left|right]; (apply binRelI; [apply CPrdI..|zfc_simple])...
Qed.

Theorem loMul_loset : ∀ S T, loset (A S × A T) (S * T).
Proof.
  intros S T.
  apply loset_iff_connected_poset. repeat split.
  - apply loMul_connected.
  - apply loMul_is_binRel.
  - eapply binRel_is_rel. apply loMul_is_binRel.
  - apply loMul_trans.
  - apply loMul_irrefl.
Qed.

Definition LoMul := λ S T,
  constr (A S × A T) (S * T) (loMul_loset S T).
Notation "S ⋅ T" := (LoMul S T) : LoStruct_scope.

Lemma loMul_well_defined : ∀ S S' T T',
  S ≅ S' → T ≅ T' → S ⋅ T ≅ S' ⋅ T'.
Proof with eauto; try congruence.
  intros * [f [Hf Hopf]] [g [Hg Hopg]].
  apply bijection_is_func in Hf as [Hf [Hinjf Hrf]].
  apply bijection_is_func in Hg as [Hg [Hinjg Hrg]].
  assert (H := Hf). destruct H as [_ [Hdf _]].
  assert (H := Hg). destruct H as [_ [Hdg _]].
  set (Func (A S × A T) (A S' × A T') (λ x, <f[π1 x], g[π2 x]>)) as F.
  assert (Hbi: F: A S × A T ⟺ A S' × A T'). {
    apply meta_bijection.
    - intros x Hx. apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]].
      subst x. zfc_simple. apply CPrdI; eapply ap_ran...
    - intros x1 H1 x2 H2 Heq.
      apply CPrdE1 in H1 as [a [Ha [b [Hb H1]]]].
      apply CPrdE1 in H2 as [c [Hc [d [Hd H2]]]].
      subst. zfc_simple. apply op_iff in Heq as [H1 H2].
      apply injectiveE in H1... apply injectiveE in H2...
    - intros y Hy.
      apply CPrdE1 in Hy as [a [Ha [b [Hb Hy]]]].
      subst. zfc_simple.
      exists <f⁻¹[a], g⁻¹[b]>. split; zfc_simple.
      + apply CPrdI; eapply ap_ran; eauto;
        apply bijection_is_func; apply inv_bijection;
        apply bijection_is_func...
      + rewrite inv_ran_reduction, inv_ran_reduction...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split... unfold LoMul. simpl.
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]].
  apply CPrdE1 in Hy as [c [Hc [d [Hd Hy]]]].
  subst. zfc_simple. split; intros Hxy.
  - apply binRelI; zfc_simple; [apply CPrdI; eapply ap_ran; eauto..|].
    apply binRelE2 in Hxy as [_ [_ [Hlt|[Hlt Heq]]]]; zfc_simple.
    + left. apply Hopg...
    + right. split... apply Hopf...
  - apply binRelI; zfc_simple; [apply CPrdI..|]...
    apply binRelE2 in Hxy as [_ [_ [Hlt|[Hlt Heq]]]]; zfc_simple.
    + left. apply Hopg...
    + right. split. apply Hopf... apply injectiveE in Heq...
Qed.

Import OrderType.

Definition otMul_spec := λ ρ σ τ,
  ∀ S T, ρ = ot S → σ = ot T → τ = ot (S ⋅ T).
Definition OtMul := λ ρ σ, describe (otMul_spec ρ σ).
Notation "ρ ⋅ σ" := (OtMul ρ σ) : OrderType_scope.

Lemma otMul_spec_intro : ∀ ρ σ ⋵ 𝐎𝐓, otMul_spec ρ σ (ρ ⋅ σ).
Proof.
  intros ρ [S HS] σ [T HT]. apply (desc_spec (otMul_spec ρ σ)).
  rewrite <- unique_existence. split.
  - exists (ot (S ⋅ T)%lo). intros S' T' H1 H2. subst.
    apply ot_correct in H1. apply ot_correct in H2.
    apply ot_correct. apply loMul_well_defined; auto.
  - intros τ1 τ2 H1 H2.
    pose proof (H1 S T HS HT).
    pose proof (H2 S T HS HT). congruence.
Qed.

Lemma otMul_eq_ot_of_loMul : ∀ S T, ot S ⋅ ot T = ot (S ⋅ T)%lo.
Proof. intros. erewrite otMul_spec_intro; auto. Qed.

Theorem otMul_well_defined : ∀ S S' T T',
  S ≅ S' → T ≅ T' → ot S ⋅ ot T = ot S' ⋅ ot T'.
Proof.
  intros * HisoS HisoT. do 2 rewrite otMul_eq_ot_of_loMul.
  apply ot_correct. apply loMul_well_defined; auto.
Qed.

Lemma otMul_iff_loMul : ∀ S T U,
  ot S ⋅ ot T = ot U ↔ (S ⋅ T ≅ U)%lo.
Proof.
  intros. split; intros H.
  - apply ot_correct. rewrite <- otMul_eq_ot_of_loMul. apply H.
  - rewrite otMul_eq_ot_of_loMul. apply ot_correct. apply H.
Qed.

Import Coq.micromega.Lia.
Import ZFC.Lib.NatIsomorphism.
Open Scope omega_scope.

Lemma lt_nba_ndc : ∀ n a b c d ∈ ω, n ≠ 0 →
  a ∈ n → b ∈ d → n ⋅ b + a ∈ n ⋅ d + c.
Proof with nauto.
  intros n Hn a Ha b Hb c Hc d Hd Hn0 Han Hbd.
  apply nat_subtr' in Hbd as [e [He [Hsum He0]]]...
  rewrite <- Hsum, mul_distr, add_assoc; auto; [|apply mul_ran..]...
  apply add_preserve_lt'... apply add_ran...
  apply mul_ran... apply mul_ran...
  apply add_enlarge_lt... apply mul_ran...
  apply mul_enlarge_lt...
Qed.

Lemma neq_nba_ndc : ∀ n a b c d ∈ ω, n ≠ 0 →
  a ∈ n → b ∈ d → n ⋅ b + a ≠ n ⋅ d + c.
Proof with eauto.
  intros n Hn a Ha b Hb c Hc d Hd Hn0 Han Hbd Heq.
  pose proof (lt_nba_ndc n Hn a Ha b Hb c Hc d Hd Hn0 Han Hbd).
  eapply nat_not_lt_self; revgoals...
  apply add_ran... apply mul_ran...
  apply add_ran... apply mul_ran...
Qed.

Lemma lt_nba_nm : ∀ n m a b ∈ ω,
  a ∈ n → b ∈ m → n ⋅ b + a ∈ n ⋅ m.
Proof with nauto.
  intros n Hn m Hm a Ha b Hb Han Hbm.
  apply nat_subtr' in Hbm as [e [He [Hsum Hne]]]...
  rewrite <- Hsum, mul_distr...
  apply add_preserve_lt'... apply mul_ran... apply mul_ran...
  apply mul_enlarge_lt...
Qed.

Lemma loMul_n_m : ∀ n m : nat, (LOⁿ n ⋅ LOⁿ m)%lo ≅ LOⁿ (n * m)%nat.
Proof with neauto; try congruence.
  intros. rewrite mul_isomorphic_n.
  set (Func (n × m) (n ⋅ m) (λ p, n ⋅ π2 p + π1 p)) as F.
  assert (Hbi: F: n × m ⟺ n ⋅ m). {
    apply meta_bijection.
    - intros x Hx.
      apply CPrdE1 in Hx as [a [Ha [b [Hb Hp]]]]. subst. zfc_simple.
      ω_destruct (Embed m)... rewrite H in Hb. exfalso0.
      rename n' into m'. rename Hn' into Hm'. rename Hn'eq into Hm'eq.
      assert (Haw: a ∈ ω). eapply ω_trans...
      assert (Hbw: b ∈ ω). eapply ω_trans...
      rewrite Hm'eq, mul_suc, add_comm; neauto; [|apply mul_ran]...
      assert (Hle: n ⋅ b ⋸ n ⋅ m'). {
        destruct (classic (b = m')) as [|Hnq]. right... left.
        apply mul_preserve_lt'...
        - intros H0. rewrite H0 in Ha. exfalso0.
        - rewrite Hm'eq in Hb. apply BUnionE in Hb as []...
          apply SingE in H...
      }
      destruct Hle.
      + apply add_preserve_lt_trans... apply mul_ran... apply mul_ran...
      + rewrite H. apply add_preserve_lt... apply mul_ran...
    - intros x1 H1 x2 H2 Heq.
      apply CPrdE1 in H1 as [a [Ha [b [Hb H1]]]].
      apply CPrdE1 in H2 as [c [Hc [d [Hd H2]]]].
      subst. zfc_simple.
      assert (Haw: a ∈ ω). eapply ω_trans...
      assert (Hbw: b ∈ ω). eapply ω_trans...
      assert (Hcw: c ∈ ω). eapply ω_trans...
      assert (Hdw: d ∈ ω). eapply ω_trans...
      assert (Hn0: Embed n ≠ 0). {
        intros H0. rewrite H0 in Ha. exfalso0.
      }
      destruct (classic (a = c ∧ b = d)). apply op_iff...
      exfalso. apply not_and_or in H as [];
      apply nat_connected in H as []...
      + apply nat_subtr' in H as [e [He [Hsum Hnq0]]]...
        rewrite (add_comm (n ⋅ b)) in Heq; [|apply mul_ran|]...
        rewrite (add_comm (n ⋅ d)) in Heq; [|apply mul_ran|]...
        rewrite <- Hsum, add_assoc in Heq; [..|apply mul_ran]...
        apply add_cancel' in Heq; [|apply mul_ran|apply add_ran;[|apply mul_ran]|auto]...
        rewrite add_comm in Heq; [..|apply mul_ran]...
        destruct (classic (b = d)). {
          subst. rewrite <- (add_0_r (n ⋅ d)) in Heq at 1; [|apply mul_ran]...
          apply add_cancel' in Heq; [..|apply mul_ran]...
        }
        apply nat_connected in H as []; auto;
        (rewrite <- (add_0_r (n ⋅ b)) in Heq; [|apply mul_ran])...
        * apply (neq_nba_ndc n (embed_ran n) 0 (embed_ran 0) b Hbw e He d Hdw)...
          apply neq_0_gt_0...
        * apply (neq_nba_ndc n (embed_ran n) e He d Hdw 0 (embed_ran 0) b Hbw)...
          rewrite <- Hsum, add_comm in Hc...
          eapply add_shrink_lt; revgoals...
      + apply nat_subtr' in H as [e [He [Hsum Hnq0]]]...
        rewrite (add_comm (n ⋅ b)) in Heq; [|apply mul_ran|]...
        rewrite (add_comm (n ⋅ d)) in Heq; [|apply mul_ran|]...
        rewrite <- Hsum, add_assoc in Heq; [..|apply mul_ran]...
        apply add_cancel' in Heq; [|apply add_ran;[|apply mul_ran]|apply mul_ran|auto]...
        rewrite add_comm in Heq; [..|apply mul_ran]...
        destruct (classic (b = d)). {
          subst. rewrite <- (add_0_r (n ⋅ d)) in Heq at 2; [|apply mul_ran]...
          apply add_cancel' in Heq; [..|apply mul_ran]...
        }
        apply nat_connected in H as []; auto;
        (rewrite <- (add_0_r (n ⋅ d)) in Heq; [|apply mul_ran])...
        * apply (neq_nba_ndc n (embed_ran n) e He b Hbw 0 (embed_ran 0) d Hdw)...
          rewrite <- Hsum, add_comm in Ha...
          eapply add_shrink_lt; revgoals...
        * apply (neq_nba_ndc n (embed_ran n) 0 (embed_ran 0) d Hdw e He b Hbw)...
          apply neq_0_gt_0...
      + apply (neq_nba_ndc n (embed_ran n) a Haw b Hbw c Hcw d Hdw)...
      + apply (neq_nba_ndc n (embed_ran n) c Hcw d Hdw a Haw b Hbw)...
    - intros y Hy.
      assert (Hn0: Embed n ≠ 0). {
        intros H0. rewrite H0, mul_0_l in Hy... exfalso0.
      }
      assert (Hm0: Embed m ≠ 0). {
        intros H0. rewrite H0, mul_0_r in Hy... exfalso0.
      }
      assert (Hyw: y ∈ ω). eapply ω_trans... apply mul_ran...
      generalize dependent Hy.
      ω_induction y; intros Hy.
      + exists <0, 0>. split. apply CPrdI.
        apply neq_0_gt_0... apply neq_0_gt_0...
        zfc_simple. rewrite mul_0_r, add_0_r...
      + rename m0 into k. rename Hm into Hk.
        rewrite suc in Hy...
        apply add_shrink_lt in Hy as Hy'; [..|apply mul_ran]...
        apply IH in Hy' as [p [Hp Heq]].
        apply CPrdE1 in Hp as [a [Ha [b [Hb Hp]]]].
        subst. zfc_simple.
        assert (Haw: a ∈ ω). eapply ω_trans...
        assert (Hbw: b ∈ ω). eapply ω_trans...
        destruct (classic (a + 1 = n)).
        * rewrite add_assoc, H in Hy; [|apply mul_ran|..]...
          rewrite <- (mul_1_r n) in Hy at 2...
          rewrite <- mul_distr in Hy...
          apply mul_preserve_lt' in Hy; [|apply add_ran|..]...
          exists <0, b + 1>. split. apply CPrdI...
          apply neq_0_gt_0... zfc_simple.
          rewrite add_0_r, suc, add_assoc, H...
          rewrite <- (mul_1_r n) at 3...
          apply mul_distr... apply mul_ran...
          apply mul_ran... apply add_ran...
        * apply nat_connected in H as []; [| |apply add_ran|]...
          --- exists <a + 1, b>. split. apply CPrdI... zfc_simple.
              rewrite suc, add_assoc... apply mul_ran...
          --- exfalso. apply (ω_not_dense a)...
              exists n. split... split... rewrite suc...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split; simpl; (rewrite embed_proj_id; [|apply mul_ran])...
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]];
  apply CPrdE1 in Hy as [c [Hc [d [Hd Hy]]]]; subst; zfc_simple.
  assert (Haw: a ∈ ω). eapply ω_trans...
  assert (Hbw: b ∈ ω). eapply ω_trans...
  assert (Hcw: c ∈ ω). eapply ω_trans...
  assert (Hdw: d ∈ ω). eapply ω_trans...
  assert (Hn0: Embed n ≠ 0). {
    intros H0. rewrite H0 in Ha. exfalso0.
  }
  split; intros Hxy.
  - apply binRelE3 in Hxy as []; zfc_simple.
    + apply binRelE3 in H. apply binRelI.
      apply lt_nba_nm... apply lt_nba_nm...
      apply lt_nba_ndc...
    + destruct H as [Hac Hbd]. apply binRelE3 in Hac.
      subst. apply binRelI.
      apply lt_nba_nm... apply lt_nba_nm...
      apply add_preserve_lt'... apply mul_ran...
  - apply binRelE3 in Hxy. apply binRelI.
    apply CPrdI... apply CPrdI... zfc_simple.
    destruct (classic (b = d)); [right|left].
    + split... subst. apply binRelI...
      apply add_preserve_lt' in Hxy... apply mul_ran...
    + apply binRelI... apply nat_connected in H as []...
      exfalso. eapply nat_not_lt_gt; revgoals.
      apply Hxy. apply lt_nba_ndc...
      apply add_ran... apply mul_ran...
      apply add_ran... apply mul_ran...
Qed.

(** 序类型算术定律 **)

Open Scope LoStruct_scope.

Lemma loAdd_assoc : ∀ S T U, S + T + U ≅ S + (T + U).
Proof with auto; try congruence.
  intros. unfold LoAdd at 1 3. simpl. unfold LoDisj_A.
  set (A (S + T) × {0,} ∪ A U × {1,}) as Dom.
  set (A S × {0,} ∪ A (T + U) × {1,}) as Ran.
  set (Func Dom Ran (λ x, match (ixm (π2 x = 0)) with
    | inl _ => match (ixm (π2 (π1 x) = 0)) with
      | inl _ => <π1 (π1 x), 0>
      | inr _ => <<π1 (π1 x), 0>, 1> end
    | inr _ => <<π1 x, 1>, 1> end
  )) as F.
  pose proof contra_1_0 as H10.
  pose proof contra_0_1 as H01.
  assert (Hbi: F: Dom ⟺ Ran). {
    apply meta_bijection.
    - intros x Hx. 
      apply BUnionE in Hx as []; destruct (ixm (π2 x = 0));
      apply CPrdE1 in H as [a [Ha [b [Hb Heq]]]];
      apply SingE in Hb; subst; zfc_simple.
      + apply BUnionE in Ha as []; destruct (ixm (π2 a = 0));
        apply CPrdE1 in H as [c [Hc [d [Hd Heq]]]];
        apply SingE in Hd; subst; zfc_simple.
        * apply BUnionI1. apply CPrdI...
        * apply BUnionI2. apply CPrdI...
          apply BUnionI1. apply CPrdI...
      + apply BUnionI2. apply CPrdI...
        apply BUnionI2. apply CPrdI...
    - intros x1 H1 x2 H2 Heq.
      destruct (ixm (π2 x1 = 0)) as [Hx1|Hx1];
      destruct (ixm (π2 x2 = 0)) as [Hx2|Hx2];
      destruct (ixm (π2 (π1 x1) = 0)) as [Hx11|Hx12];
      destruct (ixm (π2 (π1 x2) = 0)) as [Hx21|Hx22];
      apply op_iff in Heq as []; subst;
      apply BUnionE in H1 as [H1|H1];
      apply BUnionE in H2 as [H2|H2];
      apply CPrdE1 in H1 as [a [Ha [b [Hb H1]]]];
      apply CPrdE1 in H2 as [c [Hc [d [Hd H2]]]];
      apply SingE in Hb; apply SingE in Hd; subst; zfc_simple;
      try (apply op_iff in H as []; congruence);
      apply BUnionE in Ha as [Ha|Ha];
      apply BUnionE in Hc as [Hc|Hc];
      apply CPrdE1 in Ha as [s [Hs [t [Ht Ha]]]];
      apply CPrdE1 in Hc as [u [Hu [v [Hv Hc]]]];
      apply SingE in Ht; apply SingE in Hv; subst; zfc_simple;
      apply op_iff in H as []; subst...
    - intros y Hy. apply BUnionE in Hy as [];
      apply CPrdE1 in H as [a [Ha [b [Hb Hy]]]];
      apply SingE in Hb; subst.
      + exists <<a, 0>, 0>. split.
        apply BUnionI1. apply CPrdI...
        apply BUnionI1. apply CPrdI... zfc_simple.
        destruct (ixm (Embed 0 = 0))...
      + apply BUnionE in Ha as [];
        apply CPrdE1 in H as [c [Hc [d [Hd H]]]];
        apply SingE in Hd; subst; zfc_simple.
        * exists <<c, 1>, 0>. split.
          apply BUnionI1. apply CPrdI...
          apply BUnionI2. apply CPrdI... zfc_simple.
          destruct (ixm (Embed 0 = 0))...
          destruct (ixm (Embed 1 = 0))...
        * exists <c, 1>. split.
          apply BUnionI2. apply CPrdI... zfc_simple.
          destruct (ixm (Embed 1 = 0))...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split... unfold LoAdd. simpl.
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  split; intros Hxy.
  - destruct (ixm (π2 x = 0));
    destruct (ixm (π2 y = 0));
    apply BUnionE in Hx as [Hx|Hx];
    apply BUnionE in Hy as [Hy|Hy];
    apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]];
    apply CPrdE1 in Hy as [c [Hc [d [Hd Hy]]]];
    apply SingE in Hb; apply SingE in Hd; subst; zfc_simple;
    (apply BUnionE in Hxy as [Hxy|Hxy]; [
      apply BUnionE in Hxy as [Hxy|Hxy];
      apply ReplAx in Hxy as H; destruct H as [p [Hp H]]; 
      apply op_iff in H as [H1 H2];
      apply op_iff in H1 as [H1 H1'];
      apply op_iff in H2 as [H2 H2']; subst; zfc_simple
    |]).
    + apply BUnionE in Hp as [Hp|Hp].
      * apply BUnionE in Hp as [Hp|Hp];
        apply ReplAx in Hp as [q [Hq H]];
        apply BUnionE in Ha as [Ha|Ha];
        apply BUnionE in Hc as [Hc|Hc];
        apply CPrdE1 in Ha as [s [Hs [t [Ht Ha]]]];
        apply CPrdE1 in Hc as [u [Hu [v [Hv Hc]]]];
        apply SingE in Ht; apply SingE in Hv; subst; zfc_simple;
        apply op_iff in Ha as []; apply op_iff in Hc as []...
        -- destruct (ixm (Embed 0 = 0))...
           apply BUnionI1. apply BUnionI1.
           apply ReplAx. exists q; split...
        -- destruct (ixm (Embed 1 = 0))...
           apply BUnionI1. apply BUnionI2. apply ReplAx.
           exists <<π1 q, 0>, <π2 q, 0>>. split; zfc_simple.
           apply BUnionI1. apply BUnionI1.
           apply ReplAx. exists q; split...
      * apply CPrdE1 in Hp as [s [Hs [t [Ht Hp]]]];
        apply CPrdE1 in Hs as [u [Hu [v [Hv Hs]]]];
        apply CPrdE1 in Ht as [x [Hx [y [Hy Ht]]]];
        apply SingE in Hv; apply SingE in Hy; subst; zfc_simple.
        destruct (ixm (Embed 0 = 0))...
        destruct (ixm (Embed 1 = 0))...
        apply BUnionI2. apply CPrdI; apply CPrdI...
        apply BUnionI1. apply CPrdI...
    + apply CPrdE1 in Hxy as [s [Hs [t [Ht Hxy]]]].
      apply op_iff in Hxy as [_ H]. subst.
      apply CPrdE2 in Ht as [_ H]. apply SingE in H...
    + apply CPrdE1 in Hxy as [s [Hs [t [Ht Hxy]]]].
      apply op_iff in Hxy as []; subst.
      apply CPrdE2 in Hs as [Hs _].
      apply BUnionE in Hs as [];
      apply CPrdE1 in H as [x [Hx [y [Hy H]]]];
      apply SingE in Hy; subst; zfc_simple.
      * destruct (ixm (Embed 0 = 0))...
        apply BUnionI2. apply CPrdI; apply CPrdI... apply BUnionI2...
      * destruct (ixm (Embed 1 = 0))...
        apply BUnionI1. apply BUnionI2. apply ReplAx.
        exists <<x, 0>, <c, 1>>. split; zfc_simple.
        apply BUnionI2. apply CPrdI; apply CPrdI...
    + apply CPrdE1 in Hxy as [s [Hs [t [Ht Hxy]]]].
      apply op_iff in Hxy as [_ H]. subst.
      apply CPrdE2 in Ht as [_ H]. apply SingE in H...
    + apply BUnionI1. apply BUnionI2. apply ReplAx.
      exists <<π1 p, 1>, <π2 p, 1>>. split; zfc_simple.
      apply BUnionI1. apply BUnionI2...
    + apply CPrdE2 in Hxy as [H _].
      apply CPrdE2 in H as [_ H]. apply SingE in H...
  - destruct (ixm (π2 x = 0));
    destruct (ixm (π2 y = 0));
    apply BUnionE in Hx as [Hx|Hx];
    apply BUnionE in Hy as [Hy|Hy];
    apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]];
    apply CPrdE1 in Hy as [c [Hc [d [Hd Hy]]]];
    apply SingE in Hb; apply SingE in Hd; subst; zfc_simple;
    (apply BUnionE in Hxy as [Hxy|Hxy]; [
      apply BUnionE in Hxy as [Hxy|Hxy];
      apply ReplAx in Hxy as H; destruct H as [p [Hp H]]; 
      apply op_iff in H as [H1 H2];
      destruct (ixm (π2 a = 0));
      destruct (ixm (π2 c = 0));
      apply op_iff in H1 as [H1 H1'];
      apply op_iff in H2 as [H2 H2'];
      subst; zfc_simple
    |]);
    try (apply BUnionE in Ha as [Ha|Ha];
      apply CPrdE1 in Ha as [s [Hs [t [Ht Ha]]]];
      apply SingE in Ht);
    try (apply BUnionE in Hc as [Hc|Hc];
      apply CPrdE1 in Hc as [u [Hu [v [Hv Hc]]]];
      apply SingE in Hv);
    subst; zfc_simple;
    destruct (ixm (Embed 0 = 0));
    destruct (ixm (Embed 1 = 0))...
    + destruct (ixm (Embed 0 = 0))...
      apply BUnionI1. apply BUnionI1. apply ReplAx.
      exists <<s, 0>, <u, 0>>. split; zfc_simple.
      apply BUnionI1. apply BUnionI1...
    + apply BUnionE in Hp as [Hp|Hp].
      * apply BUnionE in Hp as [Hp|Hp];
        apply ReplAx in Hp as [q [Hq H]]; subst; zfc_simple;
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst;
        apply BUnionI1; apply BUnionI1; apply ReplAx;
        exists <<π1 q, 1>, <π2 q, 1>>; split; zfc_simple.
        apply BUnionI1. apply BUnionI2.
        apply ReplAx. exists q. split...
      * apply CPrdE0 in Hp as [_ H]. apply CPrdE0 in H as [_ H].
        rewrite H2 in H. zfc_simple. apply SingE in H...
    + apply CPrdE1 in Hxy as [a [Ha [b [Hb H]]]].
      apply op_iff in H as [_ H]. subst.
      apply CPrdE2 in Hb as [_ H]. apply SingE in H...
    + apply BUnionI1. apply BUnionI1. apply ReplAx.
      exists <<s, 0>, <u, 1>>. split; zfc_simple.
      apply BUnionI2. apply CPrdI; apply CPrdI...
    + apply CPrdE1 in Hxy as [a [Ha [b [Hb H]]]].
      apply op_iff in H as [_ H]. subst.
      apply CPrdE2 in Hb as [_ H]. apply SingE in H...
    + apply CPrdE1 in Hxy as [a [Ha [b [Hb H]]]].
      apply op_iff in H as [H _]. subst.
      apply CPrdE2 in Ha as [_ H]. apply SingE in H...
    + apply BUnionI2. apply CPrdI. apply CPrdI...
      apply BUnionI2. apply CPrdI... apply CPrdI...
    + apply BUnionI2. apply CPrdI. apply CPrdI...
      apply BUnionI2. apply CPrdI... apply CPrdI...
    + apply BUnionI2. apply CPrdI. apply CPrdI...
      apply BUnionI1. apply CPrdI... apply CPrdI...
    + apply BUnionI2. apply CPrdI. apply CPrdI...
      apply BUnionI2. apply CPrdI... apply CPrdI...
    + apply BUnionE in Hp as [Hp|Hp].
      * apply BUnionE in Hp as [Hp|Hp];
        apply ReplAx in Hp as [q [Hq H]]; subst; zfc_simple;
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst;
        apply BUnionI1; apply BUnionI1; apply ReplAx;
        exists <<π1 q, 1>, <π2 q, 1>>; split; zfc_simple.
      * apply CPrdE0 in Hp as [_ H]. apply CPrdE0 in H as [_ H].
        rewrite H2 in H. zfc_simple. apply SingE in H...
    + apply BUnionE in Hp as [Hp|Hp].
      * apply BUnionE in Hp as [Hp|Hp];
        apply ReplAx in Hp as [q [Hq H]]; subst; zfc_simple;
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst;
        apply BUnionI1; apply BUnionI1; apply ReplAx;
        exists <<π1 q, 1>, <π2 q, 1>>; split; zfc_simple.
      * apply CPrdE0 in Hp as [_ H]. apply CPrdE0 in H as [_ H].
        rewrite H2 in H. zfc_simple. apply SingE in H...
    + apply CPrdE2 in Hxy as [H _].
      apply CPrdE2 in H as [_ H]. apply SingE in H...
    + apply CPrdE2 in Hxy as [H _].
      apply CPrdE2 in H as [_ H]. apply SingE in H...
    + apply BUnionE in Hp as [Hp|Hp].
      * apply BUnionE in Hp as [Hp|Hp];
        apply ReplAx in Hp as [q [Hq H]]; subst; zfc_simple;
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst...
        apply BUnionI1. apply BUnionI2. apply ReplAx.
        exists q. split; zfc_simple.
      * apply CPrdE0 in Hp as [H _]. rewrite H1 in H.
        apply CPrdE0 in H as [_ H]. zfc_simple. apply SingE in H...
    + apply BUnionE in Hp as [Hp|Hp].
      * apply BUnionE in Hp as [Hp|Hp];
        apply ReplAx in Hp as [q [Hq H]]; subst; zfc_simple;
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst...
        apply BUnionI1. apply BUnionI2. apply ReplAx.
        exists q. split; zfc_simple.
      * apply CPrdE0 in Hp as [H _]. rewrite H1 in H.
        apply CPrdE0 in H as [_ H]. zfc_simple. apply SingE in H...
    + apply BUnionE in Hp as [Hp|Hp].
      * apply BUnionE in Hp as [Hp|Hp];
        apply ReplAx in Hp as [q [Hq H]]; subst; zfc_simple;
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst...
        apply BUnionI1. apply BUnionI2. apply ReplAx.
        exists q. split; zfc_simple.
      * apply CPrdE0 in Hp as [H _]. rewrite H1 in H.
        apply CPrdE0 in H as [_ H]. zfc_simple. apply SingE in H...
    + apply BUnionE in Hp as [Hp|Hp].
      * apply BUnionE in Hp as [Hp|Hp];
        apply ReplAx in Hp as [q [Hq H]]; subst; zfc_simple;
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst...
        apply BUnionI1. apply BUnionI2. apply ReplAx.
        exists q. split; zfc_simple.
      * apply CPrdE0 in Hp as [H _]. rewrite H1 in H.
        apply CPrdE0 in H as [_ H]. zfc_simple. apply SingE in H...
    + apply CPrdE2 in Hxy as [H _].
      apply CPrdE2 in H as [_ H]. apply SingE in H...
Qed.

Lemma loMul_assoc : ∀ S T U, S ⋅ T ⋅ U ≅ S ⋅ (T ⋅ U).
Proof with auto; try congruence.
  intros. unfold LoMul. simpl.
  set (A S × A T × A U) as Dom.
  set (A S × (A T × A U)) as Ran.
  set (Func Dom Ran (λ x, <π1 (π1 x), <π2 (π1 x), π2 x>>)) as F.
  assert (Hbi: F: Dom ⟺ Ran). {
    apply meta_bijection.
    - intros x Hx.
      apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]].
      apply CPrdE1 in Ha as [c [Hc [d [Hd Ha]]]].
      subst. zfc_simple. apply CPrdI... apply CPrdI...
    - intros x1 H1 x2 H2 Heq.
      apply CPrdE1 in H1 as [a [Ha [b [Hb H1]]]].
      apply CPrdE1 in Ha as [c [Hc [d [Hd Ha]]]].
      apply CPrdE1 in H2 as [s [Hs [t [Ht H2]]]].
      apply CPrdE1 in Hs as [u [Hu [v [Hv Hs]]]].
      subst. zfc_simple.
      apply op_iff in Heq as [H1 H2].
      apply op_iff in H2 as [H2 H3]...
    - intros y Hy.
      apply CPrdE1 in Hy as [a [Ha [b [Hb Hy]]]].
      apply CPrdE1 in Hb as [c [Hc [d [Hd Hb]]]].
      exists <<a, c>, d>. split. apply CPrdI... apply CPrdI...
      subst. zfc_simple.
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split... unfold LoAdd. simpl.
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]].
  apply CPrdE1 in Ha as [c [Hc [d [Hd Ha]]]].
  apply CPrdE1 in Hy as [s [Hs [t [Ht Hy]]]].
  apply CPrdE1 in Hs as [u [Hu [v [Hv Hs]]]].
  split; intros Hxy; apply binRelI; subst; zfc_simple;
  try (apply CPrdI; auto; apply CPrdI; auto).
  - apply binRelE1 in Hxy as [a [Ha [s [Hs [H [Hlt|[Hlt Heq]]]]]]];
    apply op_iff in H as []; subst; zfc_simple.
    + left. apply binRelI. apply CPrdI... apply CPrdI...
      left. zfc_simple.
    + apply binRelE1 in Hlt as [k [Hk [l [Hl [H' [Hlt|[Hlt Heq']]]]]]];
      apply op_iff in H' as []; subst; zfc_simple.
      * left. apply binRelI. apply CPrdI... apply CPrdI...
        right. zfc_simple...
      * right. split...
  - apply binRelE1 in Hxy as [a [Ha [s [Hs [H [Hlt|[Hlt Heq]]]]]]];
    apply op_iff in H as []; subst; zfc_simple.
    + apply binRelE1 in Hlt as [k [Hk [l [Hl [H' [Hlt|[Hlt Heq']]]]]]];
      apply op_iff in H' as []; subst; zfc_simple. left...
      right. split... apply binRelI. apply CPrdI... apply CPrdI...
      left. zfc_simple...
    + apply op_iff in Heq as []; subst.
      right. split... apply binRelI. apply CPrdI... apply CPrdI...
      right. zfc_simple...
Qed.

Lemma loMul_distr : ∀ S T U, S ⋅ (T + U) ≅ S ⋅ T + S ⋅ U.
Proof with auto; try congruence.
  intros. unfold LoMul. unfold LoAdd at 4. simpl.
  unfold LoDisj_A. simpl.
  set (A S × (A T × {0,} ∪ A U × {1,})) as Dom.
  set ((A S × A T) × {0,} ∪ (A S × A U) × {1,}) as Ran.
  set (Func Dom Ran (λ x, match (ixm (π2 (π2 x) = 0)) with
    | inl _ => <π1 x, π1 (π2 x), 0>
    | inr _ => <π1 x, π1 (π2 x), 1> end
  )) as F.
  pose proof contra_0_1 as H01.
  pose proof contra_1_0 as H10.
  assert (Hbi: F: Dom ⟺ Ran). {
    apply meta_bijection.
    - intros x Hx.
      apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]].
      apply BUnionE in Hb as [];
      apply CPrdE1 in H as [c [Hc [d [Hd H]]]];
      apply SingE in Hd; subst; zfc_simple.
      + destruct (ixm (Embed 0 = 0))...
        apply BUnionI1. apply CPrdI... apply CPrdI...
      + destruct (ixm (Embed 1 = 0))...
        apply BUnionI2. apply CPrdI... apply CPrdI...
    - intros x1 H1 x2 H2 Heq.
      apply CPrdE1 in H1 as [a [Ha [b [Hb H1]]]].
      apply CPrdE1 in H2 as [c [Hc [d [Hd H2]]]].
      apply BUnionE in Hb as [];
      apply CPrdE1 in H as [s [Hs [t [Ht Hb]]]];
      apply BUnionE in Hd as [];
      apply CPrdE1 in H as [u [Hu [v [Hv Hd]]]];
      apply SingE in Ht; apply SingE in Hv; subst; zfc_simple;
      destruct (ixm (Embed 0 = 0));
      destruct (ixm (Embed 1 = 0)); try congruence;
      apply op_iff in Heq as [H1 H2];
      apply op_iff in H1 as []...
    - intros y Hy. apply BUnionE in Hy as [];
      apply CPrdE1 in H as [a [Ha [b [Hb H]]]];
      apply CPrdE1 in Ha as [c [Hc [d [Hd Ha]]]];
      apply SingE in Hb; subst; zfc_simple.
      + exists <c, <d, 0>>. split; zfc_simple.
        apply CPrdI... apply BUnionI1. apply CPrdI...
        destruct (ixm (Embed 0 = 0))...
      + exists <c, <d, 1>>. split; zfc_simple.
        apply CPrdI... apply BUnionI2. apply CPrdI...
        destruct (ixm (Embed 1 = 0))...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split... unfold LoAdd. simpl.
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  split; intros Hxy;
  apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]];
  apply CPrdE1 in Hy as [c [Hc [d [Hd Hy]]]];
  apply BUnionE in Hb as [];
  apply CPrdE1 in H as [s [Hs [t [Ht Hb]]]];
  apply BUnionE in Hd as [];
  apply CPrdE1 in H as [u [Hu [v [Hv Hd]]]];
  apply SingE in Ht; apply SingE in Hv; subst; zfc_simple;
  destruct (ixm (Embed 0 = 0));
  destruct (ixm (Embed 1 = 0))...
  - apply BUnionI1. apply BUnionI1. apply ReplAx.
    exists <<a, s>, <c, u>>. split; zfc_simple.
    apply binRelI. apply CPrdI... apply CPrdI...
    apply binRelE3 in Hxy as []; zfc_simple.
    + apply BUnionE in H as [].
      * apply BUnionE in H as []; apply ReplAx in H as [x [Hx H]];
        apply op_iff in H as [H1 H2];
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst... left.
        unfold relLt. rewrite <- (rel_pair (R T))...
        eapply binRel_is_rel. apply lo.
      * apply CPrdE2 in H as [_ H].
        apply CPrdE2 in H as [_ H]. apply SingE in H...
    + destruct H as [H1 H2]. apply op_iff in H2 as []; subst. right...
  - apply BUnionI2. apply CPrdI; apply CPrdI; auto; apply CPrdI...
  - apply binRelE3 in Hxy as []; zfc_simple.
    + apply BUnionE in H as [].
      * apply BUnionE in H as []; apply ReplAx in H as [x [Hx H]];
        apply op_iff in H as [H1 H2];
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst...
      * apply CPrdE2 in H as [_ H].
        apply CPrdE2 in H as [_ H]. apply SingE in H...
    + destruct H as [H1 H2]. apply op_iff in H2 as []; subst...
  - apply BUnionI1. apply BUnionI2. apply ReplAx.
    exists <<a, s>, <c, u>>. split; zfc_simple.
    apply binRelI. apply CPrdI... apply CPrdI...
    apply binRelE3 in Hxy as []; zfc_simple.
    + apply BUnionE in H as [].
      * apply BUnionE in H as []; apply ReplAx in H as [x [Hx H]];
        apply op_iff in H as [H1 H2];
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst... left.
        unfold relLt. rewrite <- (rel_pair (R U))...
        eapply binRel_is_rel. apply lo.
      * apply CPrdE2 in H as [H _].
        apply CPrdE2 in H as [_ H]. apply SingE in H...
    + destruct H as [H1 H2]. apply op_iff in H2 as []; subst...
  - apply binRelI; zfc_simple.
    + apply CPrdI... apply BUnionI1. apply CPrdI...
    + apply CPrdI... apply BUnionI1. apply CPrdI...
    + apply BUnionE in Hxy as [].
      * apply BUnionE in H as []; apply ReplAx in H as [x [Hx H]];
        apply op_iff in H as [H1 H2];
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst...
        apply binRelE1 in Hx as [b [Hb [d [Hd [Hx [Hlt|[Hlt Heq]]]]]]];
        subst; zfc_simple; subst; zfc_simple.
        -- left. apply BUnionI1. apply BUnionI1. apply ReplAx.
           exists <s, u>. split; zfc_simple...
        -- right. split...
      * apply CPrdE2 in H as [_ H].
        apply CPrdE2 in H as [_ H]. apply SingE in H...
  - apply binRelI; zfc_simple.
    + apply CPrdI... apply BUnionI1. apply CPrdI...
    + apply CPrdI... apply BUnionI2. apply CPrdI...
    + left. apply BUnionI2. apply CPrdI; apply CPrdI...
  - apply binRelI; zfc_simple.
    + apply CPrdI... apply BUnionI2. apply CPrdI...
    + apply CPrdI... apply BUnionI1. apply CPrdI...
    + apply BUnionE in Hxy as [].
      * apply BUnionE in H as []; apply ReplAx in H as [x [Hx H]];
        apply op_iff in H as [H1 H2];
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst...
      * apply CPrdE2 in H as [_ H].
        apply CPrdE2 in H as [_ H]. apply SingE in H...
  - apply binRelI; zfc_simple.
    + apply CPrdI... apply BUnionI2. apply CPrdI...
    + apply CPrdI... apply BUnionI2. apply CPrdI...
    + apply BUnionE in Hxy as [].
      * apply BUnionE in H as []; apply ReplAx in H as [x [Hx H]];
        apply op_iff in H as [H1 H2];
        apply op_iff in H1 as [];
        apply op_iff in H2 as []; subst...
        apply binRelE1 in Hx as [b [Hb [d [Hd [Hx [Hlt|[Hlt Heq]]]]]]];
        subst; zfc_simple; subst; zfc_simple.
        -- left. apply BUnionI1. apply BUnionI2. apply ReplAx.
           exists <s, u>. split; zfc_simple...
        -- right. split...
      * apply CPrdE2 in H as [H _].
        apply CPrdE2 in H as [_ H]. apply SingE in H...
Qed.

Import StructureCasting.

Lemma loAdd_0_r : ∀ S, S + LOⁿ 0 ≅ S.
Proof with auto; try congruence.
  intros. unfold LoAdd. simpl.
  unfold LoDisj_A. simpl.
  set (A S × {0,} ∪ 0 × {1,}) as Dom.
  set (Func Dom (A S) (λ x, match (ixm (π2 x = 0)) with
    | inl _ => π1 x
    | inr _ => ∅
  end)) as F.
  pose proof contra_0_1 as H01.
  pose proof contra_1_0 as H10.
  assert (Hbi: F: Dom ⟺ A S). {
    apply meta_bijection.
    - intros x Hx.
      apply BUnionE in Hx as []; destruct (ixm (π2 x = 0));
      apply CPrdE0 in H as []...
      apply SingE in H0... exfalso0. exfalso0.
    - intros x1 H1 x2 H2 Heq.
      destruct (ixm (π2 x1 = 0)) as [Hx1|Hx1];
      destruct (ixm (π2 x2 = 0)) as [Hx2|Hx2];
      apply BUnionE in H1 as [H1|H1];
      apply BUnionE in H2 as [H2|H2];
      apply CPrdE1 in H1 as [a [Ha [b [Hb H1]]]];
      apply CPrdE1 in H2 as [c [Hc [d [Hd H2]]]];
      apply SingE in Hb; apply SingE in Hd; subst; zfc_simple.
      exfalso0. exfalso0. exfalso0.
    - intros y Hy. exists <y, 0>. split.
      + apply BUnionI1. apply CPrdI...
      + zfc_simple. destruct (ixm (Embed 0 = 0))...
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
  apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]];
  apply CPrdE1 in Hy as [c [Hc [d [Hd Hy]]]];
  apply SingE in Hb; apply SingE in Hd; subst; zfc_simple; [(
    apply BUnionE in Hxy as [Hxy|Hxy]; [
      apply BUnionE in Hxy as [Hxy|Hxy];
      apply ReplAx in Hxy as [p [Hp H]]; 
      apply op_iff in H as [H1 H2];
      apply op_iff in H1 as [H1 H1'];
      apply op_iff in H2 as [H2 H2']; subst; zfc_simple
    |]
  )..| | | |]; try exfalso0.
  - unfold relLt. rewrite <- (rel_pair (R S))...
    eapply binRel_is_rel. apply lo.
  - apply CPrdE2 in Hxy as [_ H].
    apply CPrdE2 in H as [_ H]. apply SingE in H...
  - apply BUnionI1. apply BUnionI1. apply ReplAx.
    exists <a, c>. split; zfc_simple...
Qed.

Lemma loAdd_0_l : ∀ S, LOⁿ 0 + S ≅ S.
Proof with auto; try congruence.
  intros. unfold LoAdd. simpl.
  unfold LoDisj_A. simpl.
  set (0 × {0,} ∪ A S × {1,}) as Dom.
  set (Func Dom (A S) (λ x, match (ixm (π2 x = 0)) with
    | inl _ => ∅
    | inr _ => π1 x
  end)) as F.
  pose proof contra_0_1 as H01.
  pose proof contra_1_0 as H10.
  assert (Hbi: F: Dom ⟺ A S). {
    apply meta_bijection.
    - intros x Hx.
      apply BUnionE in Hx as []; destruct (ixm (π2 x = 0));
      apply CPrdE0 in H as []...
      exfalso0. exfalso0. apply SingE in H0...
    - intros x1 H1 x2 H2 Heq.
      destruct (ixm (π2 x1 = 0)) as [Hx1|Hx1];
      destruct (ixm (π2 x2 = 0)) as [Hx2|Hx2];
      apply BUnionE in H1 as [H1|H1];
      apply BUnionE in H2 as [H2|H2];
      apply CPrdE1 in H1 as [a [Ha [b [Hb H1]]]];
      apply CPrdE1 in H2 as [c [Hc [d [Hd H2]]]];
      apply SingE in Hb; apply SingE in Hd; subst; zfc_simple.
      exfalso0. exfalso0. exfalso0.
    - intros y Hy. exists <y, 1>. split.
      + apply BUnionI2. apply CPrdI...
      + zfc_simple. destruct (ixm (Embed 1 = 0))...
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
  apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]];
  apply CPrdE1 in Hy as [c [Hc [d [Hd Hy]]]];
  apply SingE in Hb; apply SingE in Hd; subst; zfc_simple; [(
    apply BUnionE in Hxy as [Hxy|Hxy]; [
      apply BUnionE in Hxy as [Hxy|Hxy];
      apply ReplAx in Hxy as [p [Hp H]]; 
      apply op_iff in H as [H1 H2];
      apply op_iff in H1 as [H1 H1'];
      apply op_iff in H2 as [H2 H2']; subst; zfc_simple
    |]
  )..| | | |]; try exfalso0.
  - unfold relLt. rewrite <- (rel_pair (R S))...
    eapply binRel_is_rel. apply lo.
  - apply CPrdE2 in Hxy as [H _].
    apply CPrdE2 in H as [_ H]. apply SingE in H...
  - apply BUnionI1. apply BUnionI2. apply ReplAx.
    exists <a, c>. split; zfc_simple...
Qed.

Lemma loMul_1_r : ∀ S, S ⋅ LOⁿ 1 ≅ S.
Proof with nauto; try congruence.
  intros. unfold LoMul. simpl.
  set (Func (A S × 1) (A S) π1) as F.
  assert (Hbi: F: A S × 1 ⟺ A S). {
    apply meta_bijection.
    - intros x Hx. apply CPrdE0 in Hx as []...
    - intros x1 H1 x2 H2 Heq.
      apply CPrdE1 in H1 as [a [Ha [b [Hb H1]]]].
      apply CPrdE1 in H2 as [c [Hc [d [Hd H2]]]].
      rewrite one in Hb, Hd.
      apply SingE in Hb. apply SingE in Hd. subst. zfc_simple.
    - intros y Hy. exists <y, 0>. split; zfc_simple.
      apply CPrdI... apply BUnionI2...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split; simpl...
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]].
  apply CPrdE1 in Hy as [c [Hc [d [Hd Hy]]]].
  rewrite one in Hb, Hd.
  apply SingE in Hb. apply SingE in Hd. subst. zfc_simple.
  split; intros Hxy.
  - apply binRelE3 in Hxy as [|[]]; zfc_simple.
    apply SepE2 in H. zfc_simple.
    exfalso. apply (nat_irrefl ∅)...
  - apply binRelI; zfc_simple.
    apply CPrdI... apply BUnionI2...
    apply CPrdI... apply BUnionI2...
    right. split...
Qed.

Lemma loMul_1_l : ∀ S, LOⁿ 1 ⋅ S ≅ S.
Proof with nauto; try congruence.
  intros. unfold LoMul. simpl.
  set (Func (1 × A S) (A S) π2) as F.
  assert (Hbi: F: 1 × A S ⟺ A S). {
    apply meta_bijection.
    - intros x Hx. apply CPrdE0 in Hx as []...
    - intros x1 H1 x2 H2 Heq.
      apply CPrdE1 in H1 as [a [Ha [b [Hb H1]]]].
      apply CPrdE1 in H2 as [c [Hc [d [Hd H2]]]].
      rewrite one in Ha, Hc.
      apply SingE in Ha. apply SingE in Hc. subst. zfc_simple.
    - intros y Hy. exists <0, y>. split; zfc_simple.
      apply CPrdI... apply BUnionI2...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split; simpl...
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]].
  apply CPrdE1 in Hy as [c [Hc [d [Hd Hy]]]].
  rewrite one in Ha, Hc.
  apply SingE in Ha. apply SingE in Hc. subst. zfc_simple.
  split; intros Hxy.
  - apply binRelE3 in Hxy as [|[]]; zfc_simple.
    apply SepE2 in H. zfc_simple.
    exfalso. apply (nat_irrefl ∅)...
  - apply binRelI; zfc_simple.
    apply CPrdI... apply BUnionI2...
    apply CPrdI... apply BUnionI2... left...
Qed.

Lemma loMul_0_r : ∀ S, S ⋅ LOⁿ 0 ≅ LOⁿ 0.
Proof with auto; try congruence.
  intros. unfold LoMul. simpl.
  exists ∅. split; simpl.
  rewrite cprd_0_r. apply empty_bijection.
  intros x Hx. apply CPrdE0 in Hx as [_ H]. exfalso0.
Qed.

Lemma loMul_0_l : ∀ S, LOⁿ 0 ⋅ S ≅ LOⁿ 0.
Proof with auto; try congruence.
  intros. unfold LoMul. simpl.
  exists ∅. split; simpl.
  rewrite cprd_0_l. apply empty_bijection.
  intros x Hx. apply CPrdE0 in Hx as [H _]. exfalso0.
Qed.

Open Scope OrderType_scope.

Theorem otAdd_assoc : ∀ ρ σ τ ⋵ 𝐎𝐓, ρ + σ + τ = ρ + (σ + τ).
Proof with auto.
  intros ρ [S HS] σ [T HT] τ [U HU]. subst.
  do 4 rewrite otAdd_eq_ot_of_loAdd.
  apply ot_correct. apply loAdd_assoc.
Qed.

Theorem otMul_assoc : ∀ ρ σ τ ⋵ 𝐎𝐓, ρ ⋅ σ ⋅ τ = ρ ⋅ (σ ⋅ τ).
Proof with auto.
  intros ρ [S HS] σ [T HT] τ [U HU]. subst.
  do 4 rewrite otMul_eq_ot_of_loMul.
  apply ot_correct. apply loMul_assoc.
Qed.

Theorem otMul_distr : ∀ ρ σ τ ⋵ 𝐎𝐓, ρ ⋅ (σ + τ) = ρ ⋅ σ + ρ ⋅ τ.
Proof with auto.
  intros ρ [S HS] σ [T HT] τ [U HU]. subst.
  rewrite (otAdd_eq_ot_of_loAdd T U).
  rewrite (otMul_eq_ot_of_loMul S T).
  rewrite (otMul_eq_ot_of_loMul S U).
  rewrite otMul_eq_ot_of_loMul.
  rewrite otAdd_eq_ot_of_loAdd.
  apply ot_correct. apply loMul_distr.
Qed.

Theorem otAdd_0_r : ∀ρ ⋵ 𝐎𝐓, ρ + otⁿ 0 = ρ.
Proof with auto.
  intros ρ [S HS]. subst.
  unfold otⁿ. rewrite otAdd_eq_ot_of_loAdd.
  apply ot_correct. apply loAdd_0_r.
Qed.

Theorem otAdd_0_l : ∀ρ ⋵ 𝐎𝐓, otⁿ 0 + ρ = ρ.
Proof with auto.
  intros ρ [S HS]. subst.
  unfold otⁿ. rewrite otAdd_eq_ot_of_loAdd.
  apply ot_correct. apply loAdd_0_l.
Qed.

Theorem otMul_1_r : ∀ρ ⋵ 𝐎𝐓, ρ ⋅ otⁿ 1 = ρ.
Proof with auto.
  intros ρ [S HS]. subst.
  unfold otⁿ. rewrite otMul_eq_ot_of_loMul.
  apply ot_correct. apply loMul_1_r.
Qed.

Theorem otMul_1_l : ∀ρ ⋵ 𝐎𝐓, otⁿ 1 ⋅ ρ = ρ.
Proof with auto.
  intros ρ [S HS]. subst.
  unfold otⁿ. rewrite otMul_eq_ot_of_loMul.
  apply ot_correct. apply loMul_1_l.
Qed.

Theorem otMul_0_r : ∀ρ ⋵ 𝐎𝐓, ρ ⋅ otⁿ 0 = otⁿ 0.
Proof with auto.
  intros ρ [S HS]. subst.
  unfold otⁿ. rewrite otMul_eq_ot_of_loMul.
  apply ot_correct. apply loMul_0_r.
Qed.

Theorem otMul_0_l : ∀ρ ⋵ 𝐎𝐓, otⁿ 0 ⋅ ρ = otⁿ 0.
Proof with auto.
  intros ρ [S HS]. subst.
  unfold otⁿ. rewrite otMul_eq_ot_of_loMul.
  apply ot_correct. apply loMul_0_l.
Qed.
