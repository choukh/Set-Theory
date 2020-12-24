(** Solutions to "Elements of Set Theory" Chapter 7 Part 1 **)
(** Coq coding by choukh, Nov 2020 **)

Require Export ZFC.EST7_2.
Require Import ZFC.lib.Real.
Require Import ZFC.lib.Cardinal.
Require Import ZFC.lib.WosetMin.
Import WosetMin.SimpleVer.

(* ex7_1
  (a) No (b) No
    let < be divisibility
    let A = {2, 3, 6}
    let B = {3, 3, 6}
*)
(* ex7_2 see EST7_1 Fact inv_partialOrder *)
(* ex7_3 Combination (n, 2) = n! / 2!(n - 2)! = (1/2)n(n-1) *)
(* ex7_4 skip *)

(* ex7_5 良序集到自身的保序映射的值不可能比输入小 *)
Lemma self_order_preserving_func_progressive :
  ∀ f A R, woset A R → f: A ⇒ A →
  (∀ x y ∈ A, (x <ᵣ y) R → (f[x] <ᵣ f[y]) R) →
  ∀x ∈ A, (x ≤ᵣ f[x]) R.
Proof with eauto; try congruence.
  intros * Hwo Hf Hopf x Hxa.
  assert (H := Hwo). destruct H as [Hlo Hmin].
  assert (Hfx: f[x] ∈ A) by (eapply ap_ran; eauto).
  destruct (classic (x = f[x])) as [|Hnq]. right...
  eapply linearOrder_connected in Hnq as [|Hfxx]... left... exfalso.
  set {x ∊ A | λ x, (f[x] <ᵣ x) R} as B.
  pose proof (Hmin B) as [m [Hm Hlt]].
  - exists x. apply SepI...
  - intros b Hb. apply SepE1 in Hb...
  - apply SepE in Hm as [Hm Hltm].
    assert (Hfm: f[m] ∈ B). {
      apply SepI. eapply ap_ran...
      apply Hopf... eapply ap_ran...
    }
    assert (H := Hlo). destruct H as [_ [Htr _]].
    apply Hlt in Hfm as []; eapply linearOrder_irrefl...
    rewrite H in Hltm at 2...
Qed.

Module EX7_15_AlternativeProof.

Lemma self_order_preserving_func_progressive :
  ∀ f A R, woset A R → f: A ⇒ A →
  (∀ x y ∈ A, (x <ᵣ y) R → (f[x] <ᵣ f[y]) R) →
  ∀x ∈ A, (x ≤ᵣ f[x]) R.
Proof with eauto; try congruence.
  intros * Hwo Hf Hopf x Hxa.
  assert (H := Hwo). destruct H as [Hlo Hmin].
  assert (Hfx: f[x] ∈ A) by (eapply ap_ran; eauto).
  destruct (classic (x = f[x])) as [|Hnq]. right...
  eapply linearOrder_connected in Hnq as [|Hfxx]... left... exfalso.
  eapply woset_no_descending_chain...
  pose proof (ω_recursion f A x Hf Hxa) as [h [Hh [Hh0 Hhn]]].
  exists h. split... intros n Hn. rewrite Hhn...
  set {n ∊ ω | λ n, <f[h[n]], h[n]> ∈ R} as N.
  ω_induction N Hn... rewrite Hhn... apply Hopf...
  eapply ap_ran... eapply ap_ran... eapply ap_ran...
Qed.

End EX7_15_AlternativeProof.

(** ex7_6 **)

Close Scope Real_scope.

Lemma card_int_eq_aleph0 : |ℤ| = ℵ₀.
Proof with nauto.
  apply CardAx1. symmetry.
  apply Schröeder_Bernstein.
  - set (Func ω ℤ Int) as f.
    exists f. apply meta_injective.
    + intros n Hn...
    + intros n Hn m Hm Heq. apply int_ident in Heq...
      do 2 rewrite add_ident, proj_embed_id in Heq...
  - eapply dominate_rewrite_r.
    rewrite ω_eqnum_ω_cp_ω...
    set (Func ℤ ω² IntProj) as f.
    exists f. apply meta_injective.
    + intros a Ha. apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]].
      pose proof (intProj m Hm n Hn) as [p [Hp [q [Hq [Heq _]]]]].
      subst. rewrite Heq. apply CProdI...
    + intros a Ha b Hb Heq.
      apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]].
      apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]].
      pose proof (intProj m Hm n Hn) as [s [Hs [t [Ht [H11 H12]]]]].
      pose proof (intProj p Hp q Hq) as [u [Hu [v [Hv [H21 H22]]]]].
      subst. rewrite H11, H21 in Heq.
      apply op_iff in Heq as []; subst.
      apply planeEquiv in H12... apply planeEquiv in H22...
      apply int_ident... eapply intEqTran; revgoals;
        [apply intEqSymm; apply H22|apply H12|..]...
Qed.

(* ==使用了类型论上的选择函数== *)
Lemma card_rat_eq_aleph0 : |ℚ| = ℵ₀.
Proof with nauto.
  apply CardAx1. symmetry.
  apply Schröeder_Bernstein.
  - set (Func ω ℚ Rat) as f.
    exists f. apply meta_injective.
    + intros n Hn...
    + intros n Hn m Hm Heq.
      apply rat_ident in Heq...
      do 2 rewrite intMul_ident in Heq...
      apply int_ident in Heq...
      do 2 rewrite add_ident, proj_embed_id in Heq...
  - eapply dominate_rewrite_r.
    eapply eqnum_tran; revgoals. rewrite ω_eqnum_ω_cp_ω...
    apply cardMul_well_defined; apply CardAx1; apply card_int_eq_aleph0.
    set (Func ℚ ℤ² RatProj) as f.
    exists f. apply meta_injective.
    + intros r Hr. apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]].
      pose proof (ratProj a Ha b Hb) as [c [Hc [d [Hd [Heq _]]]]].
      subst. rewrite Heq. apply CProdI... apply SepE1 in Hd...
    + intros r Hr q Hq Heq.
      apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]].
      apply pQuotE in Hq as [c [Hc [d [Hd Hq]]]].
      pose proof (ratProj a Ha b Hb) as [s [Hs [t [Ht [H11 [H12 _]]]]]].
      pose proof (ratProj c Hc d Hd) as [u [Hu [v [Hv [H21 [H22 _]]]]]].
      subst. rewrite H11, H21 in Heq.
      apply op_iff in Heq as []; subst.
      apply planeEquiv in H12... apply planeEquiv in H22...
      apply rat_ident... eapply ratEqTran; revgoals;
        [apply ratEqSymm; apply H22|apply H12|..]...
Qed.

Open Scope Real_scope.

(* ==需要选择公理== *)
(* 对实数的任意子集，如果它按小于关系是良序集，那么它是可数的 *)
Example ex7_6 : AC_III → ∀ A, A ⊆ ℝ → woset A (RealLt ⥏ A) → countable A.
Proof with neauto.
  intros AC3 A Hsub Hwo.
  assert (H := Hwo). destruct H as [Hlo _].
  assert (AC3': AC_III') by (apply AC_III_iff_III'; auto).
  apply countable_iff.
  destruct (classic (finite A)) as [|Hinf]...
  right. symmetry.
  apply Schröeder_Bernstein. {
    apply ω_is_the_least_infinite_set...
  }
  eapply dominate_rewrite_r. {
    apply CardAx1. apply card_rat_eq_aleph0.
  }
  destruct (classic (∀x ∈ A, ∃y ∈ A, x <𝐫 y)) as [Hnomax|Hmax]. {
    set (Next A (RealLt ⥏ A)) as next.
    set (λ x y z, x <𝐫 y ∧ y <𝐫 z) as bt.
    set (λ Q, ∃x ∈ A, ∀r ∈ ℚ, bt x RatEmbed[r] (next x) → r ∈ Q) as P.
    set {Q ∊ 𝒫 ℚ | P} as 𝒬.
    assert (Hstar: ∀x ∈ A, (∃q ∈ ℚ, bt x RatEmbed[q] (next x)) ∧
      ∀y ∈ A, x <𝐫 y → (next x) ≤ y
    ). {
      intros x Hx.
      pose proof (next_correct A (RealLt ⥏ A) A) as [H1 H2]... {
        apply Hnomax in Hx as Hlt. destruct Hlt as [y [Hy Hxy]].
        exists y. split... apply SepI... apply CProdI...
      }
      split.
      - apply SepE in H1 as [Hnxt Hlt].
        apply realDense... apply Hsub...
        apply Hsub... apply SepE1 in Hlt...
      - intros y Hy Hxy.
        assert (Hyt: y ∈ tail x A (RealLt ⥏ A)). {
          apply SepI... apply SepI... apply CProdI...
        }
        apply H2 in Hyt as []... left. apply SepE1 in H...
    }
    pose proof (AC3' 𝒬) as [F [HfF [HdF HrF]]]. {
      intros Q HQ. apply SepE in HQ as [_ [x [Hx H]]].
      apply Hstar in Hx as [[r [Hr Hbt]] _]...
      exists r. apply H...
    }
    set (λ x, {r ∊ ℚ | λ r, bt x RatEmbed[r] (next x)}) as ℬ.
    assert (HB: ∀x ∈ A, ℬ x ∈ 𝒬). {
      intros x Hx. apply SepI.
      - apply PowerAx. intros r Hr. apply SepE1 in Hr...
      - exists x. split... intros r Hr Hbt. apply SepI...
    }
    set (Func A ℚ (λ x, F[ℬ x])) as f.
    exists f. apply meta_injective.
    - intros x Hx. cut (F[ℬ x] ∈ ℬ x). {
        intros H. apply SepE1 in H...
      }
      apply HrF. apply SepI.
      + apply PowerAx. intros r Hr. apply SepE1 in Hr...
      + exists x. split... intros r Hr. intros Hbt. apply SepI...
    - intros x1 H1 x2 H2 Heq.
      apply HB in H1 as HB1. apply HrF in HB1. apply SepE2 in HB1.
      apply HB in H2 as HB2. apply HrF in HB2. apply SepE2 in HB2.
      rewrite <- Heq in HB2.
      destruct (classic (x1 = x2)) as [|Hnq]...
      eapply linearOrder_connected in Hnq as [Hlt|Hlt]...
      + exfalso. apply Hstar in H1 as [[r [Hr Hbt]] Hle]...
        destruct HB1 as [_ Hlt1]. destruct HB2 as [Hlt2 _].
        apply SepE1 in Hlt. apply Hle in Hlt as []; auto;
        eapply realLt_irrefl; eapply realLt_tranr.
        apply Hlt1. eapply realLt_tranr...
        apply Hlt1. subst x2...
      + exfalso. apply Hstar in H2 as [[r [Hr Hbt]] Hle]...
        destruct HB2 as [_ Hlt1]. destruct HB1 as [Hlt2 _].
        apply SepE1 in Hlt. apply Hle in Hlt as []; auto;
        eapply realLt_irrefl; eapply realLt_tranr.
        apply Hlt1. eapply realLt_tranr...
        apply Hlt1. subst x1...
  } {
    apply set_not_all_ex_not in Hmax as [m [Hm Hmax]].
    set (A - ⎨m⎬)%zfc as B.
    set (Next A (RealLt ⥏ A)) as next.
    set (λ x y z, x <𝐫 y ∧ y <𝐫 z) as bt.
    set (λ Q, ∃x ∈ B, ∀r ∈ ℚ, bt x RatEmbed[r] (next x) → r ∈ Q) as P.
    set {Q ∊ 𝒫 ℚ | P} as 𝒬.
    assert (Hstar: ∀x ∈ B, (∃q ∈ ℚ, bt x RatEmbed[q] (next x)) ∧
      (∀y ∈ A, x <𝐫 y → (next x) ≤ y) ∧ (next x) ∈ A
    ). {
      intros x Hx.
      pose proof (next_correct A (RealLt ⥏ A) A) as [H1 H2]; auto. {
        apply SepE1 in Hx...
      } {
        apply SepE in Hx as [Hx Hnq]. apply SingNE in Hnq.
        eapply linearOrder_connected in Hnq as []...
        - exists m. split...
        - exfalso. eapply Hmax.
          exists x. split... apply SepE1 in H...
      }
      apply SepE in H1 as [Hnxt Hlt].
      split; [|split]...
      - apply realDense... apply Hsub... apply SepE1 in Hx...
        apply Hsub... apply SepE1 in Hlt...
      - intros y Hy Hxy.
        assert (Hyt: y ∈ tail x A (RealLt ⥏ A)). {
          apply SepI... apply SepI... apply CProdI...
          apply SepE1 in Hx...
        }
        apply H2 in Hyt as []... left. apply SepE1 in H...
    }
    pose proof (AC3' 𝒬) as [F [HfF [HdF HrF]]]. {
      intros Q HQ. apply SepE in HQ as [_ [x [Hx H]]].
      apply Hstar in Hx as [[r [Hr Hbt]] _]...
      exists r. apply H...
    }
    apply Hsub in Hm as Hmr.
    assert (Hmp: m <𝐫 m + Real 1). {
      rewrite <- (realAdd_ident m) at 1...
      rewrite realAdd_comm, (realAdd_comm m)...
      apply realAdd_preserve_lt... apply realPos_sn.
    }
    apply realDense in Hmp as [q [Hq [Hmq _]]]; revgoals...
    apply realAdd_ran...
    set (λ x, {r ∊ ℚ | λ r, bt x RatEmbed[r] (next x)}) as ℬ.
    assert (HB: ∀x ∈ B, ℬ x ∈ 𝒬). {
      intros x Hx. apply SepI.
      - apply PowerAx. intros r Hr. apply SepE1 in Hr...
      - exists x. split... intros r Hr Hbt. apply SepI...
    }
    set (Func A ℚ (λ x, match (ixm (x ∈ B)) with
      | inl _ => F[ℬ x]
      | inr _ => q
    end)) as f.
    exists f. apply meta_injective.
    - intros x Hx. destruct (ixm (x ∈ B))...
      cut (F[ℬ x] ∈ ℬ x). {
        intros H. apply SepE1 in H...
      }
      apply HrF. apply SepI.
      + apply PowerAx. intros r Hr. apply SepE1 in Hr...
      + exists x. split... intros r Hr. intros Hbt. apply SepI...
    - intros x1 H1 x2 H2 Heq.
      destruct (ixm (x1 ∈ B)) as [H1B|H1B];
      destruct (ixm (x2 ∈ B)) as [H2B|H2B].
      + apply HB in H1B as HB1. apply HrF in HB1. apply SepE2 in HB1.
        apply HB in H2B as HB2. apply HrF in HB2. apply SepE2 in HB2.
        rewrite <- Heq in HB2.
        destruct (classic (x1 = x2)) as [|Hnq]...
        eapply linearOrder_connected in Hnq as [Hlt|Hlt]...
        * exfalso. apply Hstar in H1B as [[r [Hr Hbt]] [Hle _]]...
          destruct HB1 as [_ Hlt1]. destruct HB2 as [Hlt2 _].
          apply SepE1 in Hlt. apply Hle in Hlt as []; auto;
          eapply realLt_irrefl; eapply realLt_tranr.
          apply Hlt1. eapply realLt_tranr...
          apply Hlt1. subst x2...
        * exfalso. apply Hstar in H2B as [[r [Hr Hbt]] [Hle _]]...
          destruct HB2 as [_ Hlt1]. destruct HB1 as [Hlt2 _].
          apply SepE1 in Hlt. apply Hle in Hlt as []; auto;
          eapply realLt_irrefl; eapply realLt_tranr.
          apply Hlt1. eapply realLt_tranr...
          apply Hlt1. subst x1...
      + exfalso. apply HB in H1B as HB1. apply HrF in HB1.
        apply SepE2 in HB1. rewrite Heq in HB1.
        apply Hstar in H1B as [_ [_ Hn]]...
        apply Hmax. exists (next x1). split...
        destruct HB1 as [_ Hlt]... eapply realLt_tranr...
      + exfalso. apply HB in H2B as HB2. apply HrF in HB2.
        apply SepE2 in HB2. rewrite <- Heq in HB2.
        apply Hstar in H2B as [_ [_ Hn]]...
        apply Hmax. exists (next x2). split...
        destruct HB2 as [_ Hlt]... eapply realLt_tranr...
      + destruct (classic (x1 = x2))... exfalso.
        apply H1B. apply SepI... apply SingNI. intros Heqx1.
        apply H2B. apply SepI... apply SingNI. congruence.
  }
Qed.

Close Scope Real_scope.

(* ex7_7 see EST7_2 transitive closure *)
(* ex7_8 see ZFC2 Definition Sep *)
(* ex7_9 see ZFC1 Definition Pair *)
