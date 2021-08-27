(** Solutions to "Elements of Set Theory" Chapter 7 **)
(** Coq coding by choukh, Nov 2020 **)

Require ZFC.Lib.Choice.
Require Import ZFC.Lib.Real.
Require Import ZFC.Lib.ChoiceFacts.
Require Import ZFC.Lib.Cardinal.
Require Import ZFC.Lib.WosetMin.
Close Scope Real_scope.

(* ex7_1
  (a) No (b) No
    let < be divisibility
    let A = {2, 3, 6}
    let B = {3, 3, 6}
*)
(* ex7_2 see EST7_1 Fact inv_po *)
(* ex7_3 Combination (n, 2) = n! / 2!(n - 2)! = (1/2)n(n-1) *)
(* ex7_4 skip *)

(* ex7_5 良序集的自保序映射具有单调性 *)
Lemma auto_order_preserving_func_monotone :
  ∀ f A R, woset A R → f: A ⇒ A →
  (∀ x y ∈ A, (x <ᵣ y) R → (f[x] <ᵣ f[y]) R) →
  ∀x ∈ A, (x ≤ᵣ f[x]) R.
Proof with eauto; try congruence.
  intros * Hwo Hf Hoe x Hxa.
  assert (H := Hwo). destruct H as [Hlo Hmin].
  assert (Hfx: f[x] ∈ A) by (eapply ap_ran; eauto).
  destruct (classic (x = f[x])) as [|Hnq]. right...
  eapply lo_connected in Hnq as [|Hfxx]... left... exfalso.
  set {x ∊ A | (f[x] <ᵣ x) R} as B.
  pose proof (Hmin B) as [m [Hm Hlt]].
  - exists x. apply SepI...
  - intros b Hb. apply SepE1 in Hb...
  - apply SepE in Hm as [Hm Hltm].
    assert (Hfm: f[m] ∈ B). {
      apply SepI. eapply ap_ran...
      apply Hoe... eapply ap_ran...
    }
    apply Hlt in Hfm. eapply lo_not_leq_gt...
Qed.

Module EX7_15_AlternativeProof.

Lemma auto_order_preserving_func_monotone :
  ∀ f A R, woset A R → f: A ⇒ A →
  (∀ x y ∈ A, (x <ᵣ y) R → (f[x] <ᵣ f[y]) R) →
  ∀x ∈ A, (x ≤ᵣ f[x]) R.
Proof with eauto; try congruence.
  intros * Hwo Hf Hoe x Hxa.
  assert (H := Hwo). destruct H as [Hlo Hmin].
  assert (Hfx: f[x] ∈ A) by (eapply ap_ran; eauto).
  destruct (classic (x = f[x])) as [|Hnq]. right...
  eapply lo_connected in Hnq as [|Hfxx]... left... exfalso.
  eapply woset_no_descending_chain...
  pose proof (ω_recursion f A x Hf Hxa) as [h [Hh [Hh0 Hhn]]].
  exists h. split... intros n Hn. rewrite Hhn...
  ω_induction n... rewrite Hh0...
  rewrite Hhn... apply Hoe...
  eapply ap_ran... eapply ap_ran... eapply ap_ran...
Qed.

End EX7_15_AlternativeProof.

(** ex7_6 **)

Section EX7_6.
Import WosetMin.SimpleVer.

Lemma card_int_eq_aleph0 : |ℤ| = ℵ₀.
Proof with nauto.
  apply CardAx1. symmetry.
  apply Schröeder_Bernstein.
  - set (Func ω ℤ Int) as f.
    exists f. apply meta_injection.
    + intros n Hn...
    + intros n Hn m Hm Heq. apply int_ident in Heq...
      do 2 rewrite add_0_r, embed_proj_id in Heq...
  - eapply dominate_rewrite_r.
    now rewrite ω_eqnum_ω_cp_ω.
    set (Func ℤ ω² IntProj) as f.
    exists f. apply meta_injection.
    + intros a Ha. apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]].
      pose proof (intProj m Hm n Hn) as [p [Hp [q [Hq [Heq _]]]]].
      subst. rewrite Heq. apply CPrdI...
    + intros a Ha b Hb Heq.
      apply pQuotE in Ha as [m [Hm [n [Hn Ha]]]].
      apply pQuotE in Hb as [p [Hp [q [Hq Hb]]]].
      pose proof (intProj m Hm n Hn) as [s [Hs [t [Ht [H11 [H12 _]]]]]].
      pose proof (intProj p Hp q Hq) as [u [Hu [v [Hv [H21 [H22 _]]]]]].
      subst. rewrite H11, H21 in Heq.
      apply op_iff in Heq as []; subst.
      apply planeEquiv in H12... apply planeEquiv in H22...
      apply int_ident... eapply intEqTran; revgoals;
        [apply intEqSymm; apply H22|apply H12|..]...
Qed.

Lemma card_rat_eq_aleph0 : |ℚ| = ℵ₀.
Proof with nauto.
  apply CardAx1. symmetry.
  apply Schröeder_Bernstein.
  - set (Func ω ℚ Rat) as f.
    exists f. apply meta_injection.
    + intros n Hn...
    + intros n Hn m Hm Heq.
      apply rat_ident in Heq...
      do 2 rewrite intMul_1_r in Heq...
      apply int_ident in Heq...
      do 2 rewrite add_0_r, embed_proj_id in Heq...
  - eapply dominate_rewrite_r.
    eapply Equivalence_Transitive; revgoals. now rewrite ω_eqnum_ω_cp_ω.
    apply cardMul_well_defined; apply CardAx1; apply card_int_eq_aleph0.
    set (Func ℚ ℤ² RatProj) as f.
    exists f. apply meta_injection.
    + intros r Hr. apply pQuotE in Hr as [a [Ha [b [Hb Hr]]]].
      pose proof (ratProj a Ha b Hb) as [c [Hc [d [Hd [Heq _]]]]].
      subst. rewrite Heq. apply CPrdI... apply SepE1 in Hd...
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
Theorem reals_well_ordered_by_lt_is_countable : AC_III →
  ∀ A, A ⊆ ℝ → woset A (RealLt ⥏ A) → countable A.
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
    set {Q ∊ 𝒫 ℚ | P Q} as 𝒬.
    assert (Hstar: ∀x ∈ A, (∃q ∈ ℚ, bt x RatEmbed[q] (next x)) ∧
      ∀y ∈ A, x <𝐫 y → (next x) ≤ y
    ). {
      intros x Hx.
      pose proof (next_correct A (RealLt ⥏ A) A) as [H1 H2]... {
        apply Hnomax in Hx as Hlt. destruct Hlt as [y [Hy Hxy]].
        exists y. split... apply SepI... apply CPrdI...
      }
      split.
      - apply SepE in H1 as [Hnxt Hlt].
        apply real_dense... apply SepE1 in Hlt...
      - intros y Hy Hxy.
        assert (Hyt: y ∈ tail x A (RealLt ⥏ A)). {
          apply SepI... apply SepI... apply CPrdI...
        }
        apply H2 in Hyt as []... left. apply SepE1 in H...
    }
    pose proof (AC3' 𝒬) as [F [HfF [HdF HrF]]]. {
      intros Q HQ. apply SepE in HQ as [_ [x [Hx H]]].
      apply Hstar in Hx as [[r [Hr Hbt]] _]...
      exists r. apply H...
    }
    set (λ x, {r ∊ ℚ | bt x RatEmbed[r] (next x)}) as ℬ.
    assert (HB: ∀x ∈ A, ℬ x ∈ 𝒬). {
      intros x Hx. apply SepI.
      - apply PowerAx. intros r Hr. apply SepE1 in Hr...
      - exists x. split... intros r Hr Hbt. apply SepI...
    }
    set (Func A ℚ (λ x, F[ℬ x])) as f.
    exists f. apply meta_injection.
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
      eapply lo_connected in Hnq as [Hlt|Hlt]...
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
    set (A - ⎨m⎬)%set as B.
    set (Next A (RealLt ⥏ A)) as next.
    set (λ x y z, x <𝐫 y ∧ y <𝐫 z) as bt.
    set (λ Q, ∃x ∈ B, ∀r ∈ ℚ, bt x RatEmbed[r] (next x) → r ∈ Q) as P.
    set {Q ∊ 𝒫 ℚ | P Q} as 𝒬.
    assert (Hstar: ∀x ∈ B, (∃q ∈ ℚ, bt x RatEmbed[q] (next x)) ∧
      (∀y ∈ A, x <𝐫 y → (next x) ≤ y) ∧ (next x) ∈ A
    ). {
      intros x Hx.
      pose proof (next_correct A (RealLt ⥏ A) A) as [H1 H2]; auto. {
        apply SepE1 in Hx...
      } {
        apply SepE in Hx as [Hx Hnq]. apply SingNE in Hnq.
        eapply lo_connected in Hnq as []... exfalso.
        eapply Hmax. exists x. split... apply SepE1 in H...
      }
      apply SepE in H1 as [Hnxt Hlt].
      split; [|split]...
      - apply real_dense... apply Hsub...
        apply SepE1 in Hx... apply SepE1 in Hlt...
      - intros y Hy Hxy.
        assert (Hyt: y ∈ tail x A (RealLt ⥏ A)). {
          apply SepI... apply SepI... apply CPrdI...
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
      rewrite <- (realAdd_0_r m) at 1...
      rewrite realAdd_comm, (realAdd_comm m)...
      apply realAdd_preserve_lt... apply realPos_sn.
    }
    apply real_dense in Hmp as [q [Hq [Hmq _]]]; revgoals...
    apply realAdd_ran...
    set (λ x, {r ∊ ℚ | bt x RatEmbed[r] (next x)}) as ℬ.
    assert (HB: ∀x ∈ B, ℬ x ∈ 𝒬). {
      intros x Hx. apply SepI.
      - apply PowerAx. intros r Hr. apply SepE1 in Hr...
      - exists x. split... intros r Hr Hbt. apply SepI...
    }
    set (Func A ℚ (λ x, match (ixm (x ∈ B)) with
      | inl _ => F[ℬ x]
      | inr _ => q
    end)) as f.
    exists f. apply meta_injection.
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
        eapply lo_connected in Hnq as [Hlt|Hlt]...
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
      + contra.
        apply H1B. apply SepI... apply SingNI. intros Heqx1.
        apply H2B. apply SepI... apply SingNI. congruence.
  }
Qed.

Close Scope Real_scope.
End EX7_6.

(* ex7_7 see EST7_2 transitive closure *)
(* ex7_8 see ZFC2 Definition Sep *)
(* ex7_9 see ZFC1 Definition Pair *)
(* ex7_10-17 see EX7_2 *)
(* ex7_18 see EST7_4 limit ordinal *)

Section EX7_19.

(* 传递关系上的无穷降链是序反转 *)
Lemma descending_chain_order_reversing : ∀ f A R,
  tranr R → descending_chain f A R →
  ∀ n m ∈ ω, n ∈ m → (f[m] <ᵣ f[n]) R.
Proof with auto.
  intros f A R Htr [[Hf [Hd Hr]] Hdesc].
  intros k Hk n Hn. generalize dependent k.
  ω_induction n; intros k Hk H. exfalso0.
  apply BUnionE in H as [].
  - eapply Htr. apply Hdesc... apply IH...
  - apply SingE in H; subst. apply Hdesc...
Qed.

(* 偏序上的无穷降链具有单射性 *)
Lemma descending_chain_injective : ∀ f A R, poset A R →
  descending_chain f A R → injective f.
Proof with eauto; try congruence.
  intros f A R [_ [_ [Htr Hir]]] Hdesc.
  assert (H := Hdesc). destruct H as [[Hf [Hd Hr]] _].
  split... intros y Hy. rewrite <- unique_existence.
  split. apply ranE in Hy...
  intros n m Hpn Hpm.
  apply domI in Hpn as Hn; rewrite Hd in Hn.
  apply domI in Hpm as Hm; rewrite Hd in Hm.
  apply func_ap in Hpn... apply func_ap in Hpm... subst y.
  contra as Hnq.
  pose proof (descending_chain_order_reversing f A R Htr Hdesc).
  apply nat_connected in Hnq as [Hnm|Hmn]; auto.
  - pose proof (H n Hn m Hm Hnm) as Hlt.
    rewrite Hpm in Hlt. eapply Hir...
  - pose proof (H m Hm n Hn Hmn) as Hlt.
    rewrite Hpm in Hlt. eapply Hir...
Qed.

Import ZFC.Lib.Choice.

(* ==可以不用选择公理== *)
(* 有限集的线序是良序 *)
(* can be proved without AC, see https://math.stackexchange.com/questions/2155285/show-that-a-set-is-finite-if-and-only-if-every-linear-ordering-on-it-is-a-well-o *)
Lemma finite_loset_is_woset : ∀ A R,
  finite A → loset A R → woset A R.
Proof with eauto.
  intros A R [n [Hn [f Hf]]] Hlo.
  apply woset_iff_no_descending_chain...
  apply ac1. intros [g Hdesc].
  assert (Hinj: g: ω ⇔ A). {
    apply injection_is_func. split. apply Hdesc.
    eapply descending_chain_injective...
    apply loset_iff_connected_poset...
  }
  apply bijection_is_injection in Hf as [Hf _].
  set (f ∘ g) as h.
  assert (Hh: h : ω ⇔ n). eapply compo_injection...
  apply ω_infinite. eapply dominated_by_finite_is_finite.
  exists h... apply nat_finite...
Qed.

Import WoStruct.

(* 有限集的序数等于基数 *)
Lemma finite_ord_eq_card : ∀ S, finite (A S) → ord S = |A S|.
Proof with eauto; try congruence.
  intros S Hfin.
  assert (H := Hfin). destruct H as [n [Hn [f Hf]]].
  assert (Hcard: |A S| = n). {
    rewrite (card_of_nat n)... apply CardAx1. exists f...
  }
  set (Seg n ℕ̃) as N.
  assert (Heqn: A N = n). {
    unfold N. rewrite seg_a_eq... rewrite seg_of_nat...
  }
  assert (Hord: ord N = n). {
    unfold N. rewrite α_nat...
  }
  rewrite Hcard, <- Hord. apply ord_well_defined.
  pose proof (wo_iso_at_least_trich S N) as [|[]]; auto; exfalso.
  - destruct H as [m [Hm [g [Hg _]]]].
    assert (Hmw: m ∈ ω). eapply ω_trans...
    assert (Heqm: (A (Seg m N)) = m). {
      ext Hx.
      - apply SepE2 in Hx. unfold N in Hx. apply SepE1 in Hx.
        apply binRelE3 in Hx...
      - rewrite seg_a_eq... apply segI. unfold N.
        apply seg_lt; apply binRelI... eapply ω_trans...
    }
    assert (Hcard': |A S| = m). {
      rewrite (card_of_nat m)... apply CardAx1. exists g...
    }
    rewrite Heqn, <- Hcard', Hcard in Hm. eapply nat_irrefl...
  - destruct H as [t [Ht [g [Hg _]]]].
    rewrite Heqn in Hg. apply inv_bijection in Hg.
    set (g ⁻¹ ∘ f) as h.
    assert (Hh: h: A S ⟺ A (Seg t S)). eapply compo_bijection...
    assert (Hqn: A S ≈ A (Seg t S)). exists h...
    eapply infinite_if_eqnum_proper_sub... split.
    + intros x Hx. apply SepE1 in Hx...
    + intros Heq. rewrite <- Heq in Ht. apply SepE2 in Ht.
      eapply lo_irrefl... apply wo.
Qed.

(* 有限集的不同良序同构 *)
Lemma well_order_on_same_finite_set_isomorphic :
  ∀ S T, A S = A T → finite (A S) → S ≅ T.
Proof with auto.
  intros S T Heq Hfin.
  apply finite_ord_eq_card in Hfin as Hos. rewrite Heq in Hfin.
  apply finite_ord_eq_card in Hfin as Hot.
  assert (Heqo: ord S = ord T) by congruence.
  apply ord_well_defined. apply Heqo.
Qed.

Import OrderedStruct.

Example ex7_19 : ∀ S T, lo S → lo T → A S = A T →
  finite (A S) → S ≅ T.
Proof with auto; try congruence.
  intros * Hlos Hlot Heqa Hfin.
  apply finite_loset_is_woset in Hlos as Hwos...
  apply finite_loset_is_woset in Hlot as Hwot...
  set (WoStruct.constr (A S) (R S) Hwos) as U.
  set (WoStruct.constr (A T) (R T) Hwot) as V.
  cut (U ≅ V)%wo...
  apply well_order_on_same_finite_set_isomorphic...
Qed.

End EX7_19.

Section EX7_20.
Import WosetMin.FullVer.

(* ex7_20 如果良序集反序仍是良序那么它是有限集 *)
Theorem well_order_forward_backward_impl_finite :
  ∀ A R, woset A R → woset A R⁻¹ → finite A.
Proof with eauto; try congruence.
  intros A R Hwo1 Hwo2.
  contra as Hinf.
  set (λ t, {x ∊ A | (x <ᵣ t) R}) as seg.
  set (λ t, {x ∊ A | (t <ᵣ x) R}) as tail.
  set {x ∊ A | infinite (seg x)} as S.
  set {x ∊ A | infinite (tail x)} as T.
  assert (Hinf2: ∀t ∈ A, ¬(finite (seg t) ∧ finite (tail t))). {
    intros t Ht [Hfin1 Hfin2]. apply Hinf.
    replace A with (seg t ∪ tail t ∪ ⎨t⎬). {
      apply bunion_finite... apply bunion_finite... 
    }
    ext Hx.
    - apply BUnionE in Hx as []... apply BUnionE in H as []...
      apply SepE1 in H... apply SepE1 in H...
      apply SingE in H; subst...
    - destruct (classic (x = t)). {
        apply BUnionI2. subst...
      }
      eapply lo_connected in H as []; [| |apply Hwo1|auto..].
      + apply BUnionI1. apply BUnionI1. apply SepI...
      + apply BUnionI1. apply BUnionI2. apply SepI...
  }
  destruct (classic (S = ∅ ∧ T = ∅)) as [[Hnea Hneb]|Hne]. {
    apply infinite_set_nonempty in Hinf as [a Ha].
    eapply not_and_or in Hinf2 as []...
    - apply EmptyNI in Hnea... exists a. apply SepI...
    - apply EmptyNI in Hneb... exists a. apply SepI...
  }
  apply not_and_or in Hne as [Hne|Hne]; apply EmptyNE in Hne.
  - assert (H := Hwo1). destruct H as [Hlo Hmin].
    assert (H := Hlo). destruct H as [_ [Htr _]].
    assert (Hne': ⦿ (A - S)). {
      apply comp_nonempty. split. {
        intros x Hx. apply SepE1 in Hx...
      }
      contra. apply NNPP in H.
      specialize Hmin with S as [m [Hm Hle]]...
      apply SepE2 in Hm.
      apply infinite_set_nonempty in Hm as [n Hn].
      apply SepE in Hn as [Hn Hlt]. rewrite <- H in Hn.
      apply Hle in Hn. eapply lo_not_leq_gt...
    }
    set ((Min A R)[S]) as a.
    set ((Min A R⁻¹)[A - S]) as b.
    pose proof (min_correct A R S) as [Ha Hlea]... {
      intros x Hx. apply SepE1 in Hx...
    }
    fold a in Ha, Hlea. apply SepE in Ha as [Ha Hfina].
    pose proof (min_correct A R⁻¹ (A - S)) as [Hb Hleb]...
    fold b in Hb, Hleb. apply SepE in Hb as [Hb Hb'].
    apply Hb'. apply SepI... intros Hfinb. apply Hfina.
    replace (seg a) with (seg b ∪ ⎨b⎬). {
      apply bunion_finite...
    }
    ext Hx.
    + assert (Hba: (b <ᵣ a) R). {
        destruct (classic (b = a))...
        eapply lo_connected in H as []; [| |apply Hwo1|..]...
        exfalso. apply Hfina.
        apply (subset_of_finite_is_finite _ (seg b))...
        intros y Hy. apply SepE in Hy as [Hy Hyb].
        apply SepI... eapply Htr...
      }
      apply BUnionE in Hx as [Hx|Hx].
      * apply SepE in Hx as [Hx Hxb]. apply SepI... eapply Htr...
      * apply SingE in Hx; subst. apply SepI...
    + apply SepE in Hx as [Hx Hxa].
      assert (Hx': x ∈ A - S). {
        apply SepI... intros H.
        apply Hlea in H. eapply lo_not_leq_gt...
      }
      apply Hleb in Hx' as [Hxb|Heq].
      * apply BUnionI1. apply SepI... rewrite <- inv_relLt...
      * apply BUnionI2. subst...
  - assert (H := Hwo1). destruct H as [[_ [Htr _]] _].
    assert (H := Hwo2). destruct H as [Hlo Hmin].
    assert (Hne': ⦿ (A - T)). {
      apply comp_nonempty. split. {
        intros x Hx. apply SepE1 in Hx...
      }
      contra. apply NNPP in H.
      specialize Hmin with T as [m [Hm Hle]]...
      apply SepE2 in Hm.
      apply infinite_set_nonempty in Hm as [n Hn].
      apply SepE in Hn as [Hn Hlt]. rewrite <- H in Hn.
      apply Hle in Hn. rewrite <- inv_relLt in Hlt.
      eapply lo_not_leq_gt...
    }
    set ((Min A R⁻¹)[T]) as a.
    set ((Min A R)[A - T]) as b.
    pose proof (min_correct A R⁻¹ T) as [Ha Hlea]... {
      intros x Hx. apply SepE1 in Hx...
    }
    fold a in Ha, Hlea. apply SepE in Ha as [Ha Hfina].
    pose proof (min_correct A R (A - T)) as [Hb Hleb]...
    fold b in Hb, Hleb. apply SepE in Hb as [Hb Hb'].
    apply Hb'. apply SepI... intros Hfinb. apply Hfina.
    replace (tail a) with (tail b ∪ ⎨b⎬). {
      apply bunion_finite...
    }
    ext Hx.
    + assert (Hba: (a <ᵣ b) R). {
        destruct (classic (b = a))...
        eapply lo_connected in H as []; [| |apply Hwo1|..]...
        exfalso. apply Hfina.
        apply (subset_of_finite_is_finite _ (tail b))...
        intros y Hy. apply SepE in Hy as [Hy Hyb].
        apply SepI... eapply Htr...
      }
      apply BUnionE in Hx as [Hx|Hx].
      * apply SepE in Hx as [Hx Hxb]. apply SepI... eapply Htr...
      * apply SingE in Hx; subst. apply SepI...
    + apply SepE in Hx as [Hx Hxa].
      assert (Hx': x ∈ A - T). {
        apply SepI... intros H. apply Hlea in H.
        rewrite <- inv_relLt in Hxa. eapply lo_not_leq_gt...
      }
      apply Hleb in Hx' as [Hxb|Heq].
      * apply BUnionI1. apply SepI...
      * apply BUnionI2. subst...
Qed.

End EX7_20.

(* ex7_21 see lib/ZornsLemma Lemma Zorn's *)
(* ex7_22 see lib/ZornsLemma Theorem Zorn_to_WO *)
(* ex7_23 see lib/Cardinal Theorem hartogs_is_card_suc *)
(* ex7_24 see lib/Cardinal Theorem all_ord_ex_larger_card *)
(* ex7_25 see EST7_4 Theorem transfinite_induction_schema_on_ordinals *)
