(** Based on "Elements of Set Theory" Chapter 6 Part 4 EX **)
(** Coq coding by choukh, Sep 2020 **)

Require Export ZFC.EST6_4.

(*** EST第六章4扩展：选择公理的系统考察：图基引理，豪斯多夫极大原理 ***)

(* 具有有穷特征 *)
Definition finite_character : set → Prop := λ 𝒜,
  ∀ B, B ∈ 𝒜 ↔ ∀ C, finite C → C ⊆ B → C ∈ 𝒜.

(* 选择公理等效表述7：图基引理（第二极大原理） *)
(* 具有有穷特征的非空集合必有子集关系下的极大元 *)
Definition AC_VII : Prop := ∀ 𝒜, ⦿ 𝒜 →
  finite_character 𝒜 → has_max 𝒜.

(* 空集是链 *)
Lemma emptyset_is_chain : is_chain ∅.
Proof. intros x Hx. exfalso0. Qed.

(* 链的子集仍是链 *)
Lemma sub_of_chain_is_chain : ∀ ℬ 𝒞, is_chain ℬ → 𝒞 ⊆ ℬ → is_chain 𝒞.
Proof.
  intros * Hchn Hsub C HC D HD. apply Hchn; apply Hsub; auto.
Qed.

(* 非空有限链必有极大元 *)
Lemma finite_chain_has_max : ∀ ℬ, ⦿ ℬ →
  finite ℬ → is_chain ℬ → has_max ℬ.
Proof with eauto; try congruence.
  intros ℬ Hne [n [Hn Hqn]]. generalize dependent ℬ.
  set {n ∊ ω | λ n, ∀ ℬ, ⦿ ℬ → ℬ ≈ n → is_chain ℬ → has_max ℬ} as N.
  ω_induction N Hn; intros ℬ Hne Hqn Hchn. {
    exfalso. apply EmptyNI in Hne. apply eqnum_empty in Hqn...
  }
  destruct Hne as [B HB].
  apply split_one_element in HB as Heq.
  destruct (classic (ℬ - ⎨B⎬ = ∅)) as [|Hne]. {
    exists B. split... intros x Hx.
    apply sub_iff_no_comp in H. apply H in Hx. apply SingE in Hx...
  }
  pose proof (IH (ℬ - ⎨B⎬)) as [M [HM Hmax]].
  - apply EmptyNE...
  - apply fin_set_remove_one_element...
  - eapply sub_of_chain_is_chain...
  - assert (HM': M ∈ ℬ). { apply SepE in HM as []... }
    pose proof (Hchn B HB M HM') as [].
    + exists M. split... intros x Hx.
      destruct (classic (x = B)). subst x...
      apply Hmax. apply SepI... apply SingNI...
    + exists B. split... intros x Hx.
      destruct (classic (x = B)). subst x...
      eapply sub_tran in H... apply Hmax. apply SepI... apply SingNI...
Qed.

(* AC cycle
    6 → 7 → 8 → 8' → 6
*)

Theorem AC_VI_to_AC_VII : AC_VI → AC_VII.
Proof with eauto.
  unfold AC_VI, AC_VII.
  intros Zorn 𝒜 [A HA] Hcha. apply Zorn.
  intros ℬ Hchn Hs1. apply Hcha.
  intros C Hfin Hs2. destruct (classic (C = ∅)). {
    eapply Hcha in HA. apply HA. apply Hfin.
    subst C. apply empty_sub_all.
  }
  cut (∃B ∈ ℬ, C ⊆ B). {
    intros [B [HB Hs3]]. apply Hs1 in HB.
    apply Hcha with B C in HB...
  }
  set {p ∊ C × ℬ | λ p, π1 p ∈ π2 p} as R.
  pose proof (AC_VI_to_I Zorn) as AC1.
  pose proof (AC1 R) as [F [HfF [HsF Hd]]]. { apply sep_cp_is_rel. }
  assert (HdF: dom F = C). {
    rewrite Hd. apply ExtAx. split; intros Hx.
    - apply domE in Hx as [y Hp]. apply SepE in Hp as [Hp _].
      apply CProdE1 in Hp as [Hx _]. zfcrewrite.
    - apply Hs2 in Hx as Hxb.
      apply UnionAx in Hxb as [B [HB Hxb]].
      eapply domI. apply SepI. apply CProdI... zfcrewrite.
  }
  assert (Hsub: ran F ⊆ ℬ). {
    intros y Hy. apply ranE in Hy as [x Hp].
    apply HsF in Hp. apply SepE in Hp as [Hp _].
    apply CProdE1 in Hp as [_ Hy]. zfcrewrite.
  }
  pose proof (finite_chain_has_max (ran F)) as [M [HM Hmax]].
  - apply EmptyNE in H as [c Hc].
    exists (F[c]). eapply ap_ran... split...
  - eapply dominated_by_finite_is_finite.
    apply domain_dominate_range... rewrite HdF...
  - intros D HD E HE. apply Hchn; apply Hsub...
  - exists M. split. apply Hsub...
    intros x Hx. eapply Hmax. eapply ranI. apply func_correct...
    rewrite HdF... rewrite <- HdF in Hx. apply domE in Hx as [B Hp].
    apply func_ap in Hp as Hap... subst B.
    apply HsF in Hp. apply SepE in Hp as [_ Hx]. zfcrewrite.
Qed.
