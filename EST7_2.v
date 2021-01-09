(** Based on "Elements of Set Theory" Chapter 7 Part 2 **)
(** Coq coding by choukh, Nov 2020 **)

Require Export ZFC.lib.Natural.
Require Import ZFC.lib.FuncFacts.

(*** EST第七章2：良序，超限归纳原理，超限递归定理，传递闭包 ***)

(* 良序结构 *)
Definition woset : set → set → Prop := λ A R,
  wellOrder R A.

(* Theorem 7J *)
Theorem subRel_woset : ∀ A R B, woset A R → B ⊆ A → woset B (R ⥏ B).
Proof with eauto.
  intros * [Hlo Hmin] Hsub.
  split. eapply subRel_loset...
  intros C Hne HsubC.
  pose proof (Hmin C Hne) as [m [Hm Hle]]. eapply sub_tran...
  exists m. split... intros x Hx.
  pose proof (Hle x Hx) as []; [left|right]...
  apply SepI... apply CProdI; apply HsubC...
Qed.

Lemma nat_woset : ∀n ∈ ω, woset n (Lt ⥏ n).
Proof with auto.
  intros n Hn. eapply subRel_woset. apply Lt_wellOrder.
  apply trans_sub... apply ω_trans.
Qed.

Lemma empty_woset : woset ∅ ∅.
Proof with auto.
  split. apply empty_loset.
  intros B [b Hb] Hsub. apply Hsub in Hb. exfalso0.
Qed.

(* 无穷降链 *)
Definition descending_chain : set → set → set → Prop := λ f A R,
  f: ω ⇒ A ∧ ∀n ∈ ω, (f[n⁺] <ᵣ f[n]) R.

(* 良序结构不存在无穷降链 *)
Theorem woset_no_descending_chain : ∀ A R,
  woset A R → ¬ ∃ f, descending_chain f A R.
Proof with neauto.
  intros * [Hlo Hmin] [f [[Hf [Hd Hr]] Hlt]].
    assert (Hne: ⦿ ran f). {
      exists (f[0]). eapply ranI.
      apply func_correct... rewrite Hd...
    }
    apply Hmin in Hne as [m [Hm Hle]]...
    apply ranE in Hm as [x Hp].
    apply domI in Hp as Hx. rewrite Hd in Hx.
    apply func_ap in Hp as Hap... subst m.
    assert (Hfx: f[x⁺] ∈ ran f). {
      eapply ap_ran. split... apply ω_inductive...
    }
    apply Hlt in Hx. apply Hle in Hfx.
    eapply lo_not_leq_gt...
Qed.

(* ==需要选择公理== *)
(* 非良序的关系存在无穷降链 *)
Lemma ex_descending_chain : AC_I → ∀ A R, ⦿ A →
  (∀y ∈ A, ∃x ∈ A, (x <ᵣ y) R) →
  ∃ f, descending_chain f A R.
Proof with eauto.
  intros AC1 * [a Ha] Hpr.
  set {p ∊ R | λ p, π1 p ∈ A ∧ π2 p ∈ A} as R'.
  pose proof (inv_rel R') as Hrel'.
  apply AC1 in Hrel' as [F [HfF [HsF HdF]]].
  assert (HF: F: A ⇒ A). {
    split; [|split]...
    - rewrite HdF. rewrite inv_dom.
      apply ExtAx. intros y. split; intros Hy.
      + apply ranE in Hy as [x Hp].
        apply SepE in Hp as [_ [_ Hy]]. zfcrewrite.
      + pose proof (Hpr _ Hy) as [x [Hx Hp]].
        eapply ranI. apply SepI. apply Hp. zfcrewrite...
    - intros y Hy. apply ranE in Hy as [x Hp].
      apply HsF in Hp. apply inv_op in Hp.
      apply SepE in Hp as [_ [Hx _]]. zfcrewrite.
  }
  pose proof (ω_recursion _ _ _ HF Ha) as [f [Hf [Hf0 Heq]]].
  exists f. split... intros n Hn. rewrite Heq...
  assert (HsR: R' ⊆ R). { intros p Hp. apply SepE1 in Hp... }
  apply HsR. rewrite inv_op. apply HsF. apply func_correct...
  destruct HF as [_ [Hd _]]. rewrite Hd. eapply ap_ran...
Qed.

(* ==需要选择公理== *)
(* 全序是良序当且仅当其上不存在无穷降链 *)
Theorem woset_iff_no_descending_chain :
  AC_I → ∀ A R, loset A R →
  woset A R ↔ ¬ ∃ f, descending_chain f A R.
Proof with neauto.
  intros AC1 * Hlo. split.
  - intros Hwo. apply woset_no_descending_chain...
  - intros Hndc. split... intros B Hne Hsub.
    destruct (classic (∃ m, minimum m B R))...
    pose proof (ex_descending_chain AC1 B R Hne) as [f Hdc]. {
      intros y Hy. eapply not_ex_all_not in H.
      apply not_and_or in H as []. exfalso...
      apply set_not_all_ex_not in H as [x [Hx H]].
      apply not_or_and in H as []. exists x. split...
      apply Hsub in Hy. apply Hsub in Hx.
      eapply lo_connected in H0 as []... exfalso...
    }
    exfalso. apply Hndc. exists f.
    destruct Hdc as [[Hf [Hd Hr]] Hdc].
    split... split... split... eapply sub_tran...
Qed.

(* 前节 *)
(* initial segment *)
Definition seg := λ t R, {x ∊ dom R | λ x, (x <ᵣ t) R}.
Definition head := λ t A R, {x ∊ A | λ x, (x ≤ᵣ t) R}.
Definition tail := λ t A R, {x ∊ A | λ x, (t <ᵣ x) R}.

Lemma segI : ∀ x t R, (x <ᵣ t) R → x ∈ seg t R.
Proof with eauto.
  intros. apply SepI... eapply domI...
Qed.

Lemma seg_0_Lt : seg 0 Lt = ∅.
Proof.
  apply ExtAx; split; intros Hx.
  apply SepE in Hx as [_ Hx0].
  apply binRelE3 in Hx0. exfalso0. exfalso0.
Qed.

Lemma seg_with_single_eq_head : ∀ t A R, t ∈ A → is_binRel R A →
  seg t R ∪ ⎨t⎬ = head t A R.
Proof with eauto.
  intros * Ht Hbr. apply ExtAx. split; intros Hx.
  - apply BUnionE in Hx as [].
    + apply SepE in H as [Hx Hxt].
      apply SepI. eapply dom_binRel... left...
    + apply SingE in H; subst. apply SepI... right...
  - apply SepE in Hx as [Hx [Hlt|Heq]].
    + apply BUnionI1. apply segI...
    + apply BUnionI2. subst...
Qed.

(* 自然数的前节等于自身 *)
Example seg_of_nat : ∀n ∈ ω, seg n Lt = n.
Proof with eauto.
  intros n Hn. apply ExtAx. split; intros Hx.
  - apply SepE in Hx as [_ Hp].
    apply SepE in Hp as [_ H]. zfcrewrite.
  - assert (Hxw: x ∈ ω). { eapply ω_trans... }
    apply SepI. eapply domI. apply (binRelI _ _ x Hxw (x⁺)).
    apply ω_inductive... apply suc_has_n. apply binRelI...
Qed.

(* 归纳子集 *)
Definition inductive_subset : set → set → set → Prop := λ B A R,
  B ⊆ A ∧ ∀t ∈ A, seg t R ⊆ B → t ∈ B.

(* 超限归纳原理：良序集的归纳子集与自身相等 *)
Theorem transfinite_induction : ∀ A R, woset A R →
  ∀ B, inductive_subset B A R → B = A.
Proof with auto.
  intros A R [[Hbr [Htr Htri]] Hwo] B [Hsub Hind].
  destruct (classic (B = A)) as [|Hnq]... exfalso.
  assert (Hne: ⦿ (A - B)) by (apply comp_nonempty; split; auto).
  apply Hwo in Hne as [m [Hm Hmin]]...
  apply SepE in Hm as [Hm Hm']. apply Hm'. apply Hind...
  intros x Hx. apply SepE in Hx as [_ Hp].
  apply Hbr in Hp as Hx. apply CProdE2 in Hx as [Hx _].
  destruct (classic (x ∈ B)) as [|Hx']... exfalso.
  assert (x ∈ A - B) by (apply SepI; auto).
  apply Hmin in H as []; firstorder.
Qed.

(* 线序集良序当且仅当其归纳子集与自身相等 *)
Theorem woset_iff_inductive : ∀ A R, loset A R →
  woset A R ↔ ∀ B, inductive_subset B A R → B = A.
Proof with eauto; try congruence.
  intros A R Hlo.
  split. { apply transfinite_induction. }
  intros Hind. split... intros C [c Hc] Hsub.
  (* strict lower bounds of C *)
  set {t ∊ A | λ t, ∀x ∈ C, (t <ᵣ x) R} as B.
  destruct (classic (inductive_subset B A R)).
  - exfalso. apply Hsub in Hc as Hc'.
    apply Hind in H. rewrite <- H in Hc'.
    apply SepE in Hc' as [_ Hp]. apply Hp in Hc.
    eapply lo_irrefl...
  - apply not_and_or in H as []. {
      exfalso. apply H. intros x Hx. apply SepE1 in Hx...
    }
    apply set_not_all_ex_not in H as [t [Hta H]].
    apply imply_to_and in H as [Hseg Htb].
    cut (∀x ∈ C, (t ≤ᵣ x) R). {
      intros H. exists t. split...
      destruct (classic (t ∈ C)) as [|Htc]...
      exfalso. apply Htb. apply SepI...
      intros x Hx. pose proof (H x Hx) as []...
    }
    intros x Hxc. apply Hsub in Hxc as Hxa.
    destruct (classic (t = x)). right...
    eapply lo_connected in H as [|Hxt]... left...
    exfalso. assert (Hxb: x ∈ B). {
      apply Hseg. apply segI...
    }
    apply SepE in Hxb as [_ H]. apply H in Hxc.
    eapply lo_irrefl...
Qed.

(* 以前节为定义域的所有函数 *)
Definition SegFuncs : set → set → set → set := λ A R B,
  {f ∊ 𝒫 (A × B) | λ f, ∃ t ∈ A, f: seg t R ⇒ B}.

(* 超限递归定理初级表述 *)
Definition transfinite_recursion_preliminary_form :=
  ∀ A R B G, woset A R → G: SegFuncs A R B ⇒ B →
  ∃! F, F: A ⇒ B ∧ ∀t ∈ A, F[t] = G[F ↾ seg t R].

(* 超限递归定理模式 *)
Definition transfinite_recursion_schema :=
  ∀ A R γ, woset A R → (∀ f, ∃! y, γ f y) →
  ∃! F, is_function F ∧ dom F = A ∧ ∀t ∈ A, γ (F ↾ seg t R) F[t].

(* 超限递归定理模式蕴含其初级表述 *)
Fact transfinite_recursion_schema_to_preliminary_form :
  transfinite_recursion_schema →
  transfinite_recursion_preliminary_form.
Proof with eauto; try congruence.
  intros Schema A R B G Hwo HG.
  set (λ f y, y = G[f]) as γ.
  pose proof (Schema A R γ Hwo) as [[F [HF [Hd Hrec]]] Hu]. {
    intros f. split. exists (G[f])... intros...
  }
  set {x ∊ A | λ x, F[x] ∈ B} as A'.
  replace A with A' in *. {
    assert (Hr: ran F ⊆ B). {
      intros y Hy. apply ranE in Hy as [x Hp].
      apply domI in Hp as Hx. rewrite Hd in Hx.
      apply func_ap in Hp... apply SepE2 in Hx...
    }
    split.
    - exists F. split. split... intros t Ht. rewrite Hrec...
    - intros f1 f2 [[Hf1 [Hd1 Hr1]] H1] [[Hf2 [Hd2 Hr2]] H2].
      apply Hu; split...
  }
  eapply transfinite_induction... split.
  - intros x Hx. apply SepE1 in Hx...
  - intros t Ht Hsub. apply SepI...
    rewrite Hrec... eapply ap_ran... apply SepI.
    + apply PowerAx. intros p Hp.
      apply restrE1 in Hp as [a [b [Ha [Hp Heq]]]]. subst p.
      apply Hsub in Ha. apply SepE in Ha as [Ha HFa].
      apply func_ap in Hp... apply CProdI...
    + exists t. split... split; [|split].
      * apply restr_func...
      * apply restr_dom... eapply sub_tran. apply Hsub.
        rewrite Hd. intros x Hx. apply SepE1 in Hx...
      * intros y Hy. apply ranE in Hy as [x Hp].
        apply restrE2 in Hp as [Hp Hx]. apply func_ap in Hp...
        apply Hsub in Hx. apply SepE2 in Hx...
Qed.

(* 替代公理再考 *)
Local Fact sometimes_replacement_is_simpler_than_separation : ∀ A,
  {λ a, 𝒫 a | a ∊ A} = {x ∊ 𝒫 𝒫 ⋃A | λ x, ∃a ∈ A, x = 𝒫 a}.
Proof with auto.
  intro. apply ExtAx. split; intros Hx.
  - apply ReplAx in Hx as [a [Ha Heq]]. subst x.
    apply SepI. apply ex2_10... exists a. split...
  - apply SepE in Hx as [_ [a [Ha Heq]]]. subst x.
    apply ReplAx. exists a. split...
Qed.

(* 超限递归定理模式的证明 *)
Theorem transfinite_recursion : transfinite_recursion_schema.
Proof with eauto; try congruence.
  intros A R γ Hwo Hu.
  assert (H := Hwo). destruct H as [Hlo Hmin].
  assert (H := Hlo). destruct H as [Hbr [Htr _]].
  set (λ t, seg t R) as seg.
  set (λ t, head t A R) as head.
  set (λ t ν, dom ν = head t ∧ ∀x ∈ dom ν, γ (ν ↾ seg x) ν[x]) as γ_constr.
  assert (HL1: ∀ ν₁ ν₂, ∀ t₁ t₂ ∈ A, (t₁ ≤ᵣ t₂) R →
    is_function ν₁ → is_function ν₂ → γ_constr t₁ ν₁ → γ_constr t₂ ν₂ →
    ∀x ∈ A, (x ≤ᵣ t₁) R → ν₁[x] = ν₂[x]
  ). {
    intros ν₁ ν₂ t₁ Ht₁ t₂ Ht₂ Htle Hf₁ Hf₂ [Hd₁ Hr₁] [Hd₂ Hr₂].
    destruct (classic (∀x ∈ A, (x ≤ᵣ t₁) R → ν₁[x] = ν₂[x]))...
    exfalso. apply set_not_all_ex_not in H as [s [Hs H]].
    apply imply_to_and in H as [Hst1 Hnqt].
    set {x ∊ A | λ x, ν₁ [x] ≠ ν₂ [x]} as B.
    specialize Hmin with B as [m [Hm Hmin]].
      { exists s. apply SepI... }
      { intros x Hx. apply SepE1 in Hx... }
    apply SepE in Hm as [Hm Hnqm]. apply Hnqm.
    assert (Hms: (m ≤ᵣ s) R) by (apply Hmin; apply SepI; auto).
    assert (Hmt₁: (m ≤ᵣ t₁) R) by (apply (relLe_tranr m s t₁ R); auto).
    assert (Hmt₂: (m ≤ᵣ t₂) R) by (apply (relLe_tranr m t₁ t₂ R); auto).
    assert (Hmd₁: m ∈ head t₁) by (apply SepI; auto).
    assert (Hmd₂: m ∈ head t₂) by (apply SepI; auto).
    eapply Hu. apply Hr₁...
    replace (ν₁ ↾ seg m) with (ν₂ ↾ seg m). apply Hr₂...
    apply ExtAx. split; intros Hx.
    - apply restrE1 in Hx as [a [b [Ha [Hp Heqx]]]].
      subst x. apply restrI...
      apply SepE in Ha as [Ha Ham]. eapply dom_binRel in Ha...
      apply func_ap in Hp... apply func_point...
      rewrite Hd₁. apply SepI... apply (relLe_tranr a m t₁ R)... left...
      destruct (classic (ν₁[a] = ν₂[a])) as [|Hnq]... exfalso.
      assert (a ∈ B) by (apply SepI; auto).
      apply Hmin in H. eapply lo_not_leq_gt...
    - apply restrE1 in Hx as [a [b [Ha [Hp Heqx]]]].
      subst x. apply restrI...
      apply SepE in Ha as [Ha Ham]. eapply dom_binRel in Ha...
      apply func_ap in Hp... apply func_point...
      rewrite Hd₂. apply SepI... apply (relLe_tranr a m t₂ R)... left...
      destruct (classic (ν₁[a] = ν₂[a])) as [|Hnq]... exfalso.
      assert (a ∈ B) by (apply SepI; auto).
      apply Hmin in H. eapply lo_not_leq_gt...
  }
  assert (HL1_1: ∀ ν₁ ν₂, ∀ t ∈ A, is_function ν₁ → is_function ν₂ →
    γ_constr t ν₁ → γ_constr t ν₂ → ∀x ∈ A, (x ≤ᵣ t) R → ν₁[x] = ν₂[x]
  ). {
    intros ν₁ ν₂ t Ht Hf₁ Hf₂ Hγ₁ Hγ₂.
    eapply HL1... right...
  }
  assert (HL1_2: ∀ ν₁ ν₂, ∀ t ∈ A, is_function ν₁ → is_function ν₂ →
    γ_constr t ν₁ → γ_constr t ν₂ → ν₁ = ν₂
  ). {
    intros ν₁ ν₂ t Ht Hf₁ Hf₂ Hγ₁ Hγ₂.
    assert (H := Hγ₁). destruct H as [Hd₁ _].
    assert (H := Hγ₂). destruct H as [Hd₂ _].
    apply func_ext_intro... intros x Hx. rewrite Hd₁ in Hx.
    eapply HL1_1... apply SepE1 in Hx... apply SepE2 in Hx...
  }
  set (λ t ν, is_function ν ∧ γ_constr t ν) as ϕ.
  set {t ∊ A | λ t, ∃ ν, ϕ t ν} as A'.
  (* first time that ϕ_Repl is a must *)
  set (ϕ_Repl ϕ A') as ℋ.
  set (⋃ ℋ) as F.
  assert (Hϕ: ∀t ∈ A', ∃! ν, ϕ t ν). {
    intros t Ht. apply SepE in Ht as [Ht H]. split...
    intros ν μ [] []. eapply HL1_2...
  }
  assert (Hrepl: ∀ ν, ν ∈ ℋ ↔ is_function ν ∧ ∃t ∈ A, γ_constr t ν). {
    intros. split.
    - intros Hν. apply ϕ_ReplAx in Hν as [t [Ht [Hfν Hγ]]]; [|apply Hϕ].
      split... exists t. split... apply SepE1 in Ht...
    - intros [Hfν [t [Ht Hγ]]]. apply ϕ_ReplAx. apply Hϕ.
      exists t. split. apply SepI... exists ν. split... split...
  }
  assert (Hstar: ∀ x y, <x, y> ∈ F ↔ ∃ν ∈ ℋ, <x, y> ∈ ν). {
    intros. split.
    - intros Hp. apply UnionAx in Hp as [ν [Hν Hp]].
      exists ν. split...
    - intros [ν [Hν Hap]]. apply UnionAx.
      exists ν. split...
  }
  assert (Hhd: ∀ ν t x y, γ_constr t ν → <x, y> ∈ ν → x ∈ A ∧ (x ≤ᵣ t) R). {
    intros * [Hd _] Hp. apply domI in Hp as Hx.
    rewrite Hd in Hx. apply SepE in Hx...
  }
  assert (HfF: is_function F). {
    repeat split.
    - intros p Hp. apply UnionAx in Hp as [ν [Hν Hp]].
      apply Hrepl in Hν as [[Hrel _] _]. apply Hrel...
    - apply domE in H...
    - intros y₁ y₂ Hp₁ Hp₂.
      apply Hstar in Hp₁ as [ν₁ [Hν₁ Hp₁]].
      apply Hstar in Hp₂ as [ν₂ [Hν₂ Hp₂]].
      apply Hrepl in Hν₁ as [Hf₁ [t₁ [Ht₁ Hγ₁]]].
      apply Hrepl in Hν₂ as [Hf₂ [t₂ [Ht₂ Hγ₂]]].
      apply func_ap in Hp₁ as Hν₁... eapply Hhd in Hp₁ as [Hx Hhd₁]...
      apply func_ap in Hp₂ as Hν₂... eapply Hhd in Hp₂ as [_ Hhd₂]...
      destruct (classic (t₁ = t₂)) as [Heq|Hnq].
      + rewrite (HL1_1 ν₁ ν₂ t₁ Ht₁) in Hν₁...
      + eapply lo_connected in Hnq as []...
        * rewrite (HL1 ν₁ ν₂ t₁ Ht₁ t₂ Ht₂) in Hν₁... left...
        * rewrite (HL1 ν₂ ν₁ t₂ Ht₂ t₁ Ht₁) in Hν₂... left...
  }
  assert (HL2: ∀x ∈ dom F, γ (F ↾ seg x) F[x]). {
    intros x Hx. apply domE in Hx as [y Hp].
    apply Hstar in Hp as [ν [Hν Hpν]]. assert (Hν' := Hν).
    apply Hrepl in Hν' as [Hfν [t [Ht Hγν]]].
    apply domI in Hpν as Hx. apply Hγν in Hx as Hνx.
    assert (Heq1: F[x] = ν[x]). {
      apply func_ap... apply Hstar.
      exists ν. split... apply func_correct...
    }
    assert (Heq2: ν ↾ seg x = F ↾ seg x). {
      apply ExtAx. intros p. split; intros Hp.
      - apply restrE1 in Hp as [a [b [Ha [Hp Heq]]]]. subst p.
        apply restrI... apply Hstar. exists ν. split...
      - apply restrE1 in Hp as [a [b [Ha [Hp Heq]]]]. subst p.
        apply restrI... apply Hstar in Hp as [μ [Hμ Hp]].
        apply Hrepl in Hμ as [Hfμ [s [Hs Hγμ]]].
        assert (H := Hγμ). destruct H as [Hdμ _].
        assert (H := Hγν). destruct H as [Hdν _].
        apply domI in Hp as Hadμ. rewrite Hdμ in Hadμ.
        apply SepE in Hadμ as [HaA Has].
        assert (Hat: (a ≤ᵣ t) R). {
          rewrite Hdν in Hx. apply SepE in Hx as [Hx Hxt].
          apply SepE in Ha as [_ Hax]. left. eapply relLt_le_tranr...
        }
        apply func_ap in Hp... apply func_point...
        rewrite Hdν. apply SepI... subst b.
        destruct (classic (t = s)).
        + apply (HL1 ν μ t Ht s Hs)... right...
        + eapply lo_connected in H as []...
          * apply (HL1 ν μ t Ht s Hs)... left...
          * symmetry. apply (HL1 μ ν s Hs t Ht)... left...
    }
    congruence.
  }
  assert (HL3: dom F = A). {
    destruct (classic (dom F = A)) as [|Hnq]... exfalso.
    assert (Hps: dom F ⊂ A). {
      split... intros x Hx. apply domE in Hx as [y Hp].
      apply Hstar in Hp as [ν [Hν Hp]].
      apply Hrepl in Hν as [_ [t [_ Hγ]]]. eapply Hhd...
    }
    set {x ∊ A | λ x, x ∉ dom F} as B.
    specialize Hmin with B as [t [Ht Hmin]]. {
      apply comp_nonempty in Hps as [a Ha].
      apply SepE in Ha as [Ha Ha']. exists a. apply SepI...
    } { 
      intros x Hx. apply SepE1 in Hx...
    }
    apply SepE in Ht as [Ht Ht']. apply Ht'.
    assert (Hseg: seg t = dom F). {
      apply ExtAx. split; intros Hx.
      - apply SepE in Hx as [Hx Hxt].
        apply (dom_binRel R A) in Hx...
        destruct (classic (x ∈ dom F))... exfalso.
        assert (Hxb: x ∈ B) by (apply SepI; auto).
        apply Hmin in Hxb. eapply lo_not_leq_gt...
      - apply Hps in Hx as Hxa. apply segI...
        destruct (classic (x = t))...
        eapply lo_connected in H as []... exfalso.
        apply domE in Hx as [y Hp]. apply Hstar in Hp as [ν [Hν Hp]].
        apply Ht'. eapply domI. apply Hstar. exists ν. split...
        apply Hrepl in Hν as [Hfν [s [Hs [Hdν Hγ]]]].
        apply func_point... rewrite Hdν. apply SepI...
        apply domI in Hp as Hx. rewrite Hdν in Hx.
        apply SepE in Hx as [_ Hxs]. left. eapply relLt_le_tranr...
    }
    specialize Hu with F as [[y Hγ] _].
    set (F ∪ ⎨<t, y>⎬) as ν.
    assert (Hfs : is_function ⎨<t, y>⎬)
      by apply single_pair_is_func.
    assert (Hfν: is_function ν). {
      apply bunion_is_func...
      intros x Hx. apply BInterE in Hx as [H1 H2].
      rewrite dom_of_single_pair in H2. apply SingE in H2; subst...
    }
    assert (Hdν: dom ν = head t). {
      unfold ν. rewrite dom_of_bunion_func...
      rewrite dom_of_single_pair, <- Hseg.
      apply seg_with_single_eq_head...
    }
    eapply domI. apply Hstar. exists ν. split; revgoals.
    apply func_point... rewrite Hdν. apply SepI... right...
    apply Hrepl. split... exists t. split... split...
    intros x Hx. rewrite Hdν in Hx.
    apply SepE in Hx as [Hx [Hxt|Heqx]].
    - assert (Hxs: x ∈ seg t) by (apply segI; auto).
      rewrite Hseg in Hxs. apply HL2 in Hxs.
      assert (Heq1: ν ↾ seg x = F ↾ seg x). {
        apply ExtAx. intros p. split; intros Hp.
        - apply restrE1 in Hp as [a [b [Ha [Hp Heq]]]]. subst p.
          apply restrI... apply BUnionE in Hp as []...
          exfalso. apply SingE in H. apply op_iff in H as []; subst.
          apply SepE in Ha as [_ Htx]. eapply lo_irrefl...
        - apply restrE1 in Hp as [a [b [Ha [Hp Heq]]]]. subst p.
          apply restrI... apply BUnionI1...
      }
      assert (Heq2: ν[x] = F[x]). {
        apply func_ap... apply BUnionI1. apply func_correct...
        rewrite <- Hseg. apply segI...
      }
      congruence.
    - assert (Heq1: ν ↾ seg t = F). {
        apply ExtAx. intros p. split; intros Hp.
        - apply restrE1 in Hp as [a [b [Ha [Hp Heq]]]]. subst p.
          apply BUnionE in Hp as []...
          exfalso. apply SingE in H. apply op_iff in H as []; subst.
          apply SepE in Ha as [_ Htx]. eapply lo_irrefl...
        - apply func_pair in Hp as Heqp... rewrite Heqp in *.
          apply restrI. apply domI in Hp... apply BUnionI1...
      }
      assert (Heq2: ν[t] = y). {
        apply func_ap... apply BUnionI2...
      }
      congruence.
  }
  rewrite HL3 in HL2.
  split. exists F. split...
  (* uniqueness *)
  intros F₁ F₂ [HfF₁ [HdF₁ Hγ₁]] [HfF₂ [HdF₂ Hγ₂]].
  apply func_ext_intro...
  intros x Hx. rewrite HdF₁ in Hx.
  set {t ∊ A | λ t, F₁[t] = F₂[t]} as B.
  replace A with B in Hx. apply SepE2 in Hx...
  eapply transfinite_induction...
  split. intros t Ht. apply SepE1 in Ht...
  intros t Ht Hsub. apply SepI...
  apply Hγ₁ in Ht as H1. apply Hγ₂ in Ht as H2.
  replace (F₂ ↾ EST7_2.seg t R) with (F₁ ↾ EST7_2.seg t R) in H2. eapply Hu...
  apply ExtAx. intros w. split; intros Hw.
  - apply restrE1 in Hw as [a [b [Ha [Hp Hw]]]]. subst w.
    apply restrI... apply Hsub in Ha. apply SepE in Ha as [Ha Heq].
    apply func_ap in Hp... apply func_point...
  - apply restrE1 in Hw as [a [b [Ha [Hp Hw]]]]. subst w.
    apply restrI... apply Hsub in Ha. apply SepE in Ha as [Ha Heq].
    apply func_ap in Hp... apply func_point...
Qed.

Theorem transfinite_recursion_pre : transfinite_recursion_preliminary_form.
Proof.
  apply transfinite_recursion_schema_to_preliminary_form.
  apply transfinite_recursion.
Qed.

Module Import TransfiniteRecursion.

Definition spec := λ A R γ F,
  is_function F ∧ dom F = A ∧ ∀t ∈ A, γ (F ↾ seg t R) F[t].

Definition constr := λ A R γ,
  epsilon (inhabits ∅) (λ F, spec A R γ F).

Lemma spec_intro : ∀ A R γ, woset A R →
  (∀ x, ∃! y, γ x y) → spec A R γ (constr A R γ).
Proof.
  intros. apply (epsilon_spec (inhabits ∅) (λ F, spec A R γ F)).
  apply transfinite_recursion; auto.
Qed.

End TransfiniteRecursion.

(** 传递闭包 **)

Module Import TransitiveClosureDef.

Definition γ := λ A x y, y = A ∪ ⋃ ⋃ (ran x).

Definition F := λ A, constr ω Lt (γ A).

Lemma f_spec : ∀ A, spec ω Lt (γ A) (F A).
Proof.
  intros. apply spec_intro. apply Lt_wellOrder.
  intros f. split. exists (A ∪ ⋃ ⋃ (ran f)). congruence. congruence.
Qed.

Fact f_0 : ∀ A, (F A)[0] = A.
Proof with nauto.
  intros. destruct (f_spec A) as [Hf [Hd Hγ]].
  rewrite Hγ, seg_0_Lt, restr_to_empty, ran_of_empty,
    union_empty, union_empty, bunion_empty...
Qed.

Fact f_1 : ∀ A, (F A)[1] = A ∪ ⋃ A.
Proof with nauto.
  intros. destruct (f_spec A) as [Hf [Hd Hγ]].
  rewrite Hγ... replace (ran (F A ↾ seg 1 Lt)) with ⎨A⎬.
  rewrite union_single...
  apply ExtAx; intros y; split; intros Hy.
  - apply SingE in Hy; subst.
    apply (ranI _ 0). apply restrI.
    + apply segI. apply binRelI... apply suc_has_n.
    + apply func_point... rewrite Hd... apply f_0.
  - apply ranE in Hy as [].
    apply restrE2 in H as [Hp Hx].
    apply SepE in Hx as [_ Hx1].
    apply binRelE3 in Hx1.
    apply BUnionE in Hx1 as []. exfalso0.
    apply SingE in H; subst. apply func_ap in Hp...
    rewrite f_0 in Hp; subst...
Qed.

Lemma f_ap_preserve_lt : ∀ A, ∀ n m ∈ ω,
  n ∈ m → (F A)[n] ⊆ (F A)[m].
Proof with auto.
  intros A n Hn m Hm Hnm.
  destruct (f_spec A) as [Hf [Hd Hγ]].
  rewrite Hγ, Hγ... intros y Hy.
  apply BUnionE in Hy as [|Hy]; [apply BUnionI1|apply BUnionI2]...
  apply UnionAx in Hy as [a [Ha Hy]].
  apply UnionAx in Ha as [b [Hb Ha]].
  apply UnionAx. exists a. split...
  apply UnionAx. exists b. split...
  apply ranE in Hb as [x Hp].
  apply restrE2 in Hp as [Hp Hx].
  apply (ranI _ x). apply restrI...
  apply segI. apply SepE in Hx as [_ Hxn].
  eapply Lt_tranr; eauto. apply binRelI...
Qed.

Lemma f_n : ∀ A, ∀n ∈ ω, (F A)[n⁺] = A ∪ ⋃ (F A)[n].
Proof with auto; try congruence.
  intros A n Hn.
  destruct (f_spec A) as [Hf [Hd Hγ]].
  assert (Hnp: n⁺ ∈ ω) by (apply ω_inductive; auto).
  rewrite Hγ...
  apply ExtAx; intros y; split; intros Hy;
  (apply BUnionE in Hy as [|Hy]; [apply BUnionI1|apply BUnionI2])...
  - apply UnionAx in Hy as [a [Ha Hy]].
    apply UnionAx in Ha as [b [Hb Ha]].
    apply ranE in Hb as [c Hp].
    apply restrE2 in Hp as [Hp Hc].
    apply func_ap in Hp... subst.
    apply SepE in Hc as [_ Hc].
    apply binRelE2 in Hc as [Hc [_ Hcn]].
    apply UnionAx. exists a. split...
    apply leq_iff_lt_suc in Hcn as []...
    apply (f_ap_preserve_lt _ c)...
  - apply UnionAx in Hy as [a [Ha Hy]].
    apply UnionAx. exists a. split...
    apply UnionAx. exists ((F A)[n]). split...
    apply (ranI _ n). apply restrI.
    apply segI. apply binRelI... apply suc_has_n.
    apply func_correct...
Qed.

Lemma f_inclusion : ∀ A, ∀n ∈ ω, ∀a ∈ (F A)[n], a ⊆ (F A)[n⁺].
Proof with neauto.
  intros A n Hn.
  set {n ∊ ω | λ n, ∀a ∈ (F A)[n], a ⊆ (F A)[n⁺]} as N.
  ω_induction N Hn; intros a Ha x Hx.
  - rewrite f_0 in Ha. rewrite f_1.
    apply BUnionI2. apply UnionAx. exists a. split...
  - rewrite f_n in Ha...
    rewrite f_n, f_n; [..|apply ω_inductive]...
    apply BUnionE in Ha as []; apply BUnionI2.
    + apply UnionAx. exists a. split... apply BUnionI1...
    + apply UnionAx. exists a. split... apply BUnionI2...
Qed.

End TransitiveClosureDef.

Definition TransitiveClosure := λ A, ⋃ (ran (F A)).
Notation "'𝗧𝗖' A" := (TransitiveClosure A) (at level 70).

(* 传递闭包是传递集 *)
Theorem tc_trans : ∀ A, trans (𝗧𝗖 A).
Proof with auto; try congruence.
  intros A x y Hxy Hy.
  destruct (f_spec A) as [Hf [Hd _]].
  apply UnionAx in Hy as [a [Ha Hy]].
  apply ranE in Ha as [n Hp]. apply domI in Hp as Hn.
  apply func_ap in Hp... subst a.
  apply f_inclusion in Hy... apply Hy in Hxy.
  apply UnionAx. exists ((F A)[n⁺]). split...
  eapply ranI. apply func_point...
  rewrite Hd. apply ω_inductive...
Qed.

(* 传递闭包包含原集合 *)
Theorem tc_contains : ∀ A, A ⊆ 𝗧𝗖 A.
Proof with nauto.
  intros A x Hx.
  destruct (f_spec A) as [Hf [Hd _]].
  apply UnionAx. exists A. split...
  apply (ranI _ 0). apply func_point...
  rewrite Hd... apply f_0.
Qed.
