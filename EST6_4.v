(** Based on "Elements of Set Theory" Chapter 6 Part 4 **)
(** Coq coding by choukh, Sep 2020 **)

Require Export ZFC.EST6_3.

(*** EST第六章4：选择公理的系统考察：基数的三歧性，佐恩引理，
  阿列夫零是最小的无限基数，戴德金无穷 ***)

(* 选择公理的等效表述1：可以从关系中选出函数 *)
Definition AC_I : Prop := ∀ R,
  is_relation R → ∃ F, is_function F ∧ F ⊆ R ∧ dom F = dom R.

(* 选择公理等效表述2：非空集合的笛卡尔积非空 *)
Definition AC_II : Prop := ∀ I X,
  (∀i ∈ I, ⦿ X[i]) → ⦿ InfCProd I X.

(* 选择公理等效表述3：存在选择函数 *)
Definition AC_III : Prop := ∀ A, ∃ F, is_function F ∧
  dom F = {x ∊ 𝒫 A | nonempty} ∧ (∀ B, ⦿ B → B ⊆ A → F[B] ∈ B).

(* 选择公理等效表述4：存在单选集 *)
Definition AC_IV : Prop := ∀ 𝒜,
  (* a 子集非空 *) (∀A ∈ 𝒜, ⦿ A) →
  (* b 子集不交 *) (∀ A B ∈ 𝒜, A ≠ B → disjoint A B) →
  ∃ C, ∀A ∈ 𝒜, ∃ x, A ∩ C = ⎨x⎬.

(* 选择公理等效表述5：基数有可比较性 *)
Definition AC_V : Prop := ∀ A B, A ≼ B ∨ B ≼ A.

(* 链：子集关系的全序集 *)
Definition is_chain : set → Prop := λ ℬ,
  ∀ C D ∈ ℬ, C ⊆ D ∨ D ⊆ C.

(* 选择公理等效表述6：佐恩引理：若偏序集中任意链均有上界，则该偏序集存在极大元 *)
Definition AC_VI : Prop := ∀ 𝒜,
  (∀ ℬ, is_chain ℬ → ℬ ⊆ 𝒜 → ⋃ℬ ∈ 𝒜) →
  ∃M ∈ 𝒜, ∀A ∈ 𝒜, M ⊈ A.

Theorem AC_I_to_II : AC_I → AC_II.
Proof with eauto.
  unfold AC_I, AC_II. intros * AC1 I X Hxi.
  set (I × ⋃{λ i, X[i] | i ∊ I}) as P.
  set {p ∊ P | λ p, π2 p ∈ X[π1 p]} as R.
  assert (H: is_relation R) by apply sep_cp_is_rel.
  apply AC1 in H as [F [Hf [Hsub Hdeq]]].
  assert (Hdeq2: dom F = I). {
    rewrite Hdeq. apply ExtAx. intros i. split; intros Hi.
    - apply domE in Hi as [y Hp]. apply SepE in Hp as [Hp _].
      apply CProdE1 in Hp as [Hi _]. zfcrewrite.
    - apply Hxi in Hi as Hx. destruct Hx.
      eapply domI. apply SepI. apply CProdI...
      eapply FUnionI... zfcrewrite.
  }
  exists F. apply SepI.
  + apply SepI. rewrite PowerAx. intros x Hp.
    apply func_pair in Hp as Hxeq... rewrite Hxeq in *.
    apply domI in Hp as Hd. rewrite Hdeq2 in Hd.
    apply Hsub in Hp. apply SepE in Hp as [_ Hp]. zfcrewrite.
    apply CProdI... eapply FUnionI... split... split...
    intros y Hy. apply ranE in Hy as [i Hp].
    apply Hsub in Hp. apply SepE in Hp as [Hp _].
    apply CProdE1 in Hp as [_ Hy]. zfcrewrite.
  + intros i Hi. rewrite <- Hdeq2 in Hi.
    apply func_correct in Hi... apply Hsub in Hi.
    apply SepE in Hi as [_ Hy]. zfcrewrite.
Qed.

Theorem AC_II_to_IV : AC_II → AC_IV.
Proof with eauto.
  unfold AC_II, AC_IV. intros AC2 𝒜 Hi Hdj.
  destruct (AC2 𝒜 (Ident 𝒜)) as [f Hf]. {
    intros A HA. rewrite ident_ap... apply Hi...
  }
  apply SepE in Hf as [Hf Hin].
  apply arrow_iff in Hf as [Hf [Hd _]].
  exists (ran f). intros A HA. exists (f[A]). apply sub_asym.
  - intros y Hy. apply BInterE in Hy as [H1 H2].
    apply ranE in H2 as [x Hp]. apply domI in Hp as Hx.
    rewrite Hd in Hx. apply Hin in Hx as Hfx. rewrite ident_ap in Hfx...
    apply func_ap in Hp... subst y. 
    destruct (classic (A = x)). subst x...
    exfalso. apply Hdj in H... eapply disjointE...
  - apply in_impl_sing_sub. apply BInterI.
    + rewrite <- (ident_ap 𝒜 A) at 2... apply Hin...
    + eapply ap_ran... split...
Qed.

Theorem AC_IV_to_III : AC_IV → AC_III.
Proof with eauto.
  unfold AC_IV, AC_III. intros AC4 A.
  set {x ∊ 𝒫 A | nonempty} as A'.
  set {λ B, ⎨B⎬ × B | B ∊ A'} as 𝒜.
  destruct AC4 with 𝒜 as [C Hsg]. {
    intros x Hx. apply ReplAx in Hx as [B [HB Hx]].
    apply SepE in HB as [_ [b Hb]]. subst x.
    exists <B, b>. apply CProdI...
  } {
    intros x Hx y Hy Hnq.
    apply ReplAx in Hx as [B [_ Hx]].
    apply ReplAx in Hy as [C [_ Hy]].
    apply disjointI. intros [p [H1 H2]]. apply Hnq. subst.
    apply cprod_iff in H1 as [a [Ha [b [Hb H1]]]].
    apply cprod_iff in H2 as [c [Hc [d [Hd H2]]]]. subst.
    apply SingE in Ha. apply SingE in Hc.
    apply op_iff in H2 as []. congruence.
  }
  assert (Hstar: ∀x ∈ ⋃ 𝒜, ∃ B, B ∈ A' ∧ x ∈ ⎨B⎬ × B). {
    intros x Hx. apply UnionAx in Hx as [p [Hp Hx]].
    apply ReplAx in Hp as [B [HB Hp]]. subst. exists B. split...
  }
  assert (Hcp: ∀B ∈ A', ⎨B⎬ × B ∈ 𝒜). {
    intros B HB. apply ReplAx. exists B. split...
  }
  set (C ∩ ⋃𝒜) as F.
  assert (Hf: is_function F). {
    repeat split.
    - intros x Hx. apply BInterE in Hx as [_ Hx].
      apply Hstar in Hx as [B [_ Hp]].
      apply cprod_iff in Hp as [a [Ha [b [Hb Hp]]]].
      apply SingE in Ha. subst...
    - apply domE in H...
    - intros y1 y2 H1 H2.
      apply BInterE in H1 as [Hc1 H1].
      apply BInterE in H2 as [Hc2 H2].
      apply Hstar in H1 as [B1 [_ H1]].
      apply Hstar in H2 as [B2 [HB2 H2]].
      apply cprod_iff in H1 as [a [Ha [b [Hb H1]]]].
      apply cprod_iff in H2 as [c [Hc [d [Hd H2]]]].
      apply SingE in Ha. apply SingE in Hc.
      apply op_iff in H1 as []. apply op_iff in H2 as []. subst.
      apply Hcp in HB2 as H0.
      assert (H1: <B2, b> ∈ ⎨B2⎬ × B2 ∩ C).
        { apply BInterI... apply CProdI... }
      assert (H2: <B2, d> ∈ ⎨B2⎬ × B2 ∩ C).
        { apply BInterI... apply CProdI... }
      apply Hsg in H0 as [x Hx]. rewrite Hx in H1, H2.
      apply SingE in H1. apply SingE in H2. subst.
      apply op_iff in H2 as []...
  }
  exists F. split... split.
  - apply ExtAx. split; intros Hx.
    + apply domE in Hx as [y Hp].
      apply BInterE in Hp as [_ Hp].
      apply Hstar in Hp as [B [HB Hp]].
      apply CProdE1 in Hp as [Hx _]. zfcrewrite.
      apply SingE in Hx. subst...
    + assert (H: ⎨x⎬ × x ∈ 𝒜). { apply ReplAx. exists x. split... }
      pose proof (Hsg _ H) as [p Heq].
      assert (Hp: p ∈ ⎨x⎬ × x ∩ C). { rewrite Heq... }
      apply BInterE in Hp as [H1 H2]. assert (H1' := H1).
      apply cprod_iff in H1 as [a [Ha [b [Hb H1]]]].
      apply SingE in Ha. subst. eapply domI. apply BInterI...
      apply UnionAx. exists (⎨x⎬ × x). split...
  - intros B Hi Hsub.
    assert (HB: B ∈ A'). { apply SepI... apply PowerAx... }
    apply Hcp in HB. pose proof (Hsg _ HB) as [p Heq].
    assert (Hp: p ∈ ⎨B⎬ × B ∩ C). { rewrite Heq... }
    apply BInterE in Hp as [H1 H2].
    apply cprod_iff in H1 as [a [Ha [b [Hb H1]]]].
    apply SingE in Ha. subst. cut (F[B] = b). congruence.
    apply func_ap... apply BInterI... apply UnionAx.
    exists (⎨B⎬ × B). split... apply CProdI...
Qed.

Theorem AC_III_to_I : AC_III → AC_I.
Proof with auto.
  unfold AC_III, AC_I. intros AC3 R Hrel.
  specialize AC3 with (ran R) as [G [Hgf [Hgd Hgr]]].
  set (λ x, {y ∊ ran R | λ y, <x, y> ∈ R}) as ℬ.
  set (Func (dom R) (ran R) (λ x, G[ℬ x])) as F.
  assert (Hstar: ∀x ∈ dom R, <x, G[ℬ x]> ∈ R). {
    intros x Hx. cut (G[ℬ x] ∈ ℬ x).
    intros H. apply SepE in H as []...
    apply domE in Hx as [y Hp].
    apply ranI in Hp as Hr. apply Hgr. exists y.
    apply SepI... intros z Hz. apply SepE in Hz as []...
  }
  assert (Hf: F: dom R ⇒ ran R). {
    apply meta_maps_into. intros x Hx.
    eapply ranI. apply Hstar...
  }
  destruct Hf as [Hff [Hfd _]].
  exists F. split; [|split]...
  intros p Hp. apply SepE in Hp as [H1 H2].
  apply cprod_iff in H1 as [a [Ha [b [Hb Hp]]]].
  subst. zfcrewrite. subst. apply Hstar...
Qed.

Theorem AC_VI_to_I : AC_VI → AC_I.
Proof with eauto.
  unfold AC_VI, AC_I. intros Zorn R Hrel.
  set {f ∊ 𝒫 R | λ f, is_function f} as 𝒜.
  specialize Zorn with 𝒜 as [M [HM Hmax]]. {
    intros ℬ Hchn Hsub.
    assert (Hu: ⋃ ℬ ∈ 𝒫 R). {
      apply PowerAx. intros x Hx.
      apply UnionAx in Hx as [B [HB Hx]].
      apply Hsub in HB. apply SepE in HB as [HB _].
      apply PowerAx in HB. apply HB...
    }
    apply SepI... repeat split.
    - intros x Hx. apply Hrel. apply PowerAx in Hu. apply Hu...
    - apply domE in H...
    - intros y1 y2 H1 H2.
      apply UnionAx in H1 as [g [Hg H1]].
      apply UnionAx in H2 as [h [Hh H2]].
      pose proof (Hchn _ Hg _ Hh) as [Hgh|Hhg].
      + apply Hsub in Hh. apply SepE in Hh as [_ Hh].
        apply Hgh in H1. eapply func_sv...
      + apply Hsub in Hg. apply SepE in Hg as [_ Hg].
        apply Hhg in H2. eapply func_sv...
  }
  exists M. apply SepE in HM as [Hsub Hf].
  apply PowerAx in Hsub. split; [|split]...
  destruct (classic (dom M = dom R)) as [|Hnq]... exfalso.
  assert (Hps: dom M ⊂ dom R). {
    split... intros x Hx. apply domE in Hx as [y Hp].
    eapply domI. apply Hsub...
  }
  apply comp_inhabited in Hps as [a Ha].
  apply SepE in Ha as [Ha Hb]. apply domE in Ha as [b Hab].
  set (M ∪ ⎨<a, b>⎬) as M'. cut (M' ∈ 𝒜). {
    intros HM'. apply Hmax in HM'.
    apply HM'. intros p Hp. apply BUnionI1...
  }
  apply SepI.
  - apply PowerAx. intros p Hp. apply BUnionE in Hp as [].
    apply Hsub... apply SingE in H. subst...
  - apply bunion_func... apply single_pair_is_func.
    intros x Hx. exfalso. apply BInterE in Hx as [H1 H2].
    apply domE in H1 as [y1 H1].
    apply domE in H2 as [y2 H2].
    apply SingE in H2. apply op_iff in H2 as []; subst.
    apply Hb. eapply domI...
Qed.

Theorem AC_VI_to_V : AC_VI → AC_V.
Proof with eauto; try congruence.
  unfold AC_VI, AC_V. intros Zorn A B.
  set {f ∊ 𝒫 (A × B) | λ f, injective f} as 𝒜.
  specialize Zorn with 𝒜 as [M [HM Hmax]]. {
    intros ℬ Hchn Hsub.
    assert (Hu: ⋃ ℬ ∈ 𝒫 (A × B)). {
      apply PowerAx. intros x Hx.
      apply UnionAx in Hx as [C [HC Hx]].
      apply Hsub in HC. apply SepE in HC as [HC _].
      apply PowerAx in HC. apply HC...
    }
    apply SepI... apply PowerAx in Hu. split; [split|].
    - intros x Hx. apply Hu in Hx. apply CProdE2 in Hx...
    - split. apply domE in H...
      intros y1 y2 H1 H2.
      apply UnionAx in H1 as [g [Hg H1]].
      apply UnionAx in H2 as [h [Hh H2]].
      pose proof (Hchn _ Hg _ Hh) as [Hgh|Hhg].
      + apply Hsub in Hh. apply SepE in Hh as [_ [Hh _]].
        apply Hgh in H1. eapply func_sv...
      + apply Hsub in Hg. apply SepE in Hg as [_ [Hg _]].
        apply Hhg in H2. eapply func_sv...
    - intros y Hy. split. apply ranE in Hy...
      intros x1 x2 H1 H2.
      apply UnionAx in H1 as [g [Hg H1]].
      apply UnionAx in H2 as [h [Hh H2]].
      pose proof (Hchn _ Hg _ Hh) as [Hgh|Hhg].
      + apply Hsub in Hh. apply SepE in Hh as [_ Hh].
        apply Hgh in H1. eapply injectiveE...
        eapply domI... eapply domI... destruct Hh as [Hh _].
        apply func_ap in H1... apply func_ap in H2...
      + apply Hsub in Hg. apply SepE in Hg as [_ Hg].
        apply Hhg in H2. eapply injectiveE...
        eapply domI... eapply domI... destruct Hg as [Hg _].
        apply func_ap in H1... apply func_ap in H2...
  }
  apply SepE in HM as [Hsub Hinj]. apply PowerAx in Hsub.
  destruct (classic (dom M = A ∨ ran M = B)). {
    destruct H; [left; exists M|right; exists (M⁻¹)].
    - split... split... intros y Hy. apply ranE in Hy as [x Hp].
      apply Hsub in Hp. apply CProdE1 in Hp as []; zfcrewrite.
    - split. apply inv_injective... split.
      rewrite inv_dom... rewrite inv_ran.
      intros x Hx. apply domE in Hx as [y Hp].
      apply Hsub in Hp. apply CProdE1 in Hp as []; zfcrewrite.
  }
  exfalso. apply not_or_and in H as [Hnq1 Hnq2].
  assert (Hps1: dom M ⊂ A). {
    split... intros x Hx. apply domE in Hx as [y Hp].
    apply Hsub in Hp. apply CProdE1 in Hp as []; zfcrewrite.
  }
  assert (Hps2: ran M ⊂ B). {
    split... intros y Hy. apply ranE in Hy as [x Hp].
    apply Hsub in Hp. apply CProdE1 in Hp as []; zfcrewrite.
  }
  apply comp_inhabited in Hps1 as [a Ha].
  apply comp_inhabited in Hps2 as [b Hb].
  apply SepE in Ha as [Ha Ha'].
  apply SepE in Hb as [Hb Hb'].
  set ((M ∪ ⎨<a, b>⎬)) as M'. cut (M' ∈ 𝒜). {
    intros HM'. apply Hmax in HM'.
    apply HM'. intros p Hp. apply BUnionI1...
  }
  assert (Hinj' := Hinj). destruct Hinj' as [Hf Hs].
  apply SepI; [|split].
  - apply PowerAx. intros p Hp. apply BUnionE in Hp as [].
    apply Hsub... apply SingE in H. subst. apply CProdI...
  - apply bunion_func... apply single_pair_is_func.
    intros x Hx. exfalso. apply BInterE in Hx as [H1 H2].
    apply domE in H1 as [y1 H1].
    apply domE in H2 as [y2 H2].
    apply SingE in H2. apply op_iff in H2 as []; subst.
    apply Ha'. eapply domI...
  - intros y Hy. split. apply ranE in Hy...
    intros x1 x2 H1 H2.
    apply BUnionE in H1 as [H1|H1]; apply BUnionE in H2 as [H2|H2].
    + eapply injectiveE... eapply domI... eapply domI...
      apply func_ap in H1... apply func_ap in H2...
    + exfalso. apply SingE in H2. apply op_iff in H2 as []; subst.
      apply Hb'. eapply ranI...
    + exfalso. apply SingE in H1. apply op_iff in H1 as []; subst.
      apply Hb'. eapply ranI...
    + apply SingE in H1. apply op_iff in H1 as []; subst.
      apply SingE in H2. apply op_iff in H2 as []; subst...
Qed.

Theorem ac1 : AC_I.
Proof. exact choose_func_from_rel. Qed.

Theorem ac2 : AC_II.
Proof. apply AC_I_to_II. apply ac1. Qed.

Theorem ac4 : AC_IV.
Proof. apply AC_II_to_IV. apply ac2. Qed.

Theorem ac3 : AC_III.
Proof. apply AC_IV_to_III. apply ac4. Qed.

(* 满射的定义域支配值域 *)
Lemma domain_of_surjection_dominate_range :
  ∀ A B F, F: A ⟹ B → B ≼ A.
Proof with auto.
  intros. apply right_inv_of_surjection_injective in H as [G [H _]].
  exists G. apply H.
Qed.

(* 对任意非空集合，存在到此集合的满射如果此集合被定义域支配 *)
Lemma surjective_if_domain_dominate_range :
  ∀ A B, ⦿ B → B ≼ A → ∃ F, F: A ⟹ B.
Proof with auto.
  intros * Hne [G HG].
  apply injection_is_func in HG as [HG Hi].
  apply (left_inv G B A HG Hne) in Hi as [F [HF Hid]].
  exists F. apply right_inv... exists G. split...
Qed.

(* 对任意非空集合，存在到此集合的满射当且仅当此集合被定义域支配 *)
Fact surjective_iff_domain_dominate_range :
  ∀ A B, ⦿ B → (∃ F, F: A ⟹ B) ↔ B ≼ A.
Proof with eauto.
  split; intros [F HF].
  - eapply domain_of_surjection_dominate_range...
  - apply surjective_if_domain_dominate_range... exists F...
Qed.

(* (可以不用选择公理) *)
(* 对任意非空集合，存在定义域为ω且值域为此集合的满射当且仅当此集合被ω支配 *)
Corollary surjective_iff_ω_dominate_range :
  ∀ B, ⦿ B → (∃ F, F: ω ⟹ B) ↔ B ≼ ω.
Proof.
  intros. apply surjective_iff_domain_dominate_range. apply H.
Qed.

(* 有限集在无限集里的补集是无限集 *)
Lemma comp_of_finite_is_infinite : ∀ A B, B ⊆ A →
  infinite A → finite B → infinite (A - B).
Proof with auto.
  intros A B Hsub Hinf [n [Hn H1]].
  intros [m [Hm H2]]. apply Hinf.
  exists (n + m). split. apply cardAdd_ω...
  rewrite <- (bunion_comp_parent B A)...
  unfold CardAdd. rewrite <- CardAx0.
  apply cardAdd_well_defined.
  - rewrite <- eqnum_cprod_single...
  - rewrite <- eqnum_cprod_single...
  - apply disjointI. intros [x [Hx1 Hx2]].
    apply SepE in Hx2 as []...
  - apply disjoint_cprod_0_1.
Qed.

(* ω是最小的无限集 *)
Theorem ω_is_the_least_infinite_set : ∀ A, infinite A → ω ≼ A.
Proof with neauto; try congruence.
  intros A Hinf. pose proof (ac3 A) as [F [HFf [HFd HFr]]].
  set {B ∊ 𝒫 A | λ B, finite B} as 𝒜.
  set (Func 𝒜 𝒜 (λ B, B ∪ ⎨F[A - B]⎬)) as ℋ.
  assert (Hℋ: ℋ: 𝒜 ⇒ 𝒜). {
    apply meta_maps_into. intros B HB.
    apply SepE in HB as [Hsub Hfin].
    apply PowerAx in Hsub. apply SepI.
    - apply PowerAx. intros x Hx.
      apply BUnionE in Hx as [Hx|Hx]. apply Hsub...
      apply SingE in Hx. subst. assert (A - B ⊆ A) by auto.
      apply H. apply HFr... apply infinite_set_nonempty.
      apply comp_of_finite_is_infinite...
    - apply finite_set_adding_one_still_finite...
  }
  pose proof (ω_recursion_0 ℋ 𝒜 ∅) as [h [Hh [Hh0 Hhn]]]... {
    apply SepI... apply empty_in_all_power.
  }
  assert (Hne: ∀n ∈ ω, ⦿ (A - h[n])). {
    intros n Hn. apply infinite_set_nonempty.
    apply comp_of_finite_is_infinite...
    + intros x Hx. ω_destruct n; subst n.
      * rewrite Hh0 in Hx. exfalso0.
      * rewrite Hhn in Hx...
        assert (ℋ[h[n']] ∈ 𝒜). { eapply ap_ran... eapply ap_ran... }
        apply SepE in H as [H _]. apply PowerAx in H. apply H...
    + assert (h[n] ∈ 𝒜) by (eapply ap_ran; eauto).
      apply SepE in H as []...
  }
  set (Func ω A (λ n, F[A - h[n]])) as g.
  exists g. apply meta_injective.
  - intros n Hn. assert (Hsub: A - h[n] ⊆ A) by auto.
    apply Hsub. apply HFr... apply Hne...
  - cut (∀ m n ∈ ω, m ∈ n → F [A - h[m]] ≠ F [A - h[n]]). {
      intros Hcut. intros m Hm n Hn Heq.
      destruct (classic (m = n))... exfalso.
      apply lt_connected in H as []; auto;
      [|symmetry in Heq]; eapply Hcut; revgoals...
    }
    intros m Hm n Hn Hmn Heq.
    assert (Hgm: F[A - h[m]] ∈ h[m⁺]). {
      rewrite Hhn... unfold ℋ.
      rewrite meta_func_ap; [|auto|eapply ap_ran]... apply BUnionI2...
    }
    assert (Hgn: F[A - h[n]] ∈ A - h[n]). {
      apply HFr... apply Hne...
    }
    cut (h[m⁺] ⊆ h[n]). {
      intros Hcut. apply Hcut in Hgm. apply SepE in Hgn as []...
    }
    clear Heq Hgm Hgn g. generalize dependent m.
    set {n ∊ ω | λ n, ∀ m, m ∈ ω → m ∈ n → h[m⁺] ⊆ h[n]} as N.
    ω_induction N Hn; intros k Hk Hlt. exfalso0.
    intros x Hx. apply BUnionE in Hlt as [].
    + apply IH in Hx... rewrite Hhn... unfold ℋ.
      rewrite meta_func_ap; [|auto|eapply ap_ran]... apply BUnionI1...
    + apply SingE in H. subst...
Qed.

(* ℵ₀是最小的无限基数 *)
Corollary aleph0_is_the_least_infinite_card : ∀ 𝜅,
  is_card 𝜅 → infinite 𝜅 → ℵ₀ ≤ 𝜅.
Proof with auto.
  intros 𝜅 Hcd Hinf. rewrite card_of_card...
  apply cardLeq_iff. apply ω_is_the_least_infinite_set...
Qed.

(* (可以不用选择公理) *)
(* ω的任意无限子集与ω等势 *)
Corollary any_infinite_subset_of_ω_eqnum_ω : ∀ N,
  N ⊆ ω → infinite N → N ≈ ω.
Proof.
  intros N Hsub Hinf.
  apply dominate_sub in Hsub.
  apply ω_is_the_least_infinite_set in Hinf.
  apply Schröeder_Bernstein; auto.
Qed.

(* 基数是有限基数当且仅当它小于ℵ₀ *)
Corollary card_is_finite_iff_lt_aleph0 : ∀ 𝜅,
  is_card 𝜅 → 𝜅 <𝐜 ℵ₀ ↔ finite 𝜅.
Proof with auto.
  intros 𝜅 Hcd. split.
  - intros [Hleq Hnq]. destruct (classic (finite 𝜅))... exfalso.
    apply aleph0_is_the_least_infinite_card in H...
    apply Hnq. apply cardLeq_asym...
  - intros [k [Hk Hqn]]. apply CardAx1 in Hqn.
    rewrite <- card_of_card, <- card_of_nat in Hqn... rewrite Hqn.
    apply cardLt_nat_aleph0...
Qed.

(* Check EST6_1.sub_of_finite_is_finite. *)
(* 有限集的子集是有限集(另一种证法) *)
Corollary sub_of_finite_is_finite : ∀ A B,
  A ⊆ B → finite B → finite A.
Proof with auto.
  intros * Hsub Hfin.
  rewrite set_finite_iff_card_finite.
  apply card_is_finite_iff_lt_aleph0...
  eapply cardLeq_lt_tran. apply cardLeq_iff.
  apply dominate_sub. apply Hsub.
  apply card_is_finite_iff_lt_aleph0...
  rewrite <- set_finite_iff_card_finite...
Qed.

(* 戴德金无穷：与自身的真子集等势的集合 *)
Definition dedekind_infinite : set → Prop := λ A, ∃ B, B ⊂ A ∧ A ≈ B.

(* 集合是无限集当且仅当它与自身的真子集等势 *)
Theorem infinite_iff_eqnum_proper_subset : ∀ A,
  dedekind_infinite A ↔ infinite A.
Proof with neauto; try congruence.
  split. intros [B [H1 H2]]. eapply infinite_if_eqnum_proper_sub...
  intros Hinf. apply ω_is_the_least_infinite_set in Hinf as [f Hf].
  apply injection_is_func in Hf as [Hf Hif]...
  assert (Hf' := Hf). destruct Hf' as [Hff [Hdf Hrf]].
  assert (Hf': f⁻¹: ran f ⇒ ω). {
    split. apply inv_func_iff_sr. destruct Hif...
    split. apply inv_dom. rewrite inv_ran...
  }
  assert (Hif': injective f⁻¹) by (apply inv_injective; auto).
  set (Func A (A - ⎨f[0]⎬) (λ x, match (ixm (x ∈ ran f)) with
    | inl _ => f[f⁻¹[x]⁺]
    | inr _ => x
  end)) as g.
  exists (A - ⎨f[0]⎬). split. {
    split... intros Heq.
    assert (Hf0: f[0] ∈ A)by (eapply ap_ran; neauto).
    rewrite <- Heq in Hf0. apply SepE in Hf0 as [_ H]. apply H...
  }
  exists g. apply meta_bijective.
  - intros x Hx. destruct (ixm (x ∈ ran f)).
    + apply SepI.
      * eapply ap_ran... apply ω_inductive. eapply ap_ran...
      * intros Hap. apply SingE in Hap.
        apply (suc_neq_0 (f⁻¹[x])). apply (injectiveE f)...
        rewrite Hdf. apply ω_inductive. eapply ap_ran... rewrite Hdf...
    + apply SepI... intros Heqx. apply SingE in Heqx. apply n.
      rewrite Heqx. eapply ranI. apply func_correct... rewrite Hdf...
  - intros x1 Hx1 x2 Hx2 Heq.
    assert (Hap: ∀x ∈ ran f, f⁻¹[x]⁺ ∈ dom f). {
      intros x Hx. rewrite Hdf. apply ω_inductive. eapply ap_ran...
    }
    destruct (ixm (x1 ∈ ran f)); destruct (ixm (x2 ∈ ran f))...
    + apply injectiveE in Heq; [|auto|apply Hap..]...
      apply suc_injective in Heq. apply (injectiveE f⁻¹)...
      rewrite inv_dom... rewrite inv_dom...
      eapply ap_ran... eapply ap_ran...
    + exfalso. apply n. rewrite <- Heq.
      eapply ranI. apply func_correct... apply Hap...
    + exfalso. apply n. rewrite Heq.
      eapply ranI. apply func_correct... apply Hap...
  - intros y Hy. apply SepE in Hy as [Hy Hy'].
    destruct (classic (y ∈ ran f)); revgoals. {
      exists y. split... destruct (ixm (y ∈ ran f))...
    }
    set (f⁻¹[y]) as n. ω_destruct n; subst n; [| |eapply ap_ran]...
    + exfalso. assert (Heqy: y = f[0]). {
        rewrite zero, <- H0, inv_ran_reduction...
      }
      apply Hy'. rewrite Heqy...
    + exists (f[n']). split. eapply ap_ran...
      destruct (ixm (f[n'] ∈ ran f)).
      * rewrite inv_dom_reduction... rewrite <- Hn'eq.
        rewrite inv_ran_reduction...
      * exfalso. apply n. eapply ranI. apply func_correct...
Qed.
