(** Based on "Elements of Set Theory" Chapter 4 Part 1 **)
(** Coq coding by choukh, May 2020 **)

Require Export ZFC.lib.Relation.

(*** EST第四章1：自然数，归纳原理，传递集，皮亚诺结构，ω递归定理 ***)

(** 自然数 **)
Definition is_nat := λ n, ∀ A, inductive A → n ∈ A.

Theorem ω_exists : ∃ ω, ∀ n, n ∈ ω ↔ is_nat n.
Proof with auto.
  exists {x ∊ 𝐈 | is_nat}. split.
  - intros Hn A HA. apply SepE in Hn as [_ H]. apply H in HA...
  - intros Hn. apply SepI. apply Hn. apply InfAx.
    intros A HA. apply Hn in HA...
Qed.

Definition ω := {n ∊ 𝐈 | is_nat}.

Lemma ω_has_0 : ∅ ∈ ω.
Proof with auto.
  apply SepI... apply InfAx. intros x []...
Qed.

Fact ω_neq_0 : ω ≠ ∅.
Proof.
  intros H. assert (∅ ∈ ω). apply ω_has_0.
  rewrite H in H0. exfalso0.
Qed.

(* ω是归纳集 *)
Theorem ω_inductive : inductive ω.
Proof with auto.
  split. apply ω_has_0.
  intros a Ha. apply SepE in Ha as [_ H]. apply SepI.
  - apply InfAx. apply H. apply InfAx.
  - intros A HA. apply H in HA as Ha.
    destruct HA as [_ H1]. apply H1...
Qed. 

Theorem ω_sub_inductive : ∀ A, inductive A → ω ⊆ A.
Proof. intros A Hi x Hx. apply SepE in Hx as [_ H]. auto. Qed.

(** 归纳原理 **)
Theorem ω_ind : ∀ x, x ⊆ ω → inductive x → x = ω.
Proof with auto.
  intros * Hs Hi. apply ExtAx. intros n. split; intros Hn.
  - apply Hs...
  - apply SepE in Hn as [_ Hn]. apply Hn in Hi...
Qed.

Ltac ω_induction N H := cut (N = ω); [
  intros ?Heq; rewrite <- Heq in H;
  apply SepE in H as []; auto |
  apply ω_ind; [
    intros ?x ?Hx; apply SepE in Hx as []; auto |
    split; [apply SepI; [apply ω_has_0 |]|]
  ]; [|
    intros ?m ?Hm; apply SepE in Hm as [?Hm ?IH];
    apply SepI; [apply ω_inductive; auto |]
  ]
].

Theorem pred_exists : ∀n ∈ ω, n ≠ ∅ → ∃n' ∈ ω, n = n'⁺.
Proof with auto.
  intros n Hn.
  set {n ∊ ω | λ n, n ≠ ∅ → ∃n' ∈ ω, n = n'⁺} as N.
  ω_induction N Hn.
  - intros. exfalso. apply H...
  - intros _. exists m. split...
Qed.

(* 传递集 *)
Definition trans :=
  λ X, ∀ a A, a ∈ A → A ∈ X → a ∈ X.

(* 传递集的成员都是该传递集的子集 *)
Example trans_ex_1 : ∀ x X, trans X → x ∈ X → x ⊆ X.
Proof. intros x X Htr Hx y Hy. eapply Htr; eauto. Qed.

(* 传递集的并集也是该传递集的成员 *)
Example trans_ex_2 : ∀ X, trans X → ⋃X ⊆ X.
Proof.
  intros X Htr y Hy.
  apply UnionAx in Hy as [A [H1 H2]].
  eapply Htr; eauto.
Qed.

Lemma trans_union_sub : ∀ A, trans A ↔ ⋃A ⊆ A.
Proof with eauto.
  split.
  - intros * Ht x Hx.
    apply UnionAx in Hx as [y [Hy Hx]]. eapply Ht...
  - intros Hs x n Hx Hn. apply Hs. eapply UnionI... 
Qed.

Lemma trans_sub : ∀ A, trans A ↔ ∀a ∈ A, a ⊆ A.
Proof with eauto.
  split.
  - intros * Ht a Ha x Hx. eapply Ht...
  - intros H x n Hx Hn. apply H in Hn. apply Hn...
Qed.

Lemma trans_sub_power : ∀ A, trans A ↔ A ⊆ 𝒫 A.
Proof with eauto.
  split.
  - intros * Ht a Ha. apply PowerAx.
    intros x Hx. eapply Ht...
  - intros H x n Hx Hn. apply H in Hn.
    rewrite PowerAx in Hn. apply Hn...
Qed.

Theorem trans_union_suc : ∀ a, trans a ↔ ⋃a⁺ = a.
Proof with auto.
  split; intros.
  - unfold Suc. rewrite ex2_21, union_single.
    apply ExtAx. split; intros Hx.
    + apply BUnionE in Hx as []...
      assert (⋃a ⊆ a) by (apply trans_union_sub; auto). apply H1...
    + apply BUnionI2...
  - unfold Suc in H. rewrite ex2_21, union_single in H.
    apply trans_union_sub. intros x Hx. rewrite <- H.
    apply BUnionI1...
Qed.

(* 自然数是传递集 *)
Theorem nat_trans : ∀n ∈ ω, trans n.
Proof with eauto.
  intros n Hn.
  set {n ∊ ω | λ n, trans n} as N.
  ω_induction N Hn.
  - intros a A Ha HA. exfalso0.
  - intros b B Hb HB. apply BUnionE in HB as [].
    + apply BUnionI1. eapply IH...
    + apply SingE in H. subst. apply BUnionI1...
Qed.

(* ω是传递集 *)
Theorem ω_trans : trans ω.
Proof with eauto.
  rewrite trans_sub. intros n Hn.
  set {n ∊ ω | λ n, n ⊆ ω} as N.
  ω_induction N Hn.
  - intros x Hx. exfalso0.
  - intros x Hx. apply BUnionE in Hx as [].
    apply IH... apply SingE in H. subst...
Qed.

(* 后继运算是单射 *)
Lemma suc_injective : ∀ n k ∈ ω, n⁺ = k⁺ → n = k.
Proof.
  intros n Hn k Hk Heq.
  assert (⋃n⁺ = ⋃k⁺) by congruence.
  apply nat_trans in Hn. apply nat_trans in Hk.
  apply trans_union_suc in Hn.
  apply trans_union_suc in Hk. congruence.
Qed.

Ltac ω_destruct n :=
  destruct (classic (n = ∅)) as [|Hωdes]; [|
    apply pred_exists in Hωdes as [?n' [?Hn' ?Hn'eq]]; auto
  ].

(* 集合对函数封闭 *)
Definition close := λ S A, ∀x ∈ A, S[x] ∈ A.

(** 皮亚诺结构 **)
Definition is_Peano := λ N S e,
  S: N ⇒ N ∧ e ∈ N ∧
  e ∉ ran S ∧
  injective S ∧
  ∀ A, A ⊆ N → e ∈ A → close S A → A = N.

(* 后继函数 *)
Definition σ := {λ n, <n, n⁺> | n ∊ ω}.

Lemma σ_function : σ : ω ⇒ ω.
Proof with eauto; try congruence.
  repeat split.
  - intros p Hp. apply ReplAx in Hp as [x [_ Hp]].
    rewrite <- Hp. eexists...
  - intros x Hx. rewrite <- unique_existence.
    split. apply domE in Hx...
    intros y1 y2 H1 H2.
    apply ReplAx in H1 as [u [_ H1]]. apply op_iff in H1 as [].
    apply ReplAx in H2 as [v [_ H2]]. apply op_iff in H2 as []...
  - apply ExtAx. split; intros.
    + apply domE in H as [y Hp]. apply ReplAx in Hp as [v [Hv Heq]].
      apply op_iff in Heq as []...
    + eapply domI. apply ReplAx. exists x. split...
  - intros y Hy. apply ranE in Hy as [x Hp].
    apply ReplAx in Hp as [v [Hv Heq]].
    apply op_iff in Heq as [_ Heq]. subst y.
    apply ω_inductive...
Qed.

(* 后继函数是双射 *)
Lemma σ_bijective : σ: ω ⟺ ω - ⎨∅⎬.
Proof with eauto.
  pose proof σ_function as [Hf [Hd Hr]]. split; split...
  - intros x Hx. rewrite <- unique_existence.
    split. apply ranE in Hx...
    intros y1 y2 H1 H2.
    apply ReplAx in H1 as [m [Hm H1]].
    apply ReplAx in H2 as [n [Hn H2]].
    apply op_iff in H1 as [].
    apply op_iff in H2 as []. subst m n x.
    apply suc_injective...
  - apply ExtAx. intros y. split; intros Hy.
    + apply SepI. apply Hr... intros H. apply SingE in H.
      subst y. apply ranE in Hy as [x Hp].
      apply ReplAx in Hp as [n [Hn Hp]].
      apply op_iff in Hp as [_ H].
      eapply suc_neq_0...
    + apply SepE in Hy as [Hy H0].
      ω_destruct y; subst y. exfalso. apply H0...
      eapply ranI. apply ReplAx. exists n'. split... 
Qed.

Lemma σ_ap : ∀n ∈ ω, σ[n] = n⁺.
Proof with auto.
  intros n Hn.  destruct σ_function as [Hf _].
  eapply func_ap... apply ReplAx. exists n. split...
Qed.

(* <ω, σ, ∅>是一个皮亚诺结构 *)
Theorem ω_Peano : is_Peano ω σ ∅.
Proof with eauto.
  intros. assert (Hσ:= σ_function). split...
  destruct Hσ as [Hf [Hd _]].
  split. apply ω_has_0. split; [|split].
  - intros H. apply ranE in H as [x Hp].
    apply ReplAx in Hp as [n [Hn H]].
    apply op_iff in H as [_ H]. eapply suc_neq_0...
  - split... intros y Hy. rewrite <- unique_existence.
    split. apply ranE in Hy...
    intros x1 x2 H1 H2.
    apply ReplAx in H1 as [n [Hx1 Hn]].
    apply ReplAx in H2 as [m [Hx2 Hm]].
    apply op_iff in Hn as [Hn1 Hn2].
    apply op_iff in Hm as [Hm1 Hm2]. subst.
    apply suc_injective...
  - intros A HA H0 Hc. apply ω_ind... split...
    intros a Ha. apply Hc in Ha as Hsa.
    apply HA in Ha. rewrite <- Hd in Ha.
    apply domE in Ha as [a1 Hp]. apply func_ap in Hp as Hap...
    apply ReplAx in Hp as [n [_ Heq]].
    apply op_iff in Heq as []; subst. congruence.
Qed.

(** ω递归定理 **)
Lemma ω_recursion : ∀ F A a, F: A ⇒ A → a ∈ A →
  ∃ h, h: ω ⇒ A ∧
  h[∅] = a ∧
  ∀n ∈ ω, h[n⁺] = F[h[n]].
Proof with eauto; try congruence.
  intros * [HFf [HFd HFr]] Ha.
  set (λ v, is_function v ∧
    (* (i)  *) (∅ ∈ dom v → v[∅] = a) ∧
    (* (ii) *) ∀n ∈ ω, n⁺ ∈ dom v → n ∈ dom v ∧ v[n⁺] = F[v[n]]
  ) as acceptable.
  set {λ N, N ⟶ A | N ∊ 𝒫 ω} as ℱ.
  set {v ∊ ⋃ℱ | λ v, acceptable v} as ℋ.
  set (⋃ℋ) as h. exists h.
  Local Ltac des Hv :=
    apply SepE in Hv as [Hv Hac];
    apply UnionAx in Hv as [u [Hu Hv]];
    apply ReplAx in Hu as [w [Hw Heq]]; subst u;
    apply arrow_iff in Hv as [Hfv [Hdv Hrv]]; subst w.
  assert (Hdrv: ∀v ∈ ℋ, dom v ⊆ ω ∧ ran v ⊆ A). {
    intros v Hv. des Hv. split.
    - apply PowerAx...
    - intros y Hy. apply ranE in Hy as [x Hp].
      apply func_ap in Hp as Hap... subst y.
      apply domI in Hp as Hd. apply Hrv in Hd...
  }
  assert ((* (☆) *)Hstar: ∀ n y, <n, y> ∈ h ↔
    ∃v ∈ ℋ, acceptable v ∧ <n, y> ∈ v). {
    split.
    - intros Hp. apply UnionAx in Hp as [v [Hv Hp]].
      exists v. split... split... des Hv...
    - intros [v [Hv [[Hvf _] Heq]]]. eapply UnionI...
  }
  assert (Hdhω: dom h ⊆ ω). {
    intros x Hx. apply domE in Hx as [y Hp].
    apply Hstar in Hp as [v [Hv [_ Hp]]].
    apply Hdrv in Hv as [Hd _].
    eapply domI in Hp. apply Hd...
  }
  assert (Hrha: ran h ⊆ A). {
    intros y Hy. apply ranE in Hy as [x Hp].
    apply Hstar in Hp as [v [Hv [_ Hp]]].
    apply Hdrv in Hv as [_ Hr].
    eapply ranI in Hp. apply Hr...
  }
  assert (Hfh: is_function h). {
    split. intros p Hp. apply UnionAx in Hp as [v [Hv Hp]].
    des Hv. apply func_pair in Hp as Hpeq...
    rewrite Hpeq. eexists...
    intros n Hn. rewrite <- unique_existence.
    split. apply domE in Hn... apply Hdhω in Hn.
    set {n ∊ ω | λ n, ∀ y1 y2,
      <n, y1> ∈ h → <n, y2> ∈ h → y1 = y2} as N.
    ω_induction N Hn; intros y1 y2 H1 H2.
    - apply Hstar in H1 as [v1 [_ [[Hf1 [Hi1 _]] Hp1]]].
      apply Hstar in H2 as [v2 [_ [[Hf2 [Hi2 _]] Hp2]]].
      apply domI in Hp1 as Hd1. apply domI in Hp2 as Hd2.
      apply func_ap in Hp1... apply func_ap in Hp2...
      apply Hi1 in Hd1. apply Hi2 in Hd2...
    - apply Hstar in H1 as [v1 [Hv1 [Hac1 Hp1]]].
      apply Hstar in H2 as [v2 [Hv2 [Hac2 Hp2]]].
      assert (Hii1:= Hac1). destruct Hii1 as [Hf1 [_ Hii1]].
      assert (Hii2:= Hac2). destruct Hii2 as [Hf2 [_ Hii2]].
      apply domI in Hp1 as Hd1. apply domI in Hp2 as Hd2.
      apply Hii1 in Hd1 as [Hd1 Heq1]...
      apply Hii2 in Hd2 as [Hd2 Heq2]...
      apply func_ap in Hp1... apply func_ap in Hp2...
      rewrite <- Hp1, <- Hp2. rewrite Heq1, Heq2.
      cut (v1[m] = v2[m])... clear Hii1 Hii2 Hp1 Hp2 Heq1 Heq2.
      apply func_correct in Hd1... apply func_correct in Hd2...
      apply IH; apply Hstar; [exists v1|exists v2]; split; auto.
  }
  assert (Hach: acceptable h). {
    split... split.
    - intros. apply domE in H as [y Hp]. apply func_ap in Hp as Hy...
      apply Hstar in Hp as [v [_ [[Hfv [Hi _]] Hp]]].
      apply func_ap in Hp as Hy'... subst y.
      apply domI in Hp as Hd. apply Hi in Hd...
    - intros n Hn Hn1.
      apply domE in Hn1 as [y Hp]. apply func_ap in Hp as Hy...
      apply Hstar in Hp as [v [Hv [Hac Hp]]].
      assert (Hac':= Hac). destruct Hac' as [Hfv [_ Hii]].
      apply func_ap in Hp as Hy'... subst y.
      apply domI in Hp as Hd. apply Hii in Hd as [Hndv Heq]...
      apply domE in Hndv as [y Hpv]. apply func_ap in Hpv as Hapv...
      cut (<n, y> ∈ h). intros Hph.
      apply domI in Hph as Hndh. apply func_ap in Hph... split...
      apply Hstar. exists v. split...
  }
  assert (H0dh: ∅ ∈ dom h). {
    set ⎨<∅, a>⎬ as f0.
    assert (Hf: is_function f0). {
      split.
      - intros x Hx. apply SingE in Hx. subst x. eexists...
      - intros x Hx. rewrite <- unique_existence.
        split. apply domE in Hx...
        intros y1 y2 H1 H2.
        apply SingE in H1. apply op_iff in H1 as [_ H1].
        apply SingE in H2. apply op_iff in H2 as [_ H2]...
    }
    assert (H0: f0[∅] = a). {
      eapply func_ap... apply SingI.
    }
    assert (Hac: acceptable f0). {
      split... split. intros... intros n Hn Hn1.
      exfalso. apply func_correct in Hn1... apply SingE in Hn1.
      apply op_iff in Hn1 as [Hn1 _]. eapply suc_neq_0...
    }
    eapply domI. apply Hstar. exists f0.
    split; [|split; [apply Hac|apply SingI]].
    apply SepI... eapply UnionI. apply ReplI.
    apply PowerAx. cut (⎨∅⎬ ⊆ ω)...
    intros x Hx. apply SingE in Hx. subst x. apply ω_has_0.
    apply arrow_iff. split... split.
    + apply ExtAx. split; intros.
      apply domE in H as [y Hp]. apply SingE in Hp.
      apply op_iff in Hp as [Hx _]. subst x. apply SingI.
      apply SingE in H. subst x. eapply domI. apply SingI.
    + intros x Hx. apply SingE in Hx. subst x. rewrite H0...
  }
  assert (Hdheq: dom h = ω). {
    apply ω_ind... split... intros k Hk.
    destruct (classic (k⁺ ∈ dom h)) as [|Hc]...
    set <k⁺, F[h[k]]> as p1.
    set (h ∪ ⎨p1⎬) as v.
    assert (Hp1: p1 ∈ v) by (apply BUnionI2; apply SingI).
    assert (Hf: is_function v). {
      split.
      - intros p Hp. apply BUnionE in Hp as [].
        + apply func_pair in H... rewrite H. eexists...
        + apply SingE in H. subst p. exists k⁺, (F[h[k]])...
      - intros x Hx. rewrite <- unique_existence.
        split. apply domE in Hx...
        intros y1 y2 H1 H2.
        apply BUnionE in H1 as []; apply BUnionE in H2 as [].
        + eapply func_sv...
        + apply domI in H. apply SingE in H0.
          apply op_iff in H0 as [H0 _]. subst x.
          exfalso. apply Hc...
        + apply domI in H0. apply SingE in H.
          apply op_iff in H as [H _]. subst x.
          exfalso. apply Hc...
        + apply SingE in H. apply op_iff in H as [_ H].
          apply SingE in H0. apply op_iff in H0 as [_ H0]...
    }
    assert (Hd: dom v ⊆ ω). {
      intros x Hx. apply domE in Hx as [y Hp].
      apply BUnionE in Hp as [].
      - apply domI in H. apply Hdhω...
      - apply SingE in H. apply op_iff in H as [H _]. subst x.
        apply ω_inductive. apply Hdhω...
    }
    assert (Hr: ran v ⊆ A). {
      intros y Hy. apply ranE in Hy as [x Hp].
      apply BUnionE in Hp as [].
      - apply ranI in H. apply Hrha...
      - apply SingE in H. apply op_iff in H as [_ H]. subst y.
        apply HFr. eapply ranI. eapply func_correct...
        rewrite HFd. apply Hrha. eapply ranI. eapply func_correct... 
    }
    assert (Hac: acceptable v). {
      split... split.
      - intros H0. apply func_correct in H0...
        apply BUnionE in H0 as [H0|H0].
        + apply domI in H0 as Hd0. apply func_ap in H0...
          destruct Hach as [_ [Hi _]]. apply Hi in Hd0...
        + apply SingE in H0. apply op_iff in H0 as [H0 _].
          exfalso. eapply suc_neq_0...
      - intros n Hn Hn1.
        apply domE in Hn1 as [y Hp]. apply func_ap in Hp as Hy...
        apply BUnionE in Hp as [Hp|Hp].
        + apply domI in Hp as Hd1. apply func_ap in Hp... subst y.
          destruct Hach as [_ [_ Hii]].
          apply Hii in Hd1 as [Hndh Heq]...
          apply domE in Hndh as [y Hp].
          cut (n ∈ dom v). intros Hndv. split...
          cut (v[n] = h[n])... apply func_ap in Hp as Hap...
          rewrite Hap. eapply func_ap... apply BUnionI1...
          eapply domI. apply BUnionI1...
        + apply SingE in Hp. apply op_iff in Hp as [Heq1 Heq2].
          assert (Heq3: n = k). eapply suc_injective...
          subst k y. clear Heq1 Hn Hc.
          apply domE in Hk as [y Hp].
          cut (n ∈ dom v). intros Hndv. split...
          cut (v[n] = h[n])... apply func_ap in Hp as Hap...
          rewrite Hap. eapply func_ap... apply BUnionI1...
          eapply domI. apply BUnionI1...
    }
    eapply domI. cut (v ⊆ h). intros. apply H...
    intros p Hp. apply BUnionE in Hp as []...
    apply SingE in H. subst p. apply Hstar.
    exists v. split; [|split; [apply Hac|apply Hp1]].
    apply SepI... eapply UnionI. apply ReplI.
    apply PowerAx. apply Hd.
    apply arrow_iff. split... split...
    intros x Hx. apply Hr. eapply ranI. eapply func_correct...
  }
  split; [
    split; [apply Hfh | split; [apply Hdheq | apply Hrha]] |
    split
  ].
  - (* h [∅] = a *) destruct Hach as [_ [Hi _]]...
  - (* ∀n ∈ ω, h[n⁺] = F[h[n]] *) intros n Hn.
    destruct Hach as [_ [_ Hii]]. apply Hii...
    rewrite Hdheq. apply ω_inductive...
Qed.

Theorem ω_recursion_uniqueness : ∀ F A a, F: A ⇒ A → a ∈ A →
  ∃! h, h: ω ⇒ A ∧
  h[∅] = a ∧
  ∀n ∈ ω, h[n⁺] = F[h[n]].
Proof with eauto; try congruence.
  intros * HF Ha. rewrite <- unique_existence.
  split. apply ω_recursion...
  intros h1 h2 [[H1f [H1d _]] [H10 H1]] [[H2f [H2d _]] [H20 H2]].
  apply func_ext_intro... intros n Hn. rewrite H1d in Hn.
  set {n ∊ ω | λ n, h1[n] = h2[n]} as S.
  ω_induction S Hn...
  apply H1 in Hm as Heq1. apply H2 in Hm as Heq2...
Qed.

(* 皮亚诺结构同构 *)
Theorem Peano_isomorphism : ∀ N S e, is_Peano N S e →
  ∃ h, h: ω ⟺ N ∧
  ∀n ∈ ω, h[σ[n]] = S[h[n]] ∧
  h[∅] = e.
Proof with eauto; try congruence.
  intros N S e [HS [He [Hi [Hii Hiii]]]].
  pose proof (ω_recursion S N e HS He) as [h [H1 [H2 H3]]].
  destruct H1 as [Hf [Hd Hr]].
  exists h. split. split; split...
  - (* single_rooted h *)
    intros y Hy. rewrite <- unique_existence.
    split. apply ranE in Hy...
    assert (Hnq0: ∀p ∈ ω, h[∅] ≠ h[p⁺]). {
      intros p Hp. apply H3 in Hp as Heq. rewrite H2, Heq.
      intros Hc. apply Hi. rewrite Hc. destruct HS as [HfS [HdS _]].
      eapply ranI. apply func_correct... rewrite HdS.
      eapply ap_ran... split...
    }
    intros n m Hp. apply domI in Hp as Hn. rewrite Hd in Hn.
    generalize Hp. generalize dependent m.
    clear Hp Hy. generalize dependent y.
    set {n ∊ ω | λ n, ∀ y m, <n, y> ∈ h → <m, y> ∈ h → n = m} as M.
    ω_induction M Hn.
    + intros y m Hp1 Hp2. apply domI in Hp2 as Hdm.
      apply func_ap in Hp1... apply func_ap in Hp2...
      ω_destruct m... exfalso. subst m. eapply Hnq0...
    + intros y k Hp1 Hp2. apply domI in Hp2 as Hdk.
      apply func_ap in Hp1... apply func_ap in Hp2...
      ω_destruct k... subst k. exfalso. eapply Hnq0...
      subst k. clear Hdk.
      apply H3 in Hm as Heq1. apply H3 in Hn' as Heq2.
      assert (S[h[n']] = S[h[m]]) by congruence.
      cut (m = n')... eapply IH. apply func_correct...
      cut (h[n'] = h[m]). intros Heq.
      rewrite <- Heq. apply func_correct...
      destruct HS as [HSf [HSd _]].
      eapply injectiveE; eauto; rewrite HSd; apply Hr;
        eapply ranI; apply func_correct...
  - (* ran h = N *) apply Hiii...
    + rewrite <- H2. eapply ap_ran. split... apply ω_has_0.
    + intros x Hx. apply ranE in Hx as [n Hp].
      apply domI in Hp as Hn. rewrite Hd in Hn.
      apply H3 in Hn as Heq. apply func_ap in Hp... subst x.
      rewrite <- Heq. eapply ap_ran. split... apply ω_inductive...
  - intros n Hn. split... rewrite σ_ap...
Qed.
