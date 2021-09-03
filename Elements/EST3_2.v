(** Adapted from "Elements of Set Theory" Chapter 3 **)
(** Coq coding by choukh, May 2020 **)

Require Export ZFC.Elements.EST3_1.

(*** EST第三章2：函数的左右逆，限制，像，函数空间，无限笛卡尔积 ***)

(* 映射 *) (* maps into *)
Definition function : set → set → set → Prop :=
  λ F A B, is_function F ∧ dom F = A ∧ ran F ⊆ B.
Notation "F : A ⇒ B" := (function F A B) (at level 60) : set_scope.

(* 单射 *) (* maps one-to-one / one-to-one function *)
Definition injection : set → set → set → Prop :=
  λ F A B, injective F ∧ dom F = A ∧ ran F ⊆ B.
Notation "F : A ⇔ B" := (injection F A B) (at level 60) : set_scope.

(* 满射 *) (* maps onto *)
Definition surjection : set → set → set → Prop :=
  λ F A B, is_function F ∧ dom F = A ∧ ran F = B.
Notation "F : A ⟹ B" := (surjection F A B) (at level 60) : set_scope.

(* 双射 *) (* one-to-one correspondence *)
Definition bijection : set → set → set → Prop :=
  λ F A B, injective F ∧ dom F = A ∧ ran F = B.
Notation "F : A ⟺ B" := (bijection F A B) (at level 60) : set_scope.

(* 单射是一对一的映射 *)
Lemma injection_is_func : ∀ F A B,
  F: A ⇔ B ↔ F: A ⇒ B ∧ injective F.
Proof with auto.
  split. intros [Hi [Hd Hr]]. split... split... destruct Hi...
  intros [[_ [Hd Hr]] Hi]. split...
Qed.

(* 满射是满的映射 *)
Lemma surjection_is_func : ∀ F A B,
  F: A ⟹ B ↔ F: A ⇒ B ∧ ran F = B.
Proof with auto.
  split. intros [Hf [Hd Hr]]. split...
  split... split... rewrite Hr...
  intros [[Hf [Hd _]] Hr]. split...
Qed.

(* 双射是满的单射 *)
Lemma bijection_is_injection : ∀ F A B,
  F: A ⟺ B ↔ F: A ⇔ B ∧ ran F = B.
Proof with auto.
  split. intros [Hi [Hd Hr]]. split;[split;[|split]|]... rewrite Hr...
  intros [[Hi [Hd Hr]] Heq]. split...
Qed.

(* 双射是一对一的满射 *)
Lemma bijection_is_surjection : ∀ F A B,
  F: A ⟺ B ↔ F: A ⟹ B ∧ injective F.
Proof with auto.
  split. intros [Hi [Hd Hr]]. split... split... destruct Hi...
  intros [[_ [Hd Hr]] Hi]. split...
Qed.

(* 双射是一对一的且满的映射 *)
Lemma bijection_is_func : ∀ F A B,
  F: A ⟺ B ↔ F: A ⇒ B ∧ injective F ∧ ran F = B.
Proof with auto.
  split. intros [Hi [Hd Hr]]. split... split.
  destruct Hi... split... rewrite Hr...
  intros [[Hf [Hd _]] [Hi Hr]]. split...
Qed.

(* 函数应用属于值域 *)
Lemma ap_ran : ∀ A B F, F: A ⇒ B → ∀x ∈ A, F[x] ∈ B.
Proof with auto.
  intros * [Hf [Hd Hr]] x Hx.
  apply Hr. eapply ranI. apply func_correct... rewrite Hd...
Qed.

Lemma cprd_single_is_func : ∀ F a, is_function (F × {a,}).
Proof with auto.
  split.
  - apply cprd_is_rel.
  - intros x Hx. apply domE in Hx as [y Hy].
    exists y. split... intros y' Hy'.
    apply CPrdE2 in Hy  as [_ Hy ].
    apply CPrdE2 in Hy' as [_ Hy'].
    apply SingE in Hy. apply SingE in Hy'. subst...
Qed.

Lemma bunion_is_func : ∀ F G,
  is_function F → is_function G →
  dom F ∩ dom G = ∅ → is_function (F ∪ G).
Proof with eauto.
  intros F G Hf Hg Hi. split.
  - intros x Hx. apply BUnionE in Hx as [Hx|Hx].
    + destruct Hf as [Hr _]. apply Hr in Hx...
    + destruct Hg as [Hr _]. apply Hr in Hx...
  - intros x Hx. apply domE in Hx as [y Hy].
    exists y. split... intros y' Hy'.
    apply BUnionE in Hy as [Hy|Hy];
    apply BUnionE in Hy' as [Hy'|Hy'].
    + eapply unique_existence. eapply func_dom_sv.
      apply Hf. eapply domI... easy. easy.
    + apply domI in Hy. apply domI in Hy'.
      exfalso. eapply disjointE...
    + apply domI in Hy. apply domI in Hy'.
      exfalso. eapply disjointE...
    + eapply unique_existence. eapply func_dom_sv.
      apply Hg. eapply domI... easy. easy.
Qed.

(** 函数的左逆 **)
Theorem left_inv : ∀ F A B, F: A ⇒ B → ⦿ A →
  (∃ G, G: B ⇒ A ∧ G ∘ F = Ident A) ↔ injective F.
Proof with eauto.
  intros F A B [Hf [Hdf Hrf]] [a Ha]. split.
  (* -> *)
  intros [G [[Hg [Hdg _]] Heq]]. split... intros t Ht.
  apply ranE in Ht as [x Hx].
  exists x. split... intros x' Hx'.
  assert (Hd: ∀u ∈ dom F, u ∈ dom (G ∘ F)). {
    intros u Hu. rewrite compo_dom... apply SepI.
    apply Hu. rewrite Hdg. apply Hrf.
    apply func_correct in Hu... eapply ranI...
  }
  apply domI in Hx as Hdx. apply domI in Hx' as Hdx'.
  apply Hd in Hdx as Hdcx. apply Hd in Hdx' as Hdcx'.
  apply func_ap in Hx... apply func_ap in Hx'...
  assert (G[t] = G[t]) by reflexivity.
  rewrite <- Hx in H at 1. rewrite <- Hx' in H.
  do 2 rewrite <- compo_correct in H...
  rewrite Heq in H. rewrite Hdf in Hdx, Hdx'.
  do 2 rewrite ident_ap in H...
  (* <- *)
  intros [_ Hs]. assert (F⁻¹: ran F ⟹ A). {
    split. apply inv_func_iff_sr... split.
    apply inv_dom. rewrite inv_ran...
  }
  exists (F⁻¹ ∪ (B - ran F) × {a,}). split.
  (* G: B ⇒ A *) split.
  (* is_function G *)
  - apply bunion_is_func.
    + apply inv_func_iff_sr...
    + apply cprd_single_is_func.
    + apply EmptyI. intros x Hx.
      apply BInterE in Hx as [H1 H2].
      apply domE in H2 as [y H2].
      apply CPrdE2 in H2 as [H2 _].
      apply CompE in H2 as [_ H2]. rewrite inv_dom in H1...
  (* dom G = B ∧ ran G ⊆ A *)
  - split; [apply ExtAx; split; intros Hx|].
    (* dom G ⊆ B *)
    + apply domE in Hx as [y Hp]. apply BUnionE in Hp as [].
      * apply domI in H0. rewrite inv_dom in H0. apply Hrf in H0...
      * apply CPrdE2 in H0 as [H0 _]. apply CompE in H0 as []...
    (* dom G ⊇ B *)
    + destruct (classic (x ∈ ran F)); eapply domI.
      * apply BUnionI1. rewrite <- inv_dom in H0.
        apply func_correct in H0... apply inv_func_iff_sr...
      * apply BUnionI2. apply CPrdI. apply CompI... apply SingI.
    (* ran G ⊆ A *)
    + intros x Hx. apply ranE in Hx as [y Hp].
      apply BUnionE in Hp as [].
      * apply ranI in H0. rewrite inv_ran in H0. subst A...
      * apply CPrdE2 in H0 as [_ H0]. apply SingE in H0. subst a...
  (* G ∘ F = Ident A*)
  - ext Hx.
    + apply SepE in Hx as [_ [Hp [y [H1 H2]]]].
      apply BUnionE in H2 as [H2|H2].
      * apply ReplAx. exists (π1 x). split.
        apply domI in H1 as Hd. subst A...
        apply op_η in Hp. rewrite Hp at 3. apply op_iff.
        split... rewrite <- inv_op in H2. eapply singrE...
      * exfalso. apply ranI in H1.
        apply CPrdE2 in H2 as [H2 _].
        apply CompE in H2 as []...
    + apply ReplAx in Hx as [b [Hb Heq]]. subst x.
      rewrite <- Hdf in Hb. apply domE in Hb as [c Hb].
      eapply compoI... apply BUnionI1. rewrite <- inv_op...
Qed.

Lemma binter_unique : ∀ a b s C,
  a ∈ s → b ∈ s → a ∈ C → b ∈ C → (∃ u, s ∩ C = {u,}) → a = b.
Proof.
  intros a b s C Has Hbs Hac Hbc [u Hu].
  assert (Hai: a ∈ s ∩ C) by (apply BInterI; auto).
  assert (Hbi: b ∈ s ∩ C) by (apply BInterI; auto).
  rewrite Hu in Hai, Hbi.
  apply SingE in Hai.
  apply SingE in Hbi. congruence.
Qed.

(* 函数的右逆 *)
(* For right inverse of function please see lib/ChoiceFacts.v *)

(** 限制 **)
Definition Restriction : set → set → set :=
  λ F A, {p ∊ F | is_pair p ∧ π1 p ∈ A}.
Notation "F ↾ A" := (Restriction F A) (at level 60) : set_scope.

Lemma restrI : ∀ F A a b, a ∈ A → <a, b> ∈ F → <a, b> ∈ F ↾ A.
Proof with auto.
  intros. apply SepI... split. exists a, b...
  rewrite π1_correct...
Qed.

Lemma restrE1 : ∀ F A, ∀x ∈ F ↾ A,
  ∃ a b, a ∈ A ∧ <a, b> ∈ F ∧ x = <a, b>.
Proof.
  intros F A x Hx. apply SepE in Hx as [Hx [[a [b Hp]] Ha]].
  subst x. rewrite π1_correct in Ha. exists a, b; auto.
Qed.

Lemma restrE2 : ∀ F A x y, <x, y> ∈ F ↾ A →
  <x, y> ∈ F ∧ x ∈ A.
Proof.
  intros * Hp. apply restrE1 in Hp as [a [b [Ha [Hp Heq]]]].
  apply op_iff in Heq as []; subst. split; auto.
Qed.

Lemma restr_dom_included : ∀ F A, dom (F ↾ A) ⊆ dom F.
Proof.
  intros F A x H. apply domE in H as [y Hy].
  apply SepE in Hy as [Hp _]. eapply domI. apply Hp.
Qed.

Lemma restr_ran_included : ∀ F A, ran (F ↾ A) ⊆ ran F.
Proof.
  intros F A y H. apply ranE in H as [x Hx].
  apply SepE in Hx as [Hp _]. eapply ranI. apply Hp.
Qed.

Lemma restr_to_dom : ∀ F, is_rel F → F ↾ (dom F) = F.
Proof with eauto.
  intros. ext Hx.
  - apply restrE1 in Hx as [a [b [Ha [Hx Heq]]]]. subst...
  - apply rel_pair in Hx as Heq... rewrite Heq.
    rewrite Heq in Hx. apply restrI... eapply domI...
Qed.

Lemma restr_dom : ∀ F A, is_function F →
  A ⊆ dom F ↔ dom (F ↾ A) = A.
Proof with auto.
  intros * Hf. split; intros.
  - ext Hx.
    + apply domE in Hx as [y Hp].
      apply restrE2 in Hp as []...
    + eapply domI. apply restrI...
      apply func_correct...
  - rewrite <- H. apply restr_dom_included.
Qed.

Lemma restr_func : ∀ F A,
  is_function F → is_function (F ↾ A).
Proof.
  unfold is_function, is_rel. intros F A [H1 H2]. split.
  - intros x Hx. apply SepE in Hx as [Hx _].
    apply H1 in Hx. apply Hx.
  - intros x Hx. rewrite <- unique_existence.
    split. apply domE in Hx. apply Hx.
    intros y1 y2 Hy1 Hy2.
    apply SepE in Hy1 as [Hy1 _].
    apply SepE in Hy2 as [Hy2 _].
    eapply unique_existence. apply H2.
    eapply restr_dom_included. apply Hx. easy. easy.
Qed.

Lemma restr_injective : ∀ F A, injective F → injective (F ↾ A).
Proof with eauto.
  intros * [Hf Hs]. split. apply restr_func...
  intros y Hy. rewrite <- unique_existence.
  split. apply ranE in Hy...
  intros x1 x2 H1 H2.
  apply restrE2 in H1 as [H1 _].
  apply restrE2 in H2 as [H2 _].
  eapply unique_existence. eapply Hs.
  eapply restr_ran_included... easy. easy.
Qed.

Lemma restr_ap : ∀ F A B, B ⊆ A → is_function F → dom F = A →
  ∀x ∈ B, (F ↾ B)[x] = F[x].
Proof with auto.
  intros * Hsub Hf Hd x Hxb.
  apply Hsub in Hxb as Hxa. rewrite <- Hd in Hxa.
  apply domE in Hxa as [y Hp]. apply func_ap in Hp as Hap...
  rewrite Hap. apply func_ap. apply restr_func... apply restrI...
Qed.

(** 像 **)
Definition Image : set → set → set :=
  λ F A, ran (F ↾ A).
Notation "F ⟦ A ⟧" := (Image F A) (at level 30, format "F ⟦ A ⟧") : set_scope.

Lemma imgI : ∀ F A x y, x ∈ A → <x, y> ∈ F → y ∈ F⟦A⟧.
Proof with eauto.
  intros F A x y Hx Hp. eapply ranI. apply SepI...
  split. exists x, y... rewrite π1_correct...
Qed.

Lemma imgE : ∀ F A y, y ∈ F⟦A⟧ → ∃ x, x ∈ A ∧ <x, y> ∈ F.
Proof.
  intros F A y Hy. apply ranE in Hy as [x Hp].
  apply SepE in Hp as [Hp_ [_ Hx]]. rewrite π1_correct in Hx.
  exists x; auto.
Qed.

Example img_included : ∀ F A, F⟦A⟧ ⊆ ran F.
Proof.
  intros F A y Hy. apply imgE in Hy as [x [_ Hp]].
  eapply ranI. apply Hp.
Qed.

Fact img_empty : ∀ f, f⟦∅⟧ = ∅.
Proof.
  intros. ext p Hp.
  apply imgE in Hp as [x [Hx _]]. exfalso0. exfalso0.
Qed.

Fact img_single : ∀ f, is_function f → ∀x ∈ dom f, f⟦{x,}⟧ = {f[x],}.
Proof with auto.
  intros f Hf x Hx.
  ext y Hy.
  - apply imgE in Hy as [w [Hw Hp]].
    apply SingE in Hw; subst.
    apply func_ap in Hp... subst...
  - apply SingE in Hy; subst.
    eapply imgI... apply func_correct...
Qed.

Lemma img_correct : ∀ F A,
  is_function F → A ⊆ dom F → F⟦A⟧ = {F[a] | a ∊ A}.
Proof with eauto.
  intros F A Hf Hsub. ext y Hy.
  - apply ReplAx. apply imgE in Hy as [x [Hx Hp]].
    exists x. split... apply Hsub in Hx. apply func_ap...
  - apply ReplAx in Hy as [x [Hx Heq]]. apply Hsub in Hx as Hx'.
    pose proof (ap_exists F Hf x Hx') as [t [_ [Hxy Ht]]].
    subst t. rewrite Heq in Hxy. eapply imgI...
Qed.

Theorem img_bunion_distr : ∀ F A B, F⟦A ∪ B⟧ = F⟦A⟧ ∪ F⟦B⟧.
Proof with eauto.
  intros. ext y Hy.
  - apply imgE in Hy as [x [Hx Hp]]. apply BUnionE in Hx as [].
    + apply BUnionI1. eapply imgI...
    + apply BUnionI2. eapply imgI...
  - apply BUnionE in Hy as []; apply imgE in H as [x [Hx Hp]].
    + eapply imgI... apply BUnionI1...
    + eapply imgI... apply BUnionI2...
Qed.

Theorem img_union_distr : ∀ F 𝒜, F⟦⋃𝒜⟧ = ⋃{F⟦A⟧ | A ∊ 𝒜}.
Proof with eauto.
  intros. ext y Hy.
  - apply imgE in Hy as [x [Hx Hp]].
    apply UnionAx in Hx as [A [HA Hx]].
    eapply FUnionI... eapply imgI...
  - apply FUnionE in Hy as [A [HA Hy]].
    apply imgE in Hy as [x [Hx Hp]].
    eapply imgI... eapply UnionI...
Qed.

Theorem img_binter_distr_sub : ∀ F A B, F⟦A ∩ B⟧ ⊆ F⟦A⟧ ∩ F⟦B⟧.
Proof.
  intros * y Hy. apply imgE in Hy as [x [Hx Hp]].
  apply BInterE in Hx as []. apply BInterI; eapply imgI; eauto.
Qed.

Theorem img_binter_distr : ∀ F A B,
  single_rooted F → F⟦A ∩ B⟧ = F⟦A⟧ ∩ F⟦B⟧.
Proof with eauto.
  intros F A B Hs. ext y Hy.
  - apply img_binter_distr_sub...
  - apply BInterE in Hy as [Ha Hb].
    apply imgE in Ha as [w [Hw Hpf]].
    apply imgE in Hb as [x [Hx Hpg]].
    assert (Heq: w = x) by (eapply singrE; eauto).
    subst. eapply imgI... apply BInterI...
Qed.

Theorem img_inter_distr_sub : ∀ F 𝒜, F⟦⋂𝒜⟧ ⊆ ⋂{F⟦A⟧ | A ∊ 𝒜}.
Proof with eauto.
  intros F 𝒜 y Hy. apply imgE in Hy as [x [Hx Hp]].
  apply InterE in Hx as [[A HA] H].
  apply InterI. exists (F⟦A⟧). apply ReplI...
  intros Y HY. apply ReplAx in HY as [B [HB Heq]]. subst Y.
  eapply imgI...
Qed.

Theorem img_inter_distr : ∀ F 𝒜,
  single_rooted F → F⟦⋂𝒜⟧ = ⋂{F⟦A⟧ | A ∊ 𝒜}.
Proof with eauto.
  intros F 𝒜 Hs. ext y Hy.
  - apply img_inter_distr_sub...
  - apply InterE in Hy as [[Y HY] H]. apply H in HY as Hy.
    apply ReplAx in HY as [A [HA Heq]]. subst Y.
    apply imgE in Hy as [x [_ Hp]].
    eapply imgI... apply InterI. exists A... intros B HB.
    assert (HY: F⟦B⟧ ∈ {F⟦A⟧ | A ∊ 𝒜}). {
      apply ReplAx. exists B. split...
    }
    apply H in HY. apply imgE in HY as [x' [Hx' Hp']].
    assert (Heq: x = x') by (eapply singrE; eauto). subst...
Qed.

Theorem img_comp_distr_sub : ∀ F A B, F⟦A⟧ - F⟦B⟧ ⊆ F⟦A - B⟧.
Proof with eauto.
  intros F A B y Hy. apply CompE in Hy as [H1 H2].
  apply imgE in H1 as [x [Ha Hp]].
  eapply imgI... apply CompI... intros Hb.
  apply H2. eapply imgI...
Qed.

Theorem img_comp_distr : ∀ F A B,
  single_rooted F → F⟦A⟧ - F⟦B⟧ = F⟦A - B⟧.
Proof with eauto.
  intros * Hs. ext y Hy.
  - apply img_comp_distr_sub...
  - apply imgE in Hy as [x [Hx Hp]]. apply CompE in Hx as [Ha Hb].
    apply CompI. eapply imgI... intros H.
    apply Hb. apply imgE in H as [w [Hw Hq]].
    assert (w = x) by (eapply singrE; eauto). subst...
Qed.

Corollary img_inv_union_distr : ∀ F 𝒜,
  F⁻¹⟦⋃𝒜⟧ = ⋃{F⁻¹⟦A⟧ | A ∊ 𝒜}.
Proof. intros. exact (img_union_distr F⁻¹ 𝒜). Qed.

Corollary img_inv_inter_distr : ∀ F 𝒜,
  is_function F → F⁻¹⟦⋂𝒜⟧ = ⋂{F⁻¹⟦A⟧ | A ∊ 𝒜}.
Proof with auto.
  intros. apply img_inter_distr.
  apply inv_sr_iff_func...
Qed.

Corollary img_inv_comp_distr : ∀ F A B,
  is_function F → F⁻¹⟦A⟧ - F⁻¹⟦B⟧ = F⁻¹⟦A - B⟧.
Proof with auto.
  intros. apply img_comp_distr.
  apply inv_sr_iff_func...
Qed.

(** 函数空间 **)
Definition Arrow : set → set → set := λ A B,
  {F ∊ 𝒫(A × B) | F: A ⇒ B}.
Notation "A ⟶ B" := (Arrow A B) (at level 60) : set_scope.

Theorem arrowI : ∀ F A B, F: A ⇒ B → F ∈ A ⟶ B.
Proof with auto; try congruence.
  intros. apply SepI... apply PowerAx. intros p Hp.
  destruct H as [Hff [Hdf Hrf]].
  apply func_pair in Hp as Heqp... rewrite Heqp in Hp.
  apply domI in Hp as Hd. apply ranI in Hp as Hr.
  rewrite Heqp. apply CPrdI...
Qed.

Theorem arrow_iff : ∀ F A B,
  F ∈ A ⟶ B ↔ is_function F ∧ dom F = A ∧ ∀x ∈ A, F[x] ∈ B.
Proof with eauto.
  intros. split.
  - intros HF. apply SepE2 in HF as [Hf [Heq Hsub]].
    split... split... intros x Hx.
    apply Hsub. eapply ap_ran... split...
  - intros [Hf [Hd Hap]]. subst A. apply SepI.
    + apply PowerAx. intros p Hp.
      assert (Hp' := Hp). apply func_pair in Hp'...
      rewrite Hp'. rewrite Hp' in Hp.
      apply CPrdI. eapply domI... apply domI in Hp as Hd.
      apply func_ap in Hp... rewrite <- Hp. apply Hap...
    + split... split... intros y Hy.
      apply ranE in Hy as [x Hp]. apply domI in Hp as Hd.
      apply func_ap in Hp... subst y. apply Hap...
Qed.

(** 无限笛卡尔积 
  A × B × ... = {
    {<0, a0>, <1, b0>, ... },
    {<0, a1>, <1, b1>, ... },
    ...
  }
**)
Definition InfCPrd : set → (set → set) → set := λ I ℱ,
  {f ∊ I ⟶ ⋃{ℱ i | i ∊ I} | ∀i ∈ I, f[i] ∈ ℱ i}.

Lemma InfCPrdI : ∀ x I ℱ, x: I ⇒ ⋃ {ℱ i | i ∊ I} →
  (∀i ∈ I, x[i] ∈ ℱ i) → x ∈ InfCPrd I ℱ.
Proof with auto.
  intros * Hx Hxi. apply SepI. apply arrowI...
  intros i Hi. apply Hxi...
Qed.

Lemma InfCPrdE : ∀ x I ℱ, x ∈ InfCPrd I ℱ →
  x: I ⇒ ⋃ {ℱ i | i ∊ I} ∧ ∀i ∈ I, x[i] ∈ ℱ i.
Proof.
  intros * Hx. apply SepE in Hx as [Hx Hxi].
  apply SepE in Hx as [_ Hx]. split; auto.
Qed.

Example infcprd_self : ∀ I ℱ A, ⦿ I →
  (∀i ∈ I, ℱ i = A) → InfCPrd I ℱ = I ⟶ A.
Proof with eauto.
  intros * [i Hi] H.
  assert (Heq: ⋃ {ℱ i | i ∊ I} = A). {
    ext Hx.
    - apply FUnionE in Hx as [j [Hj Hx]]. apply H in Hj. subst A...
    - eapply FUnionI... apply H in Hi. subst A...
  }
  ext f Hf.
  - apply SepE in Hf as [Hf _]. subst A...
  - apply SepI. subst A... clear Heq.
    intros j Hj. apply H in Hj as Heq. rewrite Heq. clear Heq.
    apply SepE in Hf as [_ Hf]. eapply ap_ran...
Qed.
