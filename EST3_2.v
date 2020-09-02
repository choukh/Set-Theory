(** Based on "Elements of Set Theory" Chapter 3 Part 2 **)
(** Coq coding by choukh, May 2020 **)

Require Export ZFC.EST3_1.

(*** EST第三章2：函数的左右逆，限制，像，函数空间，无限笛卡尔积 ***)

(* 映射 *)
Definition maps_into : set → set → set → Prop :=
  λ F A B, is_function F ∧ dom F = A ∧ ran F ⊆ B.
Notation "F : A ⇒ B" := (maps_into F A B) (at level 60).

(* 单射 *) (* one-to-on function *)
Definition maps_one_to_one : set → set → set → Prop :=
  λ F A B, injective F ∧ dom F = A ∧ ran F ⊆ B.
Notation "F : A ⇔ B" := (maps_one_to_one F A B) (at level 60).

(* 满射 *) (* surjection *)
Definition maps_onto : set → set → set → Prop :=
  λ F A B, is_function F ∧ dom F = A ∧ ran F = B.
Notation "F : A ⟹ B" := (maps_onto F A B) (at level 60).

(* 双射 *) (* one-to-one correspondence *)
Definition bijection : set → set → set → Prop :=
  λ F A B, injective F ∧ dom F = A ∧ ran F = B.
  Notation "F : A ⟺ B" := (bijection F A B) (at level 60).

Lemma cprod_single_func : ∀ F a, is_function (F × ⎨a⎬).
Proof with auto.
  repeat split.
  - apply cprod_is_rel.
  - apply domE in H as [y H]. exists y...
  - intros y y' Hy Hy'.
    apply CProdE1 in Hy  as [_ Hy ]. rewrite π2_correct in Hy.
    apply CProdE1 in Hy' as [_ Hy']. rewrite π2_correct in Hy'.
    apply SingE in Hy. apply SingE in Hy'. subst...
Qed.

Lemma bunion_func : ∀ F G,
  is_function F → is_function G →
  dom F ∩ dom G = ∅ → is_function (F ∪ G).
Proof with eauto.
  intros F G Hf Hg Hi. repeat split.
  - intros x Hx. apply BUnionE in Hx as [Hx|Hx].
    + destruct Hf as [Hr _]. apply Hr in Hx...
    + destruct Hg as [Hr _]. apply Hr in Hx...
  - apply domE in H...
  - intros y y' Hy Hy'.
    apply BUnionE in Hy as []; apply BUnionE in Hy' as [];
      apply domE in H as [y0 H]; apply BUnionE in H as [];
      apply domI in H; (apply func_dom_sv in H as [_ Hu]; auto)
      + exfalso; apply domI in H0; apply domI in H1;
        eapply EmptyE in Hi; apply Hi; apply BInterI...
Qed.

(** 函数的左逆 **)
Theorem left_inv : ∀ F A B,
  F: A ⇒ B → ⦿ A →
  (∃ G, G: B ⇒ A ∧ G ∘ F = Ident A) ↔ injective F.
Proof with eauto.
  intros F A B [Hf [Hdf Hrf]] [a Ha]. split.
  (* -> *)
  intros [G [[Hg [Hdg _]] Heq]]. split... intros t Ht. split.
  apply ranE in Ht... intros x x' Hx Hx'.
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
  do 2 rewrite ident_correct in H...
  (* <- *)
  intros [_ Hs]. assert (F⁻¹: ran F ⟹ A). {
    split. apply inv_func_iff_sr... split.
    apply inv_dom. rewrite inv_ran...
  }
  exists (F⁻¹ ∪ (B - ran F) × ⎨a⎬). split.
  (* G: B ⇒ A *) split.
  (* is_function G *)
  - apply bunion_func.
    + apply inv_func_iff_sr...
    + apply cprod_single_func.
    + apply EmptyI. intros x Hx.
      apply BInterE in Hx as [H1 H2]. apply domE in H2 as [y H2].
      apply CProdE1 in H2 as [H2 _]. rewrite π1_correct in H2.
      apply CompE in H2 as [_ H2]. rewrite inv_dom in H1...
  (* dom G = B ∧ ran G ⊆ A *)
  - split; [apply ExtAx; split; intros Hx|].
    (* dom G ⊆ B *)
    + apply domE in Hx as [y Hp]. apply BUnionE in Hp as [].
      * apply domI in H0. rewrite inv_dom in H0. apply Hrf in H0...
      * apply CProdE1 in H0 as [H0 _]. rewrite π1_correct in H0.
        apply CompE in H0 as []...
    (* dom G ⊇ B *)
    + destruct (classic (x ∈ ran F)); eapply domI.
      * apply BUnionI1. rewrite <- inv_dom in H0.
        apply func_correct in H0... apply inv_func_iff_sr...
      * apply BUnionI2. apply CProdI. apply CompI... apply SingI.
    (* ran G ⊆ A *)
    + intros x Hx. apply ranE in Hx as [y Hp].
      apply BUnionE in Hp as [].
      * apply ranI in H0. rewrite inv_ran in H0. subst A...
      * apply CProdE1 in H0 as [_ H0]. rewrite π2_correct in H0.
        apply SingE in H0. subst a...
  (* G ∘ F = Ident A*)
  - apply ExtAx. split; intros Hx.
    + apply SepE in Hx as [_ [Hp [y [H1 H2]]]].
      apply BUnionE in H2 as [H2|H2].
      * apply ReplAx. exists (π1 x). split.
        apply domI in H1 as Hd. subst A...
        apply op_η in Hp. rewrite Hp at 3. apply op_correct.
        split... rewrite <- inv_op in H2. eapply singrE...
      * exfalso. apply ranI in H1. apply CProdE1 in H2 as [H2 _].
        rewrite π1_correct in H2. apply CompE in H2 as []...
    + apply ReplAx in Hx as [b [Hb Heq]]. subst x.
      rewrite <- Hdf in Hb. apply domE in Hb as [c Hb].
      eapply compoI... apply BUnionI1. rewrite <- inv_op...
Qed.

Lemma binter_unique : ∀ a b s C,
  a ∈ s → b ∈ s → a ∈ C → b ∈ C → (∃ u, s ∩ C = ⎨u⎬) → a = b.
Proof.
  intros a b s C Has Hbs Hac Hbc [u Hu]. rewrite ExtAx in Hu.
  assert (Hai: a ∈ s ∩ C) by (apply BInterI; auto).
  assert (Hbi: b ∈ s ∩ C) by (apply BInterI; auto).
  apply Hu in Hai. apply SingE in Hai.
  apply Hu in Hbi. apply SingE in Hbi. subst. reflexivity.
Qed.

(* 选择公理的等效表述1：可以从关系中选出函数 *)
Definition AC_1st_form : Prop := ∀ R,
  is_relation R → ∃ F, is_function F ∧ F ⊆ R ∧ dom F = dom R.

Theorem choose_func_from_rel : AC_1st_form.
Proof with eauto.
  unfold AC_1st_form. intros.
  (* S := {{<x, y>, <x, y'>, <x, y''>}, { ... }, ... } *)
  set {λ x, {p ∊ R | λ p, π1 p = x} | x ∊ dom R} as S.
  assert (Hi: ∀s ∈ S, ⦿ s). {
    intros s Hs. apply ReplAx in Hs as [x [Hx Hs]].
    apply domE in Hx as [y Hp]. subst s.
    exists <x, y>. apply SepI... rewrite π1_correct...
  }
  assert (Hsp: ∀s ∈ S, ∀x ∈ s, is_pair x). {
    intros s Hs x Hx. apply ReplAx in Hs as [y [_ Hs]].
    subst s. apply SepE in Hx as [Hx _]. apply H in Hx...
  }
  assert (Hss: ∀ a b c, ∀ s t ∈ S,
    <a, b> ∈ s → <a, c> ∈ t → s = t). {
    intros * s Hs t Ht His Hit.
    apply ReplAx in Hs as [z [_ Hs] ]. subst s.
    apply ReplAx in Ht as [w [_ Ht]]. subst t.
    apply SepE in His as [_ Hz].
    apply SepE in Hit as [_ Hw]. rewrite π1_correct in *. subst...
  }
  assert (Hdj: ∀ s t ∈ S, s ≠ t → s ∩ t = ∅). {
    intros s Hs t Ht Hnq. apply EmptyI. intros x Hx.
    apply BInterE in Hx as [Hxs Hxt]. apply Hnq. clear Hnq.
    apply ReplAx in Hs as [z [_ Hs]]. subst s.
    apply ReplAx in Ht as [w [_ Ht]]. subst t.
    apply SepE in Hxs as [_ Hxz].
    apply SepE in Hxt as [_ Hxw]. subst...
  }
  assert (Hsub: {Choice | s ∊ S} ⊆ R). {
    intros x Hx. apply ReplAx in Hx as [s [Hs Hx]]. subst x.
    pose proof (chosen_contained s (Hi s Hs)) as Hc.
    apply ReplAx in Hs as [a [_ Hs]]. rewrite <- Hs in Hc at 2.
    apply SepE in Hc as []...
  }
  exists {Choice | s ∊ S}. repeat split...
  - intros x Hx. apply ReplAx in Hx as [s [Hs Heq]].
    pose proof (chosen_contained s (Hi s Hs)) as Hx.
    rewrite Heq in Hx. eapply Hsp...
  - apply domE in H0...
  - intros y y' Hcy Hcy'.
    assert (Hy := Hcy). assert (Hy' := Hcy').
    apply ReplAx in Hy  as [s  [Hs  Heq ]].
    apply ReplAx in Hy' as [s' [Hs' Heq']].
    pose proof (chosen_contained s  (Hi s  Hs )) as Hsy.
    pose proof (chosen_contained s' (Hi s' Hs')) as Hsy'.
    rewrite Heq in Hsy. rewrite Heq' in Hsy'.
    assert (s = s') by (eapply Hss; eauto). subst s'.
    cut (<x, y> = <x, y'>). apply op_correct.
    eapply binter_unique. apply Hsy. apply Hsy'.
    apply Hcy. apply Hcy'. apply one_chosen...
  - apply ExtAx. intros x. split; intros Hxd.
    + apply domE in Hxd as [y Hp]. apply Hsub in Hp. eapply domI...
    + set {p ∊ R | λ p, π1 p = x} as s.
      assert (Hs: s ∈ S). { apply ReplAx. exists x. split... }
      pose proof (chosen_contained s (Hi s Hs)) as Hc.
      assert (Hc' := Hc). apply SepE in Hc as [_ Hx].
      apply Hsp in Hc' as [x' [y Hp]]... rewrite Hp in Hx.
      rewrite π1_correct in Hx. subst x'.
      eapply domI. apply ReplAx. exists s. split...
Qed.

(** 函数的右逆 **)
Theorem right_inv : ∀ F A B,
  F: A ⇒ B →
  (∃ G, G: B ⇒ A ∧ F ∘ G = Ident B) ↔ F: A ⟹ B.
Proof with eauto.
  intros F A B [Hf [Hdf Hrf]]. split.
  (* -> *)
  intros [G [[Hg [Hdg _]] Heq]]. split... split...
  (* ran F = B *)
  apply ExtAx. intros x. split; intros Hx. apply Hrf...
  assert (H: x ∈ dom (Ident B)) by (rewrite dom_ident; auto).
  apply domE in H as [y Hp].
  pose proof (identE _ _ _ Hp) as [_ H].
  subst y. rewrite <- Heq in Hp.
  apply compoE in Hp as [t [_ Ht]]. eapply ranI...
  (* <- *)
  intros [_ [_ Hr]].
  assert (is_relation F ⁻¹) by apply inv_rel.
  apply choose_func_from_rel in H as [G [H1 [H2 H3]]].
  exists G. split.
  (* G: B ⇒ A *) split... split.
  rewrite inv_dom in H3. subst B...
  intros x Hx. apply ranE in Hx as [y Hx].
  apply H2, ranI in Hx. rewrite inv_ran in Hx. subst A...
  (* F ∘ G = Ident B *)
  apply ExtAx. intros y. split; intros Hy.
  - apply SepE in Hy as [_ [Hp [x [Hp1 Hp2]]]].
    apply H2 in Hp1. rewrite <- inv_op in Hp1.
    apply ReplAx. exists (π1 y). split. subst B. eapply ranI...
    apply op_η in Hp. rewrite Hp at 3. apply op_correct. split...
    clear H1. eapply func_sv...
  - apply ReplAx in Hy as [a [Hp Heq]].
    subst y. subst B. rewrite <- inv_dom in Hp. rewrite <- H3 in Hp. 
    apply domE in Hp as [b Hpg]. assert (Hpf := Hpg).
    apply H2 in Hpf. rewrite <- inv_op in Hpf. eapply compoI...
Qed.

(** 限制 **)
Definition Restriction : set → set → set :=
  λ F A, {p ∊ F | λ p, is_pair p ∧ π1 p ∈ A}.
Notation "F ↾ A" := (Restriction F A) (at level 60).

Lemma restrI : ∀ F A a b, a ∈ A → <a, b> ∈ F → <a, b> ∈ F ↾ A.
Proof with auto.
  intros. apply SepI... split. exists a, b...
  rewrite π1_correct...
Qed.

Lemma restrE1 : ∀ F A, ∀x ∈ F ↾ A,
  ∃ a b, a ∈ A ∧ <a, b> ∈ F ∧ x = <a, b>.
Proof.
  intros * x Hx. apply SepE in Hx as [Hx [[a [b Hp]] Ha]].
  subst x. rewrite π1_correct in Ha. exists a, b; auto.
Qed.

Lemma restrE2 : ∀ F A x y, <x, y> ∈ F ↾ A →
  <x, y> ∈ F ∧ x ∈ A.
Proof.
  intros * Hp. apply restrE1 in Hp as [a [b [Ha [Hp Heq]]]].
  apply op_correct in Heq as []; subst. split; auto.
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

Lemma restr_to_dom : ∀ F, is_relation F → F ↾ (dom F) = F.
Proof with eauto.
  intros. apply ExtAx. split; intros Hx.
  - apply restrE1 in Hx as [a [b [Ha [Hx Heq]]]]. subst...
  - apply rel_pair in Hx as Heq... rewrite Heq.
    rewrite Heq in Hx. apply restrI... eapply domI...
Qed.

Lemma restr_dom : ∀ F A, is_function F →
  A ⊆ dom F ↔ dom (F ↾ A) = A.
Proof with auto.
  intros * Hf. split; intros.
  - apply ExtAx. intros x. split; intros Hx.
    + apply domE in Hx as [y Hp].
      apply restrE2 in Hp as []...
    + eapply domI. apply restrI...
      apply func_correct... apply H...
  - rewrite <- H. apply restr_dom_included.
Qed.

Example restr_func : ∀ F A,
  is_function F → is_function (F ↾ A).
Proof.
  unfold is_function, is_relation. intros F A [H1 H2]. split.
  - intros x Hx. apply SepE in Hx as [Hx _].
    apply H1 in Hx. apply Hx.
  - intros x Hx. split.
    + apply domE in Hx as Hp. apply Hp.
    + intros y1 y2 Hy1 Hy2.
      apply SepE in Hy1 as [Hy1 _].
      apply SepE in Hy2 as [Hy2 _].
      apply restr_dom_included in Hx.
      apply H2 in Hx as [_ H]. apply H; assumption.
Qed.

Lemma restr_injective : ∀ F A, injective F → injective (F ↾ A).
Proof with eauto.
  intros * [Hf Hs]. split. apply restr_func...
  split. apply ranE in H... clear H.
  intros y1 y2 H1 H2.
  apply restrE2 in H1 as [H1 _].
  apply restrE2 in H2 as [H2 _].
  eapply Hs; revgoals... eapply ranI...
Qed.

(** 像 **)
Definition Image : set → set → set :=
  λ F A, ran (F ↾ A).
Notation "F ⟦ A ⟧" := (Image F A) (at level 30).

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

Lemma img_correct : ∀ F A,
  is_function F → A ⊆ dom F → F⟦A⟧ = {λ a, F[a] | a ∊ A}.
Proof with eauto.
  intros F A Hf Hsub. apply ExtAx. intros y. split; intros Hy.
  - apply ReplAx. apply imgE in Hy as [x [Hx Hp]].
    exists x. split... apply Hsub in Hx. apply func_ap...
  - apply ReplAx in Hy as [x [Hx Heq]]. apply Hsub in Hx as Hx'.
    pose proof (ap_exists F Hf x Hx') as [t [_ [Hxy Ht]]].
    subst t. rewrite Heq in Hxy. eapply imgI...
Qed.

Theorem img_bunion_distr : ∀ F A B, F⟦A ∪ B⟧ = F⟦A⟧ ∪ F⟦B⟧.
Proof with eauto.
  intros. apply ExtAx. intros y. split; intros Hy.
  - apply imgE in Hy as [x [Hx Hp]]. apply BUnionE in Hx as [].
    + apply BUnionI1. eapply imgI...
    + apply BUnionI2. eapply imgI...
  - apply BUnionE in Hy as []; apply imgE in H as [x [Hx Hp]].
    + eapply imgI... apply BUnionI1...
    + eapply imgI... apply BUnionI2...
Qed.

Theorem img_union_distr : ∀ F 𝒜, F⟦⋃𝒜⟧ = ⋃{λ A, F⟦A⟧ | A ∊ 𝒜}.
Proof with eauto.
  intros. apply ExtAx. intros y. split; intros Hy.
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
  intros F A B Hs. apply ExtAx. intros y. split; intros Hy.
  - apply img_binter_distr_sub...
  - apply BInterE in Hy as [Ha Hb].
    apply imgE in Ha as [w [Hw Hpf]].
    apply imgE in Hb as [x [Hx Hpg]].
    assert (Heq: w = x) by (eapply singrE; eauto).
    subst. eapply imgI... apply BInterI...
Qed.

Theorem img_inter_distr_sub : ∀ F 𝒜, F⟦⋂𝒜⟧ ⊆ ⋂{λ A, F⟦A⟧ | A ∊ 𝒜}.
Proof with eauto.
  intros F 𝒜 y Hy. apply imgE in Hy as [x [Hx Hp]].
  apply InterE in Hx as [[A HA] H].
  apply InterI. exists (F⟦A⟧). apply ReplI...
  intros Y HY. apply ReplAx in HY as [B [HB Heq]]. subst Y.
  eapply imgI... apply H in HB...
Qed.

Theorem img_inter_distr : ∀ F 𝒜,
  single_rooted F → F⟦⋂𝒜⟧ = ⋂{λ A, F⟦A⟧ | A ∊ 𝒜}.
Proof with eauto.
  intros F 𝒜 Hs. apply ExtAx. intros y. split; intros Hy.
  - apply img_inter_distr_sub...
  - apply InterE in Hy as [[Y HY] H]. apply H in HY as Hy.
    apply ReplAx in HY as [A [HA Heq]]. subst Y.
    apply imgE in Hy as [x [_ Hp]].
    eapply imgI... apply InterI. exists A... intros B HB.
    assert (HY: F⟦B⟧ ∈ {Image F | A ∊ 𝒜}). {
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
  intros * Hs. apply ExtAx. intros y. split; intros Hy.
  - apply img_comp_distr_sub...
  - apply imgE in Hy as [x [Hx Hp]]. apply CompE in Hx as [Ha Hb].
    apply CompI. eapply imgI... intros H.
    apply Hb. apply imgE in H as [w [Hw Hq]].
    assert (w = x) by (eapply singrE; eauto). subst...
Qed.

Corollary img_inv_union_distr : ∀ F 𝒜,
  F⁻¹⟦⋃𝒜⟧ = ⋃{λ A, F⁻¹⟦A⟧ | A ∊ 𝒜}.
Proof. intros. exact (img_union_distr F⁻¹ 𝒜). Qed.

Corollary img_inv_inter_distr : ∀ F 𝒜,
  is_function F → F⁻¹⟦⋂𝒜⟧ = ⋂{λ A, F⁻¹⟦A⟧ | A ∊ 𝒜}.
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
  {F ∊ 𝒫(A × B) | λ F, F: A ⇒ B}.
Notation "A ⟶ B" := (Arrow A B) (at level 60).

Theorem Arrow_correct : ∀ F A B,
  F ∈ A ⟶ B ↔ is_function F ∧ dom F = A ∧ ∀x ∈ A, F[x] ∈ B.
Proof with eauto.
  intros. split.
  - intros HF. apply SepE2 in HF as [Hf [Heq Hsub]].
    split... split... intros x Hx.
    apply Hsub. eapply ranI. apply func_correct... subst...
  - intros [Hf [Hd Hap]]. subst A. apply SepI.
    + apply PowerAx. intros p Hp.
      assert (Hp' := Hp). apply func_pair in Hp'...
      rewrite Hp'. rewrite Hp' in Hp.
      apply CProdI. eapply domI... apply domI in Hp as Hd.
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
Definition InfCProd : set → set → set := λ I X,
  {f ∊ I ⟶ ⋃{λ i, X[i] | i ∊ I} | λ f, ∀i ∈ I, f[i] ∈ X[i]}.

Example infcprod_self : ∀ I X A,
  ⦿ I → (∀i ∈ I, X[i] = A) → InfCProd I X = I ⟶ A.
Proof with eauto.
  intros * [i Hi] H.
  assert (Heq: ⋃ {ap X | i ∊ I} = A). {
    apply ExtAx. split; intros Hx.
    - apply FUnionE in Hx as [j [Hj Hx]]. apply H in Hj. subst A...
    - eapply FUnionI... apply H in Hi. subst A...
  }
  apply ExtAx. intros f. split; intros Hf.
  - apply SepE in Hf as [Hf _]. subst A...
  - apply SepI. subst A... clear Heq.
    intros j Hj. apply H in Hj as Heq. rewrite Heq. clear Heq.
    apply SepE in Hf as [_ [Hf [Hd Hr]]]. apply Hr.
    eapply ranI. apply func_correct... subst I...
Qed.

(* 选择公理等效表述2：非空集合的笛卡尔积非空 *)
Definition AC_2nd_form : Prop := ∀ I X,
  (∀i ∈ I, ⦿ X[i]) → ⦿ InfCProd I X.

Theorem AC_1_iff_2 : AC_1st_form ↔ AC_2nd_form.
Proof with eauto.
  unfold AC_1st_form, AC_2nd_form. split.
  - intros * AC1 I X Hxi.
    set (I × ⋃{λ i, X[i] | i ∊ I}) as P.
    set {p ∊ P | λ p, π2 p ∈ X[π1 p]} as R.
    assert (H: is_relation R) by apply sep_cp_is_rel.
    apply AC1 in H as [F [Hf [Hsub Hdeq]]].
    assert (Hdeq2: dom F = I). {
      rewrite Hdeq. apply ExtAx. intros i. split; intros Hi.
      - apply domE in Hi as [y Hp]. apply SepE in Hp as [Hp _].
        apply CProdE1 in Hp as [Hi _]. rewrite π1_correct in Hi...
      - apply Hxi in Hi as Hx. destruct Hx.
        eapply domI. apply SepI. apply CProdI...
        eapply FUnionI... rewrite π1_correct, π2_correct...
    }
    exists F. apply SepI.
    + apply SepI. rewrite PowerAx. intros x Hp.
      apply func_pair in Hp as Hxeq... rewrite Hxeq in *.
      apply domI in Hp as Hd. rewrite Hdeq2 in Hd.
      apply Hsub in Hp. apply SepE in Hp as [_ Hp].
      rewrite π1_correct, π2_correct in Hp.
      apply CProdI... eapply UnionI... eapply ReplI...
      split... split... intros y Hy. apply ranE in Hy as [i Hp].
      apply Hsub in Hp. apply SepE in Hp as [Hp _].
      apply CProdE1 in Hp as [_ Hy]. rewrite π2_correct in Hy...
    + intros i Hi. rewrite <- Hdeq2 in Hi.
      apply func_correct in Hi... apply Hsub in Hi.
      apply SepE in Hi as [_ Hy].
      rewrite π1_correct, π2_correct in Hy...
  - intros AC2 R Hr.
    set (dom R) as I.
    set (λ i, {y ∊ ran R | λ y, <i, y> ∈ R}) as ℱ.
    set ({p ∊ I × 𝒫(ran R) | λ p, π2 p = ℱ (π1 p)}) as X.
    assert (HXf: is_function X). {
      split. apply sep_cp_is_rel.
      intros i. split. apply domE in H...
      intros Y Y' HY HY'.
      apply SepE in HY as [_ Hp].
      apply SepE in HY' as [_ Hp'].
      rewrite π1_correct, π2_correct in *. subst...
    }
    assert (HXd: dom X = I). {
      apply ExtAx. intros i. split; intros Hi.
      - apply domE in Hi as [y Hp]. apply SepE in Hp as [Hp _].
        apply CProdE1 in Hp as [Hi _]. rewrite π1_correct in Hi...
      - eapply domI. apply SepI. apply CProdI...
        rewrite PowerAx. cut (ℱ i ⊆ ran R)...
        intros x Hx. apply SepE in Hx as []...
        rewrite π1_correct, π2_correct...
    }
    assert (Hℱeq: ∀i ∈ I, X[i] = ℱ i). {
      intros i Hi. rewrite <- HXd in Hi.
      apply func_correct in Hi... apply SepE in Hi as [_ Heq].
      rewrite π1_correct, π2_correct in Heq...
    }
    assert (HXP: ∀i ∈ I, ∀y ∈ X[i], <i, y> ∈ R). {
      intros i Hi y Hy. apply Hℱeq in Hi. rewrite Hi in Hy.
      apply SepE in Hy as []...
    }
    assert (HXi: ∀i ∈ I, ⦿ X[i]). {
      intros i Hi. assert (Hi' := Hi).
      apply domE in Hi' as [y Hp]. apply Hℱeq in Hi. rewrite Hi.
      exists y. apply SepI... eapply ranI...
    }
    apply AC2 in HXi as [F HF].
    apply SepE in HF as [HF HP].
    apply Arrow_correct in HF as [Hf [Hdeq _]].
    exists F. split... split...
    intros x Hx. apply func_pair in Hx as Hxeq...
    rewrite Hxeq in *. apply domI in Hx as Hd.
    rewrite Hdeq in Hd. apply HP in Hd as H.
    apply HXP in H... apply func_ap in Hx... rewrite Hx in H...
Qed.
