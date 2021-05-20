(** Based on "Elements of Set Theory" Chapter 7 Part 3 **)
(** Coq coding by choukh, Dec 2020 **)

Require Import Relation_Definitions.
Require Import RelationClasses.
Require Import PropExtensionality.
Require Import ZFC.lib.FuncFacts.
Require Import ZFC.lib.WosetMin.
Require Export ZFC.EST7_2.

(*** EST第七章3：序结构，序同构，良序结构，伊普西隆像 ***)

(* 序结构 *)
Module OrderedStruct.
Declare Scope OrderedStruct_scope.
Delimit Scope OrderedStruct_scope with os.
Open Scope OrderedStruct_scope.

Record OrderedStruct : Type := constr {
  A : set;
  R : set;
  ordered_struct : is_binRel R A;
}.

Lemma eq_intro : ∀ S T, A S = A T → R S = R T → S = T.
Proof.
  intros S T HA HR. destruct S. destruct T.
  simpl in *. subst. f_equal. apply proof_irrelevance.
Qed.

Definition po := λ S, poset (A S) (R S).
Definition lo := λ S, loset (A S) (R S).
Definition wo := λ S, woset (A S) (R S).

(* 序嵌入双射 *)
Definition order_embedding_bijection := λ f S T, f: A S ⟺ A T ∧
  ∀ x y ∈ A S, (x <ᵣ y) (R S) ↔ (f[x] <ᵣ f[y]) (R T).
Notation "f :ₒₑ S ⟺ T" := (order_embedding_bijection f S T)
  (at level 70) : OrderedStruct_scope.

(* 序同构 *)
Definition isomorphic : relation OrderedStruct :=
  λ S T, ∃ f, f :ₒₑ S ⟺ T.

Notation "S ≅ T" := ( isomorphic S T) (at level 60) : OrderedStruct_scope.
Notation "S ≇ T" := (¬isomorphic S T) (at level 60) : OrderedStruct_scope.

Theorem iso_refl : Reflexive isomorphic.
Proof with auto.
  intros S. exists (Ident (A S)).
  split. apply ident_bijection.
  intros x Hx y Hy. rewrite ident_ap, ident_ap... reflexivity.
Qed.

Theorem iso_symm : Symmetric isomorphic.
Proof with eauto.
  intros S T [f [Hf H]]. exists (f⁻¹).
  pose proof (inv_bijection f (A S) (A T) Hf) as Hf'.
  destruct Hf as [Hi [_ Hr]].
  split... intros x Hx y Hy. symmetry.
  replace x with (f[f⁻¹[x]]) at 2.
  replace y with (f[f⁻¹[y]]) at 2. apply H.
  eapply ap_ran... apply bijection_is_func...
  eapply ap_ran... apply bijection_is_func...
  rewrite inv_ran_reduction... congruence.
  rewrite inv_ran_reduction... congruence.
Qed.

Theorem iso_tran : Transitive isomorphic.
Proof with eauto; try congruence.
  intros S T U [f [Hf H1]] [g [Hg H2]]. exists (g ∘ f).
  pose proof (compo_bijection f g (A S) (A T) (A U) Hf Hg) as Hcom.
  apply bijection_is_func in Hf as [Hf _].
  apply bijection_is_func in Hg as [Hg _].
  assert (H := Hf). destruct H as [Hff [Hdf _]].
  assert (H := Hg). destruct H as [Hfg [Hdg _]].
  split... intros x Hx y Hy.
  rewrite (H1 x Hx y Hy).
  rewrite compo_correct, compo_correct...
  - apply H2. eapply ap_ran... eapply ap_ran...
  - rewrite compo_dom... apply SepI...
    rewrite Hdg. eapply ap_ran...
  - rewrite compo_dom... apply SepI...
    rewrite Hdg. eapply ap_ran...
Qed.

(* 序同构是等价关系 *)
Theorem iso_equiv : Equivalence isomorphic.
Proof.
  split. apply iso_refl. apply iso_symm. apply iso_tran.
Qed.
Existing Instance iso_equiv.

(* 像关系 *)
Module ImageRel.

Definition constr := λ f B R,
  BinRel B (λ x y, (f[x] <ᵣ f[y]) R).

Lemma po : ∀ f B A R, poset A R → poset B (constr f B R).
Proof with eauto.
  intros * [_ [_ [Htr Hir]]]. repeat split...
  - apply binRel_is_binRel.
  - eapply binRel_is_rel... apply binRel_is_binRel.
  - intros x y z Hxy Hyz.
    apply binRelE2 in Hxy as [Hx [Hy Hxy]].
    apply binRelE2 in Hyz as [_  [Hz Hyz]].
    apply binRelI... eapply Htr...
  - intros x Hxx.
    apply binRelE3 in Hxx. eapply Hir...
Qed.

Lemma lo : ∀ f B A R, f: B ⇔ A →
  loset A R → loset B (constr f B R).
Proof with eauto; try congruence.
  intros * Hf Hlo.
  apply injection_is_func in Hf as [Hf Hi].
  apply loset_iff_connected_poset in Hlo as [Hcon Hpo].
  apply loset_iff_connected_poset. split; [|eapply po]...
  intros x Hx y Hy Hnq.
  assert (Hnqf: f[x] ≠ f[y]). {
    destruct Hf as [_ [Hd _]].
    intros H. apply Hnq. eapply injectiveE...
  }
  edestruct Hcon... eapply ap_ran... eapply ap_ran...
  - left. apply binRelI...
  - right. apply binRelI...
Qed.

Lemma wo : ∀ f B A R, f: B ⇔ A →
  woset A R → woset B (constr f B R).
Proof with eauto; try congruence.
  intros * Hf [Hlo Hmin]. split. eapply lo...
  intros A' [a Ha'] Hsub. apply Hsub in Ha' as Ha.
  apply injection_is_func in Hf as [[Hf [Hd Hr]] Hi].
  specialize Hmin with (f⟦A'⟧) as [b [Hb Hmin]]. {
    exists (f[a]). eapply imgI... apply func_correct...
  } {
    intros y Hy. apply imgE in Hy as [x [Hx Hp]].
    eapply ranI in Hp. apply Hr...
  }
  apply imgE in Hb as [m [Hm' Hp]].
  apply Hsub in Hm' as Hm.
  apply func_ap in Hp... subst b.
  exists m. split... intros x Hx'.
  destruct (classic (m = x)). right... left.
  apply Hsub in Hx' as Hx.
  apply binRelI... edestruct Hmin...
  eapply imgI... apply func_correct...
  exfalso. apply H. eapply injectiveE...
Qed.

Fact eq_subRel : ∀ R B, R ⥏ B = constr (Ident B) B R.
Proof with auto.
  intros. apply ExtAx. split; intros Hx.
  - apply SepE in Hx as [Hlt Hp].
    apply CProdE1 in Hp as [a [Ha [b [Hb Heq]]]]. subst x.
    apply SepI... apply CProdI... zfc_simple.
    rewrite ident_ap, ident_ap...
  - apply SepE in Hx as [Hp Hlt].
    apply CProdE1 in Hp as [a [Ha [b [Hb Heq]]]]. subst x.
    zfc_simple. rewrite ident_ap, ident_ap in Hlt...
    apply SepI... apply CProdI...
Qed.

End ImageRel.

(* 与偏序结构同构的结构也是偏序结构 *)
Theorem iso_po : ∀ S T, S ≅ T → po S → po T.
Proof with auto.
  intros * Hiso Hpo. symmetry in Hiso.
  destruct Hiso as [f [_ H]].
  eapply (ImageRel.po f (A T)) in Hpo.
  replace (ImageRel.constr f (A T) (R S)) with (R T) in Hpo...
  apply ExtAx. intros p. split; intros Hp.
  - apply ordered_struct in Hp as Hcp.
    apply CProdE1 in Hcp as [a [Ha [b [Hb Heq]]]].
    subst p. apply binRelI... apply H...
  - apply binRelE1 in Hp as [a [Ha [b [Hb [Heq Hlt]]]]].
    subst p. apply H...
Qed.

(* 与线序结构同构的结构也是线序结构 *)
Theorem iso_lo : ∀ S T, S ≅ T → lo S → lo T.
Proof with auto.
  intros * Hiso Hlo. symmetry in Hiso.
  destruct Hiso as [f [Hf H]].
  apply bijection_is_injection in Hf as [Hf _].
  apply (ImageRel.lo f (A T)) in Hlo...
  replace (ImageRel.constr f (A T) (R S)) with (R T) in Hlo...
  apply ExtAx. intros p. split; intros Hp.
  - apply ordered_struct in Hp as Hcp.
    apply CProdE1 in Hcp as [a [Ha [b [Hb Heq]]]].
    subst p. apply binRelI... apply H...
  - apply binRelE1 in Hp as [a [Ha [b [Hb [Heq Hlt]]]]].
    subst p. apply H...
Qed.

(* 与良序结构同构的结构也是良序结构 *)
Theorem iso_wo : ∀ S T, S ≅ T → wo S → wo T.
Proof with auto.
  intros * Hiso Hwo. symmetry in Hiso.
  destruct Hiso as [f [Hf H]].
  apply bijection_is_injection in Hf as [Hf _].
  apply (ImageRel.wo f (A T)) in Hwo...
  replace (ImageRel.constr f (A T) (R S)) with (R T) in Hwo...
  apply ExtAx. intros p. split; intros Hp.
  - apply ordered_struct in Hp as Hcp.
    apply CProdE1 in Hcp as [a [Ha [b [Hb Heq]]]].
    subst p. apply binRelI... apply H...
  - apply binRelE1 in Hp as [a [Ha [b [Hb [Heq Hlt]]]]].
    subst p. apply H...
Qed.

End OrderedStruct.

(* 良序结构 *)
Module WoStruct.
Declare Scope WoStruct_scope.
Delimit Scope WoStruct_scope with wo.
Open Scope WoStruct_scope.

Record WoStruct : Type := constr {
  A : set;
  R : set;
  wo : woset A R;
}.
Global Hint Immediate wo : core.

Notation 𝛚 := (constr ω Lt Lt_wellOrder).

Lemma eq_intro : ∀ S T, A S = A T → R S = R T → S = T.
Proof.
  intros S T HA HR. destruct S. destruct T.
  simpl in *. subst. f_equal. apply proof_irrelevance.
Qed.

(* 序嵌入双射 *)
Definition order_embedding_bijection := λ f S T, f: A S ⟺ A T ∧
  ∀ x y ∈ A S, (x <ᵣ y) (R S) ↔ (f[x] <ᵣ f[y]) (R T).
Notation "f :ₒₑ S ⟺ T" := (order_embedding_bijection f S T)
  (at level 70) : WoStruct_scope.

Definition isomorphic : relation WoStruct :=
  λ S T, ∃ f, f :ₒₑ S ⟺ T.

Notation "S ≅ T" := ( isomorphic S T) (at level 60) : WoStruct_scope.
Notation "S ≇ T" := (¬isomorphic S T) (at level 60) : WoStruct_scope.

Definition SubStruct := λ S T, A S ⊆ A T ∧ R S = R T ⥏ A S.
Notation "S ⊑ T" := (SubStruct S T) (at level 70) : WoStruct_scope.

Local Lemma woset_is_binRel : ∀ A R, woset A R → is_binRel R A.
Proof. intros. apply H. Qed.

Local Definition br := λ S, woset_is_binRel (A S) (R S) (wo S).
Definition parent := λ S, OrderedStruct.constr (A S) (R S) (br S).

Lemma parent_iso : ∀ S T,
  S ≅ T ↔ OrderedStruct.isomorphic (parent S) (parent T).
Proof.
  split; intros [f [Hf Hoe]]; exists f; split; auto.
Qed.

Lemma parent_wo : ∀ S, OrderedStruct.wo (parent S).
Proof. intros. apply wo. Qed.

Theorem iso_refl : Reflexive isomorphic.
Proof.
  intros S. apply parent_iso. apply OrderedStruct.iso_refl.
Qed.

Theorem iso_symm : Symmetric isomorphic.
Proof.
  intros S T H. rewrite parent_iso in H. apply parent_iso.
  apply OrderedStruct.iso_symm; auto.
Qed.

Theorem iso_tran : Transitive isomorphic.
Proof.
  intros S T U H1 H2. rewrite parent_iso in H1, H2.
  apply parent_iso. eapply OrderedStruct.iso_tran; eauto.
Qed.

Theorem iso_equiv : Equivalence isomorphic.
Proof.
  split. apply iso_refl. apply iso_symm. apply iso_tran.
Qed.
Existing Instance iso_equiv.

(* 良序结构间的态射唯一 *)
Theorem wo_iso_unique : ∀ S T, S ≅ T → ∃! f, f :ₒₑ S ⟺ T.
Proof with eauto; try congruence.
  intros S T Hiso. split...
  intros f g [Hf H1] [Hg H2].
  cut (∀ f g S T, f :ₒₑ S ⟺ T → g :ₒₑ S ⟺ T → f ⊆ g). {
    intros H. apply sub_antisym; eapply H; split...
  }
  clear Hiso Hf H1 Hg H2 f g S T.
  intros f g S T [Hf Hoe] [Hg Hopg] p Hp.
  destruct (wo S) as [Hlo Hmin].
  apply inv_bijection in Hf as Hf'.
  apply bijection_is_func in Hf' as [Hf' _].
  apply bijection_is_func in Hf as [Hf [Hif Hrf]].
  assert (H := Hf). destruct H as [Hff [Hdf _]].
  apply inv_bijection in Hg as Hg'.
  apply bijection_is_func in Hg' as [Hg' _].
  apply bijection_is_func in Hg as [Hg [Hig Hrg]].
  assert (H := Hg). destruct H as [Hfg [Hdg _]].
  apply func_pair' in Hp as [x [y [Hp Heqp]]]... subst p.
  apply domI in Hp as Hx. rewrite Hdf in Hx.
  set {x ∊ A S | λ x, f[x] = g[x]} as AS'.
  replace (A S) with AS' in Hx. {
    apply SepE in Hx as [Hx Heq].
    apply func_ap in Hp... apply func_point...
  }
  eapply transfinite_induction...
  split. intros a Ha. apply SepE1 in Ha...
  intros t Ht Hsub. apply SepI...
  destruct (classic (f[t] = g[t]))... exfalso.
  apply (lo_connected (R T) (A T)) in H as []; revgoals...
  eapply ap_ran... eapply ap_ran... apply (wo T).
  - assert (Hgt: g[t] ∈ ran f). {
      rewrite Hrf, <- Hrg. eapply ranI. apply func_correct...
    }
    rewrite <- (inv_ran_reduction f Hif (g[t])) in H...
    apply Hoe in H; revgoals... { eapply ap_ran... }
    remember (f⁻¹[g[t]]) as t'.
    assert (Ht': t' ∈ seg t (R S)) by (apply segI; auto).
    apply Hsub in Ht'. apply SepE in Ht' as [Ht' Heq].
    rewrite Heqt' in Heq at 1.
    rewrite inv_ran_reduction in Heq...
    eapply injectiveE in Heq... rewrite Heq in H.
    eapply (lo_irrefl (R S) (A S))...
  - assert (Hft: f[t] ∈ ran g). {
      rewrite Hrg, <- Hrf. eapply ranI. apply func_correct...
    }
    rewrite <- (inv_ran_reduction g Hig (f[t])) in H...
    apply Hopg in H; revgoals... { eapply ap_ran... }
    remember (g⁻¹[f[t]]) as t'.
    assert (Ht': t' ∈ seg t (R S)) by (apply segI; auto).
    apply Hsub in Ht'. apply SepE in Ht' as [Ht' Heq].
    rewrite Heqt' in Heq at 2.
    rewrite inv_ran_reduction in Heq...
    eapply injectiveE in Heq... rewrite Heq in H.
    eapply (lo_irrefl (R S) (A S))...
Qed.

Section Seg.

Let seg := λ t A R, {x ∊ A | λ x, (x <ᵣ t) R}.

Lemma seg_woset : ∀ t A R, woset A R →
  let B := seg t A R in woset B (R ⥏ B).
Proof.
  intros t A R H B. eapply subRel_woset; eauto.
  intros x Hx. apply SepE1 in Hx. apply Hx.
Qed.

Definition Seg := λ t S,
  let B := seg t (A S) (R S) in
  constr B ((R S) ⥏ B) (seg_woset _ _ _ (wo S)).

End Seg.

Lemma seg_a_eq : ∀ S, ∀t ∈ A S, A (Seg t S) = seg t (R S).
Proof with eauto.
  intros S t Ha.
  apply ExtAx. split; intros Hx.
  - apply SepE in Hx as [Hx Hxa].
    apply SepI... eapply domI...
  - apply SepE in Hx as [Hx Hxa].
    apply SepI... eapply dom_binRel... apply wo.
Qed.

Lemma seg_lt : ∀ S r s t, (s <ᵣ t) (R S) →
  (r <ᵣ s) (R (Seg t S)) ↔ (r <ᵣ s) (R S).
Proof with eauto.
  intros S r s t Hst. split; intros Hlt.
  - apply SepE1 in Hlt...
  - apply SepI... apply CProdI; apply SepI...
    eapply dom_binRel. apply wo. eapply domI...
    destruct (wo S) as [[_ [Htr _]] _]. eapply Htr...
    eapply dom_binRel. apply wo. eapply domI...
Qed.

Lemma seg_of_seg : ∀ S r s t, (s <ᵣ t) (R S) →
  r ∈ seg s (R (Seg t S)) ↔ r ∈ seg s (R S).
Proof with auto.
  intros S r s t Hst. split; intros Hlt.
  - apply SepE2 in Hlt. apply seg_lt in Hlt... apply segI...
  - apply segI. apply seg_lt... apply SepE2 in Hlt...
Qed.

Section Recursion.
Import TransfiniteRecursion.

Definition Recursion := λ S γ, constr (A S) (R S) γ.

Definition recrusion_spec := λ S γ F,
  is_function F ∧ dom F = A S ∧ ∀t ∈ A S, γ (F ↾ seg t (R S)) F[t].

Lemma recrusion_spec_intro : ∀ S γ, (∀ x, ∃! y, γ x y) →
  recrusion_spec S γ (Recursion S γ).
Proof. intros. apply spec_intro; auto. Qed.

End Recursion.

(* 伊普西隆像 *)
Module Import EpsilonImage.

Definition γ := λ x y, y = ran x.
Definition E := λ S, Recursion S γ.
Definition α := λ S, ran (E S).
Definition ε := λ S, MemberRel (α S).

Lemma e_spec : ∀ S, recrusion_spec S γ (E S).
Proof.
  intros. apply recrusion_spec_intro. intros f. split.
  exists (ran f). congruence. congruence.
Qed.

Lemma e_empty : ∀ S, A S = ∅ → E S = ∅.
Proof.
  intros. destruct (e_spec S) as [Hf [Hd _]].
  apply empty_dom; congruence.
Qed.

Lemma e_ap : ∀ S,
  ∀t ∈ A S, (E S)[t] = {λ x, (E S)[x] | x ∊ seg t (R S)}.
Proof with eauto.
  intros S t Ht. destruct (e_spec S) as [Hf [Hd Hγ]].
  apply Hγ in Ht. rewrite Ht.
  apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [x Hp]. apply restrE2 in Hp as [Hp Hx].
    apply ReplAx. exists x. split... apply func_ap in Hp...
  - apply ReplAx in Hy as [x [Hx Hap]].
    apply (ranI _ x). apply restrI... apply func_point...
    rewrite Hd. apply SepE in Hx as [Hx _].
    eapply dom_binRel... destruct (wo S) as [[] _]...
Qed.

Lemma e_ap_order : ∀ S,
  ∀ s t ∈ A S, (s <ᵣ t) (R S) → (E S)[s] ∈ (E S)[t].
Proof with auto.
  intros S s Hs t Ht Hst. rewrite (e_ap S t Ht).
  apply ReplI... apply segI...
Qed.

Lemma e_intro : ∀ S, ∀ x, ∀ s t ∈ A S,
  (s <ᵣ t) (R S) → x = (E S)[s] → x ∈ (E S)[t].
Proof.
  intros S x s Hs t Ht Hst Hest. subst.
  apply e_ap_order; auto.
Qed.

Lemma e_elim : ∀ S, ∀t ∈ A S, ∀x ∈ (E S)[t],
  ∃s ∈ A S, (s <ᵣ t) (R S) ∧ x = (E S)[s] ∧ x ∈ (E S)[t].
Proof with eauto.
  intros S t Ht x Hx.
  assert (H := Hx). rewrite e_ap in H...
  apply ReplAx in H as [s [Hs Heq]].
  apply SepE in Hs as [Hs Hst].
  eapply dom_binRel in Hs...
  exists s. split... apply wo.
Qed.

Theorem e_irrefl : ∀ S, ∀t ∈ A S, (E S)[t] ∉ (E S)[t].
Proof with eauto.
  intros S t Ht Hin.
  destruct (wo S) as [Hlo Hmin].
  set {t ∊ A S | λ t, (E S)[t] ∈ (E S)[t]} as B.
  specialize Hmin with B as [t₀ [Ht₀ Hmin]].
  - exists t. apply SepI...
  - intros x Hx. apply SepE1 in Hx...
  - apply SepE in Ht₀ as [Ht₀ Hin₀]. assert (H := Hin₀).
    apply e_elim in H as [s [Hs [Hst₀ [Heq H]]]]...
    assert (Hsb: s ∈ B). { apply SepI... rewrite Heq in H... }
    apply Hmin in Hsb. eapply lo_not_leq_gt...
Qed.

Lemma e_injective : ∀ S, injective (E S).
Proof with eauto; try congruence.
  intros. destruct (wo S) as [Hlo Hmin].
  destruct (e_spec S) as [Hf [Hd _]]...
  split... intros y Hy. split. apply ranE in Hy...
  intros s t Hs Ht.
  apply func_ap in Hs as H1... apply domI in Hs.
  apply func_ap in Ht as H2... apply domI in Ht.
  rewrite <- H2 in H1.
  destruct (classic (s = t))... exfalso.
  eapply lo_connected in H as []...
  - apply e_ap_order in H...
    rewrite H1 in H. eapply e_irrefl...
  - apply e_ap_order in H...
    rewrite H1 in H. eapply e_irrefl...
Qed.

Theorem e_bijective : ∀ S, (E S): A S ⟺ α S.
Proof with auto.
  intros. destruct (e_spec S) as [Hf [Hd _]]...
  apply bijection_is_surjection. split. split...
  apply e_injective...
Qed.

Lemma e_ap_in_α : ∀ S, ∀x ∈ A S, (E S)[x] ∈ α S.
Proof with eauto.
  intros S x Hx. eapply ap_ran...
  apply bijection_is_func. apply e_bijective...
Qed.

Theorem e_preserve_order : ∀ S, ∀ x y ∈ A S,
  (x <ᵣ y) (R S) ↔ ((E S)[x] <ᵣ (E S)[y]) (ε S).
Proof with eauto; try congruence.
  intros S x Hx y Hy.
  destruct (e_spec S) as [Hf [Hd _]]...
  split; intros.
  - apply binRelI. apply e_ap_in_α... apply e_ap_in_α...
    apply e_ap_order...
  - apply binRelE3 in H.
    apply (e_elim S) in H as [u [Hu [Hut [Heq He]]]]...
    apply injectiveE in Heq... apply e_injective...
Qed.

Section ImportOrderedStruct.
Import OrderedStruct.

Let Epsilon := λ S,
  constr (α S) (ε S) (memberRel_is_binRel _).

(* 任意良序结构与其伊普西隆结构同构 *)
Lemma wo_iso_epsilon : ∀ S, parent S ≅ Epsilon S.
Proof with auto.
  intros S. exists (E S). split.
  - apply e_bijective...
  - apply e_preserve_order...
Qed.

(* 任意良序结构的伊普西隆结构也是良序结构 *)
Lemma epsilon_wo : ∀ S, wo (Epsilon S).
Proof.
  intros. eapply iso_wo. apply wo_iso_epsilon. apply parent_wo.
Qed.

End ImportOrderedStruct.

Definition Epsilon := λ S, constr (α S) (ε S) (epsilon_wo S).

(* 任意良序结构与其伊普西隆结构同构 *)
Theorem iso_epsilon : ∀ S, S ≅ Epsilon S.
Proof with auto.
  intros S. exists (E S). split.
  - apply e_bijective...
  - apply e_preserve_order...
Qed.

Theorem α_trans : ∀ S, trans (α S).
Proof with auto; try congruence.
  intros S x y Hxy Hy.
  destruct (e_spec S) as [Hf [Hd _]]...
  apply ranE in Hy as [t Hp]. apply domI in Hp as Ht.
  apply func_ap in Hp... subst y.
  apply e_elim in Hxy as [s [Hs [_ [Heq _]]]]...
  subst x. eapply ranI. apply func_correct...
Qed.

Lemma α_intro : ∀ S t, ∀s ∈ A S, (E S)[s] = t → t ∈ α S.
Proof with auto.
  intros S t s Hs Heqt.
  pose proof (e_spec S) as [Hf [Hd _]].
  apply (ranI _ s). apply func_point... rewrite Hd...
Qed.

Lemma α_elim : ∀ S, ∀t ∈ α S, ∃s ∈ A S, (E S)[s] = t.
Proof with auto.
  intros S t Ht.
  pose proof (e_spec S) as [Hf [Hd _]].
  apply ranE in Ht as [s Hp]. apply domI in Hp as Hs.
  apply func_ap in Hp... exists s. split. congruence. unfold E...
Qed.

Fact ε_iff : ∀ S, ∀ x y,
  (x <ᵣ y) (ε S) ↔ x ∈ α S ∧ y ∈ α S ∧ x ∈ y.
Proof with auto.
  intros S x y. split.
  - intros Hxy. apply binRelE2...
  - intros [Hx [Hy Hxy]]. apply binRelI...
Qed.

Lemma seg_e_ap : ∀ S, ∀t ∈ A S, ∀ s, (s <ᵣ t) (R S) → 
  (E (Seg t S))[s] = (E S)[s].
Proof with eauto.
  intros S t Ht s Hst.
  destruct (wo S) as [[_ [Htr _]] _].
  assert (Hs: s ∈ A S). {
    eapply dom_binRel. apply wo. eapply domI...
  }
  generalize dependent Hst.
  set {x ∊ A S | λ x, (x <ᵣ t) (R S) → (E (Seg t S))[x] = (E S)[x]} as AS'.
  replace (A S) with AS' in Hs. apply SepE2 in Hs... clear Hs s.
  eapply transfinite_induction... split.
  intros s Hs. apply SepE1 in Hs...
  intros s Hs Hsub. apply SepI... intros Hst.
  rewrite e_ap; revgoals... apply SepI...
  apply ExtAx. split; intros Hx.
  - apply ReplAx in Hx as [r [Hr Heqx]]. subst x.
    assert (Hrs: (r <ᵣ s) (R S)). {
      apply SepE in Hr as [_ Hrs]. apply seg_lt in Hrs...
    }
    assert (Hrt: (r <ᵣ t) (R S)). eapply Htr...
    apply seg_of_seg in Hr... apply Hsub in Hr.
    apply SepE in Hr as [Hr IH]. apply IH in Hrt.
    eapply e_intro; revgoals...
  - apply e_elim in Hx as [r [Hr [Hrs [Heqx _]]]]...
    assert (Hr': r ∈ seg s (R S)) by (apply segI; auto).
    assert (Hrt: (r <ᵣ t) (R S)). eapply Htr...
    apply ReplAx. exists r. split. apply seg_of_seg...
    apply Hsub in Hr'. apply SepE in Hr' as [_ IH].
    apply IH in Hrt. congruence.
Qed.

Lemma seg_α : ∀ S, ∀t ∈ A S, α (Seg t S) = (E S)[t].
Proof with eauto.
  intros S t Ht.
  pose proof (e_spec (Seg t S)) as [Hf [Hd _]].
  apply ExtAx. split; intros Hx.
  - apply α_elim in Hx as [s [Hs Hp]].
    apply SepE2 in Hs. subst x. rewrite seg_e_ap...
    apply e_ap_order... eapply dom_binRel. apply wo. eapply domI...
  - apply e_elim in Hx as [s [Hs [Hst [Heqx Hx]]]]...
    apply (α_intro _ _ s). apply SepI... rewrite seg_e_ap...
Qed.

End EpsilonImage.

(* Examples *)
Module Export EpsilonImageOfNats.

Example e_ω_nat : ∀n ∈ ω, (E 𝛚)[n] = n.
Proof with neauto.
  intros n Hn.
  set {n ∊ ω | λ n, (E 𝛚)[n] = n} as N.
  ω_induction N Hn.
  - apply ExtAx. split; intros Hx.
    + apply e_elim in Hx as [k [_ [Hk _]]]...
      apply binRelE3 in Hk. exfalso0.
    + exfalso0.
  - assert (Hmp: m⁺ ∈ ω) by (apply ω_inductive; auto).
    apply ExtAx. split; intros Hx.
    + apply e_elim in Hx as [k [Hk [Hkmp [Heqx Hx]]]]...
      apply binRelE3 in Hkmp.
      apply leq_iff_lt_suc in Hkmp as []...
      * apply BUnionI1. rewrite <- IH.
        eapply e_intro... apply binRelI...
      * apply BUnionI2. subst. rewrite <- IH at 2...
    + apply leq_iff_lt_suc in Hx as []; [| |eapply ω_trans|]...
      * rewrite <- IH in H.
        apply e_elim in H as [k [Hk [Hkm [Heqx Hx]]]]...
        apply binRelE3 in Hkm.
        eapply e_intro... apply binRelI... apply BUnionI1...
      * apply (e_intro 𝛚 x m)... apply binRelI... congruence.
Qed.

Example e_nat_nat : ∀ n m ∈ ω, n ∈ m → (E (Seg m 𝛚))[n] = n.
Proof with neauto.
  intros n Hn p Hp.
  set {n ∊ ω | λ n, n ∈ p → (E (Seg p 𝛚))[n] = n} as N.
  ω_induction N Hn; intros Hnp.
  - apply ExtAx. split; intros Hx; [|exfalso0].
    apply (e_elim (Seg p 𝛚)) in Hx as [k [_ [Hk _]]].
    + apply SepE in Hk as [Hk _].
      apply binRelE3 in Hk. exfalso0.
    + apply SepI... apply binRelI...
  - assert (Hp': p⁺ ∈ ω) by (apply ω_inductive; auto).
    assert (Hm': m⁺ ∈ ω) by (apply ω_inductive; auto).
    assert (Hmp: m ∈ p). { apply (nat_trans p Hp m m⁺)... }
    assert (Hmseg: m ∈ A (Seg p 𝛚)). {
      apply SepI... apply binRelI...
    }
    assert (Hm'seg: m⁺ ∈ A (Seg p 𝛚)). {
      apply SepI... apply binRelI...
    }
    apply ExtAx. split; intros Hx.
    + apply (e_elim (Seg p 𝛚)) in Hx as [k [Hk [Hkm [Heqx Hx]]]]...
      apply SepE in Hkm as [Hkm _].
      apply binRelE2 in Hkm as [Hkw [_ Hkm]].
      apply leq_iff_lt_suc in Hkm as []...
      * apply BUnionI1. rewrite <- IH...
        eapply e_intro... apply seg_lt; apply binRelI...
      * apply BUnionI2. subst. rewrite <- IH at 2...
    + apply leq_iff_lt_suc in Hx as []; [| |eapply ω_trans|]...
      * rewrite <- IH in H...
        apply (e_elim (Seg p 𝛚)) in H as [k [Hk [Hkm [Heqx Hx]]]]...
        apply SepE in Hkm as [Hkm _].
        apply binRelE2 in Hkm as [Hkw [_ Hkm]].
        eapply (e_intro (Seg p 𝛚))...
        apply seg_lt; apply binRelI... apply BUnionI1...
      * apply (e_intro (Seg p 𝛚) x m)...
        apply seg_lt; apply binRelI... rewrite IH...
Qed.

Example α_nat : ∀n ∈ ω, α (Seg n 𝛚) = n.
Proof with neauto; try congruence.
  intros n Hn.
  set {n ∊ ω | λ n, α (Seg n 𝛚) = n} as N.
  ω_induction N Hn.
  - unfold α. replace (E (Seg ∅ 𝛚)) with ∅.
    apply ran_of_empty. symmetry. apply e_empty.
    apply ExtAx. split; intros Hx; [|exfalso0].
    apply SepE2 in Hx. apply binRelE3 in Hx...
  - assert (Hm': m⁺ ∈ ω) by (apply ω_inductive; auto).
    destruct (e_spec (Seg m⁺ 𝛚)) as [Hf [Hd _]]...
    apply ExtAx. intros y. split; intros Hy.
    + apply ranE in Hy as [x Hp]. apply domI in Hp as Hx.
      rewrite Hd in Hx. apply SepE2 in Hx.
      apply binRelE2 in Hx as [Hx [_ Hx']].
      apply func_ap in Hp... rewrite e_nat_nat in Hp...
    + assert (Hyw: y ∈ ω) by (eapply ω_trans; eauto).
      apply (ranI _ y). apply func_point...
      * rewrite Hd. apply SepI... apply binRelI...
      * rewrite seg_e_ap... apply e_ω_nat... apply binRelI...
Qed.

Example α_ω : α 𝛚 = ω.
Proof with auto.
  destruct (e_spec 𝛚) as [Hf [Hd _]].
  apply ExtAx. intros m. split; intros Hm.
  - apply ranE in Hm as [n Hp]. apply domI in Hp as Hn.
    rewrite Hd in Hn. apply func_ap in Hp...
    rewrite e_ω_nat in Hp... subst...
  - apply (ranI _ m). apply func_point...
    rewrite Hd... apply e_ω_nat...
Qed.

End EpsilonImageOfNats.

Import WosetMin.FullVer.

Definition Min := λ S, Min (A S) (R S).

Lemma min_correct : ∀ S B,
  ⦿ B → B ⊆ A S → minimum (Min S)[B] B (R S).
Proof. intros; apply min_correct; auto. Qed.

(* 良序结构的同构关系具有至少三歧性 *)
Theorem wo_iso_at_least_trich : ∀ S T,
  S ≅ T ∨
  (∃t ∈ A T, S ≅ Seg t T) ∨
  (∃t ∈ A S, Seg t S ≅ T).
Proof with eauto; try congruence.
  intros.
  destruct (wo S) as [Hlo HminS]. assert (Hlo' := Hlo).
  destruct Hlo' as [_ [Htr _]].
  destruct (wo T) as [[_ [Htr' _]] _].
  set (Extraneous (A S ∪ A T)) as e.
  set (λ f y, y = match (ixm (⦿ (A T - ran f))) with
    | inl _ => (Min T)[A T - ran f]
    | inr _ => e
  end) as γ.
  set (Recursion S γ) as F.
  pose proof (recrusion_spec_intro S γ) as [HfF [HdF Hγ]]. {
    intros f. split... unfold γ.
    destruct (ixm (⦿ (A T - ran f))).
    - exists ((Min T)[A T - ran f])...
    - exists e...
  }
  fold F in HfF, HdF, Hγ. unfold γ in Hγ.
  assert (HL1: ∀ x y, (x <ᵣ y) (R S) →
    A T - F⟦seg y (R S)⟧ ⊆ A T - F⟦seg x (R S)⟧
  ). {
    intros x y Hxy. intros b Hb.
    apply SepE in Hb as [Hb Hb'].
    apply SepI... intros Hb''. apply Hb'.
    apply imgE in Hb'' as [t [Htx Hp]].
    eapply imgI... apply SepE in Htx as [_ Htx].
    apply segI. eapply Htr...
  }
  (* Case I *)
  destruct (classic (e ∈ ran F)) as [He|He]. {
    right; right.
    set {x ∊ A S | λ x, F[x] = e} as B.
    specialize HminS with B as [a [Ha HminS]]. {
      apply ranE in He as [a Hp]. apply domI in Hp as Ha.
      apply func_ap in Hp... exists a. apply SepI...
    } {
      intros b Hb. apply SepE1 in Hb...
    }
    assert (HL2: ∀ x y ∈ A S, (x <ᵣ y) (R S) → (y <ᵣ a) (R S) →
      (F[x] <ᵣ F[y]) (R T)
    ). {
      intros x Hx y Hy Hxy Hya. rewrite Hγ, Hγ...
      set (A T - ran (F ↾ seg x (R S))) as C.
      set (A T - ran (F ↾ seg y (R S))) as D.
      apply Hγ in Hx as HFx. fold C in HFx.
      apply Hγ in Hy as HFy. fold D in HFy.
      destruct (ixm (⦿ C)); destruct (ixm (⦿ D)).
      + pose proof (min_correct T C) as [_ Hmin]...
          { intros c Hc. apply SepE1 in Hc... }
        pose proof (min_correct T D) as [Hmd _]...
          { intros d Hd. apply SepE1 in Hd... }
        assert (Hmc: (Min T)[D] ∈ C). { eapply HL1... }
        apply Hmin in Hmc as []... exfalso.
        rewrite <- H, <- HFx in Hmd. apply SepE2 in Hmd.
        apply Hmd. eapply ranI. apply restrI.
        apply segI... apply func_correct...
      + exfalso. assert (y ∈ B). apply SepI...
        apply HminS in H. eapply lo_not_leq_gt...
      + exfalso. assert (x ∈ B). apply SepI...
        apply HminS in H as []; subst; eapply lo_irrefl...
      + exfalso. assert (x ∈ B). apply SepI...
        apply HminS in H as []; subst; eapply lo_irrefl...
    }
    set (F ↾ seg a (R S)) as Fᵒ.
    apply SepE1 in Ha as Haa.
    exists a. split... exists Fᵒ. split; [split; split|].
    - apply restr_func...
    - intros b Hb. split. apply ranE in Hb...
      intros x y Hpx Hpy.
      apply restrE2 in Hpx as [Hpx Hx]. apply func_ap in Hpx...
      apply restrE2 in Hpy as [Hpy Hy]. apply func_ap in Hpy...
      apply SepE in Hx as [Hx Hxa].
      apply SepE in Hy as [Hy Hya].
      eapply dom_binRel in Hx; [|apply wo].
      eapply dom_binRel in Hy; [|apply wo].
      destruct (classic (x = y))... exfalso.
      eapply lo_connected in H as []; eauto;
      (eapply lo_irrefl; [apply (wo T)|]).
      + apply (HL2 _ Hx _ Hy) in Hya... rewrite Hpx, Hpy in Hya...
      + apply (HL2 _ Hy _ Hx) in Hxa... rewrite Hpx, Hpy in Hxa...
    - unfold Fᵒ. rewrite <- seg_a_eq... apply restr_dom...
      intros x Hx. apply SepE1 in Hx...
    - apply sub_antisym.
      + intros y Hy. apply ranE in Hy as [x Hp].
        apply restrE2 in Hp as [Hp Hx].
        apply SepE in Hx as [Hx Hxa].
        eapply dom_binRel in Hx; [|apply wo].
        apply func_ap in Hp... subst y.
        apply Hγ in Hx as Hap. rewrite Hap.
        set (A T - ran (F ↾ seg x (R S))) as C. fold C in Hap.
        destruct (ixm (⦿ C)).
        * pose proof (min_correct T C) as [Hm _]...
          intros c Hc. apply SepE1 in Hc... apply SepE1 in Hm...
        * exfalso. assert (x ∈ B). apply SepI...
          apply HminS in H. eapply lo_not_leq_gt...
      + apply sub_iff_no_comp.
        destruct (classic (A T - ran Fᵒ = ∅))...
        exfalso. apply EmptyNE in H.
        apply Hγ in Haa. fold Fᵒ in Haa.
        destruct (ixm (⦿ (A T - ran Fᵒ)))...
        assert (Hm: (Min T)[A T - ran Fᵒ] ∈ A T - ran Fᵒ). apply min_correct...
        apply SepE1 in Hm. apply SepE2 in Ha.
        apply (extraneous (A S ∪ A T)). fold e. apply BUnionI2...
    - intros x Hx y Hy.
      apply SepE in Hx as [Hx Hxa].
      apply SepE in Hy as [Hy Hya].
      replace (Fᵒ[x]) with (F[x]).
      replace (Fᵒ[y]) with (F[y]).
      + split; intros Hxy.
        apply HL2... apply SepE1 in Hxy...
        destruct (classic (x = y)).
        * exfalso. subst. 
          eapply lo_irrefl. apply (wo T). apply Hxy.
        * apply SepI; [|apply CProdI; apply SepI]...
          eapply lo_connected in H as []... exfalso.
          eapply lo_irrefl. apply (wo T).
          eapply Htr'... apply HL2...
      + symmetry. apply func_ap. apply restr_func...
        apply restrI. apply segI... apply func_correct...
      + symmetry. apply func_ap. apply restr_func...
        apply restrI. apply segI... apply func_correct...
  }
  (* End of Case I *)
  (* Lemma for Case II & III *)
  assert (HL2: ∀ x y ∈ A S, (x <ᵣ y) (R S) →
    (F[x] <ᵣ F[y]) (R T)
  ). {
    intros x Hx y Hy Hxy. rewrite Hγ, Hγ...
    set (A T - ran (F ↾ seg x (R S))) as C.
    set (A T - ran (F ↾ seg y (R S))) as D.
    apply Hγ in Hx as HFx. fold C in HFx.
    apply Hγ in Hy as HFy. fold D in HFy.
    destruct (ixm (⦿ C)); destruct (ixm (⦿ D)).
    + pose proof (min_correct T C) as [_ Hmin]...
        { intros c Hc. apply SepE1 in Hc... }
      pose proof (min_correct T D) as [Hmd _]...
        { intros d Hd. apply SepE1 in Hd... }
      assert (Hmc: (Min T)[D] ∈ C). { eapply HL1... }
      apply Hmin in Hmc as []... exfalso.
      rewrite <- H in Hmd. apply SepE2 in Hmd.
      apply Hmd. eapply ranI. apply restrI.
      apply segI... apply func_point...
    + exfalso. apply He. rewrite <- HFy.
      eapply ranI. apply func_correct...
    + exfalso. apply He. rewrite <- HFx.
      eapply ranI. apply func_correct...
    + exfalso. apply He. rewrite <- HFx.
      eapply ranI. apply func_correct...
  }
  (* Case II *)
  destruct (classic (ran F = A T)) as [Hr|Hnq]. {
    left.
    exists F. split; [split; split|]...
    - intros b Hb. split. apply ranE in Hb...
      intros x y Hpx Hpy.
      apply domI in Hpx as Hx. apply func_ap in Hpx...
      apply domI in Hpy as Hy. apply func_ap in Hpy...
      rewrite HdF in Hx, Hy.
      destruct (classic (x = y))... exfalso.
      eapply lo_connected in H as []; eauto;
      (eapply lo_irrefl; [apply (wo T)|]).
      + apply (HL2 _ Hx _ Hy) in H... rewrite Hpx, Hpy in H...
      + apply (HL2 _ Hy _ Hx) in H... rewrite Hpx, Hpy in H...
    - intros x Hx y Hy. split; intros Hxy. apply HL2...
      destruct (classic (x = y)).
      + exfalso. subst. 
        eapply lo_irrefl. apply (wo T). apply Hxy.
      + eapply lo_connected in H as []... exfalso.
        eapply lo_irrefl. apply (wo T).
        eapply Htr'... apply HL2...
  }
  (* Case III *)
  right; left.
  assert (Hsub: ran F ⊆ A T). {
    intros y Hy.
    apply ranE in Hy as [x Hp]. apply domI in Hp as Hx.
    apply func_ap in Hp as Hap... rewrite Hγ in Hap...
    set (A T - ran (F ↾ seg x (R S))) as B. fold B in Hap.
    destruct (ixm (⦿ B)).
    - assert ((Min T)[B] ∈ B). {
        apply min_correct...
        intros b Hb. apply SepE1 in Hb...
      }
      apply SepE1 in H...
    - exfalso. apply He. apply (ranI _ x)...
  }
  assert (Hpsub: ran F ⊂ A T) by (split; auto).
  apply comp_nonempty in Hpsub.
  set ((Min T)[A T - ran F]) as b.
  pose proof (min_correct T (A T -ran F)) as [Hm Hminb]...
  fold b in Hm, Hminb.
  assert (Hr: ran F = A (Seg b T)). {
    apply sub_antisym; intros y Hy.
    - destruct (wo T) as [Hlo' _].
      apply SepE in Hm as [Hb1 Hb2]. apply Hsub in Hy as Hyt.
      apply SepI... destruct (classic (y = b)). subst...
      apply (lo_connected (R T) (A T)) in H as []...
      exfalso. apply ranE in Hy as [x Hp]. apply domI in Hp as Hx.
      apply func_ap in Hp... rewrite Hγ in Hp...
      set (A T - ran (F ↾ seg x (R S))) as C. fold C in Hp.
      destruct (ixm (⦿ C)); subst y.
      + pose proof (min_correct T C) as [Hm Hminc]...
        intros c Hc. apply SepE1 in Hc...
        assert (Hb: b ∈ C). {
          apply SepI... intros Hb'. apply restr_ran_included in Hb'...
        }
        apply Hminc in Hb as [];
        (eapply lo_irrefl; [apply (wo T)|])...
        rewrite H0 in H...
      + assert (e ∈ A S ∪ A T) by (apply BUnionI2; auto).
        eapply extraneous...
    - apply SepE in Hy as [Hy Hyb].
      destruct (classic (y ∈ ran F)) as [|Hy']... exfalso.
      assert (y ∈ A T - ran F) by (apply SepI; auto).
      apply Hminb in H as []; subst;
      (eapply lo_irrefl; [apply (wo T)|])...
  }
  exists b. split. apply SepE1 in Hm...
  exists F. split; [split; split|]...
  - intros c Hc. split. apply ranE in Hc...
    intros x y Hpx Hpy.
    apply domI in Hpx as Hx. apply func_ap in Hpx...
    apply domI in Hpy as Hy. apply func_ap in Hpy...
    rewrite HdF in Hx, Hy.
    destruct (classic (x = y))... exfalso.
    eapply lo_connected in H as []; eauto;
    (eapply lo_irrefl; [apply (wo T)|]).
    + apply (HL2 _ Hx _ Hy) in H... rewrite Hpx, Hpy in H...
    + apply (HL2 _ Hy _ Hx) in H... rewrite Hpx, Hpy in H...
  - intros x Hx y Hy. split; intros Hxy.
    + apply SepI. apply HL2...
      rewrite <- HdF in Hx, Hy.
      apply func_correct in Hx... apply ranI in Hx.
      apply func_correct in Hy... apply ranI in Hy.
      apply CProdI; (apply SepI; [apply Hsub|])...
      * rewrite Hr in Hx. apply SepE2 in Hx...
      * rewrite Hr in Hy. apply SepE2 in Hy...
    + apply SepE1 in Hxy.
      destruct (classic (x = y)).
      * exfalso. subst.
        eapply lo_irrefl. apply (wo T). apply Hxy.
      * eapply lo_connected in H as []... exfalso.
        eapply lo_irrefl. apply (wo T).
        eapply Htr'... apply HL2...
Qed.

End WoStruct.
