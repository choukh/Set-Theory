(** Based on "Elements of Set Theory" Chapter 7 Part 3 **)
(** Coq coding by choukh, Dec 2020 **)

Require Export ZFC.EST7_2.
Require Import ZFC.lib.FuncFacts.
Require Import ZFC.lib.WosetMin.

(*** EST第七章3：伊普西隆像，序同构，良序结构 ***)

(* 保序映射 *)
Definition order_preserved_func := λ A R f S,
  ∀ x y ∈ A, (x <ᵣ y) R ↔ (f[x] <ᵣ f[y]) S.

(* 伊普西隆像 *)
Module EpsilonImage.
Import TransfiniteRecursion.

Definition γ := λ x y, y = ran x.
Definition E := λ A R, constr A R γ.
Definition α := λ A R, ran (E A R).
Definition ε := λ A R, MemberRel (α A R).

Lemma e_spec : ∀ A R, woset A R → spec A R γ (E A R).
Proof.
  intros. apply spec_intro. apply H.
  intros f. split. exists (ran f). congruence. congruence.
Qed.

Lemma e_empty : ∀ R, E ∅ (R ⥏ ∅) = ∅.
Proof with auto.
  intros. rewrite subRel_empty.
  destruct (e_spec ∅ ∅) as [Hf [Hd _]].
  apply empty_woset. apply empty_dom...
Qed.

Lemma e_ap : ∀ A R, woset A R →
  ∀t ∈ A, (E A R)[t] = {λ x, (E A R)[x] | x ∊ seg t R}.
Proof with eauto.
  intros A R Hwo t Ht.
  destruct (e_spec A R Hwo) as [Hf [Hd Hγ]].
  apply Hγ in Ht. rewrite Ht.
  apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [x Hp]. apply restrE2 in Hp as [Hp Hx].
    apply ReplAx. exists x. split... apply func_ap in Hp...
  - apply ReplAx in Hy as [x [Hx Hap]].
    apply (ranI _ x). apply restrI... apply func_point...
    rewrite Hd. apply SepE in Hx as [Hx _].
    eapply dom_binRel... destruct Hwo as [[] _]...
Qed.

Lemma e_ap_order : ∀ A R, woset A R →
  ∀ s t ∈ A, (s <ᵣ t) R → (E A R)[s] ∈ (E A R)[t].
Proof with auto.
  intros A R Hwo s Hs t Ht Hst.
  rewrite (e_ap A R Hwo t Ht).
  apply ReplAx. exists s. split... apply segI...
Qed.

Lemma e_intro : ∀ A R, woset A R →
  ∀ x, ∀ s t ∈ A, (s <ᵣ t) R → x = (E A R)[s] →
  x ∈ (E A R)[t].
Proof with auto.
  intros A R Hwo x s Hs t Ht Hst Hest. subst.
  apply e_ap_order...
Qed.

Lemma e_elim : ∀ A R, woset A R →
  ∀t ∈ A, ∀x ∈ (E A R)[t],
  ∃s ∈ A, (s <ᵣ t) R ∧ x = (E A R)[s] ∧ x ∈ (E A R)[t].
Proof with auto.
  intros A R Hwo t Ht x Hx.
  assert (H := Hx). rewrite e_ap in H...
  apply ReplAx in H as [s [Hs Heq]].
  apply SepE in Hs as [Hs Hst].
  eapply dom_binRel in Hs; [|apply Hwo].
  exists s. split...
Qed.

Theorem e_irrefl : ∀ A R, woset A R →
  ∀t ∈ A, (E A R)[t] ∉ (E A R)[t].
Proof with eauto.
  intros A R Hwo t Ht Hin.
  assert (H := Hwo). destruct H as [Hlo Hmin].
  assert (H := Hlo). destruct H as [Hbr [Htr _]].
  set {t ∊ A | λ t, (E A R)[t] ∈ (E A R)[t]} as B.
  specialize Hmin with B as [t₀ [Ht₀ Hmin]].
  - exists t. apply SepI...
  - intros x Hx. apply SepE1 in Hx...
  - apply SepE in Ht₀ as [Ht₀ Hin₀]. assert (H := Hin₀).
    apply (e_elim A R) in H as [s [Hs [Hst₀ [Heq H]]]]...
    assert (Hsb: s ∈ B). { apply SepI... rewrite Heq in H... }
    apply Hmin in Hsb as []. eapply linearOrder_irrefl...
    subst. eapply linearOrder_irrefl...
Qed.

Lemma e_injective : ∀ A R, woset A R → injective (E A R).
Proof with eauto; try congruence.
  intros A R Hwo.
  assert (H := Hwo). destruct H as [Hlo Hmin].
  destruct (e_spec A R) as [Hf [Hd _]]...
  split... intros y Hy. split. apply ranE in Hy...
  intros s t Hs Ht.
  apply func_ap in Hs as H1... apply domI in Hs.
  apply func_ap in Ht as H2... apply domI in Ht.
  rewrite <- H2 in H1.
  destruct (classic (s = t))... exfalso.
  eapply linearOrder_connected in H as []...
  - apply (e_ap_order A R) in H...
    rewrite H1 in H. eapply e_irrefl...
  - apply (e_ap_order A R) in H...
    rewrite H1 in H. eapply e_irrefl...
Qed.

Theorem e_bijective : ∀ A R, woset A R → (E A R): A ⟺ (α A R).
Proof with auto.
  intros A R Hwo.
  destruct (e_spec A R) as [Hf [Hd _]]...
  apply bijection_is_surjection. split. split...
  apply e_injective...
Qed.

Lemma e_ap_in_α : ∀ A R, woset A R → ∀x ∈ A, (E A R)[x] ∈ α A R.
Proof with eauto.
  intros A R Hwo x Hx. eapply ap_ran...
  apply bijection_is_func. apply e_bijective...
Qed.

Theorem e_preserve_order : ∀ A R, woset A R →
  order_preserved_func A R (E A R) (ε A R).
Proof with eauto; try congruence.
  intros A R Hwo s Hs t Ht.
  destruct (e_spec A R) as [Hf [Hd _]]...
  split; intros.
  - apply binRelI. apply e_ap_in_α... apply e_ap_in_α...
    apply e_ap_order...
  - apply binRelE2 in H as [_ [_ H]].
    apply (e_elim A R Hwo) in H as [u [Hu [Hut [Heq He]]]]...
    apply injectiveE in Heq... apply e_injective...
Qed.

Theorem α_trans : ∀ A R, woset A R → trans (α A R).
Proof with auto; try congruence.
  intros A R Hwo x y Hxy Hy.
  destruct (e_spec A R) as [Hf [Hd _]]...
  apply ranE in Hy as [t Hp]. apply domI in Hp as Ht.
  apply func_ap in Hp... subst y.
  apply (e_elim A R Hwo) in Hxy as [s [Hs [_ [Heq _]]]]...
  subst x. eapply ranI. apply func_correct...
Qed.

Fact ε_iff : ∀ A R, woset A R →
  ∀ x y, (x <ᵣ y) (ε A R) ↔ x ∈ α A R ∧ y ∈ α A R ∧ x ∈ y.
Proof with auto.
  intros A R Hwo x y. split.
  - intros Hxy. apply binRelE2...
  - intros [Hx [Hy Hxy]]. apply binRelI...
Qed.

Example e_ω_nat : ∀n ∈ ω, (E ω Lt)[n] = n.
Proof with neauto.
  intros n Hn.
  pose proof Lt_wellOrder as Hwo.
  set {n ∊ ω | λ n, (E ω Lt)[n] = n} as N.
  ω_induction N Hn.
  - apply ExtAx. split; intros Hx.
    + apply (e_elim ω Lt Hwo) in Hx as [k [_ [Hk _]]]...
      apply binRelE2 in Hk as [_ [_ Hk]]. exfalso0.
    + exfalso0.
  - assert (Hmp: m⁺ ∈ ω) by (apply ω_inductive; auto).
    apply ExtAx. split; intros Hx.
    + apply (e_elim ω Lt Hwo) in Hx as [k [Hk [Hkmp [Heqx Hx]]]]...
      apply binRelE2 in Hkmp as [_ [_ Hkmp]].
      apply leq_iff_lt_suc in Hkmp as []...
      * apply BUnionI1. rewrite <- IH.
        eapply e_intro... apply binRelI...
      * apply BUnionI2. subst. rewrite <- IH at 2...
    + apply leq_iff_lt_suc in Hx as []; [| |eapply ω_trans|]...
      * rewrite <- IH in H.
        apply (e_elim ω Lt Hwo) in H as [k [Hk [Hkm [Heqx Hx]]]]...
        apply binRelE2 in Hkm as [_ [_ Hkm]].
        apply (e_intro ω Lt Hwo x k)...
        apply binRelI... apply BUnionI1...
      * apply (e_intro ω Lt Hwo x m)...
        apply binRelI... congruence.
Qed.

Example e_nat_nat : ∀ n m ∈ ω, n ∈ m → (E m (Lt ⥏ m))[n] = n.
Proof with neauto.
  intros n Hn p Hp.
  pose proof (nat_woset p Hp) as Hwo.
  set {n ∊ ω | λ n, n ∈ p → (E p (Lt ⥏ p))[n] = n} as N.
  ω_induction N Hn; intros Hnp.
  - apply ExtAx. split; intros Hx.
    + apply (e_elim p (Lt ⥏ p) Hwo) in Hx as [k [_ [Hk _]]]...
      apply SepE in Hk as [Hk _].
      apply binRelE2 in Hk as [_ [_ Hk]]. exfalso0.
    + exfalso0.
  - assert (Hp': p⁺ ∈ ω) by (apply ω_inductive; auto).
    assert (Hm': m⁺ ∈ ω) by (apply ω_inductive; auto).
    assert (Hmp: m ∈ p). { apply (nat_trans p Hp m m⁺)... }
    apply ExtAx. split; intros Hx.
    + apply (e_elim p (Lt ⥏ p) Hwo) in Hx as [k [Hk [Hkm [Heqx Hx]]]]...
      apply SepE in Hkm as [Hkm _].
      apply binRelE2 in Hkm as [Hkw [_ Hkm]].
      apply leq_iff_lt_suc in Hkm as []...
      * apply BUnionI1. rewrite <- IH...
        eapply e_intro... apply SepI.
        apply binRelI... apply CProdI...
      * apply BUnionI2. subst. rewrite <- IH at 2...
    + apply leq_iff_lt_suc in Hx as []; [| |eapply ω_trans|]...
      * rewrite <- IH in H...
        apply (e_elim p (Lt ⥏ p) Hwo) in H as [k [Hk [Hkm [Heqx Hx]]]]...
        apply SepE in Hkm as [Hkm _].
        apply binRelE2 in Hkm as [Hkw [_ Hkm]].
        apply (e_intro p (Lt ⥏ p) Hwo x k)...
        apply SepI. apply binRelI...
        apply BUnionI1... apply CProdI...
      * apply (e_intro p (Lt ⥏ p) Hwo x m)...
        apply SepI. apply binRelI... apply CProdI... rewrite IH...
Qed.

Example α_nat : ∀n ∈ ω, α n (Lt ⥏ n) = n.
Proof with neauto; try congruence.
  intros n Hn.
  set {n ∊ ω | λ n, α n (Lt ⥏ n) = n} as N.
  ω_induction N Hn.
  - unfold α. replace (E ∅ (Lt ⥏ ∅)) with ∅.
    apply ran_of_empty.
    apply ExtAx. split; intros Hx. exfalso0.
    rewrite e_empty in Hx. exfalso0.
  - assert (Hm': m⁺ ∈ ω) by (apply ω_inductive; auto).
    destruct (e_spec m⁺ (Lt ⥏ m⁺)) as [Hf' [Hd' _]]...
      { apply nat_woset... }
    apply ExtAx. intros y. split; intros Hy.
    + apply ranE in Hy as [x Hp]. apply domI in Hp as Hx.
      apply func_ap in Hp... rewrite e_nat_nat in Hp...
      eapply ω_trans. apply Hx. congruence.
    + apply (ranI _ y). apply func_point...
      rewrite e_nat_nat... eapply ω_trans...
Qed.

Example α_ω : α ω Lt = ω.
Proof with auto; try congruence.
  destruct (e_spec ω Lt) as [Hf [Hd _]]. apply Lt_wellOrder.
  apply ExtAx. intros m. split; intros Hm.
  - apply ranE in Hm as [n Hp]. apply domI in Hp as Hn.
    apply func_ap in Hp... rewrite e_ω_nat in Hp...
  - apply (ranI _ m). apply func_point... apply e_ω_nat...
Qed.

End EpsilonImage.

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
    apply binRelE2 in Hxx as [_ [_ Hxx]]. eapply Hir...
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
    apply SepI... apply CProdI... zfcrewrite.
    rewrite ident_ap, ident_ap...
  - apply SepE in Hx as [Hp Hlt].
    apply CProdE1 in Hp as [a [Ha [b [Hb Heq]]]]. subst x.
    zfcrewrite. rewrite ident_ap, ident_ap in Hlt...
    apply SepI... apply CProdI...
Qed.

End ImageRel.

(* 序结构 *)
Module OrderedStruct.

Record OrderedStruct : Type := constr {
  A : set;
  R : set;
  ordered_struct : is_binRel R A;
}.

Definition po := λ S, poset (A S) (R S).
Definition lo := λ S, loset (A S) (R S).
Definition wo := λ S, woset (A S) (R S).

(* 序同构 *)
Definition isomorphic := λ S T,
  ∃ f, f: A S ⟺ A T ∧ order_preserved_func (A S) (R S) f (R T).

Notation "S ≅ T" := (isomorphic S T) (at level 60).

Theorem iso_refl : ∀ S, S ≅ S.
Proof with auto.
  intros. exists (Ident (A S)).
  split. apply ident_bijective.
  intros x Hx y Hy. rewrite ident_ap, ident_ap... reflexivity.
Qed.

Theorem iso_symm : ∀ S T, S ≅ T → T ≅ S.
Proof with eauto.
  intros * [f [Hf H]]. exists (f⁻¹).
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

Theorem iso_tran : ∀ S T U, S ≅ T → T ≅ U → S ≅ U.
Proof with eauto; try congruence.
  intros * [f [Hf H1]] [g [Hg H2]]. exists (g ∘ f).
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
Add Relation OrderedStruct isomorphic
  reflexivity proved by iso_refl
  symmetry proved by iso_symm
  transitivity proved by iso_tran
  as iso_rel.

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

Import EpsilonImage.

Definition E := λ S, E (A S) (R S).
Definition α := λ S, α (A S) (R S).
Definition ε := λ S, ε (A S) (R S).
Definition Epsilon := λ S,
  constr (α S) (ε S) (memberRel_is_binRel _).

(* 任意良序结构与其伊普西隆结构同构 *)
Fact wo_iso_epsilon : ∀ S, wo S → S ≅ Epsilon S.
Proof with auto.
  intros S Hwo. exists (E S). split.
  - apply e_bijective...
  - apply e_preserve_order...
Qed.

(* 任意良序结构的伊普西隆像是传递集 *)
Corollary α_trans : ∀ S, wo S → trans (α S).
Proof. intros. apply α_trans. apply H. Qed.

(* 任意良序结构的伊普西隆结构也是良序结构 *)
Corollary epsilon_wo : ∀ S, wo S → wo (Epsilon S).
Proof with eauto.
  intros. eapply iso_wo... apply wo_iso_epsilon...
Qed.

End OrderedStruct.

(* 良序结构 *)
Module WOStruct.

Record WOStruct : Type := constr {
  A : set;
  R : set;
  wo : woset A R;
}.
Hint Immediate wo : core.

Definition isomorphic := λ S T,
  ∃ f, f: A S ⟺ A T ∧ order_preserved_func (A S) (R S) f (R T).

Notation "S ≅ T" := (isomorphic S T) (at level 60).

Module Import Inheritance.

Local Lemma woset_is_binRel : ∀ A R, woset A R → is_binRel R A.
Proof. intros. apply H. Qed.

Local Definition br := λ S, woset_is_binRel (A S) (R S) (wo S).
Definition parent := λ S, OrderedStruct.constr (A S) (R S) (br S).

Lemma parent_iso : ∀ S T,
  S ≅ T ↔ OrderedStruct.isomorphic (parent S) (parent T).
Proof.
  split; intros [f [Hf Hopf]]; exists f; split; auto.
Qed.

Lemma parent_wo : ∀ S, OrderedStruct.wo (parent S).
Proof. intros. apply wo. Qed.

End Inheritance.

Theorem iso_refl : ∀ S, S ≅ S.
Proof.
  intros. apply parent_iso. apply OrderedStruct.iso_refl.
Qed.

Theorem iso_symm : ∀ S T, S ≅ T → T ≅ S.
Proof.
  intros. rewrite parent_iso in H. apply parent_iso.
  apply OrderedStruct.iso_symm; auto.
Qed.

Theorem iso_tran : ∀ S T U, S ≅ T → T ≅ U → S ≅ U.
Proof.
  intros * H1 H2. rewrite parent_iso in H1, H2.
  apply parent_iso. eapply OrderedStruct.iso_tran; eauto.
Qed.

Add Relation WOStruct isomorphic
  reflexivity proved by iso_refl
  symmetry proved by iso_symm
  transitivity proved by iso_tran
  as iso_rel.

(* 良序结构间的态射唯一 *)
Theorem wo_iso_unique : ∀ S T, S ≅ T →
  ∃! f, f: A S ⟺ A T ∧ order_preserved_func (A S) (R S) f (R T).
Proof with eauto; try congruence.
  intros S T Hiso. split...
  intros f g [Hf H1] [Hg H2].
  pose proof (wo S) as Hwo.
  pose proof (wo T) as Hwo'.
  cut (∀ f g A R B S, woset A R → woset B S →
    f: A ⟺ B → order_preserved_func A R f S →
    g: A ⟺ B → order_preserved_func A R g S → f ⊆ g
  ). {
    intros Lemma. apply sub_antisym; eapply Lemma; revgoals...
  }
  clear Hwo Hwo' Hiso Hf H1 Hg H2 f g S T.
  intros f g A R B S Hwor Hwos Hf Hopf Hg Hopg p Hp.
  destruct Hwos as [Hlo Hmin].
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
  set {x ∊ A | λ x, f[x] = g[x]} as A'.
  replace A with A' in Hx. {
    apply SepE in Hx as [Hx Heq].
    apply func_ap in Hp... apply func_point...
  }
  eapply transfinite_induction...
  split. intros a Ha. apply SepE1 in Ha...
  intros t Ht Hsub. apply SepI...
  destruct (classic (f[t] = g[t]))... exfalso.
  apply (linearOrder_connected S B) in H as []; revgoals...
  eapply ap_ran... eapply ap_ran...
  - assert (Hgt: g[t] ∈ ran f). {
      rewrite Hrf, <- Hrg. eapply ranI. apply func_correct...
    }
    rewrite <- (inv_ran_reduction f Hif (g[t])) in H...
    apply Hopf in H; revgoals... { eapply ap_ran... }
    remember (f⁻¹[g[t]]) as t'.
    assert (Ht': t' ∈ seg t R) by (apply segI; auto).
    apply Hsub in Ht'. apply SepE in Ht' as [Ht' Heq].
    rewrite Heqt' in Heq at 1.
    rewrite inv_ran_reduction in Heq...
    eapply injectiveE in Heq... rewrite Heq in H.
    eapply (linearOrder_irrefl R A)... apply Hwor.
  - assert (Hft: f[t] ∈ ran g). {
      rewrite Hrg, <- Hrf. eapply ranI. apply func_correct...
    }
    rewrite <- (inv_ran_reduction g Hig (f[t])) in H...
    apply Hopg in H; revgoals... { eapply ap_ran... }
    remember (g⁻¹[f[t]]) as t'.
    assert (Ht': t' ∈ seg t R) by (apply segI; auto).
    apply Hsub in Ht'. apply SepE in Ht' as [Ht' Heq].
    rewrite Heqt' in Heq at 2.
    rewrite inv_ran_reduction in Heq...
    eapply injectiveE in Heq... rewrite Heq in H.
    eapply (linearOrder_irrefl R A)... apply Hwor.
Qed.

Import EpsilonImage.

Definition E := λ S, E (A S) (R S).
Definition α := λ S, α (A S) (R S).
Definition ε := λ S, ε (A S) (R S).
Definition Epsilon := λ S,
  constr (α S) (ε S) (OrderedStruct.epsilon_wo (parent S) (parent_wo S)).

(* 任意良序结构与其伊普西隆结构同构 *)
Fact iso_epsilon : ∀ S, S ≅ Epsilon S.
Proof with auto.
  intros S. exists (E S). split.
  - apply e_bijective...
  - apply e_preserve_order...
Qed.

(* 任意良序结构的伊普西隆像是传递集 *)
Corollary α_trans : ∀ S, trans (α S).
Proof. intros. apply α_trans. auto. Qed.

Lemma e_spec : ∀ S, TransfiniteRecursion.spec (A S) (R S) γ (E S).
Proof. intros. apply e_spec. apply wo. Qed.

Lemma e_ap : ∀ S,
  ∀t ∈ A S, (E S)[t] = {λ x, (E S)[x] | x ∊ seg t (R S)}.
Proof. intros S t Ht. unfold E. rewrite e_ap; auto. Qed.

Lemma e_ap_order : ∀ S,
  ∀ s t ∈ A S, (s <ᵣ t) (R S) → (E S)[s] ∈ (E S)[t].
Proof. intros S s Hs t Ht Hst. apply e_ap_order; auto. Qed.

Lemma e_intro : ∀ S x, ∀ s t ∈ A S,
  (s <ᵣ t) (R S) → x = (E S)[s] → x ∈ (E S)[t].
Proof.
  intros S x s Hs t Ht Hst Heqx.
  eapply e_intro; revgoals; eauto.
Qed.

Lemma e_elim : ∀ S,
  ∀t ∈ A S, ∀x ∈ (E S)[t],
  ∃s ∈ A S, (s <ᵣ t) (R S) ∧ x = (E S)[s] ∧ x ∈ (E S)[t].
Proof.
  intros S t Ht x Hx.
  apply (e_elim (A S) (R S) (wo S)) in Hx; auto.
Qed.

Lemma α_intro : ∀ S t, ∀s ∈ A S, (E S)[s] = t → t ∈ α S.
Proof with auto.
  intros S t s Hs Heqt.
  pose proof (EpsilonImage.e_spec (A S) (R S) (wo S)) as [Hf [Hd _]].
  apply (ranI _ s). apply func_point... rewrite Hd...
Qed.

Lemma α_elim : ∀ S, ∀t ∈ α S, ∃s ∈ A S, (E S)[s] = t.
Proof with auto.
  intros S t Ht.
  pose proof (EpsilonImage.e_spec (A S) (R S) (wo S)) as [Hf [Hd _]].
  apply ranE in Ht as [s Hp]. apply domI in Hp as Hs.
  apply func_ap in Hp... exists s. split. congruence. unfold E...
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

Lemma seg_r_eq : ∀ S r s t, (s <ᵣ t) (R S) →
  (r <ᵣ s) (R (Seg t S)) ↔ (r <ᵣ s) (R S).
Proof with eauto.
  intros S r s t Hst. split; intros Hlt.
  - apply SepE1 in Hlt...
  - apply SepI... apply CProdI; apply SepI...
    eapply dom_binRel. apply wo. eapply domI...
    destruct (wo S) as [[_ [Htr _]] _]. eapply Htr...
    eapply dom_binRel. apply wo. eapply domI...
Qed.

Lemma seg_seg_eq : ∀ S r s t, (s <ᵣ t) (R S) →
  r ∈ seg s (R (Seg t S)) ↔ r ∈ seg s (R S).
Proof with auto.
  intros S r s t Hst. split; intros Hlt.
  - apply SepE2 in Hlt. apply seg_r_eq in Hlt... apply segI...
  - apply segI. apply seg_r_eq... apply SepE2 in Hlt...
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
  rewrite e_ap; revgoals... {
    rewrite seg_a_eq... apply segI...
  }
  apply ExtAx. split; intros Hx.
  - apply ReplAx in Hx as [r [Hr Heqx]]. subst x.
    assert (Hrs: (r <ᵣ s) (R S)). {
      apply SepE in Hr as [_ Hrs]. apply seg_r_eq in Hrs...
    }
    assert (Hrt: (r <ᵣ t) (R S)). eapply Htr...
    apply seg_seg_eq in Hr... apply Hsub in Hr.
    apply SepE in Hr as [Hr IH]. apply IH in Hrt.
    eapply e_intro; revgoals...
  - apply e_elim in Hx as [r [Hr [Hrs [Heqx _]]]]...
    assert (Hr': r ∈ seg s (R S)) by (apply segI; auto).
    assert (Hrt: (r <ᵣ t) (R S)). eapply Htr...
    apply ReplAx. exists r. split. apply seg_seg_eq...
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
    apply (α_intro _ _ s). rewrite seg_a_eq...
    apply segI... rewrite seg_e_ap...
Qed.

Import TransfiniteRecursion.
Import WosetMin.FullVer.

(* 良序结构的同构关系具有三歧性 *)
Theorem wo_iso_trich : ∀ S T,
  S ≅ T ∨
  (∃t ∈ A T, S ≅ Seg t T) ∨
  (∃t ∈ A S, Seg t S ≅ T).
Proof with eauto; try congruence.
  intros.
  destruct (wo S) as [Hlo HminS]. assert (Hlo' := Hlo).
  destruct Hlo' as [_ [Htr _]].
  destruct (wo T) as [[_ [Htr' _]] _].
  set (Extraneous (A S ∪ A T)) as e.
  set (Min (A S) (R S)) as minₛ.
  set (Min (A T) (R T)) as minₜ.
  set (λ f y, y = match (ixm (⦿ (A T - ran f))) with
    | inl _ => minₜ[A T - ran f]
    | inr _ => e
  end) as γ.
  set (constr (A S) (R S) γ) as F.
  pose proof (spec_intro (A S) (R S) γ (wo S)) as [HfF [HdF Hγ]]. {
    intros f. split... unfold γ.
    destruct (ixm (⦿ (A T - ran f))).
    - exists (minₜ [A T - ran f])...
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
      + pose proof (min_correct (A T) (R T) C) as [_ Hmin]...
          { intros c Hc. apply SepE1 in Hc... }
        pose proof (min_correct (A T) (R T) D) as [Hmd _]...
          { intros d Hd. apply SepE1 in Hd... }
        fold minₜ in Hmin, Hmd.
        assert (Hmc: minₜ[D] ∈ C). { eapply HL1... }
        apply Hmin in Hmc as []... exfalso.
        rewrite <- H, <- HFx in Hmd. apply SepE2 in Hmd.
        apply Hmd. eapply ranI. apply restrI.
        apply segI... apply func_correct...
      + exfalso. assert (y ∈ B). apply SepI...
        apply HminS in H as []; subst; eapply linearOrder_irrefl...
      + exfalso. assert (x ∈ B). apply SepI...
        apply HminS in H as []; subst; eapply linearOrder_irrefl...
      + exfalso. assert (x ∈ B). apply SepI...
        apply HminS in H as []; subst; eapply linearOrder_irrefl...
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
      eapply linearOrder_connected in H as []; eauto;
      (eapply linearOrder_irrefl; [apply (wo T)|]).
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
        * pose proof (min_correct (A T) (R T) C) as [Hm _]...
          intros c Hc. apply SepE1 in Hc... apply SepE1 in Hm...
        * exfalso. assert (x ∈ B). apply SepI...
          apply HminS in H as []; subst; eapply linearOrder_irrefl...
      + apply sub_iff_no_comp.
        destruct (classic (A T - ran Fᵒ = ∅))...
        exfalso. apply EmptyNE in H.
        apply Hγ in Haa. fold Fᵒ in Haa.
        destruct (ixm (⦿ (A T - ran Fᵒ)))...
        assert (Hm: minₜ[A T - ran Fᵒ] ∈ A T - ran Fᵒ). apply min_correct...
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
          eapply linearOrder_irrefl. apply (wo T). apply Hxy.
        * apply SepI; [|apply CProdI; apply SepI]...
          eapply linearOrder_connected in H as []... exfalso.
          eapply linearOrder_irrefl. apply (wo T).
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
    + pose proof (min_correct (A T) (R T) C) as [_ Hmin]...
        { intros c Hc. apply SepE1 in Hc... }
      pose proof (min_correct (A T) (R T) D) as [Hmd _]...
        { intros d Hd. apply SepE1 in Hd... }
      fold minₜ in Hmin, Hmd.
      assert (Hmc: minₜ[D] ∈ C). { eapply HL1... }
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
      eapply linearOrder_connected in H as []; eauto;
      (eapply linearOrder_irrefl; [apply (wo T)|]).
      + apply (HL2 _ Hx _ Hy) in H... rewrite Hpx, Hpy in H...
      + apply (HL2 _ Hy _ Hx) in H... rewrite Hpx, Hpy in H...
    - intros x Hx y Hy. split; intros Hxy. apply HL2...
      destruct (classic (x = y)).
      + exfalso. subst. 
        eapply linearOrder_irrefl. apply (wo T). apply Hxy.
      + eapply linearOrder_connected in H as []... exfalso.
        eapply linearOrder_irrefl. apply (wo T).
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
    - assert (minₜ[B] ∈ B). {
        apply min_correct...
        intros b Hb. apply SepE1 in Hb...
      }
      apply SepE1 in H...
    - exfalso. apply He. apply (ranI _ x)...
  }
  assert (Hpsub: ran F ⊂ A T) by (split; auto).
  apply comp_nonempty in Hpsub.
  set (minₜ[A T - ran F]) as b.
  pose proof (min_correct (A T) (R T) (A T -ran F)) as [Hm Hminb]...
  fold minₜ b in Hm, Hminb.
  assert (Hr: ran F = A (Seg b T)). {
    apply sub_antisym; intros y Hy.
    - destruct (wo T) as [Hlo' _].
      apply SepE in Hm as [Hb1 Hb2]. apply Hsub in Hy as Hyt.
      apply SepI... destruct (classic (y = b)). subst...
      apply (linearOrder_connected (R T) (A T)) in H as []...
      exfalso. apply ranE in Hy as [x Hp]. apply domI in Hp as Hx.
      apply func_ap in Hp... rewrite Hγ in Hp...
      set (A T - ran (F ↾ seg x (R S))) as C. fold C in Hp.
      destruct (ixm (⦿ C)); subst y.
      + pose proof (min_correct (A T) (R T) C) as [Hm Hminc]...
        intros c Hc. apply SepE1 in Hc... fold minₜ in Hm, Hminc.
        assert (Hb: b ∈ C). {
          apply SepI... intros Hb'. apply restr_ran_included in Hb'...
        }
        apply Hminc in Hb as [];
        (eapply linearOrder_irrefl; [apply (wo T)|])...
        rewrite H0 in H...
      + assert (e ∈ A S ∪ A T) by (apply BUnionI2; auto).
        eapply extraneous...
    - apply SepE in Hy as [Hy Hyb].
      destruct (classic (y ∈ ran F)) as [|Hy']... exfalso.
      assert (y ∈ A T - ran F) by (apply SepI; auto).
      apply Hminb in H as []; subst;
      (eapply linearOrder_irrefl; [apply (wo T)|])...
  }
  exists b. split. apply SepE1 in Hm...
  exists F. split; [split; split|]...
  - intros c Hc. split. apply ranE in Hc...
    intros x y Hpx Hpy.
    apply domI in Hpx as Hx. apply func_ap in Hpx...
    apply domI in Hpy as Hy. apply func_ap in Hpy...
    rewrite HdF in Hx, Hy.
    destruct (classic (x = y))... exfalso.
    eapply linearOrder_connected in H as []; eauto;
    (eapply linearOrder_irrefl; [apply (wo T)|]).
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
        eapply linearOrder_irrefl. apply (wo T). apply Hxy.
      * eapply linearOrder_connected in H as []... exfalso.
        eapply linearOrder_irrefl. apply (wo T).
        eapply Htr'... apply HL2...
Qed.

End WOStruct.
