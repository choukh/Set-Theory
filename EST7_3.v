(** Based on "Elements of Set Theory" Chapter 7 Part 3 **)
(** Coq coding by choukh, Dec 2020 **)

Require Export ZFC.EST7_2.
Require Import ZFC.lib.FuncFacts.

(*** EST第七章3：序同构，序数的定义 ***)

(* 保序映射 *)
Definition order_preserved_func := λ A R f S,
  ∀ x y ∈ A, (x <ᵣ y) R ↔ (f[x] <ᵣ f[y]) S.

(* 伊普西龙像 *)
Module EpsilonImage.

Definition γ := λ x y, y = ran x.

Definition E := λ A R,
  TransfiniteRecursion.constr A R γ.

Definition α := λ A R, ran (E A R).

Definition ε := λ A R, MemberRel (α A R).

Lemma e_spec : ∀ A R, woset A R →
  TransfiniteRecursion.spec A R γ (E A R).
Proof.
  intros. apply TransfiniteRecursion.spec_intro. apply H.
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

Definition constr := λ f A S,
  BinRel A (λ x y, (f[x] <ᵣ f[y]) S).

Lemma po : ∀ f A B S, poset B S → poset A (constr f A S).
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

Lemma lo : ∀ f A B S, f: A ⇔ B →
  loset B S → loset A (constr f A S).
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

Lemma wo : ∀ f A B S, f: A ⇔ B →
  woset B S → woset A (constr f A S).
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

End ImageRel.

(* 序结构 *)
Module OrderedStructure.

Record Structure : Type := constr {
  A : set;
  R : set;
  cond : is_binRel R A;
}.

Definition po := λ S, poset (A S) (R S).
Definition lo := λ S, loset (A S) (R S).
Definition wo := λ S, woset (A S) (R S).

Definition α := λ S, EpsilonImage.α (A S) (R S).
Definition ε := λ S, EpsilonImage.ε (A S) (R S).
Definition Epsilon := λ S,
  constr (α S) (ε S) (memberRel_is_binRel _).

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
Add Relation Structure isomorphic
  reflexivity proved by iso_refl
  symmetry proved by iso_symm
  transitivity proved by iso_tran
  as iso_rel.

(* 与偏序结构同构的结构也是偏序结构 *)
Theorem iso_po : ∀ S T, S ≅ T → po S → po T.
Proof with auto.
  intros * Hiso Hpo. symmetry in Hiso.
  destruct Hiso as [f [_ H]].
  apply (ImageRel.po f (A T)) in Hpo.
  replace (ImageRel.constr f (A T) (R S)) with (R T) in Hpo...
  apply ExtAx. intros p. split; intros Hp.
  - apply cond in Hp as Hcp.
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
  - apply cond in Hp as Hcp.
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
  - apply cond in Hp as Hcp.
    apply CProdE1 in Hcp as [a [Ha [b [Hb Heq]]]].
    subst p. apply binRelI... apply H...
  - apply binRelE1 in Hp as [a [Ha [b [Hb [Heq Hlt]]]]].
    subst p. apply H...
Qed.

(* 任意良序结构与其伊普西龙结构同构 *)
Fact wo_iso_epsilon : ∀ S, wo S → S ≅ Epsilon S.
Proof with auto.
  intros S Hwo.
  exists (EpsilonImage.E (A S) (R S)). split.
  - apply EpsilonImage.e_bijective...
  - apply EpsilonImage.e_preserve_order...
Qed.

(* 任意良序结构的伊普西龙像是传递集 *)
Corollary α_trans : ∀ S, wo S → trans (α S).
Proof. intros. apply EpsilonImage.α_trans. apply H. Qed.

(* 任意良序结构的伊普西龙结构也是良序结构 *)
Corollary epsilon_wo : ∀ S, wo S → wo (Epsilon S).
Proof with eauto.
  intros. eapply iso_wo... apply wo_iso_epsilon...
Qed.

(* 良序结构间的态射唯一 *)
Theorem wo_iso_unique : ∀ S T, wo S → S ≅ T →
  ∃! f, f: A S ⟺ A T ∧ order_preserved_func (A S) (R S) f (R T).
Proof with eauto; try congruence.
  intros S T Hwo Hiso. split...
  intros f g [Hf H1] [Hg H2].
  eapply iso_wo in Hwo as Hwo'...
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

End OrderedStructure.

Notation "S ≅ T" := (OrderedStructure.isomorphic S T) (at level 60).
