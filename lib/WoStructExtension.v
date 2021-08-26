(** Coq coding by choukh, June 2021 **)

Require Import ZFC.Lib.FuncFacts.
Require Import ZFC.Lib.Ordinal.
Import WoStruct.
Import WoStruct.EpsilonImage.

Definition WOₛ_spec := λ p S, p = <A S, R S>.

Lemma WOₛ_unique : ∀ p, uniqueness (WOₛ_spec p).
Proof.
  intros p S T H1 H2. unfold WOₛ_spec in *. subst.
  apply op_iff in H2 as []. apply eq_intro; auto.
Qed.

(* 从良序结构集合到良序结构类型 *)
Definition WOₛ := λ p, iota (inhabits ø̃) (WOₛ_spec p).

Lemma WOₛ_spec_intro : ∀ p, (∃ S, WOₛ_spec p S) → WOₛ_spec p (WOₛ p).
Proof.
  intros p [S H].
  apply (iota_spec (inhabits ø̃) (WOₛ_spec p)).
  rewrite <- unique_existence. split.
  exists S. apply H. apply WOₛ_unique.
Qed.

Lemma WOₛ_pair_id : ∀ S, WOₛ <A S, R S> = S.
Proof.
  intros. pose proof (WOₛ_spec_intro <A S, R S>).
  apply op_iff in H as [HA HR].
  apply eq_intro; auto. exists S. reflexivity.
Qed.

(* 良序结构集集 well-ordered structures *)
Definition wos := λ 𝒞, ∀p ∈ 𝒞, ∃ S, WOₛ_spec p S.

Lemma WOₛ_spec_intro_for_wos :
  ∀ 𝒞, wos 𝒞 → ∀p ∈ 𝒞, WOₛ_spec p (WOₛ p).
Proof.
  intros 𝒞 Hwos p Hp.
  apply (iota_spec (inhabits ø̃) (WOₛ_spec p)).
  rewrite <- unique_existence. split.
  apply Hwos. auto. apply WOₛ_unique.
Qed.

(* 从良序结构集到序数*)
Definition ordₛ := λ p, ord (WOₛ p).
(* 从良序结构集集到序数集 *)
Definition ordsₛ := λ 𝒞, {ordₛ p | p ∊ 𝒞}.

(* 从良序结构集到伊普西隆映射 *)
Definition Eₛ := λ p, E (WOₛ p).
(* 从良序结构集集到伊普西隆映射集 *)
Definition Es := λ 𝒞, {Eₛ p | p ∊ 𝒞}.

Lemma Eₛ_pair : ∀ S, Eₛ <A S, R S> = E S.
Proof. intros. unfold Eₛ. now rewrite WOₛ_pair_id. Qed.

(* 尾扩张 *)
Definition EndExtension := λ S T, S ⊑ T ∧
  ∀a ∈ A S, ∀b ∈ A T - A S, (a <ᵣ b) (R T).
Notation "S ⊑⊑ T" := (EndExtension S T) (at level 70) : WoStruct_scope.

(* 尾扩张结构集集 end extension structures *)
Definition ees := λ 𝒞, ∀ S T,
  <A S, R S> ∈ 𝒞 → <A T, R T> ∈ 𝒞 → S ⊑⊑ T ∨ T ⊑⊑ S.

Lemma E_restr : ∀ S T, S ⊑⊑ T → E S = E T ↾ A S.
Proof with eauto.
  intros * [[HAsub HRsub] Hop].
  pose proof (e_bijective S) as [[HfS _] [HdS _]].
  pose proof (e_bijective T) as [[HfT _] [HdT _]].
  apply func_ext... apply restr_func... split.
  replace (dom (E T ↾ A S)) with (A S)...
  symmetry. apply restr_dom... rewrite HdT...
  intros x Hx. rewrite HdS in Hx.
  erewrite restr_ap; revgoals...
  set {x ∊ A S | (E S)[x] = (E T)[x]} as AS'.
  replace (A S) with AS' in Hx. apply SepE2 in Hx... clear Hx x.
  eapply transfinite_induction...
  split. intros t Ht. apply SepE1 in Ht...
  intros t Ht Hsub. apply SepI... rewrite e_ap...
  ext Hx.
  - apply ReplAx in Hx as [s [Hs Hx]].
    apply SepE2 in Hs as Hst. apply Hsub in Hs.
    apply SepE in Hs as [Hs Heq]. rewrite <- Hx, Heq.
    eapply e_ap_order. apply HAsub... apply HAsub...
    rewrite HRsub in Hst. apply SepE1 in Hst...
  - apply e_elim in Hx as [s [Hs [Hst [Heq Hx]]]]; [|apply HAsub]...
    assert (Hst': (s <ᵣ t) (R S)). {
      rewrite HRsub. apply SepI... apply CProdI...
      contra.
      eapply lo_irrefl. apply (wo T).
      destruct (wo T) as [[_ [Htr _]] _].
      eapply Htr... apply Hop... apply SepI...
    }
    assert (s ∈ seg t (R S)). apply SepI... eapply domI...
    apply ReplAx. exists s. split...
    apply Hsub in H. apply SepE2 in H. congruence.
Qed.

Lemma Es_is_chain : ∀ 𝒞, wos 𝒞 → ees 𝒞 → is_chain (Es 𝒞).
Proof.
  intros 𝒞 Hwos Hees B HB C HC.
  apply ReplAx in HB as [p [Hp HB]].
  apply ReplAx in HC as [q [Hq HC]].
  pose proof (Hwos p Hp) as [S HS].
  pose proof (Hwos q Hq) as [T HT].
  unfold WOₛ_spec in HS, HT. subst.
  repeat rewrite Eₛ_pair.
  pose proof (Hees S T Hp Hq) as [].
  - left. apply E_restr in H. rewrite H.
    intros x Hx. now apply SepE1 in Hx.
  - right. apply E_restr in H. rewrite H.
    intros x Hx. now apply SepE1 in Hx.
Qed.

(* 良序结构集集的并 *)
Definition Unionₐ := λ 𝒞, ⋃{π1 p | p ∊ 𝒞}.
Definition Unionᵣ := λ 𝒞, ⋃{π2 p | p ∊ 𝒞}.

Lemma Unionₐ_eq : ∀ 𝒞, wos 𝒞 → Unionₐ 𝒞 = ⋃{dom f | f ∊ Es 𝒞}.
Proof.
  intros 𝒞 Hwos. unfold Unionₐ. f_equal.
  ext Hx.
  - apply ReplAx in Hx as [p [Hp Heqx]].
    pose proof (Hwos p Hp) as [S HS].
    unfold WOₛ_spec in HS. subst. zfc_simple.
    apply ReplAx. exists (E S). split.
    apply ReplAx. exists <A S, R S>. split; auto.
    now rewrite Eₛ_pair. apply e_spec.
  - apply ReplAx in Hx as [F [HF Heqx]].
    apply ReplAx in HF as [p [Hp HeqF]]. subst.
    pose proof (Hwos p Hp) as [S HS].
    unfold WOₛ_spec in HS. subst. rewrite Eₛ_pair.
    apply ReplAx. exists <A S, R S>. split; auto.
    zfc_simple. symmetry. apply e_spec.
Qed.

Lemma sup_ordsₛ_eq : ∀ 𝒞, wos 𝒞 → sup (ordsₛ 𝒞) = ⋃{ran f | f ∊ Es 𝒞}.
Proof.
  intros 𝒞 Hwos. unfold sup. f_equal.
  ext Hx.
  - apply ReplAx in Hx as [p [Hp Heqp]].
    apply ReplAx. exists (Eₛ p). split; auto.
    now apply ReplI.
  - apply ReplAx in Hx as [F [HF HeqF]].
    apply ReplAx in HF as [p [Hp Heqp]].
    apply ReplAx. exists p. split; auto.
    subst. reflexivity.
Qed.

Lemma union_of_Es_is_bijection : ∀ 𝒞, wos 𝒞 → ees 𝒞 →
  ⋃(Es 𝒞): Unionₐ 𝒞 ⟺ sup (ordsₛ 𝒞).
Proof.
  intros 𝒞 Hwos Hees.
  rewrite Unionₐ_eq, sup_ordsₛ_eq; auto.
  apply union_of_chain_of_injective_functions.
  now apply Es_is_chain. intros f Hf.
  apply ReplAx in Hf as [p [Hp Heq]]. subst.
  apply e_injective.
Qed.

Lemma union_of_Es_preserves_order : ∀ 𝒞, wos 𝒞 → ees 𝒞 →
  let f := ⋃(Es 𝒞) in
  let r := MemberRel (sup (ordsₛ 𝒞)) in
  ∀ x y ∈ Unionₐ 𝒞, (x <ᵣ y) (Unionᵣ 𝒞) ↔ (f[x] <ᵣ f[y]) r.
Proof with eauto; try congruence.
  intros 𝒞 Hwos Hees f r x Hx y Hy. unfold r, f.
  pose proof (union_of_Es_is_bijection 𝒞 Hwos Hees) as Hbi.
  apply bijection_is_func in Hbi as [Hmf [Hinj Hr]].
  assert (H := Hmf). destruct H as [Hf [Hd _]].
  rewrite <- Hd in Hx, Hy.
  assert (H := Hx). apply domE in H as [z1 H1].
  assert (H := Hy). apply domE in H as [z2 H2].
  apply func_ap in H1 as Hap2...
  apply func_ap in H2 as Hap1... subst.
  apply UnionAx in H1 as [F [HF H1]].
  apply UnionAx in H2 as [G [HG H2]].
  apply ReplAx in HF as [u [Hu HF]].
  apply ReplAx in HG as [v [Hv HG]]. subst.
  pose proof (Hwos u Hu) as [U HU].
  pose proof (Hwos v Hv) as [V HV].
  pose proof (e_bijective U) as [[HfU _] [HdU _]].
  pose proof (e_bijective V) as [[HfV _] [HdV _]].
  unfold WOₛ_spec in HU, HV. subst.
  rewrite Eₛ_pair in H1, H2.
  apply domI in H1 as Hd1. apply func_ap in H1...
  apply domI in H2 as Hd2. apply func_ap in H2...
  split; intros Hlt.
  - apply UnionAx in Hlt as [p [Hp Hlt]].
    apply ReplAx in Hp as [s [Hs Hp]].
    pose proof (Hwos s Hs) as [S HS].
    unfold WOₛ_spec in HS. subst. zfc_simple.
    apply binRelI. eapply ap_ran... eapply ap_ran...
    rewrite <- H1, <- H2.
    pose proof (Hees U V Hu Hv) as [];
    apply E_restr in H as Heq; rewrite Heq;
    destruct H as [[Hsub Hrsub] Hop].
    + assert (HxV: x ∈ A V). apply Hsub...
      erewrite restr_ap; revgoals... apply e_ap_order...
      pose proof (Hees S V Hs Hv) as [[[_ H] _]|[[_ H] _]].
      * rewrite H in Hlt. apply SepE1 in Hlt...
      * rewrite H. apply SepI... apply CProdI...
    + assert (HyU: y ∈ A U). apply Hsub...
      erewrite restr_ap; revgoals... apply e_ap_order... 
      pose proof (Hees S U Hs Hu) as [[[_ H] _]|[[_ H] _]].
      * rewrite H in Hlt. apply SepE1 in Hlt...
      * rewrite H. apply SepI... apply CProdI...
  - apply binRelE3 in Hlt. rewrite <- H1, <- H2 in Hlt.
    pose proof (Hees U V Hu Hv) as [];
    apply E_restr in H as Heq;
    destruct H as [[Hsub Hrsub] Hop].
    + apply UnionAx. exists (R V). split.
      apply ReplAx. exists <A V, R V>. split... zfc_simple.
      assert (HxV: x ∈ A V). apply Hsub...
      apply e_preserve_order... apply binRelI.
      apply e_ap_in_α... apply e_ap_in_α...
      erewrite Heq, restr_ap in Hlt; revgoals...
    + apply UnionAx. exists (R U). split.
      apply ReplAx. exists <A U, R U>. split... zfc_simple.
      assert (HyU: y ∈ A U). apply Hsub...
      apply e_preserve_order... apply binRelI.
      apply e_ap_in_α... apply e_ap_in_α...
      erewrite Heq, restr_ap in Hlt; revgoals...
Qed.

Lemma sup_ordsₛ_is_ord : ∀ 𝒞, sup (ordsₛ 𝒞) ⋵ 𝐎𝐍.
Proof.
  intros. apply union_of_ords_is_ord.
  intros α Hα. apply ReplAx in Hα as [p [_ Heq]].
  subst. apply ord_is_ord.
Qed.

Lemma union_wos_is_binRel : ∀ 𝒞, wos 𝒞 →
  is_binRel (Unionᵣ 𝒞) (Unionₐ 𝒞).
Proof.
  intros 𝒞 Hwos x Hx.
  apply UnionAx in Hx as [a [Ha Hx]].
  apply ReplAx in Ha as [p [Hp HR]].
  pose proof (Hwos p Hp) as [S HS].
  unfold WOₛ_spec in HS. subst. zfc_simple.
  destruct (wo S) as [[Hbr _] _]. apply Hbr in Hx.
  apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]]. subst.
  apply CProdI; apply UnionAx; exists (A S); split; auto;
  apply ReplAx; exists <A S, R S>; split; auto; zfc_simple.
Qed.

(* 良序结构尾扩张集集的并是良序结构集 *)
Lemma union_wos_is_woet : ∀ 𝒞, wos 𝒞 → ees 𝒞 →
  woset (Unionₐ 𝒞) (Unionᵣ 𝒞).
Proof.
  intros 𝒞 Hwos Hees.
  pose proof (union_wos_is_binRel 𝒞 Hwos) as Hbr.
  set (OrderedStruct.constr (Unionₐ 𝒞) (Unionᵣ 𝒞) Hbr) as S.
  cut (OrderedStruct.wo S). easy.
  pose proof (sup_ordsₛ_is_ord 𝒞) as [T HT].
  apply (OrderedStruct.iso_wo (parent (Epsilon T))); [|apply wo].
  symmetry. exists (⋃(Es 𝒞)).
  split; simpl; unfold ord in HT; [|unfold ε]; rewrite <- HT.
  now apply union_of_Es_is_bijection.
  now apply union_of_Es_preserves_order.
Qed.

Definition unionStruct_spec := λ 𝒞 S,
  A S = Unionₐ 𝒞 ∧ R S = Unionᵣ 𝒞.

Lemma unionStruct_exists : ∀ 𝒞, wos 𝒞 → ees 𝒞 →
  ∃! S, unionStruct_spec 𝒞 S.
Proof.
  intros 𝒞 Hwos Hees.
  pose proof (union_wos_is_woet 𝒞 Hwos Hees) as Hwo.
  rewrite <- unique_existence. split.
  - exists (constr (Unionₐ 𝒞) (Unionᵣ 𝒞) Hwo). split; auto.
  - intros S T [H11 H12] [H21 H22].
    apply eq_intro; congruence.
Qed.

(* 对良序结构集集取并得到良序结构类型 *)
Definition UnionStruct :=
  λ 𝒞, iota (inhabits ø̃) (unionStruct_spec 𝒞).
Notation "⊔ 𝒞" := (UnionStruct 𝒞) (at level 9, format "⊔ 𝒞") : WoStruct_scope.

Lemma unionStruct_spec_intro : ∀ 𝒞, wos 𝒞 → ees 𝒞 →
  unionStruct_spec 𝒞 ⊔𝒞.
Proof.
  intros 𝒞 Hwos Hees.
  apply (iota_spec (inhabits ø̃) (unionStruct_spec 𝒞)).
  apply unionStruct_exists; auto.
Qed.

(* 良序结构尾扩张集集𝒞的并的序数等于𝒞对应序数集的上确界 *)
Lemma ord_union_eq_sup_ordsₛ_wos : ∀ 𝒞,
  wos 𝒞 → ees 𝒞 → ord ⊔𝒞 = sup (ordsₛ 𝒞).
Proof.
  intros 𝒞 Hwos Hees.
  pose proof (unionStruct_spec_intro 𝒞 Hwos Hees) as [HA HR].
  assert (Ho: sup (ordsₛ 𝒞) ⋵ 𝐎𝐍). apply sup_ordsₛ_is_ord.
  destruct Ho as [S HS]. rewrite HS.
  apply ord_well_defined. rewrite (iso_epsilon S).
  exists (⋃(Es 𝒞)). split; simpl; unfold ord in HS;
  rewrite HA; [|rewrite HR; unfold ε]; rewrite <- HS.
  now apply union_of_Es_is_bijection.
  now apply union_of_Es_preserves_order.
Qed.

(* 从序数到良序结构集 *)
Definition woₒ := λ α, <α, MemberRel α>.
(* 从序数到良序结构类型 *)
Definition WOₒ := λ α, WOₛ (woₒ α).

(*
  ord WOₛ woₒ α =
  ord WOₒ      α =
  ordₛ    woₒ α = α
*)

Lemma WOₛ_eq_Epsilon : ∀ S,
  WOₛ <ord S, MemberRel (ord S)> = Epsilon S.
Proof.
  intros. replace <ord S, MemberRel (ord S)> with <A (Epsilon S), R (Epsilon S)>.
  now rewrite WOₛ_pair_id. now apply op_iff.
Qed.

Lemma A_WOₒ_id : ∀α ⋵ 𝐎𝐍, A (WOₒ α) = α.
Proof.
  intros α [S HS]. subst. unfold WOₒ, woₒ.
  now rewrite WOₛ_eq_Epsilon.
Qed.

Lemma R_WOₒ : ∀α ⋵ 𝐎𝐍, R (WOₒ α) = MemberRel α.
Proof.
  intros α [S HS]. subst. unfold WOₒ, woₒ.
  now rewrite WOₛ_eq_Epsilon.
Qed.

Lemma ord_WOₒ_id : ∀α ⋵ 𝐎𝐍, ord (WOₒ α) = α.
Proof.
  intros α [S HS]. subst. unfold WOₒ, woₒ.
  now rewrite WOₛ_eq_Epsilon, <- ord_of_ord.
Qed.

Lemma ordₛ_woₒ_id : ∀α ⋵ 𝐎𝐍, ordₛ (woₒ α) = α.
Proof.
  intros α H. now rewrite <- (ord_WOₒ_id α) at 2.
Qed.

(* 从序数(集)到良序结构集集 *)
Definition wosₒ := λ A, {woₒ α | α ∊ A}.

Lemma ordsₛ_wosₒ_id : ∀ A, A ⪽ 𝐎𝐍 → ordsₛ (wosₒ A) = A.
Proof with auto.
  intros A Hsub. unfold ordsₛ, wosₒ.
  ext Hx.
  - apply ReplAx in Hx as [p [Hp Hx]].
    apply ReplAx in Hp as [α [Hα Hp]]. subst.
    rewrite ordₛ_woₒ_id...
  - apply ReplAx. exists (woₒ x). split.
    apply ReplAx. exists x. split...
    apply ordₛ_woₒ_id...
Qed.

Lemma wosₒ_is_wos : ∀ A, A ⪽ 𝐎𝐍 → wos (wosₒ A).
Proof with eauto.
  intros A Hsub p Hp.
  apply ReplAx in Hp as [ξ [Hξα Heq]]. subst.
  assert (Hoξ: ξ ⋵ 𝐎𝐍)...
  destruct Hoξ as [S HS]. subst.
  exists (Epsilon S). apply op_iff...
Qed.

Lemma wosₒ_is_ees : ∀ A, A ⪽ 𝐎𝐍 → ees (wosₒ A).
Proof with eauto; try congruence.
  intros B Hsub S T HS HT.
  apply ReplAx in HS as [β [Hβα Heqβ]].
  apply ReplAx in HT as [γ [Hγα Heqγ]].
  assert (Hoβ: β ⋵ 𝐎𝐍)...
  assert (Hoγ: γ ⋵ 𝐎𝐍)...
  apply op_iff in Heqβ as [H11 H12].
  apply op_iff in Heqγ as [H21 H22].
  pose proof (ord_comparability β Hoβ γ Hoγ) as []; subst;
  apply ord_leq_iff_sub in H; auto; [left|right]; repeat split...
  - rewrite <- H12, <- H22.
    ext Hx.
    + apply binRelE1 in Hx as [a [Ha [b [Hb [Hx Hab]]]]]. subst.
      apply SepI. apply binRelI... apply CProdI...
    + apply SepE in Hx as [H1 H2].
      apply CProdE1 in H2 as [a [Ha [b [Hb Heq]]]]. subst.
      apply binRelE3 in H1. apply binRelI...
  - intros x Hx y Hy. apply SepE in Hy as [Hy Hy'].
    assert (Hoy: y ⋵ 𝐎𝐍). eapply ord_is_ords...
    apply ord_leq_iff_not_gt in Hy'...
    rewrite <- H22. apply binRelI...
    destruct Hy'... eapply ord_trans... 
  - rewrite <- H12, <- H22.
    ext Hx.
    + apply binRelE1 in Hx as [a [Ha [b [Hb [Hx Hab]]]]]. subst.
      apply SepI. apply binRelI... apply CProdI...
    + apply SepE in Hx as [H1 H2].
      apply CProdE1 in H2 as [a [Ha [b [Hb Heq]]]]. subst.
      apply binRelE3 in H1. apply binRelI...
  - intros x Hx y Hy. apply SepE in Hy as [Hy Hy'].
    assert (Hoy: y ⋵ 𝐎𝐍). apply (ord_is_ords (A S))...
    apply ord_leq_iff_not_gt in Hy'...
    rewrite <- H12. apply binRelI...
    destruct Hy'... eapply ord_trans...
Qed.

(* 序数集A的结构集集的并的序数等于A的上确界 *)
Lemma ord_union_eq_sup_of_ords : ∀ A,
  A ⪽ 𝐎𝐍 → ord ⊔(wosₒ A) = sup A.
Proof with auto.
  intros A Hsub.
  rewrite <- (ordsₛ_wosₒ_id A) at 2...
  apply ord_union_eq_sup_ordsₛ_wos.
  apply wosₒ_is_wos... apply wosₒ_is_ees...
Qed.
