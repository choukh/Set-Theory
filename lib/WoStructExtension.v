(** Coq coding by choukh, June 2021 **)

Require Import ZFC.lib.FuncFacts.
Require Import ZFC.lib.Ordinal.
Import WoStruct.
Import WoStruct.EpsilonImage.

Definition wos_spec := λ p S, p = <A S, R S>.

Lemma wos_unique : ∀ p, uniqueness (wos_spec p).
Proof.
  intros p S T H1 H2. unfold wos_spec in *. subst.
  apply op_iff in H2 as []. apply eq_intro; auto.
Qed.

(* 从良序集到良序结构 *)
Definition WOₛ := λ p, iota (inhabits ø̃) (wos_spec p).

Lemma wos_spec_intro : ∀ p, (∃ S, wos_spec p S) → wos_spec p (WOₛ p).
Proof.
  intros p [S H].
  apply (iota_spec (inhabits ø̃) (wos_spec p)).
  rewrite <- unique_existence. split.
  exists S. apply H. apply wos_unique.
Qed.

Lemma wos_pair_id : ∀ S, WOₛ <A S, R S> = S.
Proof.
  intros. pose proof (wos_spec_intro <A S, R S>).
  apply op_iff in H as [HA HR].
  apply eq_intro; auto. exists S. reflexivity.
Qed.

(* 良序结构集 well-ordered structures *)
Definition woss := λ 𝒞, ∀p ∈ 𝒞, ∃ S, wos_spec p S.

Lemma wos_spec_intro_for_woss :
  ∀ 𝒞, woss 𝒞 → ∀p ∈ 𝒞, wos_spec p (WOₛ p).
Proof.
  intros 𝒞 Hwoss p Hp.
  apply (iota_spec (inhabits ø̃) (wos_spec p)).
  rewrite <- unique_existence. split.
  apply Hwoss. auto. apply wos_unique.
Qed.

(* 从良序集到序数*)
Definition ordₛ := λ p, ord (WOₛ p).
(* 从良序结构集到序数集 *)
Definition ords := λ 𝒞, {ordₛ | p ∊ 𝒞}.

(* 从良序集到伊普西隆映射 *)
Definition Eₛ := λ p, E (WOₛ p).
(* 从良序结构集到伊普西隆映射集 *)
Definition Es := λ 𝒞, {Eₛ | p ∊ 𝒞}.

Lemma es_pair_id : ∀ S, Eₛ <A S, R S> = E S.
Proof. intros. unfold Eₛ. now rewrite wos_pair_id. Qed.

(* 尾扩张 *)
Definition EndExtension := λ S T, S ⊑ T ∧
  ∀a ∈ A S, ∀b ∈ A T - A S, (a <ᵣ b) (R T).
Notation "S ⊑⊑ T" := (EndExtension S T) (at level 70) : WoStruct_scope.

(* 尾扩张结构集 end extension structures *)
Definition eess := λ 𝒞, ∀ S T,
  <A S, R S> ∈ 𝒞 → <A T, R T> ∈ 𝒞 → S ⊑⊑ T ∨ T ⊑⊑ S.

Lemma es_restr : ∀ S T, S ⊑⊑ T → E S = E T ↾ A S.
Proof with eauto.
  intros * [[HAsub HRsub] Hop].
  pose proof (e_bijective S) as [[HfS _] [HdS _]].
  pose proof (e_bijective T) as [[HfT _] [HdT _]].
  apply func_ext... apply restr_func... split.
  replace (dom (E T ↾ A S)) with (A S)...
  symmetry. apply restr_dom... rewrite HdT...
  intros x Hx. rewrite HdS in Hx.
  rewrite restr_ap; revgoals...
  set {x ∊ A S | λ x, (E S)[x] = (E T)[x]} as AS'.
  replace (A S) with AS' in Hx. apply SepE2 in Hx... clear Hx x.
  eapply transfinite_induction...
  split. intros t Ht. apply SepE1 in Ht...
  intros t Ht Hsub. apply SepI... rewrite e_ap...
  apply ExtAx. split; intros Hx.
  - apply ReplAx in Hx as [s [Hs Hx]].
    apply SepE2 in Hs as Hst. apply Hsub in Hs.
    apply SepE in Hs as [Hs Heq]. rewrite <- Hx, Heq.
    eapply e_ap_order. apply HAsub... apply HAsub...
    rewrite HRsub in Hst. apply SepE1 in Hst...
  - apply e_elim in Hx as [s [Hs [Hst [Heq Hx]]]]; [|apply HAsub]...
    assert (Hst': (s <ᵣ t) (R S)). {
      rewrite HRsub. apply SepI... apply CProdI...
      destruct (classic (s ∈ A S))... exfalso.
      eapply lo_irrefl. apply (wo T).
      destruct (wo T) as [[_ [Htr _]] _].
      eapply Htr... apply Hop... apply SepI...
    }
    assert (s ∈ seg t (R S)). apply SepI... eapply domI...
    apply ReplAx. exists s. split...
    apply Hsub in H. apply SepE2 in H. congruence.
Qed.

Lemma es_is_chain : ∀ 𝒞, woss 𝒞 → eess 𝒞 → is_chain (Es 𝒞).
Proof.
  intros 𝒞 Hwoss Heess B HB C HC.
  apply ReplAx in HB as [p [Hp HB]].
  apply ReplAx in HC as [q [Hq HC]].
  pose proof (Hwoss p Hp) as [S HS].
  pose proof (Hwoss q Hq) as [T HT].
  unfold wos_spec in HS, HT. subst.
  repeat rewrite es_pair_id.
  pose proof (Heess S T Hp Hq) as [].
  - left. apply es_restr in H. rewrite H.
    intros x Hx. now apply SepE1 in Hx.
  - right. apply es_restr in H. rewrite H.
    intros x Hx. now apply SepE1 in Hx.
Qed.

(* 良序结构集的并 *)
Definition Union_A := λ 𝒞, ⋃{π1 | p ∊ 𝒞}.
Definition Union_R := λ 𝒞, ⋃{π2 | p ∊ 𝒞}.

Lemma union_A_eq : ∀ 𝒞, woss 𝒞 → Union_A 𝒞 = ⋃{dom | f ∊ Es 𝒞}.
Proof.
  intros 𝒞 Hwoss. unfold Union_A. f_equal.
  apply ExtAx. split; intros Hx.
  - apply ReplAx in Hx as [p [Hp Heqx]].
    pose proof (Hwoss p Hp) as [S HS].
    unfold wos_spec in HS. subst. zfc_simple.
    apply ReplAx. exists (E S). split.
    apply ReplAx. exists <A S, R S>. split; auto.
    now rewrite es_pair_id. apply e_spec.
  - apply ReplAx in Hx as [F [HF Heqx]].
    apply ReplAx in HF as [p [Hp HeqF]]. subst.
    pose proof (Hwoss p Hp) as [S HS].
    unfold wos_spec in HS. subst. rewrite es_pair_id.
    apply ReplAx. exists <A S, R S>. split; auto.
    zfc_simple. symmetry. apply e_spec.
Qed.

Lemma sup_ords_eq : ∀ 𝒞, woss 𝒞 → sup (ords 𝒞) = ⋃{ran | f ∊ Es 𝒞}.
Proof.
  intros 𝒞 Hwoss. unfold sup. f_equal.
  apply ExtAx. split; intros Hx.
  - apply ReplAx in Hx as [p [Hp Heqp]].
    apply ReplAx. exists (Eₛ p). split; auto.
    now apply ReplI.
  - apply ReplAx in Hx as [F [HF HeqF]].
    apply ReplAx in HF as [p [Hp Heqp]].
    apply ReplAx. exists p. split; auto.
    subst. reflexivity.
Qed.

Lemma union_of_es_is_bijection : ∀ 𝒞, woss 𝒞 → eess 𝒞 →
  ⋃(Es 𝒞): Union_A 𝒞 ⟺ sup (ords 𝒞).
Proof.
  intros 𝒞 Hwoss Heess.
  rewrite union_A_eq, sup_ords_eq; auto.
  apply union_of_chain_of_injective_functions.
  now apply es_is_chain. intros f Hf.
  apply ReplAx in Hf as [p [Hp Heq]]. subst.
  apply e_injective.
Qed.

Lemma union_of_es_preserves_order : ∀ 𝒞, woss 𝒞 → eess 𝒞 →
  let f := ⋃(Es 𝒞) in
  let r := MemberRel (sup (ords 𝒞)) in
  ∀ x y ∈ Union_A 𝒞, (x <ᵣ y) (Union_R 𝒞) ↔ (f[x] <ᵣ f[y]) r.
Proof with eauto; try congruence.
  intros 𝒞 Hwoss Heess f r x Hx y Hy. unfold r, f.
  pose proof (union_of_es_is_bijection 𝒞 Hwoss Heess) as Hbi.
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
  pose proof (Hwoss u Hu) as [U HU].
  pose proof (Hwoss v Hv) as [V HV].
  pose proof (e_bijective U) as [[HfU _] [HdU _]].
  pose proof (e_bijective V) as [[HfV _] [HdV _]].
  unfold wos_spec in HU, HV. subst.
  rewrite es_pair_id in H1, H2.
  apply domI in H1 as Hd1. apply func_ap in H1...
  apply domI in H2 as Hd2. apply func_ap in H2...
  split; intros Hlt.
  - apply UnionAx in Hlt as [p [Hp Hlt]].
    apply ReplAx in Hp as [s [Hs Hp]].
    pose proof (Hwoss s Hs) as [S HS].
    unfold wos_spec in HS. subst. zfc_simple.
    apply binRelI. eapply ap_ran... eapply ap_ran...
    rewrite <- H1, <- H2.
    pose proof (Heess U V Hu Hv) as [];
    apply es_restr in H as Heq; rewrite Heq;
    destruct H as [[Hsub Hrsub] Hop].
    + assert (HxV: x ∈ A V). apply Hsub...
      rewrite restr_ap; revgoals... apply e_ap_order...
      pose proof (Heess S V Hs Hv) as [[[_ H] _]|[[_ H] _]].
      * rewrite H in Hlt. apply SepE1 in Hlt...
      * rewrite H. apply SepI... apply CProdI...
    + assert (HyU: y ∈ A U). apply Hsub...
      rewrite restr_ap; revgoals... apply e_ap_order... 
      pose proof (Heess S U Hs Hu) as [[[_ H] _]|[[_ H] _]].
      * rewrite H in Hlt. apply SepE1 in Hlt...
      * rewrite H. apply SepI... apply CProdI...
  - apply binRelE3 in Hlt. rewrite <- H1, <- H2 in Hlt.
    pose proof (Heess U V Hu Hv) as [];
    apply es_restr in H as Heq;
    destruct H as [[Hsub Hrsub] Hop].
    + apply UnionAx. exists (R V). split.
      apply ReplAx. exists <A V, R V>. split... zfc_simple.
      assert (HxV: x ∈ A V). apply Hsub...
      apply e_preserve_order... apply binRelI.
      apply e_ap_in_α... apply e_ap_in_α...
      rewrite Heq, restr_ap in Hlt; revgoals...
    + apply UnionAx. exists (R U). split.
      apply ReplAx. exists <A U, R U>. split... zfc_simple.
      assert (HyU: y ∈ A U). apply Hsub...
      apply e_preserve_order... apply binRelI.
      apply e_ap_in_α... apply e_ap_in_α...
      rewrite Heq, restr_ap in Hlt; revgoals...
Qed.

Lemma sup_ords_is_ord : ∀ 𝒞, sup (ords 𝒞) ⋵ 𝐎𝐍.
Proof.
  intros. apply union_of_ords_is_ord.
  intros α Hα. apply ReplAx in Hα as [p [_ Heq]].
  subst. apply ord_is_ord.
Qed.

Lemma union_woss_is_binRel : ∀ 𝒞, woss 𝒞 →
  is_binRel (Union_R 𝒞) (Union_A 𝒞).
Proof.
  intros 𝒞 Hwoss x Hx.
  apply UnionAx in Hx as [a [Ha Hx]].
  apply ReplAx in Ha as [p [Hp HR]].
  pose proof (Hwoss p Hp) as [S HS].
  unfold wos_spec in HS. subst. zfc_simple.
  destruct (wo S) as [[Hbr _] _]. apply Hbr in Hx.
  apply CProdE1 in Hx as [a [Ha [b [Hb Hx]]]]. subst.
  apply CProdI; apply UnionAx; exists (A S); split; auto;
  apply ReplAx; exists <A S, R S>; split; auto; zfc_simple.
Qed.

(* 良序结构尾扩张集的并是良序结构 *)
Lemma union_woss_is_woset : ∀ 𝒞, woss 𝒞 → eess 𝒞 →
  woset (Union_A 𝒞) (Union_R 𝒞).
Proof.
  intros 𝒞 Hwoss Heess.
  pose proof (union_woss_is_binRel 𝒞 Hwoss) as Hbr.
  set (OrderedStruct.constr (Union_A 𝒞) (Union_R 𝒞) Hbr) as S.
  cut (OrderedStruct.wo S). easy.
  pose proof (sup_ords_is_ord 𝒞) as [T HT].
  apply (OrderedStruct.iso_wo (parent (Epsilon T))); [|apply wo].
  symmetry. exists (⋃(Es 𝒞)).
  split; simpl; unfold ord in HT; [|unfold ε]; rewrite <- HT.
  now apply union_of_es_is_bijection.
  now apply union_of_es_preserves_order.
Qed.

Definition unionStruct_spec := λ 𝒞 S,
  A S = Union_A 𝒞 ∧ R S = Union_R 𝒞.

Lemma unionStruct_exists : ∀ 𝒞, woss 𝒞 → eess 𝒞 →
  ∃! S, unionStruct_spec 𝒞 S.
Proof.
  intros 𝒞 Hwoss Heess.
  pose proof (union_woss_is_woset 𝒞 Hwoss Heess) as Hwo.
  rewrite <- unique_existence. split.
  - exists (constr (Union_A 𝒞) (Union_R 𝒞) Hwo). split; auto.
  - intros S T [H11 H12] [H21 H22].
    apply eq_intro; congruence.
Qed.

(* 结构并 *)
Definition UnionStruct :=
  λ 𝒞, iota (inhabits ø̃) (unionStruct_spec 𝒞).
Notation "⊔ 𝒞" := (UnionStruct 𝒞) (at level 9, format "⊔ 𝒞") : WoStruct_scope.

Lemma unionStruct_spec_intro : ∀ 𝒞, woss 𝒞 → eess 𝒞 →
  unionStruct_spec 𝒞 ⊔𝒞.
Proof.
  intros 𝒞 Hwoss Heess.
  apply (iota_spec (inhabits ø̃) (unionStruct_spec 𝒞)).
  apply unionStruct_exists; auto.
Qed.

(* 良序结构尾扩张集𝒞的并的序数等于𝒞对应序数集的上确界 *)
Lemma ord_of_union_eq_union_of_ord : ∀ 𝒞,
  woss 𝒞 → eess 𝒞 → ord ⊔𝒞 = sup (ords 𝒞).
Proof.
  intros 𝒞 Hwoss Heess.
  pose proof (unionStruct_spec_intro 𝒞 Hwoss Heess) as [HA HR].
  assert (Ho: sup (ords 𝒞) ⋵ 𝐎𝐍). apply sup_ords_is_ord.
  destruct Ho as [S HS]. rewrite HS.
  apply ord_well_defined. rewrite (iso_epsilon S).
  exists (⋃(Es 𝒞)). split; simpl; unfold ord in HS;
  rewrite HA; [|rewrite HR; unfold ε]; rewrite <- HS.
  now apply union_of_es_is_bijection.
  now apply union_of_es_preserves_order.
Qed.
