(** Coq coding by choukh, Apr 2021 **)

Require Import ZFC.EST8_4.
Require Import ZFC.EX7_1.
Require Import ZFC.EX8_2.
Require Import ZFC.lib.FuncFacts.
Require Import ZFC.lib.Real.
Require Import ZFC.lib.LoStruct.
Require Import ZFC.lib.WosetMin.
Require Import ZFC.lib.NatIsomorphism.
Require Import ZFC.lib.IndexedFamilyUnion.

(** EX8_18 **)
(** Back-and-forth method **)
(** 来回嵌入法 **)

(* 可数无界是可数无限 *)
Fact countable_unbounded_infinite : ∀ S, A S ≠ ∅ →
  countable (A S) → unbounded (A S) (R S) → ω ≈ A S.
Proof with eauto.
  intros S Hne Hcnt [Hul _].
  apply EmptyNE in Hne.
  apply countable_iff in Hcnt as [Hfin|]; [exfalso|symmetry]...
  eapply finite_loset_is_woset in Hfin as [_ Hmin]...
  pose proof (Hmin (A S)) as [m [Hm Hle]]...
  apply Hul in Hm as [n [Hn Hlt]].
  eapply relLt_irrefl. eapply lo_irrefl. apply lo.
  eapply relLt_le_tranr... apply lo.
Qed.

Import WosetMin.SimpleVer.

Definition LeftInterval := λ x R f,
  {y ∊ dom f | λ y, (y <ᵣ x) R}.

Definition RightInterval := λ x R f,
  {y ∊ dom f | λ y, (x <ᵣ y) R}.

Definition MaxLeft := λ x R f,
  FinLoMax R (LeftInterval x R f).

Definition MinRight := λ x R f,
  FinLoMin R (RightInterval x R f).

Definition LeftNats := λ x R S b f,
  let aₗ := MaxLeft x R f in
  {n ∊ ω | λ n, (f[aₗ] <ᵣ b[n]) S}.

Definition RightNats := λ x R S b f,
  let aᵣ := MinRight x R f in
  {n ∊ ω | λ n, (b[n] <ᵣ f[aᵣ]) S}.

Definition MidNats := λ x R S b f,
  let aₗ := MaxLeft x R f in
  let aᵣ := MinRight x R f in
  {n ∊ ω | λ n, (f[aₗ] <ᵣ b[n]) S ∧ (b[n] <ᵣ f[aᵣ]) S}.

Definition PairLeft := λ x R S b f,
  let N := LeftNats x R S b f in
  b[(Min Lt)[N]].

Definition PairRight := λ x R S b f,
  let N := RightNats x R S b f in
  b[(Min Lt)[N]].

Definition PairMid := λ x R S b f,
  let N := MidNats x R S b f in
  b[(Min Lt)[N]].

Definition Pairing := λ x R S b f,
  let 𝐋 := LeftInterval x R f in
  let 𝐑 := RightInterval x R f in
  match (ixm (𝐋 = ∅)) with
  | inl _ => match (ixm (𝐑 = ∅)) with
    | inl _ => b[0]
    | inr _ => PairRight x R S b f
    end
  | inr _ => match (ixm (𝐑 = ∅)) with
    | inl _ => PairLeft x R S b f
    | inr _ => PairMid x R S b f
    end
  end.

Definition Add := λ x R S b f, f ∪ ⎨<x, Pairing x R S b f>⎬.

Definition op := λ R S f, ∀ x y ∈ dom f, (x <ᵣ y) R ↔ (f[x] <ᵣ f[y]) S.

Definition good := λ A R B S f,
  injective f ∧ dom f ⊆ A ∧ ran f ⊆ B ∧ finite f ∧ op R S f.

Lemma max_left :
  ∀ A R a, a: ω ⟺ A → loset A R →
  ∀ f, is_function f → dom f ⊆ A → finite f →
  ∀ x,
    let 𝐋 := LeftInterval x R f in
    let aₗ := MaxLeft x R f in
    𝐋 ≠ ∅ → aₗ ∈ dom f ∧ (aₗ <ᵣ x) R ∧
    ∀w ∈ dom f, (w <ᵣ x) R → (w ≤ᵣ aₗ) R.
Proof with eauto; try congruence.
  intros A R a [[Ha _] [Hda Hra]] Hlo.
  intros f Hf Hd Hfin x₀ 𝐋 aₗ Hne.
  pose proof (finite_loset_has_max A R 𝐋) as [H Hle]...
  - intros x Hx. apply SepE1 in Hx. apply Hd...
  - apply (subset_of_finite_is_finite _ (dom f)). apply sep_sub.
    rewrite dom_eq_π1_repl... apply repl_finite...
  - apply SepE in H as [H1 H2]. repeat split...
    intros w Hw Hlt. assert (w ∈ 𝐋). apply SepI...
    apply Hle in H as []; [left|right]... apply SepE1 in H...
Qed.

Lemma min_right :
  ∀ A R a, a: ω ⟺ A → loset A R →
  ∀ f, is_function f → dom f ⊆ A → finite f →
  ∀ x,
    let 𝐑 := RightInterval x R f in
    let aᵣ := MinRight x R f in
    𝐑 ≠ ∅ → aᵣ ∈ dom f ∧ (x <ᵣ aᵣ) R ∧
    ∀y ∈ dom f, (x <ᵣ y) R → (aᵣ ≤ᵣ y) R.
Proof with eauto; try congruence.
  intros A R a [[Ha _] [Hda Hra]] Hlo.
  intros f Hf Hd Hfin x₀ 𝐑 aᵣ Hne.
  pose proof (finite_loset_has_min A R 𝐑) as [H Hle]...
  - intros x Hx. apply SepE1 in Hx. apply Hd...
  - apply (subset_of_finite_is_finite _ (dom f)). apply sep_sub.
    rewrite dom_eq_π1_repl... apply repl_finite...
  - apply SepE in H as [H1 H2]. repeat split...
    intros y Hy Hlt. assert (y ∈ 𝐑). apply SepI...
    apply Hle in H as []; [left|right]... apply SepE1 in H...
Qed.

Lemma left_nats :
  ∀ A R a, a: ω ⟺ A → loset A R → 
  ∀ B S b, b : ω ⟺ B → right_unbounded B S →
  ∀ f, is_function f → dom f ⊆ A → ran f ⊆ B → finite f →
  ∀ x,
    let 𝐋 := LeftInterval x R f in
    let N := LeftNats x R S b f in
    𝐋 ≠ ∅ → (Min Lt)[N] ∈ N.
Proof with eauto; try congruence.
  intros A R a Hba Hlo B S b Hbb Hubd.
  intros f Hf Hd Hr Hfin x₀ 𝐋 N Hne.
  assert (H := Hbb). destruct H as [Hib [_ Hrb]].
  apply (ω_min N); revgoals.
  intros x Hx. apply SepE1 in Hx...
  set (f[MaxLeft x₀ R f]) as y₀.
  assert (y₀ ∈ B). {
    apply Hr. eapply ranI. apply func_correct...
    eapply (max_left A R a)...
  }
  pose proof (Hubd y₀ H) as [y₁ [Hy₁ Hlt]].
  exists (b⁻¹[y₁]). apply SepI.
  - apply (ap_ran B)... apply bijection_is_func.
    apply inv_bijection...
  - rewrite inv_ran_reduction...
Qed.

Lemma right_nats :
  ∀ A R a, a: ω ⟺ A → loset A R → 
  ∀ B S b, b : ω ⟺ B → left_unbounded B S →
  ∀ f, is_function f → dom f ⊆ A → ran f ⊆ B → finite f →
  ∀ x,
    let 𝐑 := RightInterval x R f in
    let N := RightNats x R S b f in
    𝐑 ≠ ∅ → (Min Lt)[N] ∈ N.
Proof with eauto; try congruence.
  intros A R a Hba Hlo B S b Hbb Hubd.
  intros f Hf Hd Hr Hfin x₀ 𝐑 N Hne.
  assert (H := Hbb). destruct H as [Hib [_ Hrb]].
  apply (ω_min N); revgoals.
  intros x Hx. apply SepE1 in Hx...
  set (f[MinRight x₀ R f]) as y₀.
  assert (y₀ ∈ B). {
    apply Hr. eapply ranI. apply func_correct...
    eapply (min_right A R a)...
  }
  pose proof (Hubd y₀ H) as [y₁ [Hy₁ Hlt]].
  exists (b⁻¹[y₁]). apply SepI.
  - apply (ap_ran B)... apply bijection_is_func.
    apply inv_bijection...
  - rewrite inv_ran_reduction...
Qed.

Lemma mid_nats :
  ∀ A R a, a: ω ⟺ A → loset A R → 
  ∀ B S b, b : ω ⟺ B → loset B S → dense S →
  ∀ f, is_function f → dom f ⊆ A → ran f ⊆ B → finite f → op R S f →
  ∀ x,
    let 𝐋 := LeftInterval x R f in
    let 𝐑 := RightInterval x R f in
    let N := MidNats x R S b f in
    𝐋 ≠ ∅ → 𝐑 ≠ ∅ → (Min Lt)[N] ∈ N.
Proof with eauto; try congruence.
  intros A R a Hba HloR B S b Hbb HloS HdnS.
  intros f Hf Hd Hr Hfin Hop x₀ 𝐋 𝐑 N Hnel Hner.
  assert (H := Hbb). destruct H as [Hib [_ Hrb]].
  apply (ω_min N); revgoals.
  intros x Hx. apply SepE1 in Hx...
  set (MaxLeft x₀ R f) as aₗ.
  set (MinRight x₀ R f) as aᵣ.
  pose proof (HdnS (f[aₗ]) (f[aᵣ])) as [qₘ [H1 H2]]. {
    pose proof (max_left A R a) as [Haₗd [Hlt1 _]]...
    pose proof (min_right A R a) as [Haᵣd [Hlt2 _]]...
    eapply Hop... eapply relLt_tranr... apply HloR.
  }
  assert (Hqₘ: qₘ ∈ B). {
    apply HloS in H1. apply CProdE2 in H1 as [_ H]...
  }
  exists (b⁻¹[qₘ]). apply SepI...
  - apply (ap_ran B)... apply bijection_is_func.
    apply inv_bijection...
  - rewrite inv_ran_reduction...
Qed.

Lemma pairing :
  ∀ A R a, a: ω ⟺ A → loset A R → 
  ∀ B S b, b : ω ⟺ B → loset B S → unbounded B S → dense S →
  ∀ f, is_function f → dom f ⊆ A → ran f ⊆ B → finite f → op R S f →
  ∀ x, Pairing x R S b f ∈ B.
Proof with eauto.
  intros A R a Hba HloR B S b Hbb HloS [Hlu Hru] HdnS.
  intros f Hf Hd Hr Hfin Hop x₀.
  assert (H := Hbb). apply bijection_is_func in H as [Hmb _].
  unfold Pairing.
  set (LeftInterval x₀ R f) as 𝐋.
  set (RightInterval x₀ R f) as 𝐑.
  destruct (ixm (𝐋 = ∅)) as [HL|HL];
  destruct (ixm (𝐑 = ∅)) as [HR|HR];
  eapply ap_ran; neauto; eapply SepE1.
  - eapply (right_nats A R a)...
  - eapply (left_nats A R a)...
  - eapply (mid_nats A R a)...
Qed.

Lemma both_side_empty :
  ∀ A R, loset A R → ∀ f, dom f ⊆ A → ∀ x, x ∈ A →
    let 𝐋 := LeftInterval x R f in
    let 𝐑 := RightInterval x R f in
    𝐋 = ∅ → 𝐑 = ∅ → dom f ⊆ ⎨x⎬.
Proof with eauto; try congruence.
  intros A R Hlo f Hd x₀ Hx₀ 𝐋 𝐑 HL0 HR0.
  intros x Hx. cut (x = x₀). {
    intros H. rewrite H. apply SingI.
  }
  destruct (classic (x = x₀)) as [|Hnq]... exfalso.
  apply (lo_connected R A) in Hnq as []; revgoals...
  - eapply (EmptyNI 𝐑)... exists x. apply SepI...
  - eapply (EmptyNI 𝐋)... exists x. apply SepI...
Qed.

Lemma pairing_out :
  ∀ A R a, a: ω ⟺ A → loset A R → 
  ∀ B S b, b : ω ⟺ B → loset B S → unbounded B S → dense S →
  ∀ f, is_function f → dom f ⊆ A → ran f ⊆ B → finite f → op R S f →
  ∀x ∈ A, x ∉ dom f → Pairing x R S b f ∉ ran f.
Proof with eauto; try congruence.
  intros A R a Hba HloR B S b Hbb HloS [Hlu Hru] HdnS.
  intros f Hf Hd Hr Hfin Hop x₀ Hx₀ Hout Hin.
  assert (H := HloR). destruct H as [_ [HtrR _]].
  assert (HirR: irrefl R). eapply lo_irrefl...
  assert (H := Hba). apply bijection_is_func in H as [Hma [Hia Hra]].
  assert (H := Hma). destruct H as [Hfa [Hda _]].
  apply ranE in Hin as [x Hfx]. apply domI in Hfx as Hx.
  apply Hd in Hx as H. rewrite <- Hra in H.
  apply ranE in H as [k Hak]. apply domI in Hak as Hk.
  apply func_ap in Hak... apply func_ap in Hfx... subst x.
  destruct (classic (a[k] = x₀)) as [|Hnq]...
  unfold Pairing in Hfx.
  set (LeftInterval x₀ R f) as 𝐋.
  set (RightInterval x₀ R f) as 𝐑.
  set (LeftNats x₀ R S b f) as Nₗ.
  set (RightNats x₀ R S b f) as Nᵣ.
  set (MidNats x₀ R S b f) as Nₘ.
  unfold Pairing, PairRight, PairLeft, PairMid in Hfx.
  fold 𝐋 𝐑 Nₗ Nᵣ Nₘ in Hfx.
  destruct (ixm (𝐋 = ∅)) as [HL|HL];
  destruct (ixm (𝐑 = ∅)) as [HR|HR].
  - pose proof (both_side_empty A R HloR f Hd x₀ Hx₀ HL HR)...
    apply subset_of_single in H as [].
    + rewrite H in Hx. exfalso0.
    + rewrite H in Hout. apply SingNE in Hout...
  - assert (HNᵣ: (Min Lt)[Nᵣ] ∈ Nᵣ). eapply (right_nats A R a)...
    apply SepE2 in HNᵣ. rewrite <- Hfx in HNᵣ.
    pose proof min_right as [Haᵣ [Hlt Hle]]; revgoals...
    set (MinRight x₀ R f) as aᵣ.
    fold aᵣ in Haᵣ, Hlt, Hle, HNᵣ.
    apply (lo_connected R A) in Hnq as []; revgoals...
    * apply Hle in H... eapply (relLt_irrefl _ R)...
      eapply relLt_le_tranr; revgoals... eapply Hop...
    * eapply EmptyNI in HL... exists (a[k]). apply SepI...
  - assert (HNₗ: (Min Lt)[Nₗ] ∈ Nₗ). eapply (left_nats A R a)...
    apply SepE2 in HNₗ. rewrite <- Hfx in HNₗ.
    pose proof max_left as [Haₗ [Hlt Hle]]; revgoals...
    apply (lo_connected R A) in Hnq as []; revgoals...
    * eapply EmptyNI in HR... exists (a[k]). apply SepI...
    * apply Hle in H... eapply (relLt_irrefl _ R)...
      eapply relLt_le_tranr; revgoals... eapply Hop...
  - assert (HNₘ: (Min Lt)[Nₘ] ∈ Nₘ). eapply (mid_nats A R a)...
    apply SepE2 in HNₘ. rewrite <- Hfx in HNₘ.
    pose proof max_left as [Haₗ [Hltₗ Hleₗ]]; revgoals...
    pose proof min_right as [Haᵣ [Hltᵣ Hleᵣ]]; revgoals...
    destruct HNₘ as [Hlt1 Hlt2].
    apply (lo_connected R A) in Hnq as []; revgoals...
    * apply Hleᵣ in H... eapply (relLt_irrefl _ R)...
      eapply relLt_le_tranr; revgoals... eapply Hop...
    * apply Hleₗ in H... eapply (relLt_irrefl _ R)...
      eapply relLt_le_tranr; revgoals... eapply Hop...
Qed.

Lemma add_good :
  ∀ A R a, a: ω ⟺ A → loset A R → 
  ∀ B S b, b : ω ⟺ B → loset B S → unbounded B S → dense S →
  ∀ f, good A R B S f → ∀x ∈ A, x ∉ dom f →
  good A R B S (Add x R S b f).
Proof with eauto.
  intros A R a Hba HloR B S b Hbb HloS Hubd HdnS.
  intros f [Hinj [Hd [Hr [Hfin Hop]]]] x₀ Hx₀ Hout.
  assert (H := Hubd). destruct H as [Hlu Hru].
  assert (H := HloR). destruct H as [_ [HtrR _]].
  assert (H := HloS). destruct H as [_ [HtrS _]].
  assert (HirR: irrefl R). eapply lo_irrefl...
  assert (H := Hinj). destruct H as [Hf _].
  split; [|split; [|split; [|split]]].
  - apply add_point_injective... eapply (pairing_out A)...
  - intros x Hx. apply domE in Hx as [y Hp].
    apply BUnionE in Hp as [].
    + apply domI in H. apply Hd...
    + apply SingE in H. apply op_iff in H as [H _]; subst...
  - intros y Hy. apply ranE in Hy as [x Hp].
    apply BUnionE in Hp as [].
    + apply ranI in H. apply Hr...
    + apply SingE in H. apply op_iff in H as [_ H]; subst.
      eapply (pairing A)...
  - apply add_one_still_finite_2...
  - pose proof (add_point_func_ap f (dom f) (ran f)) as [H1 H2].
    split... apply Hout... eapply (pairing_out A)...
    intros x₁ Hx₁ x₂ Hx₂.
    apply domE in Hx₁ as [y₁ Hx₁].
    apply domE in Hx₂ as [y₂ Hx₂].
    apply BUnionE in Hx₁ as [Hx₁|Hx₁];
    apply BUnionE in Hx₂ as [Hx₂|Hx₂];
    apply domI in Hx₁; try rewrite dom_of_single_pair in Hx₁;
    apply domI in Hx₂; try rewrite dom_of_single_pair in Hx₂;
    unfold Add; [
      rewrite H1, H1|rewrite H1, H2|
      rewrite H2, H1|rewrite H2, H2
    ]... {
      apply SingE in Hx₂; subst. unfold Pairing.
      destruct (classic (x₁ = x₀)) as [|Hnq]. subst... exfalso...
      set (LeftInterval x₀ R f) as 𝐋.
      set (RightInterval x₀ R f) as 𝐑.
      destruct (ixm (𝐋 = ∅)) as [HL|HL];
      destruct (ixm (𝐑 = ∅)) as [HR|HR].
      - pose proof (both_side_empty A R HloR f Hd x₀ Hx₀ HL HR)...
        apply subset_of_single in H as []; rewrite H in Hx₁.
        exfalso0. exfalso. apply Hout. rewrite H...
      - split; intros Hlt.
        + exfalso. eapply EmptyNI in HL...
          exists x₁. apply SepI...
        + set (RightNats x₀ R S b f) as N.
          assert ((Min Lt)[N] ∈ N). eapply (right_nats A)...
          apply SepE2 in H.
          pose proof (min_right A) as [Haᵣd [_ Hle]]...
          apply (lo_connected R A) in Hnq as [H10|H01]; revgoals...
          exfalso. eapply (relLt_irrefl x₁ R)...
          eapply relLt_le_tranr... apply Hop... eapply relLt_tranr...
      - split; intros Hlt.
        + set (LeftNats x₀ R S b f) as N.
          assert ((Min Lt)[N] ∈ N). eapply (left_nats A)...
          apply SepE2 in H.
          pose proof (max_left A) as [Haₗd [_ Hle]]...
          apply Hle in Hlt as []...
          * eapply relLt_tranr... apply Hop...
          * subst...
        + apply (lo_connected R A) in Hnq as [H10|H01]; revgoals...
          exfalso. eapply EmptyNI in HR... exists x₁. apply SepI...
      - split; intros Hlt.
        + set (MidNats x₀ R S b f) as N.
          assert ((Min Lt)[N] ∈ N). eapply (mid_nats A)...
          apply SepE2 in H as [H _].
          pose proof (max_left A) as [Haₗd [_ Hle]]...
          apply Hle in Hlt as []...
          * eapply relLt_tranr... apply Hop...
          * subst...
        + set (MidNats x₀ R S b f) as N.
          assert ((Min Lt)[N] ∈ N). eapply (mid_nats A)...
          apply SepE2 in H as [_ H].
          pose proof (min_right A) as [Haᵣd [_ Hle]]...
          apply (lo_connected R A) in Hnq as [H10|H01]; revgoals...
          exfalso. eapply (relLt_irrefl x₁ R)...
          eapply relLt_le_tranr... apply Hop... eapply relLt_tranr...
    } {
      apply SingE in Hx₁; subst. unfold Pairing.
      destruct (classic (x₂ = x₀)) as [|Hnq]. subst... exfalso...
      set (LeftInterval x₀ R f) as 𝐋.
      set (RightInterval x₀ R f) as 𝐑.
      destruct (ixm (𝐋 = ∅)) as [HL|HL];
      destruct (ixm (𝐑 = ∅)) as [HR|HR].
      - pose proof (both_side_empty A R HloR f Hd x₀ Hx₀ HL HR)...
        apply subset_of_single in H as []; rewrite H in Hx₂.
        exfalso0. exfalso. apply Hout. rewrite H...
      - split; intros Hlt.
        + set (RightNats x₀ R S b f) as N.
          assert ((Min Lt)[N] ∈ N). eapply (right_nats A)...
          apply SepE2 in H.
          pose proof (min_right A) as [Haᵣd [_ Hle]]...
          apply Hle in Hlt as []...
          * eapply relLt_tranr... apply Hop...
          * subst...
        + apply (lo_connected R A) in Hnq as [H20|H02]; revgoals...
          exfalso. eapply EmptyNI in HL... exists x₂. apply SepI...
      - split; intros Hlt.
        + exfalso. eapply EmptyNI in HR...
          exists x₂. apply SepI...
        + set (LeftNats x₀ R S b f) as N.
          assert ((Min Lt)[N] ∈ N). eapply (left_nats A)...
          apply SepE2 in H.
          pose proof (max_left A) as [Haₗd [_ Hle]]...
          apply (lo_connected R A) in Hnq as [H20|H02]; revgoals...
          exfalso. eapply (relLt_irrefl x₂ R)...
          eapply relLe_lt_tranr... apply Hop... eapply relLt_tranr...
      - split; intros Hlt.
        + set (MidNats x₀ R S b f) as N.
          assert ((Min Lt)[N] ∈ N). eapply (mid_nats A)...
          apply SepE2 in H as [_ H].
          pose proof (min_right A) as [Haᵣd [_ Hle]]...
          apply Hle in Hlt as []...
          * eapply relLt_tranr... apply Hop...
          * subst...
        + set (MidNats x₀ R S b f) as N.
          assert ((Min Lt)[N] ∈ N). eapply (mid_nats A)...
          apply SepE2 in H as [H _].
          pose proof (max_left A) as [Haₗd [_ Hle]]...
          apply (lo_connected R A) in Hnq as [H20|H02]; revgoals...
          exfalso. eapply (relLt_irrefl x₂ R)...
          eapply relLe_lt_tranr... apply Hop... eapply relLt_tranr...
    } {
      apply SingE in Hx₁; apply SingE in Hx₂; subst.
      split; intros Hlt; exfalso;
      eapply relLt_irrefl; revgoals; eauto;
      eapply lo_irrefl...
    }
Qed.

Lemma add_ind :
  ∀ R a S b f, is_function a → is_function f →
  ∀n ∈ ω, a[n] ∉ dom f → a⟦n⟧ ⊆ dom f →
  a⟦n⁺⟧ ⊆ dom (Add a[n] R S b f).
Proof with eauto.
  intros R a Ha S b f Hf n Hn Hout Hsub x Hx.
  apply imgE in Hx as [k [Hk Hak]].
  apply BUnionE in Hk as [].
  - eapply domI. apply BUnionI1. apply func_correct...
    apply Hsub. eapply imgI...
  - apply SingE in H; subst.
    apply func_ap in Hak... subst x.
    eapply domI. apply BUnionI2. apply SingI.
Qed.

Lemma inv_good : ∀ A R B S f, good A R B S f → good B S A R f⁻¹.
Proof with eauto.
  intros A R B S f [Hinj [Hd [Hr [Hfin Hop]]]].
  split; [|split; [|split; [|split]]].
  - apply inv_injective...
  - rewrite inv_dom...
  - rewrite inv_ran...
  - rewrite inv_as_repl... apply repl_finite...
  - assert (Hf': is_function f⁻¹). apply inv_func_iff_sr. apply Hinj.
    intros x Hx y Hy. split; intros Hlt.
    + apply Hop.
      * eapply domI. rewrite inv_op. apply func_correct...
      * eapply domI. rewrite inv_op. apply func_correct...
      * rewrite inv_ran_reduction, inv_ran_reduction...
        rewrite <- inv_dom... rewrite <- inv_dom...
    + apply Hop in Hlt.
      * rewrite inv_ran_reduction, inv_ran_reduction in Hlt...
        rewrite <- inv_dom... rewrite <- inv_dom...
      * eapply domI. rewrite inv_op. apply func_correct...
      * eapply domI. rewrite inv_op. apply func_correct...
Qed.

(* 对任意可数无穷无界稠密线序集A和B，
  存在以ω为定义域的函数F作为A与B之间的部分来回嵌入的枚举 *)
(* For any countably infinite unbounded dense loset A and B,
  there exists a function F with domain ω as the enumeration of
  all partial back and forth embeddings between A and B *)
Lemma enumeration_of_partial_back_and_forth_embeddings :
  ∀ A R a, a: ω ⟺ A → loset A R → unbounded A R → dense R →
  ∀ B S b, b: ω ⟺ B → loset B S → unbounded B S → dense S →
  ∃ G, is_function G ∧ dom G = ω ∧ ∀n ∈ ω, injective (G[n]) ∧
    (a⟦½n⟧ ⊆ dom G[n] ∧ dom G[n] ⊆ A) ∧
    (b⟦½n⟧ ⊆ ran G[n] ∧ ran G[n] ⊆ B) ∧
    (∀ x y ∈ dom G[n], (x <ᵣ y) R ↔ (G[n][x] <ᵣ G[n][y]) S) ∧
    (∀m ∈ n, ∀x ∈ dom G[m], G[m][x] = G[n][x]) ∧
    (∀m ∈ n, ∀x ∈ dom G[n] - dom G[m], G[n][x] ∉ ran G[m]) ∧
    (∀m ∈ n, dom G[m] ⊆ dom G[n]).
Proof with neauto; try congruence.
  intros A R a Hba HloR Hur HdnR
         B S b Hbb HloS Hus HdnS.
  assert (H := HloR). destruct H as [_ [HtrR _]].
  assert (HirR: irrefl R). eapply lo_irrefl...
  assert (H := HloS). destruct H as [Hbr [HtrS _]].
  assert (HirS: irrefl S). eapply lo_irrefl...
  assert (H := Hba). apply bijection_is_func in H as [Hma [Hia Hra]].
  assert (H := Hbb). apply bijection_is_func in H as [Hmb [Hib Hrb]].
  assert (H := Hma). destruct H as [Hfa [Hda _]].
  assert (H := Hmb). destruct H as [Hfb [Hdb _]].
  set (λ f, ∀ x y ∈ dom f, (x <ᵣ y) R ↔ (f[x] <ᵣ f[y]) S) as op.
  set (⋃{λ X, X ⟶ B | X ∊ 𝒫 A}) as fs0.
  set (λ f, good A R B S f) as good.
  set {f ∊ fs0 | good} as fs.
  set (λ n f, Add a[n] R S b f) as Forth.
  set (λ n f, (Add b[n] S R a f⁻¹)⁻¹) as Back.
  set {p ∊ ω × fs | λ p,
    let n := π1 p in
    let f := π2 p in
    match (ixm (odd n)) with
    | inl _ => a⟦½n⁺⟧ ⊆ dom f ∧ b⟦½n⟧ ⊆ ran f
    | inr _ => a⟦½n⟧ ⊆ dom f ∧ b⟦½n⟧ ⊆ ran f
  end} as ps.
  set <0, ∅> as p₀.
  set (λ p,
    let n := π1 p in
    let f := π2 p in
    match (ixm (even n)) with
    | inl _ => match (ixm (a[½n] ∈ dom f)) with
      | inl _ => <n⁺, f>
      | inr _ => <n⁺, Forth ½n f>
      end
    | inr _ => match (ixm (b[½n] ∈ ran f)) with
      | inl _ => <n⁺, f>
      | inr _ => <n⁺, Back ½n f>
    end
  end) as BackAndForth.
  set (Func ps ps BackAndForth) as g.
  assert (Hgoodᶠ: ∀n ∈ ω, ∀ f, good f → a[n] ∉ dom f → good (Forth n f)). {
    intros n Hn f Hc Hout. eapply add_good... eapply ap_ran...
  }
  assert (Hgoodᵇ: ∀n ∈ ω, ∀ f, good f → b[n] ∉ ran f → good (Back n f)). {
    intros n Hn f Hc Hout. apply inv_good. eapply add_good...
    apply inv_good... eapply ap_ran... rewrite inv_dom...
  }
  assert (Hindᶠ: ∀n ∈ ω, ∀ f, good f → a[n] ∉ dom f →
    a⟦n⟧ ⊆ dom f → a⟦n⁺⟧ ⊆ dom (Forth n f)). {
    intros n Hn f Hg Hout Hsub. apply add_ind... apply Hg.
  }
  assert (Hindᵇ: ∀n ∈ ω, ∀ f, good f → b[n] ∉ ran f →
    b⟦n⟧ ⊆ ran f → b⟦n⁺⟧ ⊆ ran (Back n f)). {
    intros n Hn f Hg Hout Hsub.
    unfold Back. rewrite inv_ran. apply add_ind...
    apply inv_func_iff_sr. apply Hg.
    rewrite inv_dom... rewrite inv_dom...
  }
  assert (Hfsᶠ: ∀n ∈ ω, ∀ f, good f → a[n] ∉ dom f → a⟦n⟧ ⊆ dom f → Forth n f ∈ fs). {
    intros n Hn f Hg Hout Hsub.
    pose proof (Hgoodᶠ n Hn f Hg Hout) as H1.
    pose proof (Hindᶠ n Hn f Hg Hout Hsub) as H2.
    remember (Forth n f) as f'. assert (H := H1).
    destruct H as [[Hf _] [Hd [Hr _]]].
    apply SepI... apply UnionAx. exists (dom f' ⟶ B). split.
    - apply ReplAx. exists (dom f'). split... apply PowerAx...
    - apply arrowI. split...
  }
  assert (Hfsᵇ: ∀n ∈ ω, ∀ f, good f → b[n] ∉ ran f → b⟦n⟧ ⊆ ran f → Back n f ∈ fs). {
    intros n Hn f Hg Hout Hsub.
    pose proof (Hgoodᵇ n Hn f Hg Hout) as H1.
    pose proof (Hindᵇ n Hn f Hg Hout Hsub) as H2.
    remember (Back n f) as f'. assert (H := H1).
    destruct H as [[Hf _] [Hd [Hr _]]].
    apply SepI... apply UnionAx. exists (dom f' ⟶ B). split.
    - apply ReplAx. exists (dom f'). split... apply PowerAx...
    - apply arrowI. split...
  }
  assert (Hsubdf: ∀ n f, dom f ⊆ dom (Forth n f)). {
    intros n f x Hx.
    apply domE in Hx as [y Hp].
    eapply domI. unfold Forth. apply BUnionI1...
  }
  assert (Hsubrf: ∀ n f, ran f ⊆ ran (Forth n f)). {
    intros n f y Hy.
    apply ranE in Hy as [x Hp].
    eapply ranI. unfold Forth. apply BUnionI1...
  }
  assert (Hsubdb: ∀ n f, dom f ⊆ dom (Back n f)). {
    intros n f x Hx.
    apply domE in Hx as [y Hp].
    eapply domI. unfold Back. rewrite <- inv_op.
    apply BUnionI1. rewrite <- inv_op...
  }
  assert (Hsubrb: ∀ n f, ran f ⊆ ran (Back n f)). {
    intros n f y Hy.
    apply ranE in Hy as [x Hp].
    eapply ranI. unfold Back. rewrite <- inv_op.
    apply BUnionI1. rewrite <- inv_op...
  }
  assert (Hg: g: ps ⇒ ps). {
    apply meta_function. intros p Hp.
    apply SepE in Hp as [Hp H]. simpl in H.
    apply CProdE1 in Hp as [n [Hn [f [Hf Hp]]]].
    apply SepE2 in Hf as Hc0.
    assert (Hnp: n⁺ ∈ ω). apply ω_inductive...
    assert (Hhn: ½n ∈ ω). apply halve_ran...
    unfold BackAndForth. subst p. zfc_simple.
    destruct (ixm (even n)) as [He|Hne].
    - destruct (ixm (odd n)). {
        exfalso. apply (no_even_and_odd n)...
      }
      apply even_iff_suc_odd in He as Ho'...
      destruct H as [H1 H2].
      destruct (ixm (a[½n] ∈ dom f)); apply SepI.
      + apply CProdI...
      + zfc_simple. simpl. destruct (ixm (odd n⁺))... split.
        * rewrite odd_halve_suc, even_halve_suc...
          intros x Hx. rewrite img_suc in Hx...
          apply BUnionE in Hx as [].
          apply H1... apply SingE in H...
        * rewrite even_halve_suc...
      + apply CProdI...
      + zfc_simple. simpl. destruct (ixm (odd n⁺))... split.
        * rewrite odd_halve_suc, even_halve_suc...
        * rewrite even_halve_suc... eapply sub_tran...
    - destruct (ixm (odd n)) as [Ho|]; revgoals. {
        exfalso. destruct (even_or_odd n)...
      }
      apply odd_iff_suc_even in Ho as He'...
      assert (Hno': ¬ odd n⁺). {
        intros Hno. apply (no_even_and_odd n⁺)...
      }
      destruct H as [H1 H2].
      destruct (ixm (b[½n] ∈ ran f)); apply SepI.
      + apply CProdI...
      + zfc_simple. simpl. destruct (ixm (odd n⁺))...
        rewrite odd_halve_suc in *... split...
        intros y Hy. rewrite img_suc in Hy...
        apply BUnionE in Hy as [].
        apply H2... apply SingE in H...
      + apply CProdI...
      + zfc_simple. simpl. destruct (ixm (odd n⁺))... split.
        * eapply sub_tran...
        * rewrite odd_halve_suc...
  }
  pose proof (ω_recursion g ps p₀ Hg) as [h [Hh [Hh0 Hhnp]]]. {
    apply SepI.
    - apply CProdI... apply SepI.
      + apply UnionAx. exists (∅ ⟶ B). split.
        * apply ReplAx. exists ∅. split... apply empty_in_all_power.
        * apply arrowI. apply injection_is_func. apply empty_injection.
      + split. apply empty_injection...
        split. rewrite dom_of_empty. apply empty_sub_all.
        split. rewrite ran_of_empty. apply empty_sub_all.
        split. apply nat_finite...
        intros x Hx. rewrite dom_of_empty in Hx. exfalso0.
    - unfold p₀. zfc_simple.
      destruct (ixm (odd 0)). {
        exfalso. apply (no_even_and_odd 0)... split...
        exists 0. split... rewrite mul_0_r...
      }
      rewrite <- (mul_0_r 2), halve_even, img_0, img_0...
      split; apply empty_sub_all.
  }
  set (Func ω fs (λ n, π2 h[n])) as G.
  assert (Hhnps: ∀n ∈ ω, h[n] ∈ ps). {
    intros n Hn. destruct Hh as [Hh [Hd Hr]].
    rewrite <- Hd in Hn. apply domE in Hn as [y Hp].
    apply ranI in Hp as Hy. apply func_ap in Hp... apply Hr...
  }
  assert (HG: G: ω ⇒ fs). {
    apply meta_function. intros n Hn.
    apply Hhnps in Hn as Hhn. apply SepE1 in Hhn.
    apply CProdE1 in Hhn as [k [_ [f [Hf Heq]]]].
    rewrite Heq. zfc_simple.
  }
  assert (HGnfs: ∀n ∈ ω, G[n] ∈ fs). {
    intros n Hn. destruct HG as [HG [Hd Hr]].
    rewrite <- Hd in Hn. apply domE in Hn as [y Hp].
    apply ranI in Hp as Hy. apply func_ap in Hp... apply Hr...
  }
  assert (HgGn: ∀n ∈ ω, good G[n]). {
    intros n Hn. apply HGnfs in Hn... apply SepE2 in Hn...
  }
  assert (Hindex: ∀n ∈ ω, π1 h[n] = n). {
    intros n Hn.
    set {n ∊ ω | λ n, π1 h[n] = n} as N.
    ω_induction N Hn.
    - rewrite Hh0. unfold p₀. zfc_simple. rewrite zero...
    - rewrite Hhnp... unfold g.
      rewrite meta_func_ap; [|auto|apply Hhnps]...
      unfold BackAndForth. rewrite IH.
      destruct (ixm (even m)).
      + destruct (ixm (a[½m] ∈ dom (π2 h[m]))); zfc_simple.
      + destruct (ixm (b[½m] ∈ ran (π2 h[m]))); zfc_simple.
  }
  assert (HsubGn: ∀n ∈ ω, a⟦½n⟧ ⊆ dom G[n] ∧ b⟦½n⟧ ⊆ ran G[n]). {
    intros n Hn.
    apply Hhnps in Hn as Hhn.
    apply SepE in Hhn as [Hp H].
    apply CProdE1 in Hp as [k [_ [f [_ Heq]]]].
    unfold G. rewrite meta_func_ap...
    rewrite Heq in *. simpl in H. zfc_simple.
    replace k with n in *.
    - destruct (ixm (odd n)); destruct H as [H1 H2].
      + split... rewrite odd_halve_suc in H1...
        eapply sub_tran; revgoals... apply ex3_22_a...
      + split...
    - apply Hindex in Hn. rewrite Heq in Hn. zfc_simple.
  }
  assert (Hsubd0: ∀n ∈ ω, dom G[n] ⊆ dom G[n⁺]). {
    intros n Hn.
    assert (Hnp: n⁺ ∈ ω). apply ω_inductive...
    apply Hhnps in Hn as Hhn. apply SepE1 in Hhn as Hp.
    apply CProdE1 in Hp as [k [Hk [f [_ Heq]]]].
    unfold G. rewrite meta_func_ap, meta_func_ap, Hhnp...
    unfold g. rewrite meta_func_ap...
    unfold BackAndForth. rewrite Heq. zfc_simple.
    destruct (ixm (even k)).
    - destruct (ixm (a[½k] ∈ dom f)); zfc_simple...
    - destruct (ixm (b[½k] ∈ ran f)); zfc_simple...
  }
  assert (Hsubr0: ∀n ∈ ω, ran G[n] ⊆ ran G[n⁺]). {
    intros n Hn.
    assert (Hnp: n⁺ ∈ ω). apply ω_inductive...
    apply Hhnps in Hn as Hhn. apply SepE1 in Hhn as Hp.
    apply CProdE1 in Hp as [k [Hk [f [_ Heq]]]].
    unfold G. rewrite meta_func_ap, meta_func_ap, Hhnp...
    unfold g. rewrite meta_func_ap...
    unfold BackAndForth. rewrite Heq. zfc_simple.
    destruct (ixm (even k)).
    - destruct (ixm (a[½k] ∈ dom f)); zfc_simple...
    - destruct (ixm (b[½k] ∈ ran f)); zfc_simple...
  }
  assert (Hsubd: ∀n ∈ ω, ∀m ∈ n, dom G[m] ⊆ dom G[n]). {
    intros n Hn.
    set {n ∊ ω | λ n, ∀m ∈ n, dom G[m] ⊆ dom G[n]} as N.
    ω_induction N Hn; intros k Hk. exfalso0.
    apply BUnionE in Hk as [].
    - eapply sub_tran. apply IH... apply Hsubd0...
    - apply SingE in H; subst. apply Hsubd0...
  }
  assert (Hsubr: ∀n ∈ ω, ∀m ∈ n, ran G[m] ⊆ ran G[n]). {
    intros n Hn.
    set {n ∊ ω | λ n, ∀m ∈ n, ran G[m] ⊆ ran G[n]} as N.
    ω_induction N Hn; intros k Hk. exfalso0.
    apply BUnionE in Hk as [].
    - eapply sub_tran. apply IH... apply Hsubr0...
    - apply SingE in H; subst. apply Hsubr0...
  }
  assert (Hin0: ∀n ∈ ω, ∀x ∈ dom G[n], G[n][x] = G[n⁺][x]). {
    intros n Hn x Hx.
    assert (Hnp: n⁺ ∈ ω). apply ω_inductive...
    apply Hhnps in Hn as Hhn. apply SepE1 in Hhn.
    apply CProdE1 in Hhn as [k [Hk [f [Hf Heq]]]].
    unfold G in Hx. rewrite meta_func_ap in Hx...
    unfold G. rewrite meta_func_ap, meta_func_ap, Hhnp...
    unfold g. rewrite meta_func_ap; [|auto|apply Hhnps]...
    rewrite Heq in *. unfold BackAndForth. zfc_simple.
    apply SepE2 in Hf. destruct (ixm (even k)).
    - destruct (ixm (a[½k] ∈ dom f)); zfc_simple.
      destruct Hf as [Hinj [Hd [Hr [Hfin Hop]]]].
      symmetry. eapply add_point_func_ap... split...
      eapply (pairing_out A)... apply Hinj.
      eapply ap_ran... apply halve_ran...
    - destruct (ixm (b[½k] ∈ ran f)); zfc_simple.
      symmetry. unfold Back. apply inv_good in Hf as H.
      destruct H as [Hinj [Hd [Hr [Hfin Hop]]]].
      apply domE in Hx as [y Hp]. apply ranI in Hp as Hy.
      rewrite <- inv_dom in Hy, n1.
      rewrite <- (inv_inv f) at 2; [|apply Hf].
      rewrite inv_op in Hp.
      apply func_ap in Hp as Hap; [|apply Hinj].
      subst x. rewrite inv_dom_reduction...
      assert (Pairing b[½k] S R a f⁻¹ ∉ ran f⁻¹). {
        eapply (pairing_out B S b)...
        apply Hinj. eapply ap_ran... apply halve_ran...
      }
      replace (f⁻¹[y]) with ((Add b[½k] S R a f⁻¹)[y]).
      + rewrite inv_dom_reduction... apply add_point_injective...
        eapply domI. apply BUnionI1...
      + eapply add_point_func_ap... rewrite inv_dom, inv_ran.
        apply inv_bijection. split... apply Hf.
  }
  assert (Hout0: ∀n ∈ ω, ∀x ∈ dom G[n⁺] - dom G[n], G[n⁺][x] ∉ ran G[n]). {
    intros n Hn x Hx.
    assert (Hnp: n⁺ ∈ ω). apply ω_inductive...
    apply Hhnps in Hn as Hhn. apply SepE1 in Hhn.
    apply CProdE1 in Hhn as [k [Hk [f [Hf Hhn]]]].
    unfold G in Hx. rewrite meta_func_ap, meta_func_ap, Hhnp in Hx...
    unfold g in Hx. rewrite meta_func_ap in Hx; [|auto|apply Hhnps]...
    unfold G. rewrite meta_func_ap, meta_func_ap, Hhnp...
    unfold g. rewrite meta_func_ap; [|auto|apply Hhnps]...
    rewrite Hhn in *. unfold BackAndForth in *. zfc_simple.
    apply SepE2 in Hf. apply SepE in Hx as [Hx Hx'].
    destruct (ixm (even k)).
    - destruct (ixm (a[½k] ∈ dom f)); zfc_simple.
      apply domE in Hx as [y Hp].
      apply BUnionE in Hp as []. apply domI in H...
      apply SingE in H. apply op_iff in H as [H _]; subst x.
      assert (Pairing a[½k] R S b f ∉ ran f). {
        destruct Hf as [Hinj [Hd [Hr [Hfin Hop]]]].
        eapply (pairing_out A)... apply Hinj.
        eapply ap_ran... apply halve_ran...
      }
      replace ((Forth ½k f)[a[½k]]) with (Pairing a[½k] R S b f)...
      symmetry. eapply add_point_func_ap... split... apply Hf.
    - destruct (ixm (b[½k] ∈ ran f)); zfc_simple.
      apply domE in Hx as [y Hp].
      unfold Back in Hp. apply ranI in Hp as Hy.
      apply inv_op in Hp. apply BUnionE in Hp as [].
      apply inv_op in H. apply domI in H...
      apply SingE in H. apply op_iff in H as [H Heqx]; subst y.
      assert ((Add b[½k] S R a f⁻¹)[b[½k]] = x). {
        subst x. eapply add_point_func_ap...
        apply inv_bijection. split... apply Hf.
      }
      replace ((Back ½k f)[x]) with (b[½k])...
      rewrite <- inv_dom in n1. rewrite inv_ran in Hy.
      unfold Back. rewrite <- H, inv_dom_reduction...
      apply inv_good in Hf.
      destruct Hf as [Hinj [Hd [Hr [Hfin Hop]]]].
      apply add_point_injective... eapply (pairing_out B)...
      apply Hinj. eapply ap_ran... apply halve_ran...
  }
  assert (Hin: ∀n ∈ ω, ∀m ∈ n, ∀x ∈ dom G[m], (G[m])[x] = (G[n])[x]). {
    intros n Hn.
    set {n ∊ ω | λ n, ∀k ∈ n, ∀x ∈ dom G[k], G[k][x] = G[n][x]} as N.
    ω_induction N Hn; intros k Hkn x Hx. exfalso0.
    apply BUnionE in Hkn as [].
    + rewrite IH... apply Hin0... eapply Hsubd...
    + apply SingE in H; subst k. apply Hin0...
  }
  assert (Hout: ∀n ∈ ω, ∀m ∈ n, ∀x ∈ dom G[n] - dom G[m], (G[n])[x] ∉ ran G[m]). {
    intros n Hn.
    set {n ∊ ω | λ n, ∀m ∈ n, ∀x ∈ dom G[n] - dom G[m], G[n][x] ∉ ran G[m]} as N.
    ω_induction N Hn; intros k Hkn x Hx. exfalso0.
    apply BUnionE in Hkn as [Hkm|Hkm].
    - apply SepE in Hx as [Hx Hx'].
      replace (dom G[m⁺]) with (dom G[m] ∪ (dom G[m⁺] - dom G[m])) in Hx; revgoals. {
        rewrite ex2_11_2. apply ex2_17_1_3. eapply Hsubd0...
      }
      apply BUnionE in Hx as [Hx|Hx].
      + assert (x ∈ dom G[m] - dom G[k]). apply SepI...
        apply IH in H... intros H1. apply H.
        assert (Hk: k ∈ ω). eapply ω_trans...
        destruct (HgGn k Hk) as [[Hfk _] _].
        apply ranE in H1 as [w Hp]. apply domI in Hp as Hw.
        apply func_ap in Hp... rewrite Hin0...
        apply (ranI _ w). rewrite <- Hp. apply func_correct...
      + apply Hout0 in Hx... intros H. apply Hx. eapply Hsubr...
    - apply SingE in Hkm; subst k. apply Hout0...
  }
  exists G. split. apply HG. split. apply HG.
  intros n Hn. split. apply HgGn...
  split. split. apply HsubGn... apply HgGn...
  split. split. apply HsubGn... apply HgGn...
  split. apply HgGn... repeat split.
  apply Hin... apply Hout... apply Hsubd...
Qed.

Open Scope Nat_scope.

(* 所有部分来回嵌入的并是完整同构 *)
Lemma union_of_partial_back_and_forth_embeddings :
  ∀ A R, ω ≈ A → loset A R → dense R → unbounded A R →
  ∀ B S, ω ≈ B → loset B S → dense S → unbounded B S →
  ∃ f, f: A ⟺ B ∧ ∀ x y ∈ A, (x <ᵣ y) R ↔ (f[x] <ᵣ f[y]) S.
Proof with neauto; try congruence.
  intros A R [a Hba] HloR HdnR HubdR B S [b Hbb] HloS HdnS HubdS.
  assert (H := Hba). apply bijection_is_func in H as [Hma [Hia Hra]].
  assert (H := Hma). destruct H as [Hfa [Hda _]].
  assert (H := Hbb). apply bijection_is_func in H as [Hmb [Hib Hrb]].
  assert (H := Hmb). destruct H as [Hfb [Hdb _]].
  pose proof (enumeration_of_partial_back_and_forth_embeddings A)
    as [G [HfG [HdG Hstar]]]...
  set (⋃ᵢ (Ap G)) as f.
  assert (Hf: f: A ⟺ B). {
    split; split.
    - (* is_function f *)
      split. intros p Hp.
      apply IFUnionE in Hp as [n [Hn Hp]]. apply (Hstar n Hn)...
      intros x Hx. rewrite <- unique_existence.
      split. apply domE in Hx...
      intros y1 y2 H1 H2.
      apply IFUnionE in H1 as [n [Hn H1]].
      apply IFUnionE in H2 as [m [Hm H2]].
      pose proof (Hstar n Hn) as [Hi1 [_ [_ [_ [Hin1 _]]]]].
      pose proof (Hstar m Hm) as [Hi2 [_ [_ [_ [Hin2 _]]]]].
      apply domI in H1 as Hx1.
      apply domI in H2 as Hx2.
      apply func_ap in H1; [|apply Hi1].
      apply func_ap in H2; [|apply Hi2]. subst y1 y2.
      destruct (classic (m = n))...
      apply nat_connected in H as []...
      symmetry. apply Hin1...
    - (* single_rooted f *)
      intros y Hy. rewrite <- unique_existence.
      split. apply ranE in Hy...
      intros y1 y2 H1 H2.
      apply IFUnionE in H1 as [n [Hn H1]].
      apply IFUnionE in H2 as [m [Hm H2]].
      pose proof (Hstar n Hn) as [Hi1 [_ [_ [_ [Hin1 [Hout1 _]]]]]].
      pose proof (Hstar m Hm) as [Hi2 [_ [_ [_ [Hin2 [Hout2 _]]]]]].
      apply domI in H1 as Hx1.
      apply domI in H2 as Hx2.
      apply func_ap in H1; [|apply Hi1].
      apply func_ap in H2; [|apply Hi2]. subst y.
      destruct (classic (m = n)). eapply injectiveE...
      apply nat_connected in H as []...
      + destruct (classic (y1 ∈ dom G[m])).
        * erewrite <- Hin1 in H2... apply injectiveE in H2...
        * exfalso. apply (Hout1 m H y1).
          apply SepI... rewrite <- H2. eapply ranI.
          apply func_correct... apply Hi2.
      + destruct (classic (y2 ∈ dom G[n])).
        * erewrite <- Hin2 in H2... apply injectiveE in H2...
        * exfalso. apply (Hout2 n H y2).
          apply SepI... rewrite H2. eapply ranI.
          apply func_correct... apply Hi1.
    - (* dom f = A *)
      apply ExtAx. split; intros Hx.
      + apply domE in Hx as [y Hp].
        apply IFUnionE in Hp as [n [Hn Hp]].
        apply domI in Hp. eapply Hstar...
      + set (a⁻¹[x]) as n.
        assert (Hnp: n⁺ ∈ ω). {
          apply ω_inductive. eapply ap_ran...
          apply bijection_is_func. apply inv_bijection...
        }
        assert (H2np: 2⋅n⁺ ∈ ω). apply mul_ran...
        apply (domI _ _ G[2⋅n⁺][x]). apply UnionAx.
        exists (G[2⋅n⁺]). split. eapply ReplI...
        apply func_correct... apply Hstar...
        apply Hstar... apply (imgI _ _ n)...
        * rewrite halve_even...
        * rewrite inv_op. apply func_correct.
          apply inv_func_iff_sr. apply Hia. rewrite inv_dom...
    - (* ran f = B *)
      apply ExtAx. intros y. split; intros Hy.
      + apply ranE in Hy as [x Hp].
        apply IFUnionE in Hp as [n [Hn Hp]].
        apply ranI in Hp. eapply Hstar...
      + set (b⁻¹[y]) as n.
        assert (Hnp: n⁺ ∈ ω). {
          apply ω_inductive. eapply ap_ran...
          apply bijection_is_func. apply inv_bijection...
        }
        assert (H2np: 2⋅n⁺ ∈ ω). apply mul_ran...
        apply (ranI _ G[2⋅n⁺]⁻¹[y]). apply UnionAx.
        exists (G[2⋅n⁺]). split. eapply ReplI...
        apply inv_op. apply func_correct...
        apply inv_func_iff_sr... apply Hstar...
        rewrite inv_dom. apply Hstar... apply (imgI _ _ n)...
        * rewrite halve_even...
        * rewrite inv_op. apply func_correct.
          apply inv_func_iff_sr. apply Hib. rewrite inv_dom...
  }
  assert (Hap: ∀x ∈ A, ∃n ∈ ω, <x, f[x]> ∈ G[n]). {
    intros x Hx. destruct Hf as [[Hf _] [Hd _]].
    apply IFUnionE... fold f. apply func_correct...
  }
  exists f. split...
  intros x Hx y Hy.
  apply Hap in Hx as [n [Hn H1]]. apply domI in H1 as Hx.
  apply Hap in Hy as [m [Hm H2]]. apply domI in H2 as Hy.
  pose proof (Hstar n Hn) as [[Hf1 _] [_ [_ [Hop1 [Hin1 [_ Hsub1]]]]]].
  pose proof (Hstar m Hm) as [[Hf2 _] [_ [_ [Hop2 [Hin2 [_ Hsub2]]]]]].
  apply func_ap in H1... rewrite <- H1.
  apply func_ap in H2... rewrite <- H2.
  destruct (classic (n = m)). {
    subst m. split; intros Hlt; apply Hop1...
  }
  apply nat_connected in H as []...
  - assert (Hxm: x ∈ dom G[m]). eapply Hsub2... rewrite Hin2...
  - assert (Hyn: y ∈ dom G[n]). eapply Hsub1... rewrite (Hin1 m H)...
Qed.

(* ex8_18 任意两个可数无穷无界稠密线序同构 *)
Theorem countable_unbounded_dense_loset_iso : ∀ S T,
  ω ≈ A S → unbounded (A S) (R S) → dense (R S) →
  ω ≈ A T → unbounded (A T) (R T) → dense (R T) → S ≅ T.
Proof.
  intros S T HqnS HubdS HdnsS HqnT HubdT HdnsT.
  apply union_of_partial_back_and_forth_embeddings; auto.
Qed.
