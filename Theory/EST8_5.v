(** Adapted from "Elements of Set Theory" Chapter 8 **)
(** Coq coding by choukh, May 2021 **)

Require Import ZFC.Lib.LoStruct.
Require Export ZFC.Theory.EST8_4.
Import WoStruct.
Import StructureCasting.

(*** EST第八章5：良序结构上的序类型算术 ***)

(* 结构不交化 *)
Definition WoDisj_A :=
  λ S i, (A S × ⎨i⎬).
Definition WoDisj_R :=
  λ S i, {<<π1 p, i>, <π2 p, i>> | p ∊ R S}.

Lemma woDisj_is_binRel :
  ∀ S i, is_binRel (WoDisj_R S i) (WoDisj_A S i).
Proof.
  intros S i x Hx. destruct (wo S) as [Hbr _].
  apply ReplAx in Hx as [p [Hp Hx]]. apply Hbr in Hp.
  apply CPrdE1 in Hp as [a [Ha [b [Hb Hp]]]].
  subst. zfc_simple. apply CPrdI; apply CPrdI; auto.
Qed.

Lemma woDisj_tranr : ∀ S i, tranr (WoDisj_R S i).
Proof.
  intros S i x y z Hxy Hyz.
  destruct (wo S) as [[Hbr [Htr _]] _].
  apply ReplAx in Hxy as [p [Hp Hxy]]. apply Hbr in Hp as H1.
  apply ReplAx in Hyz as [q [Hq Hyz]]. apply Hbr in Hq as H2.
  apply CPrdE1 in H1 as [a [Ha [b [Hb H1]]]].
  apply CPrdE1 in H2 as [c [Hc [d [Hd H2]]]].
  apply op_iff in Hxy as []; subst.
  apply op_iff in Hyz as []; subst. zfc_simple.
  apply op_iff in H as []; subst.
  apply ReplAx. exists <a, d>. split; zfc_simple. eapply Htr; eauto.
Qed.

Lemma woDisj_irrefl : ∀ S i, irrefl (WoDisj_R S i).
Proof.
  intros S i x Hp. destruct (wo S) as [Hbr _].
  apply ReplAx in Hp as [p [Hp Heq]]. apply Hbr in Hp as H.
  apply CPrdE1 in H as [a [Ha [b [Hb H]]]]. subst. zfc_simple.
  apply op_iff in Heq as []; subst.
  apply op_iff in H0 as []; subst.
  eapply lo_irrefl; eauto.
Qed.

Lemma woDisj_connected : ∀ S i,
  connected (WoDisj_R S i) (WoDisj_A S i).
Proof with auto.
  intros S i x Hx y Hy Hnq. destruct (wo S) as [Hlo _].
  apply CPrdE1 in Hx as [a [Ha [b [Hb Heqx]]]].
  apply CPrdE1 in Hy as [c [Hc [d [Hd Heqy]]]].
  apply SingE in Hb; apply SingE in Hd; subst.
  destruct (classic (a = c)) as [|Hnq']. subst. exfalso...
  eapply (lo_connected _ _ Hlo) in Hnq' as []...
  left. apply ReplAx. exists <a, c>. split; zfc_simple.
  right. apply ReplAx. exists <c, a>. split; zfc_simple.
Qed.

Lemma woDisj_loset :
  ∀ S i, loset (WoDisj_A S i) (WoDisj_R S i).
Proof.
  intros S i.
  apply loset_iff_connected_poset. repeat split.
  apply woDisj_connected. apply woDisj_is_binRel.
  eapply binRel_is_rel. apply woDisj_is_binRel.
  apply woDisj_tranr. apply woDisj_irrefl.
Qed.

Lemma woDisj_woset :
  ∀ S i, woset (WoDisj_A S i) (WoDisj_R S i).
Proof with auto.
  intros S i. split. apply woDisj_loset.
  intros B Hne Hsub. destruct Hne as [b Hb].
  apply Hsub in Hb as H.
  apply CPrdE1 in H as [a [Ha [c [Hc H]]]].
  apply SingE in Hc; subst.
  destruct (wo S) as [_ Hmin].
  pose proof (Hmin {π1 p | p ∊ B}) as [m [Hm Hle]].
  - exists a. apply ReplAx. exists <a, i>. split... zfc_simple.
  - intros x Hx.
    apply ReplAx in Hx as [p [Hp Hx]]. apply Hsub in Hp.
    apply CPrdE1 in Hp as [u [Hu [v [_ Hp]]]]. subst. zfc_simple.
  - exists <m, i>. split.
    + apply ReplAx in Hm as [p [Hp Hx]]. apply Hsub in Hp as H.
      apply CPrdE1 in H as [u [Hu [v [Hv H]]]].
      apply SingE in Hv; subst. zfc_simple.
    + intros x Hx. apply Hsub in Hx as H.
      apply CPrdE1 in H as [u [Hu [v [Hv H]]]].
      apply SingE in Hv; subst.
      assert (Hu': u ∈ {π1 p | p ∊ B}). {
        apply ReplAx. exists <u, i>. split... zfc_simple.
      }
      apply Hle in Hu' as [].
      * left. apply ReplAx. exists <m, u>. split... zfc_simple.
      * right. congruence.
Qed.

Definition WoDisj :=
  λ S i, constr (WoDisj_A S i) (WoDisj_R S i) (woDisj_woset S i).

Lemma woDisj_iso : ∀ S i, S ≅ WoDisj S i.
Proof with auto.
  intros S i.
  set (Func (A S) (WoDisj_A S i) (λ x, <x, i>)) as f.
  assert (Hbi: f : A S ⟺ A (WoDisj S i)). {
    apply meta_bijection.
    - intros x Hx. apply CPrdI...
    - intros x1 H1 x2 H2. apply op_iff.
    - intros y Hy. apply CPrdE1 in Hy as [a [Ha [b [Hb Hy]]]].
      apply SingE in Hb. subst. exists a. split...
  }
  apply bijection_is_func in Hbi as Hf. destruct Hf as [Hf _].
  exists f. split... intros x Hx y Hy. split; intros Hlt.
  - apply ReplAx. exists <x, y>. split... zfc_simple.
    unfold f. rewrite meta_func_ap, meta_func_ap...
  - apply ReplAx in Hlt as [p [Hp Heq]].
    unfold f in Heq. rewrite meta_func_ap, meta_func_ap in Heq...
    apply op_iff in Heq as [H1 H2].
    apply op_iff in H1 as []; subst.
    apply op_iff in H2 as []; subst.
    destruct (wo S) as [Hbr _]. apply Hbr in Hp as H.
    apply CPrdE1 in H as [a [Ha [b [Hb H]]]].
    subst. zfc_simple...
Qed.

Lemma woDisj_disjoint : ∀ S T i j, i ≠ j →
  disjoint (A (WoDisj S i)) (A (WoDisj T j)).
Proof. intros S T i j Hnq. apply cprd_disjointify; auto. Qed.

Definition WoAdd_R := λ S T,
  R S ∪ R T ∪ (A S × A T).
Notation "S ⨁ T" := (WoAdd_R S T) (at level 70) : WoStruct_scope.

Lemma woAdd_is_binRel : ∀ S T, is_binRel (S ⨁ T) (A S ∪ A T).
Proof with auto.
  intros S T x Hx.
  destruct (wo S) as [[HbrS _] _].
  destruct (wo T) as [[HbrT _] _].
  apply BUnionE in Hx as [].
  - apply BUnionE in H as []; [apply HbrS in H|apply HbrT in H];
    apply CPrdE1 in H as [a [Ha [b [Hb H]]]]; subst.
    apply CPrdI; apply BUnionI1...
    apply CPrdI; apply BUnionI2...
  - apply CPrdE1 in H as [a [Ha [b [Hb H]]]]; subst;
    apply CPrdI; [apply BUnionI1|apply BUnionI2]...
Qed.

Lemma woAdd_tranr : ∀ S T, disjoint (A S) (A T) → tranr (S ⨁ T).
Proof with eauto.
  intros S T Hdj x y z Hxy Hyz.
  destruct (wo S) as [[HbrS [HtrS _]] _].
  destruct (wo T) as [[HbrT [HtrT _]] _].
  apply BUnionE in Hxy as [Hxy|Hxy];
  apply BUnionE in Hyz as [Hyz|Hyz].
  - apply BUnionE in Hxy as [Hxy|Hxy];
    apply BUnionE in Hyz as [Hyz|Hyz].
    + apply BUnionI1. apply BUnionI1. eapply HtrS...
    + apply HbrS in Hxy. apply CPrdE2 in Hxy as [Hx _].
      apply HbrT in Hyz. apply CPrdE2 in Hyz as [_ Hz].
      apply BUnionI2. apply CPrdI...
    + apply HbrT in Hxy. apply CPrdE2 in Hxy as [_ H1].
      apply HbrS in Hyz. apply CPrdE2 in Hyz as [H2 _].
      exfalso. eapply disjointE...
    + apply BUnionI1. apply BUnionI2. eapply HtrT...
  - apply BUnionE in Hxy as [Hxy|Hxy].
    + apply HbrS in Hxy. apply CPrdE2 in Hxy as [Hx _].
      apply CPrdE2 in Hyz as [_ Hz].
      apply BUnionI2. apply CPrdI...
    + apply HbrT in Hxy. apply CPrdE2 in Hxy as [_ H1].
      apply CPrdE2 in Hyz as [H2 _].
      exfalso. eapply disjointE...
  - apply BUnionE in Hyz as [Hyz|Hyz].
    + apply HbrS in Hyz. apply CPrdE2 in Hyz as [H1 _].
      apply CPrdE2 in Hxy as [_ H2].
      exfalso. eapply disjointE...
    + apply HbrT in Hyz. apply CPrdE2 in Hyz as [_ Hz].
      apply CPrdE2 in Hxy as [Hx _].
      apply BUnionI2. apply CPrdI...
  - apply CPrdE2 in Hxy as [_ H1].
    apply CPrdE2 in Hyz as [H2 _].
    exfalso. eapply disjointE...
Qed.

Lemma woAdd_irrefl : ∀ S T, disjoint (A S) (A T) → irrefl (S ⨁ T).
Proof with eauto.
  intros S T Hdj x H.
  apply BUnionE in H as [].
  - apply BUnionE in H as [].
    + eapply lo_irrefl... apply wo.
    + eapply lo_irrefl... apply wo.
  - apply CPrdE1 in H as [a [Ha [b [Hb Heq]]]].
    apply op_iff in Heq as []; subst.
    exfalso. eapply disjointE...
Qed.

Lemma woAdd_connected : ∀ S T, connected (S ⨁ T) (A S ∪ A T).
Proof with auto.
  intros S T x Hx y Hy Hnq.
  apply BUnionE in Hx as [Hx|Hx];
  apply BUnionE in Hy as [Hy|Hy].
  - eapply (lo_connected _ _ (proj1 (wo S))) in Hnq as []...
    left. apply BUnionI1. apply BUnionI1...
    right. apply BUnionI1. apply BUnionI1...
  - left. apply BUnionI2. apply CPrdI...
  - right. apply BUnionI2. apply CPrdI...
  - eapply (lo_connected _ _ (proj1 (wo T))) in Hnq as []...
    left. apply BUnionI1. apply BUnionI2...
    right. apply BUnionI1. apply BUnionI2...
Qed.

Lemma woAdd_loset : ∀ S T,
  let S' := WoDisj S 0 in
  let T' := WoDisj T 1 in
  loset (A S' ∪ A T') (S' ⨁ T').
Proof.
  intros S T.
  apply loset_iff_connected_poset. repeat split.
  - apply woAdd_connected.
  - apply woAdd_is_binRel.
  - eapply binRel_is_rel. apply woAdd_is_binRel.
  - apply woAdd_tranr. apply woDisj_disjoint. auto.
  - apply woAdd_irrefl. apply woDisj_disjoint. auto.
Qed.

Theorem woAdd_woset : ∀ S T,
  let S' := WoDisj S 0 in
  let T' := WoDisj T 1 in
  woset (A S' ∪ A T') (S' ⨁ T').
Proof with eauto; try congruence.
  intros S T. split. apply woAdd_loset.
  intros B Hne Hsub.
  destruct (classic (B ∩ A (WoDisj S 0) = ∅)) as [H0|H0].
  - destruct Hne as [b Hb]. apply Hsub in Hb as H.
    apply BUnionE in H as [];
    apply CPrdE1 in H as [a [Ha [c [Hc H]]]];
    apply SingE in Hc; subst. {
      exfalso. apply EmptyNI in H0...
      exists <a, 0>. apply BInterI... apply CPrdI...
    }
    destruct (wo T) as [_ Hmin].
    pose proof (Hmin {π1 p | p ∊ B ∩ A (WoDisj T 1)}) as [m [Hm Hle]].
    + exists a. apply ReplAx. exists <a, 1>. split.
      apply BInterI... apply CPrdI... zfc_simple.
    + intros x Hx.
      apply ReplAx in Hx as [p [Hp Hx]].
      apply BInterE in Hp as [_ Hp].
      apply CPrdE1 in Hp as [u [Hu [v [_ Hp]]]]. subst. zfc_simple.
    + apply ReplAx in Hm as [p [Hp Hx]].
      apply BInterE in Hp as [H1 H2].
      apply CPrdE1 in H2 as [s [Hs [t [Ht H]]]].
      apply SingE in Ht; subst; zfc_simple.
      exists <s, 1>. split...
      intros x Hx. apply Hsub in Hx as H.
      apply BUnionE in H as [];
      apply CPrdE1 in H as [u [Hu [v [Hv H]]]];
      apply SingE in Hv; subst.
      * exfalso. apply EmptyNI in H0...
        exists <u, 0>. apply BInterI... apply CPrdI...
      * assert (Hu': u ∈ {π1 p | p ∊ B ∩ A (WoDisj T 1)}). {
          apply ReplAx. exists <u, 1>. split.
          apply BInterI... apply CPrdI... zfc_simple.
        }
        apply Hle in Hu' as []; [left|right]...
        apply BUnionI1. apply BUnionI2.
        apply ReplAx. exists <s, u>. split... zfc_simple.
  - apply EmptyNE in H0 as [b Hb].
    apply BInterE in Hb as [Hb H].
    apply CPrdE1 in H as [a [Ha [c [Hc H]]]];
    apply SingE in Hc; subst.
    destruct (wo S) as [_ Hmin].
    pose proof (Hmin {π1 p | p ∊ B ∩ A (WoDisj S 0)}) as [m [Hm Hle]].
    + exists a. apply ReplAx. exists <a, 0>. split.
      apply BInterI... apply CPrdI... zfc_simple.
    + intros x Hx.
      apply ReplAx in Hx as [p [Hp Hx]].
      apply BInterE in Hp as [_ Hp].
      apply CPrdE1 in Hp as [u [Hu [v [_ Hp]]]]. subst. zfc_simple.
    + apply ReplAx in Hm as [p [Hp Hx]].
      apply BInterE in Hp as [H1 H2].
      apply CPrdE1 in H2 as [s [Hs [t [Ht H]]]].
      apply SingE in Ht; subst; zfc_simple.
      exists <s, 0>. split...
      intros x Hx. apply Hsub in Hx as H.
      apply BUnionE in H as [];
      apply CPrdE1 in H as [u [Hu [v [Hv H]]]];
      apply SingE in Hv; subst.
      * assert (Hu': u ∈ {π1 p | p ∊ B ∩ A (WoDisj S 0)}). {
          apply ReplAx. exists <u, 0>. split.
          apply BInterI... apply CPrdI... zfc_simple.
        }
        apply Hle in Hu' as []; [left|right]...
        apply BUnionI1. apply BUnionI1.
        apply ReplAx. exists <s, u>. split... zfc_simple.
      * left. apply BUnionI2. apply CPrdI; apply CPrdI...
Qed.

(* 字典序 *)
Definition WoMul_R := λ S T, BinRel (A S × A T) (λ p1 p2,
  (π2 p1 <ᵣ π2 p2) (R T) ∨
  (π1 p1 <ᵣ π1 p2) (R S) ∧ π2 p1 = π2 p2
).
Notation "S * T" := (WoMul_R S T) : WoStruct_scope.

Lemma woMul_is_binRel : ∀ S T, is_binRel (S * T) (A S × A T).
Proof.
  intros S T x Hx.
  apply binRelE1 in Hx as [a [Ha [b [Hb [Hx _]]]]].
  subst x. apply CPrdI; auto.
Qed.

Lemma woMul_tranr : ∀ S T, tranr (S * T).
Proof with eauto.
  intros S T x y z Hxy Hyz.
  destruct (wo S) as [[_ [HtrS _]] _].
  destruct (wo T) as [[_ [HtrT _]] _].
  apply binRelE2 in Hxy as [Hx [Hy [Hxy|[Hxy H1]]]];
  apply binRelE2 in Hyz as [_  [Hz [Hyz|[Hyz H2]]]]; apply binRelI...
  - left. eapply HtrT...
  - left. congruence.
  - left. congruence.
  - right. split. eapply HtrS... congruence.
Qed.

Lemma woMul_irrefl : ∀ S T, irrefl (S * T).
Proof.
  intros S T x H.
  apply binRelE2 in H as [Hx [_ [H|[H _]]]];
  (eapply lo_irrefl; [apply wo|]); eauto.
Qed.

Lemma woMul_connected : ∀ S T, connected (S * T) (A S × A T).
Proof with auto.
  intros S T x Hx y Hy Hnq.
  apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]].
  apply CPrdE1 in Hy as [c [Hc [d [Hd Hy]]]]. subst.
  destruct (classic (a = c)); destruct (classic (b = d)).
  - exfalso. apply Hnq. apply op_iff...
  - eapply (lo_connected _ _ (proj1 (wo T))) in H0 as []; auto;
    [left|right]; (apply binRelI; [apply CPrdI..|zfc_simple])...
  - eapply (lo_connected _ _ (proj1 (wo S))) in H as []; auto;
    [left|right]; (apply binRelI; [apply CPrdI..|zfc_simple])...
  - eapply (lo_connected _ _ (proj1 (wo T))) in H0 as []; auto;
    [left|right]; (apply binRelI; [apply CPrdI..|zfc_simple])...
Qed.

Lemma woMul_loset : ∀ S T, loset (A S × A T) (S * T).
Proof.
  intros S T.
  apply loset_iff_connected_poset. repeat split.
  - apply woMul_connected.
  - apply woMul_is_binRel.
  - eapply binRel_is_rel. apply woMul_is_binRel.
  - apply woMul_tranr.
  - apply woMul_irrefl.
Qed.

Theorem woMul_woset : ∀ S T, woset (A S × A T) (S * T).
Proof with eauto; try congruence.
  intros S T. split. apply woMul_loset.
  intros B [pₓ Hpₓ] Hsub. apply Hsub in Hpₓ as H.
  apply CPrdE1 in H as [aₓ [Haₓ [bₓ [Hbₓ Heq]]]]. subst.
  destruct (wo S) as [_ HminS].
  destruct (wo T) as [_ HminT].
  pose proof (HminT {π2 p | p ∊ B}) as [b₀ [Hb₀ Hleb₀]]. {
    exists bₓ. apply ReplAx. exists <aₓ, bₓ>. split... zfc_simple.
  } {
    intros x Hx. apply ReplAx in Hx as [p [Hp Hx]]. apply Hsub in Hp.
    apply CPrdE1 in Hp as [a [_ [b [Hb H]]]]. subst. zfc_simple.
  }
  set {p ∊ B | π2 p = b₀} as B₀.
  pose proof (HminS {π1 p | p ∊ B₀}) as [a₀ [Ha₀ Hlea₀]]. {
    apply ReplAx in Hb₀ as [p [Hp Hb₀]]. apply Hsub in Hp as H.
    apply CPrdE1 in H as [a [Ha [b [Hb H]]]]. subst. zfc_simple.
    exists a. apply ReplAx. exists <a, b>. split.
    apply SepI... zfc_simple.
  } {
    intros x Hx. apply ReplAx in Hx as [p [Hp Hx]].
    apply SepE1 in Hp. apply Hsub in Hp.
    apply CPrdE1 in Hp as [a [Ha [b [_ H]]]]. subst. zfc_simple.
  }
  apply ReplAx in Ha₀ as [p [Hp Ha₀]].
  apply SepE in Hp as [Hp H2]. apply Hsub in Hp as H.
  apply CPrdE1 in H as [a [Ha [b [Hb H]]]].
  subst p. zfc_simple. subst.
  exists <a₀, b₀>. split... intros x Hx. apply Hsub in Hx as H.
  apply CPrdE1 in H as [u [Hu [v [Hv H]]]]. subst.
  destruct (classic (<a₀, b₀> = <u, v>)) as [|Hnq]. right... left.
  apply binRelI. apply CPrdI... apply Hsub... zfc_simple.
  assert (Hv': v ∈ {π2 p | p ∊ B}). {
    apply ReplAx. exists <u, v>. split... zfc_simple.
  }
  apply Hleb₀ in Hv' as []... right. split...
  assert (Hu': u ∈ {π1 p | p ∊ B₀}). {
    apply ReplAx. exists <u, v>. split.
    apply SepI... zfc_simple. zfc_simple.
  }
  apply Hlea₀ in Hu' as []...
Qed.

(* 良序结构加法 *)
Definition WoAdd := λ S T,
  let S' := WoDisj S 0 in
  let T' := WoDisj T 1 in
  constr (A S' ∪ A T') (S' ⨁ T') (woAdd_woset S T).
Notation "S + T" := (WoAdd S T) : WoStruct_scope.

(* 良序结构乘法 *)
Definition WoMul := λ S T,
  constr (A S × A T) (S * T) (woMul_woset S T).
Notation "S ⋅ T" := (WoMul S T) : WoStruct_scope.

Lemma woAdd_well_defined : ∀ S S' T T',
  S ≅ S' → T ≅ T' → S + T ≅ S' + T'.
Proof with auto.
  intros * HisoS HisoT.
  cut (LOʷ S + LOʷ T ≅ LOʷ S' + LOʷ T')%lo...
  apply loAdd_well_defined...
Qed.

Lemma woMul_well_defined : ∀ S S' T T',
  S ≅ S' → T ≅ T' → S ⋅ T ≅ S' ⋅ T'.
Proof with auto.
  intros * HisoS HisoT.
  cut (LOʷ S ⋅ LOʷ T ≅ LOʷ S' ⋅ LOʷ T')%lo...
  apply loMul_well_defined...
Qed.

Lemma woAdd_iff_loAdd : ∀ S T U,
  S + T ≅ U ↔ (LOʷ S + LOʷ T ≅ LOʷ U)%lo.
Proof. intros. reflexivity. Qed.

Lemma woMul_iff_loMul : ∀ S T U,
  S ⋅ T ≅ U ↔ (LOʷ S ⋅ LOʷ T ≅ LOʷ U)%lo.
Proof. intros. reflexivity. Qed.

Lemma woAdd_n_m : ∀ n m : nat, (WOⁿ n + WOⁿ m)%wo ≅ WOⁿ (n + m)%nat.
Proof. intros. apply loAdd_n_m. Qed.

Lemma woMul_n_m : ∀ n m : nat, (WOⁿ n ⋅ WOⁿ m)%wo ≅ WOⁿ (n * m)%nat.
Proof. intros. apply loMul_n_m. Qed.

Lemma woAdd_suc : ∀ α (Ho: α ⋵ 𝐎𝐍),
  (WOᵒ α Ho + WOⁿ 1)%wo ≅ WOᵒ α⁺ (ord_suc_is_ord α Ho).
Proof with eauto; try congruence.
  intros α Ho.
  unfold WOᵒ, WOⁿ, WoAdd. simpl.
  unfold WoDisj_A. simpl.
  set (α × ⎨0⎬ ∪ 1 × ⎨1⎬) as Dom.
  set (Func Dom α⁺ (λ p, match (ixm (π2 p = 0)) with
    | inl _ => π1 p | inr _ => α
  end)) as F.
  pose proof contra_0_1 as H01.
  pose proof contra_1_0 as H10.
  assert (Hbi: F: Dom ⟺ α⁺). {
    apply meta_bijection.
    - intros p Hp. apply BUnionE in Hp as [];
      apply CPrdE1 in H as [a [Ha [b [Hb H]]]];
      apply SingE in Hb; subst; zfc_simple.
      + destruct (ixm (Embed 0 = 0))... apply BUnionI1...
      + destruct (ixm (Embed 1 = 0))...
    - intros x1 H1 x2 H2 Heq.
      apply BUnionE in H1 as [H1|H1];
      apply BUnionE in H2 as [H2|H2];
      apply CPrdE1 in H1 as [a [Ha [b [Hb H1]]]];
      apply CPrdE1 in H2 as [c [Hc [d [Hd H2]]]];
      apply SingE in Hb; apply SingE in Hd; subst; zfc_simple.
      + destruct (ixm (Embed 0 = 0))...
      + destruct (ixm (Embed 0 = 0))...
        destruct (ixm (Embed 1 = 0))...
        exfalso. eapply ord_not_lt_self...
      + destruct (ixm (Embed 0 = 0))...
        destruct (ixm (Embed 1 = 0))...
        exfalso. eapply ord_not_lt_self...
      + destruct (ixm (Embed 1 = 0))...
        rewrite one in Ha, Hc.
        apply SingE in Ha. apply SingE in Hc.
        apply op_iff. split...
    - intros y Hy. apply BUnionE in Hy as [].
      + exists <y, 0>. split. apply BUnionI1. apply CPrdI...
        zfc_simple. destruct (ixm (Embed 0 = 0))...
      + apply SingE in H; subst.
        exists <0, 1>. split. apply BUnionI2. apply CPrdI...
        rewrite one. apply SingI.
        zfc_simple. destruct (ixm (Embed 1 = 0))...
  }
  apply bijection_is_func in Hbi as HF. destruct HF as [HF _].
  exists F. split; simpl...
  intros x Hx y Hy. unfold F.
  rewrite meta_func_ap, meta_func_ap...
  split; intros Hxy;
  destruct (ixm (π2 x = 0));
  destruct (ixm (π2 y = 0));
  apply BUnionE in Hx as [Hx|Hx];
  apply BUnionE in Hy as [Hy|Hy];
  apply CPrdE1 in Hx as [a [Ha [b [Hb Hx]]]];
  apply CPrdE1 in Hy as [c [Hc [d [Hd Hy]]]];
  apply SingE in Hb; apply SingE in Hd; subst; zfc_simple; [(
    apply BUnionE in Hxy as [Hxy|Hxy]; [
      apply BUnionE in Hxy as [Hxy|Hxy];
      apply ReplAx in Hxy as [p [Hp H]]; simpl in Hp;
      apply binRelE1 in Hp as [u [_ [v [_ [Hp Hab]]]]]; subst;
      apply op_iff in H as [H1 H2];
      apply op_iff in H1 as [H1 H1'];
      apply op_iff in H2 as [H2 H2']; subst; zfc_simple|
      apply CPrdE0 in Hxy as [H1 H2];
      apply CPrdE0 in H1 as [H11 H12];
      apply CPrdE0 in H2 as [H21 H22]; zfc_simple;
      apply SingE in H12; apply SingE in H22
    ]
  ); apply binRelI; auto; try apply BUnionI1..| | | |]...
  - rewrite one in Ha, Hc.
    apply SingE in Ha. apply SingE in Hc. subst. exfalso0.
  - apply BUnionI1. apply BUnionI1. apply ReplAx.
    exists <a, c>. split; zfc_simple.
    apply binRelE3 in Hxy. apply binRelI...
  - apply BUnionI2. apply CPrdI; apply CPrdI...
  - apply binRelE3 in Hxy. exfalso.
    eapply (ord_not_lt_gt α Ho c)... eapply ord_is_ords...
  - apply binRelE3 in Hxy. exfalso. eapply ord_irrefl...
Qed.
