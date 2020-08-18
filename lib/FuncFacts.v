(** Coq coding by choukh, Aug 2020 **)

Require Import ZFC.CH3_2.

Lemma single_pair_is_func : ∀ a b, is_function ⎨<a, b>⎬.
Proof with auto.
  intros. repeat split.
  - intros x Hx. apply SingE in Hx. subst x...
  - apply domE in H...
  - intros y1 y2 H1 H2.
    apply SingE in H1. apply op_correct in H1 as []; subst.
    apply SingE in H2. apply op_correct in H2 as []; subst...
Qed.

Lemma single_pair_injective : ∀ a b, injective ⎨<a, b>⎬.
Proof with auto.
  intros. split. apply single_pair_is_func.
  split. apply ranE in H...
  intros y1 y2 H1 H2.
  apply SingE in H1. apply op_correct in H1 as []; subst.
  apply SingE in H2. apply op_correct in H2 as []; subst...
Qed.

Lemma single_pair_bijective : ∀ a b, ⎨<a, b>⎬: ⎨a⎬ ⟺ ⎨b⎬.
Proof with auto.
  intros. split. apply single_pair_injective. split.
  - apply ExtAx. split; intros Hx.
    + apply domE in Hx as [y Hp]. apply SingE in Hp.
      apply op_correct in Hp as []; subst...
    + apply SingE in Hx; subst x. eapply domI...
  - apply ExtAx. intros y. split; intros Hy.
    + apply ranE in Hy as [x Hp]. apply SingE in Hp.
      apply op_correct in Hp as []; subst...
    + apply SingE in Hy; subst y. eapply ranI...
Qed.

Lemma bunion_func : ∀ f g,
  is_function f → is_function g →
  (∀x ∈ dom f ∩ dom g, f[x] = g[x]) ↔ is_function (f ∪ g).
Proof. exact ch3_14_b. Qed.

Lemma bunion_injection : ∀ f g,
  injective f → injective g →
  ( (∀x ∈ dom f ∩ dom g, f[x] = g[x]) ∧
    (∀y ∈ ran f ∩ ran g, f⁻¹[y] = g⁻¹[y])
  ) ↔ injective (f ∪ g).
Proof with eauto.
  intros * [Hf Hsf] [Hg Hsg]. split.
  - intros [Hreq Hdeq]. split. apply bunion_func...
    intros y Hy. split. apply ranE in Hy...
    intros x1 x2 H1 H2.
    apply BUnionE in H1 as [H1|H1]; apply BUnionE in H2 as [H2|H2].
    + eapply (singrE f)...
    + assert ((f⁻¹)[y] = (g⁻¹)[y]). {
        apply Hdeq. apply BInterI.
        apply ranI in H1... apply ranI in H2...
      }
      rewrite inv_op in H1. apply func_ap in H1.
      rewrite inv_op in H2. apply func_ap in H2. congruence.
      apply inv_func_iff_sr... apply inv_func_iff_sr...
    + assert ((f⁻¹)[y] = (g⁻¹)[y]). {
        apply Hdeq. apply BInterI.
        apply ranI in H2... apply ranI in H1...
      }
      rewrite inv_op in H1. apply func_ap in H1.
      rewrite inv_op in H2. apply func_ap in H2. congruence.
      apply inv_func_iff_sr... apply inv_func_iff_sr...
    + eapply (singrE g)...
  - intros [Hu Hsu]. split. apply bunion_func...
    intros y Hy. apply BInterE in Hy as [Hyf Hyg].
    apply ranE in Hyf as [x1 Hpf]. rewrite inv_op in Hpf.
    apply func_ap in Hpf as Hap1. subst x1.
    apply ranE in Hyg as [x2 Hpg]. rewrite inv_op in Hpg.
    apply func_ap in Hpg as Hap2. subst x2.
    eapply singrE. apply Hsu.
    apply BUnionI1. rewrite inv_op... 
    apply BUnionI2. rewrite inv_op...
    apply inv_func_iff_sr... apply inv_func_iff_sr...
Qed.

Lemma func_add_point : ∀ F A B a b, F: A ⇒ B →
  disjoint A ⎨a⎬ → disjoint B ⎨b⎬ →
  (F ∪ ⎨<a, b>⎬): A ∪ ⎨a⎬ ⇒ B ∪ ⎨b⎬.
Proof with eauto.
  intros * [Hf [Hd Hr]] Hdj1 Hdj2.
  pose proof (single_pair_bijective a b) as [[Hf' _] [Hd' Hr']].
  split; [|split].
  - apply bunion_func... intros x Hx. exfalso.
    apply BInterE in Hx as [H1 H2].
    rewrite Hd in H1. rewrite Hd' in H2.
    eapply disjointE; [apply Hdj1|..]...
  - apply ExtAx. split; intros Hx.
    + apply domE in Hx as [y Hp]. apply BUnionE in Hp as [].
      * apply BUnionI1. apply domI in H. congruence.
      * apply BUnionI2. apply SingE in H.
        apply op_correct in H as []; subst...
    + apply BUnionE in Hx as [].
      * eapply domI. apply BUnionI1.
        apply func_correct... rewrite Hd...
      * eapply domI. apply BUnionI2.
        apply func_correct... rewrite Hd'...
  - intros y Hy. apply ranE in Hy as [x Hp].
    apply BUnionE in Hp as [].
    + apply BUnionI1. apply Hr. eapply ranI...
    + apply BUnionI2. apply SingE in H.
      apply op_correct in H as []; subst...
Qed.

Lemma bijection_add_point : ∀ F A B a b, F: A ⟺ B →
  disjoint A ⎨a⎬ → disjoint B ⎨b⎬ →
  (F ∪ ⎨<a, b>⎬): A ∪ ⎨a⎬ ⟺ B ∪ ⎨b⎬.
Proof with eauto.
  intros * [Hif [Hdf Hrf]] Hdj1 Hdj2.
  assert (Hmap: F: A ⇒ B). {
    split. destruct Hif... split... rewrite Hrf...
  }
  pose proof (func_add_point _ _ _ _ _ Hmap Hdj1 Hdj2) as [Hfu [Hdu Hru]].
  pose proof (single_pair_bijective a b) as [[Hfs Hss] [Hds Hrs]].
  split; [|split]... apply bunion_injection...
  apply single_pair_injective. split.
  - intros x Hx. rewrite Hdf, Hds in Hx.
    apply BInterE in Hx as [H1 H2].
    exfalso. eapply disjointE; [apply Hdj1|..]...
  - intros y Hy. rewrite Hrf, Hrs in Hy.
    apply BInterE in Hy as [H1 H2].
    exfalso. eapply disjointE; [apply Hdj2|..]...
  - apply sub_asym... intros y Hy. apply BUnionE in Hy as [].
    + rewrite <- Hrf in H. eapply ranE in H as [x Hp]. 
      eapply ranI. apply BUnionI1...
    + rewrite <- Hrs in H. eapply ranE in H as [x Hp]. 
      eapply ranI. apply BUnionI2...
Qed.
