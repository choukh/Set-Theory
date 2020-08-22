(** Coq coding by choukh, Aug 2020 **)

Require Import ZFC.CH3_2.

(* 能与空集建立双射的集合是空集 *)
Lemma bijection_empty : ∀ F A, F: A ⟺ ∅ → A = ∅.
Proof.
  intros * [Hi [Hd Hr]].
  apply ExtAx. split; intros Hx; [|exfalso0].
  rewrite <- Hd in Hx. apply domE in Hx as [y Hp].
  apply ranI in Hp. rewrite Hr in Hp. exfalso0.
Qed.

(* 限制在单集上的函数的值域是单集 *)
Lemma ran_of_restr_to_single : ∀ F a, is_function F →
  a ∈ dom F → ran (F ↾ ⎨a⎬) = ⎨F[a]⎬.
Proof with auto.
  intros * Hf Ha. apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [x Hp].
    apply restrE2 in Hp as [Hp Hx]...
    apply SingE in Hx; subst.
    apply func_ap in Hp... subst...
  - apply SingE in Hy; subst. eapply ranI.
    apply restrI... apply func_correct...
Qed.

(* 限制在单集上的函数是单射 *)
Lemma restr_to_single_injective : ∀ f a, is_function f →
  injective (f ↾ ⎨a⎬).
Proof with auto.
  intros. split. apply restr_func...
  intros y Hy. split. apply ranE in Hy...
  intros x1 x2 H1 H2.
  apply restrE2 in H1 as [_ H1]. apply SingE in H1.
  apply restrE2 in H2 as [_ H2]. apply SingE in H2. congruence.
Qed.

(* 若函数的定义域是A，B的并，那么函数的值域等于函数分别限制于A，B后的值域的并 *)
Lemma ran_split_by_restr : ∀ F A B, dom F = A ∪ B →
  ran F = ran (F ↾ A) ∪ ran (F ↾ B).
Proof with eauto.
  intros. apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [x Hp]. apply domI in Hp as Hd.
    rewrite H in Hd. apply BUnionE in Hd as [].
    + apply BUnionI1. eapply ranI. apply restrI...
    + apply BUnionI2. eapply ranI. apply restrI...
  - apply BUnionE in Hy as [Hy|Hy].
    + apply ranE in Hy as [x Hp].
      apply restrE2 in Hp as [Hp _]. eapply ranI...
    + apply ranE in Hy as [x Hp].
      apply restrE2 in Hp as [Hp _]... eapply ranI...
Qed.

(* 若函数的定义域是A，B的并，那么函数等于该函数分别限制于A，B后的函数的并 *)
Lemma func_split_by_restr : ∀ F A B, is_function F → dom F = A ∪ B →
  F = (F ↾ A) ∪ (F ↾ B).
Proof with auto.
  intros * Hf Hdeq.
  apply ExtAx. intros p. split; intros Hp.
  - apply func_pair in Hp as Heq... rewrite Heq in Hp.
    apply domI in Hp as Hd. rewrite Hdeq in Hd.
    rewrite Heq. apply BUnionE in Hd as [].
    + apply BUnionI1. apply restrI...
    + apply BUnionI2. apply restrI...
  - apply BUnionE in Hp as [].
    + apply restrE1 in H as [a [b [Ha [Hp Heq]]]]. subst p...
    + apply restrE1 in H as [a [b [Ha [Hp Heq]]]]. subst p...
Qed.

(* 有序对的单集是函数 *)
Lemma single_pair_is_func : ∀ a b, is_function ⎨<a, b>⎬.
Proof with auto.
  intros. repeat split.
  - intros x Hx. apply SingE in Hx. subst x...
  - apply domE in H...
  - intros y1 y2 H1 H2.
    apply SingE in H1. apply op_correct in H1 as []; subst.
    apply SingE in H2. apply op_correct in H2 as []; subst...
Qed.

(* 有序对的单集是单射 *)
Lemma single_pair_injective : ∀ a b, injective ⎨<a, b>⎬.
Proof with auto.
  intros. split. apply single_pair_is_func.
  split. apply ranE in H...
  intros y1 y2 H1 H2.
  apply SingE in H1. apply op_correct in H1 as []; subst.
  apply SingE in H2. apply op_correct in H2 as []; subst...
Qed.

(* 有序对的单集是双射 *)
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

(* 若两个函数在定义域的交集上的值相等，则这两个函数的并也是函数 *)
Lemma bunion_func : ∀ f g,
  is_function f → is_function g →
  (∀x ∈ dom f ∩ dom g, f[x] = g[x]) ↔ is_function (f ∪ g).
Proof. exact ch3_14_b. Qed.

(* 若两个单射在定义域的交集上的值相等，且在值域的交集上有相同的原值，
  则这两个单射的并也是单射 *)
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

(* 函数加点 *)
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

(* 双射加点 *)
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

Definition ReplaceElement : set → set → (set → set) :=
  λ a b, λ x, match (ixm (x = a)) with
    | inl _ => b
    | inr _ => x
  end.

Lemma replace_element_correct_1 : ∀ a b,
  (ReplaceElement a b) a = b.
Proof.
  intros. unfold ReplaceElement.
  destruct (ixm (a = a)); congruence.
Qed.

Lemma replace_element_correct_2 : ∀ a b x,
  x ≠ a → (ReplaceElement a b) x = x.
Proof.
  intros. unfold ReplaceElement.
  destruct (ixm (x = a)); congruence.
Qed.

(* 任意集合与替换自身任一元素的集合之间可以建立双射 *)
Lemma bijection_exists_between_set_and_element_replaced :
  ∀ A a b, a ∈ A → b ∉ A →
  let R := ReplaceElement a b in
  let B := {R | x ∊ A} in
  ∃ F, F: A ⟺ B.
Proof with eauto; try congruence.
  intros * Ha Hb R B.
  assert (Hra: R a = b)
    by (apply replace_element_correct_1).
  assert (Hrx: ∀ x, x ≠ a → R x = x) 
    by (apply replace_element_correct_2; auto).
  assert (Hbb: b ∈ B). {
    apply ReplAx. exists a. split...
  }
  assert (Hxb: ∀x ∈ A, x ≠ a → x ∈ B). {
    intros x Hx H. subst B. apply ReplAx. exists x. split...
  }
  set (Relation A B (λ x y, y = R x)) as F.
  exists F. repeat split.
  - apply rel_is_rel.
  - apply domE in H...
  - intros y1 y2 H1 H2.
    apply SepE in H1 as [_ H1].
    apply SepE in H2 as [_ H2]. zfcrewrite.
  - apply ranE in H...
  - intros x1 x2 H1 H2.
    apply SepE in H1 as [H11 H12]. apply CProdE1 in H11 as [Hx1 _].
    apply SepE in H2 as [H21 H22]. apply CProdE1 in H21 as [Hx2 _].
    zfcrewrite. subst x R. unfold ReplaceElement in H22.
    destruct (ixm (x1 = a)); destruct (ixm (x2 = a))...
  - apply ExtAx. split; intros Hx.
    + apply domE in Hx as [y Hp].
      apply SepE in Hp as [Hp _].
      apply CProdE1 in Hp as [Hx _]. zfcrewrite.
    + destruct (classic (x = a)) as [Hxa|Hxa]; [subst x|].
      * eapply domI. apply SepI. apply CProdI. apply Hx.
        apply Hbb. zfcrewrite.
      * eapply domI. apply SepI. apply CProdI. apply Hx.
        apply Hxb; eauto. zfcrewrite. symmetry. apply Hrx...
  - apply ExtAx. intros y. split; intros Hy.
    + apply ranE in Hy as [x Hp].
      apply SepE in Hp as [Hp _].
      apply CProdE1 in Hp as [_ Hy]. zfcrewrite.
    + apply ReplAx in Hy as [x [Hx Hr]]. subst y.
      destruct (classic (x = a)) as [Hxa|Hxa]; [subst x|].
      * rewrite Hra. eapply ranI. apply SepI. apply CProdI...
        zfcrewrite.
      * rewrite Hrx... eapply ranI. apply SepI. apply CProdI...
        apply Hxb... zfcrewrite. symmetry. apply Hrx...
Qed.

(* 若A，B之间有单射，那么A与B的替换任一元素的集合之间也有单射 *)
Lemma injection_replace_element :
  ∀ F A B a b, F: A ⇔ B → a ∈ B → b ∉ B →
  let R := ReplaceElement a b in
  ∃ F, F: A ⇔ {R | x ∊ B}.
Proof with eauto.
  intros * [Hf [Hd Hr]] Hab Hbb R.
  assert (Hra: R a = b) by (apply replace_element_correct_1).
  assert (Hrx: ∀ x, x ≠ a → R x = x)
    by (apply replace_element_correct_2; auto).
  destruct (classic (a ∈ ran F)) as [Har|Har]; revgoals. {
    exists F. split... split...
    intros y Hy. apply ReplAx. exists y. split.
    apply Hr... apply Hrx. congruence.
  }
  assert ((F ↾ A): A ⟺ ran F). {
    split. apply restr_injective... split.
    apply restr_dom. destruct Hf... rewrite <- Hd...
    apply sub_asym. apply restr_ran_included.
    intros y Hy. apply ranE in Hy as [x Hp].
    apply domI in Hp as Hxd. rewrite Hd in Hxd.
    eapply ranI. apply restrI...
  }
  assert (Hbr: b ∉ ran F). { intro. apply Hr in H0... }
  pose proof (bijection_exists_between_set_and_element_replaced
    _ _ _ Har Hbr) as [F' Hf'].
  assert (Hg: F' ∘ (F ↾ A): A ⟺ {R | x ∊ ran F})
    by (eapply compo_bijection; eauto).
  destruct Hg as [Hig [Hdg Hdr]].
  exists (F' ∘ (F ↾ A)). split... split... rewrite Hdr.
  intros y Hy. apply ReplAx in Hy as [x [Hx Heq]].
  apply Hr in Hx. subst y. apply ReplAx. exists x. split...
Qed.

Definition FuncSwapValue : set → set → set → set := λ f a b,
  Relation (dom f) (ran f) (λ x y,
    y = match ixm (x = a) with
      | inl _ => f[b]
      | inr _ =>
        match ixm (x = b) with
        | inl _ => f[a]
        | inr _ => f[x]
        end
    end
  ).

(* 函数交换两个值后仍是函数 *)
Lemma func_swap_value : ∀ F A B, ∀ a b ∈ A,
  F: A ⇒ B → let F' := FuncSwapValue F a b in
  F': A ⇒ B ∧ ran F' = ran F.
Proof with eauto; try congruence.
  intros F A B a Ha b Hb [Hf [Hd Hr]] F'.
  assert (Hreq: ran F' = ran F). {
    apply ExtAx. intros y. split; intros Hy.
    - apply ranE in Hy as [x Hp].
      apply SepE in Hp as [Hp _].
      apply CProdE1 in Hp as [_ Hy]. zfcrewrite.
    - assert (Hy' := Hy).
      apply ranE in Hy' as [x Hp].
      apply domI in Hp as Hx. apply func_ap in Hp...
      destruct (classic (x = a)) as [Hxa|Hxa]; [|
      destruct (classic (x = b)) as [Hxb|Hxb]]; eapply ranI.
      + apply SepI. apply CProdI; auto.
        rewrite Hd. apply Hb. zfcrewrite.
        destruct (ixm (b = a)) as []...
        destruct (ixm (b = b)) as []...
      + apply SepI. apply CProdI; auto.
        rewrite Hd. apply Ha. zfcrewrite.
        destruct (ixm (a = a)) as []...
      + apply SepI. apply CProdI... zfcrewrite.
        destruct (ixm (x = a)) as []...
        destruct (ixm (x = b)) as []...
  }
  split... split; [|split].
  - repeat split. apply rel_is_rel. apply domE in H...
    intros y1 y2 H1 H2.
    apply SepE in H1 as [_ H1].
    apply SepE in H2 as [_ H2]. zfcrewrite.
  - apply ExtAx. intros x. split; intros Hx.
    + apply domE in Hx as [Hy Hpr].
      apply SepE in Hpr as [Hpr _].
      apply CProdE1 in Hpr as [Hx _]. zfcrewrite.
    + rewrite <- Hd in Hx, Ha, Hb.
      destruct (classic (x = a)) as [Hxa|Hxa]; [|
      destruct (classic (x = b)) as [Hxb|Hxb]].
      * apply domE in Hb as [y Hp]. apply ranI in Hp as Hy.
        apply func_ap in Hp... eapply domI. apply SepI.
        apply CProdI... zfcrewrite.
        destruct (ixm (x = a)) as []...
      * apply domE in Ha as [y Hp]. apply ranI in Hp as Hy.
        apply func_ap in Hp... eapply domI. apply SepI.
        apply CProdI... zfcrewrite.
        destruct (ixm (x = a)) as []...
        destruct (ixm (x = b)) as []...
      * assert (Hx' := Hx). apply domE in Hx as [y Hp].
        apply ranI in Hp as Hy. apply func_ap in Hp...
        eapply domI. apply SepI. apply CProdI... zfcrewrite.
        destruct (ixm (x = a)) as []...
        destruct (ixm (x = b)) as []...
  - rewrite Hreq...
Qed.

(* 函数交换两个值两次后与原函数相等 *)
Lemma func_swap_twice_id : ∀ F A B, ∀ a b ∈ A,
  F: A ⇒ B → F = FuncSwapValue (FuncSwapValue F a b) a b.
Proof with eauto; try congruence.
  intros F A B a Ha b Hb Hf.
  pose proof (func_swap_value _ _ _ _ Ha _ Hb Hf)
    as [[Hf' [Hd' Hr']] Hreq].
  remember (FuncSwapValue F a b) as F'.
  destruct Hf as [Hf [Hd Hr]].
  apply ExtAx. intros p. split; intros Hp.
  - apply func_pair in Hp as Heq... rewrite Heq in Hp.
    apply domI in Hp as Hpd. apply ranI in Hp as Hpr.
    apply func_ap in Hp... rewrite Heq.
    apply SepI. apply CProdI... zfcrewrite.
    destruct (ixm (π1 p = a)). {
      symmetry. apply func_ap... rewrite HeqF'.
      apply SepI. apply CProdI... zfcrewrite.
      destruct (ixm (b = a))...
      destruct (ixm (b = b))...
    }
    destruct (ixm (π1 p = b)).
    + symmetry. apply func_ap... rewrite HeqF'.
      apply SepI. apply CProdI... zfcrewrite.
      destruct (ixm (a = a))...
    + symmetry. apply func_ap... rewrite HeqF'.
      apply SepI. apply CProdI... zfcrewrite.
      destruct (ixm (π1 p = a))...
      destruct (ixm (π1 p = b))...
  - apply SepE in Hp as [Hp Heq].
    apply CProd_correct in Hp as [x [Hx [y [Hy Hp]]]].
    subst p. zfcrewrite.
    destruct (ixm (x = a))... {
      rewrite <- Hd' in Hb. apply func_correct in Hb...
      rewrite <- Heq, HeqF' in Hb. clear Heq.
      apply SepE in Hb as [Hp Heq].
      apply CProdE1 in Hp as [Hb Hyr]. zfcrewrite.
      destruct (ixm (b = a)). subst a b y. apply func_correct...
      destruct (ixm (b = b))... subst a y. apply func_correct...
    }
    destruct (ixm (x = b)).
    + rewrite <- Hd' in Ha. apply func_correct in Ha...
      rewrite <- Heq, HeqF' in Ha. clear Heq.
      apply SepE in Ha as [Hp Heq].
      apply CProdE1 in Hp as [Ha Hyr]. zfcrewrite.
      destruct (ixm (a = a)). subst b y. apply func_correct...
      destruct (ixm (a = b))...
    + apply func_correct in Hx...
      rewrite <- Heq, HeqF' in Hx. clear Heq.
      apply SepE in Hx as [Hp Heq].
      apply CProdE1 in Hp as [Hx Hyr]. zfcrewrite.
      destruct (ixm (x = a))...
      destruct (ixm (x = b))... subst y. apply func_correct...
Qed.

(* 单射交换两个值后仍是单射 *)
Lemma injection_swap_value : ∀ F A B, ∀ a b ∈ A,
  F: A ⇔ B → let F' := FuncSwapValue F a b in
  F': A ⇔ B ∧ ran F' = ran F.
Proof with eauto; try congruence.
  intros F A B a Ha b Hb [Hf [Hd Hr]] F'.
  assert (Hmap: F: A ⇒ B). { split... destruct Hf... }
  apply (func_swap_value _ _ _ _ Ha _ Hb) in Hmap
    as [[Hf' [Hd' Hr']] Hreq].
  split... split; split... split. apply ranE in H...
  intros x1 x2 H1 H2.
  apply SepE in H1 as [H11 H12]. apply CProdE1 in H11 as [].
  apply SepE in H2 as [H21 H22]. apply CProdE1 in H21 as []. zfcrewrite.
  destruct (ixm (x1 = a)); destruct (ixm (x2 = a));
  destruct (ixm (x1 = b)); destruct (ixm (x2 = b)); try congruence;
    [..|eapply func_injective; eauto; congruence]; exfalso.
  - apply n0. eapply func_injective...
  - apply n0. eapply func_injective...
  - apply n1. eapply func_injective...
  - apply n0. eapply func_injective...
  - apply n0. eapply func_injective...
  - apply n0. eapply func_injective...
  - apply n0. eapply func_injective...
  - apply n. eapply func_injective...
Qed.

(* 满射交换两个值后仍是满射 *)
Lemma surjection_swap_value : ∀ F A B, ∀ a b ∈ A,
  F: A ⟹ B → let F' := FuncSwapValue F a b in
  F': A ⟹ B ∧ ran F' = ran F.
Proof with eauto; try congruence.
  intros F A B a Ha b Hb [Hf [Hd Hr]] F'.
  assert (Hmap: F: A ⇒ B). { split... destruct Hf... split... }
  apply (func_swap_value _ _ _ _ Ha _ Hb) in Hmap
    as [[Hf' [Hd' Hr']] Hreq].
  split... split... split... apply sub_asym...
  intros y Hy. rewrite <- Hr in Hy.
  apply ranE in Hy as [x Hp]. apply ranI in Hp as Hyr.
  apply domI in Hp as Hxd. apply func_ap in Hp... 
  destruct (classic (x = a)) as [Hxa|Hxa]; [|
  destruct (classic (x = b)) as [Hxb|Hxb]].
  - eapply ranI. apply SepI. apply CProdI.
    rewrite Hd. apply Hb. apply Hyr. zfcrewrite.
    destruct (ixm (b = a)) as []...
    destruct (ixm (b = b)) as []...
  - eapply ranI. apply SepI. apply CProdI.
    rewrite Hd. apply Ha. apply Hyr. zfcrewrite.
    destruct (ixm (a = a)) as []...
  - eapply ranI. apply SepI. apply CProdI.
    apply Hxd. apply Hyr. zfcrewrite.
    destruct (ixm (x = a)) as []...
    destruct (ixm (x = b)) as []...
Qed.

(* 单射的复合仍是单射 *)
Lemma compo_inj: ∀ F G, injective F → injective G → injective (F ∘ G).
Proof. exact ch3_17_b. Qed.

(* 函数复合满足结合律 *)
Lemma compo_assoc: ∀ R S T, (R ∘ S) ∘ T = R ∘ (S ∘ T).
Proof. exact ch3_21. Qed.

(* 右复合恒等函数 *)
Lemma right_compo_ident : ∀ F A, F ∘ Ident A = F ↾ A.
Proof. intros. apply ch3_23_a. Qed.

(* 左复合恒等函数 *)
Lemma left_compo_ident : ∀ F A, Ident A ∘ F⁻¹ = (F ↾ A)⁻¹.
Proof with auto.
  intros. rewrite <- (inv_inv (Ident A)), <- compo_inv, inv_ident,
    right_compo_ident... destruct (ident_is_func A)...
Qed.

Lemma left_compo_ident' : ∀ F A, is_relation F →
  Ident A ∘ F = (F⁻¹ ↾ A)⁻¹.
Proof with auto.
  intros. rewrite <- (inv_inv F) at 1... rewrite left_compo_ident...
Qed.

(* 若有任意集合A到自身的单射f和A到自然数n的双射g，那么用f和g可以构造n到n的单射 *)
Lemma injection_transform : ∀ f g A n,
  f: A ⇔ A → g: A ⟺ n → (g ∘ f ∘ g⁻¹): n ⇔ n.
Proof with auto.
  intros * [Hif [Hdf Hrf]] [Hig [Hdg Hrg]].
  assert (Hig' := Hig). destruct Hig' as [Hg Hsg].
  assert (Hif' := Hif). destruct Hif' as [Hf Hsf].
  assert (Hig': injective g⁻¹) by (apply inv_injective; auto).
  assert (Higf: injective (g ∘ f)) by (apply compo_inj; auto).
  assert (Hfc: is_function (g ∘ f)) by (apply compo_func; auto).
  assert (Hfg': is_function g⁻¹) by (apply inv_func_iff_sr; auto).
  split; [|split].
  - apply compo_inj...
  - rewrite compo_dom; revgoals...
    apply ExtAx. split; intros Hx.
    + apply SepE in Hx as []. rewrite <- Hrg, <- inv_dom...
    + apply SepI. rewrite inv_dom, Hrg... rewrite compo_dom...
      assert ((g⁻¹) [x] ∈ dom f). {
        rewrite Hdf, <- Hdg, <- inv_ran.
        eapply ranI. apply func_correct... rewrite inv_dom, Hrg...
      }
      apply SepI... rewrite Hdg. apply Hrf.
      eapply ranI. apply func_correct...
  - intros y Hy. rewrite compo_ran in Hy...
    apply SepE in Hy as [Hy _]. rewrite compo_ran in Hy...
    apply SepE in Hy as []. rewrite <- Hrg...
Qed.

(* 若有任意集合A到自身的满射f和A到自然数n的双射g，那么用f和g可以构造n到n的满射 *)
Lemma surjection_transform : ∀ f g A n,
  f: A ⟹ A → g: A ⟺ n → (g ∘ f ∘ g⁻¹): n ⟹ n.
Proof with auto.
  intros * [Hf [Hdf Hrf]] [Hig [Hdg Hrg]].
  assert (Hig' := Hig). destruct Hig' as [Hg Hsg].
  assert (Hfc: is_function (g ∘ f)) by (apply compo_func; auto).
  assert (Hfg': is_function g⁻¹) by (apply inv_func_iff_sr; auto).
  assert (Hfc': is_function (f ∘ g⁻¹)) by (apply compo_func; auto).
  split; [|split].
  - apply compo_func...
  - rewrite compo_dom; revgoals...
    apply ExtAx. split; intros Hx.
    + apply SepE in Hx as []. rewrite <- Hrg, <- inv_dom...
    + apply SepI. rewrite inv_dom, Hrg... rewrite compo_dom...
      assert ((g⁻¹) [x] ∈ dom f). {
        rewrite Hdf, <- Hdg, <- inv_ran.
        eapply ranI. apply func_correct... rewrite inv_dom, Hrg...
      }
      apply SepI... rewrite Hdg. rewrite <- Hrf.
      eapply ranI. apply func_correct...
  - apply ExtAx. intros y. split; intros Hy.
    + rewrite compo_assoc, compo_ran in Hy...
      apply SepE in Hy as [Hy _]. rewrite Hrg in Hy...
    + rewrite compo_assoc, compo_ran... apply SepI. rewrite Hrg...
      rewrite <- Hrg, <- inv_dom in Hy.
      apply func_correct in Hy... apply ranI in Hy.
      rewrite inv_ran, Hdg, <- Hrf in Hy.
      apply ranE in Hy as [x Hp]. apply domI in Hp as Hxd.
      rewrite Hdf, <- Hdg, <- inv_ran in Hxd.
      apply ranE in Hxd as [w Hpg].
      eapply ranI. eapply compoI; eauto.
Qed.

(* 满射的右逆是单射 *)
Lemma right_inv_of_surjection_injective : ∀ F A B,
  F: A ⟹ B → ∃ G, G: B ⇔ A ∧ F ∘ G = Ident B.
Proof with eauto.
  intros * [Hf [Hd Hr]].
  assert (is_relation F⁻¹) by apply inv_rel.
  apply choose_func_from_rel in H as [G [H1 [H2 H3]]].
  (* G: B ⇔ A *)
  exists G. split. {
    split; split...
    - split. apply ranE in H...
      intros y1 y2 Hp1 Hp2. apply H2 in Hp1. apply H2 in Hp2.
      rewrite <- inv_op in Hp1, Hp2. eapply func_sv; revgoals...
    - rewrite inv_dom in H3. subst B...
    - intros x Hx. apply ranE in Hx as [y Hx].
      apply H2, ranI in Hx. rewrite inv_ran in Hx. subst A...
  }
  (* F ∘ G = Ident B *)
  apply ExtAx. intros y. split; intros Hy.
  - apply SepE in Hy as [_ [Hp [x [Hp1 Hp2]]]].
    apply H2 in Hp1. rewrite <- inv_op in Hp1.
    apply ReplAx. exists (π1 y). split. subst B. eapply ranI...
    apply op_η in Hp. rewrite Hp at 3. apply op_correct. split...
    clear H1. eapply func_sv...
  - apply ReplE in Hy as [a [Hp Heq]].
    subst y. subst B. rewrite <- inv_dom in Hp. rewrite <- H3 in Hp. 
    apply domE in Hp as [b Hpg]. assert (Hpf := Hpg).
    apply H2 in Hpf. rewrite <- inv_op in Hpf. eapply compoI...
Qed.
