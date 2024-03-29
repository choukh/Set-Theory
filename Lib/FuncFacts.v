(** Coq coding by choukh, Aug 2020 **)

Require Import ZFC.Lib.Relation.

(** dom & ran **)

(* 函数的定义域等于函数的π1替代 *)
Lemma dom_eq_π1_repl : ∀ f, is_function f → dom f = {π1 p | p ∊ f}.
Proof with eauto.
  intros f Hf. ext Hx.
  - apply domE in Hx as [y Hp]. apply ReplAx.
    exists <x, y>. split... zfc_simple.
  - apply ReplAx in Hx as [p [Hp H1]]. 
    apply func_pair in Hp as Heq... apply SepI.
    + apply UnionAx. exists {x,}. split...
      apply UnionAx. exists p. split...
      rewrite Heq, <- H1. apply PairI1.
    + exists (π2 p). congruence.
Qed.

(* 函数的值域等于函数的π2替代 *)
Lemma ran_eq_π2_repl : ∀ f, is_function f → ran f = {π2 p | p ∊ f}.
Proof with eauto.
  intros f Hf. ext y Hy.
  - apply ranE in Hy as [x Hp]. apply ReplAx.
    exists <x, y>. split... zfc_simple.
  - apply ReplAx in Hy as [p [Hp H2]]. 
    apply func_pair in Hp as Heq... apply SepI.
    + apply UnionAx. exists {π1 p, π2 p}. split.
      apply UnionAx. exists p. split...
      rewrite Heq at 3. apply PairI2.
      rewrite <- H2. apply PairI2.
    + exists (π1 p). congruence.
Qed.

(** meta **)

(* 通过类型论函数证明集合论函数的定义域 *)
Lemma meta_dom : ∀ A B F, (∀x ∈ A, F x ∈ B) →
  dom (Func A B F) = A.
Proof with eauto.
  intros. ext Hx.
  - apply domE in Hx as [y Hp]. apply SepE in Hp as [Hp _].
    apply CPrdE2 in Hp as [Hx _]...
  - eapply domI. apply SepI.
    apply CPrdI... zfc_simple.
Qed.

(* 通过类型论函数证明集合论函数的定义域与值域 *)
Lemma meta_function : ∀ A B F, (∀x ∈ A, F x ∈ B) → 
  (Func A B F): A ⇒ B.
Proof with auto.
  intros. split. apply func_is_func. split.
  - apply meta_dom...
  - intros y Hy. eapply ranE in Hy as [x Hp].
    apply SepE in Hp as [Hp _].
    apply CPrdE2 in Hp as [_ Hy]...
Qed.

(* 将集合论函数应用表达为类型论函数应用 *)
Lemma meta_func_ap : ∀ A B F, (Func A B F): A ⇒ B →
  ∀x ∈ A, (Func A B F)[x] = F x.
Proof with auto.
  intros * [Hf [Hd Hr]] x Hx.
  rewrite <- Hd in Hx. apply func_correct in Hx...
  apply SepE in Hx as [_ Hx]. zfc_simple.
Qed.

(* 通过类型论函数证明集合论函数是单射 *)
Lemma meta_injection : ∀ A B F,
  (∀x ∈ A, F x ∈ B) → 
  (∀ x1 x2 ∈ A, F x1 = F x2 → x1 = x2) →
  (Func A B F): A ⇔ B.
Proof with eauto.
  intros * Hf Hinj.
  apply meta_function in Hf as [Hf [Hd Hr]]. split... split...
  intros y Hy. rewrite <- unique_existence.
  split. apply ranE in Hy...
  intros x1 x2 H1 H2.
  apply SepE in H1 as [H11 H12]. apply CPrdE2 in H11 as [Hx1 _].
  apply SepE in H2 as [H21 H22]. apply CPrdE2 in H21 as [Hx2 _].
  zfc_simple. subst y. apply Hinj...
Qed.

(* 通过类型论函数证明集合论函数是满射 *)
Lemma meta_surjection : ∀ A B F,
  (∀x ∈ A, F x ∈ B) → 
  (∀y ∈ B, ∃x ∈ A, F x = y) →
  (Func A B F): A ⟹ B.
Proof with eauto.
  intros * Hf Hsurj.
  apply meta_function in Hf as [Hf [Hd Hr]].
  split; [|split]... apply sub_antisym...
  intros y Hy. pose proof (Hsurj _ Hy) as [x [Hx Hap]].
  eapply ranI. apply SepI. apply CPrdI... zfc_simple.
Qed.

(* 通过类型论函数证明集合论函数是双射 *)
Lemma meta_bijection : ∀ A B F,
  (∀x ∈ A, F x ∈ B) →
  (∀ x1 x2 ∈ A, F x1 = F x2 → x1 = x2) →
  (∀y ∈ B, ∃x ∈ A, F x = y) →
  (Func A B F): A ⟺ B.
Proof with auto.
  intros * H1 H2 H3.
  apply (meta_injection A B) in H2 as [Hi [Hd _]]...
  apply (meta_surjection A B) in H3 as [_ [_ Hr]]...
  split; [|split]...
Qed.

(* 通过指定定义域将类型论函数编码为集合论函数 *)
Definition LambdaEncode : (set → set) → set → set := λ F A,
  Func A {F a | a ∊ A} F.
Notation "F ↿ A" := (LambdaEncode F A) (at level 60).
Notation "'Λ' x ∊ A , F" := ((λ x, F) ↿ A) (at level 200).

Lemma lambdaEncode : ∀ F A, ∀a ∈ A, (F ↿ A)[a] = F a.
Proof with auto.
  intros F A a Ha. unfold LambdaEncode.
  rewrite meta_func_ap... apply meta_function.
  intros x Hx. apply ReplI...
Qed.

(** special cases **)

(* 常函数 *)
Definition Const : set → set → set := λ A b,
  Func A {b,} (λ _, b).

(* 常函数是映射 *)
Lemma const_function : ∀ A b, (Const A b): A ⇒ {b,}.
Proof.
  intros A b. apply meta_function. intros _ _. auto.
Qed.

(* 常函数应用 *)
Lemma const_func_ap : ∀ A b, ∀x ∈ A, (Const A b)[x] = b.
Proof with auto.
  intros A b x Hx. unfold Const.
  rewrite meta_func_ap... apply const_function.
Qed.

(* 常函数是满射 *)
Lemma const_surjection : ∀ A b, ⦿ A → (Const A b): A ⟹ {b,}.
Proof with auto.
  intros A b [a Ha]. apply meta_surjection. intros _ _...
  intros y Hy. apply SingE in Hy. exists a. split...
Qed.

(* 恒等函数是双射 *)
Lemma ident_bijection : ∀ A, Ident A: A ⟺ A.
Proof with auto.
  intros. split. apply ident_injective.
  split. apply dom_ident. apply ran_ident.
Qed.

(* 空函数的定义域等于空集 *)
Lemma dom_of_empty : dom ∅ = ∅.
Proof.
  apply ExtAx; intros y; split; intros Hy.
  apply domE in Hy as [x Hp]. exfalso0. exfalso0.
Qed.

(* 定义域等于空集的函数是空函数 *)
Lemma empty_dom : ∀ F, is_function F → dom F = ∅ → F = ∅.
Proof with auto.
  intros F Hf Hd.
  ext p Hp.
  - apply func_pair in Hp as Heq...
    rewrite Heq in Hp. apply domI in Hp.
    rewrite Hd in Hp. exfalso0.
  - exfalso0.
Qed.

(* 空函数的值域等于空集 *)
Lemma ran_of_empty : ran ∅ = ∅.
Proof.
  apply ExtAx; split; intros Hx.
  apply ranE in Hx as [y Hp]. exfalso0. exfalso0.
Qed.

(* 值域等于空集的函数是空函数 *)
Lemma empty_ran : ∀ F, is_function F → ran F = ∅ → F = ∅.
Proof with auto.
  intros F Hf Hr.
  ext p Hp.
  - apply func_pair in Hp as Heq...
    rewrite Heq in Hp. apply ranI in Hp.
    rewrite Hr in Hp. exfalso0.
  - exfalso0.
Qed.

(* 空函数是空集到任意集合的单射 *)
Lemma empty_injection : ∀ A, ∅: ∅ ⇔ A.
Proof with auto.
  intros. repeat split.
  - intros x Hx. exfalso0.
  - intros y Hy. rewrite <- unique_existence.
    split. apply domE in Hy...
    intros x1 x2 H1. exfalso0.
  - intros x Hx. rewrite <- unique_existence.
    split. apply ranE in Hx...
    intros y1 y2 H2. exfalso0.
  - ext Hx.
    apply domE in Hx as [y Hp]. exfalso0. exfalso0.
  - intros y Hy. apply ranE in Hy as [x Hp]. exfalso0.
Qed.

(* 空函数是空集到空集的双射 *)
Lemma empty_bijection : ∅: ∅ ⟺ ∅.
Proof with auto.
  apply bijection_is_injection. split.
  apply empty_injection.
  ext y Hy.
  apply ranE in Hy as [x Hp]. exfalso0. exfalso0.
Qed.

(* 能与空集建立双射的集合是空集 *)
Lemma bijection_to_empty : ∀ F A, F: A ⟺ ∅ → A = ∅.
Proof.
  intros * [Hi [Hd Hr]].
  ext Hx; [|exfalso0].
  rewrite <- Hd in Hx. apply domE in Hx as [y Hp].
  apply ranI in Hp. rewrite Hr in Hp. exfalso0.
Qed.

(* 单点集是函数 *)
Lemma single_pair_is_func : ∀ a b, is_function {<a, b>,}.
Proof with auto.
  intros. split.
  - intros x Hx. apply SingE in Hx. subst x...
  - intros x Hx. rewrite <- unique_existence.
    split. apply domE in Hx...
    intros y1 y2 H1 H2.
    apply SingE in H1. apply op_iff in H1 as []; subst.
    apply SingE in H2. apply op_iff in H2 as []; subst...
Qed.

(* 单点集是单射 *)
Lemma single_pair_injective : ∀ a b, injective {<a, b>,}.
Proof with auto.
  intros. split. apply single_pair_is_func.
  intros x Hx. rewrite <- unique_existence.
  split. apply ranE in Hx...
  intros y1 y2 H1 H2.
  apply SingE in H1. apply op_iff in H1 as []; subst.
  apply SingE in H2. apply op_iff in H2 as []; subst...
Qed.

(* 单点集的定义域 *)
Lemma dom_of_single_pair : ∀ a b, dom {<a, b>,} = {a,}.
Proof with auto.
  intros. ext Hx.
  - apply domE in Hx as [y Hp]. apply SingE in Hp.
    apply op_iff in Hp as []; subst...
  - apply SingE in Hx; subst x. eapply domI...
Qed.

(* 单点集的值域 *)
Lemma ran_of_single_pair : ∀ a b, ran {<a, b>,} = {b,}.
Proof with auto.
  intros. ext y Hy.
  - apply ranE in Hy as [x Hp]. apply SingE in Hp.
    apply op_iff in Hp as []; subst...
  - apply SingE in Hy; subst y. eapply ranI...
Qed.

(* 单点集是双射 *)
Lemma single_pair_bijection : ∀ a b, {<a, b>,}: {a,} ⟺ {b,}.
Proof with auto.
  intros. split. apply single_pair_injective. split.
  - apply dom_of_single_pair.
  - apply ran_of_single_pair.
Qed.

(* 单点函数应用 *)
Lemma single_pair_ap: ∀ a b, ∀x ∈ {a,}, {<a, b>,}[x] = b.
Proof with auto.
  intros a b x Hx.
  apply SingE in Hx; subst.
  pose proof (single_pair_bijection a b) as [[Hf _] [Hd Hr]].
  assert (Ha: a ∈ dom {<a, b>,}). rewrite Hd...
  apply func_correct in Ha... apply ranI in Ha.
  rewrite Hr in Ha. apply SingE in Ha...
Qed.

(** inv, compo, restr **)

(* 双射的逆仍是双射 *)
Lemma inv_bijection : ∀ F A B, F: A ⟺ B → F⁻¹: B ⟺ A.
Proof with auto.
  intros * [[Hf Hs] [Hd Hr]]. split. split.
  apply inv_func_iff_sr... apply inv_sr_iff_func...
  split. rewrite inv_dom... rewrite inv_ran...
Qed.

(* 复合映射 *)
Lemma compo_function : ∀ F G A B C,
  F: A ⇒ B → G: B ⇒ C → (G ∘ F): A ⇒ C.
Proof with eauto.
  intros * [Hff [Hfd Hfr]] [Hfg [Hgd Hgr]].
  split; [|split].
  - apply compo_func...
  - ext Hx.
    + apply domE in Hx as [y Hp].
      apply compoE in Hp as [t [H1 H2]].
      rewrite <- Hfd. eapply domI...
    + rewrite <- Hfd in Hx.
      apply domE in Hx as [y Hp]. apply ranI in Hp as Hr.
      apply Hfr in Hr. rewrite <- Hgd in Hr.
      apply domE in Hr as [z Hp']. eapply domI. eapply compoI...
  - intros y Hy. apply ranE in Hy as [x Hp].
    apply compoE in Hp as [t [H1 H2]]. apply Hgr. eapply ranI...
Qed.

(* 两个单射的复合仍是单射 *)
Lemma compo_injective: ∀ F G, injective F → injective G → injective (F ∘ G).
Proof. exact ex3_17_b. Qed.

(* 复合单射 *)
Lemma compo_injection : ∀ F G A B C,
  F: A ⇔ B → G: B ⇔ C → (G ∘ F): A ⇔ C.
Proof with eauto.
  intros * Hf Hg. apply injection_is_func. split.
  - eapply compo_function; apply injection_is_func...
  - apply compo_injective. destruct Hg... destruct Hf...
Qed.

(* 复合满射 *)
Lemma compo_surjection : ∀ F G A B C,
  F: A ⟹ B → G: B ⟹ C → (G ∘ F): A ⟹ C.
Proof with eauto; try congruence.
  intros * Hf Hg.
  apply surjection_is_func in Hf as [Hf Hfr].
  apply surjection_is_func in Hg as [Hg Hgr].
  apply surjection_is_func. split.
  eapply compo_function...
  ext y Hy.
  - apply ranE in Hy as [x Hp].
    apply compoE in Hp as [t [_ H]]. apply ranI in H...
  - destruct Hf as [_ [Hdf _]]. destruct Hg as [_ [Hdg _]].
    rewrite <- Hgr in Hy. apply ranE in Hy as [t Hpf].
    apply domI in Hpf as Ht. rewrite Hdg, <- Hfr in Ht.
    apply ranE in Ht as [x Hpg]. eapply ranI. eapply compoI...
Qed.

(* 复合双射 *)
Lemma compo_bijection : ∀ F G A B C,
  F: A ⟺ B → G: B ⟺ C → (G ∘ F): A ⟺ C.
Proof with eauto; try congruence.
  intros * Hf Hg.
  apply bijection_is_injection in Hf as [Hf Hfr].
  apply bijection_is_injection in Hg as [Hg Hgr].
  apply bijection_is_injection. split. eapply compo_injection...
  rewrite compo_ran; [|destruct Hg as []|destruct Hf as [[]]]...
  ext y Hy.
  - apply SepE in Hy as [Hy _]...
  - destruct Hg as [[Hfg Hsg] [Hdg _]].
    apply SepI... rewrite Hfr, <- Hdg, <- inv_ran.
    eapply ranI. apply func_correct.
    apply inv_func_iff_sr... rewrite inv_dom... 
Qed.

(* 限制在空集上的函数等于空函数 *)
Lemma restr_to_empty : ∀ F, F ↾ ∅ = ∅.
Proof.
  intros. ext Hx.
  - apply restrE1 in Hx as [a [b [Ha _]]]. exfalso0.
  - exfalso0.
Qed.

(* 限制在单集上的函数的值域是单集 *)
Lemma ran_of_restr_to_single : ∀ F a, is_function F →
  a ∈ dom F → ran (F ↾ {a,}) = {F[a],}.
Proof with auto.
  intros * Hf Ha. ext y Hy.
  - apply ranE in Hy as [x Hp].
    apply restrE2 in Hp as [Hp Hx]...
    apply SingE in Hx; subst.
    apply func_ap in Hp... subst...
  - apply SingE in Hy; subst. eapply ranI.
    apply restrI... apply func_correct...
Qed.

(* 限制在单集上的函数是单射 *)
Lemma restr_to_single_injective : ∀ f a, is_function f →
  injective (f ↾ {a,}).
Proof with auto.
  intros. split. apply restr_func...
  intros y Hy. rewrite <- unique_existence.
  split. apply ranE in Hy...
  intros x1 x2 H1 H2.
  apply restrE2 in H1 as [_ H1]. apply SingE in H1.
  apply restrE2 in H2 as [_ H2]. apply SingE in H2. congruence.
Qed.

(* 若函数的定义域是A，B的并，那么函数的值域等于函数分别限制于A，B后的值域的并 *)
Lemma ran_split_by_restr : ∀ F A B, dom F = A ∪ B →
  ran F = ran (F ↾ A) ∪ ran (F ↾ B).
Proof with eauto.
  intros. ext y Hy.
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
  ext p Hp.
  - apply func_pair in Hp as Heq... rewrite Heq in Hp.
    apply domI in Hp as Hd. rewrite Hdeq in Hd.
    rewrite Heq. apply BUnionE in Hd as [].
    + apply BUnionI1. apply restrI...
    + apply BUnionI2. apply restrI...
  - apply BUnionE in Hp as [].
    + apply restrE1 in H as [a [b [Ha [Hp Heq]]]]. subst p...
    + apply restrE1 in H as [a [b [Ha [Hp Heq]]]]. subst p...
Qed.

(* 映射的限制 *)
Lemma restr_function : ∀ f A B C, C ⊆ A → f: A ⇒ B → f ↾ C: C ⇒ B.
Proof with auto.
  intros * Hsub [Hf [Hd Hr]].
  split. apply restr_func...
  split. apply restr_dom... rewrite Hd...
  eapply sub_trans. apply restr_ran_included. apply Hr.
Qed.

(* 单射的限制 *)
Lemma restr_injection : ∀ f A B C, C ⊆ A → f: A ⇔ B → f ↾ C: C ⇔ B.
Proof with eauto.
  intros * Hsub Hf.
  apply injection_is_func in Hf as [Hf Hinj].
  apply injection_is_func. split.
  eapply restr_function... apply restr_injective...
Qed.

(* 限制于A的值域等于A的像 *)
Lemma restr_ran_eq_img : ∀ f A, ran (f ↾ A) = f⟦A⟧.
Proof with eauto.
  intros. ext y Hy.
  - apply ranE in Hy as [x Hp].
    apply restrE2 in Hp as [Hp Hx]. eapply imgI...
  - apply imgE in Hy as [x [Hx Hp]].
    eapply ranI. apply restrI...
Qed.

(* 双射的限制 *)
Lemma restr_bijection : ∀ f A B C, C ⊆ A → f: A ⟺ B → f ↾ C: C ⟺ f⟦C⟧.
Proof with eauto.
  intros * Hsub Hf.
  destruct Hf as [Hinj [Hd Hr]].
  split. apply restr_injective...
  split. apply restr_dom. apply Hinj. rewrite Hd...
  apply restr_ran_eq_img.
Qed.

(** bunion **)

(* 若两个函数在定义域的交集上的值相等，则这两个函数的并也是函数 *)
Lemma bunion_is_func : ∀ f g,
  is_function f → is_function g →
  (∀x ∈ dom f ∩ dom g, f[x] = g[x]) ↔ is_function (f ∪ g).
Proof. exact ex3_14_b. Qed.

(* 若两个单射在定义域的交集上的值相等，且在值域的交集上有相同的原值，
  则这两个单射的并也是单射 *)
Lemma bunion_injective : ∀ f g,
  injective f → injective g →
  ( (∀x ∈ dom f ∩ dom g, f[x] = g[x]) ∧
    (∀y ∈ ran f ∩ ran g, f⁻¹[y] = g⁻¹[y])
  ) ↔ injective (f ∪ g).
Proof with eauto.
  intros * [Hf Hsf] [Hg Hsg]. split.
  - intros [Hreq Hdeq]. split. apply bunion_is_func...
    intros y Hy. rewrite <- unique_existence.
    split. apply ranE in Hy...
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
  - intros [Hu Hsu]. split. apply bunion_is_func...
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

(* 映射的并定义域等于映射的定义域的并 *)
Lemma dom_of_bunion_func : ∀ F G, is_function F → is_function G →
  dom (F ∪ G) = dom F ∪ dom G.
Proof with auto.
  intros * HfF HfG. ext Hx.
  + apply domE in Hx as [y Hp].
    apply BUnionE in Hp as [].
    * apply BUnionI1. apply domI in H...
    * apply BUnionI2. apply domI in H...
  + apply BUnionE in Hx as []; eapply domI.
    * apply BUnionI1. apply func_correct...
    * apply BUnionI2. apply func_correct...
Qed.

(* 映射的并也是映射 *)
Lemma bunion_function : ∀ F G A B C D,
  F: A ⇒ B → G: C ⇒ D →
  (∀x ∈ A ∩ C, F[x] = G[x]) →
  (∀y ∈ B ∩ D, F⁻¹[y] = G⁻¹[y]) →
  F ∪ G: A ∪ C ⇒ B ∪ D.
Proof with eauto; try congruence.
  intros * [HiF [HdF HrF]] [HiG [HdG HrG]] Hreq Hdeq.
  split; [|split].
  - apply bunion_is_func...
    intros x Hx. rewrite HdF, HdG in Hx. apply Hreq...
  - rewrite dom_of_bunion_func...
  - intros y Hy. apply ranE in Hy as [x Hp].
    apply BUnionE in Hp as [].
    + apply BUnionI1. apply ranI in H. apply HrF...
    + apply BUnionI2. apply ranI in H. apply HrG...
Qed.

(* 单射的并也是单射 *)
Lemma bunion_injection : ∀ F G A B C D,
  F: A ⇔ B → G: C ⇔ D →
  (∀x ∈ A ∩ C, F[x] = G[x]) →
  (∀y ∈ B ∩ D, F⁻¹[y] = G⁻¹[y]) →
  F ∪ G: A ∪ C ⇔ B ∪ D.
Proof with eauto; try congruence.
  intros * HF HG Hreq Hdeq.
  apply injection_is_func in HF as [HF HiF].
  apply injection_is_func in HG as [HG HiG].
  apply injection_is_func. split.
  apply bunion_function... apply bunion_injective...
  destruct HF as [HfF [HdF HrF]].
  destruct HG as [HfG [HdG HrG]]. split...
  - intros x Hx. rewrite HdF, HdG in Hx. apply Hreq...
  - intros y Hy. apply BInterE in Hy as [H1 H2].
    apply Hdeq. apply BInterI. apply HrF... apply HrG...
Qed.

(* 双射的并也是双射 *)
Lemma bunion_bijection : ∀ F G A B C D,
  F: A ⟺ B → G: C ⟺ D →
  (∀x ∈ A ∩ C, F[x] = G[x]) →
  (∀y ∈ B ∩ D, F⁻¹[y] = G⁻¹[y]) →
  F ∪ G: A ∪ C ⟺ B ∪ D.
Proof with eauto; try congruence.
  intros * HF HG Hreq Hdeq.
  apply bijection_is_injection in HF as [HF HrF].
  apply bijection_is_injection in HG as [HG HrG].
  apply bijection_is_injection. split.
  apply bunion_injection...
  ext y Hy.
  - apply ranE in Hy as [x Hp].
    apply BUnionE in Hp as [].
    + apply BUnionI1. apply ranI in H...
    + apply BUnionI2. apply ranI in H...
  - apply BUnionE in Hy as [].
    + rewrite <- HrF in H. apply ranE in H as [x Hp].
      eapply ranI. apply BUnionI1...
    + rewrite <- HrG in H. apply ranE in H as [x Hp].
      eapply ranI. apply BUnionI2...
Qed.

(* 函数的并的应用 *)
Lemma bunion_func_ap : ∀ F G A B C D,
  F: A ⇒ B → G: C ⇒ D →
  (∀x ∈ A ∩ C, F[x] = G[x]) →
  (∀y ∈ B ∩ D, F⁻¹[y] = G⁻¹[y]) →
  (∀x ∈ A, (F ∪ G)[x] = F[x]) ∧ ∀x ∈ C, (F ∪ G)[x] = G[x].
Proof with auto; try congruence.
  intros * HF HG Hreq Hdeq.
  assert (HU: F ∪ G: A ∪ C ⇒ B ∪ D)
    by (apply bunion_function; auto).
  destruct HF as [HfF [HdF _]].
  destruct HG as [HfG [HdG _]].
  destruct HU as [HfU [HdU _]].
  split; intros x Hx.
  - assert (Hd: x ∈ dom (F ∪ G)). {
      rewrite HdU. apply BUnionI1...
    }
    apply domE in Hd as [y Hp].
    apply func_ap in Hp as Hap...
    apply BUnionE in Hp as [].
    + apply func_ap in H...
    + rewrite Hreq... apply func_ap in H...
      apply BInterI... apply domI in H...
  - assert (Hd: x ∈ dom (F ∪ G)). {
      rewrite HdU. apply BUnionI2...
    }
    apply domE in Hd as [y Hp].
    apply func_ap in Hp as Hap...
    apply BUnionE in Hp as [].
    + rewrite <- Hreq... apply func_ap in H...
      apply BInterI... apply domI in H...
    + apply func_ap in H...
Qed.

(** union **)

Lemma union_of_chain_of_injective_functions :
  ∀ F, is_chain F → (∀f ∈ F, injective f) →
  ⋃F: ⋃{dom f | f ∊ F} ⟺ ⋃{ran f | f ∊ F}.
Proof with eauto; try congruence.
  intros F Hchn Hfs. split; split; [split|..].
  - intros p Hp.
    apply UnionAx in Hp as [f [Hf Hp]]. eapply Hfs...
  - intros x Hx. rewrite <- unique_existence.
    split. apply domE in Hx...
    intros y1 y2 H1 H2.
    apply UnionAx in H1 as [f1 [Hf1 H1]].
    apply UnionAx in H2 as [f2 [Hf2 H2]].
    pose proof (Hchn f1 Hf1 f2 Hf2) as [].
    + apply Hfs in Hf2 as [Hff2 _]. apply H in H1.
      apply func_ap in H1...
      apply func_ap in H2...
    + apply Hfs in Hf1 as [Hff1 _]. apply H in H2.
      apply func_ap in H1...
      apply func_ap in H2...
  - intros y Hy. rewrite <- unique_existence.
    split. apply ranE in Hy...
    intros x1 x2 H1 H2.
    apply UnionAx in H1 as [f1 [Hf1 H1]].
    apply UnionAx in H2 as [f2 [Hf2 H2]].
    pose proof (Hchn f1 Hf1 f2 Hf2) as [].
    + apply H in H1. eapply singrE... apply Hfs...
    + apply H in H2. eapply singrE... apply Hfs...
  - ext Hx.
    + apply domE in Hx as [y Hp].
      apply UnionAx in Hp as [f [Hf Hp]]. apply domI in Hp.
      apply UnionAx. exists (dom f). split...
      apply ReplAx. exists f. split...
    + apply UnionAx in Hx as [p [Hp Hx]].
      apply ReplAx in Hp as [f [Hf Heq]]. subst.
      apply domE in Hx as [y Hp]. eapply domI.
      apply UnionAx. exists f. split...
  - ext y Hy.
    + apply ranE in Hy as [x Hp].
      apply UnionAx in Hp as [f [Hf Hp]]. apply ranI in Hp.
      apply UnionAx. exists (ran f). split...
      apply ReplAx. exists f. split...
    + apply UnionAx in Hy as [p [Hp Hy]].
      apply ReplAx in Hp as [f [Hf Heq]]. subst.
      apply ranE in Hy as [x Hp]. eapply ranI.
      apply UnionAx. exists f. split...
Qed.

(** add point **)

(* 函数加点仍是函数 *)
Lemma add_point_is_func : ∀ F a b,
  is_function F → a ∉ dom F →
  is_function (F ∪ {<a, b>,}).
Proof with eauto.
  intros F a b Hf Hout.
  pose proof (single_pair_bijection a b) as [[Hfs _] [Hds _]].
  apply bunion_is_func... intros x Hx. exfalso.
  apply BInterE in Hx as [H1 H2].
  rewrite Hds in H2. apply SingE in H2; subst...
Qed.

(* 单射加点仍是单射 *)
Lemma add_point_injective : ∀ F a b,
  injective F → a ∉ dom F → b ∉ ran F →
  injective (F ∪ {<a, b>,}).
Proof with eauto.
  intros F a b Hf Hout1 Hout2.
  pose proof (single_pair_bijection a b) as [Hfs [Hds Hrs]].
  apply bunion_injective... split.
  - intros x Hx. exfalso.
    apply BInterE in Hx as [H1 H2].
    rewrite Hds in H2. apply SingE in H2; subst...
  - intros y Hy. exfalso.
    apply BInterE in Hy as [H1 H2].
    rewrite Hrs in H2. apply SingE in H2; subst...
Qed.

(* 函数加点 *)
Lemma function_add_point : ∀ F A B a b,
  F: A ⇒ B → a ∉ A → b ∉ B →
  (F ∪ {<a, b>,}): A ∪ {a,} ⇒ B ∪ {b,}.
Proof with eauto; try congruence.
  intros * [Hf [Hd Hr]] Hout1 Hout2.
  split; [|split].
  - apply add_point_is_func...
  - ext Hx.
    + apply domE in Hx as [y Hp]. apply BUnionE in Hp as [].
      * apply BUnionI1. apply domI in H. congruence.
      * apply BUnionI2. apply SingE in H.
        apply op_iff in H as []; subst...
    + apply BUnionE in Hx as [].
      * eapply domI. apply BUnionI1.
        apply func_correct...
      * eapply domI. apply BUnionI2.
        pose proof (single_pair_bijection a b) as [[Hfs _] [Hds _]].
        apply func_correct...
  - intros y Hy. apply ranE in Hy as [x Hp].
    apply BUnionE in Hp as [].
    + apply BUnionI1. apply Hr. eapply ranI...
    + apply BUnionI2. apply SingE in H.
      apply op_iff in H as []; subst...
Qed.

(* 单射加点 *)
Lemma injection_add_point : ∀ F A B a b,
  F: A ⇔ B → a ∉ A → b ∉ B →
  (F ∪ {<a, b>,}): A ∪ {a,} ⇔ B ∪ {b,}.
Proof with eauto; try congruence.
  intros * Hf Hout1 Hout2.
  apply injection_is_func in Hf as [Hf Hinj].
  apply injection_is_func. split.
  apply function_add_point...
  destruct Hf as [_ [Hd Hr]].
  apply add_point_injective...
Qed.

(* 双射加点 *)
Lemma bijection_add_point : ∀ F A B a b,
  F: A ⟺ B → a ∉ A → b ∉ B →
  (F ∪ {<a, b>,}): A ∪ {a,} ⟺ B ∪ {b,}.
Proof with eauto; try congruence.
  intros * Hf Hout1 Hout2.
  apply bijection_is_injection in Hf as [Hinj Hr].
  apply bijection_is_injection... split.
  apply injection_add_point...
  pose proof (single_pair_bijection a b) as [[Hfs Hss] [Hds Hrs]].
  ext y Hy.
  - apply ranE in Hy as [x Hp].
    apply BUnionE in Hp as []; apply ranI in H.
    + apply BUnionI1...
    + rewrite Hrs in H. apply BUnionI2...
  - apply BUnionE in Hy as [].
    + rewrite <- Hr in H. apply ranE in H as [x Hp].
      eapply ranI. apply BUnionI1...
    + rewrite <- Hrs in H. apply ranE in H as [x Hp].
      eapply ranI. apply BUnionI2...
Qed.

(* 加点函数的应用 *)
Lemma add_point_func_ap : ∀ F A B a b,
  F: A ⟺ B → a ∉ A → b ∉ B →
  (∀x ∈ A, (F ∪ {<a, b>,})[x] = F[x]) ∧
  ∀x ∈ {a,}, (F ∪ {<a, b>,})[x] = b.
Proof with eauto.
  intros * HF Hout1 Hout2.
  cut (
    (∀x ∈ A, (F ∪ {<a, b>,})[x] = F[x]) ∧
    (∀x ∈ {a,}, (F ∪ {<a, b>,})[x] = {<a, b>,}[x])
  ). {
    intros [H1 H2]. split. apply H1.
    intros x Hx. rewrite <- (single_pair_ap a b x) at 2...
  }
  eapply bunion_func_ap.
  - apply bijection_is_func...
  - apply bijection_is_func. apply single_pair_bijection.
  - intros x Hx. exfalso. apply BInterE in Hx as [H1 H2].
    apply SingE in H2; subst...
  - intros x Hx. exfalso. apply BInterE in Hx as [H1 H2].
    apply SingE in H2; subst...
Qed.

(** replace value **)

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
  let B := {R x | x ∊ A} in
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
  set (Func A B (λ x, R x)) as F.
  exists F. apply meta_bijection.
  - intros x Hx. apply ReplAx. exists x. split...
  - intros x1 Hx1 x2 Hx2 Heq.
    subst R. unfold ReplaceElement in Heq.
    destruct (ixm (x1 = a)); destruct (ixm (x2 = a))...
  - intros y Hy. apply ReplAx in Hy...
Qed.

(* 若A，B之间有单射，那么A与B的替换任一元素的集合之间也有单射 *)
Lemma injection_replace_element :
  ∀ F A B a b, F: A ⇔ B → a ∈ B → b ∉ B →
  let R := ReplaceElement a b in
  ∃ F, F: A ⇔ {R x | x ∊ B}.
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
    apply sub_antisym. apply restr_ran_included.
    intros y Hy. apply ranE in Hy as [x Hp].
    apply domI in Hp as Hxd. rewrite Hd in Hxd.
    eapply ranI. apply restrI...
  }
  assert (Hbr: b ∉ ran F). { intro. apply Hr in H0... }
  pose proof (bijection_exists_between_set_and_element_replaced
    _ _ _ Har Hbr) as [F' Hf'].
  assert (Hg: F' ∘ (F ↾ A): A ⟺ {R x | x ∊ ran F})
    by (eapply compo_bijection; eauto).
  destruct Hg as [Hig [Hdg Hdr]].
  exists (F' ∘ (F ↾ A)). split... split... rewrite Hdr.
  intros y Hy. apply ReplAx in Hy as [x [Hx Heq]].
  apply Hr in Hx. subst y. apply ReplI...
Qed.

(** swap value **)

Definition FuncSwapValue : set → set → set → set := λ f a b,
  Func (dom f) (ran f) (λ x,
    match ixm (x = a) with
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
    ext y Hy.
    - apply ranE in Hy as [x Hp].
      apply SepE in Hp as [Hp _].
      apply CPrdE2 in Hp as [_ Hy]...
    - assert (Hy' := Hy).
      apply ranE in Hy' as [x Hp].
      apply domI in Hp as Hx. apply func_ap in Hp...
      destruct (classic (x = a)) as [Hxa|Hxa]; [|
      destruct (classic (x = b)) as [Hxb|Hxb]]; eapply ranI.
      + apply SepI. apply CPrdI; auto.
        rewrite Hd. apply Hb. zfc_simple.
        destruct (ixm (b = a)) as []...
        destruct (ixm (b = b)) as []...
      + apply SepI. apply CPrdI; auto.
        rewrite Hd. apply Ha. zfc_simple.
        destruct (ixm (a = a)) as []...
      + apply SepI. apply CPrdI... zfc_simple.
        destruct (ixm (x = a)) as []...
        destruct (ixm (x = b)) as []...
  }
  split... cut (F': A ⇒ ran F). {
    intros [Hf' [Hd' Hr']].
    split... split... rewrite Hreq...
  }
  subst F'. unfold FuncSwapValue. rewrite Hd.
  apply meta_function. intros x Hx.
  destruct (ixm (x = a)). eapply ap_ran... split...
  destruct (ixm (x = b)).
  eapply ap_ran... split... eapply ap_ran... split...
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
  ext p Hp.
  - apply func_pair in Hp as Heq... rewrite Heq in Hp.
    apply domI in Hp as Hpd. apply ranI in Hp as Hpr.
    apply func_ap in Hp... rewrite Heq.
    apply SepI. apply CPrdI... zfc_simple.
    destruct (ixm (π1 p = a)). {
      symmetry. apply func_ap... rewrite HeqF'.
      apply SepI. apply CPrdI... zfc_simple.
      destruct (ixm (b = a))...
      destruct (ixm (b = b))...
    }
    destruct (ixm (π1 p = b)).
    + symmetry. apply func_ap... rewrite HeqF'.
      apply SepI. apply CPrdI... zfc_simple.
      destruct (ixm (a = a))...
    + symmetry. apply func_ap... rewrite HeqF'.
      apply SepI. apply CPrdI... zfc_simple.
      destruct (ixm (π1 p = a))...
      destruct (ixm (π1 p = b))...
  - apply SepE in Hp as [Hp Heq].
    apply CPrdE1 in Hp as [x [Hx [y [Hy Hp]]]].
    subst p. zfc_simple.
    destruct (ixm (x = a))... {
      rewrite <- Hd' in Hb. apply func_correct in Hb...
      rewrite <- Heq, HeqF' in Hb. clear Heq.
      apply SepE in Hb as [Hp Heq].
      apply CPrdE2 in Hp as [Hb Hyr]. zfc_simple.
      destruct (ixm (b = a)). subst a b y. apply func_correct...
      destruct (ixm (b = b))... subst a y. apply func_correct...
    }
    destruct (ixm (x = b)).
    + rewrite <- Hd' in Ha. apply func_correct in Ha...
      rewrite <- Heq, HeqF' in Ha. clear Heq.
      apply SepE in Ha as [Hp Heq].
      apply CPrdE2 in Hp as [Ha Hyr]. zfc_simple.
      destruct (ixm (a = a)). subst b y. apply func_correct...
      destruct (ixm (a = b))...
    + apply func_correct in Hx...
      rewrite <- Heq, HeqF' in Hx. clear Heq.
      apply SepE in Hx as [Hp Heq].
      apply CPrdE2 in Hp as [Hx Hyr]. zfc_simple.
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
  split... split; split...
  intros y Hy. rewrite <- unique_existence.
  split. apply ranE in Hy as [x1 H1]...
  intros x1 x2 H1 H2.
  apply SepE in H1 as [H11 H12]. apply CPrdE2 in H11 as [].
  apply SepE in H2 as [H21 H22]. apply CPrdE2 in H21 as []. zfc_simple.
  destruct (ixm (x1 = a)); destruct (ixm (x2 = a));
  destruct (ixm (x1 = b)); destruct (ixm (x2 = b)); try congruence;
    [..|eapply injectiveE; eauto; congruence]; exfalso.
  - apply n0. eapply injectiveE...
  - apply n0. eapply injectiveE...
  - apply n1. eapply injectiveE...
  - apply n0. eapply injectiveE...
  - apply n0. eapply injectiveE...
  - apply n0. eapply injectiveE...
  - apply n0. eapply injectiveE...
  - apply n. eapply injectiveE...
Qed.

(* 满射交换两个值后仍是满射 *)
Lemma surjection_swap_value : ∀ F A B, ∀ a b ∈ A,
  F: A ⟹ B → (FuncSwapValue F a b): A ⟹ B.
Proof with eauto; try congruence.
  intros F A B a Ha b Hb [Hf [Hd Hr]].
  assert (Hmap: F: A ⇒ B). { split... destruct Hf... split... }
  apply (func_swap_value _ _ _ _ Ha _ Hb) in Hmap
    as [[Hf' [Hd' Hr']] Hreq]. split... split...
Qed.

(* 双射交换两个值后仍是双射 *)
Lemma bijection_swap_value : ∀ F A B, ∀ a b ∈ A,
  F: A ⟺ B → (FuncSwapValue F a b): A ⟺ B.
Proof with eauto; try congruence.
  intros F A B a Ha b Hb [Hf [Hd Hr]].
  assert (Hmap: F: A ⇔ B). { split... destruct Hf... split... }
  apply (injection_swap_value _ _ _ _ Ha _ Hb) in Hmap
    as [[Hf' [Hd' Hr']] Hreq]. split... split...
Qed.

(** transform **)

(* 函数复合满足结合律 *)
Lemma compo_assoc: ∀ R S T, (R ∘ S) ∘ T = R ∘ (S ∘ T).
Proof. exact ex3_21. Qed.

(* 右复合恒等函数 *)
Lemma right_compo_ident : ∀ F A, F ∘ Ident A = F ↾ A.
Proof. intros. apply ex3_23_a. Qed.

(* 左复合恒等函数 *)
Lemma left_compo_ident : ∀ F A, Ident A ∘ F⁻¹ = (F ↾ A)⁻¹.
Proof with auto.
  intros. rewrite <- (inv_inv (Ident A)), <- compo_inv, inv_ident,
    right_compo_ident... destruct (ident_is_func A)...
Qed.

Lemma left_compo_ident' : ∀ F A, is_rel F →
  Ident A ∘ F = (F⁻¹ ↾ A)⁻¹.
Proof with auto.
  intros. rewrite <- (inv_inv F) at 1... rewrite left_compo_ident...
Qed.

(* A到A的单射与A到B的双射可以构造B到B的单射 *)
Lemma injection_transform : ∀ f g A B,
  f: A ⇔ A → g: A ⟺ B → g ∘ f ∘ g⁻¹: B ⇔ B.
Proof with eauto.
  intros * [Hif [Hdf Hrf]] [Hig [Hdg Hrg]].
  assert (Hig' := Hig). destruct Hig' as [Hg Hsg].
  assert (Hif' := Hif). destruct Hif' as [Hf Hsf].
  assert (Hig': injective g⁻¹) by (apply inv_injective; auto).
  assert (Higf: injective (g ∘ f)) by (apply compo_injective; auto).
  assert (Hfc: is_function (g ∘ f)) by (apply compo_func; auto).
  assert (Hfg': is_function g⁻¹) by (apply inv_func_iff_sr; auto).
  split; [|split].
  - apply compo_injective...
  - rewrite compo_dom; revgoals...
    ext Hx.
    + apply SepE in Hx as []. rewrite <- Hrg, <- inv_dom...
    + apply SepI. rewrite inv_dom, Hrg... rewrite compo_dom...
      assert ((g⁻¹) [x] ∈ dom f). {
        rewrite Hdf, <- Hdg, <- inv_ran.
        eapply ap_ran. split... rewrite inv_dom, Hrg...
      }
      apply SepI... rewrite Hdg. eapply ap_ran... split...
  - intros y Hy. rewrite compo_ran in Hy...
    apply SepE in Hy as [Hy _]. rewrite compo_ran in Hy...
    apply SepE in Hy as []. rewrite <- Hrg...
Qed.

(* A到A的满射与A到B的双射可以构造B到B的满射 *)
Lemma surjection_transform : ∀ f g A B,
  f: A ⟹ A → g: A ⟺ B → g ∘ f ∘ g⁻¹: B ⟹ B.
Proof with eauto.
  intros * [Hf [Hdf Hrf]] [Hig [Hdg Hrg]].
  assert (Hig' := Hig). destruct Hig' as [Hg Hsg].
  assert (Hfc: is_function (g ∘ f)) by (apply compo_func; auto).
  assert (Hfg': is_function g⁻¹) by (apply inv_func_iff_sr; auto).
  assert (Hfc': is_function (f ∘ g⁻¹)) by (apply compo_func; auto).
  split; [|split].
  - apply compo_func...
  - rewrite compo_dom; revgoals...
    ext Hx.
    + apply SepE in Hx as []. rewrite <- Hrg, <- inv_dom...
    + apply SepI. rewrite inv_dom, Hrg... rewrite compo_dom...
      assert ((g⁻¹) [x] ∈ dom f). {
        rewrite Hdf, <- Hdg, <- inv_ran.
        eapply ap_ran. split... rewrite inv_dom, Hrg...
      }
      apply SepI... rewrite Hdg, <- Hrf.
      eapply ap_ran... split...
  - ext y Hy.
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

(* A到A的双射与A到B的双射可以构造B到B的双射 *)
Lemma bijection_transform : ∀ f g A B,
  f: A ⟺ A → g: A ⟺ B → g ∘ f ∘ g⁻¹: B ⟺ B.
Proof with eauto; try congruence.
  intros * [Hif [Hdf Hrf]] Hg.
  assert (Hinj: ((g ∘ f) ∘ g ⁻¹) : B ⇔ B). {
    eapply injection_transform... split; [|split]...
  }
  assert (Hsurj: ((g ∘ f) ∘ g ⁻¹) : B ⟹ B). {
    eapply surjection_transform... split... destruct Hif...
  }
  destruct Hinj as [Hi [Hd _]].
  destruct Hsurj as [_ [_ Hr]]. split; [|split]...
Qed.
