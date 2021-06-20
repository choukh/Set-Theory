(** Based on "Elements of Set Theory" Chapter 3 Part 1 **)
(** Coq coding by choukh, May 2020 **)

Require Export ZFC.EX2.

(*** EST第三章1：关系，函数，逆，复合 ***)

(** 关系 **)
Definition is_rel : set → Prop := λ X, ∀x ∈ X, is_pair x.

(* 关系是有序对的集合 *)
Lemma rel_pair : ∀ R, is_rel R → ∀p ∈ R, p = <π1 p, π2 p>.
Proof.
  intros R Hr p Hp. apply Hr in Hp. apply op_η in Hp. apply Hp.
Qed.

(* 由命题构造集合论关系 *)
Definition Rel : set → set → (set → set → Prop) → set :=
  λ A B P, {p ∊ A × B | λ p, P (π1 p) (π2 p)}.

Lemma rel_is_rel : ∀ A B P, is_rel (Rel A B P).
Proof.
  intros * x Hx. apply SepE in Hx as [Hx _].
  apply cprod_is_pairs in Hx. apply Hx.
Qed.

Lemma cprod_is_rel : ∀ A B, is_rel (A × B).
Proof. intros * x Hx. apply cprod_is_pairs in Hx. apply Hx. Qed.

Lemma sep_cp_is_rel : ∀ A B P, is_rel {p ∊ A × B | P}.
Proof.
  intros * x Hx. apply SepE in Hx as [Hx _].
  apply cprod_is_pairs in Hx. apply Hx.
Qed.

(* 恒等关系 *)
Definition Ident : set → set := λ A, {λ x, <x, x> | x ∊ A}.

Lemma ident_is_rel : ∀ A, is_rel (Ident A).
Proof.
  intros. intros x Hx. apply ReplAx in Hx as [a [_ Heq]].
    exists a, a. subst x. reflexivity.
Qed.

Lemma identI : ∀ X, ∀a ∈ X, <a, a> ∈ Ident X.
Proof.
  intros * a Ha. apply ReplAx. exists a. split; auto.
Qed.

Lemma identE : ∀ X a b, <a, b> ∈ Ident X → a ∈ X ∧ a = b.
Proof.
  intros. apply ReplAx in H as [c [Ha Heq]].
  apply op_iff in Heq as []. subst. auto.
Qed.

Fact ident_eq_rel : ∀ A,
  Ident A = Rel A A (λ a b, a = b).
Proof with auto.
  intros. apply ExtAx. split; intros.
  - apply ReplAx in H as [a [Ha Heq]]. subst x.
    apply SepI. apply CProdI... zfc_simple.
  - apply SepE in H as [Hx Heq].
    apply CProdE1 in Hx as [a [Ha [b [_ Hp]]]].
    apply ReplAx. exists a. split...
    rewrite Hp. rewrite Hp in Heq. zfc_simple.
Qed.

Fact ident_empty : Ident ∅ = ∅.
Proof.
  apply ExtAx. split; intros Hx.
  apply ReplAx in Hx as [a [Ha _]]. exfalso0. exfalso0.
Qed.

(* 定义域 *)
Definition dom : set → set :=
  λ R, {x ∊ ⋃⋃R | λ x, ∃ y, <x, y> ∈ R}.

(* 值域 *)
Definition ran : set → set :=
  λ R, {x ∊ ⋃⋃R | λ x, ∃ w, <w, x> ∈ R}.

(* 关系的全域 *)
Definition fld : set → set :=
  λ R, dom R ∪ ran R.

Lemma domI : ∀ R x y, <x, y> ∈ R → x ∈ dom R.
Proof.
  intros. apply SepI.
  - apply UnionAx. exists {x, y}. split; [|apply PairI1].
    apply UnionAx. exists <x, y>. split; [|apply PairI2]. apply H.
  - exists y. apply H.
Qed.

Lemma ranI : ∀ R x y, <x, y> ∈ R → y ∈ ran R.
Proof.
  intros. apply SepI.
  - apply UnionAx. exists {x, y}. split; [|apply PairI2].
    apply UnionAx. exists <x, y>. split; [|apply PairI2]. apply H.
  - exists x. apply H.
Qed.

Lemma domE : ∀ R, ∀x ∈ dom R, ∃ y, <x, y> ∈ R.
Proof. intros R x Hx. apply SepE in Hx as [_ H]. apply H. Qed.

Lemma ranE : ∀ R, ∀y ∈ ran R, ∃ x, <x, y> ∈ R.
Proof. intros R x Hx. apply SepE in Hx as [_ H]. apply H. Qed.

Lemma dom_rel : ∀ A B P, dom (Rel A B P) ⊆ A.
Proof.
  intros * x Hx.
  apply domE in Hx as [y Hp].
  apply SepE in Hp as [Hp _].
  apply CProdE2 in Hp as [Hx _]. zfc_simple.
Qed.

Lemma ran_rel : ∀ A B P, ran (Rel A B P) ⊆ B.
Proof.
  intros * y Hy.
  apply ranE in Hy as [x Hp].
  apply SepE in Hp as [Hp _].
  apply CProdE2 in Hp as [_ Hy]. zfc_simple.
Qed.

Lemma dom_ident : ∀ X, dom (Ident X) = X.
Proof.
  intros. apply ExtAx. intros x. split; intros Hx.
  - apply domE in Hx as [y Hp]. apply identE in Hp as []. auto.
  - eapply domI. apply ReplAx. exists x. split.
    apply Hx. reflexivity.
Qed.

Lemma ran_ident : ∀ X, ran (Ident X) = X.
Proof.
  intros. apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [x Hp]. apply identE in Hp as []. subst. auto.
  - eapply ranI. apply ReplAx. exists y. split.
    apply Hy. reflexivity.
Qed.

(** 函数是单值关系 **)
Definition is_function : set → Prop :=
  λ R, is_rel R ∧ ∀x ∈ dom R, ∃! y, <x, y> ∈ R.

(* 空集是函数 *)
Fact empty_is_func : is_function ∅.
Proof.
  split; intros x Hx. exfalso0.
  apply domE in Hx as [y Hp]. exfalso0.
Qed.

Lemma func_pair : ∀ F, is_function F →
  ∀p ∈ F, p = < π1 p, π2 p >.
Proof.
  intros F Hf p Hp. destruct Hf as [Hr _].
  exact (rel_pair F Hr p Hp).
Qed.

Lemma func_pair' : ∀ F, is_function F →
  ∀p ∈ F, ∃ x y, <x, y> ∈ F ∧ p = <x, y>.
Proof with auto.
  intros F Hf p Hp. apply func_pair in Hp as Heq...
  exists (π1 p), (π2 p). split... rewrite Heq in Hp...
Qed.

Lemma func_sv : ∀ F a b c, is_function F →
  <a, b> ∈ F → <a, c> ∈ F → b = c.
Proof.
  intros * Hf Hb Hc. destruct Hf as [_ H].
  apply domI in Hb as Hd. apply H in Hd as [x [_ Hu]].
  apply Hu in Hb. apply Hu in Hc. congruence.
Qed.

Lemma func_dom_sv : ∀ F x, is_function F → x ∈ dom F → ∃! y, <x, y> ∈ F.
Proof.
  intros F x Hf Hx. destruct Hf as [_ Hu].
  exact (Hu x Hx).
Qed.

(* 由类型论函数构造集合论函数 *)
Definition Func : set → set → (set → set) → set := λ A B F,
  Rel A B (λ x y, y = F x).

Lemma func_is_func : ∀ F A B, is_function (Func A B F).
Proof.
  intros. split. apply rel_is_rel.
  intros x Hx. rewrite <- unique_existence.
  split. apply domE in Hx. apply Hx.
  intros y1 y2 H1 H2.
  apply SepE in H1 as [_ H1].
  apply SepE in H2 as [_ H2]. zfc_simple.
Qed.

Lemma ident_is_func : ∀ A, is_function (Ident A).
Proof.
  split. apply ident_is_rel.
  intros x Hx. rewrite <- unique_existence.
  split. apply domE in Hx. apply Hx.
  intros y1 y2 H1 H2.
  apply identE in H1 as [].
  apply identE in H2 as []. congruence.
Qed.

Fact ident_eq_func : ∀ A, Ident A = Func A A (λ x, x).
Proof with auto.
intros. apply ExtAx. split; intros.
- apply ReplAx in H as [a [Ha Heq]]. subst x.
  apply SepI. apply CProdI... zfc_simple.
- apply SepE in H as [Hx Heq].
  apply CProdE1 in Hx as [a [Ha [b [_ Hp]]]].
  apply ReplAx. exists a. split...
  rewrite Hp. rewrite Hp in Heq. zfc_simple.
Qed.

(* 函数应用 *)
(* PreAp F x := {<a, b> ∈ F | a = x} = {<x, b>} *)
Definition PreAp : set → set → set := λ F x,
  {p ∊ F | λ p, is_pair p ∧ π1 p = x}.
(* Ap F x := {y | <x, y> ∈ F} *)
Definition Ap : set → set → set := λ F x, π2 ⋃ (PreAp F x).
Notation "F [ x ]" := (Ap F x) (at level 9, format "F [ x ]") : set_scope.

Lemma preAp_unique : ∀ F,
  is_function F → ∀x ∈ dom F, ∃! p, p ∈ PreAp F x.
Proof.
  intros F Hf x Hx.
  apply func_dom_sv in Hx as [y [H Hu]]; [|apply Hf].
  exists <x, y>. split.
  - apply SepI. apply H. split.
    + exists x, y. reflexivity.
    + rewrite π1_correct. reflexivity.
  - intros p Hp.
    apply SepE in Hp as [Hp [Hpp Hπp]].
    apply (op_η p) in Hpp. rewrite Hpp, Hπp in Hp.
    apply Hu in Hp. congruence.
Qed.

Lemma preAp : ∀ F,
  is_function F → ∀x ∈ dom F, ∃y ∈ ran F, PreAp F x = ⎨<x, y>⎬.
Proof.
  intros F Hf x Hd.
  pose proof (preAp_unique F Hf x Hd) as [p [Hp Hu]].
  pose proof (SepE F _ p Hp) as [Hp' [Hpp Hπp]].
  apply (op_η p) in Hpp.
  exists (π2 p). split.
  - apply SepE in Hp as [Hp _]. rewrite Hpp in Hp.
    eapply ranI. apply Hp.
  - apply ExtAx. intros q. split; intros Hq.
    + pose proof (Hu q Hq). subst q.
      rewrite Hpp at 1. rewrite <- Hπp. apply SingI.
    + apply SingE in Hq. rewrite <- Hπp in Hq.
      rewrite Hq. rewrite <- Hpp. apply Hp.
Qed.

Lemma ap_exists : ∀ F,
  is_function F → ∀x ∈ dom F, ∃y ∈ ran F, <x, y> ∈ F ∧ F[x] = y.
Proof.
  intros F H x Hd.
  pose proof (preAp F H x Hd) as [y [Hr Heq]].
  exists y. repeat split.
  - apply Hr.
  - assert (Hxy: < x, y > ∈ ⎨< x, y >⎬) by apply SingI.
    rewrite <- Heq in Hxy.
    apply SepE in Hxy as [Hxy _]. apply Hxy.
  - unfold Ap. rewrite Heq. rewrite union_single.
    rewrite π2_correct. reflexivity.
Qed.

Lemma func_ap : ∀ F x y, is_function F →
  <x, y> ∈ F → F[x] = y.
Proof.
  intros * Hf Hp. apply domI in Hp as Hd.
  pose proof (ap_exists F Hf x Hd) as [y' [_ [Hp' Heq]]].
  subst y'. eapply func_sv; eauto.
Qed.

Lemma func_correct : ∀ F x, is_function F →
  x ∈ dom F → <x, F[x]> ∈ F.
Proof with auto.
  intros F x Hf Hx. apply domE in Hx as [y Hp].
  apply func_ap in Hp as Hap... subst y...
Qed.

Lemma func_point : ∀ F x y, is_function F →
  x ∈ dom F → F[x] = y → <x, y> ∈ F.
Proof with auto.
  intros * Hf Hx Hap. apply func_correct in Hx... subst y...
Qed.

Lemma ran_eq_repl_by_ap : ∀ f, is_function f →
  ran f = {Ap f | x ∊ dom f}.
Proof with auto.
  intros f Hf.
  apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [x Hp].
    apply domI in Hp as Hx. apply func_ap in Hp...
    apply ReplAx. exists x. split...
  - apply ReplAx in Hy as [x [Hx Hap]].
    subst y. eapply ranI. apply func_correct...
Qed.

Lemma func_ext_intro : ∀ F G, is_function F → is_function G →
  dom F = dom G → (∀x ∈ dom F, F[x] = G[x]) → F = G.
Proof with auto.
  intros F G Hf Hg Heqd Heqap.
  apply ExtAx. intros p. split; intros Hp.
  - apply func_pair in Hp as Heqp... rewrite Heqp in Hp.
    apply func_ap in Hp as Hap...
    apply domI in Hp as Hd. rewrite Heqap in Hap; [|apply Hd].
    rewrite Heqd in Hd. apply func_correct in Hd; [|apply Hg].
    rewrite Hap in Hd. rewrite Heqp...
  - apply func_pair in Hp as Heqp... rewrite Heqp in Hp.
    apply func_ap in Hp as Hap...
    apply domI in Hp as Hd. rewrite <- Heqd in Hd.
    rewrite <- Heqap in Hap; [|apply Hd].
    rewrite Heqd in Hd. rewrite <- Heqd in Hd.
    apply func_correct in Hd; [|apply Hf].
    rewrite Hap in Hd. rewrite Heqp...
Qed.

Lemma func_ext_elim : ∀ F G, is_function F → is_function G →
  F = G → dom F = dom G ∧ (∀x ∈ dom F, F[x] = G[x]).
Proof with eauto.
  intros F G Hf Hg Heq. split.
  - apply ExtAx. split; intros Hx.
    + apply domE in Hx as [y Hp]. rewrite Heq in Hp. eapply domI...
    + apply domE in Hx as [y Hp]. rewrite <- Heq in Hp. eapply domI...
  - intros x Hx. apply domE in Hx as [y Hp].
    apply func_ap in Hp as Hap... rewrite Heq in Hap.
    rewrite Hap. apply func_ap...
Qed.

Theorem func_ext : ∀ F G, is_function F → is_function G →
  (dom F = dom G ∧ ∀x ∈ dom F, F[x] = G[x]) ↔ F = G.
Proof with auto.
  intros F G Hf Hg. split.
  - intros []. apply func_ext_intro...
  - apply func_ext_elim...
Qed.

Lemma ident_ap : ∀ X, ∀x ∈ X, (Ident X)[x] = x.
Proof.
  intros X x Hx. apply func_ap.
  - apply ident_is_func.
  - apply ReplAx. exists x. split. apply Hx. reflexivity.
Qed.

(* 单源 *)
Definition single_rooted : set → Prop :=
  λ R, ∀y ∈ ran R, ∃! x, <x, y> ∈ R.

Lemma singrE : ∀ R a b c, single_rooted R →
  <a, c> ∈ R → <b, c> ∈ R → a = b.
Proof.
  intros * Hs Ha Hb. apply ranI in Ha as Hr.
  apply Hs in Hr as [x [_ Hu]].
  apply Hu in Ha. apply Hu in Hb. congruence.
Qed.

Lemma ident_single_rooted : ∀ A, single_rooted (Ident A).
Proof.
  intros A y H. rewrite <- unique_existence.
  split. apply ranE in H. apply H.
  intros y1 y2 H1 H2.
  apply ReplAx in H1 as [x1 [Hx1 H1]]. apply op_iff in H1 as [].
  apply ReplAx in H2 as [x2 [Hx2 H2]]. apply op_iff in H2 as [].
  congruence.
Qed.

(* 单射是单源单值关系 *) (* one-to-one *)
Definition injective : set → Prop :=
  λ R, is_function R ∧ single_rooted R.

Lemma ident_injective : ∀ A, injective (Ident A).
Proof. split. apply ident_is_func. apply ident_single_rooted. Qed.

Lemma injectiveE : ∀ f, injective f →
  ∀ a b ∈ dom f, f[a] = f[b] → a = b.
Proof with eauto.
  intros f [Hf Hs] a Ha b Hb Heq.
  apply func_correct in Ha... apply func_correct in Hb...
  eapply unique_existence. apply Hs.
  eapply ranI... congruence. congruence.
Qed.

(** 逆 **)
Definition Inverse : set → set := λ F,
  {p ∊ (ran F × dom F) | λ p, is_pair p ∧ <π2 p, π1 p> ∈ F}.
Notation "F ⁻¹" := (Inverse F) (at level 9, format "F ⁻¹") : set_scope.

Lemma inv_rel : ∀ R, is_rel R⁻¹.
Proof.
  intros R x Hx. apply SepE in Hx as [_ [Hp _]]. apply Hp.
Qed.
Global Hint Immediate inv_rel : core.

Lemma inv_dom_ran : ∀ F a b, <a, b> ∈ F → <b, a> ∈ ran F × dom F.
Proof.
  intros. apply CProdI.
  eapply ranI. apply H. eapply domI. apply H.
Qed.

Lemma inv_op : ∀ F, ∀ x y, <x, y> ∈ F ↔ <y, x> ∈ F⁻¹.
Proof.
  split; intros.
  - apply SepI; try split.
    + apply inv_dom_ran. apply H.
    + exists y, x. reflexivity.
    + rewrite π1_correct, π2_correct. apply H.
  - apply SepE in H as [_ [_ H]].
    rewrite π1_correct, π2_correct in H. apply H.
Qed.

Lemma inv_ident : ∀ A, (Ident A)⁻¹ = Ident A.
Proof with auto.
  intros. apply ExtAx. split; intros Hx.
  - apply SepE in Hx as [_ [[a [b H]] Hx]]. subst x. zfc_simple.
    apply identE in Hx as [Hb H]. subst. apply identI...
  - apply ReplAx in Hx as [a [Ha Hx]]. subst x.
    rewrite <- inv_op. apply identI...
Qed.

Theorem inv_dom : ∀ F, dom F⁻¹ = ran F.
Proof.
  intros. apply ExtAx. split; intros.
  - apply domE in H as [y Hp]. apply inv_op in Hp.
    eapply ranI. apply Hp.
  - apply ranE in H as [w Hp]. apply inv_op in Hp.
    eapply domI. apply Hp.
Qed.

Theorem inv_ran : ∀ F, ran F⁻¹ = dom F.
Proof.
  intros. apply ExtAx. split; intros.
  - apply ranE in H as [y Hp]. apply inv_op in Hp.
    eapply domI. apply Hp.
  - apply domE in H as [w Hp]. apply inv_op in Hp.
    eapply ranI. apply Hp.
Qed.

Theorem inv_inv : ∀ F, is_rel F → (F⁻¹)⁻¹ = F.
Proof.
  intros. apply ExtAx. split; intros Hx.
  - apply SepE in Hx as [_ [Hp Hx]]. rewrite <- inv_op in Hx.
    apply op_η in Hp. rewrite <- Hp in Hx. apply Hx.
  - unfold is_rel in H.
    pose proof (H x Hx) as [a [b Heq]].
    subst x. apply SepI; try split.
    + apply inv_dom_ran. rewrite <- inv_op. apply Hx.
    + exists a, b. reflexivity.
    + apply SepI; try split; repeat rewrite π1_correct, π2_correct.
      * apply inv_dom_ran. apply Hx.
      * exists b, a. reflexivity.
      * apply Hx.
Qed.

Theorem inv_func_iff_sr : ∀ F, is_function F⁻¹ ↔ single_rooted F.
Proof.
  unfold is_function, is_rel, single_rooted. split.
  - intros [_ Hs]. intros y Hy. rewrite <- inv_dom in Hy.
    apply Hs in Hy as [x [Hp H]]. exists x. split.
    + rewrite inv_op. apply Hp.
    + intros x' Hx'. apply H; rewrite <- inv_op; assumption.
  - intros Hs. split.
    + intros x Hx. apply SepE in Hx as [_ [Hp _]]. apply Hp.
    + intros x Hx. rewrite inv_dom in Hx.
      apply Hs in Hx as [y [Hp H]]. exists y. split.
      * rewrite <- inv_op. apply Hp.
      * intros y' Hy'. apply H; rewrite inv_op; assumption.
Qed.

Theorem inv_sr_iff_func : ∀ F, 
  (is_rel F ∧ single_rooted F⁻¹) ↔ is_function F.
Proof with auto.
  unfold single_rooted, is_function. split.
  - intros [Hr Hs]. split...
    intros x Hx. rewrite <- inv_ran in Hx.
    apply Hs in Hx as [y [Hp H]]. exists y. split.
    + rewrite inv_op...
    + intros y' Hy'. apply H; rewrite <- inv_op...
  - intros [Hr Hs]. split... intros y Hy. rewrite inv_ran in Hy.
    apply Hs in Hy as [x [Hp H]]. exists x. split.
    + rewrite <- inv_op...
    + intros x' Hx'. apply H; rewrite inv_op...
Qed.

Theorem inv_injective : ∀ F, injective F → injective F⁻¹.
Proof with auto.
  intros F [Hf Hs]. split.
  - apply inv_func_iff_sr...
  - apply inv_sr_iff_func...
Qed.

Theorem inv_dom_reduction : ∀ F,
  injective F → ∀x ∈ dom F, F⁻¹[F[x]] = x.
Proof.
  unfold injective. intros F [Hf Hs] x Hx.
  apply func_correct in Hx; [|apply Hf]. apply func_ap.
  - apply inv_func_iff_sr. apply Hs.
  - rewrite inv_op in Hx. apply Hx.
Qed.

Theorem inv_ran_reduction : ∀ F,
  injective F → ∀y ∈ ran F, F[F⁻¹[y]] = y.
Proof.
  unfold injective. intros F [Hf Hs] y Hy.
  assert (Hr := Hf). destruct Hr as [Hr _].
  rewrite <- inv_dom in Hy. cut (injective F⁻¹). intros Hinj.
  pose proof (inv_dom_reduction F⁻¹ Hinj y Hy).
  rewrite inv_inv in H. apply H. apply Hr.
  unfold injective. split. 
  - apply inv_func_iff_sr. apply Hs.
  - apply inv_sr_iff_func. apply Hf.
Qed.

Fact inv_as_repl : ∀ F, injective F →
  F⁻¹ = {λ p, <π2 p, π1 p> | p ∊ F}.
Proof with eauto.
  intros F Hinj.
  apply ExtAx. intros p. split; intros Hp.
  - apply ReplAx. exists <π2 p, π1 p>. split.
    + rewrite (rel_pair F⁻¹) in Hp... apply inv_op...
    + zfc_simple. symmetry. eapply func_pair...
      apply inv_func_iff_sr. apply Hinj.
  - apply ReplAx in Hp as [q [Hq Heq]].
    rewrite (rel_pair F) in Hq; [|apply Hinj|auto].
    subst p. apply SepI. apply CProdI.
    eapply ranI... eapply domI... split... zfc_simple.
Qed.

(** 复合 **)
Definition Composition : set → set → set := λ F G,
  {p ∊ (dom G × ran F) | λ p, is_pair p ∧
    ∃ y, <π1 p, y> ∈ G ∧ <y, π2 p> ∈ F}.
Notation "F ∘ G" := (Composition F G) (at level 60) : set_scope.

Lemma compoI : ∀ F G x y t,
  <x, t> ∈ G → <t, y> ∈ F → <x, y> ∈ (F ∘ G).
Proof with eauto.
  intros * Hpg Hpf. apply SepI; try split.
  - apply CProdI. eapply domI... eapply ranI...
  - exists x, y...
  - rewrite π1_correct, π2_correct. exists t...
Qed.

Lemma compoE : ∀ F G x y,
  <x, y> ∈ (F ∘ G) → ∃ t, <x, t> ∈ G ∧ <t, y> ∈ F.
Proof.
  intros. apply SepE in H as [_ [_ [t [Htg Htf]]]].
  rewrite π1_correct, π2_correct in *.
  exists t. split; assumption.
Qed.

Lemma compo_rel : ∀ F G, is_rel (F ∘ G).
Proof.
  intros. intros x Hx. apply SepE in Hx as [_ [Hp _]]. apply Hp.
Qed.

Lemma compo_func : ∀ F G,
  is_function F → is_function G → is_function (F ∘ G).
Proof.
  intros F G Hf Hg. split.
  - intros x Hx. apply SepE in Hx as [_ [H _]]. apply H.
  - intros x Hx. apply domE in Hx as [y Hy].
    exists y. split. apply Hy.
    intros y' Hy'.
    apply compoE in Hy  as [t  [Htg  Htf]].
    apply compoE in Hy' as [t' [Ht'g Ht'f]].
    apply domI in Htg as Hdg.
    assert (t = t') by (eapply func_sv; eauto). subst t'.
    clear Htg Ht'g Hg. apply domI in Htf as Hdf.
    eapply func_sv; eauto.
Qed.

Lemma compo_dom : ∀ F G,
  is_function F → is_function G →
  dom (F ∘ G) = {x ∊ dom G | λ x, G[x] ∈ dom F}.
Proof with eauto.
  intros F G Hf Hg. apply ExtAx. split; intros.
  - apply domE in H as [y Hp].
    apply compoE in Hp as [t [Hpg Hpf]].
    apply SepI. eapply domI. apply Hpg.
    apply func_ap in Hpg; [|apply Hg]. subst t.
    eapply domI. apply Hpf.
  - apply SepE in H as [Hdg Hdf].
    apply domE in Hdg as [t Hpg].
    apply domE in Hdf as [y Hpf].
    apply func_ap in Hpg as Hap... subst t.
    eapply domI. eapply compoI...
Qed.

Lemma compo_ran : ∀ F G,
  injective F → is_function G →
  ran (F ∘ G) = {x ∊ ran F | λ x, F⁻¹[x] ∈ ran G}.
Proof with eauto.
  intros F G [Hf Hs] Hg.
  assert (Hf': is_function F ⁻¹) by (apply inv_func_iff_sr; auto).
  apply ExtAx. intros y. split; intros Hy.
  - apply ranE in Hy as [x Hp].
    apply compoE in Hp as [t [Hpg Hpf]].
    apply SepI. eapply ranI. apply Hpf.
    apply inv_op in Hpf. apply func_ap in Hpf...
    subst t. eapply ranI. apply Hpg.
  - apply SepE in Hy as [Hrf Hrg].
    apply ranE in Hrf as [t Hpf].
    apply ranE in Hrg as [x Hpg].
    apply inv_op in Hpf as Hpf'. apply func_ap in Hpf'...
    subst t. eapply ranI. eapply compoI...
Qed.

Theorem compo_correct : ∀ F G,
  is_function F → is_function G →
  ∀x ∈ dom (F ∘ G), (F ∘ G)[x] = F[G[x]].
Proof with auto.
  intros F G Hf Hg x Hx.
  apply domE in Hx as [y Hp].
  pose proof (compo_func _ _ Hf Hg) as Hcf.
  apply func_ap in Hp as Hap...
  apply compoE in Hp as [t [Hpg Hpf]].
  apply func_ap in Hpg; [|apply Hg].
  apply func_ap in Hpf; [|apply Hf]. subst t y...
Qed.

Example compo_inv_dom : ∀ G,
  injective G → dom (G⁻¹ ∘ G) = dom G.
Proof.
  intros G [Hg Hs].
  rewrite compo_dom.
  - apply ExtAx. split; intros.
    + apply SepE in H as [H _]. apply H.
    + apply SepI. apply H. rewrite inv_dom.
      eapply ranI. apply func_correct in H. apply H. apply Hg.
  - apply inv_func_iff_sr. apply Hs.
  - apply Hg.
Qed.

Example compo_inv_dom_eq : ∀ G,
  injective G → ∀x ∈ dom (G⁻¹ ∘ G), (G⁻¹ ∘ G)[x] = x.
Proof.
  intros G Hinj x Hx. rewrite compo_correct.
  - rewrite inv_dom_reduction. reflexivity. apply Hinj.
    rewrite compo_inv_dom in Hx. apply Hx. apply Hinj.
  - apply inv_func_iff_sr. destruct Hinj as [_ Hs]. apply Hs.
  - destruct Hinj as [Hg _]. apply Hg.
  - apply Hx.
Qed.

Example compo_inv_dom_ident : ∀ G,
  injective G → (G⁻¹ ∘ G) = Ident (dom G).
Proof with auto.
  intros G Hi. assert (Hi' := Hi).
  destruct Hi' as [Hf Hs]. apply func_ext_intro.
  - apply compo_func... apply inv_func_iff_sr...
  - apply ident_is_func.
  - rewrite compo_inv_dom, dom_ident...
  - intros x Hx. assert (Hx' := Hx).
    rewrite compo_inv_dom in Hx'...
    rewrite compo_inv_dom_eq... rewrite ident_ap...
Qed.

Example compo_inv_ran_ident : ∀ G,
  is_function G → (G ∘ G⁻¹) = Ident (ran G).
Proof.
  intros G Hg. apply ExtAx. intros p. split; intros Hp.
  - apply SepE in Hp as [_ [[a [b Hp]] [y [H1 H2]]]].
    apply inv_op in H1. apply domI in H1 as Hd.
    assert (π1 p = π2 p) by (eapply func_sv; eauto).
    rewrite Hp in H. apply ranI in H1 as Hr. rewrite Hp in Hr.
    rewrite π1_correct, π2_correct in *. clear H1 H2.
    rewrite <- H in Hp. rewrite Hp. apply ReplAx.
    exists a. split. apply Hr. reflexivity.
  - apply ReplAx in Hp as [b [Hb Hp]]. subst p.
    pose proof (ranE _ _ Hb) as [a Hp].
    assert (Hp' := Hp). rewrite inv_op in Hp'.
    eapply compoI; eauto.
Qed.

Example compo_inv_ran : ∀ G,
  is_function G → dom (G ∘ G⁻¹) = ran G.
Proof.
  intros G Hg. rewrite compo_inv_ran_ident.
  rewrite dom_ident. reflexivity. apply Hg.
Qed.

Theorem compo_inv : ∀ F G, (F ∘ G)⁻¹ = G⁻¹ ∘ F⁻¹.
Proof with eauto.
  intros. pose proof (compo_rel G ⁻¹ F ⁻¹) as Hr2.
  apply ExtAx. intros x. split; intros Hx.
  - apply rel_pair in Hx as Heq...
    rewrite Heq in *. rewrite <-inv_op in Hx.
    apply compoE in Hx as [t [Hpg Hpf]].
    rewrite inv_op in Hpg, Hpf. eapply compoI...
  - apply rel_pair in Hx as Heq...
    rewrite Heq in *. rewrite <- inv_op.
    apply compoE in Hx as [t [Hpg Hpf]].
    rewrite <- inv_op in Hpg, Hpf. eapply compoI...
Qed.
