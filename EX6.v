(** Based on "Elements of Set Theory" Chapter 3 Part 1 **)
(** Coq coding by choukh, May 2020 **)

Require Export ZFC.EX5.

(*** TG集合论扩展6：关系，函数(标准编码)，逆，复合 ***)

(** 二元关系 **)
Definition Relation : set → set → (set → set → Prop) → set :=
  λ A B P, {p ∊ A × B | λ p, P (π1 p) (π2 p)}.

(* 恒等关系 *)
Definition Ident : set → set := λ X, {λ x, <x, x> | x ∊ X}.

Example ident_rel_ident : ∀ X,
  Ident X = Relation X X (λ a b, a = b).
Proof.
  intros. apply ExtAx. split; intros.
  - apply ReplE in H as [a [Ha Heq]]. subst x.
    apply SepI. apply CProdI; assumption.
    rewrite π1_correct, π2_correct. reflexivity.
  - apply SepE in H as [Hx Heq].
    apply CProd_correct in Hx as [a [Ha [b [_ Hp]]]].
    apply ReplAx. exists a. split. apply Ha.
    rewrite Hp. rewrite Hp in Heq.
    rewrite π1_correct, π2_correct in Heq. subst b. reflexivity.
Qed.

Lemma identI : ∀ X, ∀a ∈ X, <a, a> ∈ Ident X.
Proof.
  intros * a Ha. apply ReplAx. exists a. split; auto.
Qed.

Lemma identE : ∀ X a b, <a, b> ∈ Ident X → a ∈ X ∧ a = b.
Proof.
  intros. apply ReplE in H as [c [Ha Heq]].
  apply op_correct in Heq as []. subst. auto.
Qed.

Definition is_relation : set → Prop := λ X, ∀x ∈ X, is_pair x.

Lemma relE : ∀ R, is_relation R → ∀p ∈ R, p = < π1 p, π2 p >.
Proof.
  intros R Hr p Hp. apply Hr in Hp. apply op_η in Hp. apply Hp.
Qed.

(* 定义域 *)
Definition dom : set → set :=
  λ R, {x ∊ ⋃⋃R | λ x, ∃ y, <x, y> ∈ R}.

(* 值域 *)
Definition ran : set → set :=
  λ R, {x ∊ ⋃⋃R | λ x, ∃ w, <w, x> ∈ R}.

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

Lemma ident_dom : ∀ X, dom (Ident X) = X.
Proof.
  intros. apply ExtAx. split; intros.
  - apply domE in H as [y Hp]. apply identE in Hp as []. auto.
  - eapply domI. apply ReplAx. exists x. split.
    apply H. reflexivity.
Qed.

(* 存在唯一 *)
Definition exu: (set → Prop) → Prop :=
  λ P, (∃ x, P x) ∧ (∀ x y, P x → P y → x = y).
Notation "∃! x , p" := (exu (λ x, p)) (at level 200, x ident).
Notation "∄! x , p" := (¬ exu (λ x, p)) (at level 200, x ident).

(** 函数（标准编码） **)

(* 函数是单值关系 *)
Definition is_function : set → Prop :=
  λ R, is_relation R ∧ ∀x ∈ dom R, ∃! y, <x, y> ∈ R.

Lemma ident_is_func : ∀ X, is_function (Ident X).
Proof.
  unfold is_function, is_relation. repeat split.
  - intros x Hx. apply ReplE in Hx as [a [_ Heq]].
    exists a, a. subst x. reflexivity.
  - apply domE in H. apply H.
  - intros y y' Hy Hy'.
    apply identE in Hy as []. apply identE in Hy' as [].
    subst. reflexivity.
Qed.

Lemma funcE1 : ∀ F, is_function F → ∀p ∈ F, p = < π1 p, π2 p >.
Proof.
  intros F Hf p Hp. destruct Hf as [Hr _]. exact (relE F Hr p Hp).
Qed.

Lemma funcE2 : ∀ F a b c, is_function F →
  <a, b> ∈ F → <a, c> ∈ F → b = c.
Proof.
  intros * Hf Hb Hc. destruct Hf as [_ H].
  apply domI in Hb as Hd. apply H in Hd as [_ Hu]. apply Hu; auto.
Qed.

Lemma funcDomE1 : ∀ F x, is_function F → x ∈ dom F → ∃! y, <x, y> ∈ F.
Proof.
  intros F x Hf Hx. destruct Hf as [_ Hu].
  exact (Hu x Hx).
Qed.

(* pre_ap F x := {<a, b> ∈ F | a = x} = {<x, b>} *)
Definition pre_ap : set → set → set := λ F x,
  {p ∊ F | λ p, is_pair p ∧ π1 p = x}.

(* 函数应用 *)
(* ap F x := {y | <x, y> ∈ F} *)
Definition ap : set → set → set := λ F x, π2 ⋃ (pre_ap F x).
Notation "F [ x ]" := (ap F x) (at level 9).

Lemma pre_ap_single : ∀ F,
  is_function F → ∀x ∈ dom F, ∃! p, p ∈ pre_ap F x.
Proof.
  intros F Hf x Hx.
  apply funcDomE1 in Hx as [[y H] Hexu]; [|apply Hf]. split.
  - exists <x, y>. apply SepI. apply H. split.
    + exists x, y. reflexivity.
    + rewrite π1_correct. reflexivity.
  - intros p q Hp Hq.
    apply SepE in Hp as [Hp [Hpp Hπp]].
    apply SepE in Hq as [Hq [Hpq Hπq]].
    apply (op_η p) in Hpp. rewrite Hpp, Hπp in Hp.
    apply (op_η q) in Hpq. rewrite Hpq, Hπq in Hq.
    pose proof (Hexu _ _ Hp Hq).
    rewrite Hpq, Hpp, Hπp, Hπq, H0. reflexivity.
Qed.

Lemma pre_ap_exists : ∀ F,
  is_function F → ∀x ∈ dom F, ∃y ∈ ran F, pre_ap F x = ⎨<x, y>⎬.
Proof.
  unfoldq. intros F Hf x Hd.
  pose proof (pre_ap_single F Hf x Hd) as [[p Hp] Hu].
  pose proof (SepE F _ p Hp) as [Hp' [Hpp Hπp]].
  apply (op_η p) in Hpp.
  exists (π2 p). split.
  - apply SepE in Hp as [Hp _]. rewrite Hpp in Hp.
    eapply ranI. apply Hp.
  - apply ExtAx. intros q. split; intros Hq.
    + pose proof (Hu p q Hp Hq). subst q.
      rewrite Hpp at 1. rewrite <- Hπp. apply SingI.
    + apply SingE in Hq. rewrite <- Hπp in Hq.
      rewrite Hq. rewrite <- Hpp. apply Hp.
Qed.

Lemma ap_exists : ∀ F,
  is_function F → ∀x ∈ dom F, ∃y ∈ ran F, <x, y> ∈ F ∧ F[x] = y.
Proof.
  unfoldq. intros F H x Hd.
  pose proof (pre_ap_exists F H x Hd) as [y [Hr Heq]].
  exists y. repeat split.
  - apply Hr.
  - assert (Hxy: < x, y > ∈ ⎨< x, y >⎬) by apply SingI.
    rewrite ExtAx in Heq. apply Heq in Hxy.
    apply SepE in Hxy as [Hxy _]. apply Hxy.
  - unfold ap. rewrite Heq. rewrite union_sing_x_x.
    rewrite π2_correct. reflexivity.
Qed.

Lemma apI : ∀ F,
  is_function F → ∀ x y, <x, y> ∈ F → F[x] = y.
Proof.
  intros F Hf x y Hp. apply domI in Hp as Hd.
  pose proof (ap_exists F Hf x Hd) as [y' [_ [Hp' Heq]]].
  subst y'. eapply funcE2; eauto.
Qed.

Lemma ident_correct : ∀ X, ∀x ∈ X, (Ident X)[x] = x.
Proof.
  intros X x Hx. apply apI.
  - apply ident_is_func.
  - apply ReplAx. exists x. split. apply Hx. reflexivity.
Qed.

Lemma funcDomE2 : ∀ F x, is_function F → x ∈ dom F → <x, F[x]> ∈ F.
Proof.
  intros F x Hf Hx. apply domE in Hx as [y Hp].
  pose proof (apI _ Hf _ _ Hp). subst y. apply Hp.
Qed.

Theorem func_ext : ∀ F G,
  is_function F → is_function G → dom F = dom G
  → (∀x ∈ dom F, F[x] = G[x]) → F = G.
Proof.
  intros F G Hf Hg Heqd Heqap.
  apply ExtAx. intros p. split; intros Hp.
  - pose proof (funcE1 _ Hf _ Hp) as Heqp.
    simpl in Heqp. rewrite Heqp in Hp.
    pose proof (apI _ Hf _ _ Hp) as Hap.
    apply domI in Hp as Hd. rewrite Heqap in Hap; [|apply Hd].
    rewrite Heqd in Hd. apply funcDomE2 in Hd; [|apply Hg].
    rewrite Hap in Hd. rewrite Heqp. apply Hd.
  - pose proof (funcE1 _ Hg _ Hp) as Heqp.
    simpl in Heqp. rewrite Heqp in Hp.
    pose proof (apI _ Hg _ _ Hp) as Hap.
    apply domI in Hp as Hd. rewrite <- Heqd in Hd.
    rewrite <- Heqap in Hap; [|apply Hd].
    rewrite Heqd in Hd. rewrite <- Heqd in Hd.
    apply funcDomE2 in Hd; [|apply Hf].
    rewrite Hap in Hd. rewrite Heqp. apply Hd.
Qed.

(* 单源 *)
Definition single_rooted : set → Prop :=
  λ R, ∀y ∈ ran R, ∃! x, <x, y> ∈ R.

Lemma singrE : ∀ R a b c, single_rooted R →
  <a, c> ∈ R → <b, c> ∈ R → a = b.
Proof.
  intros * Hs Ha Hb. apply ranI in Ha as Hr.
  apply Hs in Hr as [_ Hu]. apply Hu; auto.
Qed.

(* 一一对应是单源单值关系 *)
Definition injection : set → Prop :=
  λ R, is_function R ∧ single_rooted R.

(** 逆 **)
Definition Inverse : set → set := λ F,
  {p ∊ (ran F × dom F) | λ p, is_pair p ∧ <π2 p, π1 p> ∈ F}.
Notation "F ⁻¹" := (Inverse F) (at level 9).

Lemma inv_rel : ∀ F, is_relation F⁻¹.
Proof.
  intros F x Hx. apply SepE in Hx as [_ [Hp _]]. apply Hp.
Qed.

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

Theorem inv_inv_ident : ∀ F, is_relation F → (F⁻¹)⁻¹ = F.
Proof.
  intros. apply ExtAx. split; intros Hx.
  - apply SepE in Hx as [_ [Hp Hx]]. rewrite <- inv_op in Hx.
    apply op_η in Hp. rewrite <- Hp in Hx. apply Hx.
  - unfold is_relation in H.
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
  unfold is_function, is_relation, single_rooted. split.
  - intros [_ Hs]. intros y Hy. rewrite <- inv_dom in Hy.
    apply Hs in Hy as [[x Hp] H]. split.
    + exists x. rewrite inv_op. apply Hp.
    + intros x1 x2 H1 H2. apply H; rewrite <- inv_op; assumption.
  - intros Hs. split.
    + intros x Hx. apply SepE in Hx as [_ [Hp _]]. apply Hp.
    + intros x Hx. rewrite inv_dom in Hx.
      apply Hs in Hx as [[y Hp] H]. split.
      * exists y. rewrite <- inv_op. apply Hp.
      * intros y1 y2 H1 H2. apply H; rewrite inv_op; assumption.
Qed.

Theorem inv_sr_iff_func : ∀ F, 
  is_relation F → single_rooted F⁻¹ ↔ is_function F.
Proof.
  intros F Hr. unfold single_rooted, is_function. split.
  - intros Hs. split.
    + apply Hr.
    + intros x Hx. rewrite <- inv_ran in Hx.
      apply Hs in Hx as [[y Hp] H]. split.
      * exists y. rewrite inv_op. apply Hp.
      * intros y1 y2 H1 H2. apply H; rewrite <- inv_op; assumption.
  - intros [_ Hs]. intros y Hy. rewrite inv_ran in Hy.
    apply Hs in Hy as [[x Hp] H]. split.
    + exists x. rewrite <- inv_op. apply Hp.
    + intros x1 x2 H1 H2. apply H; rewrite inv_op; assumption.
Qed.

Theorem inv_dom_reduction : ∀ F,
  injection F → ∀x ∈ dom F, F⁻¹[F[x]] = x.
Proof.
  unfold injection. intros F [Hf Hs] x Hx.
  apply funcDomE2 in Hx; [|apply Hf]. apply apI.
  - apply inv_func_iff_sr. apply Hs.
  - rewrite inv_op in Hx. apply Hx.
Qed.

Theorem inv_ran_reduction : ∀ F,
  injection F → ∀y ∈ ran F, F[F⁻¹[y]] = y.
Proof.
  unfold injection. intros F [Hf Hs] y Hy.
  assert (Hr := Hf). destruct Hr as [Hr _].
  rewrite <- inv_dom in Hy. cut (injection F⁻¹). intros Hinj.
  pose proof (inv_dom_reduction F⁻¹ Hinj y Hy).
  rewrite inv_inv_ident in H. apply H. apply Hr.
  unfold injection. split. 
  - apply inv_func_iff_sr. apply Hs.
  - apply inv_sr_iff_func. apply Hr. apply Hf.
Qed.

(** 复合 **)
Definition Composition : set → set → set := λ F G,
  {p ∊ (dom G × ran F) | λ p, is_pair p ∧
    ∃ y, <π1 p, y> ∈ G ∧ <y, π2 p> ∈ F}.
Notation "F ∘ G" := (Composition F G) (at level 60).

Lemma compoI : ∀ F G x y t,
  <x, t> ∈ G ∧ <t, y> ∈ F → <x, y> ∈ (F ∘ G).
Proof with eauto.
  intros * [Hpg Hpf]. apply SepI; try split.
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

Lemma compo_rel : ∀ F G, is_relation (F ∘ G).
Proof.
  intros. intros x Hx. apply SepE in Hx as [_ [Hp _]]. apply Hp.
Qed.

Lemma compo_func : ∀ F G,
  is_function F → is_function G → is_function (F ∘ G).
Proof.
  intros F G Hf Hg. repeat split.
  - intros x Hx. apply SepE in Hx as [_ [H _]]. apply H.
  - apply domE in H. apply H.
  - intros y y' Hy Hy'.
    apply compoE in Hy  as [t  [Htg  Htf]].
    apply compoE in Hy' as [t' [Ht'g Ht'f]].
    apply domI in Htg as Hdg.
    assert (t = t') by (eapply funcE2; eauto). subst t'.
    clear Htg Ht'g Hg. apply domI in Htf as Hdf.
    eapply funcE2; eauto.
Qed.

Lemma compo_dom : ∀ F G,
  is_function F → is_function G →
  dom (F ∘ G) = {x ∊ dom G | λ x, G[x] ∈ dom F}.
Proof.
  intros F G Hf Hg. apply ExtAx. split; intros.
  - apply domE in H as [y Hp].
    apply compoE in Hp as [t [Hpg Hpf]].
    apply SepI. eapply domI. apply Hpg.
    apply apI in Hpg; [|apply Hg]. subst t.
    eapply domI. apply Hpf.
  - apply SepE in H as [Hdg Hdf].
    apply domE in Hdg as [t Hpg].
    apply domE in Hdf as [y Hpf].
    pose proof (apI _ Hg _ _ Hpg). rewrite H in Hpf.
    eapply domI. eapply compoI. eauto.
Qed.

Theorem compo_correct : ∀ F G,
  is_function F → is_function G →
  ∀x ∈ dom (F ∘ G), (F ∘ G)[x] = F[G[x]].
Proof.
  intros F G Hf Hg x Hx.
  apply domE in Hx as [y Hp].
  pose proof (compo_func _ _ Hf Hg) as Hcf.
  pose proof (apI _ Hcf _ _ Hp).
  apply compoE in Hp as [t [Hpg Hpf]].
  apply apI in Hpg; [|apply Hg].
  apply apI in Hpf; [|apply Hf].
  subst t y. apply H.
Qed.

Example compo_inv_dom : ∀ G,
  injection G → dom (G⁻¹ ∘ G) = dom G.
Proof.
  intros G [Hg Hs].
  rewrite compo_dom.
  - apply ExtAx. split; intros.
    + apply SepE in H as [H _]. apply H.
    + apply SepI. apply H. rewrite inv_dom.
      eapply ranI. apply funcDomE2 in H. apply H. apply Hg.
  - apply inv_func_iff_sr. apply Hs.
  - apply Hg.
Qed.

Example compo_inv_dom_eq : ∀ G,
  injection G → ∀x ∈ dom (G⁻¹ ∘ G), (G⁻¹ ∘ G)[x] = x.
Proof.
  intros G Hinj x Hx. rewrite compo_correct.
  - rewrite inv_dom_reduction. reflexivity. apply Hinj.
    rewrite compo_inv_dom in Hx. apply Hx. apply Hinj.
  - apply inv_func_iff_sr. destruct Hinj as [_ Hs]. apply Hs.
  - destruct Hinj as [Hg _]. apply Hg.
  - apply Hx.
Qed.

Example compo_inv_dom_ident : ∀ G,
  injection G → (G⁻¹ ∘ G) = Ident (dom G).
Proof with auto.
  intros G Hi. assert (Hi' := Hi).
  destruct Hi' as [Hf Hs]. apply func_ext.
  - apply compo_func... apply inv_func_iff_sr...
  - apply ident_is_func.
  - rewrite compo_inv_dom, ident_dom...
  - intros x Hx. assert (Hx' := Hx).
    rewrite compo_inv_dom in Hx'...
    rewrite compo_inv_dom_eq... rewrite ident_correct...
Qed.

Example compo_inv_ran_ident : ∀ G,
  is_function G → (G ∘ G⁻¹) = Ident (ran G).
Proof.
  intros G Hg. apply ExtAx. intros p. split; intros Hp.
  - apply SepE in Hp as [_ [[a [b Hp]] [y [H1 H2]]]].
    apply inv_op in H1. apply domI in H1 as Hd.
    assert (π1 p = π2 p) by (eapply funcE2; eauto).
    rewrite Hp in H. apply ranI in H1 as Hr. rewrite Hp in Hr.
    rewrite π1_correct, π2_correct in *. clear H1 H2.
    rewrite <- H in Hp. rewrite Hp. apply ReplAx.
    exists a. split. apply Hr. reflexivity.
  - apply ReplE in Hp as [b [Hb Hp]]. subst p.
    pose proof (ranE _ _ Hb) as [a Hp].
    assert (Hp' := Hp). rewrite inv_op in Hp'.
    eapply compoI. eauto.
Qed.

Example compo_inv_ran : ∀ G,
  is_function G → dom (G ∘ G⁻¹) = ran G.
Proof.
  intros G Hg. rewrite compo_inv_ran_ident.
  rewrite ident_dom. reflexivity. apply Hg.
Qed.

Theorem compo_inv : ∀ F G, (F ∘ G)⁻¹ = G⁻¹ ∘ F⁻¹.
Proof with eauto.
  intros.
  pose proof (inv_rel (F ∘ G)) as Hr1.
  pose proof (compo_rel G ⁻¹ F ⁻¹) as Hr2.
  apply ExtAx. intros x. split; intros Hx.
  - apply relE in Hx as Heq...
    rewrite Heq in *. rewrite <-inv_op in Hx.
    apply compoE in Hx as [t [Hpg Hpf]].
    rewrite inv_op in Hpg, Hpf. eapply compoI...
  - apply relE in Hx as Heq...
    rewrite Heq in *. rewrite <- inv_op.
    apply compoE in Hx as [t [Hpg Hpf]].
    rewrite <- inv_op in Hpg, Hpf. eapply compoI...
Qed.
