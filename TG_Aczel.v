(*** Formal Construction of a Set Theory in Coq ***)
(** based on the thesis by Jonas Kaiser, November 23, 2012 **)
(** Coq programming by choukh, April 2020 **)

Require Export ZFC.TG_full.

Open Scope TG1_scope.

(*** TG集合论：函数(Aczel编码)，有限序数及其递归原理 ***)

(** 函数（Aczel编码） **)

(* 函数应用 *)
(* ap f x := {y | <x, y> ∈ f} *)
Definition ap : set → set → set := λ f x,
  let P := {p ∊ f | λ p, is_pair p ∧ π1 p = x} in {π2 | p ∊ P}.
Notation "f [ x ]" := (ap f x) (at level 60).

(* 函数本身 *)
(* Lambda X F := {<x, y> | x ∈ X ∧ y ∈ F x} *)
Definition Lambda : set → (set → set) → set := λ X F,
  ⋃{λ x, {λ y, <x, y> | y ∊ F x} | x ∊ X}.
Notation "'Λ' X , F" := (Lambda X F) (at level 200).

(* 函数类型 *)
(* Π X Y := {Lambda X F | ∀x ∈ X, F x ∈ Y x}
          = {f ∈ 𝒫(X × ⋃⋃{Y|x ∊ X}) | ∀x ∈ X, F x ∈ Y x} *)
Definition Π : set → (set → set) → set := λ X Y, 
  {f ∊ 𝒫(X × ⋃⋃{Y|x ∊ X}) | λ f, ∀x ∈ X, f[x] ∈ Y x}.

(* 非依赖类型 *)
Definition Arrow : set → set → set := λ X Y, Π X (λ _, Y).
Notation "X ⟶ Y" := (Arrow X Y) (at level 190).

(* 常函数正好表达为笛卡尔积 *)
Fact Λ_const_is_cprod : ∀ A B, A × B = Λ A, (λ _, B).
Proof. reflexivity. Qed.

(* 函数的成员都是这样的有序对，它的左投影是定义域的成员，右投影是值域的成员的成员 *)
Lemma Λ_contain_pair : ∀ X F,
  ∀p ∈ (Λ X, F), ∃x ∈ X, ∃y ∈ F x, p = <x, y>.
Proof.
  unfoldq. unfold Lambda. intros X F p H.
  apply FUnionE in H. destruct H as [x [H1 H2]].
  apply ReplE in H2. destruct H2 as [y [H2 H3]].
  symmetry in H3. firstorder.
Qed.

Lemma ap_contain_pair : ∀ f x y, y ∈ f[x] ↔ <x, y> ∈ f.
Proof.
  split; intros.
  - apply ReplE in H. destruct H as [p [H1 H2]].
    apply SepE in H1. destruct H1 as [H3 [H4 H5]].
    apply op_η in H4. rewrite H4 in H3. subst. apply H3.
  - unfold ap. apply ReplAx. unfoldq.
    exists <x, y>. split.
    + apply SepI. apply H. split.
      * exists x, y. reflexivity.
      * apply π1_correct.
    + apply π2_correct.
Qed.

(* β规约 *)
Theorem β_reduction : ∀ X F, ∀x ∈ X, (Λ X, F)[x] = F x.
Proof.
  introq. apply ExtAx. split; intros.
  - apply ap_contain_pair in H0.
    apply Λ_contain_pair in H0.
    destruct H0 as [a [H1 [b [H2 H3]]]].
    apply op_correct in H3. destruct H3 as [H3 H4].
    subst. apply H2.
  - apply ap_contain_pair. eapply UnionI.
    + apply ReplI. apply H.
    + apply ReplI. apply H0.
Qed.

Lemma β_out_0 : ∀ X F x, x ∉ X → (Λ X, F)[x] = ∅.
Proof.
  intros. apply EmptyI. intros y H0. apply H.
  apply ap_contain_pair in H0.
  apply Λ_contain_pair in H0. destruct H0 as [a [H1 [b [H2 H3]]]].
  apply op_correct in H3 as [Hx Hy]. subst a. apply H1.
Qed.

Lemma ap_0_0 : ∀ a, ∅[a] = ∅.
Proof.
  unfold ap. introq. rewrite sep_0.
  rewrite repl0I. reflexivity.
Qed.

(* 函数是函数类型的成员 *)
Theorem Λ_in_Π : ∀ X Y F, (∀x ∈ X, F x ∈ Y x) → (Λ X, F) ∈ (Π X Y).
Proof.
  intros. apply SepI.
  - apply PowerAx. unfold Sub. unfoldq.
    intros p H0. apply Λ_contain_pair in H0.
    destruct H0 as [x [H1 [y [H2 H3]]]].
    subst. apply CProdI. apply H1.
    eapply UnionI; [|apply H2].
    eapply FUnionI. apply H1. apply H. apply H1.
  - introq. rewrite β_reduction; auto.
Qed.

(* 函数类型的成员都是良定义的函数 *)
Theorem Π_only_Λ : ∀ X Y, ∀x ∈ X, ∀f ∈ Π X Y, f[x] ∈ Y x.
Proof.
  unfoldq. intros X Y x Hx f Hf. apply SepE2 in Hf.
  apply Hf. apply Hx.
Qed.

Corollary Π_non_dependent : ∀ X Y, ∀x ∈ X, ∀f ∈ (X ⟶ Y), f[x] ∈ Y.
Proof. intros. exact (Π_only_Λ X (λ _, Y)). Qed.

Example arrow_correct : ∀ A B f a, f ∈ (A ⟶ B) → a ∈ A → f[a] ∈ B.
Proof. intros. exact (Π_only_Λ A (λ _, B) a H0 f H). Qed.

(* 集合2在函数类型建构下封闭 *)
Theorem Π_close_2 : ∀ X Y, (∀ x ∈ X, Y x ∈ 2) → Π X Y ∈ 2.
Proof.
  introq. apply funion_2 in H.
  apply in_2_impl_union_0 in H.
  unfold Π. remember (λ f, ∀x ∈ X, f [x] ∈ Y x) as P.
  rewrite H. rewrite cprod_x_0.
  rewrite power_0_1. rewrite <- power_1_2.
  apply sep_power.
Qed.

Lemma Λ_sub : ∀ X f1 f2, (∀ y ∈ X, f1 y = f2 y) → (Λ X, f1) ⊆ (Λ X, f2).
Proof.
  unfold Lambda, Sub. introq.
  apply FUnionE in H0. destruct H0 as [y [H1 H2]].
  eapply FUnionI. apply H1. apply H in H1.
  rewrite H1 in H2. apply H2.
Qed.

(* Λ算符的外延性 *)
Lemma Λ_ext : ∀ X f1 f2, (∀ y ∈ X, f1 y = f2 y) → (Λ X, f1) = (Λ X, f2).
Proof.
  introq. apply sub_asym.
  - apply Λ_sub. unfoldq. apply H.
  - apply Λ_sub. introq. apply H in H0. auto.
Qed.

Lemma Λ_β : ∀ X F, (Λ X, F) = Λ X, (λ x, (Λ X, F)[x]).
Proof. intros. apply Λ_ext. introq. rewrite β_reduction; auto. Qed.

Lemma Π_sub : ∀ X Y1 Y2, (∀x ∈ X, Y1 x = Y2 x) → Π X Y1 ⊆ Π X Y2.
Proof.
  unfold Sub. introq. 
  apply SepE in H0. destruct H0 as [H1 H2].
  apply PowerAx in H1. apply SepI.
  - apply PowerAx. unfold Sub in *.
    introq. apply H1 in H0.
    apply CProd_correct in H0.
    destruct H0 as [a [H3 [b [H4 H5]]]].
    subst x0. apply CProdI. apply H3.
    apply UnionAx in H4. destruct H4 as [c [H4 H5]].
    apply FUnionE in H4. destruct H4 as [d [H6 H7]].
    apply UnionAx. unfoldq. exists c. split; [|apply H5].
    eapply FUnionI. apply H6.
    apply H in H6. rewrite H6 in H7. apply H7.
  - introq. apply H2 in H0 as H3. apply H in H0.
    rewrite H0 in H3. apply H3.
Qed.

(* Π算符的外延性 *)
Lemma Π_ext : ∀ X Y1 Y2, (∀x ∈ X, Y1 x = Y2 x) → Π X Y1 = Π X Y2.
Proof.
  introq. apply sub_asym.
  - apply Π_sub. unfoldq. apply H.
  - apply Π_sub. introq. apply H in H0. auto.
Qed.

Lemma f_sub : ∀ X F f g, f ∈ Π X F → (∀x ∈ X, f[x] ⊆ g[x]) → f ⊆ g.
Proof.
  unfold Sub. unfoldq. intros X F f g Hf Hsub p Hp.
  apply SepE in Hf. destruct Hf as [Hf _].
  apply PowerAx in Hf. unfold Sub in Hf.
  apply Hf in Hp as Hp'. clear Hf.
  apply CProd_correct in Hp'. destruct Hp' as [x [H1 [y [_ H2]]]].
  subst. apply ap_contain_pair in Hp. apply (Hsub x H1) in Hp.
  apply ap_contain_pair in Hp. apply Hp.
Qed.

(* 函数的外延性 *)
Theorem f_ext : ∀ X F f g, f ∈ Π X F → g ∈ Π X F →
  (∀x ∈ X, f[x] = g[x]) → f = g.
Proof.
  introq. apply sub_asym.
  - eapply f_sub. apply H. unfold Sub. introq.
    apply H1 in H2. rewrite H2 in H3. apply H3. 
  - eapply f_sub. apply H0. unfold Sub. introq.
    apply H1 in H2. rewrite H2. apply H3. 
Qed.

Lemma f_η : ∀ A B f, f ∈ Π A B → f = Λ A, (λ x, f[x]).
Proof.
  intros. eapply f_ext.
  - apply H.
  - apply Λ_in_Π. introq.
    apply (Π_only_Λ A B x H0) in H. apply H.
  - introq. rewrite β_reduction; auto.
Qed.

(** 有限序数 **)

(* 序数0 *)
Definition ordO : set := Empty.

(* 后继序数 *)
Definition ordS : set → set := λ N, N ∪ ⎨N⎬.

(* 有限序数集 *)
Definition FinOrd := {N ∊ 𝒰(∅) | λ N, ∃ n, iter n ordS ordO = N}.

(* 后继运算在宇宙中封闭 *)
Lemma GUordS : ∀ N, ∀X ∈ 𝒰(N), ordS X ∈ 𝒰(N).
Proof.
  introq. apply GUBUnion. apply H. 
  apply GUSing. apply H.
Qed.

(* 序数0属于有限序数集 *)
Lemma ordO_T : ordO ∈ FinOrd.
Proof.
  unfold FinOrd. apply SepI. apply GUIn.
  exists 0. simpl. reflexivity.
Qed.

(* 后继序数属于有限序数集 *)
Lemma ordS_T : ∀N ∈ FinOrd, ordS N ∈ FinOrd.
Proof.
  introq. apply SepE in H. destruct H as [H1 [n H2]].
  apply SepI. apply GUordS. apply H1.
  exists (S n). simpl. rewrite H2. reflexivity.
Qed.

(* 有限序数集属于𝒰(∅)宇宙 *)
Lemma FinOrd_T : FinOrd ∈ 𝒰(𝒰(∅)).
Proof. apply GUSep. apply GUIn. Qed.

(* 后继运算迭代有限次得到的序数属于有限序数集 *)
Lemma iter_ord_T : ∀ n, iter n ordS ordO ∈ FinOrd.
Proof.
  induction n.
  - simpl. apply ordO_T.
  - simpl. apply ordS_T. apply IHn.
Qed.

(* 后继序数非空 *)
Lemma ordS_i : ∀ N, ⦿ (ordS N).
Proof. intros. exists N. apply BUnionI2. apply SingI. Qed.

Corollary ordS_neq_ordO : ∀ N, ordS N ≠ ordO.
Proof.
  introq. intros H. pose proof (ordS_i N).
  destruct H0 as [x H0]. rewrite H in H0. exfalso0.
Qed.

(* 后继运算是单射 *)
Lemma ordS_inj : ∀ N M, ordS N = ordS M → N = M.
Proof.
  intros.
  assert (N ∈ ordS N) by apply BUnionI2, SingI.
  rewrite H in H0. apply BUnionE in H0.
  assert (M ∈ ordS M) by apply BUnionI2, SingI.
  rewrite <- H in H1. apply BUnionE in H1.
  destruct H0, H1.
  - exfalso. eapply well_founded_2. apply H0. apply H1.
  - apply SingE in H1. auto.
  - apply SingE in H0. auto.
  - apply SingE in H0. auto.
Qed.

(* 元语言自然数嵌入到集合论序数 *)
Definition embed (n : nat) : set := iter n ordS ordO.

(* 集合论序数投射出元语言自然数 *)
Definition proj (N : set) : nat :=
  match dit (sig (λ n, iter n ordS ordO = N)) with
    | inl (exist _ n _) => n
    | inr _ => 0
  end.

(* 嵌入操作是单射 *)
Lemma embed_inj : ∀ n m : nat,
  embed n = embed m → n = m.
Proof.
  induction n; destruct m; unfold embed; simpl; intros.
  - reflexivity.
  - exfalso. eapply ordS_neq_ordO. symmetry. apply H.
  - exfalso. eapply ordS_neq_ordO. apply H.
  - apply ordS_inj in H. apply IHn in H. auto.
Qed.

(* 集合论序数与元语言自然数同构 *)
Lemma embed_proj_id : ∀ n: nat, proj (embed n) = n. 
Proof.
  intros. unfold proj.
  destruct (dit (sig (λ k, iter k ordS ordO = embed n))).
  - destruct s as [k H]. apply embed_inj in H. apply H.
  - exfalso. apply f. exists n. reflexivity.
Qed.

Lemma iter_eq_embed : ∀ n : nat, iter n ordS ordO = embed n.
Proof. intros. unfold embed. reflexivity. Qed.

Lemma proj_embed_id : ∀N ∈ FinOrd, embed (proj N) = N.
Proof.
  introq. apply SepE in H. destruct H as [_ [k Heq]].
  subst. rewrite iter_eq_embed.
  rewrite embed_proj_id. reflexivity.
Qed.

(* 关于投射的一些引理 *)
Lemma proj_O : proj ordO = 0.
Proof.
  assert (ordO = embed 0) by reflexivity.
  rewrite H. rewrite embed_proj_id. reflexivity.
Qed.

Lemma embed_iff : ∀ n N,
  iter n ordS ordO = N ↔ N = embed n.
Proof. unfold embed. split; intros; auto. Qed.

Lemma embed_S : ∀ n N,
  N = embed n → ordS N = embed (S n).
Proof.
  intros. apply embed_iff. simpl.
  rewrite iter_eq_embed. rewrite <- H. reflexivity.
Qed.

Lemma proj_S : ∀N ∈ FinOrd,
  proj (ordS N) = S (proj N).
Proof.
  introq. apply SepE in H. destruct H as [_ [k Heq]].
  rewrite iter_eq_embed in Heq. subst x.
  rewrite embed_proj_id.
  rewrite (embed_S k (embed k)).
  apply embed_proj_id. reflexivity.
Qed.

(* 有限序数构建的正确性 *)
Theorem FinOrdE : ∀N ∈ FinOrd, N = ordO ∨ ∃M ∈ FinOrd, N = ordS M.
Proof.
  unfoldq. intros N H.
  apply SepE in H. destruct H as [_ [n Heq]].
  destruct n.
  - simpl in Heq. auto.
  - right. exists (embed n). split.
    + apply iter_ord_T.
    + subst. simpl. reflexivity.
Qed.

Lemma ordO_0_id : ∀N ∈ FinOrd, 0 = proj N → N = ordO.
Proof.
  intros N HN Hp.
  apply FinOrdE in HN. destruct HN as [H|[M [HM H]]].
  - apply H.
  - subst. rewrite (proj_S M HM) in Hp. discriminate.
Qed.

Lemma proj_S_ordS : ∀ m, ∀N ∈ FinOrd,
  proj N = S m → ∃M ∈ FinOrd, N = ordS M.
Proof.
  unfoldq. intros m N HN Hp.
  apply FinOrdE in HN. destruct HN as [H|[M [HM H]]].
  - subst. rewrite proj_O in Hp. discriminate.
  - exists M. auto.
Qed.

(** 递归原理 **)

(* 元语言自然数的关于类型的递归原理 *)
Check nat_rect.
(* nat_rect :
    ∀ P : nat → Type,
    P 0 →
    (∀ n : nat, P n → P (S n)) →
    ∀ n : nat, P n
*)

(* 有限序数上的递归原理 *)
Definition FinOrd_rect : set → set → set → set := λ z f N,
  nat_rect
    (λ _, set)
    z
    (* f是一个二元函数：第一个参数是当前自然数，第二个参数是递归项 *)
    (λ n R, f[embed n][R])
    (proj N).

(* 递归零次等于初始值 *)
Lemma FinOrd_rect_O : ∀ z f, FinOrd_rect z f ordO = z.
Proof.
  intros. unfold FinOrd_rect. rewrite proj_O.
  simpl. reflexivity.
Qed.

(* 递归步进表达式 *)
Lemma FinOrd_rect_S : ∀ z f, ∀N ∈ FinOrd,
  FinOrd_rect z f (ordS N) = f[N][FinOrd_rect z f N].
Proof.
  introq. unfold FinOrd_rect at 1.
  rewrite (proj_S x H). simpl.
  rewrite (proj_embed_id x H). reflexivity.
Qed.

(* 递归构建的正确性 *)
Theorem FinOrd_rect_T : ∀ F : set → set, ∀ z f N : set,
  z ∈ F ordO →
  N ∈ FinOrd →
  f ∈ Π FinOrd (λ N, (F N) ⟶ (F (ordS N))) →
  FinOrd_rect z f N ∈ F N.
Proof.
  intros F z f N Hz HN Hf. unfold FinOrd_rect.
  rewrite <- (proj_embed_id N HN) at 2.
  generalize (proj N) as k. clear HN.
  induction k.
  - unfold embed. simpl. apply Hz.
  - simpl. eapply arrow_correct.
    + assert (Hk: embed k ∈ FinOrd) by apply iter_ord_T.
      apply (Π_only_Λ _ _ (embed k) Hk) in Hf. apply Hf.
    + apply IHk.
Qed.

Close Scope TG1_scope.
