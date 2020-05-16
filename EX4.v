(*** Formal Construction of a Set Theory in Coq ***)
(** based on the thesis by Jonas Kaiser, November 23, 2012 **)
(** Coq programming by choukh, April 2020 **)

Require Export ZFC.EX3.

(*** TG集合论扩展4：有限序数及其递归原理 ***)

(** 有限序数 **)

(* 对x迭代n次f：特别地，有 iter n S O = n *)
Fixpoint iter (n : nat) {X : Type} (f : X → X) (x : X) :=
  match n with
  | O => x
  | S n' => f (iter n' f x)
  end.

(* 序数0 *)
Definition ordO : set := Empty.

(* 后继序数 *)
Definition ordS : set → set := λ N, N ∪ ⎨N⎬.

(* 有限序数集 *)
Definition ω := {N ∊ 𝒰(∅) | λ N, ∃ n, iter n ordS ordO = N}.

(* 后继运算在宇宙中封闭 *)
Lemma GUordS : ∀ N, ∀X ∈ 𝒰(N), ordS X ∈ 𝒰(N).
Proof.
  introq. apply GUBUnion. apply H. 
  apply GUSing. apply H.
Qed.

(* 序数0属于有限序数集 *)
Lemma ordO_T : ordO ∈ ω.
Proof.
  unfold ω. apply SepI. apply GUIn.
  exists 0. simpl. reflexivity.
Qed.

(* 后继序数属于有限序数集 *)
Lemma ordS_T : ∀N ∈ ω, ordS N ∈ ω.
Proof.
  introq. apply SepE in H. destruct H as [H1 [n H2]].
  apply SepI. apply GUordS. apply H1.
  exists (S n). simpl. rewrite H2. reflexivity.
Qed.

(* 有限序数集属于𝒰(∅)宇宙 *)
Lemma ω_T : ω ∈ 𝒰(𝒰(∅)).
Proof. apply GUSep. apply GUIn. Qed.

(* 后继运算迭代有限次得到的序数属于有限序数集 *)
Lemma iter_ord_T : ∀ n, iter n ordS ordO ∈ ω.
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

(* 没有循环单链 *)
Lemma well_founded_1 : ∀ X, X ∉ X.
Proof.
  intros X. pose proof (ε_ind (λ X, X ∉ X)). simpl in H.
  apply H. introq. intros Ht. apply H0 in Ht as Hf. auto.
Qed.

(* 没有循环双链 *)
Lemma well_founded_2 : ∀ X Y, X ∈ Y → Y ∉ X.
Proof.
  intros X Y H. pose proof (ε_ind (λ X, ∀ Y, X ∈ Y → Y ∉ X)).
  apply H0; [|apply H]. clear X Y H H0. unfoldq.
  intros X H Y H1 H2.
  pose proof (H Y H2 X H2). auto.
Qed.

(* 后继运算是单射的 *)
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

(* 嵌入操作是单射的 *)
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

Lemma proj_embed_id : ∀N ∈ ω, embed (proj N) = N.
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

Lemma proj_S : ∀N ∈ ω,
  proj (ordS N) = S (proj N).
Proof.
  introq. apply SepE in H. destruct H as [_ [k Heq]].
  rewrite iter_eq_embed in Heq. subst x.
  rewrite embed_proj_id.
  rewrite (embed_S k (embed k)).
  apply embed_proj_id. reflexivity.
Qed.

(* 有限序数构建的正确性 *)
Theorem ωE : ∀N ∈ ω, N = ordO ∨ ∃M ∈ ω, N = ordS M.
Proof.
  unfoldq. intros N H.
  apply SepE in H. destruct H as [_ [n Heq]].
  destruct n.
  - simpl in Heq. auto.
  - right. exists (embed n). split.
    + apply iter_ord_T.
    + subst. simpl. reflexivity.
Qed.

Lemma ordO_0_id : ∀N ∈ ω, 0 = proj N → N = ordO.
Proof.
  intros N HN Hp.
  apply ωE in HN. destruct HN as [H|[M [HM H]]].
  - apply H.
  - subst. rewrite (proj_S M HM) in Hp. discriminate.
Qed.

Lemma proj_S_ordS : ∀ m, ∀N ∈ ω,
  proj N = S m → ∃M ∈ ω, N = ordS M.
Proof.
  unfoldq. intros m N HN Hp.
  apply ωE in HN. destruct HN as [H|[M [HM H]]].
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
Definition ω_rect : set → set → set → set := λ z f N,
  nat_rect
    (λ _, set)
    z
    (* f是一个二元函数：第一个参数是当前自然数，第二个参数是递归项 *)
    (λ n R, f[embed n]ₐ[R]ₐ)
    (proj N).

(* 递归零次等于初始值 *)
Lemma ω_rect_O : ∀ z f, ω_rect z f ordO = z.
Proof.
  intros. unfold ω_rect. rewrite proj_O.
  simpl. reflexivity.
Qed.

(* 递归步进表达式 *)
Lemma ω_rect_S : ∀ z f, ∀N ∈ ω,
  ω_rect z f (ordS N) = f[N]ₐ[ω_rect z f N]ₐ.
Proof.
  introq. unfold ω_rect at 1.
  rewrite (proj_S x H). simpl.
  rewrite (proj_embed_id x H). reflexivity.
Qed.

(* 递归构建的正确性 *)
Theorem ω_rect_T : ∀ F : set → set, ∀ z f N : set,
  z ∈ F ordO →
  N ∈ ω →
  f ∈ Πₐ ω (λ N, (F N) ⟶ₐ (F (ordS N))) →
  ω_rect z f N ∈ F N.
Proof.
  intros F z f N Hz HN Hf. unfold ω_rect.
  rewrite <- (proj_embed_id N HN) at 2.
  generalize (proj N) as k. clear HN.
  induction k.
  - unfold embed. simpl. apply Hz.
  - simpl. eapply arrowₐ_correct.
    + assert (Hk: embed k ∈ ω) by apply iter_ord_T.
      apply (Πₐ_only_Λₐ _ _ (embed k) Hk) in Hf. apply Hf.
    + apply IHk.
Qed.
