Require Export Utf8_core.
Require Export Classical.

Fact all_iff_ex_1 : ∀ {A : Type} (P : A → Prop) (Q : Prop),
  (∀ x, (P x → Q)) ↔ ((∃ x, P x) → Q).
Proof.
  intros A P Q. split.
  - intros H [x Hpx]. apply (H x Hpx).
  - intros H x Hpx. apply H. exists x. apply Hpx.
Qed.

Fact all_iff_ex_2 : ∀ {A : Type} (P : A → Prop) (Q : Prop),
  (∃ x, P x → Q) ↔ (inhabited A ∧ ((∀ x, P x) → Q)).
Proof.
  intros A P Q. split.
  - intros [x H]. split.
    + exact (inhabits x).
    + intros Hpx. apply H. apply Hpx.
  - intros [[a] H].
    destruct (classic (∀ x, P x)) as [Hpx|Hnx].
    + exists a. intros Ha. apply H. apply Hpx.
    + apply not_all_ex_not in Hnx as [x Hnx].
      exists x. intros Hx. exfalso. apply Hnx. apply Hx.
Qed.

Axiom rule : ∀ {A : Type} (P : A → Prop) (Q : Prop),
  (Q ∨ ∃ y, P y) → ∃ x, Q ∨ P x.

Fact all_iff_ex_2' : ∀ {A : Type} (P : A → Prop) (Q : Prop),
  (∃ x, P x → Q) ↔ (((∀ x, P x) → Q)).
Proof.
  intros A P Q. split.
  - intros [x H] Hx. apply H. apply Hx.
  - intros H.
    destruct (classic (∀ x, P x)) as [Hpx|Hnx].
    + destruct (rule P Q) as [a [Hq|_]]. {
        left. apply H. apply Hpx.
      }
      * exists a. intros _. apply Hq.
      * exists a. intros _. apply H. apply Hpx.
    + apply not_all_ex_not in Hnx as [x Hnx].
      exists x. intros Hx. exfalso. apply Hnx. apply Hx.
Qed.

(* 命题“存在x:A满足P”定义为满足以下条件的类型ex A P :=
∀ x:A, (P x → ex A P)
这个定义的意思是说，对于任意一个x:A，如果它满足P，你就能得到ex A P
如果你真的有一个这样的x，那么你也就得到了ex A P，也就证明了语义上的
∃ x:A, P x.
实际上，在软件里，∃ x:A, P x 只是 ex A P 的另一种表示而已。
如果你并没有x:A满足P，空有∀ x:A, (P x → ex A P) 是永远无法得到ex A P的
但是你一旦真的有了，用∀ x:A, (P x → ex A P) 这个定义就能得到ex A P *)

Inductive ex (A : Type) (P : A → Prop) : Prop :=
  ex_intro : ∀ x, (P x → ex A P).

Axiom A : Type.
Axiom a : A.

Fact test : ∀ (P : A → Prop) (Q : Prop),
  P a → ex A P.
Proof.
  intros P Q Hpa.
  exact (ex_intro A P a Hpa).
Qed.
