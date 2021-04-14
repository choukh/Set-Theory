(** Coq coding by choukh, Mar 2021 **)

Require Import ZFC.lib.Essential.

Declare Scope Topology_scope.
Delimit Scope Topology_scope with topo.
Open Scope Topology_scope.

(* 拓扑空间 *)
Record TopologicalSpace : Type := constr {
  (* 全集 *)
  X : set;
  (* 开集条件 *)
  is_open : set → Prop;
  (* 全集开 *)
  is_open_univ : is_open X;
  (* 空集开 *)
  is_open_empty : is_open ∅;
  (* 有限交开 *)
  is_open_inter : ∀ A B ∈ 𝒫 X, is_open A → is_open B → is_open (A ∩ B);
  (* 任意并开 *)
  is_open_union : ∀ 𝒜 ∈ 𝒫 𝒫 X, (∀A ∈ 𝒜, is_open A) → is_open (⋃ 𝒜)
}.

Module Type AbstractTopology.
Parameter Space : TopologicalSpace.
End AbstractTopology.

Module Topology (Abstract : AbstractTopology).
Definition S := Abstract.Space.

(* 开集族 *)
Definition Opens := {A ∊ 𝒫 S.(X) | S.(is_open) }.
Notation τ := Opens.

(* 邻域系 *)
Definition Neighbours := λ x, {A ∊ τ | λ A, x ∈ A}.
Notation U := Neighbours.

(* 闭包 *)
Definition Closure := λ A, {x ∊ S.(X) | λ x, ∀B ∈ U x, A ∩ B ≠ ∅ }.
Notation "A ⁻" := (Closure A) (at level 60).

(* 空集的闭包是空集 *)
Theorem closure_of_empty : ∅⁻ = ∅.
Proof.
  apply ExtAx. split; intros Hx; [exfalso|exfalso0].
  apply SepE in Hx as [H1 H2].
  assert (S.(X) ∈ U x). {
    apply SepI. apply SepI. apply all_in_its_power.
    apply is_open_univ. apply H1.
  }
  apply (H2 _ H).
  apply ExtAx. intros y. split; intros Hy.
  apply BInterE in Hy as []. exfalso0. exfalso0.
Qed.

(* 闭包运算保持子集关系 *)
Theorem closure_preserve_sub : ∀ A B, A ⊆ B → A⁻ ⊆ B⁻.
Proof with eauto.
  intros A B Hsub x Hx.
  apply SepE in Hx as [Hx H].
  apply SepI... intros C HC. apply H in HC.
  apply EmptyNE in HC as [a Ha]. apply BInterE in Ha as [H1 H2].
  apply EmptyNI. exists a. apply BInterI... apply Hsub...
Qed.

End Topology.

Module Test.
Definition TrivialSpace :=
  constr ∅ (λ _, True) I I (λ _ _ _ _ _ _, I) (λ _ _ _ , I).

Module Trivial <: AbstractTopology.
Definition Space := TrivialSpace.
End Trivial.

Include Topology Trivial.

Fact opens_eq : τ = ⎨∅⎬.
Proof with auto.
  apply ExtAx. split; intros Hx.
  - apply SepE1 in Hx. simpl in Hx.
    apply only_empty_in_power_empty in Hx. subst...
  - apply SingE in Hx. subst.
    apply SepI. simpl. apply all_in_its_power. apply I.
Qed.

End Test.
