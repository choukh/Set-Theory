(** Solutions to "Elements of Set Theory" Chapter 7 Part 1 **)
(** Coq coding by choukh, Nov 2020 **)

Require Export ZFC.EST7_2.

(* ex7_1
  (a) No (b) No
    let < be divisibility
    let A = {2, 3, 6}
    let B = {3, 3, 6}
*)
(* ex7_2 see EST7_1 Fact inv_partialOrder *)
(* ex7_3 Combination (n, 2) = n! / 2!(n - 2)! = (1/2)n(n-1) *)
(* ex7_4 skip *)

Example ex7_5 : ∀ A R f, wellOrder R A → f: A ⇒ A →
  (∀ x y ∈ A, <x, y> ∈ R → <f[x], f[y]> ∈ R) →
  ∀x ∈ A, <x, f[x]> ∈ R ∨ x = f[x].
Proof with auto.
  intros * Hwo Hf Hord x Hx.
Admitted.
