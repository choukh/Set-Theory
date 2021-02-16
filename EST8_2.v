(** Based on "Elements of Set Theory" Chapter 8 Part 2 **)
(** Coq coding by choukh, Feb 2021 **)

Require Export ZFC.EST8_1.
Import 𝐎𝐍Operation.

(*** EST第八章2：序数操作的性质，Veblen不动点定理 ***)

Example ord_suc_monotone : monotone Suc.
Proof with eauto.
  intros α Hoα β Hβ.
  rewrite <- ord_suc_preserve_lt...
  eapply ord_is_ords...
Qed.


