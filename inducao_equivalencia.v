(** * Equivalência entre o Princípio da Indução Matemática e o Princípio da Indução Forte *)

Require Import Arith.

(** Seja [P] uma propriedade sobre os números naturais. O Princípio da *)
(** Indução Matemática (PIM) pode ser enunciado da seguinte forma:  *)

Definition PIM :=
  forall P: nat -> Prop,
    (P 0) ->
    (forall n, P n -> P (S n)) ->
    forall n, P n.

(** Seja [Q] uma propriedade sobre os números naturais. O Princípio da *)
(** Indução Forte (PIF) pode ser enunciado da seguinte forma:  *)


Definition PIF :=
  forall Q: nat -> Prop,
    (forall n, (forall m, m<n -> Q m) -> Q n) ->
    forall n, Q n.

(** Prove que estes princípios são equivalentes: *)

Lemma PIF_to_PIM: PIF -> PIM.
Proof.
  intros.
  unfold PIF in H.
  unfold PIM.
  induction n.
  - apply H0.
  - auto.
Qed.

Lemma PIM_to_PIF: PIM -> PIF.
Proof.
  intros.
  unfold PIM in H.
  unfold PIF.
  induction n.
  - apply H0.
    intros.
    inversion H1.
  - pose proof lt_wf_ind.
    apply H1. apply H0.
Qed.

Theorem PIM_equiv_PIF: PIM <-> PIF.
Proof.
  split.
  apply PIM_to_PIF.
  apply PIF_to_PIM.
Qed.
