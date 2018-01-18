Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Require Import Lists.List.
Import ListNotations.

Require ast.
Require stream.
Require encode.
Require decode.

Fact positive_size_lt0: forall (p: positive), Pos.size_nat p > 0.
Proof.
  induction p; simpl; omega.
Qed.

Definition bijection {A}
           (dec: stream.bit -> option (A * stream.bit))
           (enc: A -> stream.bit -> stream.bit)
           (a: A) :=
  forall (a: A)(s s': stream.bit),
    (dec s') = Some (a, s) <-> (enc a s) = s'.

Lemma number: forall (bits: nat) (n: N),
    (N.size_nat n) <= (S bits) ->
    bijection (decode.number (S bits)) (encode.number (S bits)) n.
Proof.
  unfold bijection, decode.number, decode.number_rec.
  induction bits; split; intros; destruct s; simpl.
  - destruct n; try destruct p; try trivial;
      try (contradict H; simpl; apply gt_not_le;
           specialize positive_size_lt0 with (p);
           omega).
    + case_eq (stream.take s'); intros; rewrite H1 in H0.
      * destruct p. simpl in H0. admit.
      * admit.
    + admit.
  - admit.
Admitted.

Lemma condition: forall (c: ast.condition),
    bijection decode.condition encode.condition c.
Proof.
Admitted.

Theorem instruction: forall (i: ast.instruction),
    bijection decode.instruction encode.instruction i.
Proof.
Admitted.

Lemma instructions: forall (ins: ast.instructions) (s: stream.bit),
    (decode.instructions s) = Some ins
    <-> (encode.instructions ins stream.empty) = s.
Proof.
Admitted.