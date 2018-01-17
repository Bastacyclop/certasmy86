Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Require Import Lists.List.
Import ListNotations.

Require ast.
Require encode.
Require decode.

Definition stream := list bool.

(* Degenerate case *)
Compute (encode.number 1 9).
Compute (decode.number 1 [true]).

Lemma number: forall (bits: nat) (n: N) (s s': stream),
    (N.size_nat n) <= (S bits) ->
    (decode.number (S bits) s) = Some (n, s')
    <-> (encode.number (S bits) n) = (firstn (S bits) s).
Proof.
  induction bits; split; intros.
  - destruct s.
    + discriminate.
    + destruct b; injection H0; intros; subst; trivial.
  - destruct s.
    + compute. discriminate.
    + simpl in H0. destruct b. compute.