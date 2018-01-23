Require Export Coq.Arith.Arith.
Require Export Coq.omega.Omega.
Require Export Lists.List.

Ltac mcase e H p HR :=
  case_eq e; try intros p HR; try intros HR; rewrite HR in H;
  try destruct p; try discriminate.

Fact positive_size_lt0: forall (p: positive), Pos.size_nat p > 0.
Proof.
  induction p; simpl; omega.
Qed.

Fact setbit_bits: forall (n: N)(b: nat),
    b >= N.size_nat n ->
    N.size_nat (N.setbit n (N.of_nat b)) = S b.
Proof.
  intros.
  induction b.
  - destruct n.
    + reflexivity.
    + contradict H. apply gt_not_le. apply positive_size_lt0.
  - admit.
Admitted.

Lemma size_nat: forall (n: N)(s: nat),
  (n <= N.of_nat (Nat.pow s 2))%N -> (N.size_nat n) <= s.
Proof.
Admitted.