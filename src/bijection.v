Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Require Import Lists.List.
Import ListNotations.

Require ast.
Require stream.
Require encode.
Require decode.

Ltac mcase e H p HR :=
  case_eq e; try intros p HR; try intros HR; rewrite HR in H;
  try destruct p; try discriminate.

Fact positive_size_lt0: forall (p: positive), Pos.size_nat p > 0.
Proof.
  induction p; simpl; omega.
Qed.

Lemma number_encdec:
  forall (bits: nat) (n: N) (s: stream.bit),
    (N.size_nat n) <= bits ->
    decode.number bits (encode.number bits n s) = Some (n, s).
Proof.
  induction bits; intros; simpl.
  - destruct n.
    + reflexivity.
    + contradict H. simpl.
      apply gt_not_le. apply positive_size_lt0.
  - admit.
Admitted.

Lemma number_decenc:
  forall (bits: nat) (n: N) (s s': stream.bit),
    decode.number bits s = Some (n, s') ->
    encode.number bits n s' = s.
Proof.
  induction bits; intros; simpl; simpl in H.
  - injection H. intros. symmetry. assumption.
  - mcase (stream.take s) H p H0.
    mcase (decode.number bits t) H p H1.
    admit.
Admitted.

Ltac number_encdec := rewrite number_encdec; try (simpl; omega).

Fact decode_expect:
  forall (bits: nat) (e: N) (s s': stream.bit),
    decode.expect bits e s = Some (tt, s') <->
    decode.number bits s = Some (e, s').
Proof.
  unfold decode.expect.
  split; intros.
  - mcase (decode.number bits s) H p H0.
    mcase (n =? e)%N H p H1.
    injection H. intros. subst.
    apply Neqb_ok in H1. rewrite H1.
    reflexivity.
  - rewrite H. rewrite N.eqb_refl.
    reflexivity.
Qed.

Ltac expect_encdec :=
  unfold decode.expect; number_encdec; rewrite N.eqb_refl.

Ltac plain_number_encdec :=
  intros;
  rewrite number_encdec;
  try reflexivity;
  try assumption.

Fact register_encdec: forall (n: N) (s: stream.bit),
    (N.size_nat n) <= ast.register_bits ->
    decode.register (encode.register (ast.reg n) s)
    = Some (ast.reg n, s).
Proof.
  unfold encode.register, decode.register.
  plain_number_encdec.
Qed.

Fact immediate_encdec: forall (n: N) (s: stream.bit),
    (N.size_nat n) <= ast.constant_bits ->
    decode.immediate (encode.immediate (ast.imm n) s)
    = Some (ast.imm n, s).
Proof.
  unfold encode.immediate, decode.immediate.
  plain_number_encdec.
Qed.

Fact displacement_encdec: forall (n: N) (s: stream.bit),
    (N.size_nat n) <= ast.constant_bits ->
    decode.displacement (encode.displacement (ast.dsp n) s)
    = Some (ast.dsp n, s).
Proof.
  unfold encode.displacement, decode.displacement.
  plain_number_encdec.
Qed.

Fact destination_encdec: forall (n: N) (s: stream.bit),
    (N.size_nat n) <= ast.constant_bits ->
    decode.destination (encode.destination (ast.dst n) s)
    = Some (ast.dst n, s).
Proof.
  unfold encode.destination, decode.destination.
  plain_number_encdec.
Qed.

Fact condition_encdec: forall (c: ast.condition) (s: stream.bit),
    decode.condition (encode.condition c s) = Some (c, s).
Proof.
Admitted.

Fact operator_encdec: forall (op: ast.operator) (s: stream.bit),
    decode.operator (encode.operator op s) = Some (op, s).
Proof.
Admitted.

Fact register_decenc: forall (n: N) (s s': stream.bit),
    decode.register s = Some (ast.reg n, s') ->
    encode.register (ast.reg n) s' = s.
Proof.
  unfold encode.register, decode.register.
  intros.
  apply number_decenc.
  mcase (decode.number ast.register_bits s) H p H0.
  injection H. intros. subst. reflexivity.
Qed.

Ltac register_encdec r := destruct r; rewrite register_encdec.
Ltac immediate_encdec i := destruct i; rewrite immediate_encdec.
Ltac displacement_encdec i := destruct i; rewrite displacement_encdec.
Ltac destination_encdec i := destruct i; rewrite destination_encdec.

Lemma instruction_encdec:
  forall (i: ast.instruction) (s: stream.bit),
    decode.instruction (encode.instruction i s) = Some (i, s).
Proof.
  unfold decode.instruction, encode.instruction.
  intros.
  destruct i; rewrite number_encdec; try (simpl; omega).
  - expect_encdec. reflexivity.
  - expect_encdec. reflexivity.
  - unfold decode.rrmovl.
    rewrite condition_encdec.
    register_encdec r.
    register_encdec r0.
    reflexivity.
    admit. admit. (* TODO: limit values *)
  - unfold decode.irmovl.
    expect_encdec.
    expect_encdec.
    register_encdec r.
    immediate_encdec i.
    reflexivity.
    admit. admit. (* TODO: limit values *)
  - unfold decode.rmmovl.
    expect_encdec.
    register_encdec r.
    register_encdec r0.
    displacement_encdec d.
    reflexivity.
    admit. admit. admit. (* TODO: limit values *)
  - unfold decode.mrmovl.
    expect_encdec.
    register_encdec r.
    register_encdec r0.
    displacement_encdec d.
    reflexivity.
    admit. admit. admit. (* TODO: limit values *)
  - unfold decode.OPl.
    rewrite operator_encdec.
    register_encdec r.
    register_encdec r0.
    reflexivity.
    admit. admit. (* TODO: limit values *)
  - unfold decode.jump.
    rewrite condition_encdec.
    destination_encdec d.
    reflexivity.
    admit. (* TODO: limit values *)
  - unfold decode.call.
    expect_encdec.
    destination_encdec d.
    reflexivity.
    admit. (* TODO: limit values *)
  - unfold decode.ret.
    expect_encdec.
    reflexivity.
  - unfold decode.pushl.
    expect_encdec.
    register_encdec r.
    expect_encdec.
    reflexivity.
    admit. (* TODO: limit values *)
  - unfold decode.popl.
    expect_encdec.
    register_encdec r.
    expect_encdec.
    reflexivity.
    admit. (* TODO: limit values *)
Admitted.