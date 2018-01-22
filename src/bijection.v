Require Import util.
Require ast.
Require stream.
Require encode.
Require decode.

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

Ltac number_encdec := rewrite number_encdec; try (simpl; omega).

Fact condition_encdec: forall (c: ast.condition) (s: stream.bit),
    decode.condition (encode.condition c s) = Some (c, s).
Proof.
  unfold decode.condition, encode.condition, encode.condition_num.
  intros.
  destruct c; number_encdec; reflexivity.
Qed.

Fact operator_encdec: forall (op: ast.operator) (s: stream.bit),
    decode.operator (encode.operator op s) = Some (op, s).
Proof.
  unfold decode.operator, encode.operator, encode.operator_num.
  intros.
  destruct op; number_encdec; reflexivity.
Qed.

Ltac expect_encdec :=
  unfold decode.expect; number_encdec; rewrite N.eqb_refl.

Ltac register_encdec r := destruct r; rewrite register_encdec.
Ltac immediate_encdec i := destruct i; rewrite immediate_encdec.
Ltac displacement_encdec i := destruct i; rewrite displacement_encdec.
Ltac destination_encdec i := destruct i; rewrite destination_encdec.

Lemma reg_is_4bits: forall (n: nat), n <= ast.nb_registers -> N.size_nat (N.of_nat n) <= ast.register_bits.
Proof.
  intros.
  destruct n.
    - simpl. omega.
    - simpl. admit. 
Admitted.

Lemma imm_is_32bits: forall (n: N), N.le n  4294967295%N -> N.size_nat n <= ast.constant_bits.
Proof.
  admit.
Admitted.

Lemma instruction_encdec:
  forall (i: ast.instruction) (s: stream.bit),
    ast.valid_instruction i ->
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
    + reflexivity. (* inversion, apply *)
    + inversion H; try discriminate.
      injection H2. intros.
      rewrite H3. apply reg_is_4bits. assumption.
    + inversion H; try discriminate.
      injection H2. intros.
      rewrite H4. apply reg_is_4bits. assumption.
  - unfold decode.irmovl.
    expect_encdec.
    expect_encdec.
    register_encdec r.
    immediate_encdec i.
    reflexivity.
    + inversion H; try discriminate.
      injection H1. intros. 
      apply imm_is_32bits.
      simpl.
      admit.
    + admit.
      
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

Ltac injected H :=
  injection H; intros; subst; reflexivity.

Fact register_decenc:
  forall (r: ast.register) (s s': stream.bit),
    decode.register s = Some (r, s') ->
    encode.register r s' = s.
Proof.
  unfold encode.register, decode.register.
  intros. destruct r. apply number_decenc.
  mcase (decode.number ast.register_bits s) H p H0.
  injected H.
Qed.

Fact immediate_decenc:
  forall (i: ast.immediate) (s s': stream.bit),
    decode.immediate s = Some (i, s') ->
    encode.immediate i s' = s.
Proof.
  unfold encode.immediate, decode.immediate.
  intros. destruct i. apply number_decenc.
  mcase (decode.number ast.constant_bits s) H p H0.
  injected H.
Qed.

Fact displacement_decenc:
  forall (d: ast.displacement) (s s': stream.bit),
    decode.displacement s = Some (d, s') ->
    encode.displacement d s' = s.
Proof.
  unfold encode.displacement, decode.displacement.
  intros. destruct d. apply number_decenc.
  mcase (decode.number ast.constant_bits s) H p H0.
  injected H.
Qed.

Fact destination_decenc:
  forall (d: ast.destination) (s s': stream.bit),
    decode.destination s = Some (d, s') ->
    encode.destination d s' = s.
Proof.
  unfold encode.destination, decode.destination.
  intros. destruct d. apply number_decenc.
  mcase (decode.number ast.constant_bits s) H p H0.
  injected H.
Qed.

Fact condition_decenc:
  forall (c: ast.condition) (s s': stream.bit),
    decode.condition s = Some (c, s') ->
    encode.condition c s' = s.
Proof.
  unfold decode.condition, encode.condition, encode.condition_num.
  intros.
  mcase (decode.number 4 s) H p C0.
  destruct n; do 3 try destruct p; try discriminate;
    try (injection H; intros; subst; apply number_decenc; assumption).
Qed.

Fact operator_decenc:
  forall (c: ast.operator) (s s': stream.bit),
    decode.operator s = Some (c, s') ->
    encode.operator c s' = s.
Proof.
  unfold decode.operator, encode.operator, encode.operator_num.
  intros.
  mcase (decode.number 4 s) H p C0.
  destruct n; do 2 try destruct p; try discriminate;
    try (injection H; intros; subst; apply number_decenc; assumption).
Qed.

Fact decode_expect:
  forall (bits: nat) (e: N) (u: unit) (s s': stream.bit),
    decode.expect bits e s = Some (u, s') ->
    decode.number bits s = Some (e, s').
Proof.
  unfold decode.expect.
  intros.
  mcase (decode.number bits s) H p H0.
  mcase (n =? e)%N H p H1.
  injection H. intros. subst.
  apply Neqb_ok in H1. rewrite H1.
  reflexivity.
Qed.

Ltac decenc e H p HR :=
  mcase e H p HR;
  try apply decode_expect in HR;
  try apply register_decenc in HR;
  try apply immediate_decenc in HR;
  try apply destination_decenc in HR;
  try apply displacement_decenc in HR;
  try apply condition_decenc in HR;
  try apply operator_decenc in HR;
  try apply number_decenc in HR.

Lemma instruction_decenc:
  forall (i: ast.instruction) (s s': stream.bit),
    decode.instruction s = Some (i, s') ->
    encode.instruction i s' = s.
Proof.
  unfold decode.instruction.
  intros.
  decenc (decode.number 4 s) H p C0.
  destruct n; do 4 try destruct p; try discriminate.
  - decenc (decode.expect 4 0 s0) H p C1.
    injection H. intros. subst. reflexivity.
  - unfold decode.popl in H.
    decenc (decode.expect 4 0 s0) H p C1.
    decenc (decode.register s1) H p C2.
    decenc (decode.expect 4 15 s2) H p C3.
    injection H. intros. subst. reflexivity.
  - unfold decode.jump in H.
    decenc (decode.condition s0) H p C1.
    decenc (decode.destination s1) H p C2.
    injection H. intros. subst. reflexivity.
  - unfold decode.ret in H.
    decenc (decode.expect 4 0 s0) H p C1.
    injection H. intros. subst. reflexivity.
  - unfold decode.mrmovl in H.
    decenc (decode.expect 4 0 s0) H p C1.
    decenc (decode.register s1) H p C2.
    decenc (decode.register s2) H p C3.
    decenc (decode.displacement s3) H p C4.
    injection H. intros. subst. reflexivity.
  - unfold decode.irmovl in H.
    decenc (decode.expect 4 0 s0) H p C1.
    decenc (decode.expect 4 15 s1) H p C2.
    decenc (decode.register s2) H p C3.
    decenc (decode.immediate s3) H p C4.
    injection H. intros. subst. reflexivity.
  - unfold decode.pushl in H.
    decenc (decode.expect 4 0 s0) H p C1.
    decenc (decode.register s1) H p C2.
    decenc (decode.expect 4 15 s2) H p C3.
    injection H. intros. subst. reflexivity.
  - unfold decode.OPl in H.
    decenc (decode.operator s0) H p C1.
    decenc (decode.register s1) H p C2.
    decenc (decode.register s2) H p C3.
    injection H. intros. subst. reflexivity.
  - unfold decode.call in H.
    decenc (decode.expect 4 0 s0) H p C1.
    decenc (decode.destination s1) H p C2.
    injection H. intros. subst. reflexivity.
  - unfold decode.rmmovl in H.
    decenc (decode.expect 4 0 s0) H p C1.
    decenc (decode.register s1) H p C2.
    decenc (decode.register s2) H p C3.
    decenc (decode.displacement s3) H p C4.
    injection H. intros. subst. reflexivity.
  - unfold decode.rrmovl in H.
    decenc (decode.condition s0) H p C1.
    decenc (decode.register s1) H p C2.
    decenc (decode.register s2) H p C3.
    injection H. intros. subst. reflexivity.
  - decenc (decode.expect 4 0 s0) H p C1.
    injection H. intros. subst. reflexivity.
Qed.