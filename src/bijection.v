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

Lemma size_nat: forall (n: N)(s: nat),
  (n <= N.of_nat (Nat.pow s 2))%N -> (N.size_nat n) <= s.
Proof.
Admitted.

Lemma reg_is_4bits: forall (n: N), (n <= ast.reg_max)%N -> N.size_nat n <= ast.register_bits.
Proof.
  intros.
  apply size_nat.
  apply N.le_trans with (m:=ast.reg_max).
  assumption.
  unfold ast.reg_max.
  simpl. 
  admit.
Admitted.

Lemma cst_is_32bits: forall (n: N), (n <= ast.cst_max)%N -> N.size_nat n <= ast.constant_bits.
Proof.
  admit.
Admitted.

Ltac ins_arg_validity h := inversion h; try discriminate; try apply reg_is_4bits; try apply cst_is_32bits; try assumption. 

(*
Fact le_on_nat_eq_N: forall (a b: nat),
  (a <= b) -> (N.of_nat a <= N.of_nat b)%N.
Proof.
 intros.
 compute.
 
Admitted.

Fact le_on_N_eq_nat: forall (a b: N),
(a <= b)%N -> (N.to_nat a <= N.to_nat b) .
Proof.
  intros.
Admitted.
*)


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
    + reflexivity.
    + ins_arg_validity H.
    + ins_arg_validity H.
  - unfold decode.irmovl.
    expect_encdec.
    expect_encdec.
    register_encdec r.
    immediate_encdec i.
    reflexivity.
    ins_arg_validity H.
    ins_arg_validity H.
  - unfold decode.rmmovl.
    expect_encdec.
    register_encdec r.
    register_encdec r0.
    displacement_encdec d.
    reflexivity.
    inversion H; try discriminate.
    ins_arg_validity H.
    ins_arg_validity H.
    ins_arg_validity H.
  - unfold decode.mrmovl.
    expect_encdec.
    register_encdec r.
    register_encdec r0.
    displacement_encdec d.
    reflexivity.
    ins_arg_validity H.
    ins_arg_validity H.
    ins_arg_validity H.
  - unfold decode.OPl.
    rewrite operator_encdec.
    register_encdec r.
    register_encdec r0.
    reflexivity.
    ins_arg_validity H.
    ins_arg_validity H.
  - unfold decode.jump.
    rewrite condition_encdec.
    destination_encdec d.
    reflexivity.
    ins_arg_validity H.
  - unfold decode.call.
    expect_encdec.
    destination_encdec d.
    reflexivity.
    ins_arg_validity H.
  - unfold decode.ret.
    expect_encdec.
    reflexivity.
  - unfold decode.pushl.
    expect_encdec.
    register_encdec r.
    expect_encdec.
    reflexivity.
    ins_arg_validity H.
  - unfold decode.popl.
    expect_encdec.
    register_encdec r.
    expect_encdec.
    reflexivity.
    ins_arg_validity H.
Qed.

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