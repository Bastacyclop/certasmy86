Require Import util.
Import ListNotations.
Require ast.
Require stream.

Definition stream := stream.bit.

(* Helpers *)

Notation "'do' '(' a ',' b ')' '<-' e ';' c" :=
  (match e with | None => None | Some (a, b) => c end)
    (at level 70, right associativity).

Fixpoint number (bits: nat) (s: stream): option (N * stream) :=
  match bits with
  | 0 => Some (0%N, s)
  | S b =>
    do (bit, s) <- stream.take s;
    do (n, s) <- number b s;
    Some (if bit then N.setbit n (N.of_nat b) else n, s)
  end.

Lemma number_some:
  forall (bits: nat) (s: stream),
    (stream.length s >= bits) ->
    exists (r: N * stream),
      (number bits s) = Some r.
Proof.
  induction bits; intros.
  - exists (0%N, s). trivial.
  - simpl.
    case_eq (stream.take s); intros; subst.
    + destruct p.
      destruct IHbits with t.
      apply stream.take_some_length in H0.
      omega.
      rewrite H1. destruct x.
      eexists. reflexivity.
    + apply stream.take_none_length in H0.
      contradict H0. omega.
Qed.

Lemma number_length:
  forall (bits: nat) (s: stream) (n: N) (s': stream),
    (number bits s) = Some (n, s') ->
    stream.length s = bits + stream.length s'.
Proof.
  induction bits; intros.
  - compute in H. injection H; intros. subst.
    omega.
  - unfold number in H.
    mcase (stream.take s) H p H0.
    fold number in H.
    mcase (number bits t) H p H1.
    apply stream.take_some_length in H0.
    rewrite H0. simpl. apply f_equal.
    injection H. intros. subst.
    apply IHbits with (n:=n0).
    assumption.
Qed.

Lemma number_bits:
  forall (bits: nat) (s: stream) (s': stream) (n: N),
    (number bits s) = Some (n, s') ->
    (N.size_nat n <= bits).
Proof.
  induction bits; intros; simpl in H.
  - injection H. intros. subst. simpl. omega.
  - mcase (stream.take s) H p H0.
    mcase (number bits t) H p H1.
    injection H. intros. subst.
    destruct b;
      try (apply Nat.eq_le_incl; apply setbit_bits);
    assert (N.size_nat n0 <= bits); try omega;
    apply IHbits with (s:=t)(s':=s'); assumption.
Qed.

Lemma skipn_length {A}: forall (n: nat)(l: list A),
    List.length (List.skipn n l) <= List.length l.
Proof.
  induction n.
  - trivial.
  - destruct l.
    + trivial.
    + simpl. specialize IHn with (l). omega.
Qed.

Definition consumes {R} (f: stream -> option (R * stream)) :=
  forall (s s': stream)(r: R),
    f s = Some (r, s') ->
    stream.length s' < stream.length s.

Lemma number_consumes:
  forall (bits: nat), consumes (number (S bits)).
Proof.
  unfold number, consumes. intros.
  assert (stream.length s = (S bits) + stream.length s').
  eapply number_length.
  eassumption.
  omega.
Qed.

Definition expect (bits: nat) (expected: N) (s: stream):
  option (unit * stream) :=
  do (n, s) <- (number bits s);
    if (N.eqb n expected)
    then Some (tt, s)
    else None.

Ltac consumes fact I H :=
  try (injection I; intros; subst);
  eapply fact; apply H.
Ltac number_consumes := consumes number_consumes.

Fact expect_consumes:
  forall (bits: nat) (ex: N), consumes (expect (S bits) ex).
Proof.
  unfold expect, consumes. intros.
  mcase (number (S bits) s) H p H0.
  destruct ((n =? ex)%N).
  - number_consumes H H0.
  - discriminate.
Qed.

(* Actual Code *)

Definition condition (s: stream):
  option (ast.condition * stream) :=
  do (n, s) <- (number 4 s);
  match n with
  | 0%N => Some (ast.none, s)
  | 1%N => Some (ast.le, s)
  | 2%N => Some (ast.l, s)
  | 3%N => Some (ast.e, s)
  | 4%N => Some (ast.ne, s)
  | 5%N => Some (ast.ge, s)
  | 6%N => Some (ast.g, s)
  | _ => None
  end.

Fact condition_consumes: consumes (condition).
Proof.
  unfold condition, consumes. intros.
  mcase (number 4 s) H p H0.
  destruct n;
    try destruct p;
    try destruct p;
    try destruct p;
    try discriminate;
    try number_consumes H H0.
Qed.

(* TODO: whatappenz with invalid values *)

Ltac map_number_consumes n e s H p HR :=
  unfold n, consumes; intros;
  mcase (number e s) H p HR; number_consumes H HR.

Definition register (s: stream): option (ast.register * stream) :=
  do (n, s) <- (number ast.register_bits s);
  Some (ast.reg n, s).

Fact register_consumes: consumes (register).
Proof.
  map_number_consumes register ast.register_bits s H p H0.
Qed.

Definition immediate (s: stream): option (ast.immediate * stream) :=
  do (n, s) <- (number ast.constant_bits s);
  Some (ast.imm n, s).

Fact immediate_consumes: consumes (immediate).
Proof.
  map_number_consumes immediate ast.constant_bits s H p H0.
Qed.

Definition displacement (s: stream): option (ast.displacement * stream) :=
  do (n, s) <- (number ast.constant_bits s);
  Some (ast.dsp n, s).

Fact displacement_consumes: consumes (displacement).
Proof.
  map_number_consumes displacement ast.constant_bits s H p H0.
Qed.

Definition destination (s: stream): option (ast.destination * stream) :=
  do (n, s) <- (number ast.constant_bits s);
  Some (ast.dst n, s).

Fact destination_consumes: consumes (destination).
Proof.
  map_number_consumes destination ast.constant_bits s H p H0.
Qed.

(* Actual instruction decoding *)

Definition rrmovl (s: stream): option (ast.instruction * stream) :=
  do (cond, s) <- (condition s);
  do (reg1, s) <- (register s);
  do (reg2, s) <- (register s);
  Some (ast.rrmovl cond reg1 reg2, s).

Ltac assert_consumes e H n HR s s' :=
  mcase e H n HR;
  assert (stream.length s' < stream.length s).
Ltac consumes_trans s' :=
  apply lt_trans with (stream.length s'); try assumption.

Fact rrmovl_consumes: consumes (rrmovl).
Proof.
  unfold consumes, rrmovl. intros.
  assert_consumes (condition s) H x Hx s s0.
  consumes condition_consumes H Hx.
  consumes_trans s0.
  assert_consumes (register s0) H y Hy s0 s1.
  consumes register_consumes H Hy.
  consumes_trans s1.
  assert_consumes (register s1) H z Hz s1 s2.
  consumes register_consumes H Hz.
  injection H. intros. subst. assumption.
Qed.

Definition irmovl (s: stream): option (ast.instruction * stream) :=
  do (n, s) <- (expect 4 0 s);
  do (n, s) <- (expect 4 15 s);
  do (reg1, s) <- (register s);
  do (val, s) <- (immediate s);
  Some (ast.irmovl reg1 val, s).

Fact irmovl_consumes: consumes (irmovl).
Proof.
  unfold consumes, irmovl. intros.
  assert_consumes (expect 4 0 s) H x C0 s s0.
  consumes expect_consumes H C0.
  consumes_trans s0.
  assert_consumes (expect 4 15 s0) H x C1 s0 s1.
  consumes expect_consumes H C1.
  consumes_trans s1.
  assert_consumes (register s1) H x C2 s1 s2.
  consumes register_consumes H C2.
  consumes_trans s2.
  assert_consumes (immediate s2) H x C3 s2 s3.
  consumes immediate_consumes H C3.
  injection H. intros. subst. assumption.
Qed.

Definition rmmovl (s: stream): option (ast.instruction * stream) :=
  do (n, s) <- (expect 4 0 s);
  do (reg1, s) <- (register s);
  do (reg2, s) <- (register s);
  do (val, s) <- (displacement s);
  Some (ast.rmmovl reg1 reg2 val, s).

Fact rmmovl_consumes: consumes (rmmovl).
Proof.
  unfold consumes, rmmovl. intros.
  assert_consumes (expect 4 0 s) H x Hx s s0.
  consumes expect_consumes H Hx.
  consumes_trans s0.
  assert_consumes (register s0) H y Hy s0 s1.
  consumes register_consumes H Hy.
  consumes_trans s1.
  assert_consumes (register s1) H z Hz s1 s2.
  consumes register_consumes H Hz.
  consumes_trans s2.
  assert_consumes (displacement s2) H d Hd s2 s3.
  consumes displacement_consumes H Hd.
  injection H. intros. subst. assumption.
Qed.

Definition mrmovl (s: stream): option (ast.instruction * stream) :=
  do (n, s) <- (expect 4 0 s);
  do (reg1, s) <- (register s);
  do (reg2, s) <- (register s);
  do (val, s) <- (displacement s);
  Some (ast.mrmovl reg1 reg2 val, s).

Fact mrmovl_consumes: consumes (mrmovl).
Proof.
  unfold consumes, mrmovl. intros.
  assert_consumes (expect 4 0 s) H x Hx s s0.
  consumes expect_consumes H Hx.
  consumes_trans s0.
  assert_consumes (register s0) H y Hy s0 s1.
  consumes register_consumes H Hy.
  consumes_trans s1.
  assert_consumes (register s1) H z Hz s1 s2.
  consumes register_consumes H Hz.
  consumes_trans s2.
  assert_consumes (displacement s2) H d Hd s2 s3.
  consumes displacement_consumes H Hd.
  injection H. intros. subst. assumption.
Qed.

Definition operator (s: stream): option (ast.operator * stream) :=
  do (n, s) <- (number 4 s);
  match n with
  | 0%N => Some (ast.addl, s)
  | 1%N => Some (ast.subl, s)
  | 2%N => Some (ast.andl, s)
  | 3%N => Some (ast.xorl, s)
  | _ => None
  end.

Fact operator_consumes: consumes (operator).
Proof.
  unfold operator, consumes. intros.
  mcase (number 4 s) H p H0.
  destruct n;
    repeat (try destruct p;
            try discriminate;
            try number_consumes H H0).
Qed.

Definition OPl (s: stream): option (ast.instruction * stream) :=
  do (op, s) <- (operator s);
  do (reg1, s) <- (register s);
  do (reg2, s) <- (register s);
  Some (ast.OPl op reg1 reg2, s).

Fact OPl_consumes: consumes (OPl).
Proof.
  unfold consumes, OPl. intros.
  assert_consumes (operator s) H x Hx s s0.
  consumes operator_consumes H Hx.
  consumes_trans s0.
  assert_consumes (register s0) H y Hy s0 s1.
  consumes register_consumes H Hy.
  consumes_trans s1.
  assert_consumes (register s1) H z Hz s1 s2.
  consumes register_consumes H Hz.
  injection H. intros. subst. assumption.
Qed.

Definition jump (s: stream): option (ast.instruction * stream) :=
  do (cond, s) <- (condition s);
  do (dest, s) <- (destination s);
  Some (ast.jump cond dest, s).

Fact jump_consumes: consumes (jump).
Proof.
  unfold consumes, jump. intros.
  assert_consumes (condition s) H x Hx s s0.
  consumes condition_consumes H Hx.
  consumes_trans s0.
  assert_consumes (destination s0) H y Hy s0 s1.
  consumes destination_consumes H Hy.
  injection H. intros. subst. assumption.
Qed.

Definition call (s: stream): option (ast.instruction * stream) :=
  do (_, s) <- (expect 4 0 s);
  do (dest, s) <- (destination s);
  Some (ast.call dest, s).

Fact call_consumes: consumes (call).
Proof.
  unfold call, consumes. intros.
  assert_consumes (expect 4 0 s) H x Hx s s0.
  consumes expect_consumes H Hx.
  consumes_trans s0.
  assert_consumes (destination s0) H y Hy s0 s1.
  consumes destination_consumes H Hy.
  injection H. intros. subst. assumption.
Qed.

Definition ret (s: stream): option (ast.instruction * stream) :=
  do (n, s) <- (expect 4 0 s);
  Some (ast.ret, s).

Fact ret_consumes: consumes (ret).
Proof.
  unfold consumes, ret. intros.
  assert_consumes (expect 4 0 s) H x Hx s s0.
  consumes expect_consumes H Hx.
  injection H. intros. subst. assumption.
Qed.

Definition pushl (s: stream): option (ast.instruction * stream) :=
  do (n, s) <- (expect 4 0 s);
  do (reg1, s) <- (register s);
  do (n, s) <- (expect 4 15 s);
  Some (ast.pushl reg1, s).

Fact pushl_consumes: consumes (pushl).
Proof.
  unfold consumes, pushl. intros.
  assert_consumes (expect 4 0 s) H x Hx s s0.
  consumes expect_consumes H Hx.
  consumes_trans s0.
  assert_consumes (register s0) H y Hy s0 s1.
  consumes register_consumes H Hy.
  consumes_trans s1.
  assert_consumes (expect 4 15 s1) H z Hz s1 s2.
  consumes expect_consumes H Hz.
  injection H. intros. subst. assumption.
Qed.

Definition popl (s: stream): option (ast.instruction * stream) :=
  do (n, s) <- (expect 4 0 s);
  do (reg1, s) <- (register s);
  do (n, s) <- (expect 4 15 s);
  Some (ast.popl reg1, s).

Fact popl_consumes: consumes (popl).
Proof.
  unfold consumes, popl. intros.
  assert_consumes (expect 4 0 s) H x Hx s s0.
  consumes expect_consumes H Hx.
  consumes_trans s0.
  assert_consumes (register s0) H y Hy s0 s1.
  consumes register_consumes H Hy.
  consumes_trans s1.
  assert_consumes (expect 4 15 s1) H z Hz s1 s2.
  consumes expect_consumes H Hz.
  injection H. intros. subst. assumption.
Qed.

Definition instruction (s: stream) : option (ast.instruction * stream) :=
  do (n, s) <- (number 4 s);
  match n with
  | 0%N => do (_, s) <- (expect 4 0 s);
           Some (ast.halt, s)
  | 1%N => do (_, s) <- (expect 4 0 s);
           Some (ast.nop, s)
  | 2%N => rrmovl s
  | 3%N => irmovl s
  | 4%N => rmmovl s
  | 5%N => mrmovl s
  | 6%N => OPl s
  | 7%N => jump s
  | 8%N => call s
  | 9%N => ret s
  | 10%N => pushl s
  | 11%N => popl s
  | _ => None
  end.

Fact instruction_consumes: consumes (instruction).
Proof.
  unfold instruction, consumes. intros.
  assert_consumes (number 4 s) H n Hn s s0.
  number_consumes H Hn.
  consumes_trans s0.
  destruct n;
    try destruct p;
    try destruct p;
    try destruct p;
    try destruct p;
    try discriminate;
    try (assert_consumes (expect 4 0 s0) H x Hx s0 s1;
         consumes expect_consumes H Hx;
         injection H; intros; subst; assumption).
  consumes popl_consumes H H.
  consumes jump_consumes H H.
  consumes ret_consumes H H.
  consumes mrmovl_consumes H H.
  consumes irmovl_consumes H H.
  consumes pushl_consumes H H.
  consumes OPl_consumes H H.
  consumes call_consumes H H.
  consumes rmmovl_consumes H H.
  consumes rrmovl_consumes H H.
Qed.

Require Coq.Program.Wf.
Program Fixpoint instructions_rec
        (s: stream) (acc: ast.instructions)
        {measure (stream.length s)}: option (ast.instructions) :=
  if stream.is_finished s then Some acc
  else do (i, s) <- instruction s;
       instructions_rec s (cons i acc).
Next Obligation.
  symmetry in Heq_anonymous.
  eapply instruction_consumes with (r:=i).
  assumption.
Qed.

Definition instructions (s: stream): option (ast.instructions) :=
  instructions_rec s nil.
