Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Require Import Lists.List.
Import ListNotations.

Require ast.

(* Helpers *)

Notation "'do' '(' a ',' b ')' '<-' e ';' c" :=
  (match e with | None => None | Some (a, b) => c end)
    (at level 70, right associativity).

Definition stream := list bool.

Fixpoint number_rec (bits: nat) (s: stream) (acc: N):
  option (N * stream) :=
  match bits, s with
  | 0, _ => Some (acc, s)
  | _, nil => None
  | (S bits), (cons bit s) =>
    number_rec bits s
               (N.lor acc (N.shiftl (N.b2n bit) (N.of_nat bits)))
  end.

Lemma number_rec_some:
  forall (bits: nat) (s: stream) (acc: N),
    (List.length s >= bits) ->
    exists (r: N * stream),
      (number_rec bits s acc) = Some r.
Proof.
  induction bits; intros.
  - exists (acc, s). trivial.
  - simpl. case_eq s; intros; subst.
    + contradict H. simpl. omega.
    + apply IHbits.
      simpl in H.
      omega.
Qed.

Lemma number_rec_skipn:
  forall (bits: nat) (s: stream) (acc: N) (n: N) (s': stream),
    (number_rec bits s acc) = Some (n, s') ->
    s' = skipn bits s.
Proof.
  induction bits; intros.
  - compute in H. injection H.
    intros. simpl. rewrite H0. reflexivity.
  - destruct s; simpl in H.
    + contradict H. discriminate.
    + apply IHbits in H. simpl. assumption.
Qed.

Lemma size_lor: forall(a b: N)(s: nat),
    N.size_nat a <= s ->
    N.size_nat b <= s ->
    N.size_nat (N.lor a b) <= s.
Proof. Admitted.

Lemma number_rec_bits_acc:
  forall (bits: nat) (s: stream) (acc: N) (n: N) (s': stream),
    (number_rec bits s acc) = Some (n, s') ->
    (N.size_nat n <= bits + N.size_nat acc).
Proof.
  induction bits; intros.
  - compute in H. injection H. intros.
    rewrite H1. omega.
  - destruct s; simpl in H.
    + discriminate.
    + pose (complik := (N.lor acc (N.shiftl (N.b2n b) (N.of_nat bits)))).
      specialize IHbits with (s) (complik) (n) (s').
      apply IHbits in H.
      apply Nat.le_trans with (m:=bits + N.size_nat complik).
      assumption.
      simpl. rewrite plus_n_Sm.
      apply plus_le_compat_l.
      unfold complik. unfold complik in H.
      apply size_lor; try omega.
      destruct b; subst. simpl; simpl in H.
Admitted.

Lemma number_rec_bits:
  forall (bits: nat) (s: stream) (s': stream) (n: N),
    (number_rec bits s 0) = Some (n, s') ->
    (N.size_nat n <= bits).
Proof.
  intros.
  specialize number_rec_bits_acc with (bits)(s)(0%N)(n)(s').
  intros.
  apply H0 in H.
  rewrite Nat.add_comm in H.
  simpl in H.
  assumption.
Qed.

Definition number (bits: nat) (s: stream):
  option (N * stream) := (number_rec bits s 0).

Lemma skipn_length {A}: forall (n: nat)(l: list A),
    List.length (List.skipn n l) <= List.length l.
Proof.
  induction n.
  - trivial.
  - destruct l.
    + trivial.
    + simpl. specialize IHn with (l). omega.
Qed.

Lemma number_consumes:
  forall (bits: nat) (s s': stream) (n: N),
    number (S bits) s = Some (n, s') ->
    List.length s' < List.length s.
Proof.
  intros.
  unfold number in H.
  specialize number_rec_skipn with ((S bits))(s)(0%N)(n)(s').
  intros.
  assert (s' = skipn (S bits) s). {
    apply H0. apply H.
  }
  subst.
  induction s.
  - contradict H. simpl. discriminate.
  - simpl.
    apply le_lt_n_Sm.
    apply skipn_length.
Qed.

Definition expect (bits: nat) (expected: N) (s: stream):
  option (unit * stream) :=
  do (n, s) <- (number bits s);
    if (N.eqb n expected)
    then Some (tt, s)
    else None.

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

(* TODO: whatappenz with invalid values *)

Definition register (s: stream): option (ast.register * stream) :=
  do (n, s) <- (number ast.register_bits s);
  Some (ast.reg n, s).

Definition immediate (s: stream): option (ast.immediate * stream) :=
  do (n, s) <- (number ast.constant_bits s);
  Some (ast.imm n, s).

Definition displacement (s: stream): option (ast.displacement * stream) :=
  do (n, s) <- (number ast.constant_bits s);
  Some (ast.dsp n, s).

Definition destination (s: stream): option (ast.destination * stream) :=
  do (n, s) <- (number ast.constant_bits s);
  Some (ast.dst n, s).

(* Actual instruction decoding *)

Definition rrmovl (s: stream): option (ast.instruction * stream) :=
  do (cond, s) <- (condition s);
  do (reg1, s) <- (register s);
  do (reg2, s) <- (register s);
  Some (ast.rrmovl cond reg1 reg2, s).

Definition irmovl (s: stream): option (ast.instruction * stream) :=
  (* 15 is 0x0F, it's required by the spec *)
  do (n, s) <- (expect 8 15 s);
  do (reg1, s) <- (register s);
  do (val, s) <- (immediate s);
  Some (ast.irmovl val reg1, s).

Definition rmmovl (s: stream): option (ast.instruction * stream) :=
  do (n, s) <- (expect 4 0 s);
  do (reg1, s) <- (register s);
  do (reg2, s) <- (register s);
  do (val, s) <- (displacement s);
  Some (ast.rmmovl reg1 val reg2, s).

Definition mrmovl (s: stream): option (ast.instruction * stream) :=
  do (n, s) <- (expect 0 4 s);
  do (reg1, s) <- (register s);
  do (reg2, s) <- (register s);
  do (val, s) <- (displacement s);
  Some (ast.mrmovl val reg1 reg2, s).

Definition op (s: stream): option (ast.operator * stream) :=
  do (n, s) <- (number 4 s);
  match n with
  | 0%N => Some (ast.addl, s)
  | 1%N => Some (ast.subl, s)
  | 2%N => Some (ast.andl, s)
  | 3%N => Some (ast.xorl, s)
  | _ => None
  end.

Definition OPl (s: stream): option (ast.instruction * stream) :=
  do (op, s) <- (op s);
  do (reg1, s) <- (register s);
  do (reg2, s) <- (register s);
  Some (ast.OPl op reg1 reg2, s).

Definition jump (s: stream): option (ast.instruction * stream) :=
  do (cond, s) <- (condition s);
  do (dest, s) <- (destination s);
  Some (ast.jump cond dest, s).

Definition ret (s: stream): option (ast.instruction * stream) :=
  do (n, s) <- (expect 0 4 s);
  Some (ast.ret, s).

Definition pushl (s: stream): option (ast.instruction * stream) :=
  do (n, s) <- (expect 0 4 s);
  do (reg1, s) <- (register s);
  do (n, s) <- (expect 15 4 s);
  Some (ast.pushl reg1, s).

Definition popl (s: stream): option (ast.instruction * stream) :=
  do (n, s) <- (expect 0 4 s);
  do (reg1, s) <- (register s);
  do (n, s) <- (expect 15 4 s);
  Some (ast.popl reg1, s).

Definition instruction (s: stream) : option (ast.instruction * stream) :=
  do (n, s) <- (number 4 s);
  match n with
  | 0%N => do (_, s) <- (expect 0 4 s);
           Some (ast.halt, s)
  | 1%N => do (_, s) <- (expect 0 4 s);
           Some (ast.nop, s)
  | 2%N => rrmovl s
  | 3%N => irmovl s
  | 4%N => rmmovl s
  | 5%N => mrmovl s
  | 6%N => OPl s
  | 7%N => jump s
  | 8%N => rrmovl s
  | 9%N => ret s
  | 10%N => pushl s
  | 11%N => popl s
  | _ => None
  end.

Lemma instruction_consumes:
  forall (s s': stream) (i: ast.instruction),
    instruction s = Some (i, s') ->
    List.length s' < List.length s.
Proof.
  intros.
  unfold instruction, rrmovl, irmovl, rmmovl, mrmovl,
  OPl, jump, rrmovl, ret, pushl, popl, register,
  expect, immediate, displacement, destination in H.
  case_eq (number 4 s); intros; rewrite H0 in H.
Admitted.

Require Coq.Program.Wf.
Program Fixpoint _instructions_rec
        (s: stream) (acc: ast.instructions)
        {measure (List.length s)}: option (ast.instructions) :=
  match s with
  | nil => Some acc
  | s => match instruction s with
    | None => None
    | Some (instr, s) => _instructions_rec s (cons instr acc)
    end
  end.
Next Obligation.
  apply

(*Fixpoint _get_instructions_rec (bits: stream) (acc: instructions): option (instructions) :=
  match bits with
  | nil => Some acc
  | bits => match decode bits with
    | None => None
    | Some (instr, s) => _get_instructions_rec s (cons instr acc)
    end
  end.*)

Definition instructions (bits: stream): option (ast.instructions) := _instructions_rec bits nil.
