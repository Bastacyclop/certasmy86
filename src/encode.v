Require Import util.
Import ListNotations.
Require ast.
Require stream.
Import stream.BitNotations.

Definition stream := stream.bit.

(* Encodes a number into binary (little endian) *)
Fixpoint number
         (bits: nat) (n: N) (s: stream): stream :=
  match bits with
  | 0 => s
  | S b => number b (N.shiftr n 1) (stream.put (N.testbit n 0) s)
  end.

Lemma number_length:
  forall (bits: nat) (n: N) (s: stream),
    stream.length (number bits n s) = (stream.length s) + bits.
Proof.
  induction bits; intros.
  - trivial.
  - simpl.
    rewrite IHbits.
    rewrite stream.put_length.
    omega.
Qed.


Definition number_puts (bits: nat) (n: N) :=
  stream.puts (number bits n).

Goal number_puts 4 0 [0; 0; 0; 0]%bit.
Proof. compute. reflexivity. Qed.
Goal number_puts 4 5 [1; 0; 1; 0]%bit.
Proof. compute. reflexivity. Qed.
Goal number_puts 4 15 [1; 1; 1; 1]%bit.
Proof. compute. reflexivity. Qed.

Definition operator_num (op: ast.operator): N :=
  match op with
  | ast.addl => 0
  | ast.subl => 1
  | ast.andl => 2
  | ast.xorl => 3
  end.

Fact operator_4bits (op: ast.operator):
  (N.size_nat (operator_num op)) <= 4.
Proof. case op; compute; omega. Qed.

Definition operator (op: ast.operator) (s: stream): stream :=
  (number 4 (operator_num op) s).

Definition condition_num (cond: ast.condition): N :=
  match cond with
  | ast.none => 0
  | ast.le => 1
  | ast.l => 2
  | ast.e => 3
  | ast.ne => 4
  | ast.ge => 5
  | ast.g => 6
  end.

Fact condition_4bits (cond: ast.condition):
  N.size_nat (condition_num cond) <= 4.
Proof. case cond; compute; omega. Qed.

Definition condition (cond: ast.condition) (s: stream): stream :=
  (number 4 (condition_num cond) s).

Definition register (r: ast.register) (s: stream): stream :=
  match r with
  | ast.reg n => (number ast.register_bits n s)
  end.

Definition immediate (i: ast.immediate) (s: stream): stream :=
  match i with
  | ast.imm n => (number ast.constant_bits n s)
  end.

Definition displacement (d: ast.displacement) (s: stream): stream :=
  match d with
  | ast.dsp n => (number ast.constant_bits n s)
  end.

Definition destination (d: ast.destination) (s: stream): stream :=
  match d with
  | ast.dst n => (number ast.constant_bits n s)
  end.

Notation "f '>>' v" := (f v)
                         (at level 60, right associativity).

Definition instruction (i: ast.instruction) (s: stream): stream :=
  match i with
  | ast.halt => number 4 0 >> number 4 0 >> s
  | ast.nop => number 4 1 >> number 4 0 >> s
  | ast.rrmovl cond ra rb =>
    number 4 2 >> condition cond >>
           register ra >> register rb >> s
  | ast.irmovl rb v =>
    number 4 3 >> number 4 0 >>
           number 4 15 >> register rb >>
           immediate v >> s
  | ast.rmmovl ra rb d =>
    number 4 4 >> number 4 0 >>
           register ra >> register rb >>
           displacement d >> s
  | ast.mrmovl ra rb d =>
    number 4 5 >> number 4 0 >>
           register ra >> register rb >>
           displacement d >> s
  | ast.OPl op ra rb =>
    number 4 6 >> operator op >>
           register ra >> register rb >> s
  | ast.jump cond d =>
    number 4 7 >> condition cond >> destination d >> s
  | ast.call d =>
    number 4 8 >> number 4 0 >> destination d >> s
  | ast.ret => number 4 9 >> number 4 0 >> s
  | ast.pushl ra =>
    number 4 10 >> number 4 0 >>
           register ra >> number 4 15 >> s
  | ast.popl ra =>
    number 4 11 >> number 4 0 >>
           register ra >> number 4 15 >> s
  end.

Goal stream.puts (instruction ast.nop)
      [0; 0; 0; 0; 1; 0; 0; 0]%bit.
Proof. compute. reflexivity. Qed.

Fixpoint instructions
         (ins: ast.instructions) (s: stream): stream :=
  match ins with
  | cons i ins => instructions ins (instruction i s)
  | nil => s
  end.