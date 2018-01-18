Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Require Import Lists.List.
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
  | S b => number b n (stream.put (N.testbit n (N.of_nat b)) s)
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


Definition is_number_output (bits: nat) (n: N) :=
  stream.puts (number bits n).

Goal is_number_output 4 0 [0; 0; 0; 0]%bit.
Proof. compute. reflexivity. Qed.
Goal is_number_output 4 5 [0; 1; 0; 1]%bit.
Proof. compute. reflexivity. Qed.
Goal is_number_output 4 15 [1; 1; 1; 1]%bit.
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

Notation "v '|>' f" := (f v)
                         (at level 50, left associativity).

Definition instruction (i: ast.instruction) (s: stream): stream :=
  match i with
  | ast.halt => s |> number 4 0 |> number 4 0
  | ast.nop => s |> number 4 1 |> number 4 0
  | ast.rrmovl cond ra rb =>
    s |> number 4 2 |> condition cond |> register ra |> register rb
  | ast.irmovl v rb =>
    s |> number 4 3 |> number 4 0 |> number 4 15 |> register rb |> immediate v
  | ast.rmmovl ra d rb =>
    s |> number 4 4 |> number 4 0 |> register ra |> register rb |> displacement d
  | ast.mrmovl d ra rb =>
    s |> number 4 5 |> number 4 0 |> register ra |> register rb |> displacement d
  | ast.OPl op ra rb =>
    s |> number 4 6 |> operator op |> register ra |> register rb
  | ast.jump cond d =>
    s |> number 4 7 |> number 4 7 |> condition cond |> destination d
  | ast.call d =>
    s |> number 4 8 |> number 4 0 |> destination d
  | ast.ret => s |> number 4 9 |> number 4 0
  | ast.pushl ra =>
    s |> number 4 10 |> number 4 0 |> register ra |> number 4 15
  | ast.popl ra =>
    s |> number 4 11 |> number 4 0 |> register ra |> number 4 15
  end.

Goal stream.puts (instruction ast.nop)
      [0; 0; 0; 1; 0; 0; 0; 0]%bit.
Proof. compute. reflexivity. Qed.

Fixpoint instructions
         (ins: ast.instructions) (s: stream): stream :=
  match ins with
  | cons i ins => instructions ins (instruction i s)
  | nil => s
  end.