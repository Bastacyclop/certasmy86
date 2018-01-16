Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Require Import Lists.List.
Import ListNotations.

Require ast.

Fixpoint number_rec
         (n: N) (bits: nat) (acc: list bool): list bool :=
  match bits with
  | 0 => acc
  | S b => number_rec
             (N.shiftr n 1) b (cons (N.testbit n 0) acc)
  end.

(* Encodes a number into binary (little endian) *)
Definition number (bits: nat) (n: N): list bool :=
  number_rec n bits nil.

Lemma number_rec_bits:
  forall (bits: nat) (n: N) (acc: list bool),
    List.length (number_rec n bits acc)
    = (List.length acc) + bits.
Proof.
  induction bits; intros.
  - trivial.
  - simpl.
    rewrite <- plus_n_Sm.
    apply IHbits.
Qed.

Lemma number_bits: forall (n: N)(bits: nat),
    List.length (number bits n) = bits.
Proof.
  intros.
  unfold number. simpl. rewrite number_rec_bits.
  compute. trivial.
Qed.

Notation "'b[' n ';' b ']'" := (number b n) (at level 60).

Goal b[0; 4] = [false; false; false; false].
Proof. trivial. Qed.
Goal b[5; 4] = [false; true; false; true].
Proof. trivial. Qed.
Goal b[15; 4] = [true; true; true; true].
Proof. trivial. Qed.

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

Definition operator (op: ast.operator): list bool :=
  (number 4 (operator_num op)).

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

Definition condition (cond: ast.condition): list bool :=
  (number 4 (condition_num cond)).

Definition register (r: ast.register): list bool :=
  match r with
  | ast.reg n => (number ast.register_bits n)
  end.

Definition immediate (i: ast.immediate): list bool :=
  match i with
  | ast.imm n => (number ast.constant_bits n)
  end.

Definition displacement (d: ast.displacement): list bool :=
  match d with
  | ast.dsp n => (number ast.constant_bits n)
  end.

Definition destination (d: ast.destination): list bool :=
  match d with
  | ast.dst n => (number ast.constant_bits n)
  end.

Definition instruction (i: ast.instruction): list bool :=
  match i with
  | ast.halt => b[0; 4] ++ b[0; 4]
  | ast.nop => b[1; 4] ++ b[0; 4]
  | ast.rrmovl cond ra rb =>
    b[2; 4] ++ (condition cond) ++ (register ra) ++ (register rb)
  | ast.irmovl v rb =>
    b[3; 4] ++ b[0; 4] ++ b[15; 4] ++ (register rb) ++ (immediate v)
  | ast.rmmovl ra d rb =>
    b[4; 4] ++ b[0; 4] ++ (register ra) ++ (register rb) ++ (displacement d)
  | ast.mrmovl d ra rb =>
    b[5; 4] ++ b[0; 4] ++ (register ra) ++ (register rb) ++ (displacement d)
  | ast.OPl op ra rb =>
    b[6; 4] ++ (operator op) ++ (register ra) ++ (register rb)
  | ast.jump cond d =>
    b[7; 4] ++ (condition cond) ++ (destination d)
  | ast.call d =>
    b[8; 4] ++ b[0; 4] ++ (destination d)
  | ast.ret => b[9; 4] ++ b[0; 4]
  | ast.pushl ra =>
    b[10; 4] ++ b[0; 4] ++ (register ra) ++ b[15; 4]
  | ast.popl ra =>
    b[11; 4] ++ b[0; 4] ++ (register ra) ++ b[15; 4]
  end.

Fixpoint instructions_rev (ins: ast.instructions): list bool :=
  match ins with
  | cons i ins => List.rev_append (instruction i)
                                  (instructions_rev ins)
  | nil => nil
  end.

Definition instructions (ins: ast.instructions): list bool :=
  List.rev (instructions_rev ins).