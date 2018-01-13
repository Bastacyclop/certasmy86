Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Require Import Lists.List.
Import ListNotations.
Require Import ast.

Fixpoint asm_number_rec
         (n: N) (bit: nat) (acc: list bool): list bool :=
  match bit with
  | 0 => acc
  | S b => asm_number_rec
             n b (cons (N.testbit n (N.of_nat bit)) acc)
  end.

Definition asm_number {bits} (n: number bits): list bool :=
  match n with
  | num _ n _ => asm_number_rec n (pred bits) nil
  end.

Definition asm_operator_num (op: operator): N :=
  match op with
  | addl => 0
  | subl => 1
  | andl => 2
  | xorl => 3
  end.

Fact asm_operator_4bits (op: operator):
  (N.size_nat (asm_operator_num op)) <= 4.
Proof. case op; size. Qed.

Definition asm_operator (op: operator): list bool :=
  (asm_number (num 4
                   (asm_operator_num op)
                   (asm_operator_4bits op))).

Definition asm_condition_num (cond: condition): N :=
  match cond with
  | none => 0
  | le => 1
  | l => 2
  | e => 3
  | ne => 4
  | ge => 5
  | g => 6
  end.

Fact asm_condition_4bits (cond: condition):
  N.size_nat (asm_condition_num cond) <= 4.
Proof. case cond; size. Qed.

Definition asm_condition (cond: condition): list bool :=
  (asm_number (num 4
                   (asm_condition_num cond)
                   (asm_condition_4bits cond))).

Definition asm_instruction (i: instruction): list bool :=
  match i with
  | halt =>
    (asm_number (num 4 0 ltac:(size)))
      ++ (asm_number (num 4 0 ltac:(size)))
  | nop =>
    (asm_number (num 4 1 ltac:(size)))
      ++ (asm_number (num 4 0 ltac:(size)))
  | rrmovl cond (reg ra) (reg rb) =>
    (asm_number (num 4 2 ltac:(size)))
      ++ (asm_condition cond)
      ++ (asm_number ra)
      ++ (asm_number rb)
  | irmovl (imm v) (reg rb) =>
    (asm_number (num 4 3 ltac:(size)))
      ++ (asm_number (num 4 0 ltac:(size)))
      ++ (asm_number (num 4 15 ltac:(size)))
      ++ (asm_number rb)
      ++ (asm_number v)
  | rmmovl (reg ra) (dsp d) (reg rb) =>
    (asm_number (num 4 4 ltac:(size)))
      ++ (asm_number (num 4 0 ltac:(size)))
      ++ (asm_number ra)
      ++ (asm_number rb)
      ++ (asm_number d)
  | mrmovl (dsp d) (reg ra) (reg rb) =>
    (asm_number (num 4 5 ltac:(size)))
      ++ (asm_number (num 4 0 ltac:(size)))
      ++ (asm_number ra)
      ++ (asm_number rb)
      ++ (asm_number d)
  | OPl op (reg ra) (reg rb) =>
    (asm_number (num 4 6 ltac:(size)))
      ++ (asm_operator op)
      ++ (asm_number ra)
      ++ (asm_number rb)
  | jump cond (dst d) =>
    (asm_number (num 4 7 ltac:(size)))
      ++ (asm_condition cond)
      ++ (asm_number d)
  | call (dst d) =>
    (asm_number (num 4 8 ltac:(size)))
      ++ (asm_number (num 4 0 ltac:(size)))
      ++ (asm_number d)
  | ret =>
    (asm_number (num 4 9 ltac:(size)))
      ++ (asm_number (num 4 0 ltac:(size)))
  | pushl (reg ra) =>
    (asm_number (num 4 10 ltac:(size)))
      ++ (asm_number (num 4 0 ltac:(size)))
      ++ (asm_number ra)
      ++ (asm_number (num 4 15 ltac:(size)))
  | popl (reg ra) =>
    (asm_number (num 4 11 ltac:(size)))
      ++ (asm_number (num 4 0 ltac:(size)))
      ++ (asm_number ra)
      ++ (asm_number (num 4 15 ltac:(size)))
  end.

Fixpoint asm_rev (ins: instructions): list bool :=
  match ins with
  | cons i ins => List.rev_append (asm_instruction i)
                                  (asm_rev ins)
  | nil => nil
  end.

Definition asm (ins: instructions): list bool :=
  List.rev (asm_rev ins).

Definition dasm (binary: list bool): option instructions :=
  None.
