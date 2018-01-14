Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Require Import Lists.List.
Import ListNotations.
Require Import ast.

Fixpoint encode_number_rec
         (n: N) (bits: nat) (acc: list bool): list bool :=
  match bits with
  | 0 => acc
  | S b => encode_number_rec
             (N.shiftr n 1) b (cons (N.testbit n 0) acc)
  end.

(* Encodes a number into binary (little endian) *)
Definition encode_number {bits} (n: number bits): list bool :=
  match n with
  | num _ n _ => encode_number_rec n bits nil
  end.

Lemma encode_number_rec_bits:
  forall (bits: nat) (n: N) (acc: list bool),
    List.length (encode_number_rec n bits acc)
    = (List.length acc) + bits.
Proof.
  induction bits; intros.
  - trivial.
  - simpl.
    rewrite <- plus_n_Sm.
    apply IHbits.
Qed.

Lemma encode_number_bits {bits}: forall (n: number bits),
    List.length (encode_number n) = bits.
Proof.
  induction n.
  simpl. rewrite encode_number_rec_bits.
  trivial.
Qed.

Notation "'b[' n ';' b ']'" := (encode_number (num b n ltac:(size)))
                                 (at level 60).

Goal b[0; 4] = [false; false; false; false].
Proof. trivial. Qed.
Goal b[5; 4] = [false; true; false; true].
Proof. trivial. Qed.
Goal b[15; 4] = [true; true; true; true].
Proof. trivial. Qed.

Definition encode_operator_num (op: operator): N :=
  match op with
  | addl => 0
  | subl => 1
  | andl => 2
  | xorl => 3
  end.

Fact encode_operator_4bits (op: operator):
  (N.size_nat (encode_operator_num op)) <= 4.
Proof. case op; size. Qed.

Definition encode_operator (op: operator): list bool :=
  (encode_number (num 4
                      (encode_operator_num op)
                      (encode_operator_4bits op))).

Definition encode_condition_num (cond: condition): N :=
  match cond with
  | none => 0
  | le => 1
  | l => 2
  | e => 3
  | ne => 4
  | ge => 5
  | g => 6
  end.

Fact encode_condition_4bits (cond: condition):
  N.size_nat (encode_condition_num cond) <= 4.
Proof. case cond; size. Qed.

Definition encode_condition (cond: condition): list bool :=
  (encode_number (num 4
                      (encode_condition_num cond)
                      (encode_condition_4bits cond))).

Definition encode_instruction (i: instruction): list bool :=
  match i with
  | halt => b[0; 4] ++ b[0; 4]
  | nop => b[1; 4] ++ b[0; 4]
  | rrmovl cond (reg ra) (reg rb) =>
    b[2; 4]
     ++ (encode_condition cond)
     ++ (encode_number ra)
     ++ (encode_number rb)
  | irmovl (imm v) (reg rb) =>
    b[3; 4] ++ b[0; 4] ++ b[15; 4]
     ++ (encode_number rb)
     ++ (encode_number v)
  | rmmovl (reg ra) (dsp d) (reg rb) =>
    b[4; 4] ++ b[0; 4]
     ++ (encode_number ra)
     ++ (encode_number rb)
     ++ (encode_number d)
  | mrmovl (dsp d) (reg ra) (reg rb) =>
    b[5; 4] ++ b[0; 4]
     ++ (encode_number ra)
     ++ (encode_number rb)
     ++ (encode_number d)
  | OPl op (reg ra) (reg rb) =>
    b[6; 4]
     ++ (encode_operator op)
     ++ (encode_number ra)
     ++ (encode_number rb)
  | jump cond (dst d) =>
    b[7; 4]
     ++ (encode_condition cond)
     ++ (encode_number d)
  | call (dst d) =>
    b[8; 4] ++ b[0; 4]
     ++ (encode_number d)
  | ret => b[9; 4] ++ b[0; 4]
  | pushl (reg ra) =>
    b[10; 4] ++ b[0; 4] ++ (encode_number ra) ++ b[15; 4]
  | popl (reg ra) =>
    b[11; 4] ++ b[0; 4] ++ (encode_number ra) ++ b[15; 4]
  end.

Fixpoint encode_rev (ins: instructions): list bool :=
  match ins with
  | cons i ins => List.rev_append (encode_instruction i)
                                  (encode_rev ins)
  | nil => nil
  end.

Definition encode (ins: instructions): list bool :=
  List.rev (encode_rev ins).

Definition dasm (binary: list bool): option instructions :=
  None.
