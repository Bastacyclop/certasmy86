Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.

Inductive number (bits: nat): Set :=
| num: forall (x: N), (N.size_nat x) <= bits -> number bits.

Definition constant_bits := 32.
Definition register_bits := 4.

Inductive immediate: Type :=
| imm: forall (i: number constant_bits), immediate.
Inductive displacement: Type :=
| dsp: forall (d: number constant_bits), displacement.
Inductive destination: Type :=
| dst: forall (d: number constant_bits), destination.
Inductive register: Type :=
| reg: forall (r: number register_bits), register.

Inductive operator: Set :=
| addl
| subl
| andl
| xorl.

Inductive condition: Set :=
| none
| le
| l
| e
| ne
| ge
| g.

Inductive instruction: Type :=
| halt: instruction
| nop: instruction
| rrmovl: condition -> register -> register -> instruction
| irmovl: immediate -> register -> instruction
| rmmovl: register -> displacement -> register -> instruction
| mrmovl: displacement -> register -> register -> instruction
| OPl: operator -> register -> register -> instruction
| jump: condition -> destination -> instruction
| call: destination -> instruction
| ret: instruction
| pushl: register -> instruction
| popl: register -> instruction.

Ltac size := compute; omega.
Notation "'imm' i" := (imm (num constant_bits i ltac:(size)))
                      (at level 90).
Notation "'reg' r" := (reg (num register_bits r ltac:(size)))
                      (at level 90).
Notation "'dsp' d" := (dsp (num constant_bits d ltac:(size)))
                      (at level 90).
Notation "'dst' d" := (dst (num constant_bits d ltac:(size)))
                      (at level 90).

Example ex1 := (rrmovl none (reg 1) (reg 2)).
Example ex2 := (call (dst 5)).