Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.

Definition constant_bits := 32.
Definition register_bits := 4.

Inductive immediate: Type :=
| imm: forall (i: N), immediate.
Inductive displacement: Type :=
| dsp: forall (d: N), displacement.
Inductive destination: Type :=
| dst: forall (d: N), destination.
Inductive register: Type :=
| reg: forall (r: N), register.

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

Definition instructions := list instruction.