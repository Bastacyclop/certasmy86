Require Import util.

Definition constant_bits := 32.
Definition register_bits := 4.
Definition nb_registers := 7.

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
| rmmovl: register -> register -> displacement -> instruction
| mrmovl: register -> register -> displacement -> instruction
| OPl: operator -> register -> register -> instruction
| jump: condition -> destination -> instruction
| call: destination -> instruction
| ret: instruction
| pushl: register -> instruction
| popl: register -> instruction.

Definition instructions := list instruction.
Inductive valid_instruction (i: instruction): Type :=
| valid_halt: i = halt -> valid_instruction i
| valid_nop: i = nop -> valid_instruction i
| valid_rrmovl: forall(c: condition)(n1 n2: nat),
    n1 <= nb_registers -> n2 <= nb_registers -> i = (rrmovl c (reg (N.of_nat n1)) (reg (N.of_nat n2))) -> valid_instruction i
| valid_irmovl: forall(imm: immediate)(n: nat),
    n <= nb_registers -> i = (irmovl imm (reg (N.of_nat n))) -> valid_instruction i
| valid_rmmovl: forall(n1: nat)(d: displacement)(n2: nat),
    n1 <= nb_registers -> n2 <= nb_registers -> i = (rmmovl (reg (N.of_nat n1)) (reg (N.of_nat n2)) d) ->  valid_instruction i
| valid_mrmovl: forall(d: displacement)(n1 n2: nat),
    n1 <= nb_registers -> n2 <= nb_registers -> i = (mrmovl (reg (N.of_nat n1)) (reg (N.of_nat n2)) d) ->  valid_instruction i
| valid_OPl: forall(o: operator)(n1 n2: nat),
    n1 <= nb_registers -> n2 <= nb_registers -> i = (OPl o (reg (N.of_nat n1)) (reg (N.of_nat n2))) -> valid_instruction i
| valid_jump: forall(c: condition)(d: destination), i = (jump c d) -> valid_instruction i
| valid_call: forall(d: destination), i = (call d) -> valid_instruction i
| valid_ret: i = ret -> valid_instruction i
| valid_pushl: forall(n: nat), n < nb_registers -> i = (pushl (reg (N.of_nat n))) -> valid_instruction i
| valid_popl:  forall(n: nat), n < nb_registers -> i = (popl (reg (N.of_nat n)))  -> valid_instruction i.
