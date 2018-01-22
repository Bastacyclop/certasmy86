Require Import util.

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

Definition cst_max := 4294967295%N.
Definition reg_max := 7%N.

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
| irmovl: register -> immediate -> instruction
| rmmovl: register -> register -> displacement -> instruction
| mrmovl: register -> register -> displacement -> instruction
| OPl: operator -> register -> register -> instruction
| jump: condition -> destination -> instruction
| call: destination -> instruction
| ret: instruction
| pushl: register -> instruction
| popl: register -> instruction.

Definition instructions := list instruction.
Inductive valid_instruction: instruction -> Type :=
| valid_halt: valid_instruction halt
| valid_nop: valid_instruction nop
| valid_rrmovl: forall(c: condition)(n1 n2: N),
                  (n1 <= reg_max)%N ->
                  (n2 <= reg_max)%N ->
                    valid_instruction (rrmovl c (reg n1) (reg n2))
| valid_irmovl: forall(n1 n2: N),
                  (n1 <= reg_max)%N ->
                  (n2 <= cst_max)%N ->
                    valid_instruction (irmovl (reg n1) (imm n2))
| valid_rmmovl: forall(n1 n2 n3: N),
                  (n1 <= reg_max)%N ->
                  (n2 <= reg_max)%N ->
                  (n3 <= cst_max)%N ->
                    valid_instruction (rmmovl (reg n1) (reg n2) (dsp n3))
| valid_mrmovl: forall(n1 n2 n3: N),
                  (n1 <= reg_max)%N ->
                  (n2 <= reg_max)%N ->
                  (n3 <= cst_max)%N ->
                    valid_instruction (mrmovl (reg n1) (reg n2) (dsp n3))
| valid_OPl: forall(o: operator)(n1 n2: N),
                  (n1 <= reg_max)%N ->
                  (n2 <= reg_max)%N ->
                    valid_instruction (OPl o (reg n1) (reg n2))
| valid_jump: forall(c: condition)(n: N),
                  (n <= cst_max)%N ->
                    valid_instruction (jump c (dst n))
| valid_call: forall(n: N),
                  (n <= cst_max)%N ->
                    valid_instruction (call (dst n))
| valid_ret: valid_instruction ret
| valid_pushl: forall(n: N),
                    (n <= reg_max)%N -> valid_instruction (pushl (reg n))
| valid_popl:  forall(n: N),
                    (n <= reg_max)%N -> valid_instruction (popl (reg n)).
(*
Inductive valid_instruction (i: instruction): Type :=
| valid_halt: valid_instruction halt
| valid_nop: valid_instruction nop
| valid_rrmovl: forall(c: condition)(n1 n2: N),
    N.le n1 nb_registers -> N.le n2 nb_registers -> valid_instruction (rrmovl c (reg n1) (reg n2))
| valid_irmovl: forall(i: immediate)(n: N),
    n <= nb_registers -> valid_instruction irmovl.
| valid_rmmovl: forall(n1: N)(i: immediate)(n2: N),
    n1 <= nb_registers -> n2 <= nb_registers -> valid_instruction rmmovl.
| valid_mrmovl: forall(d: displacement)(n1 n2: N),
    n1 <= nb_registers -> n2 <= nb_registers -> valid_instruction mrmovl.
| valid_OPl: forall(o: operator)(n1 n2: N),
    n1 <= nb_registers -> n2 <= nb_registers -> valid_instruction OPl.
| valid_jump: valid_instruction jump
| valid_call: valid_instruction call
| valid_ret: valid_instruction ret
| valid_pushl: forall(n: N), n <= nb_registers -> valid_instruction pushl
| valid_popl:  forall(n: N), n <= nb_registers -> valid_instruction popl.*)
