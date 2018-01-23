Require Import util.

Definition constant_bits := 32.
Definition register_bits := 4.

(* Wrapper types for safety *)

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

(* Validity rules *)

Definition valid_register (n: N): Prop := (n <= 7)%N.

Definition valid_constant (n: N): Prop := N.size_nat n <= constant_bits.

Inductive valid_instruction: instruction -> Type :=
| valid_halt: valid_instruction halt
| valid_nop: valid_instruction nop
| valid_rrmovl: forall(c: condition)(r1 r2: N),
                  valid_register r1 ->
                  valid_register r2 ->
                    valid_instruction (rrmovl c (reg r1) (reg r2))
| valid_irmovl: forall(r1 c: N),
                  valid_register r1 ->
                  N.size_nat c <= constant_bits ->
                    valid_instruction (irmovl (reg r1) (imm c))
| valid_rmmovl: forall(r1 r2 c: N),
                  valid_register r1 ->
                  valid_register r2 ->
                  N.size_nat c <= constant_bits ->
                    valid_instruction (rmmovl (reg r1) (reg r2) (dsp c))
| valid_mrmovl: forall(r1 r2 c: N),
                  valid_register r1 ->
                  valid_register r2 ->
                  valid_constant c ->
                    valid_instruction (mrmovl (reg r1) (reg r2) (dsp c))
| valid_OPl: forall(o: operator)(r1 r2: N),
                  valid_register r1 ->
                  valid_register r2 ->
                    valid_instruction (OPl o (reg r1) (reg r2))
| valid_jump: forall(cond: condition)(c: N),
                  valid_constant c ->
                    valid_instruction (jump cond (dst c))
| valid_call: forall(c: N),
                  valid_constant c ->
                    valid_instruction (call (dst c))
| valid_ret: valid_instruction ret
| valid_pushl: forall(r: N),
                    valid_register r -> valid_instruction (pushl (reg r))
| valid_popl:  forall(r: N),
                    valid_register r -> valid_instruction (popl (reg r)).
