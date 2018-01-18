Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.
Require Lists.List.

Inductive t (A: Type) :=
| stream: list A -> t A.

Definition empty {A} := stream A nil.

Definition length {A} (s: t A): nat :=
  match s with
  | stream  _ l => List.length l
  end.

Definition is_finished {A} (s: t A): bool :=
  match s with
  | stream _ nil => true
  | _ => false
  end.

Definition take {A} (s: t A): option (A * t A) :=
  match s with
  | stream _ l =>
    match l with
    | nil => None
    | cons a l => Some (a, stream _ l)
    end
  end.

Lemma take_none_length: forall (A: Type)(s: t A),
    take s = None -> length s = 0.
Proof.
  unfold take, length. intros.
  destruct s. destruct l.
  - trivial.
  - discriminate.
Qed.

Lemma take_some_length: forall (A: Type)(s s': t A)(r: A),
    take s = Some (r, s') -> length s = S (length s').
Proof.
  unfold take, length. intros.
  destruct s. destruct s'. destruct l.
  - discriminate.
  - injection H. intros. subst. reflexivity.
Qed.

Definition put {A} (v: A) (s: t A): t A :=
  match s with
  | stream _ l => stream _ (cons v l)
  end.

Lemma put_length: forall (A: Type)(v: A)(s: t A),
    length (put v s) = S (length s).
Proof.
  unfold put, length. intros.
  destruct s. reflexivity.
Qed.

Fixpoint put_list {A} (l: list A) (s: t A): t A :=
  match l with
  | nil => s
  | cons a l => put_list l (put a s)
  end.

Definition puts {A}
           (f: t A -> t A)
           (l: list A): Prop :=
  eq (f empty) (put_list l empty).

Definition bit := t bool.

Module BitNotations.
  Notation "0" := (false): bit_scope.
  Notation "1" := (true): bit_scope.
  Delimit Scope bit_scope with bit.
End BitNotations.
