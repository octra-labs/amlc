(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import Bool.

Inductive mode : Type :=
| PBase
| PRec
| PStore
| PClos
| PRaise
| PDep
| PRow.

Scheme Equality for mode.

Definition allow (item : mode) : bool :=
  match item with
  | PBase => true
  | _ => false
  end.

Definition held (item : mode) : bool := negb (allow item).

Theorem allow_exact : forall item,
  allow item = true <-> item = PBase.
Proof.
  intros item.
  destruct item; simpl; split; intros H; try reflexivity; try discriminate.
Qed.

Theorem held_exact : forall item,
  held item = true <-> item <> PBase.
Proof.
  intros item.
  destruct item; simpl.
  - split.
    + intro H. discriminate.
    + intro H. exfalso. apply H. reflexivity.
  - split.
    + intro H. discriminate.
    + intro H. reflexivity.
  - split.
    + intro H. discriminate.
    + intro H. reflexivity.
  - split.
    + intro H. discriminate.
    + intro H. reflexivity.
  - split.
    + intro H. discriminate.
    + intro H. reflexivity.
  - split.
    + intro H. discriminate.
    + intro H. reflexivity.
  - split.
    + intro H. discriminate.
    + intro H. reflexivity.
Qed.

Corollary rec_held : held PRec = true.
Proof. reflexivity. Qed.

Corollary store_held : held PStore = true.
Proof. reflexivity. Qed.

Corollary clos_held : held PClos = true.
Proof. reflexivity. Qed.

Corollary raise_held : held PRaise = true.
Proof. reflexivity. Qed.

Corollary dep_held : held PDep = true.
Proof. reflexivity. Qed.

Corollary row_held : held PRow = true.
Proof. reflexivity. Qed.