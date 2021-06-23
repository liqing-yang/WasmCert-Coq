
From mathcomp Require Import ssreflect ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import gmap strings.
From iris.algebra Require Import auth.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import gen_heap proph_map gen_inv_heap.
From iris.program_logic Require Import weakestpre total_weakestpre.
From iris.program_logic Require Export language lifting.

Require Import iris.

Definition instance1 := 1%N.
Definition instance2 := 2%N.
Definition memory1 := 11%N.
Definition byte1 := 21%N.
Definition byte2 := 22%N.

Definition store11 := list_byte_of_string "store11".
Definition store42 := list_byte_of_string "store42".

Notation "A ;;; B" := (HE_seq A B) (at level 2).
Notation "A ::= B" := (HE_setglobal A B) (at level 5).

Definition Program1 :=
  (memory1 ::= (HE_wasm_memory_create 2 2 #00));;;
  (byte1 ::= (HE_value (HV_byte #34)));;;
  (byte2 ::= (HE_value (HV_byte #32)));;;
  (HE_wasm_memory_set memory1 0%N byte1);;;
  (HE_wasm_memory_set memory1 1%N byte2).

Open Scope string_scope.
Open Scope SEQ.

Context `{!hsG Σ, !locG Σ, !wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ}.

Lemma program1_spec s E:
  ⊢
  (WP Program1 @ s; E {{ v, (0%N ↦[wm][ 0%N ] #34) ∗ (0%N ↦[wm][ 1%N ] #32) }})%I.
Proof.
  repeat (iApply wp_seq; iSplitR).
  iApply wp_setglobal_reduce; iSplitR.
  iApply wp_mono; last by iApply wp_memory_create.
  iIntros (v) "H".
  destruct v => //; destruct w; try iAssumption; destruct m => //.
  admit.
Admitted.
