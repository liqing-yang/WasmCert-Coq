
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

Require Export common operations_iris datatypes_iris datatypes_properties_iris properties_iris.
Require Import iris_locations iris.

Definition instance1 := 1.
Definition instance2 := 2.

Definition store11 := list_byte_of_string "store11".
Definition store42 := list_byte_of_string "store42".

Notation "A ;;; B" := (HE_seq A B) (at level 2).
Notation "A ::= B" := (HE_setglobal A B) (at level 5).
(*
Definition Program1 :=
  10 ::= 
  10 ::= (HE_new_rec [::(store11, )])

Lemma example1:
*)
  
