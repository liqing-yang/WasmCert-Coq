From mathcomp Require Import ssreflect ssrbool eqtype seq.

From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.program_logic Require Import language ectx_language ectxi_language.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import common datatypes_iris datatypes_properties_iris.

From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From iris.program_logic Require Export weakestpre total_weakestpre.

Definition iris_expr := host_expr.
Definition iris_val := host_value.
(* Use gmap to specify the host variable store instead. *)
Definition host_state := gmap id (option iris_val).
Definition state : Type := host_state * store_record * list host_value.
Definition observation := unit. (* TODO: ??? *)

Definition of_val (v : iris_val) : iris_expr := HE_value v.

Fixpoint to_val (e : iris_expr) : option iris_val :=
  match e with
  | HE_value v => Some v
  | _ => None
  end.
  
(* https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html *)
Global Instance val_eq_dec : EqDecision iris_val.
Proof.
  decidable_equality.
Defined.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  destruct e => //=.
  move => H. by inversion H.
Qed.

