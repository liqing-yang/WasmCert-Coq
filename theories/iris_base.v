From mathcomp Require Import ssreflect ssrbool eqtype seq.

From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.program_logic Require Import language ectx_language ectxi_language.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import common operations datatypes datatypes_properties opsem interpreter binary_format_parser.

From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From iris.program_logic Require Export weakestpre total_weakestpre.

Definition expr := host_expr.
Definition val := host_value.
(* Use gmap to specify the host variable store instead. *)
Definition host_state := gmap id (option val).
Definition state : Type := host_state * store_record * (list host_value).
Definition observation := unit. (* TODO: ??? *)

Definition of_val (v : val) : expr := HE_value v.

Fixpoint to_val (e : expr) : option val :=
  match e with
  | HE_value v => Some v
  | _ => None
  end.
  
(* https://softwarefoundations.cis.upenn.edu/qc-current/Typeclasses.html *)
Global Instance val_eq_dec : EqDecision val.
Proof. decidable_equality. Defined.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  destruct e => //=.
  move => H. by inversion H.
Qed.

