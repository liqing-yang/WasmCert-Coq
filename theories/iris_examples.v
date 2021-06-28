
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
Require Import stdpp_aux iris_locations iris.

Definition memory1 := 11%N.
Definition byte1 := 21%N.
Definition byte2 := 22%N.

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

(*
  Our host language doesn't have any instruction that allocates new global variables
  (setglobal only modifies), so we assume a set of pre-allocated variables initialised to zero.
  

  Note that it's non-trivial to support the allocation of new global variables at a specific
  address (id): this would require the negative knowledge that a particular id is NOT allocated,
  which doesn't seem to be possible in Iris?
*)
Lemma program1_spec s E:
  memory1 ↦[host] wasm_zero -∗
  byte1 ↦[host] wasm_zero -∗
  byte2 ↦[host] wasm_zero -∗       
  (WP Program1 @ s; E {{ _, ∃ n, memory1 ↦[host] HV_wov (WOV_memoryref (Mk_memidx n)) ∗ byte1 ↦[host] HV_byte #34 ∗ byte2 ↦[host] HV_byte #32 ∗ N.of_nat n↦[wm][ 0%N ] #34 ∗ N.of_nat n ↦[wm][ 1%N ] #32 }})%I.
Proof.
  iIntros "Hm Hb1 Hb2".
  iApply wp_seq; iSplitL.
  iApply wp_seq; iSplitL.
  iApply wp_seq; iSplitR "Hb2".
  iApply wp_seq; iSplitR "Hb1".
  iApply wp_setglobal_reduce; iSplitR.
  - (* memory_create *)
    iApply wp_mono; last by iApply wp_memory_create.
    iIntros (v) "H".
    destruct v => //; destruct w; try iAssumption; destruct m => //.
    iSplit => //.
    instantiate (1 := (fun v => match v with
                            | HV_wov (WOV_memoryref (Mk_memidx n)) =>
                                (N.of_nat n ↦[wm][0%N] #00 ∗ N.of_nat n ↦[wm][1%N] #00)
                            | _ => False
                            end
                        )%I).
    unfold new_2d_gmap_at_n => /=.
    Print big_sepM_insert.
    iDestruct (big_sepM_insert with "H") as "[Hb H]" => /=; first by rewrite lookup_insert_ne.
    iFrame.
    iDestruct (big_sepM_insert with "H") as "[Hb H]" => /=; first by rewrite lookup_empty.
    by iFrame.
  - (* setglobal memory *)
    iIntros (v) "[%Hv H]".
    (* Having to do this every time is a bit dumb. Is there a way around this? *)
    instantiate (1 := (fun v => match v with
                            | HV_wov (WOV_memoryref (Mk_memidx n)) =>
                                (N.of_nat n ↦[wm][0%N] #00 ∗ N.of_nat n ↦[wm][1%N] #00 ∗ memory1 ↦[host] v)%I
                            | _ => False
                            end
                      )%I).
    simpl.
    iApply (wp_setglobal_value with "Hm") => //.
    iIntros "!> Hm".
    destruct v => //; destruct w; try iAssumption; destruct m => //.
    by iFrame.
  - (* setglobal byte1 *)
    iIntros (v) "H".
    iApply (wp_setglobal_value with "Hb1") => //.
    destruct v => //; destruct w; try iAssumption; destruct m => //.
    instantiate (1 := (fun v => (∃ n, (N.of_nat n ↦[wm][0%N] #00 ∗ N.of_nat n ↦[wm][1%N] #00 ∗ memory1 ↦[host] (HV_wov (WOV_memoryref (Mk_memidx n))) ∗ byte1 ↦[host] (HV_byte #34)))%I)).
    iIntros "!> Hb1".
    iExists n.
    by iFrame.
  - (* setglobal byte2 *)
    iIntros (v) "H".
    iApply (wp_setglobal_value with "Hb2") => //.
    instantiate (1 := (fun v => (∃ n, (N.of_nat n ↦[wm][0%N] #00 ∗ N.of_nat n ↦[wm][1%N] #00 ∗ memory1 ↦[host] (HV_wov (WOV_memoryref (Mk_memidx n))) ∗ byte1 ↦[host] (HV_byte #34) ∗ byte2 ↦[host] (HV_byte #32)))%I)).
    iIntros "!> Hb1".
    by iFrame.
  - (* memory_set 1 *)
    iIntros (v) "H".
    iDestruct "H" as (n) "(Hm1 & Hm2 & Hm & Hb1 & Hb2)".
    iApply (wp_memory_set with "[Hb1 Hm Hm1]"); first by iFrame.
    instantiate (1 := (fun v => (∃ n, (N.of_nat n ↦[wm][0%N] #34 ∗ N.of_nat n ↦[wm][1%N] #00 ∗ memory1 ↦[host] (HV_wov (WOV_memoryref (Mk_memidx n))) ∗ byte1 ↦[host] (HV_byte #34) ∗ byte2 ↦[host] (HV_byte #32)))%I)).
    iIntros "!> (Hb1 & Hm & Hm1)".
    iExists n.
    by iFrame.
  - (* memory_set 2 *)
    iIntros (v) "H".
    iDestruct "H" as (n) "(Hm1 & Hm2 & Hm & Hb1 & Hb2)".
    iApply (wp_memory_set with "[Hb2 Hm Hm2]"); first by iFrame.
    iIntros "!> (Hb2 & Hm & Hm2)".
    iExists n.
    by iFrame.
Qed.
    
