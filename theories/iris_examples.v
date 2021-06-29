
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

Open Scope string_scope.
Open Scope SEQ.

Context `{!hsG Σ, !locG Σ, !wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ}.

Notation "A ;;; B" := (HE_seq A B) (at level 2).
Notation "A ::= B" := (HE_setglobal A B) (at level 5).

Section Program_SetMem42.

Variable memory1 byte1 byte2 : N.

Definition Program_SetMem42 :=
  (memory1 ::= (HE_wasm_memory_create 2 2 #00));;;
  (byte1 ::= (HE_value (HV_byte #34)));;;
  (byte2 ::= (HE_value (HV_byte #32)));;;
  (HE_wasm_memory_set memory1 0%N byte1);;;
  (HE_wasm_memory_set memory1 1%N byte2).


(*
  Our host language doesn't have any instruction that allocates new global variables
  (setglobal only modifies), so we assume a set of pre-allocated variables initialised to zero.
  

  Note that it's non-trivial to support the allocation of new global variables at a specific
  address (id): this would require the negative knowledge that a particular id is NOT allocated,
  which doesn't seem to be possible in Iris?
*)
Lemma Program_SetMem42_spec s E:
  memory1 ↦[host] wasm_zero -∗
  byte1 ↦[host] wasm_zero -∗
  byte2 ↦[host] wasm_zero -∗       
  (WP Program_SetMem42 @ s; E {{ _, ∃ n, memory1 ↦[host] HV_wov (WOV_memoryref (Mk_memidx n)) ∗
                                         byte1 ↦[host] HV_byte #34 ∗
                                         byte2 ↦[host] HV_byte #32 ∗
                                         N.of_nat n ↦[wm][ 0%N ] #34 ∗
                                         N.of_nat n ↦[wm][ 1%N ] #32 }})%I.
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
    
End Program_SetMem42.

Section Program_Funcs.

Variable instance1 instance2 : N.
Variable table1 : N.
Variable memory1 memory2 : N.
Variable store11 store42 f1 dolt : N.
Variable store11_func store42_func dolt_func : N.

Definition Program_Funcs :=
  (instance1 ::= (HE_new_rec [::("store42", store42)]));;;
  (instance2 ::= (HE_new_rec [::("store11", store11); ("dolt", dolt)]));;;
  (store42_func ::= (HE_get_field instance1 "store42"));;;
  (store11_func ::= (HE_get_field instance2 "store11"));;;
  (dolt_func ::= (HE_get_field instance2 "dolt"));;;
  (HE_call store42_func [::]);;;
  (HE_call store11_func [::]);;;
  (HE_call dolt_func [::])
.

Definition wasm_zero := HV_wasm_value (VAL_int32 (Wasm_int.int_zero i32m)).

Definition wasm_i32_of_nat (n: nat) :=
  VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n)).


Definition store11_cl := FC_func_native empty_instance (Tf [::] [::]) [::] [::BI_const (wasm_i32_of_nat 0); BI_const (wasm_i32_of_nat 11); BI_store T_i32 None 0%N 0%N].

Definition store42_cl := FC_func_native empty_instance (Tf [::] [::]) [::] [::BI_const (wasm_i32_of_nat 0); BI_const (wasm_i32_of_nat 42); BI_store T_i32 None 0%N 0%N].

Definition f1_cl := FC_func_native empty_instance (Tf [::] [::]) [::] [::BI_const (wasm_i32_of_nat 0); BI_load T_i32 None 0%N 0%N].

Definition dolt_cl := FC_func_native empty_instance (Tf [::] [::]) [::] [::BI_const (wasm_i32_of_nat 0); BI_call_indirect 0].

Lemma Program_Funcs_spec s E v:
  {{{ memory1 ↦[host] HV_wov (WOV_memoryref (Mk_memidx 0)) ∗
      memory2 ↦[host] HV_wov (WOV_memoryref (Mk_memidx 1)) ∗
      table1 ↦[host] HV_wov (WOV_tableref (Mk_tableidx 0)) ∗
      store11 ↦[host] HV_wov (WOV_funcref (Mk_funcidx 0)) ∗
      store42 ↦[host] HV_wov (WOV_funcref (Mk_funcidx 1)) ∗
      f1 ↦[host] HV_wov (WOV_funcref (Mk_funcidx 2)) ∗
      dolt ↦[host] HV_wov (WOV_funcref (Mk_funcidx 3)) ∗
      instance1 ↦[host] wasm_zero ∗
      instance2 ↦[host] wasm_zero ∗
      0%N ↦[wf] store11_cl ∗
      1%N ↦[wf] store42_cl ∗
      2%N ↦[wf] f1_cl ∗
      3%N ↦[wf] dolt_cl ∗
      0%N ↦[wt][0%N] (Some 2)
  }}}
    Program_Funcs @ s; E 
  {{{ RET v; True }}}.
Proof.
  iIntros (Φ) "(Hmref1 & Hmref2 & Htref1 & Hstore11 & Hstore42 & Hf1 & Hdolt & Hinst1 & Hinst2 & Hwf0 & Hwf1 & Hwf2 & Hwf3 & Ht00)".
  iIntros "HΦ".
  iApply wp_seq; iSplitL.
  iApply wp_seq; iSplitL.
  iApply wp_seq; iSplitL.
  iApply wp_seq; iSplitL.
  iApply wp_seq; iSplitL.
  iApply wp_seq; iSplitL.
  iApply wp_seq; iSplitL "Hinst1 Hstore42".
  - (* setglobal of instance1 *)
    iApply wp_setglobal_reduce; iSplitL "Hstore42".
    + iApply (wp_new_rec with "[Hstore42]") => //=.
      * by instantiate (1 := [("store42", HV_wov (WOV_funcref (Mk_funcidx 1)))]).
      * iSplit => //.
        iExists (HV_wov (WOV_funcref (Mk_funcidx 1))).
        by iSplit.
      * iIntros "!> HP".
        iSplit => //.
        instantiate (1 := (fun v => (⌜ v = HV_record [("store42", HV_wov (WOV_funcref (Mk_funcidx 1)))] ⌝ ∗ store42 ↦[host]HV_wov (WOV_funcref (Mk_funcidx 1))))%I).
        simpl.
        iSplit => //.
        iDestruct "HP" as "(H & _)".
        iDestruct "H" as (v' Hvalue) "H".
        inversion Hvalue; subst; clear Hvalue.
        by iAssumption.
    + iIntros (v0) "(_ & %Hv0 & HP)".
      instantiate (1 := (fun _ => (instance1 ↦[host] HV_record [("store42", HV_wov (WOV_funcref (Mk_funcidx 1)))])%I)).
      subst.
      iApply (wp_setglobal_value with "Hinst1") => //.
      by iIntros "!> H".
  - (* setglobal of instance2 *)
    admit.
  - (* setglobal of store42_func *)
    admit.
  - (* setglobal of store11_func *)
    admit.
  - (* setglobal of dolt_func *)
    admit.
  - (* HE_call of store42_func *)
    admit.
  - (* HE_call of store11_func *)
    admit.
  - (* HE_call of dolt_func *)
    admit.
Admitted.
