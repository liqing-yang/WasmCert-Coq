(** Iris bindings **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrbool eqtype seq.

From iris.program_logic Require Import language.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import operations opsem interpreter.


Section Host.

Variable host_function : eqType.

Definition expr := host_expr.
Definition val := host_value.
Definition state : Type := host_state * store_record * (list host_value).
Definition observation := unit. (* TODO: maybe change? *)

Definition of_val (v : val) : expr := HE_value v.

Fixpoint to_val (e : expr) : option val :=
  match e with
  | HE_value v => Some v
  | _ => None
  end.

Definition prim_step (e : expr) (s : state) (os : list observation) (e' : expr) (s' : state) (fork_es' : list expr) : Prop :=
  let '(vars, ws, locs) := s in
  let '(vars', ws', locs') := s' in
    host_reduce vars ws locs e vars' ws' locs' e' /\ os = [] /\ fork_es' = [].

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  by [].
Qed.

(*
Definition is_none_or {A : Type} (p : A -> bool) (x : option A) : bool :=
  match x with
  | None => true
  | Some y => p y
  end.

Lemma to_val_cons_is_none_or_cons : forall e0 e r,
  to_val (e0 :: e)%SEQ = r -> is_none_or (fun l => l != []) r.
Proof.
  move => e0 e.
  rewrite /=.
  case.
  { rewrite /=.
    case: e0 => //=.
    case => //=.
    move => v0 v.
    case: (to_val e) => //=.
    move => a H.
    by case: v H. }
  { by case: e0. }
Qed.
*)
Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
  destruct e => //=.
  move => H. by inversion H.
Qed.

Lemma val_head_stuck : forall e1 s1 κ e2 s2 efs,
  prim_step e1 s1 κ e2 s2 efs →
  to_val e1 = None.
Proof.
(*
  rewrite /prim_step => e1 [hs1 σ1] κ e2 [hs2 σ2] efs.
  case_eq (split_vals_e e1) => vs es H.
  case_eq (split_vals_e e2) => vs' es' _ [i [Hred _]].
  move: vs vs' es' H Hred.
  elim: es.
  { move => vs vs' es' _ Hred.
    exfalso.
    apply: reduce_not_nil.
    apply: Hred.
    done. }
  { move => e es _ vs vs' _ H1 _ {e2 efs}.
    apply: splits_vals_e_to_val_hd.
    apply: H1. }*)
Admitted.

Inductive ectx_item := (* what items do we need??? *)
  (* Host/Wasm frame. But do we need the Label case in Wasm as well?? *)
| Ectx_setglobal : id -> ectx_item
| Ectx_seq : expr -> ectx_item.

Fixpoint fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | Ectx_setglobal id => HE_setglobal id e
  | Ectx_seq e' => HE_seq e' e
  end.

(* Need to be in Ectxilanguagemixin. But what is the diff between head_step and prim_step? *)
Lemma wasm_mixin : LanguageMixin of_val to_val prim_step.
Proof. split; eauto using to_of_val, of_to_val, val_head_stuck. Qed.

(*
Lemma wasm_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
*)  

End Host.

