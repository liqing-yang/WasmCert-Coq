From mathcomp Require Import ssreflect ssrbool eqtype seq.

From iris.program_logic Require Import language ectx_language ectxi_language.
From iris.heap_lang Require Export locations.

From Wasm Require Import opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Wasm Require Import opsem.

Module Type Instance_module.
  Parameter the_instance : instance.
End Instance_module.

Definition expr := list administrative_instruction.
Definition val := list value.
Definition state := store_record.
Definition observation := unit. (* TODO: should change when needed *)

(* TODO: should change when needed *)
Definition proph_id := unit.

Definition of_val (v : val) : expr := map (fun v => Basic (EConst v)) v.

Fixpoint to_val (e : expr) : option val :=
  match e with
  | [::] => Some [::]
  | Basic (EConst v) :: e' =>
    match to_val e' with
    | Some v' => Some (v :: v')
    | None => None
    end
  | _ => None
  end.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
move: v.
elim; first done.
move => v0 v H.
by rewrite /= H.
Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof.
Admitted.

Instance of_val_inj : Inj (=) (=) of_val.
Proof.
move => v1 v2 Hv1v2.
admit.
Admitted.

Inductive ectx_item :=
| Ectx_es : list administrative_instruction -> ectx_item.

Fixpoint fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | Ectx_es es => e ++ es
  end.

(* TODO: avoid repetition *)
Inductive head_reduce : store_record -> list value -> list administrative_instruction -> instance -> store_record -> list value -> list administrative_instruction -> Prop :=
  | hr_simple :
      forall e e' s vs i,
        reduce_simple e e' ->
        head_reduce s vs e i s vs e'
  | hr_call :
      forall s vs i j f,
        sfunc s i j = Some f ->
        head_reduce s vs [::Basic (Call j)] i s vs [::Invoke f]
  | hr_call_indirect_success :
      forall s i j cl c vs tf,
        stab s i (Wasm_int.nat_of_uint i32m c) = Some cl ->
        stypes s i j = Some tf ->
        cl_type cl = tf ->
        head_reduce s vs [::Basic (EConst (ConstInt32 c)); Basic (Call_indirect j)] i s vs [::Invoke cl]
  | hr_call_indirect_failure1 :
      forall s i j c cl vs,
        stab s i (Wasm_int.nat_of_uint i32m c) = Some cl ->
        stypes s i j <> Some (cl_type cl) ->
        head_reduce s vs [::Basic (EConst (ConstInt32 c)); Basic (Call_indirect j)] i s vs [::Trap]
  | hr_call_indirect_failure2 :
      forall s i j c vs,
        stab s i (Wasm_int.nat_of_uint i32m c) = None ->
        head_reduce s vs [::Basic (EConst (ConstInt32 c)); Basic (Call_indirect j)] i s vs [::Trap]
  | hr_invoke_native :
      forall cl t1s t2s ts es ves vcs n m k zs vs s i j,
        cl = Func_native j (Tf t1s t2s) ts es ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length ts = k ->
        length t1s = n ->
        length t2s = m ->
        n_zeros ts = zs ->
        head_reduce s vs (ves ++ [::Invoke cl]) i s vs [::Local m j (vcs ++ zs) [::Basic (Block (Tf [::] t2s) es)]]
  | hr_invoke_host_success :
      forall cl f t1s t2s ves vcs m n s s' vcs' vs i,
        cl = Func_host (Tf t1s t2s) f ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length t1s = n ->
        length t2s = m ->
        host_apply s (Tf t1s t2s) f vcs (* FIXME: hs *) = Some (s', vcs') ->
        head_reduce s vs (ves ++ [::Invoke cl]) i s' vs (v_to_e_list vcs')
  | hr_invoke_host_failure :
      forall cl t1s t2s f ves vcs n m s vs i,
        cl = Func_host (Tf t1s t2s) f ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length t1s = n ->
        length t2s = m ->
        head_reduce s vs (ves ++ [::Invoke cl]) i s vs [::Trap]
  | hr_get_local :
      forall vi v vs i j s,
        length vi = j ->
        head_reduce s (vi ++ [::v] ++ vs) [::Basic (Get_local j)] i s (vi ++ [::v] ++ vs) [::Basic (EConst v)]
  | hr_set_local :
      forall vs j v i s vd,
        length vs > j ->
        head_reduce s vs [::Basic (EConst v); Basic (Set_local j)] i s (set_nth vd vs j v) [::]
  | hr_get_global :
      forall s vs j i v,
        sglob_val s i j = Some v ->
        head_reduce s vs [::Basic (Get_global j)] i s vs [::Basic (EConst v)]
  | hr_set_global :
      forall s i j v s' vs,
        supdate_glob s i j v = Some s' ->
        head_reduce s vs [::Basic (EConst v); Basic (Set_global j)] i s' vs [::]
  | hr_load_success :
      forall s i t bs vs k a off m j,
        smem_ind s i = Some j ->
        List.nth_error s.(s_mems) j = Some m ->
        load m (Wasm_int.N_of_uint i32m k) off (t_length t) = Some bs ->
        head_reduce s vs [::Basic (EConst (ConstInt32 k)); Basic (Load t None a off)] i s vs [::Basic (EConst (wasm_deserialise bs t))]
  | hr_load_failure :
      forall s i t vs k a off m j,
        smem_ind s i = Some j ->
        List.nth_error s.(s_mems) j = Some m ->
        load m (Wasm_int.N_of_uint i32m k) off (t_length t) = None ->
        head_reduce s vs [::Basic (EConst (ConstInt32 k)); Basic (Load t None a off)] i s vs [::Trap]
  | hr_load_packed_success :
      forall s i t tp vs k a off m j bs sx,
        smem_ind s i = Some j ->
        List.nth_error s.(s_mems) j = Some m ->
        load_packed sx m (Wasm_int.N_of_uint i32m k) off (tp_length tp) (t_length t) = Some bs ->
        head_reduce s vs [::Basic (EConst (ConstInt32 k)); Basic (Load t (Some (tp, sx)) a off)] i s vs [::Basic (EConst (wasm_deserialise bs t))]
  | hr_load_packed_failure :
      forall s i t tp vs k a off m j sx,
        smem_ind s i = Some j ->
        List.nth_error s.(s_mems) j = Some m ->
        load_packed sx m (Wasm_int.N_of_uint i32m k) off (tp_length tp) (t_length t) = None ->
        head_reduce s vs [::Basic (EConst (ConstInt32 k)); Basic (Load t (Some (tp, sx)) a off)] i s vs [::Trap]
  | hr_store_success :
      forall t v s i j vs mem' k a off m,
        types_agree t v ->
        smem_ind s i = Some j ->
        List.nth_error s.(s_mems) j = Some m ->
        store m (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t) = Some mem' ->
        head_reduce s vs [::Basic (EConst (ConstInt32 k)); Basic (EConst v); Basic (Store t None a off)] i (upd_s_mem s (update_list_at s.(s_mems) j mem')) vs [::]
  | hr_store_failure :
      forall t v s i j m k off a vs,
        types_agree t v ->
        smem_ind s i = Some j ->
        List.nth_error s.(s_mems) j = Some m ->
        store m (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t) = None ->
        head_reduce s vs [::Basic (EConst (ConstInt32 k)); Basic (EConst v); Basic (Store t None a off)] i s vs [::Trap]
  | hr_store_packed_success :
      forall t v s i j m k off a vs mem' tp,
        types_agree t v ->
        smem_ind s i = Some j ->
        List.nth_error s.(s_mems) j = Some m ->
        store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp) = Some mem' ->
        head_reduce s vs [::Basic (EConst (ConstInt32 k)); Basic (EConst v); Basic (Store t (Some tp) a off)] i (upd_s_mem s (update_list_at s.(s_mems) j mem')) vs [::]
  | hr_store_packed_failure :
      forall t v s i j m k off a vs tp,
        types_agree t v ->
        smem_ind s i = Some j ->
        List.nth_error s.(s_mems) j = Some m ->
        store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp) = None ->
        head_reduce s vs [::Basic (EConst (ConstInt32 k)); Basic (EConst v); Basic (Store t (Some tp) a off)] i s vs [::Trap]
  | hr_current_memory :
      forall i j m n s vs,
        smem_ind s i = Some j ->
        List.nth_error s.(s_mems) j = Some m ->
        mem_size m = n ->
        head_reduce s vs [::Basic (Current_memory)] i s vs [::Basic (EConst (ConstInt32 (Wasm_int.int_of_Z i32m (Z.of_N n))))]
  | hr_grow_memory_success :
      forall s i j m n mem' vs c,
        smem_ind s i = Some j ->
        List.nth_error s.(s_mems) j = Some m ->
        mem_size m = n ->
        mem_grow m (Wasm_int.N_of_uint i32m c) = Some mem' ->
        head_reduce s vs [::Basic (EConst (ConstInt32 c)); Basic Grow_memory] i (upd_s_mem s (update_list_at s.(s_mems) j mem')) vs [::Basic (EConst (ConstInt32 (Wasm_int.int_of_Z i32m (Z.of_N n))))]
  | hr_grow_memory_failure :
      forall i j m n s vs c,
        smem_ind s i = Some j ->
        List.nth_error s.(s_mems) j = Some m ->
        mem_size m = n ->
        head_reduce s vs [::Basic (EConst (ConstInt32 c)); Basic Grow_memory] i s vs [::Basic (EConst (ConstInt32 int32_minus_one))]
(* TODO: should all of this case be nuked?
        | hr_label :
      forall s vs es les i s' vs' es' les' k lh,
        head_reduce s vs es i s' vs' es' ->
        lfilled k lh es les ->
        lfilled k lh es' les' ->
        head_reduce s vs les i s' vs' les'
        *)
  | hr_local :
      forall s vs es i s' vs' es' n v0s j,
        head_reduce s vs es i s' vs' es' ->
        head_reduce s v0s [::Local n i vs es] j s' v0s [::Local n i vs' es'].

Definition head_reduce_tuple (i : instance) s_vs_es s'_vs'_es' : Prop :=
  let '(s, vs, es) := s_vs_es in
  let '(s', vs', es') := s'_vs'_es' in
  head_reduce s vs es i s' vs' es'.


Module wasm (The_Inst : Instance_module).

Definition head_step (e : expr) (s : state) (os : list observation) (e' : expr) (s' : state) (es' : list expr) : Prop :=
  head_reduce_tuple The_Inst.the_instance (s, nil, e) (s', nil, e') /\
  os = nil /\
  es' = nil.

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof.
move: Ki => [es] /= x y.
apply/app_inv_tail.
Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof.
move: Ki => [es].
move => /= [v H].
admit.
Admitted.

Lemma val_head_stuck e1 σ1 κ e2 σ2 efs :
  head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof.
Admitted.

Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 efs :
  head_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof.
Admitted.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
Admitted.

Lemma wasm_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
split.
- apply to_of_val.
- apply of_to_val.
- apply val_head_stuck.
- apply fill_item_inj.
- apply fill_item_val.
- apply fill_item_no_val_inj.
- apply head_ctx_step_val.
Qed.

(** Language *)
Canonical Structure wasm_ectxi_lang := EctxiLanguage wasm_mixin.
Canonical Structure wasm_ectx_lang := EctxLanguageOfEctxi wasm_ectxi_lang.
Canonical Structure wasm_lang := LanguageOfEctx wasm_ectx_lang.

(* TODO: move this to separate file *)
From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap proph_map.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.


From iris.heap_lang Require Import locations.

Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_gen_heapG :> gen_heapG loc (option val) Σ;
  heapG_proph_mapG :> proph_mapG proph_id (val * val) Σ;
}.

From Wasm Require Export datatypes.

(* TODO: this is a dummy definition that only takes globals into account *)
Definition pmap_of_store_record (σ : store_record) : pmap.Pmap (option val).
refine (list_extra.fold_lefti _ σ.(s_globals) _).
{ move => i pm glob.
  apply: pmap.Pmerge.
  apply: (fun x y =>
    match (x, y) with
    | (None, None) => None
    | (Some xx, _) => Some xx
    | (_, Some yy) => Some yy
    end).
  apply: pm.
  pose v := Some (cons glob.(g_val) nil).
  refine (@pmap.PMap _ (@pmap.Psingleton_raw _ (Pos.of_succ_nat i) v) _).
  apply: pmap.Psingleton_wf.
}
{ apply: pmap.Pempty. }
Defined.

Definition gmap_of_store_record (σ : store_record) : gmap loc (option val) :=
  list_extra.fold_lefti
    (λ (i : nat) (pm : gmap loc (option val)) (glob : global),
       map_insert {| loc_car := Z.of_nat i |} (Some [g_val glob]) pm)
    (s_globals σ) ∅.

Instance heapG_irisG `{!heapG Σ} : irisG wasm_lang Σ := {
  iris_invG := heapG_invG;
  state_interp σ κs _ :=
    gen_heap_ctx (gmap_of_store_record σ);
  fork_post z := True%I;
}.

Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=option val) l q (Some v%V))
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.

  Ltac inv_head_step :=
    repeat match goal with
    | _ => progress simplify_map_eq/= (* simplify memory stuff *)
    | H : to_val _ = Some _ |- _ => apply of_to_val in H
    | H : head_step ?e _ _ _ _ _ |- _ =>
       try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
       and can thus better be avoided. *)
       inversion H; subst; clear H
    end.
  

Definition locof (n : nat) := {| loc_car := (Z.of_nat n) |}.

Section lifting.
Context `{!heapG Σ}.
Implicit Types σ : state.

Lemma twp_load s E imm q v :
  [[{ (locof imm) ↦{q} v }]] [Basic (Get_local imm)] @ s; E [[{ RET v; (locof imm) ↦{q} v }]].
Proof.
  iIntros (Φ) "Hl HΦ". iApply twp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 κs n) "Hσ !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit.
  inv_head_step.
  admit.
  iIntros (κ v2 σ2 efs Hstep); inv_head_step.
  move: H1 => [H1 H2].
  iModIntro; iSplit=> //; iSplit=> //.
  iSplitR.
  admit.
  unfold from_option.
  inversion H0 => {H0}; subst.
  { inversion H3 => {H3}; subst.
    { exfalso.
      admit. }
    { exfalso.
      admit. }
    { simpl.
      clear H0.
      apply lfilled_Ind_Equivalent in H1.
      inversion H1; subst.
      { admit. }
    }
  }
  { simpl.
    exfalso.
    move: H3.
    rewrite app_singleton => H3.
    move: H3 => [[H3 H4]|[H3 H4]]; discriminate. }
  { admit. }
  { admit. }
  { exfalso.
  move: H3.
  rewrite app_nil => [[_ H4]].
  discriminate. }
Admitted.

Lemma twp_wp_step s E e P Φ :
  TCEq (to_val e) None →
  ▷ P -∗
  WP e @ s; E [{ v, P ={E}=∗ Φ v }] -∗ WP e @ s; E {{ Φ }}.
Proof.
  iIntros (?) "HP Hwp".
  iApply (wp_step_fupd _ _ E _ P with "[HP]"); [auto..|].
  { by inversion H; subst. }
  by iApply twp_wp.
Qed.

Lemma wp_load s E imm q v :
  {{{ ▷ locof imm ↦{q} v }}} [Basic (Get_local imm)] @ s; E {{{ RET v; locof imm ↦{q} v }}}.
Proof.
  iIntros (Φ) ">H HΦ". iApply (twp_wp_step with "HΦ").
  iApply (twp_load with "H"); [auto..|]; iIntros "H HΦ". by iApply "HΦ".
Qed.

End lifting.

End wasm.



