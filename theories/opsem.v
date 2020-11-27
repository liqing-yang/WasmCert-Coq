(** Wasm operational semantics **)
(** The interpreter in the [interpreter] module is an executable version of this operational semantics. **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Coq Require Import NArith.BinNat ZArith.BinInt.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import operations binary_format_parser.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive reduce_simple : seq administrative_instruction -> seq administrative_instruction -> Prop :=

(** unop **)
  | rs_unop : forall v op t,
    reduce_simple [::AI_basic (BI_const v); AI_basic (BI_unop t op)] [::AI_basic (BI_const (@app_unop op v))]
                   
(** binop **)
  | rs_binop_success : forall v1 v2 v op t,
    app_binop op v1 v2 = Some v ->
    reduce_simple [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] [::AI_basic (BI_const v)]
  | rs_binop_failure : forall v1 v2 op t,
    app_binop op v1 v2 = None ->
    reduce_simple [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] [::AI_trap]
                  
  (** testops **)
  | rs_testop_i32 :
    forall c testop,
    reduce_simple [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_testop T_i32 testop)] [::AI_basic (BI_const (VAL_int32 (wasm_bool (@app_testop_i i32t testop c))))]
  | rs_testop_i64 :
    forall c testop,
    reduce_simple [::AI_basic (BI_const (VAL_int64 c)); AI_basic (BI_testop T_i64 testop)] [::AI_basic (BI_const (VAL_int32 (wasm_bool (@app_testop_i i64t testop c))))]

  (** relops **)
  | rs_relop: forall v1 v2 t op,
    reduce_simple [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] [::AI_basic (BI_const (VAL_int32 (wasm_bool (app_relop op v1 v2))))]
                    
  (** convert and reinterpret **)
  | rs_convert_success :
    forall t1 t2 v v' sx,
    types_agree t1 v ->
    cvt t2 sx v = Some v' ->
    reduce_simple [::AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] [::AI_basic (BI_const v')]
  | rs_convert_failure :
    forall t1 t2 v sx,
    types_agree t1 v ->
    cvt t2 sx v = None ->
    reduce_simple [::AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] [::AI_trap]
  | rs_reinterpret :
    forall t1 t2 v,
    types_agree t1 v ->
    reduce_simple [::AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] [::AI_basic (BI_const (wasm_deserialise (bits v) t2))]

  (** control-flow operations **)
  | rs_unreachable :
    reduce_simple [::AI_basic BI_unreachable] [::AI_trap]
  | rs_nop :
    reduce_simple [::AI_basic BI_nop] [::]
  | rs_drop :
    forall v,
    reduce_simple [::AI_basic (BI_const v); AI_basic BI_drop] [::]
  | rs_select_false :
    forall n v1 v2,
    n = Wasm_int.int_zero i32m ->
    reduce_simple [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select] [::AI_basic (BI_const v2)]
  | rs_select_true :
    forall n v1 v2,
    n <> Wasm_int.int_zero i32m ->
    reduce_simple [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select] [::AI_basic (BI_const v1)]
  | rs_block :
      forall vs es n m t1s t2s,
        const_list vs ->
        length vs = n ->
        length t1s = n ->
        length t2s = m ->
        reduce_simple (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) [::AI_label m [::] (vs ++ to_e_list es)]
  | rs_loop :
      forall vs es n m t1s t2s,
        const_list vs ->
        length vs = n ->
        length t1s = n ->
        length t2s = m ->
        reduce_simple (vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)]) [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)]
  | rs_if_false :
      forall n tf e1s e2s,
        n = Wasm_int.int_zero i32m ->
        reduce_simple ([::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)]) [::AI_basic (BI_block tf e2s)]
  | rs_if_true :
      forall n tf e1s e2s,
        n <> Wasm_int.int_zero i32m ->
        reduce_simple ([::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)]) [::AI_basic (BI_block tf e1s)]
  | rs_label_const :
      forall n es vs,
        const_list vs ->
        reduce_simple [::AI_label n es vs] vs
  | rs_label_trap :
      forall n es,
        reduce_simple [::AI_label n es [::AI_trap]] [::AI_trap]
  | rs_br :
      forall n vs es i LI lh,
        const_list vs ->
        length vs = n ->
        lfilled i lh (vs ++ [::AI_basic (BI_br i)]) LI ->
        reduce_simple [::AI_label n es LI] (vs ++ es)
  | rs_br_if_false :
      forall n i,
        n = Wasm_int.int_zero i32m ->
        reduce_simple [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] [::]
  | rs_br_if_true :
      forall n i,
        n <> Wasm_int.int_zero i32m ->
        reduce_simple [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] [::AI_basic (BI_br i)]
  | rs_br_table : (* ??? *)
      forall iss c i j,
        length iss > Wasm_int.nat_of_uint i32m c ->
        List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
        reduce_simple [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] [::AI_basic (BI_br j)]
  | rs_br_table_length :
      forall iss c i,
        length iss <= (Wasm_int.nat_of_uint i32m c) ->
        reduce_simple [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] [::AI_basic (BI_br i)]
  | rs_local_const :
      forall es n f,
        const_list es ->
        length es = n ->
        reduce_simple [::AI_local n f es] es
  | rs_local_trap :
      forall n f,
        reduce_simple [::AI_local n f [::AI_trap]] [::AI_trap]
  | rs_return : (* ??? *)
      forall n i vs es lh f,
        const_list vs ->
        length vs = n ->
        lfilled i lh (vs ++ [::AI_basic BI_return]) es ->
        reduce_simple [::AI_local n f es] vs
  | rs_tee_local :
      forall i v,
        is_const v ->
        reduce_simple [::v; AI_basic (BI_tee_local i)] [::v; v; AI_basic (BI_set_local i)]
  | rs_trap :
      forall es lh,
        es <> [::AI_trap] ->
        lfilled 0 lh [::AI_trap] es ->
        reduce_simple es [::AI_trap]
.

(*
(* TODO: I think this approach here is better, albeit different from the doc - R *)
Record host_state := {
  hs_varmap : id -> option host_value;
  hs_funcs : list host_expr;
}.
 *)

Definition host_state : Type := id -> option host_value.

Definition lookup_host_vars (vcs : list i32) hs : option (list host_value) :=
  list_extra.those
    (List.map
      (fun i => hs i)
      vcs).

Definition lookup_host_vars_as_i32s vcs hs : option (list host_value) :=
  list_extra.those
    (List.map
      (fun x =>
        match x with
        | VAL_int32 i =>
          hs i
        | _ => None
        end)
      vcs).

(* TODO: refactor these into datatypes/operations.v accordingly. *)
Definition empty_instance := Build_instance [::] [::] [::] [::] [::].

Definition empty_frame := Build_frame [::] empty_instance.

Fixpoint is_byte_list (hvs: list host_value) : bool :=
  match hvs with
  | [::] => true
  | hv :: hvs' => if hv is HV_byte _ then is_byte_list hvs' else false
  end.

(* Due to host's ability to invoke wasm functions and wasm's ability to invoke host
     functions, the opsem is necessarily mutually recursive. *)
(* TODO: add all the cases *)

Inductive host_reduce : host_state -> store_record -> list host_value -> host_expr ->
                        host_state -> store_record -> list host_value -> host_expr -> Prop :=
  (* TODO: basic exprs -- arith ops, list ops left *)
  | hr_getglobal:
    forall hs s hvs id hv,
      hs id = Some hv ->
      host_reduce hs s hvs (HE_getglobal id) hs s hvs (HE_value hv)
  | hr_setglobal_reduce:
    forall hs s hvs id e hs' s' hvs' e',
      host_reduce hs s hvs e hs' s' hvs' e' ->
      host_reduce hs s hvs (HE_setglobal id e) hs' s' hvs' (HE_setglobal id e')
  | hr_setglobal_value:
    forall hs s hvs id hv hs',
      hs' = (fun idx => if idx == id then (Some hv) else (hs idx)) ->
      host_reduce hs s hvs (HE_setglobal id (HE_value hv)) hs' s hvs (HE_skip)
  | hr_getlocal:
    forall hs s hvs n hv,
      List.nth_error hvs (nat_of_N n) = Some hv ->
      host_reduce hs s hvs (HE_getlocal n) hs s hvs (HE_value hv)
  | hr_setlocal:
    forall hs s hvs n id hvs' hv hvd,
      hs id = Some hv ->
      hvs' = set_nth hvd hvs (nat_of_N n) hv ->
      host_reduce hs s hvs (HE_setlocal n id) hs s hvs' (HE_skip)
  | hr_if_true: (* TODO: add the case for invalid id, ie. hs(id) = None *)
    forall hs s hvs id e1 e2 hv,
      hs id = Some hv ->
      hv <> HV_wasm_value (VAL_int32 (Wasm_int.int_zero i32m)) ->
      host_reduce hs s hvs (HE_if id e1 e2) hs s hvs e1
  | hr_if_false: 
    forall hs s hvs id e1 e2 hv,
      hs id = Some hv ->
      hv = HV_wasm_value (VAL_int32 (Wasm_int.int_zero i32m)) ->
      host_reduce hs s hvs (HE_if id e1 e2) hs s hvs e2
  | hr_while:
    forall hs s hvs id e,
      host_reduce hs s hvs (HE_while id e) hs s hvs (HE_if id (HE_seq e (HE_while id e)) HE_skip)
  (* TODO: record exprs *)
  (* function exprs *)
  | hr_new_host_func:
    forall hs s hvs htf hvsn e s' n,
      s' = {|s_funcs := s.(s_funcs) ++ [::FC_func_host htf hvsn e]; s_tables := s.(s_tables); s_mems := s.(s_mems); s_globals := s.(s_globals) |} ->
      n = length s.(s_funcs) ->
      host_reduce hs s hvs (HE_new_host_func htf (N_of_nat hvsn) e) hs s' hvs (HE_value (HV_wov (WOV_funcref (Mk_funcidx n))))
  | hr_call_wasm:
    forall hs s ids cl id i j vts bes tf vs tn tm vars hvs,
      hs id = Some (HV_wov (WOV_funcref (Mk_funcidx i))) ->
      List.nth_error s.(s_funcs) i = Some cl ->
      cl = FC_func_native j tf vts bes ->
      tf = Tf tn tm ->
      lookup_host_vars ids hs = Some vars ->
      list_host_value_to_wasm vars = Some vs ->
      tn = map typeof vs ->
      host_reduce hs s hvs (HE_call id ids) hs s hvs (HE_wasm_frame ((v_to_e_list vs) ++ [::AI_invoke i]))
  (* TODO: wasm state exprs *)
  (* wasm module expr *)
  | hr_call_host:
    forall hs s ids cl id i n e htf vs htn htm vars hvs,
      hs id = Some (HV_wov (WOV_funcref (Mk_funcidx i))) ->
      List.nth_error s.(s_funcs) i = Some cl ->
      cl = FC_func_host htf n e ->
      htf = HTf htn htm ->
      lookup_host_vars ids hs = Some vars ->
      list_host_typeof vars htn ->
      host_reduce hs s hvs (HE_call id ids) hs s hvs (HE_wasm_frame ((v_to_e_list vs) ++ [::AI_invoke i]))
  | hr_compile:
    forall hs s hvs id mo hbytes,
      hs id = Some (HV_bytelist hbytes) ->
      run_parse_module (map byte_of_compcert_byte hbytes) = Some mo -> (* Check: is this correct? *)
      host_reduce hs s hvs (HE_compile id) hs s hvs (HE_value (HV_module mo))
  (* TODO: our current instantiation seems to instantiate to itree -- how do we 
       incorporate it here?
  | hr_instantiate:
      idm = HV_module mo ->
      idr = HV_record r ->
      host_reduce hs s hvs (HE_instantiate idm idr) hs s hvs *)
  (* miscellaneous *)
  | hr_seq_skip:
    forall hs s hvs e,
      host_reduce hs s hvs (HE_seq HE_skip e) hs s hvs e
  | hr_seq_fst:
    forall hs s hvs e1 e2 hs' s' hvs' e1',
      host_reduce hs s hvs e1 hs' s' hvs' e1' ->
      host_reduce hs s hvs (HE_seq e1 e2) hs' s' hvs' (HE_seq e1' e2)
  | hr_seq_snd:
    forall hs s hvs v e hs' s' hvs' e',
      host_reduce hs s hvs e hs' s' hvs' e' ->
      host_reduce hs s hvs (HE_seq (HE_value v) e) hs' s' hvs' (HE_seq (HE_value v) e')
  | hr_wasm_step: forall hs s s' hvs we we',
      reduce hs s empty_frame we hs s empty_frame we' ->
      host_reduce hs s hvs (HE_wasm_frame we) hs s' hvs (HE_wasm_frame we')
      
                  
   

(* TODO: needs all the host_expr reduction steps: compile, instantiate, etc. *)
(* TODO: needs restructuring to make sense *)
with reduce : host_state -> store_record -> frame -> list administrative_instruction ->
                   host_state -> store_record -> frame -> list administrative_instruction -> Prop :=
  | r_simple :
      forall e e' s f hs,
        reduce_simple e e' ->
        reduce hs s f e hs s f e'

  (** calling operations **)
  | r_call :
      forall s f i a hs,
        List.nth_error f.(f_inst).(inst_funcs) i = Some a ->
        reduce hs s f [::AI_basic (BI_call i)] hs s f [::AI_invoke a]
  | r_call_indirect_success :
      forall s f i a cl tf c hs,
        stab_addr s f (Wasm_int.nat_of_uint i32m c) = Some a ->
        List.nth_error s.(s_funcs) a = Some cl ->
        cl_type cl = Some tf ->
        stypes s f.(f_inst) i = Some tf ->
        reduce hs s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] hs s f [::AI_invoke a]
  | r_call_indirect_failure1 :
      forall s f i a cl tf c hs,
        stab_addr s f (Wasm_int.nat_of_uint i32m c) = Some a ->
        List.nth_error s.(s_funcs) a = Some cl ->
        cl_type cl = Some tf ->
        stypes s f.(f_inst) i <> Some tf ->
        reduce hs s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] hs s f [::AI_trap]
  | r_call_indirect_failure2 :
      forall s f i c hs,
        stab_addr s f (Wasm_int.nat_of_uint i32m c) = None ->
        reduce hs s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] hs s f [::AI_trap]
  | r_invoke_native :
      forall a cl t1s t2s ts es ves vcs n m k zs s f f' i hs,
        List.nth_error s.(s_funcs) a = Some cl ->
        cl = FC_func_native i (Tf t1s t2s) ts es ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length ts = k ->
        length t1s = n ->
        length t2s = m ->
        n_zeros ts = zs ->
        f'.(f_inst) = i ->
        f'.(f_locs) = vcs ++ zs ->
        reduce hs s f (ves ++ [::AI_invoke a]) hs s f [::AI_local m f' [::AI_basic (BI_block (Tf [::] t2s) es)]]
  | r_invoke_host :
    (* TODO: check *)
    (* TODO: check - R *)  
    forall a cl e htf t1s t2s ves vcs m n s s' f hs hs' vs,
      List.nth_error s.(s_funcs) a = Some cl ->
      cl = FC_func_host htf n e ->
      host_function_type_to_wasm htf = Some (Tf t1s t2s) ->
      ves = v_to_e_list vcs ->
      length vcs = n ->
      length t1s = n ->
      length t2s = m ->
      Some vs = lookup_host_vars_as_i32s vcs hs ->
      reduce hs s f (ves ++ [::AI_invoke a]) hs' s' f [::AI_host_frame t1s vs e]

  | r_host_step :
    (* TODO: check *)
    forall hs s (f : frame) ts vs e hs' s' vs' e',
      host_reduce hs s vs e hs' s' vs' e' ->
        reduce hs s f [::AI_host_frame ts vs e] hs' s' f [::AI_host_frame ts vs' e']
  (* Don't think we should deal with these here tbh, probably should be in host_reduce *)
  (* Also, does the host_frame and wasm_frame really cancel each other? Looks weird..*)
             (*
  | r_host_call_native :
    (* TODO: check *)
    forall hs s f vts vs bes,
      List.nth_error f.(s_funcs) idx = Some cl ->
      cl = FC_func_native i tf vs bes ->
      ves = v_to_e_list vs ->
      reduce hs s f [::AI_host_frame vts vs (HE_call id ids)] hs s f [::AI_basic (BI_block (Tf [::] t2s) bes)]

  | r_host_call_host :
    (* TODO: check *)
    reduce hs s f [::AI_host_frame vts vs (HE_call id ids)] [::AI_host_frame vts vs e]
*)
  | r_host_return :
    (* TODO: check *)
    forall hs s f ts vs ids vs' vs'',
    Some vs' = lookup_host_vars ids hs ->
    Some vs'' = list_extra.those (List.map (fun x => match x with | HV_wasm_value v => Some v | _ => None end) vs') ->
    reduce hs s f [::AI_host_frame ts vs (HE_return ids)] hs s f (v_to_e_list vs'')
(*  
  | r_host_new_host_func :
    (* TODO: check *)
    forall hs s f ts vs tf n e idx idx_h hs' s',
    idx = List.length s.(s_funcs) ->
    idx_h = List.length hs.(hs_funcs) ->
    hs' = {| hs_varmap := hs.(hs_varmap); hs_funcs := hs.(hs_funcs) ++ [::e] |} ->
    s' = {| s_funcs := s.(s_funcs) ++ [::(FC_func_host tf (Mk_funcidx idx_h))]; s_tables := s.(s_tables); s_mems := s.(s_mems); s_globals := s.(s_globals) |} ->
    reduce hs s f [::AI_host_frame ts vs (HE_new_host_func tf n e)]
      hs' s' f [::AI_host_frame ts vs (HE_value (HV_wov (WOV_funcref (Mk_funcidx idx_h))))]
*)
  (** get, set, load, and store operations **)
  | r_get_local :
      forall f v j s hs,
        List.nth_error f.(f_locs) j = Some v ->
        reduce hs s f [::AI_basic (BI_get_local j)] hs s f [::AI_basic (BI_const v)]
  | r_set_local :
      forall f f' i v s vd hs,
        f'.(f_inst) = f.(f_inst) ->
        f'.(f_locs) = set_nth vd f.(f_locs) i v ->
        reduce hs s f [::AI_basic (BI_const v); AI_basic (BI_set_local i)] hs s f' [::]
  | r_get_global :
      forall s f i v hs,
        sglob_val s f.(f_inst) i = Some v ->
        reduce hs s f [::AI_basic (BI_get_global i)] hs s f [::AI_basic (BI_const v)]
  | r_set_global :
      forall s f i v s' hs,
        supdate_glob s f.(f_inst) i v = Some s' ->
        reduce hs s f [::AI_basic (BI_const v); AI_basic (BI_set_global i)] hs s' f [::]
  | r_load_success :
    forall s i f t bs k a off m hs,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load m (Wasm_int.N_of_uint i32m k) off (t_length t) = Some bs ->
      reduce hs s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load t None a off)] hs s f [::AI_basic (BI_const (wasm_deserialise bs t))]
  | r_load_failure :
    forall s i f t k a off m hs,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load m (Wasm_int.N_of_uint i32m k) off (t_length t) = None ->
      reduce hs s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load t None a off)] hs s f [::AI_trap]
  | r_load_packed_success :
    forall s i f t tp k a off m bs sx hs,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load_packed sx m (Wasm_int.N_of_uint i32m k) off (tp_length tp) (t_length t) = Some bs ->
      reduce hs s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load t (Some (tp, sx)) a off)] hs s f [::AI_basic (BI_const (wasm_deserialise bs t))]
  | r_load_packed_failure :
    forall s i f t tp k a off m sx hs,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load_packed sx m (Wasm_int.N_of_uint i32m k) off (tp_length tp) (t_length t) = None ->
      reduce hs s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load t (Some (tp, sx)) a off)] hs s f [::AI_trap]
  | r_store_success :
    forall t v s i f mem' k a off m hs,
      types_agree t v ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store m (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t) = Some mem' ->
      reduce hs s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store t None a off)] hs (upd_s_mem s (update_list_at s.(s_mems) i mem')) f [::]
  | r_store_failure :
    forall t v s i f m k off a hs,
      types_agree t v ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store m (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t) = None ->
      reduce hs s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store t None a off)] hs s f [::AI_trap]
  | r_store_packed_success :
    forall t v s i f m k off a mem' tp hs,
      types_agree t v ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp) = Some mem' ->
      reduce hs s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store t (Some tp) a off)] hs (upd_s_mem s (update_list_at s.(s_mems) i mem')) f [::]
  | r_store_packed_failure :
    forall t v s i f m k off a tp hs,
      types_agree t v ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp) = None ->
      reduce hs s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store t (Some tp) a off)] hs s f [::AI_trap]

  (** memory **)
  | r_current_memory :
      forall i f m n s hs,
        smem_ind s f.(f_inst) = Some i ->
        List.nth_error s.(s_mems) i = Some m ->
        mem_size m = n ->
        reduce hs s f [::AI_basic (BI_current_memory)] hs s f [::AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n))))]
  | r_grow_memory_success :
    forall s i f m n mem' c hs,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      mem_size m = n ->
      mem_grow m (Wasm_int.N_of_uint i32m c) = Some mem' ->
      reduce hs s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic BI_grow_memory] hs (upd_s_mem s (update_list_at s.(s_mems) i mem')) f [::AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n))))]
  | r_grow_memory_failure :
      forall i f m n s c hs,
        smem_ind s f.(f_inst) = Some i ->
        List.nth_error s.(s_mems) i = Some m ->
        mem_size m = n ->
        reduce hs s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic BI_grow_memory] hs s f [::AI_basic (BI_const (VAL_int32 int32_minus_one))]

  (** label and local **)
  | r_label :
      forall s f es les s' f' es' les' k lh hs hs',
        reduce hs s f es hs' s' f' es' ->
        lfilled k lh es les ->
        lfilled k lh es' les' ->
        reduce hs s f les hs' s' f' les'
  | r_local :
      forall s f es s' f' es' n f0 hs hs',
        reduce hs s f es hs' s' f' es' ->
        reduce hs s f0 [::AI_local n f es] hs' s' f0 [::AI_local n f' es']
  .

Definition reduce_tuple hs_s_f_es hs'_s'_f'_es' : Prop :=
  let '(hs, s, f, es) := hs_s_f_es in
  let '(hs', s', f', es') := hs'_s'_f'_es' in
  reduce hs s f es hs' s' f' es'.
      
Definition reduce_trans :
    host_state * store_record * frame * seq administrative_instruction ->
    host_state * store_record * frame * seq administrative_instruction -> Prop :=
  Relations.Relation_Operators.clos_refl_trans _ reduce_tuple.

