From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From ITree Require Import ITree.
From ITree Require ITreeFacts.
From Wasm Require Import list_extra datatypes datatypes_properties
                         interpreter binary_format_parser operations
                         typing opsem type_checker memory memory_list instantiation.
From Coq Require Import BinNat.

Section Host.

Variable host_function : eqType.
Let host := host host_function.

Variable host_instance : host.

Let store_record_eq_dec := @store_record_eq_dec host_function.
Let store_record_eqType := @store_record_eqType host_function.

Local Canonical Structure name_eqType := Eval hnf in EqType name (seq_eqMixin _).

Let store_record := store_record host_function.
Let host_state := host_state host_instance.

Let store_typing := @store_typing host_function.

Let external_typing := @external_typing host_function.

Let executable_host := executable_host host_function.
Variable executable_host_instance : executable_host.
Let host_event := host_event executable_host_instance.

Let instantiate := instantiate host_function host_instance.
Let instantiate_simpl := instantiate_simpl host_function.

Inductive ext_typing_list: store_record -> seq module_export -> seq extern_t -> Prop :=
| ext_typing_list_nil: forall s,
    ext_typing_list s [::] [::]
| ext_typing_list_cons: forall s v_exp v_exps te tes,
    ext_typing_list s v_exps tes ->
    external_typing s (modexp_desc v_exp) te ->
    ext_typing_list s (v_exp :: v_exps) (te :: tes).


Lemma instantiation_sound (s: store_record) m v_imps s' inst v_exps start:
  store_typing s ->
  instantiate s m v_imps ((s', inst, v_exps), start) ->
  (store_typing s') /\
  (exists C, inst_typing s' inst C) /\
  (exists tes, ext_typing_list s' v_exps tes) /\
  (pred_option (fun i => i < length s'.(s_funcs)) start).
  (* /\ store_extension s s' *)
Proof.
Admitted.

Lemma store_typing_preserve : forall s_funcs s_tables s_mems s_globals inst m_f,
    store_typing
      {| s_funcs := s_funcs; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |} ->
    store_typing
      {| s_funcs :=
        List.app s_funcs
                 [:: FC_func_native
                     inst
                     (List.nth (match m_f.(modfunc_type) with | Mk_typeidx n => n end) inst.(inst_types) (Tf nil nil))
                     m_f.(modfunc_locals)
                     m_f.(modfunc_body)]
      ; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |}.
Proof.
  move=> s_funcs s_tables s_mems s_globals inst m_f HSTyping.
  inversion HSTyping as [Hcl [ Htb Hmem ]].
  constructor.
  - (* cl_typing *)admit.
  split.
  - (* tab_agree *)
    induction s_tables as [| table s_tables' IHs_tables' ]; first by constructor.
    + (* forall tab_agree (table :: s_tables') *)
      rewrite /tab_agree. rewrite /tab_agree in Htb.
      inversion Htb as [|x y Htable Hs_tables]; subst.
      constructor.
      * (* tab_agree table *)
        destruct Htable as [H1 H2].
        split.
        -- (* forall tabcl_agree (table_data table) *)
          induction (table_data table) as [| hd tl IH]; first by constructor.
          (* forall tabcl_agree hd :: tl *)
          inversion H1 as [| x y Hhd Htl]; subst.
          constructor.
          (* tabcl_agree hd *)
          destruct hd. rewrite /tabcl_agree. simpl.
          rewrite /tabcl_agree in Hhd. simpl in Hhd.
          rewrite size_cat. by rewrite ltn_addr. by [].
          (* forall tabcl_agree tl *)
          apply IH. exact Htl.
        -- (* tabsize_agree table *)
          exact H2.
      * (* forall tab_agree s_tables' *)
        (*
        apply IHs_tables'.
        inversion HSTyping as [H1 [H2 H3]].
        rewrite /cl_type_check_single in H1. simpl in H1. *)
        admit.
  - (* mem_agree *)
    assumption.
    
    
        
Lemma alloc_funcs_property: forall s_funcs s_tables s_mems s_globals m_f inst,
    

  
Lemma instantiation_sound_simpl:  forall (s: store_record) m v_imps s' inst v_exps start,
  store_typing s ->
  instantiate_simpl s m v_imps ((s', inst, v_exps), start) ->
  (store_typing s') /\
  (exists C, inst_typing s' inst C) /\
  (exists tes, ext_typing_list s' v_exps tes) /\
  (pred_option (fun i => i < length s'.(s_funcs)) start).
  (* /\ store_extension s s' *)
Proof.
  move=> s m v_imps s' inst v_exps start HType HInst. inversion HInst.
  rewrite /alloc_funcs /alloc_Xs in H0. rewrite /alloc_func /add_func in H0. simpl in H0. simpl in H0.
  destruct (alloc_funcs host_function s (mod_funcs m) inst).
  
  move/andP : H0. 
  
  move=> [] s's inst_funcs_inst.
  move/eqP : s's. move=> s's.
  destruct s'. destruct s0.
  destruct (alloc_funcs host_function {| s_funcs := s_funcs; s_tables := s_tables; s_mems := s_mems; s_globals := s_globals |} (mod_funcs m) inst).

  move/andP : H0. move=> [] s's inst_funcs_inst. move/eqP : s's. destruct s'.  destruct s. move=> s's.

  move/andP : H0. Search eqP.
  case. apply andb_true_iff in H0.  split. 
  - (* store_typing s' *)
    destruct s'. split.
    * admit.
    * split. 
  Admitted.
End Host.
