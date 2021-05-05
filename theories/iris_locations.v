(** Iris location definitions and lemmas **)

From mathcomp Require Import ssreflect ssrbool eqtype seq.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.program_logic Require Import language ectx_language ectxi_language.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import common operations datatypes datatypes_properties opsem interpreter binary_format_parser iris_base.
From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From iris.program_logic Require Export weakestpre total_weakestpre.

Inductive loc : Type :=
  | loc_host_var: id -> loc
  | loc_local_var: N -> loc
  | loc_wasm_func: N -> loc
  | loc_wasm_tab: N -> loc
  | loc_wasm_mem: N -> loc
  | loc_wasm_glob: N -> loc
.

(* The following two location type definitions are for lookup lemmas later. *)
Inductive loc_type : Type :=
  | LOC_HV
  | LOC_LV
  | LOC_WF
  | LOC_WT
  | LOC_WM
  | LOC_WG
.

Definition loc_typeof (l: loc): loc_type :=
  match l with
  | loc_host_var _ => LOC_HV
  | loc_local_var _ => LOC_LV
  | loc_wasm_func _ => LOC_WF
  | loc_wasm_tab _ => LOC_WT
  | loc_wasm_mem _ => LOC_WM
  | loc_wasm_glob _ => LOC_WG
  end.

Global Instance loc_eq_decision : EqDecision loc.
Proof. solve_decision. Defined.

Global Instance loc_inhabited : Inhabited loc := populate (loc_host_var 0%N).

Definition loc_constructor_count := 6%N.

Definition encode_loc (l : loc) : N :=
  match l with
  | loc_host_var n => loc_constructor_count * n + 0%N
  | loc_local_var n => loc_constructor_count * n + 1%N
  | loc_wasm_func n => loc_constructor_count * n + 2%N
  | loc_wasm_tab n => loc_constructor_count * n + 3%N
  | loc_wasm_mem n => loc_constructor_count * n + 4%N
  | loc_wasm_glob n => loc_constructor_count * n + 5%N
  end.

Definition decode_loc (n : N) : option loc :=
  let (q, r) := N.div_eucl n loc_constructor_count in
  match r with
  | 0%N => Some (loc_host_var q)
  | 1%N => Some (loc_local_var q)
  | 2%N => Some (loc_wasm_func q)
  | 3%N => Some (loc_wasm_tab q)
  | 4%N => Some (loc_wasm_mem q)
  | 5%N => Some (loc_wasm_glob q)
  | _ => None
  end.

Lemma mult_div_eucl (a b r: N):
  (r < a)%N -> N.div_eucl (a*b+r) a = (b,r).
Proof.
Admitted.

Global Instance loc_countable : Countable loc.
Proof.
  apply (inj_countable encode_loc decode_loc).
  intros l. destruct l; unfold encode_loc, decode_loc; by rewrite mult_div_eucl.
Defined.

Inductive heap_val : Type :=
  | hval_val: val -> heap_val
  | hval_func: function_closure -> heap_val
  | hval_tab: tableinst -> heap_val
  | hval_mem: memory -> heap_val
  | hval_glob: global -> heap_val
.

(* Implemented using imap, should be the optimal now *)
Definition heap_gmap_of_list {T: Type} (l: list T) (f: N -> loc) (g: T -> heap_val) : gmap loc (option heap_val) :=
  list_to_map (imap (fun n x => (f (N.of_nat n), Some (g x))) l).

Definition gmap_of_store_func (s : store_record) : gmap loc (option heap_val) :=
  heap_gmap_of_list s.(s_funcs) (fun n => loc_wasm_func n) (fun x => hval_func x).

Definition gmap_of_store_tab (s : store_record) : gmap loc (option heap_val) :=
  heap_gmap_of_list s.(s_tables) (fun n => loc_wasm_tab n) (fun x => hval_tab x).

Definition gmap_of_store_mem (s : store_record) : gmap loc (option heap_val) :=
  heap_gmap_of_list s.(s_mems) (fun n => loc_wasm_mem n) (fun x => hval_mem x).

Definition gmap_of_store_glob (s : store_record) : gmap loc (option heap_val) :=
  heap_gmap_of_list s.(s_globals) (fun n => loc_wasm_glob n) (fun x => hval_glob x).

Definition gmap_of_store (s : store_record) : gmap loc (option heap_val) :=
  map_union (gmap_of_store_func s)
            (map_union (gmap_of_store_tab s)
                       (map_union (gmap_of_store_mem s)
                                 (gmap_of_store_glob s))).

Definition gmap_of_locs (locs: list host_value) : gmap loc (option heap_val) :=
  heap_gmap_of_list locs (fun n => loc_local_var n) (fun x => hval_val x).

Definition heap_gmap_of_hs (hs: host_state) : gmap loc (option heap_val) :=
  list_to_map
  (fmap (fun p => match p with | (x, y) => (loc_host_var x, option_map (fun y => hval_val y) y) end)
        (map_to_list hs)).

(* automatically remembers a lookup result and make the hypothesis ready for destruct *)
Ltac remember_lookup :=
  match goal with
  | |- context C [?m !! ?x = _] =>
    let Hlookup := fresh "Hlookup" in
    remember (m !! x) as lookup_res eqn: Hlookup; symmetry in Hlookup
  end.

(* resolving predicates related to maps and lookups in stdpp. *)
Ltac resolve_finmap :=
  repeat match goal with
         | H: (list_to_map _) !! _ = Some _ |- _ =>
           let H2 := fresh "H2" in 
           apply elem_of_list_to_map in H as H2; clear H
         | H: (list_to_map _) !! _ = None |- _ =>
           let H2 := fresh "H2" in 
           apply not_elem_of_list_to_map in H as H2; clear H
         | H: _ ∈ fmap _ _ |- _ =>
           let Heq := fresh "Heq" in
           let Helem := fresh "Helem" in
           apply elem_of_list_fmap in H; destruct H as [? [Heq Helem]]; subst; simpl in *
         | H: ?x ∈ map_to_list _ |- _ =>
           destruct x; apply elem_of_map_to_list in H
         | H: _ ∈ imap _ _ |- _ =>
           let Heq := fresh "Heq" in
           let Helem := fresh "Helem" in
           apply elem_of_lookup_imap in H; destruct H as [? [? [Heq Helem]]]
         | H: (_, _) = (_, _) |- _ =>
           inversion H; subst; clear H
         | H: _ |- NoDup (fmap fst _) =>
           apply NoDup_fmap_fst; intros; subst; simpl in *; try by []
         | H: _ |- NoDup (map_to_list _) =>
           apply NoDup_map_to_list; try by []
         | H1: ?m !! ?x = _, H2: ?m !! ?x = _ |- _ =>
           rewrite H2 in H1; subst; simpl in *; clear H2
         | H: Some _ = Some _ |- _ =>
           inversion H; subst; simpl in *; try by []
         | H: _ |- (_, _) ∈ map_to_list _ =>
           apply elem_of_map_to_list
         | _ => simpl in *; try by eauto
         end.

(* Turns out that this is surprisingly not a standard lemma in stdpp and non-trivial to prove. *)
Lemma nodup_imap_inj1 {T X: Type} (l: list T) (f: nat -> T -> X):
  (forall n1 n2 t1 t2, f n1 t1 = f n2 t2 -> n1 = n2) ->
  NoDup (imap f l).
Proof.
  move: f.
  induction l => //=; first by intros; apply NoDup_nil.
  move => f HInj1. apply NoDup_cons. split.
  - move => HContra. apply elem_of_lookup_imap in HContra.
    destruct HContra as [i [y [Heq Helem]]].
    by apply HInj1 in Heq.
  - apply IHl. move => n1 n2 t1 t2 Heq.
    simpl in Heq. apply HInj1 in Heq. lia.
Qed.
    
Lemma heapg_of_list_lookup {T: Type} (l: list T) (f: N -> loc) (g: T -> heap_val) (n: N):
  Inj eq eq f ->
  (heap_gmap_of_list l f g) !! (f n) = option_map (fun x => Some (g x)) (l !! (N.to_nat n)).
Proof with resolve_finmap.
  move => HInj.
  unfold heap_gmap_of_list, option_map.
  remember_lookup.
  destruct lookup_res => //=...
  - apply HInj in H0. subst.
    rewrite Nat2N.id. by rewrite Helem.
  - apply HInj, N_of_nat_inj in H1. subst...
  - apply nodup_imap_inj1.
    move => n1 n2 t1 t2 Heq...
    by apply HInj, N_of_nat_inj in H1.
  - rewrite -> elem_of_list_fmap in H2.
    remember (l !! N.to_nat n) as lookup_res eqn: Hlookup; symmetry in Hlookup.
    destruct lookup_res => //=.
    exfalso. apply H2.
    exists (f n, Some (g t)). split => //=.
    apply elem_of_lookup_imap.
    exists (N.to_nat n), t. split => //=.
    by rewrite N2Nat.id.
Qed.

(* Technically this is true without injectivity of f as well, but unfortunately our tactic is a 
     bit too aggressive and makes this unprovable without injectivity. Luckily all uses in this
     project will be injective. *)
Lemma heapg_of_list_lookup_none {T: Type} (l: list T) (f: N -> loc) (g: T -> heap_val) (lo: loc):
  Inj eq eq f ->
  (forall x, f x <> lo) ->
  (heap_gmap_of_list l f g) !! lo = None.
Proof with resolve_finmap.
  move => HInj Hne.
  unfold heap_gmap_of_list.
  remember_lookup.
  destruct lookup_res => //=...
  - exfalso. by apply (Hne (N.of_nat x)).
  - apply HInj, N_of_nat_inj in H1. subst...
  - apply nodup_imap_inj1.
    move => n1 n2 t1 t2 Heq...
    by apply HInj, N_of_nat_inj in H1.
Qed.
    
Lemma heapg_hs_hs_lookup (hs: host_state) (i: id):
  (heap_gmap_of_hs hs) !! (loc_host_var i) = option_map (option_map (fun y => hval_val y)) (hs !! i).
Proof with resolve_finmap.
  remember_lookup.
  unfold heap_gmap_of_hs, option_map in *.
  destruct lookup_res...
  - by rewrite Helem.
  - apply NoDup_fmap...
    move => [x1 y1] [x2 y2] Heq...
    destruct y1, y2 => //...
  - rewrite -> elem_of_list_fmap in H2.
    remember (hs !! i) as lookup_res2 eqn: Hlookup2; symmetry in Hlookup2.
    repeat destruct lookup_res2 as [lookup_res2|] => //=; exfalso; apply H2...
    + exists (loc_host_var i, Some (hval_val lookup_res2)). split => //=.
      apply elem_of_list_fmap.
      exists (i, Some lookup_res2). split...
    + exists (loc_host_var i, None). split => //=.
      apply elem_of_list_fmap.
      exists (i, None). split...
Qed.

Lemma heapg_hs_noths_lookup (hs: host_state) (l: loc):
  loc_typeof l <> LOC_HV ->
  (heap_gmap_of_hs hs) !! l = None.
Proof with resolve_finmap.
  remember_lookup.
  move => HLT.
  destruct lookup_res => //=.
  unfold heap_gmap_of_hs in Hlookup...
  apply NoDup_fmap...
  move => [x1 y1] [x2 y2] Heq...
  unfold option_map in H2.
  destruct y1, y2 => //...
Qed.

Ltac resolve_heapg_list_typed :=
  remember_lookup;
  match goal with
  | Hlookup: ?pred _ !! _ = ?lookup_res |- _ =>
    unfold pred in Hlookup;
    rewrite -> heapg_of_list_lookup in Hlookup => //=;
    try by (intros ?? Heq; inversion Heq);
    unfold option_map in *; try by destruct lookup_res; resolve_finmap
  | _ => idtac
  end.

Lemma heapg_loc_loc_lookup (locs: list host_value) (n: N):
  (gmap_of_locs locs) !! (loc_local_var n) = option_map (fun y => Some (hval_val y)) (locs !! (N.to_nat n)).
Proof.
  by resolve_heapg_list_typed.
Qed.  

Lemma heapg_func_func_lookup (s: store_record) (n: N):
  (gmap_of_store_func s) !! (loc_wasm_func n) = option_map (fun x => Some (hval_func x)) (s.(s_funcs) !! (N.to_nat n)).
Proof.
  by resolve_heapg_list_typed.
Qed.

Lemma heapg_tab_tab_lookup (s: store_record) (n: N):
  (gmap_of_store_tab s) !! (loc_wasm_tab n) = option_map (fun x => Some (hval_tab x)) (s.(s_tables) !! (N.to_nat n)).
Proof.
  by resolve_heapg_list_typed.
Qed.

Lemma heapg_mem_mem_lookup (s: store_record) (n: N):
  (gmap_of_store_mem s) !! (loc_wasm_mem n) = option_map (fun x => Some (hval_mem x)) (s.(s_mems) !! (N.to_nat n)).
Proof.
  by resolve_heapg_list_typed.
Qed.

Lemma heapg_glob_glob_lookup (s: store_record) (n: N):
  (gmap_of_store_glob s) !! (loc_wasm_glob n) = option_map (fun x => Some (hval_glob x)) (s.(s_globals) !! (N.to_nat n)).
Proof.
  by resolve_heapg_list_typed.
Qed.

Ltac resolve_heapg_list_mistyped :=
  remember_lookup;
  intros ?;
  match goal with
  | Hlookup: ?pred _ !! ?l = ?lookup_res |- _ =>
    destruct lookup_res => //=;
    unfold pred in Hlookup;
    rewrite -> heapg_of_list_lookup_none in Hlookup; try by (destruct l; try resolve_finmap);
    try by (intros ?? Heq; inversion Heq)
  | _ => idtac
  end.

Lemma heapg_loc_notloc_lookup (locs: list host_value) (l: loc):
  loc_typeof l <> LOC_LV ->
  (gmap_of_locs locs) !! l = None.
Proof.
  by resolve_heapg_list_mistyped.
Qed.

Lemma heapg_func_notfunc_lookup (s: store_record) (l: loc):
  loc_typeof l <> LOC_WF ->
  (gmap_of_store_func s) !! l = None.
Proof.
  by resolve_heapg_list_mistyped.
Qed.

Lemma heapg_tab_nottab_lookup (s: store_record) (l: loc):
  loc_typeof l <> LOC_WT ->
  (gmap_of_store_tab s) !! l = None.
Proof.
  by resolve_heapg_list_mistyped.
Qed.

Lemma heapg_mem_notmem_lookup (s: store_record) (l: loc):
  loc_typeof l <> LOC_WM ->
  (gmap_of_store_mem s) !! l = None.
Proof.
  by resolve_heapg_list_mistyped.
Qed.

Lemma heapg_glob_notglob_lookup (s: store_record) (l: loc):
  loc_typeof l <> LOC_WG ->
  (gmap_of_store_glob s) !! l = None.
Proof.
  by resolve_heapg_list_mistyped.
Qed.

Ltac simplify_store_lookup H :=
  repeat match type of H with
  | context C [gmap_of_store_func _ !! _] =>
    try rewrite heapg_func_func_lookup in H; try rewrite heapg_func_notfunc_lookup in H
  | context C [gmap_of_store_tab _ !! _ ] =>
    try rewrite heapg_tab_tab_lookup in H; try rewrite heapg_tab_nottab_lookup in H
  | context C [gmap_of_store_mem _ !! _ ] =>
    try rewrite heapg_mem_mem_lookup in H; try rewrite heapg_mem_notmem_lookup in H
  | context C [gmap_of_store_glob _ !! _ ] =>
    try rewrite heapg_glob_glob_lookup in H; try rewrite heapg_glob_notglob_lookup in H
  end.

Ltac resolve_heapg_store_lookup :=
  remember_lookup;
  repeat match goal with
  | Hlookup: gmap_of_store _ !! _ = ?lookup_res |- _ =>
    destruct lookup_res => //=;
    unfold gmap_of_store, map_union in Hlookup;
    repeat rewrite lookup_union_with in Hlookup;
    unfold union_with, option_union_with in Hlookup;
    simplify_store_lookup Hlookup; try by []
  | _ => idtac
  end.

Lemma heapg_store_hs_lookup (s: store_record) (i: id):
  (gmap_of_store s) !! (loc_host_var i) = None.
Proof.
  resolve_heapg_store_lookup.
Qed.
  
Lemma heapg_store_loc_lookup (s: store_record) (n: N):
  (gmap_of_store s) !! (loc_local_var n) = None.
Proof.
  resolve_heapg_store_lookup.
Qed.

Lemma heapg_store_func_lookup (s: store_record) (n: N):
  (gmap_of_store s) !! (loc_wasm_func n) = option_map (fun x => Some (hval_func x)) (s.(s_funcs) !! (N.to_nat n)).
Proof.
  resolve_heapg_store_lookup; rewrite - Hlookup; by destruct (option_map _ _).
Qed.

Lemma heapg_store_tab_lookup (s: store_record) (n: N):
  (gmap_of_store s) !! (loc_wasm_tab n) = option_map (fun x => Some (hval_tab x)) (s.(s_tables) !! (N.to_nat n)).
Proof.
  resolve_heapg_store_lookup; rewrite - Hlookup; by destruct (option_map _ _).
Qed.

Lemma heapg_store_mem_lookup (s: store_record) (n: N):
  (gmap_of_store s) !! (loc_wasm_mem n) = option_map (fun x => Some (hval_mem x)) (s.(s_mems) !! (N.to_nat n)).
Proof.
  resolve_heapg_store_lookup; rewrite - Hlookup; by destruct (option_map _ _).
Qed.

Lemma heapg_store_glob_lookup (s: store_record) (n: N):
  (gmap_of_store s) !! (loc_wasm_glob n) = option_map (fun x => Some (hval_glob x)) (s.(s_globals) !! (N.to_nat n)).
Proof.
  resolve_heapg_store_lookup; rewrite - Hlookup; by destruct (option_map _ _).
Qed.

Definition gmap_of_state (σ : state) : gmap loc (option heap_val) :=
  let (hss, locs) := σ in
  let (hs, s) := hss in
  map_union (gmap_of_store s)
            (map_union (gmap_of_locs locs)
                       (heap_gmap_of_hs hs)).

Ltac simplify_component_lookup :=
  repeat match goal with
  | |- context C [gmap_of_store _ !! loc_host_var _ ] =>
    rewrite heapg_store_hs_lookup
  | |- context C [gmap_of_store _ !! loc_local_var _ ] =>
    rewrite heapg_store_loc_lookup
  | |- context C [gmap_of_store _ !! loc_wasm_func _ ] =>
    rewrite heapg_store_func_lookup
  | |- context C [gmap_of_store _ !! loc_wasm_tab _ ] =>
    rewrite heapg_store_tab_lookup
  | |- context C [gmap_of_store _ !! loc_wasm_mem _ ] =>
    rewrite heapg_store_mem_lookup
  | |- context C [gmap_of_store _ !! loc_wasm_glob _ ] =>
    rewrite heapg_store_glob_lookup
  | |- context C [gmap_of_locs _ !! _ ] =>
    try rewrite heapg_loc_loc_lookup; try rewrite heapg_loc_notloc_lookup
  | |- context C [heap_gmap_of_hs _ !! _ ] =>
    try rewrite heapg_hs_hs_lookup; try rewrite heapg_hs_noths_lookup
  | _ => idtac
  end.

Ltac resolve_heapg_state_lookup :=
  intros;
  unfold gmap_of_state, map_union;
  repeat (rewrite lookup_union_with; simplify_component_lookup) => //;
  unfold union_with, option_union_with;
  destruct (option_map _ _)
  .
  
Lemma heapg_state_hs_lookup: forall hs s locs id,
  (gmap_of_state (hs, s, locs)) !! (loc_host_var id) = option_map (option_map (fun v => hval_val v)) (hs !! id).
Proof.
  by resolve_heapg_state_lookup.
Qed.  

Lemma heapg_state_loc_lookup: forall hs s locs n,
  (gmap_of_state (hs, s, locs)) !! (loc_local_var n) = option_map (fun v => Some (hval_val v)) (locs !! (N.to_nat n)).
Proof.
  by resolve_heapg_state_lookup.
Qed.

Lemma heapg_state_func_lookup: forall hs s locs n,
  (gmap_of_state (hs, s, locs)) !! (loc_wasm_func n) = option_map (fun v => Some (hval_func v)) (s.(s_funcs) !! (N.to_nat n)).
Proof.
  by resolve_heapg_state_lookup.
Qed.

Lemma heapg_state_tab_lookup: forall hs s locs n,
  (gmap_of_state (hs, s, locs)) !! (loc_wasm_tab n) = option_map (fun v => Some (hval_tab v)) (s.(s_tables) !! (N.to_nat n)).
Proof.
  by resolve_heapg_state_lookup.
Qed.

Lemma heapg_state_mem_lookup: forall hs s locs n,
  (gmap_of_state (hs, s, locs)) !! (loc_wasm_mem n) = option_map (fun v => Some (hval_mem v)) (s.(s_mems) !! (N.to_nat n)).
Proof.
  by resolve_heapg_state_lookup.
Qed.

Lemma heapg_state_glob_lookup: forall hs s locs n,
  (gmap_of_state (hs, s, locs)) !! (loc_wasm_glob n) = option_map (fun v => Some (hval_glob v)) (s.(s_globals) !! (N.to_nat n)).
Proof.
  by resolve_heapg_state_lookup.
Qed.

Ltac simplify_lookup H :=
  repeat match type of H with
  | context C [gmap_of_state (_, _, _) !! (loc_host_var _)] =>
    try rewrite heapg_state_hs_lookup in H
  | context C [gmap_of_state (_, _, _) !! (loc_local_var _)] =>
    try rewrite heapg_state_loc_lookup in H
  | context C [gmap_of_state (_, _, _) !! (loc_wasm_func _)] =>
    try rewrite heapg_state_func_lookup in H
  | context C [gmap_of_state (_, _, _) !! (loc_wasm_tab _)] =>
    try rewrite heapg_state_tab_lookup in H
  | context C [gmap_of_state (_, _, _) !! (loc_wasm_mem _)] =>
    try rewrite heapg_state_mem_lookup in H
  | context C [gmap_of_state (_, _, _) !! (loc_wasm_glob _)] =>
    try rewrite heapg_state_glob_lookup in H
  end.

Lemma fold_gmap_state hs s locs:
  map_union (gmap_of_store s) (map_union (gmap_of_locs locs) (heap_gmap_of_hs hs)) = gmap_of_state (hs, s, locs).
Proof.
  trivial.
Qed.

Lemma heapg_hs_update hs s locs i v:
  gmap_of_state (<[i := (Some v)]> hs, s, locs) = <[(loc_host_var i) := (Some (hval_val v))]> (gmap_of_state (hs, s, locs)).
Proof with resolve_finmap.
  unfold gmap_of_state, map_union.
  repeat rewrite insert_union_with_r; simplify_component_lookup => //.
  repeat f_equal.
  unfold heap_gmap_of_hs.
  apply map_eq; intros i'.
  destruct (decide (i' = (loc_host_var i))) as [->|HN].
  - rewrite lookup_insert.
    apply elem_of_list_to_map...
    + apply NoDup_fmap; last by apply NoDup_map_to_list.
      move => [x1 y1] [x2 y2] Heq.
      unfold option_map in Heq.
      by destruct y1; destruct y2; inversion Heq; subst.
    + rewrite -> elem_of_list_fmap.
      exists (i, Some v).
      split => //=.
      apply elem_of_map_to_list.
      by apply lookup_insert.
  - rewrite lookup_insert_ne => //.
    remember_lookup...
    destruct lookup_res...
    + rewrite lookup_insert_ne in Helem => //; last by intros ?; apply HN; subst.
      symmetry. apply elem_of_list_to_map...
      * apply NoDup_fmap; last by apply NoDup_map_to_list.
        move => [x1 y1] [x2 y2] Heq...
        unfold option_map in H1. destruct y1; destruct y2 => //=; by inversion H1.
      * apply elem_of_list_fmap.
        exists (i0, o0). split => //...
    + apply NoDup_fmap; last by apply NoDup_map_to_list.
      move => [x1 y1] [x2 y2] Heq...
      unfold option_map in H2.
      destruct y1; destruct y2 => //=; by inversion H2. (* This proof for NoDup is becoming a pattern. *)
    + symmetry. apply not_elem_of_list_to_map.
      move => HContra. apply H2...
      apply elem_of_list_fmap.
      exists (loc_host_var i0, option_map (fun x => hval_val x) o).
      split => //=.
      apply elem_of_list_fmap.
      exists (i0, o).
      split => //...
      rewrite lookup_insert_ne => //.
      intros ?; by apply HN => //; subst.
Qed.

(* This means the proposition that 'the location l of the heap has value v, and we own q of it' 
     (fractional algebra). 
   We really only need either 0/1 permission for our language, though. *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=option heap_val) l q (Some v%V))
   (at level 20, q at level 5, format "l  ↦{ q } v") : bi_scope.
Notation "l ↦ v" := (mapsto (L:=loc) (V:=option heap_val) l 1 (Some v%V))
   (at level 20, format "l ↦ v") : bi_scope.
