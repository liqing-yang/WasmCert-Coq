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
  | loc_host_var: N -> loc
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
  | hval_glob: global -> heap_val.

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

Ltac remember_lookup :=
  match goal with
  | |- context C [?m !! ?x = _] =>
    let Hlookup := fresh "Hlookup" in
    remember (m !! x) as lookup_res eqn: Hlookup; symmetry in Hlookup
  end.

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

Lemma heapg_locs_locs_lookup (locs: list host_value) (n: N):
  (gmap_of_locs locs) !! (loc_local_var n) = option_map (fun y => Some (hval_val y)) (locs !! (N.to_nat n)).
Proof with resolve_finmap.
  remember_lookup.
  unfold gmap_of_locs in Hlookup.
  rewrite -> heapg_of_list_lookup in Hlookup.
  - unfold option_map in *. by destruct lookup_res...
  - move => x y Heq. by inversion Heq.
Qed.  

Lemma heapg_locs_notlocs_lookup (locs: list host_value) (l: loc):
  loc_typeof l <> LOC_LV ->
  (gmap_of_locs locs) !! l = None.
Proof with resolve_finmap.
  remember_lookup.
  move => HLT.
  destruct lookup_res => //=.
  unfold gmap_of_locs in Hlookup.
  rewrite -> heapg_of_list_lookup_none in Hlookup; last by destruct l...
  move => x y Heq; by inversion Heq.
Qed.

Lemma heapg_store_hs_lookup (s: store_record) (i: id):
  (gmap_of_store s) !! (loc_host_var i) = None.
Proof.
  remember_lookup.
  destruct lookup_res => //=.
  unfold gmap_of_store in Hlookup.
  unfold map_union in Hlookup.
  repeat rewrite lookup_union_with in Hlookup.
  unfold union_with, option_union_with in Hlookup.
Admitted.
  
Definition gmap_of_state (σ : state) : gmap loc (option heap_val) :=
  let (hss, locs) := σ in
  let (hs, s) := hss in
  (* TODO: maybe better to make a disjoint_union predicate to make lookup lemmas easier. *)
  map_union (gmap_of_store s)
            (map_union (gmap_of_locs locs)
                       (heap_gmap_of_hs hs)).

Lemma gmap_of_state_lookup_hs: forall hs s locs id,
    (gmap_of_state (hs, s, locs)) !! (loc_host_var id) = option_map (option_map (fun v => hval_val v)) (hs !! id).
Proof.
  move => hs s locs id. unfold gmap_of_state.
  rewrite lookup_union. unfold union_with, option_union_with.
Admitted.

Lemma gmap_of_state_lookup_locs: forall hs s locs n,
    (gmap_of_state (hs, s, locs)) !! (loc_local_var n) = option_map (fun v => Some (hval_val v)) (List.nth_error locs (N.to_nat n)).
Proof.
  move => hs s locs n.
Admitted.


(* This means the proposition that 'the location l of the heap has value v, and we own q of it' 
     (fractional algebra). 
   We really only need either 0/1 permission for our language, though. *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=option heap_val) l q (Some v%V))
   (at level 20, q at level 5, format "l  ↦{ q } v") : bi_scope.
Notation "l ↦ v" := (mapsto (L:=loc) (V:=option heap_val) l 1 (Some v%V))
   (at level 20, format "l ↦ v") : bi_scope.
