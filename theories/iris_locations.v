(** Iris location definitions and lemmas **)

From mathcomp Require Import ssreflect ssrbool eqtype seq.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.program_logic Require Import language ectx_language ectxi_language.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import common operations_iris datatypes_iris datatypes_properties_iris.
From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From iris.program_logic Require Export weakestpre total_weakestpre.

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
         | H: _ ∈ ?l |- _ =>
           let Helem := fresh "Helem" in
           try is_var l; apply elem_of_list_lookup in H; destruct H as [? Helem]
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
    
Definition lookup_2d {T: Type} (l: list (list T)) (n: nat) (i: nat) : option T :=
  match (l !! n) with
  | Some x => x !! i
  | None => None
  end.

Definition flatten_list {T: Type} (l: list T) : list (N * T) :=
  imap (fun n x => (N.of_nat n, x)) l.

Lemma flatten_list_nodup {T: Type} (l: list T):
  NoDup (flatten_list l).
Proof.
  unfold flatten_list.
  apply nodup_imap_inj1.
  intros.
  inversion H.
  lia.
Qed.

Lemma flatten_list_lookup_Some {T: Type} (l: list T) (i: nat) x:
  l !! i = Some x ->
  (flatten_list l) !! i = Some (N.of_nat i, x).
Proof.
  move => H.
  unfold flatten_list.
  rewrite list_lookup_imap.
  by rewrite H.
Qed.

Definition gmap_of_list {T: Type} (l: list T) : gmap N T :=
  list_to_map (flatten_list l).

Fixpoint flatten_2d_list_i {T: Type} (l: list (list T)) (i: N) : list ((N*N) * T) :=
  match l with
  | [::] => [::]
  | l1 :: l' =>
    let lf := flatten_list l1 in
    (fmap (fun x => match x with | (n, b) => ((i, n), b) end) lf) ++ (flatten_2d_list_i l' (i+1))
  end.

Definition flatten_2d_list {T: Type} (l: list (list T)) : list ((N*N) * T) :=
  flatten_2d_list_i l 0.

Definition gmap_of_list_2d {T: Type} (l: list (list T)) : gmap (N*N) T :=
  list_to_map (flatten_2d_list l).

Definition memory_to_list (m: memory) : list byte :=
  (m.(mem_data)).(memory_list.ml_data).

Definition gmap_of_memory (l: list memory) : gmap (N*N) byte :=
  gmap_of_list_2d (fmap memory_to_list l).

Definition table_to_list (tab: tableinst) : list funcelem :=
  tab.(table_data).

Definition gmap_of_table (l: list tableinst) : gmap (N*N) funcelem :=
  gmap_of_list_2d (fmap table_to_list l).

Lemma gmap_of_list_lookup {T: Type} (l: list T) n:
  (gmap_of_list l) !! n = l !! (N.to_nat n).
Proof with resolve_finmap.
  unfold gmap_of_list, flatten_list.
  remember_lookup.
  destruct lookup_res...
  - rewrite Nat2N.id. by rewrite Helem.
  - apply Nat2N.inj in H1. subst. rewrite Helem in Helem0. by inversion Helem0.
  - apply nodup_imap_inj1. move => n1 n2 t1 t2 Heq.
    inversion Heq.
    by apply Nat2N.inj in H1.
  - destruct (l !! (N.to_nat n)) eqn: Hlookup => //.
    exfalso. apply H2. clear H2.
    apply elem_of_list_fmap.
    exists (n, t). split => //.
    apply elem_of_lookup_imap.
    exists (N.to_nat n), t. split => //.
    by rewrite N2Nat.id.
Qed.

(* Commutativity between gmap_of_list and list_insert. *)
Lemma gmap_of_list_insert {T: Type} (l: list T) (v: T) n:
  N.to_nat n < length l ->
  gmap_of_list (<[N.to_nat n:=v]> l) = <[n:=v]> (gmap_of_list l).
Proof with resolve_finmap.
  move => Hlen.
  apply map_eq. move => i.
  rewrite gmap_of_list_lookup.
  destruct (decide (i = n)).
  - subst. rewrite lookup_insert. by rewrite list_lookup_insert.
  - rewrite lookup_insert_ne => //.
    rewrite list_lookup_insert_ne => //.
    + by rewrite gmap_of_list_lookup.
    + move => HContra. apply n0.
      by apply N2Nat.inj.    
Qed.

Lemma gmap_of_list_append {T: Type} (l: list T) (v: T):
  gmap_of_list (l ++ [:: v]) = <[N.of_nat (length l) := v]> (gmap_of_list l).
Proof with resolve_finmap.
  apply map_eq. move => i.
  repeat rewrite gmap_of_list_lookup.
  destruct (decide (i = N.of_nat (length l))).
  - subst. rewrite Nat2N.id. rewrite lookup_insert. rewrite lookup_app.
    destruct (l !! length l) eqn:Hlookup => //=.
    + apply lookup_lt_Some in Hlookup. lia.
    + by replace (length l - length l) with 0; last lia.
  - remember_lookup. symmetry.
    destruct lookup_res...
    + assert (N.to_nat i < length l) as HLength.
      { apply lookup_lt_Some in Hlookup.
        rewrite app_length in Hlookup. simpl in Hlookup.
        lia. }
      rewrite lookup_insert_ne => //.
      rewrite gmap_of_list_lookup.
      rewrite lookup_app in Hlookup.
      destruct (l !! N.to_nat i) eqn:Hlookup2 => //=.
      apply lookup_ge_None in Hlookup2.
      lia.
    + apply lookup_ge_None in Hlookup.
      rewrite lookup_insert_ne => //.
      rewrite gmap_of_list_lookup.
      apply lookup_ge_None.
      rewrite app_length in Hlookup; simpl in Hlookup.
      lia.
Qed.

Lemma flatten_2d_list_i_acc_shift_spec {T: Type} (l: list (list T)) (acc: N):
  flatten_2d_list_i l (acc+1) = (fun x => match x with
                                            | (n, i, t) => ((n+1)%N, i, t)
                                            end) <$>
                                                 (flatten_2d_list_i l acc).
Proof.
  move: l acc.
  induction l => //.
  move => acc.
  simpl.
  rewrite fmap_app.
  rewrite IHl.
  f_equal.
  clear IHl.
  apply list_eq.
  move => i.
  repeat rewrite list_lookup_fmap.
  destruct (a !! i) eqn:Hl.
  - apply flatten_list_lookup_Some in Hl.
    by rewrite Hl.
  - assert (flatten_list a !! i = None) as H; last by rewrite H.
    unfold flatten_list.
    apply lookup_ge_None.
    apply lookup_ge_None in Hl.
    by rewrite imap_length.
Qed.
  
Lemma flatten_2d_list_i_acc_shift {T: Type} (l: list (list T)) n i t acc:
  (N.of_nat (n+1), i, t) ∈ flatten_2d_list_i l (acc+1) <->
  (N.of_nat n, i, t) ∈ flatten_2d_list_i l acc.
Proof.
  rewrite flatten_2d_list_i_acc_shift_spec.
  rewrite elem_of_list_fmap.
  split.
  - move => [[[n' i'] t'] [Heq Helem]].
    inversion Heq; subst; clear Heq.
    replace (N.of_nat n) with n' => //.
    lia.
  - move => Helem.
    exists (N.of_nat n, i, t).
    split => //.
    repeat f_equal.
    lia.
Qed.
    
Lemma flatten_2d_list_i_acc_domain1 {T: Type} (l: list (list T)) n i t acc:
  (n, i, t) ∈ flatten_2d_list_i l acc ->
  (n >= acc)%N.
Proof.
  rewrite - (N2Nat.id n).
  remember (N.to_nat n) as n0. clear Heqn0 n.
  rewrite - (N2Nat.id acc).
  remember (N.to_nat acc) as acc0. clear Heqacc0 acc.
  move: n0 i t acc0.
  induction n0 => //; move => i t acc0 Helem.
  - destruct acc0 => //.
    replace (N.of_nat (S acc0)) with (N.of_nat acc0 + 1)%N in Helem; last lia.
    rewrite flatten_2d_list_i_acc_shift_spec in Helem.
    resolve_finmap.
    destruct x.
    destruct p.
    inversion Heq.
    lia.
  - destruct acc0 => //.
    replace (N.of_nat (S acc0)) with (N.of_nat acc0 + 1)%N in Helem; last lia.
    assert (N.of_nat n0 >= N.of_nat acc0)%N; last lia.
    eapply IHn0.
    apply flatten_2d_list_i_acc_shift.
    replace (n0+1) with (S n0) => //.
    lia.
Qed.
    
Lemma flatten_2d_list_lookup {T: Type} (l: list (list T)) n i t:
  (n, i, t) ∈ flatten_2d_list l <->
  match l !! (N.to_nat n) with
  | Some l' => l' !! (N.to_nat i)
  | None => None
  end = Some t.
Proof.
  unfold flatten_2d_list.
  split.
  - move: n i t.
    induction l => //=; move => n i t Helem.
    + by apply elem_of_nil in Helem.
    + destruct (N.to_nat n) eqn: Hn => //=.
      * unfold flatten_list in Helem.
        assert (n = 0%N); first lia. subst; clear Hn.
        apply elem_of_app in Helem.
        destruct Helem as [Helem|Helem]; resolve_finmap; subst.
        -- inversion Heq. subst.
          by rewrite Nat2N.id.
        -- apply elem_of_list_lookup_2 in Helem0.
          apply flatten_2d_list_i_acc_domain1 in Helem0.
          lia.
      * assert (n = N.of_nat (S n0)); first lia; subst; clear Hn.
        rewrite - (Nat2N.id n0).
        apply IHl.
        apply flatten_2d_list_i_acc_shift.
        apply elem_of_app in Helem.
        destruct Helem as [Helem|Helem]; resolve_finmap; subst; first by destruct x.
        apply elem_of_list_lookup_2 in Helem0.
        replace (N.of_nat (n0+1)) with (N.pos (Pos.of_succ_nat n0)) => //.
        lia.
  - move: n i t.
    induction l => //=; move => n i t Hl.
    destruct (N.to_nat n) eqn:Hn => //=.
    + assert (n=0%N); first lia. subst; clear Hn.
      simpl in Hl.
      apply elem_of_app; left.
      apply elem_of_list_fmap.
      exists (i, t).
      split => //.
      unfold flatten_list.
      apply elem_of_lookup_imap.
      exists (N.to_nat i), t.
      split => //.
      f_equal.
      lia.
    + simpl in Hl.
      replace n with (N.of_nat (n0+1)); last lia.
      rewrite - (Nat2N.id n0) in Hl.
      apply IHl in Hl.
      unfold flatten_list.
      apply flatten_2d_list_i_acc_shift in Hl.
      apply elem_of_app; by right.
Qed.
      
Lemma flatten_2d_list_inj12 {T: Type} (l: list (list T)) x1 x2 p t1 t2:
  flatten_2d_list l !! x1 = Some (p, t1) ->
  flatten_2d_list l !! x2 = Some (p, t2) ->
  t1 = t2.
Proof.
  destruct p as [n i].
  move => Hl1 Hl2.
  apply elem_of_list_lookup_2 in Hl1, Hl2.
  apply flatten_2d_list_lookup in Hl1, Hl2.
  rewrite Hl1 in Hl2.
  by inversion Hl2.
Qed.
  
Lemma flatten_2d_list_nodup {T: Type} (l: list (list T)):
  NoDup (flatten_2d_list l).
Proof.
  unfold flatten_2d_list.
  induction l => //=.
  - by apply NoDup_nil.
  - apply NoDup_app => //=.
    split.
    + apply NoDup_fmap.
      * move => x1 x2 Heq.
        destruct x1, x2.
        by inversion Heq.
      * by apply flatten_list_nodup.
    + split.
      * move => [[n i] t] Helem.
        resolve_finmap.
        destruct x.
        inversion Heq; subst; clear Heq.
        move => HContra.
        apply flatten_2d_list_i_acc_domain1 in HContra.
        lia.
      * rewrite flatten_2d_list_i_acc_shift_spec => //.
        apply NoDup_fmap => //.
        move => x1 x2 Heq.
        destruct x1, x2.
        destruct p, p0.
        inversion Heq; subst; clear Heq.
        repeat f_equal.
        lia.
Qed.
        
Lemma gmap_of_list_2d_lookup {T: Type} (l: list (list T)) n i:
  (gmap_of_list_2d l) !! (n, i) = match l !! (N.to_nat n) with
                                  | Some l' => l' !! (N.to_nat i)
                                  | None => None
                                  end.
Proof with resolve_finmap.
  unfold gmap_of_list_2d, flatten_2d_list.
  remember_lookup.
  destruct lookup_res...
  - symmetry. apply flatten_2d_list_lookup.
    by apply elem_of_list_lookup; eexists.
  - by eapply flatten_2d_list_inj12.
  - fold (flatten_2d_list l).
    by apply flatten_2d_list_nodup.
  - destruct (l !! (N.to_nat n)) eqn: Hlookup => //.
    destruct (l0 !! (N.to_nat i)) eqn: Hlookup2 => //.
    exfalso. apply H2. clear H2.
    apply elem_of_list_fmap.
    exists (n, i, t). split => //.
    apply flatten_2d_list_lookup.
    by rewrite Hlookup Hlookup2.
Qed.

Definition new_2d_gmap_at_n {T: Type} (n: N) (len: nat) (x: T) : gmap (N*N) T :=
  list_to_map (imap (fun i x => ((n, N.of_nat i), x)) (repeat x len)).

Lemma repeat_lookup {T: Type} (x: T) (n i: nat):
  i < n <->
  (repeat x n) !! i = Some x.
Proof.
  split. 
  - move : n.
    induction i; move => n HLen; destruct n => //=; try lia.
    apply IHi.
    lia.
  - move => Hlookup.
    apply lookup_lt_Some in Hlookup.
    by rewrite repeat_length in Hlookup.
Qed.

Lemma new_2d_gmap_at_n_lookup {T: Type} n i len (x:T):
  N.to_nat i < len ->
  new_2d_gmap_at_n n len x !! (n, i) = Some x.
Proof.
  move => HLen.
  unfold new_2d_gmap_at_n.
  apply elem_of_list_to_map; resolve_finmap.
  - apply Nat2N.inj in H0. subst.
    rewrite Helem0 in Helem.
    by inversion Helem.
  - apply nodup_imap_inj1.
    move => n1 n2 t1 t2 Heq.
    inversion Heq.
    by apply Nat2N.inj in H0.
  - apply elem_of_lookup_imap.
    exists (N.to_nat i), x.
    split.
    + repeat f_equal.
      lia.
    + apply repeat_lookup.
      lia.
Qed.
      
Lemma new_2d_gmap_at_n_lookup_None {T: Type} n i len (x:T):
  N.to_nat i >= len ->
  new_2d_gmap_at_n n len x !! (n, i) = None.
Proof.
  move => HLen.
  unfold new_2d_gmap_at_n.
  apply not_elem_of_list_to_map. move => HContra. resolve_finmap. subst => //=.
  inversion Heq; subst; clear Heq.
  apply lookup_lt_Some in Helem0.
  rewrite repeat_length in Helem0.
  lia.
Qed.
  
Lemma new_2d_gmap_at_n_lookup_None2 {T: Type} n m i len (x:T):
  n <> m ->
  new_2d_gmap_at_n n len x !! (m, i) = None.
Proof.
  move => Hneq.
  unfold new_2d_gmap_at_n.
  apply not_elem_of_list_to_map. move => HContra. resolve_finmap. subst => //=.
  by inversion Heq.
Qed.

Lemma gmap_of_list_2d_append_disjoint {T: Type} l len (x: T):
  new_2d_gmap_at_n (N.of_nat (length l)) len x ##ₘ gmap_of_list_2d l.
Proof.
  apply map_disjoint_spec.
  move => [n i] f1 f2 H1 H2.
  unfold new_2d_gmap_at_n in H1.
  resolve_finmap.
  - rewrite gmap_of_list_2d_lookup in H2.
    rewrite Nat2N.id in H2.
    destruct (_ !! length _ ) eqn: HContra => //. clear H2.
    assert (Some l0 = None) => //.
    rewrite - HContra. clear HContra.
    apply lookup_ge_None.
    lia.
  - apply Nat2N.inj in H1. subst.
    rewrite Helem0 in Helem.
    by inversion Helem.
  - apply nodup_imap_inj1.
    move => n1 n2 t1 t2 Heq.
    inversion Heq.
    by apply Nat2N.inj in H1.
Qed.

Lemma gmap_of_list_2d_append {T: Type} l len (x: T):
  gmap_of_list_2d (l ++ [::repeat x len]) =
  new_2d_gmap_at_n (N.of_nat (length l)) len x ∪ gmap_of_list_2d l.
Proof.
  apply map_eq.
  move => [n i].
  remember_lookup; rewrite gmap_of_list_2d_lookup in Hlookup.
  destruct lookup_res => //=.
  - destruct (_ !! N.to_nat n) eqn:Hlookup2 => //.
    assert (N.to_nat n <= length l) as Hlen.
    {
      apply lookup_lt_Some in Hlookup2.
      rewrite app_length in Hlookup2.
      simpl in Hlookup2.
      lia.
    }
    destruct (decide (N.to_nat n = length l)) => //.
    + rewrite e in Hlookup2.
      rewrite lookup_app_r in Hlookup2; last lia.
      replace (length l - length l) with 0 in Hlookup2; last lia.
      simpl in Hlookup2.
      inversion Hlookup2; subst; clear Hlookup2.
      assert (N.to_nat i < len).
      { apply lookup_lt_Some in Hlookup.
        by rewrite repeat_length in Hlookup.
      }
      apply elem_of_list_lookup_2 in Hlookup.
      apply elem_of_list_In in Hlookup.
      apply repeat_spec in Hlookup. subst.
      symmetry.
      apply lookup_union_Some_l.
      rewrite - e.
      rewrite N2Nat.id.
      apply new_2d_gmap_at_n_lookup.
      lia.
    + assert (N.to_nat n < length l) as Hlenlt; first lia.
      symmetry.
      apply lookup_union_Some_r; first by apply gmap_of_list_2d_append_disjoint.
      rewrite gmap_of_list_2d_lookup.
      rewrite lookup_app_l in Hlookup2; last lia.
      by rewrite Hlookup2.
  - destruct (_ !! N.to_nat n) eqn:Hlookup2 => //.
    + assert (N.to_nat n <= length l) as Hlen.
      {
        apply lookup_lt_Some in Hlookup2.
        rewrite app_length in Hlookup2.
        simpl in Hlookup2.
        lia.
      }
      destruct (decide (N.to_nat n = length l)) => //.
      * rewrite e in Hlookup2.
        rewrite lookup_app_r in Hlookup2; last lia.
        replace (length l - length l) with 0 in Hlookup2; last lia.
        simpl in Hlookup2.
        inversion Hlookup2; subst; clear Hlookup2.
        assert (N.to_nat i >= len).
        { apply lookup_ge_None in Hlookup.
          by rewrite repeat_length in Hlookup.
        }
        symmetry.
        apply lookup_union_None.
        split.
        -- rewrite - e.
          rewrite N2Nat.id.
          apply new_2d_gmap_at_n_lookup_None.
          lia.
        -- rewrite gmap_of_list_2d_lookup.
          assert (N.to_nat n ≥ length l) as Hlen2; first lia.
          apply lookup_ge_None in Hlen2.
          by rewrite Hlen2.
      * assert (N.to_nat n < length l) as Hlenlt; first lia.
        symmetry.
        apply lookup_union_None.
        split.
        -- rewrite new_2d_gmap_at_n_lookup_None2 => //.
          lia.
        -- rewrite gmap_of_list_2d_lookup.
           rewrite lookup_app_l in Hlookup2; last lia.
           by rewrite Hlookup2.
    + clear Hlookup.
      destruct (_ !! N.to_nat n) eqn:Hlookup => //.
      clear Hlookup2.
      apply lookup_ge_None in Hlookup.
      rewrite app_length in Hlookup.
      simpl in Hlookup.
      symmetry.
      apply lookup_union_None.
      split.
      * apply new_2d_gmap_at_n_lookup_None2 => //.
        lia.
      * rewrite gmap_of_list_2d_lookup.
        assert (N.to_nat n >= length l) as Hlen; first lia.
        apply lookup_ge_None in Hlen.
        by rewrite Hlen.
Qed.

Lemma gmap_of_list_2d_insert {T: Type} n i (x: T) (l: list (list T)) (t: list T):
  l !! (N.to_nat n) = Some t ->
  N.to_nat i < length t ->
  <[(n, i) := x]> (gmap_of_list_2d l) = gmap_of_list_2d (<[N.to_nat n := (<[N.to_nat i := x]> t)]> l).
Proof.
  move => HLookup HLen.
  apply map_eq.
  move => [m j].
  unfold gmap_of_table.
  remember_lookup. rewrite gmap_of_list_2d_lookup. symmetry.
  destruct (decide ((n, i) = (m,j))).
  - inversion e; subst; clear e.
    repeat rewrite Nat2N.id.
    rewrite lookup_insert.
    rewrite list_lookup_insert => /=; last by apply lookup_lt_Some in HLookup.
    by rewrite list_lookup_insert.
  - rewrite lookup_insert_ne in Hlookup => //.
    destruct (decide (n = m)); subst.
    + rewrite list_lookup_insert => /=; last by apply lookup_lt_Some in HLookup.
      destruct (decide (i = j)).
      * exfalso. apply n0. subst.
        by repeat rewrite N2Nat.id.
      * rewrite list_lookup_insert_ne; last lia.
        rewrite gmap_of_list_2d_lookup.
        by rewrite HLookup.
    + rewrite list_lookup_insert_ne; last lia.
      by rewrite gmap_of_list_2d_lookup.
Qed.

Lemma gmap_of_table_append_disjoint l len:
  new_2d_gmap_at_n (N.of_nat (length l)) len None ##ₘ gmap_of_table l.
Proof.
  unfold gmap_of_table.
  replace (length l) with (length (table_to_list <$> l)); first by apply gmap_of_list_2d_append_disjoint.
  by rewrite fmap_length.
Qed.

Lemma gmap_of_memory_append_disjoint l len:
  new_2d_gmap_at_n (N.of_nat (length l)) len #00 ##ₘ gmap_of_memory l.
Proof.
  unfold gmap_of_memory.
  replace (length l) with (length (memory_to_list <$> l)); first by apply gmap_of_list_2d_append_disjoint.
  by rewrite fmap_length.
Qed.

Lemma gmap_of_table_append l len:
  gmap_of_table (l ++ [::create_table len]) =
  new_2d_gmap_at_n (N.of_nat (length l)) (N.to_nat len) None ∪ gmap_of_table l.
Proof.
  unfold gmap_of_table, create_table.
  replace (length l) with (length (table_to_list <$> l)); last by rewrite fmap_length.
  rewrite fmap_app => /=.
  by apply gmap_of_list_2d_append.
Qed.

Lemma gmap_of_memory_append l sz sz_lim:
  gmap_of_memory (l ++ [::create_memory sz sz_lim]) =
  new_2d_gmap_at_n (N.of_nat (length l)) (N.to_nat sz) #00 ∪ gmap_of_memory l.
Proof.
  unfold gmap_of_memory, create_memory.
  replace (length l) with (length (memory_to_list <$> l)); last by rewrite fmap_length.
  rewrite fmap_app => /=.
  by apply gmap_of_list_2d_append.
Qed.

Lemma gmap_of_table_insert n i x l t:
  l !! (N.to_nat n) = Some t ->
  N.to_nat i < length t.(table_data) ->
  <[(n, i) := x]> (gmap_of_table l) = gmap_of_table (<[N.to_nat n := {| table_data := (<[N.to_nat i := x]> t.(table_data)); table_max_opt := t.(table_max_opt) |}]> l).
Proof.
  unfold gmap_of_table.
  move => HLookup HLen.
  rewrite list_fmap_insert => /=.
  apply gmap_of_list_2d_insert; last lia.
  rewrite list_lookup_fmap.
  by rewrite HLookup.
Qed.

Lemma insert_take_drop {T: Type} i (l: list T) (x: T):
  i < length l ->
  <[i := x]> l = seq.take i l ++ [::x] ++ seq.drop (i+1) l.  
Proof.
  move: i. induction l => //=; move => i HLen; first lia.
  destruct i => //=; f_equal.
  - by rewrite drop0.
  - assert (i < length l) as H; first lia.
    apply IHl in H.
    by rewrite H.
Qed.
    
Lemma gmap_of_memory_insert n i x l m md':
  l !! (N.to_nat n) = Some m ->
  N.to_nat i < length m.(mem_data).(memory_list.ml_data) ->
  memory_list.mem_update i x m.(mem_data) = Some md' ->
  <[(n, i) := x]> (gmap_of_memory l) = gmap_of_memory (<[ N.to_nat n := {| mem_data := md'; mem_max_opt := m.(mem_max_opt)|} ]> l).
Proof.
  unfold gmap_of_memory.
  move => HLookup HLen Hmemupd.
  unfold memory_list.mem_update in Hmemupd.
  destruct (i <? _)%N eqn:HiLen => //; clear HiLen.
  inversion Hmemupd; subst; clear Hmemupd => /=.
  rewrite list_fmap_insert => /=.
  erewrite gmap_of_list_2d_insert; eauto.
  + repeat f_equal.
    unfold memory_to_list => /=.
    by apply insert_take_drop.
  + rewrite list_lookup_fmap.
    by rewrite HLookup.
Qed.

Lemma nth_error_lookup {T: Type} (l: list T) i:
  nth_error l i = l !! i.
Proof.
  move: i.
  by induction l; move => i; destruct i => //=.
Qed.
  
Axiom mem_length_divisible: forall m,
  (((mem_length m) `div` page_size) * page_size)%N = mem_length m.

Lemma mem_grow_data m n m':
  mem_grow m n = Some m' ->
  m'.(mem_data).(memory_list.ml_data) = (m.(mem_data).(memory_list.ml_data) ++ (repeat (m.(mem_data).(memory_list.ml_init)) (N.to_nat (n*page_size))))%SEQ.
Proof.
  unfold mem_grow, mem_size, mem_length, memory_list.mem_length => //=.
  move => H.
  destruct (mem_max_opt m) in H => //=.
  - destruct (_ <=? n0)%N => //=.
    by inversion H; subst.
  - by inversion H.
Qed.

Lemma mem_grow_length m n m':
  mem_grow m n = Some m' ->
  mem_length m' = (mem_length m + n * page_size)%N.
Proof.
  move => H.
  apply mem_grow_data in H.
  unfold mem_size, mem_length, memory_list.mem_length.
  rewrite H.
  rewrite app_length repeat_length.
  by rewrite Nat2N.inj_add N2Nat.id.
Qed.

Definition mem_grow_appendix (m:memory) (mn: nat) (n:N) : gmap (N*N) byte := list_to_map (imap (fun i x => ((N.of_nat mn, ((N.of_nat i) + (mem_size m) * page_size)%N), x)) (repeat (m.(mem_data).(memory_list.ml_init)) (N.to_nat (n * page_size)))).

Lemma mem_grow_appendix_disjoint m n mn m' mems:
  mn < length mems ->
  mems !! mn = Some m ->
  mem_grow m n = Some m' ->
  (mem_grow_appendix m mn n) ##ₘ gmap_of_memory mems.
Proof.
  move => HLen Hmem Hmemgrow.
  unfold mem_grow_appendix.
  apply map_disjoint_spec.
  move => [i j] x y Hlookup1 Hlookup2.
  unfold gmap_of_memory in Hlookup2.
  resolve_finmap.
  - rewrite gmap_of_list_2d_lookup in Hlookup2.
    rewrite Nat2N.id in Hlookup2.
    destruct ((_ <$> _) !! mn) eqn: HContra => //.
    rewrite list_lookup_fmap in HContra.
    rewrite Hmem in HContra.
    simpl in HContra.
    inversion HContra; subst; clear HContra.
    assert (Some y = None) => //.
    rewrite - Hlookup2. clear Hlookup2.
    apply lookup_ge_None.
    unfold memory_to_list, mem_size.
    rewrite mem_length_divisible.
    unfold mem_length, memory_list.mem_length.
    lia.
  - assert (x1 = x3); first lia.
    subst.
    rewrite Helem0 in Helem.
    by inversion Helem.
  - apply nodup_imap_inj1.
    move => n1 n2 t1 t2 Heq.
    inversion Heq.
    lia.
Qed.
    
Lemma gmap_of_memory_grow m n m' mn mems:
  mn < length mems ->
  mems !! mn = Some m ->
  mem_grow m n = Some m' ->
  (mem_grow_appendix m mn n) ∪ gmap_of_memory mems =
  gmap_of_memory (<[ mn := m' ]> mems).
Proof.
  move => Hlen Hmemlookup Hmemgrow.
  remember (mem_grow_length Hmemgrow) as Hmemlen; clear HeqHmemlen.
  unfold mem_length, memory_list.mem_length in Hmemlen.
  remember (mem_grow_data Hmemgrow) as Hmemgrowdata; clear HeqHmemgrowdata.
  apply map_eq.
  move => [i j].
  unfold gmap_of_memory, mem_grow_appendix.
  rewrite gmap_of_list_2d_lookup.
  rewrite list_lookup_fmap.
  unfold memory_to_list.
  destruct (decide (N.to_nat i = mn)); subst.
  - rewrite list_lookup_insert => //=.
    destruct (decide (N.to_nat j < length m.(mem_data).(memory_list.ml_data))).
    + destruct (_ !! N.to_nat j) eqn:Hl; last by apply lookup_ge_None in Hl; lia.
      apply lookup_union_Some_r; first by eapply mem_grow_appendix_disjoint.
      rewrite gmap_of_list_2d_lookup.
      rewrite list_lookup_fmap.
      rewrite Hmemlookup => //=.
      rewrite Hmemgrowdata in Hl.
      by rewrite lookup_app_l in Hl.
    + destruct (decide (N.to_nat j < length m'.(mem_data).(memory_list.ml_data))).
      * destruct (_ !! N.to_nat j) eqn:Hl; last by apply lookup_ge_None in Hl; lia.
        apply lookup_union_Some_l.
        apply elem_of_list_to_map; resolve_finmap.
        -- assert (x0 = x2); first lia.
           subst.
           by rewrite Helem0 in Helem; inversion Helem.
        -- apply nodup_imap_inj1.
           move => n1 n2 t1 t2 Heq.
           inversion Heq.
           lia.
        -- apply elem_of_lookup_imap.
           rewrite N2Nat.id.
           exists (N.to_nat (j - (mem_size m * page_size))%N), b.
           split.
           ++ repeat f_equal.
              rewrite N2Nat.id.
              unfold mem_size.
              rewrite mem_length_divisible.
              unfold mem_length, memory_list.mem_length.
              lia.
           ++ rewrite Hmemgrowdata in Hl.
              rewrite lookup_app_r in Hl; last lia.
              rewrite - Hl.
              f_equal.
              unfold mem_size.
              rewrite mem_length_divisible.
              unfold mem_length, memory_list.mem_length.
              lia.
      * destruct (_ !! N.to_nat j) eqn:Hl; first by apply lookup_lt_Some in Hl; lia.
        apply lookup_union_None.
        split.
        -- apply not_elem_of_list_to_map.
           move => HContra.
           resolve_finmap; subst => //=.
           inversion Heq; subst; clear Heq.
           apply lookup_lt_Some in Helem0.
           rewrite repeat_length in Helem0.
           apply n1.
           rewrite N2Nat.inj_add Nat2N.id.
           apply N2Nat.inj_iff in Hmemlen.
           rewrite N2Nat.inj_add in Hmemlen.
           repeat rewrite Nat2N.id in Hmemlen.
           rewrite Hmemlen.
           unfold mem_size.
           rewrite mem_length_divisible.
           unfold mem_length, memory_list.mem_length.
           lia.
        -- rewrite gmap_of_list_2d_lookup list_lookup_fmap Hmemlookup => /=.
           apply lookup_ge_None.
           lia.
  - rewrite list_lookup_insert_ne => //=.
    rewrite lookup_union_r.
    + rewrite gmap_of_list_2d_lookup.
      by rewrite list_lookup_fmap.
    + apply not_elem_of_list_to_map.
      move => HContra.
      resolve_finmap; subst => //=.
      inversion Heq; subst; clear Heq.
      lia.
Qed.

(* Old
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

*)
