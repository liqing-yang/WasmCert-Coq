(** Iris bindings **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrbool eqtype seq.

(* There is a conflict between ssrnat and Iris language. *)
(* Also a conflict between ssrnat and stdpp on the notation .* *)
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris.program_logic Require Import language ectx_language ectxi_language.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import common operations_iris datatypes_iris datatypes_properties_iris.
Require Import iris_locations iris_base iris_opsem.

From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From iris.program_logic Require Export weakestpre total_weakestpre.

Lemma wasm_mixin : LanguageMixin of_val to_val head_step.
Proof.
  split => //.
  - by apply of_to_val.
  - by apply head_step_not_val.
Qed.

Canonical Structure wasm_lang := Language wasm_mixin.

Definition proph_id := unit. (* ??? *)

Class hsG Σ := HsG {
  hs_invG : invG Σ;
  hs_gen_hsG :> gen_heapG id iris_val Σ
}.

Class locG Σ := LocG {
  loc_invG : invG Σ;
  loc_gen_hsG :> gen_heapG N iris_val Σ
}.

Class wfuncG Σ := WFuncG {
  func_invG : invG Σ;
  func_gen_hsG :> gen_heapG N function_closure Σ;
}.

Class wtabG Σ := WTabG {
  tab_invG : invG Σ;
  tab_gen_hsG :> gen_heapG N tableinst Σ;
}.

Class wmemG Σ := WMemG {
  mem_invG : invG Σ;
  mem_gen_hsG :> gen_heapG (N*N) byte Σ;
}.

Class wglobG Σ := WGlobG {
  glob_invG : invG Σ;
  glob_gen_hsG :> gen_heapG N global Σ;
}.

Instance heapG_irisG `{hsG Σ, locG Σ, wfuncG Σ, wtabG Σ, wmemG Σ, wglobG Σ} : irisG wasm_lang Σ := {
  iris_invG := hs_invG; (* TODO: determine the correct invariant. Or, do we have any actually? *)
  state_interp σ κs _ :=
    let (hss, locs) := σ in
    let (hs, s) := hss in
    ((gen_heap_ctx hs) ∗
      (gen_heap_ctx (gmap_of_list locs)) ∗
      (gen_heap_ctx (gmap_of_list s.(s_funcs))) ∗
      (gen_heap_ctx (gmap_of_list s.(s_tables))) ∗
      (gen_heap_ctx (gmap_of_mem s.(s_mems))) ∗
      (gen_heap_ctx (gmap_of_list s.(s_globals)))
    )%I;
  fork_post _ := True%I;
                                                                                                  }.

(* This means the proposition that 'the location l of the heap has value v, and we own q of it' 
     (fractional algebra). 
   We really only need either 0/1 permission for our language, though. *)
Notation "i ↦ₕ{ q } v" := (mapsto (L:=id) (V:=host_value) i q v%V)
                           (at level 20, q at level 5, format "i ↦ₕ{ q } v") : bi_scope.
Notation "i ↦ₕ v" := (mapsto (L:=id) (V:=host_value) i 1 v%V)
                      (at level 20, format "i ↦ₕ v") : bi_scope.
Notation "n ↦ₗ{ q } v" := (mapsto (L:=N) (V:=host_value) n q v%V)
                           (at level 20, q at level 5, format "n ↦ₗ{ q } v") : bi_scope.
Notation "n ↦ₗ v" := (mapsto (L:=N) (V:=host_value) n 1 v%V)
                      (at level 20, format "n ↦ₗ v") : bi_scope.
(* Unfortunately Unicode does not have every letter in the subscript small latin charset, so we 
     will have to fall back on indices for now. It's best to use subscripts with 2 letters such
     as wf/wt/wm/wg, but immediately we realize we don't have w in the character set. A 
     workaround is to use some pretty printing macro option in emacs, but that will not be 
     displayed when viewed on github etc. *)
Notation "n ↦₁{ q } v" := (mapsto (L:=N) (V:=function_closure) n q v%V)
                           (at level 20, q at level 5, format "n ↦₁{ q } v") : bi_scope.
Notation "n ↦₁ v" := (mapsto (L:=N) (V:=function_closure) n 1 v%V)
                      (at level 20, format "n ↦₁ v") : bi_scope.
Notation "n ↦₂{ q } v" := (mapsto (L:=N) (V:=tableinst) n q v%V)
                           (at level 20, q at level 5, format "n ↦₂{ q } v") : bi_scope.
Notation "n ↦₂ v" := (mapsto (L:=N) (V:=tableinst) n 1 v%V)
                      (at level 20, format "n ↦₂ v") : bi_scope.
Notation "n [ i ] ↦₃{ q } v" := (mapsto (L:=N*N) (V:=byte) (n, i) q v%V)
                           (at level 20, q at level 5, format "n [ i ] ↦₃{ q } v") : bi_scope.
Notation "n [ i ] ↦₃ v" := (mapsto (L:=N*N) (V:=byte) (n, i) 1 v%V)
                           (at level 20, format "n [ i ] ↦₃ v") : bi_scope.
Notation "n ↦₄{ q } v" := (mapsto (L:=N) (V:=global) n q v%V)
                           (at level 20, q at level 5, format "n  ↦₄{ q } v") : bi_scope.
Notation "n ↦₄ v" := (mapsto (L:=N) (V:=global) n 1 v%V)
                      (at level 20, format "n ↦₄ v") : bi_scope.

Let wasm_zero := HV_wasm_value (VAL_int32 (Wasm_int.int_zero i32m)).

Global Instance wasm_lang_inhabited : Inhabited (language.state wasm_lang) :=
  populate (∅, Build_store_record [::] [::] [::] [::], [::]).

Section lifting.

Context `{!hsG Σ, !locG Σ, !wfuncG Σ, !wtabG Σ, !wmemG Σ, !wglobG Σ}.

Implicit Types σ : state.

Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ _ |- _ =>
     inversion H; subst; clear H
  | H : head_reduce _ ?e _ _ |- _ => (* in our language simply inverting head_step won't produce
     anything meaningful as we just get a head_reduce back, so we need a further inversion.
     Moreover, the resulting pure_reduce also needs one last inversion. *)
    inversion H => //; subst; clear H
  | H : pure_reduce _ _ _ ?e _ _ _ _ |- _ =>
    try (is_var e; fail 1); (* this is the case where we want to avoid inverting if e is a var. *)
    inversion H => //; subst; clear H
  | H : _ = [] /\ _ = [] |- _ => (* this is to resolve the resulting equalities from head_step. *) 
     destruct H
         end.

(* The following 3 lemmas establish that reducible is the same as taking a head_step in our
     language. *)
Lemma reducible_head_step e σ:
  reducible e σ ->
  exists e' σ', head_step e σ [] e' σ' [].
Proof.
  move => HRed. unfold reducible in HRed.
  destruct HRed as [?[?[?[? HRed]]]].
  inversion HRed; simpl in *; subst.
  inv_head_step.
  by repeat eexists.
Qed.

Lemma head_step_reducible e σ e' σ':
  head_step e σ [] e' σ' [] ->
  reducible e σ.
Proof.
  intro HRed. unfold reducible => /=.
  by do 4 eexists.
Qed.

Lemma hs_red_equiv e σ:
  reducible e σ <-> exists e' σ', head_step e σ [] e' σ' [].
Proof.
  split; first by apply reducible_head_step.
  intro HRed. destruct HRed as [?[??]]. by eapply head_step_reducible.
Qed.

Lemma wp_getglobal s E id q v:
  {{{ id ↦ₕ{ q } v }}} (HE_getglobal id) @ s; E
  {{{ RET v; id ↦ₕ{ q } v }}}.
Proof.
  (* Some explanations on proofmode tactics and patterns are available on 
       https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/proof_mode.md *)
  iIntros (Φ) "Hl HΦ".
  iApply wp_lift_atomic_step => //.
  (*
    This is just another iIntros although with something new: !>. This !> pattern is for
      removing the ={E}=* from our goal (this symbol represents an update modality).
  *)
  iIntros (σ1 κ κs n) "Hσ !>".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "[Hhs Ho]".
  iDestruct (gen_heap_valid with "Hhs Hl") as %?.
  iSplit.
  - destruct s => //.
    (* iPureIntro takes an Iris goal ⌜ P ⌝ into a Coq goal P. *)
    iPureIntro.
    apply hs_red_equiv.
    repeat eexists.
    by apply pr_getglobal.
  - iIntros (e2 σ2 efs Hstep); inv_head_step.
    (* There are two cases -- either the lookup result v is an actual valid value, or a trap. *)
    + repeat iModIntro; repeat (iSplit; first done). iFrame. iSplit => //. by iApply "HΦ".
    (* But it can't be a trap since we already have full knowledge from H what v should be. *)    
    + by rewrite H5 in H. (* TODO: fix this bad pattern of using generated hypothesis names *)  
Qed.

(* If we have full ownership then we can also set the value of it -- provided that the value
     is not a trap. *)
Lemma wp_setglobal_value s E id w v:
  v <> HV_trap ->
  {{{ id ↦ₕ w }}} HE_setglobal id (HE_value v) @ s; E
  {{{ RET v; id ↦ₕ v }}}.
Proof.
  intros HNTrap.
  iIntros (Φ) "Hl HΦ". iApply wp_lift_atomic_step => //.
  iIntros (σ1 κ κs n) "Hσ !>".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "[Hhs Ho]".
  iDestruct (gen_heap_valid with "Hhs Hl") as %?.
  (* Dealing with the lookup hypothesis first again. TODO: maybe refactor this into another 
       ltac as well *)
  iSplit.
  - destruct s => //. iPureIntro.
    apply hs_red_equiv. repeat eexists.
    by apply pr_setglobal_value.
  - iIntros (v2 σ2 efs Hstep); inv_head_step.
    iModIntro.
    (* This eliminates the update modality by updating hs *)
    iMod (gen_heap_update with "Hhs Hl") as "[Hhs Hl]".
    iModIntro.
    iFrame.
    iSplit => //.
    by iApply "HΦ".
Qed.
      
Lemma wp_setglobal_trap s E id Ψ:
  {{{ Ψ }}} HE_setglobal id (HE_value HV_trap) @ s; E
  {{{ RET (HV_trap); Ψ }}}.
Proof.
  iIntros (Φ) "Hl HΦ". iApply wp_lift_atomic_step => //.
  iIntros (σ1 κ κs n) "Hσ !>".
  iSplit.
  - destruct s => //.
    iPureIntro. destruct σ1 as [[hs ws] locs].
    apply hs_red_equiv. repeat eexists.
    by apply pr_setglobal_trap.
  - iIntros (e2 σ2 efs Hstep); inv_head_step.
    repeat iModIntro. iFrame. iSplit => //. by iApply "HΦ".
Qed.
 
(* Manually deal with evaluation contexts. Supposedly this proof should be similar to
     wp_bind. *)
(*
  Technically this lemma might be correct without the v ≠ HV_trap, but Hev can't be 
    simplfied without it somehow. Actually will this lemma be true without the v ≠ trap part?
 *)
(*
  {P} e {Q} ≡ P -∗ WP e {Q} ?

  also get unfolded by iStartProof to

  P -∗ (Q -∗ Φ v) -∗ WP e {v. Φ v}

  But page 139 of ILN says they are almost equivalent (and indeed equivalent when e is not a val).
*)
Lemma wp_setglobal_reduce s E id e Ψ Φ:
  WP e @ s; E {{ v, ⌜ v <> HV_trap ⌝ ∗ Ψ v }} ∗
  (∀ v, (( ⌜ v <> HV_trap ⌝ ∗ Ψ v) -∗ WP (HE_setglobal id (HE_value v)) @ s; E {{ Φ }})) ⊢
  WP (HE_setglobal id e) @ s; E {{ Φ }}.
Proof.
  iIntros "[Hev Hv]".
  (*
    iLöb does a Löb induction. In Iris the Löb rule is:
      Q /\ ▷P ⊢ P -> Q ⊢ P

    What iLöb does is basically adding another hypothesis IH which is the entire current goal
      (including the premises), but with a later modality. It is then sufficient to prove the 
      current goal given that the goal holds later -- so Löb induction is a coinduction.
      http://adam.chlipala.net/cpdt/html/Coinductive.html
  *)
  iLöb as "IH" forall (E e Φ).
  rewrite wp_unfold /wp_pre /=.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply fupd_wp. by iApply "Hv". }
  rewrite wp_unfold /wp_pre /=.
  iIntros (σ1 κ κs n) "Hσ".
  (* How to resolve this fancy update modality? *)
  (* Update: using iMod is fine, just that in this case Iris doens't automatically
       instantiate the variables for Hev for some reasons. *)
  (* $! means instantiate the hypothesis with the following variables. *)
  iMod ("Hev" $! σ1 κ κs n with "Hσ") as "[% H]".
  iModIntro; iSplit.
  {
    destruct s; eauto.
    (* There are some weird consequences with our choice of having 0 ectx item while
         still using the ectxi_language framework: reducible is now equivalent to a head_step. *)
    apply hs_red_equiv in H. destruct H as [e' [σ' H]].
    iPureIntro.
    apply hs_red_equiv. exists (HE_setglobal id e'), σ'.
    inv_head_step.
    unfold head_step; repeat split => //.
    by apply pr_setglobal_step.
  }
  iIntros (e2 σ2 efs Hstep).
  inversion Hstep; simpl in *; subst.
  inv_head_step.
  (* The pattern "[//]" seems to mean automaitcally deduce the required assumption for 
       elimnating the modality using H (like inserting an eauto). *)
  (* TODO: I forgot what's going on here. Add comments on how these modalities are resolved. *)
  iMod ("H" $! e' (hs', s', locs') [] with "[//]") as "H". iIntros "!>!>".
  iMod "H". iModIntro. iSimpl in "H".
  iDestruct "H" as "[Hheap H]".
  iSplitL "Hheap"; first by eauto.
  iSplitL; last by eauto.
  iDestruct "H" as "[H _]".
  (* "[$]" seems to mean 'find the useful hypotheses by yourself', as this can be normally
    resolved by with "Hv H". Interestingly enough, "[//]" won't work. What's the difference? *)
  by iApply ("IH" with "[$]").
  (* Now we've actually proved this thing finally.. *)  
Qed.

(* This is rather easy, following the same idea as getglobal. *)
Lemma wp_getlocal s E n q v:
  {{{ n ↦ₗ{ q } v }}} (HE_getlocal n) @ s; E
  {{{ RET v; n ↦ₗ{ q } v }}}.
Proof.
  iIntros (Φ) "Hl HΦ".
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 κ κs m) "Hσ !>".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "[Hhs [Hlocs Ho]]".
  iDestruct (gen_heap_valid with "Hlocs Hl") as %?.
  rewrite gmap_of_list_lookup in H.
  unfold option_map in H.
  remember (locs !! N.to_nat n) as lookup_res eqn:Hlookup; destruct lookup_res; inversion H; subst; clear H.
  iSplit.
  - destruct s => //.
    iPureIntro. apply hs_red_equiv.
    repeat eexists. by apply pr_getlocal. 
  - iIntros (e2 σ2 efs Hstep); inv_head_step.
    + repeat iModIntro; repeat (iSplit; first done).
      rewrite H4 in Hlookup. inversion Hlookup.
      iFrame. iSplit => //. by iApply "HΦ".
    + by rewrite H4 in Hlookup.
Qed.

(* This is now very interesting and a bit different to setglobal, since we need to retrieve the
     value to be set from a resource first. 
   Note the ownership required for the different types of resources.
*)
Lemma wp_setlocal s E n q id w v:
  {{{ n ↦ₗ w ∗ id ↦ₕ{ q } v }}} (HE_setlocal n id) @ s; E
  {{{ RET v; n ↦ₗ v ∗ id ↦ₕ{ q } v}}}.
Proof.
  iIntros (Φ) "[Hl Hh] HΦ".
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 κ κs m) "Hσ !>".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "[Hhs [Hlocs Ho]]".
  (* This is the first case where we have two types of resources in the precondition. We do
       iDestruct on each of them to gather the required information into the Coq context first,
       as the Iris propositions won't be available to use after iPureIntro. *)
  iDestruct (gen_heap_valid with "Hlocs Hl") as %?.
  rewrite gmap_of_list_lookup in H.
  unfold option_map in H.
  remember (locs !! N.to_nat n) as lookup_res eqn:Hlookup_locs; destruct lookup_res; inversion H; subst; clear H.
  iDestruct (gen_heap_valid with "Hhs Hh") as %?.
  iSplit.
  - destruct s => //.
    iPureIntro. apply hs_red_equiv.
    repeat eexists.
    apply pr_setlocal => //.
    by apply lookup_lt_Some with (x := w).
  - iIntros (e2 σ2 efs Hstep); inv_head_step.
    + iModIntro.
      (* Don't just mindlessly iModIntro again! This would waste the update modality, while we 
           need it to get the locs resources modified. *)
      iMod (gen_heap_update with "Hlocs Hl") as "[Hlocs Hl]".
      simpl.
      repeat iModIntro.
      (* It takes rather long for Iris to find the correct frame. *)
      iFrame.
      simpl.
      rewrite gmap_of_list_insert => //.
      iSplitL "Hlocs" => //.
      iSplit => //. iApply "HΦ". by iFrame.
    + by rewrite H11 in H.
    + symmetry in Hlookup_locs. apply lookup_lt_Some in Hlookup_locs.
      lia.
Qed.

Lemma he_if_reducible: forall id e1 e2 σ,
  @reducible wasm_lang (HE_if id e1 e2) σ.
Proof.
  move => id e1 e2 [[hs ws] locs].
  apply hs_red_equiv.
  destruct (hs !! id) as [res|] eqn:Hlookup.
  - destruct (decide (res = HV_wasm_value (VAL_int32 (Wasm_int.int_zero i32m)))); subst.
    + repeat eexists; by eapply pr_if_false.
    + destruct (decide (res = HV_trap)); subst; repeat eexists.
      * by eapply pr_if_trap.
      * by eapply pr_if_true.
  - repeat eexists. by eapply pr_if_none.
Qed.

(* We now get to some control flow instructions. It's a bit tricky since rules like these
     do not need to be explicitly dealt with in Heaplang, but instead taken automatically by 
     defining it as an evaluation context. We have to see what needs to be done here. The proof
     to this should be a standard model to other context-like instructions (seq, etc.). *)
(* TODO: Add detailed comments on how to resolve fupd in both iris 3.3 and new iris *)
Lemma wp_if s E id q v w e1 e2 P Q:
  v ≠ HV_trap ->
  {{{ P ∗ id ↦ₕ{ q } v ∗ ⌜ v ≠ wasm_zero ⌝ }}} e1 @ s; E {{{ RET w; Q }}} ∗
  {{{ P ∗ id ↦ₕ{ q } v ∗ ⌜ v = wasm_zero ⌝ }}} e2 @ s; E {{{ RET w; Q }}} ⊢
  {{{ P ∗ id ↦ₕ{ q } v }}} (HE_if id e1 e2) @ s; E
  {{{ RET w; Q }}}.
Proof.
  move => HNTrap.
  iIntros "[#HT #HF]".
  (* If the goal involves more than one triples (unlike the previous proofs), the conclusion 
       will somehow have a □ modality around. That's not a problem nonetheless since our premises
       are persistent as well. *)
  iModIntro.
  iIntros (Φ) "[HP Hh] HΦ".
  iApply wp_lift_step => //.
  iIntros (σ1 κ κs n) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "[Hhs Ho]".
  iDestruct (gen_heap_valid with "Hhs Hh") as %?.
  (* I really wish we're using the new version of Iris, where we can just apply one of the new
       fupd intro lemmas to get this fupd into a premise. But we don't have that currently. *)
  (* UPD: After some treasure hunting, this is also doable in Iris 3.3 via an iMod! *)
  (* TODO: add comments on resolving this fupd modality. Iris 3.3: only do iMod 
       fupd_intro_mask'. New Iris: either iMod fupd_intro_subseteq or iApply fupd_mask_intro. *)
  (* TODO: upgrade to the current version of Iris -- upgrade Coq to 8.12? But need to fix 
       CompCert compilation issues. Maybe better when there's no ongoing changes *)
  iMod (fupd_intro_mask' E ∅) as "Hfupd"; first by set_solver.
  iModIntro.
  iSplit.
  - iPureIntro. destruct s => //.
    by apply he_if_reducible.
  - iModIntro.
    iIntros (e0 σ2 efs HStep).
    inv_head_step.
    (* There are 4 cases for the lookup result: non-zero/zero/trap/none. trap is automatically
         resolved by the first premise, and none is impossible by the mapsto predicate. *)
    + iMod "Hfupd".
      iModIntro.
      iFrame.
      iApply ("HT" with "[HP Hh]") => //; by iFrame.
    + iMod "Hfupd".
      iModIntro.
      iFrame.
      iApply ("HF" with "[HP Hh]") => //; by iFrame.
    + by rewrite H in H12.
Qed.

(* a simper-to-use version that only needs the branch for true. Note that this and the following
     lemma combined form a solution to Exercise 4.9 in ILN. *)
Lemma wp_if_true s E id q v w e1 e2 P Q:
  v ≠ HV_trap ->
  v ≠ wasm_zero ->
  {{{ P ∗ id ↦ₕ{ q } v }}} e1 @ s; E {{{ RET w; Q }}} ⊢
  {{{ P ∗ id ↦ₕ{ q } v }}} (HE_if id e1 e2) @ s; E
  {{{ RET w; Q }}}.
Proof.
  move => HNTrap HNZero.
  iIntros "#HT".
  iApply wp_if => //.
  iSplit.
  - iModIntro.
    iIntros (Φ) "[HP [Hh Hn0]] HQ".
    iApply ("HT" with "[HP Hh Hn0]"); by iFrame.
  - iModIntro.
    iIntros (Φ) "[? [?%]] ?"; subst => //.
Qed.

Lemma wp_if_false s E id q v e1 e2 P Q:
  {{{ P ∗ id ↦ₕ{ q } wasm_zero }}} e2 @ s; E {{{ RET v; Q }}} ⊢
  {{{ P ∗ id ↦ₕ{ q } wasm_zero }}} (HE_if id e1 e2) @ s; E
  {{{ RET v; Q }}}.
Proof.
  iIntros "#HF".
  iApply wp_if => //.
  iSplit.
  - iModIntro.
    by iIntros (Φ) "[? [?%]] ?" => //.
  - iModIntro.
    iIntros (Φ) "[HP [Hh ?]] HQ".
    iApply ("HF" with "[HP Hh]"); by iFrame.
Qed.

(* 
  Almost the same as if -- actually easier, since there's only one case. 
  We could certainly follow the same proof structure of if. However here we choose another 
    approach, noting that this step is a 'pure' step, in the sense that there is only one
    reduction pathway which does not depend on any resource of the state. Therefore we can apply
    'wp_lift_pure_step' to avoid having to manually opening the states and dealing with fupd 
    modalities.
  Note that we do not actually need any knowledge on the host variable id, since we're delaying
    the lookup to one step later.
*)
Lemma wp_while s E id w e P Q:
  {{{ P }}} (HE_if id (HE_seq e (HE_while id e)) (HE_value wasm_zero)) @ s; E {{{ RET w; Q }}} ⊢
  {{{ P }}} (HE_while id e) @ s; E {{{ RET w; Q }}}.
Proof.
  iIntros "#HT".
  iModIntro.
  iIntros (Φ) "HP HQ".
  iApply wp_lift_pure_step_no_fork.
  - move => σ1. destruct σ1 as [[hs ws] locs].
    destruct s => //.
    apply hs_red_equiv.
    repeat eexists. by apply pr_while.
  - move => κ σ1 e2 σ2 efs HStep.
    by inv_head_step.
  - repeat iModIntro.
    iIntros (κ e2 efs σ) "%".
    inv_head_step.
    iApply ("HT" with "HP"); by iFrame.
Qed.

Lemma those_none: forall {T: Type} (l: list (option T)),
  list_extra.those l = None <-> None ∈ l.
Proof.
  intros.
  rewrite - list_extra.those_those0.
  induction l => //=.
  - split => //.
    unfold elem_of.
    move => HContra.
    by inversion HContra.
  - destruct a => //; rewrite elem_of_cons.
    + unfold option_map.
      destruct (those0 l) eqn:Hthose.
      * split => //.
        move => [H|H]; try by inversion H.
        apply IHl in H.
        by inversion H.
      * split => //. intros _.
        right. by apply IHl.
    + split => //.
      intros _. by left.
Qed.

Lemma those_length: forall {T: Type} (l: list (option T)) (le: list T),
  list_extra.those l = Some le -> length l = length le.
Proof.
  move => T l le H.
  rewrite - list_extra.those_those0 in H.
  move: l le H.
  induction l => //=.
  - move => le H. simpl in H.
    by inversion H.
  - move => le H.
    destruct a => //=.
    unfold option_map in H.
    destruct (those0 _) eqn:H2 => //=.
    inversion H; subst; clear H.
    simpl.
    f_equal.
    by apply IHl.
Qed.
    
Lemma wp_new_rec s E (kip: list (field_name * id)) (w: list (field_name * host_value)) P:
  length kip = length w ->
  (∀ i key id,
      ⌜ kip !! i = Some (key, id) ⌝ -∗
      ∃ v, ⌜ w !! i = Some (key, v)⌝ ∗
      □(P -∗ ( id ↦ₕ v ))) ⊢
  {{{ P }}} (HE_new_rec kip) @ s; E {{{ RET (HV_record w); P }}}.
Proof.
  move => HLength.
  iIntros "#Hkvp".
  iModIntro.
  iIntros (Φ) "HP HQ".
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 κ κs n) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "[Hhs Ho]".
  repeat iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //.
    apply hs_red_equiv.
    destruct (list_extra.those (fmap (fun id => hs !! id) (kip.*2))) eqn:Hkvp; repeat eexists.
    + by eapply pr_new_rec.
    + by eapply pr_new_rec_trap.
  - iModIntro.
    iIntros (e2 σ2 efs HStep).
    repeat iModIntro.
    iAssert ( ∀ (i: nat) (key: field_name) (id: id), ⌜ kip !! i = Some (key, id) ⌝ -∗
                           ∃ v, ⌜w !! i = Some (key, v) ⌝ ∗ ⌜ hs !! id = Some v ⌝ )%I as "%".
    {
      iIntros (i key id) "Hlookup".
      iAssert ((∃ v, ⌜ w !! i = Some (key, v) ⌝ ∗ □(P -∗ id ↦ₕ v))%I) with "[Hlookup]" as "H".
      {
        by iApply "Hkvp".
      }
      iDestruct "H" as (v) "[H1 #H2]".
      iExists v.
      iFrame.
      iDestruct (gen_heap_valid with "Hhs [H2 HP]") as %?; first by iApply "H2".
      by iPureIntro.
    }
    inv_head_step; iFrame; iSplit => //.
    + iAssert (⌜ zip kip.*1 hvs = w ⌝)%I as "%".
      {
        iPureIntro.
        move: kip hvs HLength H H2.
        induction w => //; move => kip hvs HLength H H2.
        * simpl in HLength.
          by destruct kip => //.
        * destruct kip => //=.
          simpl in HLength.
          inversion HLength. clear HLength.
          destruct hvs => //=.
          - simpl in H2.
            apply those_length in H2.
            simpl in H2.
            by inversion H2.
          - destruct p => /=.
            rewrite - list_extra.those_those0 in H2.
            simpl in H2.
            destruct (hs' !! i) eqn: Hlookup => //.
            unfold option_map in H2.
            destruct (those0 _) eqn: H3 => //.
            inversion H2; subst; clear H2.
            rewrite list_extra.those_those0 in H3.
            apply IHw in H3 => //.
            + rewrite H3.
              f_equal.
              assert (exists v, (a :: w) !! 0 = Some (f, v) /\ hs' !! i = Some v) as HL; first by apply H.
              simpl in HL.
              destruct HL as [v [H4 H5]].
              inversion H4; subst; clear H4.
              rewrite H5 in Hlookup. by inversion Hlookup.
            + move => i0 key id Hlookup0.
              assert (exists v, (a :: w) !! (S i0) = Some (key, v) /\ hs' !! id = Some v) as Hgoal.
              { apply H.
                by rewrite lookup_cons_ne_0 => /=. }
              simpl in Hgoal.
              assumption.
      }
      subst. by iApply "HQ".
    + apply those_none in H5.
      resolve_finmap.
      destruct x0. simpl in *.
      apply elem_of_list_lookup in Helem0.
      destruct Helem0 as [i0 Heq0].
      apply H in Heq0.
      destruct Heq0 as [v [Heq2 Hlookup]].
      by rewrite Hlookup in Heq.
Qed.

End lifting.
