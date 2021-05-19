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

Require Import common operations datatypes datatypes_properties.

From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From iris.program_logic Require Export weakestpre total_weakestpre.

Require Import iris_locations iris_base iris_opsem.

Lemma wasm_mixin : LanguageMixin of_val to_val head_step.
Proof.
  split => //.
  - by apply of_to_val.
  - by apply head_step_not_val.
Qed.

Canonical Structure wasm_lang := Language wasm_mixin.

Global Instance Inhabited_wasm_state: Inhabited (language.state wasm_lang) := populate (∅, Build_store_record [::] [::] [::] [::], [::]).

Definition proph_id := unit. (* ??? *)

Class hsG Σ := HsG {
  hs_invG : invG Σ;
  hs_gen_hsG :> gen_heapG id (option val) Σ
}.

Class locG Σ := LocG {
  loc_invG : invG Σ;
  loc_gen_hsG :> gen_heapG N (option val) Σ
}.

Class wfuncG Σ := WFuncG {
  func_invG : invG Σ;
  func_gen_hsG :> gen_heapG N (option function_closure) Σ;
}.

Class wtabG Σ := WTabG {
  tab_invG : invG Σ;
  tab_gen_hsG :> gen_heapG N (option tableinst) Σ;
}.

Class wmemG Σ := WMemG {
  mem_invG : invG Σ;
  mem_gen_hsG :> gen_heapG N (option memory) Σ;
}.

Class wglobG Σ := WGlobG {
  glob_invG : invG Σ;
  glob_gen_hsG :> gen_heapG N (option global) Σ;
}.

Instance heapG_irisG `{hsG Σ, locG Σ, wfuncG Σ, wtabG Σ, wmemG Σ, wglobG Σ} : irisG wasm_lang Σ := {
  iris_invG := hs_invG; (* TODO: determine the correct invariant *)
  state_interp σ κs _ :=
    let (hss, locs) := σ in
    let (hs, s) := hss in
    ((gen_heap_ctx hs) ∗
      (gen_heap_ctx (gmap_of_list locs)) ∗
      (gen_heap_ctx (gmap_of_list s.(s_funcs))) ∗
      (gen_heap_ctx (gmap_of_list s.(s_tables))) ∗
      (gen_heap_ctx (gmap_of_list s.(s_mems))) ∗ (* TODO: change this to some implementation like
arrays *)
      (gen_heap_ctx (gmap_of_list s.(s_globals)))
    )%I;
  fork_post _ := True%I;
                                                                                                  }.

(* This means the proposition that 'the location l of the heap has value v, and we own q of it' 
     (fractional algebra). 
   We really only need either 0/1 permission for our language, though. *)
Notation "i ↦ₕ{ q } v" := (mapsto (L:=id) (V:=option host_value) i q (Some v%V))
                           (at level 20, q at level 5, format "i ↦ₕ{ q } v") : bi_scope.
Notation "i ↦ₕ v" := (mapsto (L:=id) (V:=option host_value) i 1 (Some v%V))
                      (at level 20, format "i ↦ₕ v") : bi_scope.
Notation "n ↦ₗ{ q } v" := (mapsto (L:=N) (V:=option host_value) n q (Some v%V))
                           (at level 20, q at level 5, format "n ↦ₗ{ q } v") : bi_scope.
Notation "n ↦ₗ v" := (mapsto (L:=N) (V:=option host_value) n 1 (Some v%V))
                      (at level 20, format "n ↦ₗ v") : bi_scope.
(* Unfortunately Unicode does not have every letter in the subscript small latin charset, so we 
     will have to fall back on indices for now. *)
Notation "n ↦₁{ q } v" := (mapsto (L:=N) (V:=option function_closure) n q (Some v%V))
                           (at level 20, q at level 5, format "n ↦₁{ q } v") : bi_scope.
Notation "n ↦₁ v" := (mapsto (L:=N) (V:=option function_closure) n 1 (Some v%V))
                      (at level 20, format "n ↦₁ v") : bi_scope.
Notation "n ↦₂{ q } v" := (mapsto (L:=N) (V:=option tableinst) n q (Some v%V))
                           (at level 20, q at level 5, format "n ↦₂{ q } v") : bi_scope.
Notation "n ↦₂ v" := (mapsto (L:=N) (V:=option tableinst) n 1 (Some v%V))
                      (at level 20, format "n ↦₂ v") : bi_scope.
Notation "n ↦₃{ q } v" := (mapsto (L:=N) (V:=option memory) n q (Some v%V))
                           (at level 20, q at level 5, format "n ↦₃{ q } v") : bi_scope.
Notation "n ↦₃ v" := (mapsto (L:=N) (V:=option memory) n 1 (Some v%V))
                      (at level 20, format "n ↦₃ v") : bi_scope.
Notation "n ↦₄{ q } v" := (mapsto (L:=N) (V:=option global) n q (Some v%V))
                           (at level 20, q at level 5, format "n  ↦₄{ q } v") : bi_scope.
Notation "n ↦₄ v" := (mapsto (L:=N) (V:=option global) n 1 (Some v%V))
                      (at level 20, format "n ↦₄ v") : bi_scope.

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

(* The following 3 lemmas establish that reducible in Ectxilanguagemixin is the same as 
     reducible in the sense of taking a head_step in our language, due to having an empty
     Ectx item only. *)
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
     value to be set from a resource first. *)
Lemma wp_setlocal s E n id w v:
  {{{ n ↦ₗ w ∗ id ↦ₕ v }}} (HE_setlocal n id) @ s; E
  {{{ RET v; n ↦ₗ v }}}.
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
      (* It takes rather long time for Iris to find the correct frame. *)
      iFrame.
      simpl.
      rewrite gmap_of_list_insert => //.
      iSplitL "Hlocs" => //.
      iSplit => //. by iApply "HΦ".
    + by rewrite H11 in H.
    + symmetry in Hlookup_locs. apply lookup_lt_Some in Hlookup_locs.
      lia.
Qed.

Print host_expr.

Print HE_if.

Print reducible.

Lemma he_if_reducible: forall id e1 e2 σ,
  @reducible wasm_lang (HE_if id e1 e2) σ.
Proof.
Admitted.

Section IrisNew.

Context `{BiFUpd PROP}.
(*
(* This is a proved lemma in the current newest Iris, but not Iris 3.3. *)
(* Actually neither the lemma it relies on is in Iris 3.3, so we resort to another method to 
     introduce the fupd modality. *)
Lemma fupd_mask_intro E1 E2 (P: PROP) {HAbs: Absorbing P}:
  E2 ⊆ E1 →
  ((|={E2,E1}=> emp) -∗ P) -∗ |={E1,E2}=> P.
Proof.
  intros. etrans; [|by apply fupd_mask_weaken]. by rewrite -fupd_intro.
Qed.*)

End IrisNew.

(* We now get to some control flow instructions. It's a bit tricky since rules like these
     do not need to be explicitly dealt with in Heaplang, but instead taken automatically by 
     defining it as an evaluation context. We have to see what needs to be done here. For 
     example, the following version, albeit sensible, does not seem to be provable at 
     the moment. *)
(* UPD: THIS IS PROVED!!!! *)
(* TODO: ADD DETAILED COMMENTS ON HOW TO RESOLVING FUPD, AND EXPLAIN WHY IT IS HARDER TO DO IT
           IN IRIS 3.3 *)
Lemma wp_if_true s E id v w e1 e2 P Q:
  v <> HV_wasm_value (VAL_int32 (Wasm_int.int_zero i32m)) ->
  {{{ P ∗ id ↦ₕ v }}} e1 @ s; E {{{ RET w; Q }}} ⊢
  {{{ P ∗ id ↦ₕ v }}} (HE_if id e1 e2) @ s; E
  {{{ RET w; Q }}}.
Proof.
  move => HNzero.
  iIntros "#HT".
  iModIntro.
  iIntros (Φ) "[HP Hh] HΦ".
  iApply wp_lift_step => //.
  iIntros (σ1 κ κs n) "Hσ".
  destruct σ1 as [[hs ws] locs].
  simpl in *.
  iDestruct "Hσ" as "[Hhs Ho]".
  iDestruct (gen_heap_valid with "Hhs Hh") as %?.
  (* I really wish we're using the new version of Iris, where we can just apply one of the new
       fupd intro lemmas to get this fupd into a premise. But we don't have that currently. *)
  (* UPD: After some treasure hunting, this is also doable via an iMod! *)
  (* TODO: add comments on resolving this fupd modality. Old version: only do iMod fupd_intro_mask'. New version: either iMod fupd_intro_subseteq or iApply fupd_mask_intro. *)
  (* TODO: update to the current version of Iris -- which involves upgrading Coq to 8.12? *)
  iMod (fupd_intro_mask' E ∅) as "Hfupd"; first by set_solver.
  iModIntro.
  iSplit.
  - iPureIntro. destruct s => //.
    by apply he_if_reducible.
  - iModIntro.
    iIntros (e0 σ2 efs HStep).
    inv_head_step.
    + iMod "Hfupd".
      iModIntro.
      iFrame.
      iApply ("HT" with "[HP Hh]") => //; first by iFrame.
    + by rewrite H in H12.
Qed.
 
End lifting.
