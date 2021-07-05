From mathcomp Require Import ssreflect ssrbool eqtype seq.

(* There is a conflict between ssrnat and Iris language. *)
(* Also a conflict between ssrnat and stdpp on the notation .* *)

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

Open Scope string_scope.
Open Scope SEQ.
  
Lemma wp_getglobal s E id q v:
  id ↦[host]{ q } v -∗
     WP (HE_getglobal id) @ s; E {{ v', ⌜ v = v' ⌝ ∗ id ↦[host]{ q } v }}.
Proof.
  (* Some explanations on proofmode tactics and patterns are available on 
       https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/proof_mode.md *)
  (* After 2 days the solution is finally found -- need to 'Open Scope string_scope' first. *)
  iIntros "Hl".
  iApply wp_lift_atomic_step => //.
  (*
    This is just another iIntros although with something new: !>. This !> pattern is for
      removing the ={E}=* from our goal (this symbol represents an update modality).
  *)
  iIntros (σ1 ns κ κs nt) "Hσ !>".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "(Hhs & Ho)".
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
    + repeat iModIntro. by iFrame.
    (* But it can't be a trap since we already have full knowledge from H what v should be. *)    
    + by rewrite H5 in H. (* TODO: fix this bad pattern of using generated hypothesis names *)  
Qed.

(* If we have full ownership then we can also set the value of it -- provided that the value
     is not a trap. *)
Lemma wp_setglobal_value s E id w v:
  v <> HV_trap ->
  id ↦[host] w -∗
     WP HE_setglobal id (HE_value v) @ s; E {{ v', ⌜ v = v' ⌝ ∗ id ↦[host] v' }}.
Proof.
  intros HNTrap.
  iIntros "Hl".
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ !>".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "(Hhs & Ho)".
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
    iMod (gen_heap_update with "Hhs Hl") as "(Hhs & Hl)".
    iModIntro.
    by iFrame.
Qed.
      
Lemma wp_setglobal_trap s E id:
  ⊢ WP HE_setglobal id (HE_value HV_trap) @ s; E {{ v, ⌜ v = HV_trap ⌝ }}.
Proof.
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ !>".
  iSplit.
  - destruct s => //.
    iPureIntro. destruct σ1 as [[hs ws] locs].
    apply hs_red_equiv. repeat eexists.
    by apply pr_setglobal_trap.
  - iIntros (e2 σ2 efs Hstep); inv_head_step.
    repeat iModIntro. by iFrame.
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
  iIntros (σ1 ns κ κs nt) "Hσ".
  (* How to resolve this fancy update modality? *)
  (* Update: using iMod is fine, just that in this case Iris doens't automatically
       instantiate the variables for Hev for some reasons. *)
  (* $! means instantiate the hypothesis with the following variables. *)
  iMod ("Hev" $! σ1 ns κ κs nt with "Hσ") as "[% H]".
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
  iMod ("H" $! e' (hs', s', locs') [] with "[//]") as "H". iIntros "!>!>!>".
  iMod "H". iMod "H". repeat iModIntro. iSimpl in "H".
  iDestruct "H" as "(Hheap & H)".
  iSplitL "Hheap"; first by eauto.
  iSplitL; last by eauto.
  iDestruct "H" as "(H & _)".
  (* "[$]" seems to mean 'find the useful hypotheses by yourself', as this can be normally
    resolved by with "Hv H". Interestingly enough, "[//]" won't work. What's the difference? *)
  by iApply ("IH" with "[$]").
  (* Now we've actually proved this thing finally.. *)  
Qed.

(* This is rather easy, following the same idea as getglobal. *)
Lemma wp_getlocal s E n q v:
  n ↦ₗ{ q } v -∗
    WP (HE_getlocal n) @ s; E {{ v', ⌜ v = v' ⌝ ∗ n ↦ₗ{ q } v }}.
Proof.
  iIntros "Hl".
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ms κ κs mt) "Hσ !>".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "(Hhs & Hlocs & Ho)".
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
      by iFrame.
    + by rewrite H4 in Hlookup.
Qed.

(* This is now very interesting and a bit different to setglobal, since we need to retrieve the
     value to be set from a resource first. 
   Note the ownership required for the different types of resources.
*)
Lemma wp_setlocal s E n q id w v:
  n ↦ₗ w ∗ id ↦[host]{ q } v -∗
    WP HE_setlocal n id @ s; E {{ v', ⌜ v = v' ⌝ ∗ n ↦ₗ v ∗ id ↦[host]{ q } v}}.
Proof.
  iIntros "[Hl Hh]".
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ms κ κs mt) "Hσ !>".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "(Hhs & Hlocs & Ho)".
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
      iMod (gen_heap_update with "Hlocs Hl") as "(Hlocs & Hl)".
      simpl.
      repeat iModIntro.
      (* It takes rather long for Iris to find the correct frame. *)
      iFrame.
      simpl.
      rewrite gmap_of_list_insert => //.
      by iSplitL "Hlocs" => //.
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
Lemma wp_if s E id q v e1 e2 Φ:
  v ≠ HV_trap ->
  (id ↦[host]{ q } v ∗ ⌜ v ≠ wasm_zero ⌝ -∗ WP e1 @ s; E {{ Φ }}) -∗
  (id ↦[host]{ q } v ∗ ⌜ v = wasm_zero ⌝ -∗ WP e2 @ s; E {{ Φ }}) -∗
  id ↦[host]{ q } v -∗ WP HE_if id e1 e2 @ s; E {{ Φ }}.
Proof.
  move => HNTrap.
  iIntros "HT HF Hh".
  iApply wp_lift_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "(Hhs & Ho)".
  iDestruct (gen_heap_valid with "Hhs Hh") as %?.
  (* I really wish we're using the new version of Iris, where we can just apply one of the new
       fupd intro lemmas to get this fupd into a premise. But we don't have that currently. *)
  (* UPD: After some treasure hunting, this is also doable in Iris 3.3 via an iMod! *)
  (* TODO: add comments on resolving this fupd modality. Iris 3.3: only do iMod 
       fupd_intro_mask'. New Iris: either iMod fupd_intro_subseteq or iApply fupd_mask_intro. *)
  (* TODO: upgrade to the current version of Iris -- upgrade Coq to 8.12? But need to fix 
       CompCert compilation issues. Maybe better when there's no ongoing changes *)
  iApply fupd_mask_intro; first by set_solver.
  iIntros "Hfupd".
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
      iApply "HT".
      by iFrame.
    + iMod "Hfupd".
      iModIntro.
      iFrame.
      iApply "HF".
      by iFrame.
    + by rewrite H in H12.
Qed.

(* a simper-to-use version that only needs the branch for true. Note that this and the following
     lemma combined form a solution to Exercise 4.9 in ILN. *)
Lemma wp_if_true s E id q v e1 e2 Φ:
  v ≠ HV_trap ->
  v ≠ wasm_zero ->
  (id ↦[host]{ q } v -∗ WP e1 @ s; E {{ Φ }}) -∗
  id ↦[host]{ q } v -∗ WP HE_if id e1 e2 @ s; E {{ Φ }}.
Proof.
  move => HNTrap HNZero.
  iIntros "HT".
  iApply (wp_if with "[HT] []") => //; iIntros "(Hh & %Hv)"; by [iApply "HT" | ].
Qed.

Lemma wp_if_false s E id q e1 e2 Φ:
  (id ↦[host]{ q } wasm_zero -∗ WP e2 @ s; E {{ Φ }}) -∗
  id ↦[host]{ q } wasm_zero -∗ WP HE_if id e1 e2 @ s; E {{ Φ }}.
Proof.
  iIntros "HF".
  iApply (wp_if with "[] [HF]") => //; iIntros "(Hh & %Hv)"; by [ | iApply "HF"].
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
Lemma wp_while s E id e Φ:
  WP HE_if id (HE_seq e (HE_while id e)) (HE_value wasm_zero) @ s; E {{ Φ }} -∗
  WP HE_while id e @ s; E {{ Φ }}.
Proof.
  iIntros "HT".
  iApply wp_lift_pure_step_no_fork.
  - move => σ1. destruct σ1 as [[hs ws] locs].
    destruct s => //.
    apply hs_red_equiv.
    repeat eexists. by apply pr_while.
  - move => κ σ1 e2 σ2 efs HStep.
    by inv_head_step.
  - repeat iModIntro.
    iIntros (κ e2 efs σ HStep).
    by inv_head_step.
Qed.

Lemma wp_new_rec s E (kip: list (field_name * id)) (w: list (field_name * host_value)):
  length kip = length w ->
  ([∗ list] i ↦ p ∈ kip, match p with
                            | (key, id) => (∃ v, ⌜ w !! i = Some (key, v) ⌝ ∗ id ↦[host] v)
                            end)
  -∗ WP HE_new_rec kip @ s; E {{ v, ⌜ v = (HV_record w) ⌝ }}.
Proof.
  move => HLength.
  iIntros "HP".
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "(Hhs & Ho)".
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
                           ∃ v, ⌜w !! i = Some (key, v) ⌝ ∗ ⌜ hs !! id = Some v ⌝ )%I as "%H".
    {
      iIntros (i key id) "%Hlookup".
      iDestruct (big_sepL_lookup with "HP") as "H"; first by apply Hlookup.
      iSimpl.
      iDestruct "H" as (v Hreslookup) "Hid".
      iExists v.
      iSplit => //.
      by iDestruct (gen_heap_valid with "Hhs Hid") as "%".
    }
    inv_head_step; iFrame; iSplit => //.
    + iAssert (⌜ zip kip.*1 hvs = w ⌝)%I as "%Heq".
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
              by simpl in Hgoal.
      }
      by subst.
    + apply those_none in H5.
      resolve_finmap.
      destruct x0. simpl in *.
      apply H in Helem.
      destruct Helem as [v [Heq2 Hlookup]].
      by rewrite Hlookup in Heq.
Qed.

Lemma wp_getfield s E id fieldname kvp v:
  lookup_kvp kvp fieldname = Some v ->
  id ↦[host] (HV_record kvp) -∗
     WP HE_get_field id fieldname @ s; E {{ v', ⌜ v = v' ⌝ ∗ id ↦[host] (HV_record kvp) }}.
Proof.
  move => HkvpLookup.
  iIntros "Hh".
  iApply wp_lift_atomic_step => //.
  iIntros (σ ns κ κs nt) "Hσ !>".
  destruct σ as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "(Hhs & Ho)".
  iDestruct (gen_heap_valid with "Hhs Hh") as "%".
  iSplit.
  - iPureIntro.
    destruct s => //.
    apply hs_red_equiv.
    repeat eexists.
    by eapply pr_getfield.
  - iModIntro.
    iIntros (e2 σ2 efs HStep).
    destruct σ2 as [[hs2 ws2] locs2] => //=.
    iModIntro.
    inv_head_step; by [ iFrame | rewrite H in H11 ].
Qed.

Lemma wp_seq_value s E v e Φ:
  v ≠ HV_trap ->
  WP e @ s; E {{ Φ }} -∗
  WP HE_seq (HE_value v) e @ s; E {{ Φ }}.
Proof.
  move => Hvalue.
  iIntros "HP".
  iApply wp_lift_pure_step_no_fork.
  - move => σ.
    destruct σ as [[hs ws] locs].
    destruct s => //.
    apply hs_red_equiv.
    repeat eexists.
    by apply pr_seq_const.
  - move => κ σ1 e2 σ2 efs HStep.
    by inv_head_step.
  - repeat iModIntro.
    iIntros (κ e2 efs σ HStep).
    by inv_head_step.
Qed.    

Lemma wp_seq s E e1 e2 Φ Ψ:
  (WP e1 @ s; E {{ v, Ψ v }} ∗
  (∀ v, (Ψ v) -∗ WP e2 @ s; E {{ Φ }})) ⊢
  WP HE_seq e1 e2 @ s; E {{ Φ }}.    
Proof.
  iLöb as "IH" forall (E e1 Φ Ψ).
  iIntros "[H1 H2]".
  repeat rewrite wp_unfold /wp_pre /=.
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (to_val e1) as [v|] eqn:He.
  { apply of_to_val in He as <-.
    iMod "H1".
    iApply fupd_mask_intro; first by set_solver.
    iIntros "HMask".
    iSplit.
    - iPureIntro. destruct s => //=.
      apply hs_red_equiv.
      destruct σ as [[??]?].
      repeat eexists.
      by apply pr_seq_const.
    - iIntros (e0 σ2 efs HStep).
      inv_head_step.
      repeat iModIntro.
      iMod "HMask".
      repeat iModIntro.
      iFrame.
      by iApply "H2"; iAssumption.
  }
  iMod ("H1" $! σ ns κ κs nt with "Hσ") as "[% H]".  
  iModIntro; iSplit.
  {
    destruct s; eauto.
    iPureIntro.
    apply hs_red_equiv in H. destruct H as [e' [σ' H]].
    inv_head_step.
    apply hs_red_equiv.
    repeat eexists.
    by apply pr_seq.
  }
  iIntros (e0 σ2 efs Hstep).
  inv_head_step.
  iMod ("H" $! e1' (hs', s', locs') [] with "[//]") as "H". iIntros "!>!>!>".
  iMod "H". iMod "H". repeat iModIntro. iSimpl in "H".
  iDestruct "H" as "[Hheap [H _]]".
  iFrame.
  iSplit => //.
  iApply "IH".
  by iFrame.
Qed.

(* The same seq rule as above, but written in hoare triples. *)
Lemma wp_seq_hoare s E e1 e2 P Q R v w:
  ({{{ P }}} e1 @ s; E {{{ RET v; Q }}} ∗
  {{{ Q }}} e2 @ s; E {{{ RET w; R }}})%I ⊢
  {{{ P }}} HE_seq e1 e2 @ s; E {{{ RET w; R }}}.
Proof.
  iIntros "[#H1 #H2]" (Φ) "!> HP HΦ".
  iApply wp_seq.
  iSplitL "HP HΦ".
  - iApply ("H1" with "HP").
    iIntros "!> HQ".
    (* This is actually subtle: we need to 'carry' all the information to the second part. *)
    instantiate (1 := (fun v => (Q ∗ (R -∗ Φ w)))%I).
    by iFrame.
  - iIntros (v0) "[HQ HΦ]".
    by iApply ("H2" with "HQ").
Qed.

(*
  (* wasm state exprs *)
  | pr_table_create:
    forall hs s locs s' tab len n,
      tab = create_table len ->
      s' = {|s_funcs := s.(s_funcs); s_tables := s.(s_tables) ++ [::tab]; s_mems := s.(s_mems); s_globals := s.(s_globals) |} ->
      n = length s.(s_tables) ->
      pure_reduce hs s locs (HE_wasm_table_create len) hs s' locs (HE_value (HV_wov (WOV_tableref (Mk_tableidx n))))
 *)

(*
  This is another interesting instruction to look at, since it involves creation of a chunk of
    resources at once, so we need something other than gen_heap_alloc.

  It turns out that Iris has a gen_heap_alloc_big for this purpose, but we need to be careful
    when we handle the generated heap gmaps (need a lot of lemmas to prove disjointness etc).

  Note the post-condition specified in universal quantifiers would not be useful
    in proving actual programs, since there's no way to instantiate a universally-quantified
    assertion with multiple instances of variables in general: Note that the following two:
    1. ∀ i ∈ S, P(i) and
    2. [∗ Set] i, P(i)
    are generally not equivalent (although in our case where P(i) is just a points-to predicate
    with P being injective, they are equivalent). We should use the second notation since
    that version allows lookup of individual addresses but not the first.

  We have to use the big_op notations that Iris has defined instead. The following files in Iris
    are references:

  - https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/algebra/big_op.v, especially the start
  - https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/bi/big_op.v

  To get a specific instance from this big_sepM post-condition, use big_sepM_lookup.

  new_2d_gmap_at_n n l x creates a gmap with domain being the set of tuples {(n, j) | 0≤j<l}, 
  with all of them mapped to the same value x.
*)
Lemma wp_table_create len s E:
  ⊢
  (WP HE_wasm_table_create len @ s; E
  {{ fun v => match v with
           | HV_wov (WOV_tableref (Mk_tableidx n)) => [∗ map] p ↦ v ∈ new_2d_gmap_at_n (N.of_nat n) (N.to_nat len) (None: funcelem), p.1↦[wt][p.2] v
           | _ => False
           end
  }})%I.
Proof.
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "(? & ? & ? & Hwt & ?)".
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //.
    apply hs_red_equiv.
    repeat eexists.
    by eapply pr_table_create.
  - iModIntro.
    iIntros (e2 σ2 efs HStep).
    destruct σ2 as [[hs2 ws2] locs2].
    inv_head_step.
    (* gen_heap_alloc_big allocates a chunk of heap at once, which is exactly what we need here.

       https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris/base_logic/lib/gen_heap.v

       Upon applying gen_heap_alloc_big, we need to prove that the interpretation of the 
       additional part is disjoint to the old heap interpretation, then we get a few resources
       provided in the [∗ _] notation.

       We actually also get a 'meta_token' when allocating fresh resources in the heap, meaning
       that 'no meta data has been associated with the namespaces in the mask for the location',
       or whatever that means. It does not seem to be useful here. Maybe it's for dealing with
       opening invariants?
    *)
    iMod (gen_heap_alloc_big with "Hwt") as "(Hwt & Hl & Hm)".
    {
      unfold gmap_of_table.
      instantiate (1 := new_2d_gmap_at_n (N.of_nat (length ws.(s_tables))) (N.to_nat len) None).
      by apply gmap_of_table_append_disjoint.
    }
    iModIntro.
    iFrame.
    iSplitL "Hwt".
    + by rewrite gmap_of_table_append.
    + iSplit => //.
      iApply big_sepM_mono; last by iApply "Hl".
      by move => [i j] x Hlookup.
Qed.

(*
  | pr_table_set:
    forall hs s locs idt n id v tn tab tab' s' fn,
      hs !! idt = Some (HV_wov (WOV_tableref (Mk_tableidx tn))) ->
      s.(s_tables) !! tn = Some tab ->
      hs !! id = Some v ->
      v = HV_wov (WOV_funcref (Mk_funcidx fn)) ->
      tab' = {|table_data := list_insert n (Some fn) tab.(table_data); table_max_opt := tab.(table_max_opt) |} ->
      s' = {|s_funcs := s.(s_funcs); s_tables := list_insert tn tab' s.(s_tables); s_mems := s.(s_mems); s_globals := s.(s_globals) |} ->
      pure_reduce hs s locs (HE_wasm_table_set idt (N_of_nat n) id) hs s' locs (HE_value v)
 *)
Lemma wp_table_set s E idt n id f fn tn:
  let P := (id ↦[host] (HV_wov (WOV_funcref (Mk_funcidx fn))) ∗
      idt ↦[host] (HV_wov (WOV_tableref (Mk_tableidx tn))))%I in
  (P ∗ N.of_nat tn ↦[wt][ n ] f) -∗ WP HE_wasm_table_set idt n id @ s; E {{ v, ⌜ v = (HV_wov (WOV_funcref (Mk_funcidx fn))) ⌝ ∗ P ∗ N.of_nat tn ↦[wt][ n ] (Some fn)}}.
Proof.
  iIntros "[[Hfuncref Htableref] Hfunc]".
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iDestruct "Hσ" as "(Hhs & ? & ? & Hwt & ?)".
  iDestruct (gen_heap_valid with "Hhs Hfuncref") as "%Hfuncref".
  iDestruct (gen_heap_valid with "Hhs Htableref") as "%Htableref".
  iDestruct (gen_heap_valid with "Hwt Hfunc") as "%Hfunc".
  simplify_lookup.
  rewrite list_lookup_fmap in Heq.
  destruct (s_tables _ !! _) eqn:Hlookup => //.
  simpl in Heq. inversion Heq. subst. clear Heq.
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //.
    apply hs_red_equiv.
    repeat eexists.
    eapply pr_table_set => //.
    unfold table_to_list in Hfunc.
    by apply lookup_lt_Some in Hfunc.
  - iIntros "!>" (e2 σ2 efs HStep).
    inv_head_step.
    iMod (gen_heap_update with "Hwt Hfunc") as "[Hwt Hfunc]".
    iModIntro.
    iFrame.
    iSplit => //.
    erewrite gmap_of_table_insert => //; last by rewrite Nat2N.id.
    rewrite Nat2N.id.
    by iFrame.
Qed.
  
(*
  | pr_table_get:
    forall hs s locs idt n tn tab fn,
      hs !! idt = Some (HV_wov (WOV_tableref (Mk_tableidx tn))) ->
      s.(s_tables) !! tn = Some tab ->
      tab.(table_data) !! n = Some (Some fn) ->
      pure_reduce hs s locs (HE_wasm_table_get idt (N_of_nat n)) hs s locs (HE_value (HV_wov (WOV_funcref (Mk_funcidx fn))))
 *)
Lemma wp_table_get s E id n fn tn:
  let P := (id ↦[host] (HV_wov (WOV_tableref (Mk_tableidx tn))) ∗ (N.of_nat tn) ↦[wt][ n ] (Some fn))%I in
  P -∗ WP HE_wasm_table_get id n @ s; E {{ v, ⌜ v = HV_wov (WOV_funcref (Mk_funcidx fn)) ⌝ ∗ P }}.
Proof.
  iIntros "[Htableref Hfunc]".
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iDestruct "Hσ" as "(Hhs & ? & ? & Hwt & ?)".
  iDestruct (gen_heap_valid with "Hhs Htableref") as "%Htableref".
  iDestruct (gen_heap_valid with "Hwt Hfunc") as "%Hfunc".
  simplify_lookup.
  rewrite list_lookup_fmap in Heq.
  destruct (s_tables _ !! _) eqn:Hlookup => //.
  simpl in Heq.
  inversion Heq; subst; clear Heq.
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //.
    apply hs_red_equiv.
    repeat eexists.
    by eapply pr_table_get.
  - iIntros "!>" (e2 σ2 efs HStep).
    inv_head_step.
    iModIntro.
    by iFrame.
Qed.

  (*
  | pr_memory_create:
    forall hs s locs s' sz sz_lim n,
      s' = {|s_funcs := s.(s_funcs); s_tables := s.(s_tables); s_mems := s.(s_mems) ++ [::create_memory sz sz_lim]; s_globals := s.(s_globals) |} ->
      n = length s.(s_mems) ->
      pure_reduce hs s locs (HE_wasm_memory_create sz sz_lim) hs s' locs (HE_value (HV_wov (WOV_memoryref (Mk_memidx n))))
   *)

Lemma wp_memory_create sz sz_lim init_b s E:
  ⊢
  (WP HE_wasm_memory_create sz sz_lim init_b @ s; E
  {{ fun v => match v with
           | HV_wov (WOV_memoryref (Mk_memidx n)) => [∗ map] p ↦ v ∈ new_2d_gmap_at_n (N.of_nat n) (N.to_nat sz) init_b, p.1↦[wm][p.2] v
           | _ => False
           end
  }})%I.
Proof.
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "(? & ? & ? & ? & Hwm & ?)".
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //.
    apply hs_red_equiv.
    repeat eexists.
    by eapply pr_memory_create.
  - iModIntro.
    iIntros (e2 σ2 efs HStep).
    destruct σ2 as [[hs2 ws2] locs2].
    inv_head_step.
    iMod (gen_heap_alloc_big with "Hwm") as "(Hwm & Hl & Hm)".
    {
      instantiate (1 := new_2d_gmap_at_n (N.of_nat (length ws.(s_mems))) (N.to_nat sz) init_b).
      by apply gmap_of_memory_append_disjoint.
    }
    iModIntro.
    iFrame.
    iSplitL "Hwm".
    + by rewrite gmap_of_memory_append.
    + iSplit => //.
      iApply big_sepM_mono; last by iApply "Hl".
      by move => [i j] x Hlookup.
Qed.

(*  
  | pr_memory_set:
    forall hs s locs idm n id md' mn m m' s' b,
      hs !! idm = Some (HV_wov (WOV_memoryref (Mk_memidx mn))) ->
      s.(s_mems) !! mn = Some m ->
      hs !! id = Some (HV_byte b) ->
      memory_list.mem_update n b m.(mem_data) = Some md' ->
      m' = {|mem_data := md'; mem_max_opt := m.(mem_max_opt) |} ->
      s' = {|s_funcs := s.(s_funcs); s_tables := s.(s_tables); s_mems := list_insert mn m' s.(s_mems); s_globals := s.(s_globals) |} ->
      pure_reduce hs s locs (HE_wasm_memory_set idm n id) hs s' locs (HE_value (HV_byte b))
 *)
Lemma wp_memory_set s E idm n id mn b' b:
  let P := (fun xb =>  
      (id ↦[host] (HV_byte b) ∗
      idm ↦[host] (HV_wov (WOV_memoryref (Mk_memidx mn))) ∗
      (N.of_nat mn) ↦[wm][ n ] xb)%I) in
  (P b') -∗ WP HE_wasm_memory_set idm n id @ s; E {{ v, ⌜ v = HV_byte b ⌝ ∗ P b }}.
Proof.
  iIntros "[Hbyte [Hmemref Hmembyte]]".
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iDestruct "Hσ" as "(Hhs & ? & ? & ? & Hwm & ?)".
  iDestruct (gen_heap_valid with "Hhs Hbyte") as "%Hbyte".
  iDestruct (gen_heap_valid with "Hhs Hmemref") as "%Hmemref".
  iDestruct (gen_heap_valid with "Hwm Hmembyte") as "%Hmembyte".
  simplify_lookup.
  rewrite list_lookup_fmap in Heq.
  destruct (s_mems _ !! _) eqn:Hlookup => //.
  simpl in Heq. inversion Heq. subst. clear Heq.
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //.
    apply hs_red_equiv.
    repeat eexists.
    eapply pr_memory_set => //.
    unfold memory_to_list in Hmembyte.
    unfold memory_list.mem_update => /=.
    destruct (n <? _)%N eqn:HLen => //.
    apply lookup_lt_Some in Hmembyte.
    exfalso.
    apply N.ltb_nlt in HLen.
    lia.
  - iIntros "!>" (e2 σ2 efs HStep).
    inv_head_step.
    iMod (gen_heap_update with "Hwm Hmembyte") as "[Hwm Hmembyte]".
    iModIntro.
    iFrame.
    erewrite gmap_of_memory_insert => //=.
    + unfold memory_list.mem_update in H10.
      rewrite Nat2N.id.
      by iFrame.
    + by rewrite Nat2N.id.
    + apply lookup_lt_Some in Hmembyte.
      by unfold memory_to_list in Hmembyte.
Qed.

(*
  | pr_memory_get:
    forall hs s locs idm n b m mn,
      hs !! idm = Some (HV_wov (WOV_memoryref (Mk_memidx mn))) ->
      s.(s_mems) !! mn = Some m ->
      memory_list.mem_lookup n m.(mem_data) = Some b ->
      pure_reduce hs s locs (HE_wasm_memory_get idm n) hs s locs (HE_value (HV_byte b))
 *)
Lemma wp_memory_get s E n id mn b:
  let P :=
  (id ↦[host] (HV_wov (WOV_memoryref (Mk_memidx mn))) ∗
  (N.of_nat mn) ↦[wm][ n ] b)%I in
  P -∗ WP HE_wasm_memory_get id n @ s; E {{ v, ⌜ v = HV_byte b ⌝ ∗ P }}.
Proof.
  iIntros "[Hmemoryref Hbyte]".
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iDestruct "Hσ" as "(Hhs & ? & ? & ? & Hwm & ?)".
  iDestruct (gen_heap_valid with "Hhs Hmemoryref") as "%Hmemoryref".
  iDestruct (gen_heap_valid with "Hwm Hbyte") as "%Hbyte".
  simplify_lookup.
  rewrite list_lookup_fmap in Heq.
  destruct (s_mems _ !! _) eqn:Hlookup => //.
  simpl in Heq.
  inversion Heq; subst; clear Heq.
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //.
    apply hs_red_equiv.
    repeat eexists.
    eapply pr_memory_get; eauto.
    unfold memory_list.mem_lookup.
    by rewrite nth_error_lookup.
  - iIntros "!>" (e2 σ2 efs HStep).
    inv_head_step.
    iModIntro.
    iFrame.
    unfold memory_list.mem_lookup in H12.
    rewrite nth_error_lookup in H12.
    unfold memory_to_list in Hbyte.
    rewrite H12 in Hbyte.
    by inversion Hbyte.
Qed.

(*
  | pr_memory_grow:
    forall hs s s' locs idm n m m' mn,
      hs !! idm = Some (HV_wov (WOV_memoryref (Mk_memidx mn))) ->
      s.(s_mems) !! mn = Some m ->
      mem_grow m n = Some m' ->
      s' = {|s_funcs := s.(s_funcs); s_tables := s.(s_tables); s_mems := list_insert mn m' s.(s_mems); s_globals := s.(s_globals) |} ->
      pure_reduce hs s locs (HE_wasm_memory_grow idm n) hs s' locs (HE_value (HV_wasm_value (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N (mem_size m'))))))
 *)
      
Lemma wp_memory_grow s E idm mn n:
  idm ↦[host] (HV_wov (WOV_memoryref (Mk_memidx mn)))
  ⊢
  (WP HE_wasm_memory_grow idm n @ s; E
  {{ fun v => match v with
           | HV_wasm_value (VAL_int32 v') => ∃ (m: memory), [∗ map] p ↦ v ∈ mem_grow_appendix m mn n, p.1 ↦[wm][ p.2 ] v
           | HV_trap => True
           | _ => False     
           end
  }})%I.
Proof.
  iIntros "Hmemref".
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ !>".
  destruct σ1 as [[hs ws] locs].
  iDestruct "Hσ" as "(Hhs & ? & ? & ? & Hwm & ?)".
  iDestruct (gen_heap_valid with "Hhs Hmemref") as "%Hmemref".
  iSplit.
  - iPureIntro.
    destruct s => //.
    apply hs_red_equiv.
    repeat eexists.
    by eapply pr_memory_grow_fail_nondet; eauto.
  - iIntros "!>" (e2 [[hs' ws'] locs'] efs HStep).
    inv_head_step; last by iFrame.
    iMod (gen_heap_alloc_big with "Hwm") as "(Hwm & Hmembytes & Htoken)".
    {
      instantiate (1 := mem_grow_appendix m mn n).
      eapply mem_grow_appendix_disjoint; eauto.
      by eapply lookup_lt_Some.
    }
    iModIntro. iFrame.
    iSplitL "Hwm".
    + erewrite gmap_of_memory_grow; eauto.
      by eapply lookup_lt_Some.
    + iSplit => //.
      iExists m.
      iApply big_sepM_mono; last by iApply "Hmembytes".
      by move => [i j] x Hlookup.
Qed.

(*
  | pr_globals_create:
    forall hs s locs s' g n,
      s' = {|s_funcs := s.(s_funcs); s_tables := s.(s_tables); s_mems := s.(s_mems); s_globals := s.(s_globals) ++ [::g] |} ->
      n = length s.(s_globals) ->
      pure_reduce hs s locs (HE_wasm_global_create g) hs s' locs (HE_value (HV_wov (WOV_globalref (Mk_globalidx n))))
 *)
(*
  This one is more like new_host_func: we're only creating one item here, unlike table/memory 
    creation which creates a chunk of items at once.
*)
Lemma wp_global_create s E g:
  ⊢
  (WP HE_wasm_global_create g @ s; E
  {{ fun v => match v with
           | HV_wov (WOV_globalref (Mk_globalidx n)) => N.of_nat n ↦[wg] g
           | _ => False
           end
  }})%I.
Proof.
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "(? & ? & ? & ? & ? & Hwg)".
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //.
    apply hs_red_equiv.
    repeat eexists.
    by apply pr_globals_create.
  - iModIntro.
    iIntros (e2 σ2 efs HStep).
    destruct σ2 as [[hs2 ws2] locs2].
    inv_head_step.
    iMod (gen_heap_alloc with "Hwg") as "(Hσ & Hl & Hm)".
    {
      instantiate (1 := N.of_nat (length ws.(s_globals))).
      rewrite gmap_of_list_lookup.
      rewrite Nat2N.id.
      by rewrite lookup_ge_None.
    }
    iModIntro.
    iFrame.
    by rewrite - gmap_of_list_append.
Qed.

(*
  | pr_global_set:
    forall hs s locs gn idg id s' v g g',
      hs !! id = Some (HV_wasm_value v) ->
      hs !! idg = Some (HV_wov (WOV_globalref (Mk_globalidx gn))) ->
      s.(s_globals) !! gn = Some g ->
      g.(g_mut) = MUT_mut ->
      typeof v = typeof (g.(g_val)) ->
      g' = {|g_mut := MUT_mut; g_val := v|} ->
      s' = {|s_funcs := s.(s_funcs); s_tables := s.(s_tables); s_mems := s.(s_mems); s_globals := list_insert gn g' s.(s_globals)|} ->
      pure_reduce hs s locs (HE_wasm_global_set idg id) hs s' locs (HE_value (HV_wasm_value v))
 *)
(*
  For this to succeed we need not only the full ownership of the global, but the mutability of the
    targetted global as well.
 *)
Lemma wp_global_set idg id s E w v gn:
  w.(g_mut) = MUT_mut ->
  typeof v = typeof (w.(g_val)) ->
  let P := (fun xg => (id ↦[host] HV_wasm_value v ∗
      idg ↦[host] HV_wov (WOV_globalref (Mk_globalidx gn)) ∗
      (N.of_nat gn) ↦[wg] xg)%I) in
  P w -∗ WP HE_wasm_global_set idg id @ s; E {{ v', ⌜ v' = HV_wasm_value v ⌝ ∗ P (Build_global MUT_mut v) }}.
Proof.
  move => HMut HType.
  iIntros "[Hwvalue [Hglobalref Hglobal]]".
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iDestruct "Hσ" as "(Hhs & ? & ? & ? & ? & Hwg)".
  iDestruct (gen_heap_valid with "Hhs Hwvalue") as "%Hwvalue".
  iDestruct (gen_heap_valid with "Hhs Hglobalref") as "%Hglobalref".
  iDestruct (gen_heap_valid with "Hwg Hglobal") as "%Hglobal".
  rewrite gmap_of_list_lookup in Hglobal.
  rewrite Nat2N.id in Hglobal.
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //.
    apply hs_red_equiv.
    repeat eexists.
    by eapply pr_global_set.
  - iIntros "!>" (e2 σ2 efs HStep).
    inv_head_step.
    iMod (gen_heap_update with "Hwg Hglobal") as "[Hwg Hglobal]".
    iModIntro.
    iFrame.
    rewrite - gmap_of_list_insert; last by apply lookup_lt_Some in Hglobal; lia.
    rewrite Nat2N.id.
    by iFrame.
Qed.

(*
  | pr_global_get:
    forall hs s locs idg g gn v,
      hs !! idg = Some (HV_wov (WOV_globalref (Mk_globalidx gn))) ->
      g.(g_val) = v ->
      pure_reduce hs s locs (HE_wasm_global_get idg) hs s locs (HE_value (HV_wasm_value v))
 *)
Lemma wp_global_get idg s E g gn:
  let P :=
  (idg ↦[host] HV_wov (WOV_globalref (Mk_globalidx gn)) ∗
  (N.of_nat gn) ↦[wg] g)%I in
  P -∗ WP HE_wasm_global_get idg @ s; E {{ v, ⌜ v = HV_wasm_value g.(g_val) ⌝ ∗ P }}.
Proof.
  iIntros "[Hglobalref Hglobal]".
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iDestruct "Hσ" as "(Hhs & ? & ? & ? & ? & Hwg)".
  iDestruct (gen_heap_valid with "Hhs Hglobalref") as "%Hglobalref".
  iDestruct (gen_heap_valid with "Hwg Hglobal") as "%Hglobal".
  rewrite gmap_of_list_lookup in Hglobal.
  rewrite Nat2N.id in Hglobal.
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //.
    apply hs_red_equiv.
    repeat eexists.
    by eapply pr_global_get.
  - iIntros "!>" (e2 σ2 efs HStep).
    inv_head_step.
    iModIntro.
    by iFrame.
Qed.
      
(*
  | pr_new_host_func:
    forall hs s locs htf locsn e s' n,
      s' = {|s_funcs := s.(s_funcs) ++ [::datatypes_iris.FC_func_host htf locsn e]; s_tables := s.(s_tables); s_mems := s.(s_mems); s_globals := s.(s_globals) |} ->
      n = length s.(s_funcs) ->
      pure_reduce hs s locs (HE_new_host_func htf (N_of_nat locsn) e) hs s' locs (HE_value (HV_wov (WOV_funcref (Mk_funcidx n))))
 *)

Lemma wp_new_host_func s E htf locsn e:
  ⊢
  (WP HE_new_host_func htf (N_of_nat locsn) e @ s; E
  {{ fun v => match v with
           | HV_wov (WOV_funcref (Mk_funcidx n)) => N.of_nat n ↦[wf] FC_func_host htf locsn e
           | _ => False
           end
  }})%I.
Proof.
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "[?[?[Hwf ?]]]".
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //.
    apply hs_red_equiv.
    repeat eexists.
    by apply pr_new_host_func.
  - iModIntro.
    iIntros (e2 σ2 efs HStep).
    destruct σ2 as [[hs2 ws2] locs2].
    inv_head_step.
    iMod (gen_heap_alloc with "Hwf") as "(Hσ & Hl & Hm)".
    {
      instantiate (1 := N.of_nat (length ws.(s_funcs))).
      rewrite gmap_of_list_lookup.
      rewrite Nat2N.id.
      by rewrite lookup_ge_None.
    }
    iModIntro.
    iFrame.
    by rewrite - gmap_of_list_append.
Qed.    
(*

(*
  | pr_host_return:
    forall hs s locsf locs ids e vs tn,
      list_extra.those (fmap (fun id => hs !! id) ids) = Some vs ->
      pure_reduce hs s locsf (HE_host_frame tn locs (HE_seq (HE_return ids) e)) hs s locsf (HE_value (HV_list vs))

  Note that we actually have the list of local variables living in the instruction here...

  This spec is proved, but it sounds a bit weak. For example, no information about the local
     variable is extracted from P and no similar information is obtained in the post condition.
 *)
(* TODO: change this and function call together to use function spec instead *)
Lemma wp_return s E tn locs ids e (vs: list host_value) P:
  length vs = length ids ->
  (∀ n id, ⌜ ids !! n = Some id ⌝ -∗ ∃ v, ⌜ vs !! n = Some v ⌝ ∗ □ (P -∗ id ↦[host] v)) ⊢
  {{{ P }}} (HE_host_frame tn locs (HE_seq (HE_return ids) e)) @ s; E {{{ RET (HV_list vs); True }}}.
Proof.
  move => HLength.
  iIntros "#Href !>" (Φ) "HP HΦ".
  iApply wp_lift_atomic_step => //=.
  iIntros (σ1 ns κ κs nt) "Hσ !>".
  destruct σ1 as [[hs ws] ls].
  iDestruct "Hσ" as "(Hhs & Ho)".
  iSplit.
  - iPureIntro.
    destruct s => //.
    apply hs_red_equiv.
    destruct (those (fmap (fun (id: datatypes_iris.id) => hs !! id) ids)) eqn:Hlookup; repeat eexists.
    + by eapply pr_host_return.
    + by eapply pr_host_return_trap.
  - iIntros "!>" (e2 σ2 efs HStep) "!>".
    destruct σ2 as [[hs2 ws2] locs2].
    iAssert ( ∀ (n: nat) (id: datatypes_iris.id), ⌜ ids !! n = Some id ⌝ -∗
                           ∃ v, ⌜vs !! n = Some v ⌝ ∗ ⌜ hs !! id = Some v ⌝ )%I as "%H".
    {
      iIntros (n id) "Hlookup".
      iAssert ((∃ v, ⌜ vs !! n = Some v ⌝ ∗ □(P -∗ id ↦[host] v))%I) with "[Hlookup]" as "H".
      {
        by iApply "Href".
      }
      iDestruct "H" as (v) "[H1 #H2]".
      iExists v.
      iFrame.
      iDestruct (gen_heap_valid with "Hhs [H2 HP]") as %?; first by iApply "H2".
      by iPureIntro.
    }
    inv_head_step; iFrame; iSplit => //.
    + replace vs0 with vs; first iApply "HΦ" => //.
      apply list_eq.
      move => i.
      destruct (ids !! i) eqn:Hlookup.
      * apply those_lookup with (n := i) in H13.
        unfold option_map in H13.
        symmetry in H13.
        rewrite list_lookup_fmap in H13.
        rewrite Hlookup in H13.
        simpl in H13.
        destruct (vs0 !! i) => //=.
        inversion H13; clear H13.
        apply H in Hlookup.
        destruct Hlookup as [x [Heqvs Heqhs]].
        by rewrite Heqhs.
      * apply those_length in H13.
        rewrite fmap_length in H13.
        apply lookup_ge_None in Hlookup.
        assert (vs !! i = None) as H1.
        { apply lookup_ge_None. by rewrite HLength. }
        assert (vs0 !! i = None).
        { apply lookup_ge_None. by rewrite - H13. }
        by rewrite H1.
    + apply those_none in H13.
      resolve_finmap.
      apply H in Helem0.
      destruct Helem0 as [hv [Heq' Helem]].
      by rewrite Helem in Heq.
Qed.

Lemma he_call_reducible id ids hs ws locs:
  @reducible wasm_lang (HE_call id ids) (hs, ws, locs).
Proof.
  apply hs_red_equiv.
  destruct (hs !! id) eqn: Heqid; last by eapply pr_call_trap1 in Heqid; repeat eexists.
  destruct i; try by eapply pr_call_trap2 in Heqid; repeat eexists.
  destruct w; try by eapply pr_call_trap2 in Heqid; repeat eexists.
  destruct f; try by eapply pr_call_trap2 in Heqid; repeat eexists.
  destruct (ws.(s_funcs) !! n) eqn: Hfref; last by eapply pr_call_trap3 in Hfref; repeat eexists.
  destruct (list_extra.those (fmap (fun id => hs !! id) ids)) eqn: Hvals; last by eapply pr_call_trap4 in Hvals; repeat eexists.
  destruct f.
  - destruct f as [tn tm].
    destruct (list_extra.those (fmap host_value_to_wasm l)) eqn: Hwvs; last by eapply pr_call_wasm_trap1 in Hwvs => //; repeat eexists.
    assert ({tn = fmap typeof l2} + {tn <> fmap typeof l2}); first by decidable_equality.
    destruct H as [H|H]; subst.
    + by eapply pr_call_wasm in Heqid; repeat eexists.
    + by eapply pr_call_wasm_trap2 in H; repeat eexists.
  - destruct f as [tn tm].
    destruct (decide (length ids = length tn)) as [H|H]; subst.
    + by eapply pr_call_host in Hfref; repeat eexists.      
    + by eapply pr_call_host_trap1 in H; repeat eexists.
Qed.

(*
  TODO: delete this and replace with wasm spec once instantiation is done
*)
  (*
Lemma wp_call_wasm id ids vs i s E v Q j tn tm vts bes:
  length ids = length vs ->
  fmap typeof vs = tn ->
  ({{{  id ↦[host] HV_wov (WOV_funcref (Mk_funcidx i)) ∗
  N.of_nat i ↦[wf] FC_func_native j (Tf tn tm) vts bes ∗
  [∗ list] n ↦ idx ∈ ids, (∃ wv, ⌜ vs !! n = Some wv ⌝ ∗ idx ↦[host] HV_wasm_value wv) }}}
    HE_wasm_frame ((v_to_e_list vs) ++ [::AI_invoke i]) @ s; E {{{ RET v; Q }}} ⊢
  {{{  id ↦[host] HV_wov (WOV_funcref (Mk_funcidx i)) ∗
  N.of_nat i ↦[wf] FC_func_native j (Tf tn tm) vts bes ∗
  [∗ list] n ↦ idx ∈ ids, (∃ wv, ⌜ vs !! n = Some wv ⌝ ∗ idx ↦[host] HV_wasm_value wv) }}}
    HE_call id ids @ s; E {{{ RET v; Q }}}).
Proof.
  move => HLen HType.
  iIntros "#HwFrame" (Φ) "!> HP HΦ".
  subst.
  iDestruct "HP" as "(Hfref & Hfbody & Hval)".
  iApply wp_lift_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  iApply fupd_mask_intro; first by set_solver.
  iIntros "Hfupd".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "(Hhs & ? & Hwf & ?)".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    by apply he_call_reducible.
  - iIntros "!>" (e2 σ2 efs HStep).
    iMod "Hfupd".
    iDestruct (gen_heap_valid with "Hhs Hfref") as "%Hfref".
    iDestruct (gen_heap_valid with "Hwf Hfbody") as "%Hfbody".
    iAssert (∀ n idx, ⌜ids !! n = Some idx ⌝ -∗ ∃ wv, ⌜ vs !! n = Some wv ⌝ ∗ ⌜ hs !! idx = Some (HV_wasm_value wv) ⌝)%I as "%Hval".
    { iIntros (n idx H).
      iDestruct (big_sepL_lookup with "Hval") as "Hreslookup"; first by apply H.
      iDestruct "Hreslookup" as (wv) "(%Hvslookup & Hidx)".
      iExists wv.
      iSplit => //.
      by iDestruct (gen_heap_valid with "Hhs Hidx") as "%".
    }
    rewrite gmap_of_list_lookup in Hfbody.
    rewrite Nat2N.id in Hfbody.
    iModIntro.
    inv_head_step; iFrame.
    + replace vs0 with vs; first by iApply ("HwFrame" with "[Hfref Hfbody Hval]"); iFrame.
      apply list_eq. move => n.
      destruct (ids !! n) eqn:Hlookupid.
      * apply those_lookup with (n0 := n) in H6.
        rewrite list_lookup_fmap in H6.
        apply those_lookup with (n0 := n) in H11.
        rewrite list_lookup_fmap in H11. 
        unfold host_value_to_wasm in H11.
        unfold option_map in H6, H11.
        rewrite Hlookupid in H6.
        destruct (vars !! n) as [hv'|] eqn:Hvars => //.
        destruct (vs0 !! n) => //.
        simpl in H6, H11.
        inversion H6; subst; clear H6.
        inversion H11; subst; clear H11.
        destruct hv' => //.
        inversion H2; subst; clear H2.
        rewrite H0 in Hvars.
        apply Hval in Hlookupid.
        destruct Hlookupid as [hv [Heqvs Heqwv]].
        rewrite Heqvs.
        rewrite - H0 in Heqwv.
        by inversion Heqwv.
      * apply lookup_ge_None in Hlookupid.
        assert (length vs <= n); first by rewrite HLen in Hlookupid.
        assert (vs !! n = None) as Hvsn; first by apply lookup_ge_None.
        rewrite Hvsn; clear Hvsn.
        symmetry.
        apply lookup_ge_None.
        replace (length vs0) with (length ids) => //.
        apply those_length in H6, H11. 
        rewrite fmap_length in H6.
        rewrite fmap_length in H11.
        lia.
    + by rewrite Hfref in H10.
    + apply those_none in H10.
      resolve_finmap.
      apply Hval in Helem0.
      destruct Helem0 as [hv [Heqvs Heqwv]].
      by rewrite - Heq in Heqwv.
    + apply those_none in H15.
      resolve_finmap.
      apply those_lookup with (n := x0) in H10.
      rewrite list_lookup_fmap in H10.
      rewrite Helem0 in H10.
      destruct (ids !! x0) eqn: Hids => //.
      simpl in H10.
      inversion H10; subst; clear H10.
      apply Hval in Hids.
      destruct Hids as [hv [Heqvs Heqwv]].
      rewrite Heqwv in H0.
      inversion H0; subst; clear H0.
      by simpl in Heq.
    + exfalso; apply H16; clear H16.
      apply list_eq. move => n.
      repeat rewrite list_lookup_fmap.
      apply those_lookup with (n0 := n) in H6, H11.
      unfold option_map in H6, H11.
      rewrite list_lookup_fmap in H6.
      rewrite list_lookup_fmap in H11.
      destruct (ids !! n) eqn:Hlookupid => //=.
      * unfold host_value_to_wasm in H11.
        destruct (vars !! n) => //.
        destruct (vs0 !! n) => //.
        simpl in H6, H11.
        destruct h => //.
        inversion H6; subst; clear H6.
        inversion H11; subst; clear H11.
        apply Hval in Hlookupid.
        destruct Hlookupid as [hv [Heqvs Heqwv]].
        rewrite - H0 in Heqwv.
        inversion Heqwv; subst; clear Heqwv.
        by rewrite Heqvs.
      * apply lookup_ge_None in Hlookupid.
        destruct (vars !! n) => //.
        simpl in *.
        destruct (vs0 !! n) => //.
        assert (vs !! n = None) as H; last by rewrite H => //.
        apply lookup_ge_None.
        by rewrite - HLen.
Qed.
   *)
  
(*
  | pr_call_host:
    forall hs s ids cl id i n e tf tn tm vars locs,
      hs !! id = Some (HV_wov (WOV_funcref (Mk_funcidx i))) ->
      s.(s_funcs) !! i = Some cl ->
      cl = FC_func_host tf n e ->
      tf = Tf tn tm ->
      list_extra.those (fmap (fun id => hs !! id) ids) = Some vars ->
      length ids = length tn ->
      pure_reduce hs s locs (HE_call id ids) hs s locs (HE_host_frame tm (vars ++ List.repeat wasm_zero (length tm)) e)
 *)

(*
  From HeapLang (https://gitlab.mpi-sws.org/iris/iris/-/blob/master/iris_heap_lang/primitive_laws.v):

  Recursive functions: we do not use this lemmas as it is easier to use Löb
induction directly, but this demonstrates that we can state the expected
reasoning principle for recursive functions, without any visible ▷.
Lemma wp_rec_löb s E f x e Φ Ψ :
  □ ( □ (∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ s; E {{ Φ }}) -∗
     ∀ v, Ψ v -∗ WP (subst' x v (subst' f (rec: f x := e) e)) @ s; E {{ Φ }}) -∗
  ∀ v, Ψ v -∗ WP (rec: f x := e)%V v @ s; E {{ Φ }}.

  So does this mean we won't need a lemma for function invocations at all (since it is easier to
  'use Löb induction directly' when required)? That sounds a bit questionable in our setting.

  We need to be aware that the function stored at id could be changed within the function body, 
    so we can't simply have a spec of the function initially stored at id and go for a lob 
    induction from that like HeapLang does above. Try running the following in JavaScript:

    var x = function (i) {
      console.log('another function')
      if (!i) return;
      x = f;
      x(i-1);
    }

    var f = function (i) {
      console.log(i);
      if (!i) return;
      f = x;
      f(i-1);
    }

    f(5);
 *)
(*
  TODO: ?
  This currently doesn't work
 *)

Lemma wp_call_host id ids hvs i s E Φ tn tm n e:
  length ids = length hvs ->
  length ids = length tn ->
  ( id ↦[host] HV_wov (WOV_funcref (Mk_funcidx i)) ∗
  N.of_nat i ↦[wf] FC_func_host (Tf tn tm) n e ∗
  [∗ list] n ↦ idx ∈ ids, (∃ v, ⌜ hvs !! n = Some v ⌝ ∗ idx ↦[host] v )) ⊢
  □(WP HE_call id ids @ s; E {{ v, Φ v }} -∗ WP HE_host_frame tm (hvs ++ List.repeat wasm_zero (length tm)) e @ s; E {{ v, Φ v }}) -∗
  WP HE_call id ids @ s; E {{ v, Φ v }}.
Proof.
  move => HLen HLenType.
  iIntros "% #HhFrame" (Φ) "!> HP HΦ".
  subst.
  iDestruct "HP" as "[Hfref [Hfbody Hval]]".
  iApply wp_lift_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  iApply fupd_mask_intro; first by set_solver.
  iIntros "Hfupd".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "(Hhs & ? & Hwf & ?)".
  iSplit.
  - iPureIntro.
    destruct s => //=.
    by apply he_call_reducible.
  - iIntros "!>" (e2 σ2 efs HStep).
    iMod "Hfupd".
    iDestruct (gen_heap_valid with "Hhs Hfref") as "%Hfref".
    iDestruct (gen_heap_valid with "Hwf Hfbody") as "%Hfbody".
    iAssert (∀ n idx, ⌜ids !! n = Some idx ⌝ -∗ ∃ hv, ⌜ hvs !! n = Some hv ⌝ ∗ ⌜ hs !! idx = Some hv ⌝)%I as "%Hval".
    { iIntros (n0 idx H).
      iSpecialize ("Hval" $! n0 idx H).
      iDestruct "Hval" as (hv) "[?Hid]".
      iExists hv.
      iFrame.
      by iDestruct (gen_heap_valid with "Hhs Hid") as "%".
    }
    rewrite gmap_of_list_lookup in Hfbody.
    rewrite Nat2N.id in Hfbody.
    iModIntro.
    inv_head_step; iFrame.
    + by rewrite Hfref in H10.
    + apply those_none in H10.
      resolve_finmap.
      apply Hval in Helem0.
      destruct Helem0 as [hv [Heqvs Heqhv]].
      by rewrite - Heq in Heqhv.
    + replace vars with hvs; first by iApply ("HhFrame" with "[Hfref Hfbody Hval]"); iFrame.
      apply list_eq. move => m.
      destruct (ids !! m) eqn:Hlookupid.
      * apply those_lookup with (n0 := m) in H10.
        rewrite list_lookup_fmap in H10.
        unfold option_map in H10.
        rewrite Hlookupid in H10.
        destruct (vars !! m) as [hv|] eqn:Hvars => //.
        simpl in H10.
        inversion H10; subst; clear H10.
        rewrite H0.
        apply Hval in Hlookupid.
        destruct Hlookupid as [hv' [Heqvs Heqhv]].
        rewrite Heqvs.
        rewrite - H0 in Heqhv.
        by inversion Heqhv; subst.
      * apply lookup_ge_None in Hlookupid.
        assert (length hvs <= m); first by rewrite HLen in Hlookupid.
        assert (hvs !! m = None) as Hvsn; first by apply lookup_ge_None.
        rewrite Hvsn; clear Hvsn.
        symmetry.
        apply lookup_ge_None.
        apply those_length in H10.
        rewrite fmap_length in H10.
        lia.
Qed.

Lemma he_binop_reducible op id1 id2 hs ws locs:
  @reducible wasm_lang (HE_binop op id1 id2) (hs, ws, locs).
Proof.
  apply hs_red_equiv.
  destruct (hs !! id1) as [v1|] eqn:Hv1; last by eapply pr_binop_trap2 in Hv1; repeat eexists.
  destruct (hs !! id2) as [v2|] eqn:Hv2; last by eapply pr_binop_trap3 in Hv2; repeat eexists.
  destruct (host_value_to_wasm v1) as [wv1|] eqn:Hwv1 => //=; last by eapply pr_binop_trap4 in Hwv1; repeat eexists.
  destruct (host_value_to_wasm v2) as [wv2|] eqn:Hwv2 => //=; last by eapply pr_binop_trap5 in Hwv2; repeat eexists.
  unfold host_value_to_wasm in Hwv1, Hwv2.
  destruct v1, v2 => //.
  inversion Hwv1; subst; clear Hwv1.
  inversion Hwv2; subst; clear Hwv2.
  destruct (app_binop op wv1 wv2) eqn:Hbinop; [eapply pr_binop_success in Hbinop | eapply pr_binop_trap1 in Hbinop] => //; by repeat eexists.
Qed.
  
Lemma wp_binop s E op v1 v2 v id1 id2:
  app_binop op v1 v2 = Some v ->
  {{{ id1 ↦[host] (HV_wasm_value v1) ∗ id2 ↦[host] (HV_wasm_value v2) }}} HE_binop op id1 id2 @ s; E {{{ RET (HV_wasm_value v); id1 ↦[host] (HV_wasm_value v1) ∗ id2 ↦[host] (HV_wasm_value v2) }}}.
Proof.
  move => Hbinop.
  iIntros (Φ) "[Hv1 Hv2] HΦ".
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "[Hhs ?]".
  iDestruct (gen_heap_valid with "Hhs Hv1") as "%Hv1".
  iDestruct (gen_heap_valid with "Hhs Hv2") as "%Hv2".
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //.
    by apply he_binop_reducible.
  - iIntros "!>" (e2 σ2 efs HStep) "!>".
    inv_head_step; iFrame; try iSplit => //.
    + iApply ("HΦ" with "[Hv1 Hv2]"); by iFrame.
    + by rewrite Hv1 in H11.
    + by rewrite Hv2 in H11.
Qed.

Lemma he_list_concat_reducible id1 id2 hs ws locs:
  @reducible wasm_lang (HE_list_concat id1 id2) (hs, ws, locs).
Proof.
  apply hs_red_equiv.
  destruct (hs !! id1) as [v1|] eqn:Hv1; last by eapply pr_list_concat_trap1 in Hv1; repeat eexists.
  destruct (hs !! id2) as [v2|] eqn:Hv2; last by eapply pr_list_concat_trap2 in Hv2; repeat eexists.
  destruct (host_typeof v1) as [t1|] eqn:Ht1 => //=; try destruct t1; try by eapply pr_list_concat_trap3 in Hv1; repeat eexists => //; rewrite Ht1.
  destruct (host_typeof v2) as [t2|] eqn:Ht2 => //=; try destruct t2; try by eapply pr_list_concat_trap4 in Hv2; repeat eexists => //; rewrite Ht2.
  destruct v1, v2 => //.
  repeat eexists.
  by eapply pr_list_concat.
Qed.

Lemma wp_list_concat s E l1 l2 id1 id2:
  {{{ id1 ↦[host] (HV_list l1) ∗ id2 ↦[host] (HV_list l2) }}} HE_list_concat id1 id2 @ s; E {{{ RET (HV_list (l1 ++ l2)); id1 ↦[host] (HV_list l1) ∗ id2 ↦[host] (HV_list l2) }}}.
Proof.
  iIntros (Φ) "[Hv1 Hv2] HΦ".
  iApply wp_lift_atomic_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "[Hhs ?]".
  iDestruct (gen_heap_valid with "Hhs Hv1") as "%Hv1".
  iDestruct (gen_heap_valid with "Hhs Hv2") as "%Hv2".
  iModIntro.
  iSplit.
  - iPureIntro.
    destruct s => //.
    by apply he_list_concat_reducible.
  - iIntros "!>" (e2 σ2 efs HStep) "!>".
    inv_head_step; iFrame; try iSplit => //.
    + iApply ("HΦ" with "[Hv1 Hv2]"); by iFrame.
    + by rewrite Hv1 in H10.
    + by rewrite Hv2 in H10.
Qed.

(* Note that this is not actually true -- memory_grow is allowed to fail non-det. We
   need a way to deal with that. *)
Axiom wasm_reduce_deterministic: forall hs s f we hs1 s1 f1 we1 hs2 s2 f2 we2,
  wasm_reduce hs s f we hs1 s1 f1 we1 ->
  wasm_reduce hs s f we hs2 s2 f2 we2 ->
  (hs1, s1, f1, we1) = (hs2, s2, f2, we2).

(*
  A bit ugly that we have to do these. Also it's worth note that we now have 3 different 
    list libraries: Coq.List, stdpp, and seq (ssreflect).
*)
Lemma cat_split {T: Type} (l1 l2 l: list T):
  l1 ++ l2 = l ->
  l1 = seq.take (length l1) l /\
  l2 = seq.drop (length l1) l.
Proof.
  move => HCat.
  rewrite - HCat.
  repeat rewrite length_is_size.
  rewrite take_size_cat => //.
  by rewrite drop_size_cat => //.
Qed.
  
Lemma v_to_e_split: forall vs l1 l2,
  l1 ++ l2 = v_to_e_list vs ->
  l1 = v_to_e_list (seq.take (length l1) vs) /\
  l2 = v_to_e_list (seq.drop (length l1) vs).
Proof.
  move => vs l1 l2 H.
  apply cat_split in H.
  destruct H as [H1 H2].
  rewrite v_to_e_take.
  rewrite v_to_e_drop => //.
Qed.
  
Lemma v_to_e_const2: forall vs l,
  l = v_to_e_list vs ->
  ¬ const_list l -> False.
Proof.
  move => vs l H HContra. subst.
  apply HContra.
  by apply v_to_e_is_const_list.
Qed.

Lemma v_to_e_injection vs1 vs2:
  v_to_e_list vs1 = v_to_e_list vs2 ->
  vs1 = vs2.
Proof.
  move: vs2.
  unfold v_to_e_list.
  induction vs1 => //=; move => vs2 H; destruct vs2 => //.
  simpl in H.
  inversion H; subst; clear H.
  apply IHvs1 in H2.
  by f_equal.
Qed.
  
Ltac resolve_v_to_e:=
  match goal with
  | H: _ ++ _ = v_to_e_list _ |- False =>
    let Hl1 := fresh "Hl1" in
    let Hl2 := fresh "Hl2" in
    apply v_to_e_split in H;
    destruct H as [Hl1 Hl2];
    try apply v_to_e_const2 in Hl1 => //; try apply v_to_e_const2 in Hl2 => //
  end.

Lemma v_to_e_list_irreducible: forall vs we,
  ¬ reduce_simple (v_to_e_list vs) we.
Proof.
  move => vs we HContra.
  inversion HContra; try do 5 (destruct vs => //); subst; try resolve_v_to_e.
  - apply lfilled_Ind_Equivalent in H0.
    inversion H0; subst; clear H0.
    by resolve_v_to_e.
Qed.
    
Lemma trap_irreducible: forall we,
  ¬ reduce_simple ([::AI_trap]) we.
Proof.
  move => we HContra.
  inversion HContra; try do 5 (destruct vs => //).
  subst.
  apply lfilled_Ind_Equivalent in H0.
  by inversion H0.
Qed.

Lemma wp_wasm_reduce_simple_det s E we we' Φ:
  reduce_simple we we' ->
  □WP HE_wasm_frame we' @ s; E {{ Φ }} ⊢
  □WP HE_wasm_frame we @ s; E {{ Φ }}.
Proof.
  move => HReduce.
  iIntros "#Hwp".
  iModIntro.
  iApply wp_lift_pure_step_no_fork.
  - move => σ1.
    destruct s => //.
    apply hs_red_equiv.
    destruct σ1 as [[hs ws] locs].
    repeat eexists.
    apply pr_wasm_frame.
    by apply wr_simple.
  - move => κ σ1 e2 σ2 efs HStep.
    inv_head_step => //.
    repeat split => //.
    f_equal.
    assert ((hs', s', empty_frame, we'0) = (hs, s0, empty_frame, we')) as HDet.
    { eapply wasm_reduce_deterministic => //.
      by apply wr_simple. }
    by inversion HDet.
  - iIntros "!>!>!>" (κ e2 efs σ HStep).
    inv_head_step.
    + by apply v_to_e_list_irreducible in HReduce.
    + by apply trap_irreducible in HReduce.
    + replace we' with we'0; first by iAssumption.
      eapply wr_simple in HReduce.
      eapply wasm_reduce_deterministic in H4 => //.
      by inversion H4.
Qed.

(*
| wr_call :
   forall s f i a hs,
     f.(f_inst).(inst_funcs) !! i = Some a ->
     wasm_reduce hs s f [::AI_basic (BI_call i)] hs s f [::AI_invoke a]
 *)

Lemma wp_wasm_call: True.
(*  {{{ P }}} [::AI_basic (BI_call i)] {{{ Q }}}.*)
Admitted.
(*
  | wr_invoke_native :
      forall a cl t1s t2s ts es ves vcs n m k zs s f f' i hs,
        s.(s_funcs) !! a = Some cl ->
        cl = FC_func_native i (Tf t1s t2s) ts es ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length ts = k ->
        length t1s = n ->
        length t2s = m ->
        n_zeros ts = zs ->
        f'.(f_inst) = i ->
        f'.(f_locs) = vcs ++ zs ->
        wasm_reduce hs s f (ves ++ [::AI_invoke a]) hs s f [::AI_local m f' [::AI_basic (BI_block (Tf [::] t2s) es)]]
 *)

Lemma wp_wasm_invoke_native s E a inst t1s t2s ts es ves vcs zs Q v m:
  ves = v_to_e_list vcs ->
  length vcs = length t1s ->
  length t2s = m ->
  n_zeros ts = zs ->
  {{{ N.of_nat a ↦[wf] FC_func_native inst (Tf t1s t2s) ts es }}} HE_wasm_frame ([::AI_local m (Build_frame (vcs ++ zs) inst) [::AI_basic (BI_block (Tf [::] t2s) es)]]) @ s; E {{{ RET v; Q }}} -∗
  {{{ N.of_nat a ↦[wf] FC_func_native inst (Tf t1s t2s) ts es }}} HE_wasm_frame (ves ++ [::AI_invoke a]) @ s; E {{{ RET v; Q }}}.
Proof.
  move => Hves HLen1 HLen2 Hnzero.
  iIntros "#Hprem" (Φ) "!> Hf HΦ".
  iApply wp_lift_step => //.
  iIntros (σ1 ns κ κs nt) "Hσ".
  destruct σ1 as [[hs ws] locs].
  iDestruct "Hσ" as "[? [? [Hwf ?]]]".
  iDestruct (gen_heap_valid with "Hwf Hf") as "%Hfuncref".
  rewrite gmap_of_list_lookup in Hfuncref.
  rewrite Nat2N.id in Hfuncref.
  iApply fupd_mask_intro; first by set_solver.
  iIntros "Hfupd".
  iSplit.
  - iPureIntro.
    destruct s => //.
    apply hs_red_equiv.
    repeat eexists.
    apply pr_wasm_frame.
    by eapply wr_invoke_native with (f' := Build_frame (vcs ++ zs) inst); eauto => //.
  - iIntros "!>" (e2 σ2 efs HStep).
    iMod "Hfupd".
    iModIntro.
    destruct σ2 as [[hs' ws'] locs'] => //=.
    inv_head_step; iFrame.
    + exfalso. symmetry in H4. by resolve_v_to_e.
    + by destruct vcs => //.
    + inversion H4; subst; clear H4 => //=; try do 5 (destruct vcs => //=).
      * admit. (* never happens *)
      * apply concat_cancel_last in H.
        destruct H.
        inversion H1; subst; clear H1.
        apply v_to_e_injection in H. subst.
        rewrite Hfuncref in H0.
        inversion H0; subst; clear H0.
        iFrame.
        replace f' with (Build_frame (vcs ++ n_zeros ts0) (f_inst f')); first by iApply ("Hprem" with "Hf HΦ").
        destruct f'.
        f_equal.
        by simpl in H13.
      * apply concat_cancel_last in H.
        destruct H.
        inversion H1; subst; clear H1.
        by rewrite Hfuncref in H0.
      * apply lfilled_Ind_Equivalent in H0.
        admit. (* never happens *)
Admitted.
(*
  | wr_invoke_host :
    (* TODO: check *)
    forall a cl e tf t1s t2s ves vcs m n s s' f hs hs' vs,
      s.(s_funcs) !! a = Some cl ->
      cl = FC_func_host tf n e ->
      tf = Tf t1s t2s ->
      ves = v_to_e_list vcs ->
      length vcs = n ->
      length t1s = n ->
      length t2s = m ->
      (* TODO: check if this is what we want *)
      fmap (fun x => HV_wasm_value x) vcs = vs ->
      wasm_reduce hs s f (ves ++ [::AI_invoke a]) hs' s' f [::AI_host_frame t1s vs e]
*)
*)
End lifting.
