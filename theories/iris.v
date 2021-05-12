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

(* empty definitions just to enable the tactics in EctxiLanguageMixin as almost all prebuilt
     tactics could only work for EctxilanguageMixin *)
Inductive ectx_item := .

(* as a result, this is just a dummy definition. *)
Definition fill_item (Ki: ectx_item) (e: expr) : expr := e.

Lemma wasm_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split => //.
  - by apply of_to_val.
  - by apply head_step_not_val.
Qed.

(* binary parser also has a Language definition. *)
Canonical Structure wasm_ectxi_lang := EctxiLanguage wasm_mixin.
Canonical Structure wasm_ectx_lang := EctxLanguageOfEctxi wasm_ectxi_lang.
Canonical Structure wasm_lang := LanguageOfEctx wasm_ectx_lang.

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
  destruct K => //.
  unfold fill, ectxi_language.fill_item, fill_item in *. inversion H1.
  destruct H1; subst. repeat eexists. by eauto.
Qed.

Lemma head_step_reducible e σ e' σ':
  head_step e σ [] e' σ' [] ->
  reducible e σ.
Proof.
  intro HRed. unfold reducible => /=.
  exists [], e', σ', []. eapply Ectx_step => /=.
  - instantiate (1 := e). by instantiate (1 := []).
  - by instantiate (1 := e').
  - by [].
Qed.

Lemma hs_red_equiv e σ:
  reducible e σ <-> exists e' σ', head_step e σ [] e' σ' [].
Proof.
  split; first by apply reducible_head_step.
  intro HRed. destruct HRed as [?[??]]. by eapply head_step_reducible.
Qed.

(* Iris formulate its propositions using this 'bi' typeclass (bunched logic) and defined a uPred
     instance. 

   There are a few different notations in parallel for some reason. The first one is

  {{{ P }}} e @ s; E {{{ RET _ ; Q }}}

  s is some 'stuckness' and E is presumably the set of invariant names available (mask). It seems
    that s and E can also be dropped from a tuple in some cases. Another similar tuple is

  [[{ P }]] e @ s; E [[{ RET _ ; Q }]]

  tbh I haven't found the difference between this (with sq brackets and the above (with braces)).
 *)

(*
 [[ ]] -- total wp, can't do much (bad)
 {{ }}
*)
  
Lemma wp_getglobal s E id q v:
  {{{ id ↦ₕ{ q } v }}} (HE_getglobal id) @ s; E
  {{{ RET v; id ↦ₕ{ q } v }}}.
Proof.
  (* Some explanations on proofmode tactics and patterns are available on 
       https://gitlab.mpi-sws.org/iris/iris/blob/master/docs/proof_mode.md *)
  (*
    By doing iStartProof we can see that the triple [[{ P }]] e @ s; E [[{ Q }]] is defined as
    forall x: val -> iPropI Σ, P -* (Q -* x v) -* WP e @ s; E [{ v, x v }].
    x should be thought of as an arbitrary proposition on a value v. So this roughly reads:

    For any proposition Φ on v, if we're on a state where P holds, and Q could imply Φ v, then 
      if we execute e and get v back then Φ v holds.
   *)
  (*
    This iIntros introduces the proposition Φ into Coq context and the two 'ifs' (wands) into
      Iris context and call them Hl and HΦ. So anything inside quotations is going to Iris 
      context while anything inside brackets is going to the Coq context.
  *)
  iIntros (Φ) "Hl HΦ".
  (*
     This lemma seems to be applicable if our instruction is atomic, can take a step, and does 
       not involve concurrency (which is always true in our language). Upon applying the lemma
       we are first asked to prove that the instruction is not a value (trivial). Then we get            
       a very sophisticated expression whose meaning is to be deciphered.
  *)
  iApply wp_lift_atomic_head_step_no_fork; first done.
  (*
    This is just another iIntros although with something new: !>. This !> pattern is for
      removing the ={E}=* from our goal (this symbol represents an update modality).
  *)
  iIntros (σ1 κ κs n) "Hσ !>".
  (* With the new state interpretation by ∗, we can just destruct Hσ and take out the part that
       we want to use. *)
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "[Hhs Ho]".
  (*
    A lot is going on here. The %? pattern in the end actually consists of two things: 
      it should be read as first the %H pattern, which is for moving the destructed hypothesis
      into the Coq context and naming it H; the ? pattern is just saying that this will be
      anonymous (so give it any name). It turns out that it receives a name 'H' as well anyway.

    The iDestruct itself specialises the term (gen_heap_valid with "Hσ Hl") -- called a 'proof 
      mode term' -- and destruct it. It is currently unclear what 'specialise' means. But
      we do have an explanation for what a 'proof mode term' is: the general syntax is

        (H $ t1 ... tn with "spat1 ... spatn")

      where H is a hypothesis or a lemma whose conclusion is of the form P ⊢ Q, the t_i's are 
        for instantiating any quantifiers, and the spat_i's are 'specialization patterns' to 
        instruct how wands and implications are dealt with. In this case, it is like the 
        reverse of what happens in Intros, where we need to provide the lemma with hypotheses
        to remove the wands -- note that the lemma gen_heap_valid is the following:

        gen_heap_ctx σ -* l ↦ { q } v -* ⌜ σ !! l = Some v ⌝

    So we are just providing our Hσ and Hl to help resolve the two assertions before wands.
      Hl is id ↦ { q } v so that fills the second assertion directly. On the other hand,
      Hσ is 

        state_interp σ1 κs n

      which is somewhat similar to the second component of our heapG_irisG construct,
      whatever that heapG_irisG means; but that definition does say:

        state_interp σ κs _ := gen_heap_ctx (gmap_of_state σ);

    So we can see intuitively why Hσ could help to resolve the first assertion (although not 
      knowing what exactly has happened).

    Lastly, note that gmap_of_state σ1 is going to be just our host variable store hs due to
      our dummy definition -- but we haven't destructed σ1, so we should get back a hypothesis 

         (gmap_of_state σ1) !! id = Some (Some v), 

      automatically named H due to the ? pattern, and moved into the Coq context due to the %?
      pattern; the double Some comes from gmap contributing 1 and our definition of (option val)
      contributing one.
   *)
  iDestruct (gen_heap_valid with "Hhs Hl") as %?.
  (*
    The iSplit tactic is easier -- it basically tries to split up P * Q into two, but only when
      one of P or Q is persistent (else we'll have to use iSplitL/iSplitR, and also divide our
      Iris hypothesis into two parts and we can only use one part on each side). 
   *)
  iSplit.
  (* The first part asks to prove that HE_getglobal id actually can reduce further. The proof
      is just normal Coq instead of Iris so is left mostly without comments. *)
  - unfold head_reducible. inv_head_step. iExists [], (HE_value v), (hs, ws, locs), [].
    simpl in *. unfold head_step. repeat iSplit => //.
    (* iPureIntro takes an Iris goal ⌜ P ⌝ into a Coq goal P. *)
    iPureIntro.
    apply purer_headr. by apply pr_getglobal.
  (* The second part asks us to prove that, on all cases where we take a step, we can 
       establish the proposition Φ.
     
     The function 'from_option f y mx' checks what option the mx is: if it's a Some x, then
       return f applied to x; else return y. So in this case we are saying that, if the 
       reduction result e2 is a value v, then we need to prove Φ v; else, if it's not a value,
       we will need to be ready to prove False (why?).
  *)
  - iIntros (e2 σ2 efs Hstep); inv_head_step.
    (* There are two cases -- either the lookup result v is an actual valid value, or a trap. *)
    + repeat iModIntro; repeat (iSplit; first done). iFrame; by iApply "HΦ".
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
  iIntros (Φ) "Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 κ κs n) "Hσ !>".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "[Hhs Ho]".
  iDestruct (gen_heap_valid with "Hhs Hl") as %?.
  (* Dealing with the lookup hypothesis first again. TODO: maybe refactor this into another 
       ltac as well *)
  iSplit.
  - iPureIntro. repeat eexists. by apply pr_setglobal_value.
  - iIntros (v2 σ2 efs Hstep); inv_head_step.
    iModIntro.
    iMod (gen_heap_update with "Hhs Hl") as "[Hhs Hl]".
    iModIntro.
    iSplit => //.
    iSplitR "HΦ Hl" => //; first by iSplitR "Ho" => //.
    by iApply "HΦ".
Qed.
      
Lemma wp_setglobal_trap s E id Ψ:
  {{{ Ψ }}} HE_setglobal id (HE_value HV_trap) @ s; E
  {{{ RET (HV_trap); Ψ }}}.
Proof.
  iIntros (Φ) "Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 κ κs n) "Hσ !>".
  iSplit.
  - unfold head_reducible_no_obs. simpl in *. destruct σ1 as [[hs ws] locs].
    iPureIntro. repeat eexists. by apply pr_setglobal_trap.
  - iIntros (e2 σ2 efs Hstep); inv_head_step.
    repeat iModIntro. repeat (iSplit => //). iFrame. by iApply "HΦ".
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
  inversion Hstep; destruct K; last by []; simpl in *; subst.
  inv_head_step.
  (* We need to manually establish this relation for the next modality to be resolved,
       unlike the proof to wp_bind -- this is because our head_step is not directly the opsem. *)
  assert (prim_step e (hs, s0, locs) [] e' (hs', s', locs') []) as Hprim.
  {
    by apply Ectx_step with (K := []) (e1' := e) (e2' := e').
  }
  (* The pattern "[//]" seems to mean automaitcally deduce the required assumption for 
       elimnating the modality using H (like inserting an eauto). *)
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
  iApply wp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 κ κs m) "Hσ !>".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "[Hhs [Hlocs Ho]]".
  iDestruct (gen_heap_valid with "Hlocs Hl") as %?.
  rewrite gmap_of_list_lookup in H.
  unfold option_map in H.
  remember (locs !! N.to_nat n) as lookup_res eqn:Hlookup; destruct lookup_res; inversion H; subst; clear H.
  iSplit.
  - unfold head_reducible. inv_head_step. iExists [], (HE_value v), (hs, ws, locs), [].
    simpl in *. unfold head_step. repeat iSplit => //.
    iPureIntro.
    apply purer_headr. by apply pr_getlocal. 
  - iIntros (e2 σ2 efs Hstep); inv_head_step.
    + repeat iModIntro; repeat (iSplit; first done).
      rewrite H4 in Hlookup. inversion Hlookup.
      iFrame. by iApply "HΦ".
    + by rewrite H4 in Hlookup.
Qed.

(* This is now very interesting and a bit different to setglobal, since we need to retrieve the
     value to be set from a resource first. *)
Lemma wp_setlocal s E n id w v:
  {{{ n ↦ₗ w ∗ id ↦ₕ v }}} (HE_setlocal n id) @ s; E
  {{{ RET v; n ↦ₗ v }}}.
Proof.
  iIntros (Φ) "[Hl Hh] HΦ".
  iApply wp_lift_atomic_head_step_no_fork; first done.
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
  - unfold head_reducible. inv_head_step. iExists [], (HE_value v), (hs, ws, <[(N.to_nat n) := v]>locs), [].
    simpl in *. unfold head_step. repeat iSplit => //.   
    iPureIntro.
    apply purer_headr. apply pr_setlocal => //.
    by apply lookup_lt_Some with (x := w).
  - iIntros (e2 σ2 efs Hstep); inv_head_step.
    + iModIntro.
      (* Don't just iModIntro again! This would throw the update modality away wastefully. *)
      iMod (gen_heap_update with "Hlocs Hl") as "[Hlocs Hl]".
      simpl.
      repeat iModIntro.
      iSplit => //.
      (* It takes rather long time for Iris to find the correct frame. *)
      iFrame.
      simpl.
      rewrite gmap_of_list_insert => //.
      iSplitL "Hlocs" => //.
      by iApply "HΦ".
    + by rewrite H11 in H.
    + symmetry in Hlookup_locs. apply lookup_lt_Some in Hlookup_locs.
      lia.
Qed.

Print host_expr.

Print HE_if.

(* We now get to some control flow instructions. It's a bit tricky since rules like these
     do not need to be explicitly dealt with in Heaplang, but instead taken automatically by 
     defining it as an evaluation context. We have to see what needs to be done here. For 
     example, the following version doesn't seem to be provable at the moment. *)
Lemma wp_if_true s E id v w e1 e2 P Q:
  v <> HV_wasm_value (VAL_int32 (Wasm_int.int_zero i32m)) ->
  {{{ P }}} e1 @ s; E {{{ RET w; Q }}} ->
  {{{ id ↦ₕ v ∗ P }}} (HE_if id e1 e2) @ s; E
  {{{ RET w; id ↦ₕ v ∗ Q }}}.
Proof.
  move => HNzero HTriple.
  iIntros (Φ) "[Hh HP] HΦ".
  iApply wp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 κ κs m) "Hσ !>".
  destruct σ1 as [[hs ws] locs].
  iSimpl in "Hσ".
  iDestruct "Hσ" as "[Hhs Ho]".
  iDestruct (gen_heap_valid with "Hhs Hh") as %?.
  iSplit.
  - unfold head_reducible. inv_head_step. iExists [], e1, (hs, ws, locs), [].
    simpl in *. unfold head_step. repeat iSplit => //.   
    iPureIntro.
    apply purer_headr. by apply pr_if_true with (hv := v).
  - iIntros (e σ2 efs Hstep); inv_head_step.
    + repeat iModIntro. repeat iSplit => //.
      iFrame.
      unfold from_option.
      destruct (to_val e) eqn:Hval => //.
      * destruct e => //.
        simpl in Hval. inversion Hval; subst; clear Hval.
        assert (w = v0).
        { admit. }
        assert (P = Q).
        { admit. }
        subst. iApply "HΦ". by iFrame.
      * admit. 
    + by rewrite H in H12.
Qed.

  
End lifting.
