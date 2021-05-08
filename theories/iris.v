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

Require Import common operations datatypes datatypes_properties opsem interpreter binary_format_parser.

Require Import iris_locations iris_base iris_opsem.

From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From iris.bi.lib Require Import fractional.
From iris.base_logic.lib Require Export gen_heap proph_map gen_inv_heap.
From iris.program_logic Require Export weakestpre total_weakestpre.

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
  iris_invG := hs_invG;
  state_interp σ κs _ := let (hss, locs) := σ in
                         let (hs, s) := hss in
                         ((gen_heap_ctx (heap_gmap_of_hs hs)) ∗
                         (gen_heap_ctx (gmap_of_locs locs)) ∗
                         (gen_heap_ctx (gmap_of_store_func s)) ∗
                         (gen_heap_ctx (gmap_of_store_tab s)) ∗
                         (gen_heap_ctx (gmap_of_store_mem s)) ∗
                         (gen_heap_ctx (gmap_of_store_glob s)))%I;
  fork_post z := True%I;
}.

Section lifting.

Context `{!heapG Σ}.

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
  intro H. unfold reducible in H.
  do 4 destruct H as [??].
  inversion H; simpl in *; subst.
  destruct K => //.
  unfold fill, ectxi_language.fill_item, fill_item in *. simpl in *. inversion H2.
  destruct H1; subst. eauto.
Qed.

Lemma head_step_reducible e σ e' σ':
  head_step e σ [] e' σ' [] ->
  reducible e σ.
Proof.
  intro H. unfold reducible => /=.
  exists [], e', σ', []. eapply Ectx_step => /=.
  - instantiate (1 := e). by instantiate (1 := []).
  - by instantiate (1 := e').
  - by [].
Qed.

Lemma hs_red_equiv e σ:
  reducible e σ <-> exists e' σ', head_step e σ [] e' σ' [].
Proof.
  split; first by apply reducible_head_step.
  intros. destruct H as [?[??]]. by eapply head_step_reducible.
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
  {{{ (loc_host_var id) ↦{ q } (hval_val v) }}} (HE_getglobal id) @ s; E
  {{{ RET v; (loc_host_var id) ↦{ q } (hval_val v) }}}.
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
  iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  (* We deal with the lookup hypothesis first. *)
  destruct σ1 as [[hs ws] locs].
  simplify_lookup H.
  remember (hs !! id) as lookup_res.
  destruct lookup_res as [ores|] => //=.
  destruct ores as [ores'|] => //=.
  simpl in H. inversion H; subst; clear H.
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
    + repeat iModIntro; repeat (iSplit; first done). iFrame.
      rewrite H4 in Heqlookup_res.
      inversion Heqlookup_res; subst; clear Heqlookup_res.
      by iApply "HΦ".
    (* But it can't be a trap since we already have full knowledge from H what v should be. *)    
    + by rewrite H4 in Heqlookup_res. (* TODO: fix this bad pattern of using generated H4*)  
Qed.

(* If we have full ownership then we can also set the value of it -- provided that the value
     is not a trap. *)
Lemma wp_setglobal_value s E id w v:
  v <> HV_trap ->
  {{{ (loc_host_var id) ↦ (hval_val w) }}} HE_setglobal id (HE_value v) @ s; E
  {{{ RET v; (loc_host_var id) ↦ (hval_val v) }}}.
Proof.
  intros HNTrap.
  iIntros (Φ) "Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; first done.
  iIntros (σ1 κ κs n) "Hσ !>". iDestruct (gen_heap_valid with "Hσ Hl") as %?.
  (* Dealing with the lookup hypothesis first again. TODO: maybe refactor this into another 
       ltac as well *)
  destruct σ1 as [[hs ws] locs].
  simplify_lookup H.
  remember (hs !! id) as lookup_res.
  destruct lookup_res as [ores|] => //.
  destruct ores as [ores'|] => //.
  simpl in H. inversion H; subst; clear H.
  iSplit.
  - iPureIntro. repeat eexists. by apply pr_setglobal_value.
  - iIntros (v2 σ2 efs Hstep); inv_head_step.
    iModIntro.
    iMod (gen_heap_update with "Hσ Hl") as "[Hσ Hl]".
    repeat rewrite fold_gmap_state.
    rewrite heapg_hs_update.
    iModIntro.
    iSplit => //.
    iSplitL "Hσ" => //.
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

End lifting.
