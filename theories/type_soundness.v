Require Import common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Program.Equality.

Require Import operations typing datatypes_properties typing opsem.

Definition b_to_a (bes: seq basic_instruction) : seq administrative_instruction :=
  map (fun x => (Basic x)) bes.

Definition a_to_b_single (e: administrative_instruction) : basic_instruction :=
  match e with
  | Basic x => x
  | _ => EConst (ConstInt32 (Wasm_int.Int32.zero))
  end.

Definition a_to_b (es: seq administrative_instruction) : seq basic_instruction :=
  map a_to_b_single es.

Lemma b_a_elim: forall bes es,
    b_to_a bes = es ->
    bes = a_to_b es.
Proof.
  induction bes; move => es H => //=.
  - by rewrite -H.
  - simpl in H. assert (es = b_to_a (a :: bes)) as H1.
    + by rewrite -H.
    + rewrite H1. simpl. f_equal. by apply IHbes.
Qed.   

Definition t_be_value (es: seq basic_instruction) : Prop :=
  const_list (b_to_a es).

Print tc_global.

Print value.

Print value_type.

(* Convert a value to its value_type. *)

Definition v_to_vt (v: value) :=
  match v with
  | ConstInt32 _ => T_i32
  | ConstInt64 _ => T_i64
  | ConstFloat32 _ => T_f32
  | ConstFloat64 _ => T_f64
  end.

(* These two definitions are very questionable *)
Definition v_to_wasm_int_type (v: value) :=
  match v with
  | ConstInt32 _ => i32t
  | ConstInt64 _ => i64t
  | ConstFloat32 _ => i32t
  | ConstFloat64 _ => i64t
  end.

Definition v_to_wasm_float_type (v: value) :=
  match v with
  | ConstInt32 _ => f32t
  | ConstInt64 _ => f64t
  | ConstFloat32 _ => f32t
  | ConstFloat64 _ => f64t
  end.

Definition vs_to_vts (vs: list value) :=
  map v_to_vt vs.

Print instance.

Ltac b_to_a_revert :=
  repeat lazymatch goal with
         | H:  b_to_a ?bes = _ |- _ =>
           apply b_a_elim in H
         end.

(* Maybe there are better/standard tactics for dealing with these, but I didn't find
     anything helpful *)
Lemma extract_list1 : forall {X:Type} (es: seq X) (e1 e2:X),
    es ++ [::e1] = [::e2] ->
    es = [::] /\ e1 = e2.
Proof.
  move => X es e1 e2 H.
  destruct es => //=.
  - split => //=. by inversion H.
  - by destruct es => //=.
Qed.

Lemma extract_list2 : forall {X:Type} (es: seq X) (e1 e2 e3:X),
    es ++ [::e1] = [::e2; e3] ->
    es = [::e2] /\ e1 = e3.
Proof.
  move => X es e1 e2 e3 H.
  destruct es => //=.
  simpl in H. inversion H; subst.
  apply extract_list1 in H2.
  by destruct H2; subst.
Qed.    

Lemma extract_list3 : forall {X:Type} (es: seq X) (e1 e2 e3 e4:X),
    es ++ [::e1] = [::e2; e3; e4] ->
    es = [::e2; e3] /\ e1 = e4.
Proof.
  move => X es e1 e2 e3 e4 H.
  destruct es => //=.
  simpl in H. inversion H; subst.
  apply extract_list2 in H2.
  by destruct H2; subst.
Qed.

(* 
  This is actually very non-trivial to prove, unlike I first thought.
  The main difficulty arises due to the two rules bet_composition and bet_weakening,
    which will apply for EVERY hypothesis of be_typing when doing inversion/induction.
  Moreover, bet_weakening has a reversed inductive structure, so the proof in fact
    required induction (where one would hardly expect an induction here!).
*)
Lemma empty_typing: forall C t1s t2s,
    be_typing C [::] (Tf t1s t2s) ->
    t1s = t2s.
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by destruct es => //=.
  - f_equal.
    by apply IHHType => //=.
Qed.

(*
  These proofs are largely similar.
  A sensible thing to do is to make tactics for all of them.
  However, some of the proofs depend on the previous ones...
*)

Lemma EConst_typing: forall C econst t1s t2s,
    be_typing C [::EConst econst] (Tf t1s t2s) ->
    t2s = t1s ++ [::typeof econst].
Proof.
  move => C econst t1s t2s HType.
  (* The name generated by dependent induction is a bit weird. *)
  dependent induction HType; subst => //=.
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by apply IHHType2 => //=.
  - rewrite - catA. f_equal.
    + move => _ _ H. by subst.
    + by apply IHHType => //=.
Qed.

Lemma EConst2_typing: forall C econst1 econst2 t1s t2s,
    be_typing C [::EConst econst1; EConst econst2] (Tf t1s t2s) ->
    t2s = t1s ++ [::typeof econst1; typeof econst2].
Proof.
  move => C econst1 econst2 t1s t2s HType.
  dependent induction HType; subst => //=.
  - apply extract_list2 in x; destruct x; subst.
    apply EConst_typing in HType1; subst.
    apply EConst_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + move => _ _ H. by subst.
    + by apply IHHType => //=.
Qed.    

Lemma Unop_i_typing: forall C t op t1s t2s,
    be_typing C [::Unop_i t op] (Tf t1s t2s) ->
    t1s = t2s /\ exists ts, t1s = ts ++ [::t].
Proof.
  move => C t op t1s t2s HType.
  dependent induction HType; subst => //=.
  - split => //=. by exists [::].
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    split => //=.
    destruct H0 as [ts' H].
    exists (ts ++ ts').
    rewrite - catA.
    by rewrite H.
Qed.

Lemma Binop_i_typing: forall C t op t1s t2s,
    be_typing C [::Binop_i t op] (Tf t1s t2s) ->
    t1s = t2s ++ [::t] /\ exists ts, t2s = ts ++ [::t].
Proof.
  move => C t op t1s t2s HType.
  dependent induction HType; subst => //=.
  - split => //=. by exists [::].
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    split => //=.
    + destruct H0 as [ts' H].
      by rewrite - catA.
    + destruct H0 as [ts' H].
      exists (ts ++ ts').
      subst.
      by rewrite - catA.  
Qed.

Lemma Binop_f_typing: forall C t op t1s t2s,
    be_typing C [::Binop_f t op] (Tf t1s t2s) ->
    t1s = t2s ++ [::t] /\ exists ts, t2s = ts ++ [::t].
Proof.
  move => C t op t1s t2s HType.
  dependent induction HType; subst => //=.
  - split => //=. by exists [::].
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    split => //=.
    + destruct H0 as [ts' H].
      by rewrite - catA.
    + destruct H0 as [ts' H].
      exists (ts ++ ts').
      subst.
      by rewrite - catA.  
Qed.

Lemma Unop_f_typing: forall C t op t1s t2s,
    be_typing C [::Unop_f t op] (Tf t1s t2s) ->
    t1s = t2s /\ exists ts, t1s = ts ++ [::t].
Proof.
  move => C t op t1s t2s HType.
  dependent induction HType; subst => //=.
  - split => //=. by exists [::].
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    split => //=.
    destruct H0 as [ts' H].
    exists (ts ++ ts').
    rewrite - catA.
    by rewrite H.
Qed.  

Lemma Testop_typing: forall C t op t1s t2s,
    be_typing C [::Testop t op] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::t] /\ t2s = ts ++ [::T_i32].
Proof.
  move => C t op t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::]. 
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Relop_i_typing: forall C t op t1s t2s,
    be_typing C [::Relop_i t op] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::t; t] /\ t2s = ts ++ [::T_i32].
Proof.
  move => C t op t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::]. 
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Relop_f_typing: forall C t op t1s t2s,
    be_typing C [::Relop_f t op] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::t; t] /\ t2s = ts ++ [::T_i32].
Proof.
  move => C t op t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::]. 
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Cvtop_typing: forall C t1 t2 op sx t1s t2s,
    be_typing C [::Cvtop t2 op t1 sx] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::t1] /\ t2s = ts ++ [::t2].
Proof.
  move => C t1 t2 op sx t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::]. 
  - by exists [::]. 
  - apply extract_list1 in x; destruct x; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

(* Some quality of life lemmas *)
Lemma bet_weakening_empty_1: forall C es ts t2s,
    be_typing C es (Tf [::] t2s) ->
    be_typing C es (Tf ts (ts ++ t2s)).
Proof.
  move => C es ts t2s HType.
  assert (be_typing C es (Tf (ts ++ [::]) (ts ++ t2s))); first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

Lemma bet_weakening_empty_2: forall C es ts t1s,
    be_typing C es (Tf t1s [::]) ->
    be_typing C es (Tf (ts ++ t1s) ts).
Proof.
  move => C es ts t1s HType.
  assert (be_typing C es (Tf (ts ++ t1s) (ts ++ [::]))); first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

Lemma concat_cancel_last: forall {X:Type} (l1 l2: seq X) (e1 e2:X),
    l1 ++ [::e1] = l2 ++ [::e2] ->
    l1 = l2 /\ e1 = e2.
Proof.
  move => X l1 l2 e1 e2 H.
  assert (rev (l1 ++ [::e1]) = rev (l2 ++ [::e2])); first by rewrite H.
  repeat rewrite rev_cat in H0. inversion H0.
  rewrite - (revK l1). rewrite H3. split => //. by apply revK.
Qed.

(*
  Unlike the above proofs which have a linear dependent structure therefore hard
    to factorize into a tactic, the following proofs are independent of each other
    and should therefore be easily refactorable.
*)

Ltac invert_be_typing:=
  repeat lazymatch goal with
  | H: (?es ++ [::?e])%list = [::_] |- _ =>
    apply extract_list1 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _] |- _ =>
    apply extract_list2 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _; _] |- _ =>
    apply extract_list3 in H; destruct H; subst
  | H: be_typing _ [:: EConst _] _ |- _ =>
    apply EConst_typing in H; subst
  | H: be_typing _ [:: EConst _; EConst _] _ |- _ =>
    apply EConst2_typing in H; subst
  | H: be_typing _ [::Unop_i _ _] _ |- _ =>
    apply Unop_i_typing in H; destruct H; subst
  | H: be_typing _ [::Unop_f _ _] _ |- _ =>
    apply Unop_f_typing in H; destruct H; subst
  | H: be_typing _ [::Binop_i _ _] _ |- _ =>
    apply Binop_i_typing in H; destruct H; subst
  | H: be_typing _ [::Binop_f _ _] _ |- _ =>
    apply Binop_f_typing in H; destruct H; subst
  | H: be_typing _ [::Testop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Testop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::Relop_i _ _] _ |- _ =>
    apply Relop_i_typing in H; destruct H; subst
  | H: be_typing _ [::Relop_f _ _] _ |- _ =>
    apply Relop_f_typing in H; destruct H; subst
  | H: be_typing _ [::Cvtop _ _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Cvtop_typing in H; destruct H as [ts [H1 H2]]; subst
  end.

(* Both 32bit and 64bit *)
Lemma t_Unop_i_preserve: forall C v iop be tf,
    be_typing C [:: EConst v; Unop_i (v_to_vt v) iop] tf ->
    reduce_simple (b_to_a [::EConst v; Unop_i (v_to_vt v) iop]) (b_to_a [::be]) ->
    be_typing C [::be] tf.
Proof.
  move => C v iop be tf HType HReduce.
  inversion HReduce; b_to_a_revert; subst.
  (* This is actually very troublesome: we have to use induction just because of
       bet_weakening every time...... *)
  - (* ConstInt32 *)
    dependent induction HType; subst.
    + (* Composition -- the right one *)
    invert_be_typing.
    (* Due to the existence of bet_composition and bet_weakening, a direction
         inversion of those be_typing rules won't work. 
       As a result we have to prove them as separate lemmas.
       Is there a way to avoid this? *)
    apply bet_weakening_empty_1.
    replace (typeof (ConstInt32 c)) with (typeof (ConstInt32 (app_unop_i iop c))).
    by apply bet_const.
    + (* Weakening *)
      apply bet_weakening.
      by apply IHHType. 
  - (* ConstInt64 *)
    dependent induction HType; subst.
    + (* Composition -- the right one *)
    invert_be_typing.
    apply bet_weakening_empty_1.
    replace (typeof (ConstInt64 c)) with (typeof (ConstInt64 (app_unop_i iop c)));
      first by apply bet_const.
    + (* Weakening *)
      apply bet_weakening.
      by apply IHHType.
Qed.

(* Both 32bit and 64bit *)
Lemma t_Unop_f_preserve: forall C v fop be tf,
    be_typing C [:: EConst v; Unop_f (v_to_vt v) fop] tf ->
    reduce_simple (b_to_a [::EConst v; Unop_f (v_to_vt v) fop]) (b_to_a [::be]) ->
    be_typing C [::be] tf.
Proof.
  move => C v fop be tf HType HReduce.
  inversion HReduce; b_to_a_revert; subst.
  - (* ConstFloat32 *)
    dependent induction HType; subst.
    + (* Composition -- the right one *)
    invert_be_typing.
    apply bet_weakening_empty_1.
    replace (typeof (ConstFloat32 c)) with (typeof (ConstFloat32 (app_unop_f fop c))).
    by apply bet_const.
    + (* Weakening *)
      apply bet_weakening.
      by apply IHHType. 
  - (* ConstFloat64 *)
    dependent induction HType; subst.
    + (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1.
    replace (typeof (ConstFloat64 c)) with (typeof (ConstFloat64 (app_unop_f fop c))).
    by apply bet_const.
    + (* Weakening *)
      apply bet_weakening.
      by apply IHHType. 
Qed.

Lemma t_Binop_i_preserve_success: forall C v1 v2 iop be tf,
    be_typing C [:: EConst v1; EConst v2; Binop_i (v_to_vt v1) iop] tf ->
    reduce_simple (b_to_a [::EConst v1; EConst v2; Binop_i (v_to_vt v2) iop]) (b_to_a [::be]) ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 iop be tf HType HReduce.
  inversion HReduce; b_to_a_revert; subst.
  - (* ConstInt32 *)
    dependent induction HType; subst.
    + (* Composition *)
      invert_be_typing.
      simpl in H.
      replace t3s with (t1s ++ [::T_i32]).
      -- apply bet_weakening_empty_1.
         by apply bet_const.
      -- (* replace *)
         replace [::T_i32; T_i32] with ([::T_i32] ++ [::T_i32]) in H => //=.
         rewrite catA in H.
         by apply concat_cancel_last in H; destruct H.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
  - (* ConstInt64 *)
    dependent induction HType; subst.
    + (* Composition *)
      invert_be_typing.
      simpl in H.
      replace t3s with (t1s ++ [::T_i64]).
      -- apply bet_weakening_empty_1.
         by apply bet_const.
      -- (* replace *)
         replace [::T_i64; T_i64] with ([::T_i64] ++ [::T_i64]) in H => //=.
         rewrite catA in H.
         by apply concat_cancel_last in H; destruct H.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
Qed.


Lemma t_Binop_f_preserve_success: forall C v1 v2 fop be tf,
    be_typing C [:: EConst v1; EConst v2; Binop_f (v_to_vt v1) fop] tf ->
    reduce_simple (b_to_a [::EConst v1; EConst v2; Binop_f (v_to_vt v2) fop]) (b_to_a [::be]) ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 iop be tf HType HReduce.
  inversion HReduce; b_to_a_revert; subst.
  - (* ConstInt32 *)
    dependent induction HType; subst.
    + (* Composition *)
      invert_be_typing.
      simpl in H.
      replace t3s with (t1s ++ [::T_f32]).
      -- apply bet_weakening_empty_1.
         by apply bet_const.
      -- (* replace *)
         replace [::T_f32; T_f32] with ([::T_f32] ++ [::T_f32]) in H => //=.
         rewrite catA in H.
         by apply concat_cancel_last in H; destruct H.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
  - (* ConstInt64 *)
    dependent induction HType; subst.
    + (* Composition *)
      invert_be_typing.
      simpl in H.
      replace t3s with (t1s ++ [::T_f64]).
      -- apply bet_weakening_empty_1.
         by apply bet_const.
      -- (* replace *)
         replace [::T_f64; T_f64] with ([::T_f64] ++ [::T_f64]) in H => //=.
         rewrite catA in H.
         by apply concat_cancel_last in H; destruct H.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
Qed.

(* It seems very hard to refactor the i32 and i64 cases into one because of
     the polymorphism of app_testop_i. *)
Lemma t_Testop_i32_preserve: forall C c testop tf,
    be_typing C [::EConst (ConstInt32 c); Testop T_i32 testop] tf ->
    be_typing C [::EConst (ConstInt32 (wasm_bool (app_testop_i testop c)))] tf.
Proof.
  move => C c testop tf HType.
  dependent induction HType; subst.
  - (* Composition *)
    invert_be_typing.
    apply concat_cancel_last in H1; destruct H1; subst.
    apply bet_weakening_empty_1. simpl.
    apply bet_const.
  - (* Weakening *)
    apply bet_weakening.
    by apply IHHType.
Qed.

Lemma t_Testop_i64_preserve: forall C c testop tf,
    be_typing C [::EConst (ConstInt64 c); Testop T_i64 testop] tf ->
    be_typing C [::EConst (ConstInt32 (wasm_bool (app_testop_i testop c)))] tf.
Proof.
  move => C c testop tf HType.
  dependent induction HType; subst.
  - (* Composition *)
    invert_be_typing.
    apply concat_cancel_last in H1; destruct H1; subst.
    apply bet_weakening_empty_1. simpl.
    apply bet_const.
  - (* Weakening *)
    apply bet_weakening.
    by apply IHHType.
Qed.


Lemma t_Relop_i_preserve: forall C v1 v2 be iop tf,
    be_typing C [::EConst v1; EConst v2; Relop_i (v_to_vt v1) iop] tf ->
    reduce_simple [:: Basic (EConst v1); Basic (EConst v2); Basic (Relop_i (v_to_vt v1) iop)] [::Basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 be iop tf HType HReduce.
  inversion HReduce; subst.
  (* i32 *)
  - dependent induction HType; subst.
    + (* Composition *)
      invert_be_typing.
      simpl in H. destruct H. subst.
      replace [:: T_i32; T_i32] with ([::T_i32] ++ [::T_i32]) in H => //=.
      repeat rewrite catA in H.
      repeat (apply concat_cancel_last in H; destruct H; subst).
      apply bet_weakening_empty_1.
      apply bet_const.
    + (* Weakening *)
      apply bet_weakening.
      by apply IHHType.
  (* i64 *)
  - dependent induction HType; subst.
    + (* Composition *)
      invert_be_typing.
      simpl in H. destruct H. subst.
      replace [:: T_i64; T_i64] with ([::T_i64] ++ [::T_i64]) in H => //=.
      repeat rewrite catA in H.
      repeat (apply concat_cancel_last in H; destruct H; subst).
      apply bet_weakening_empty_1.
      apply bet_const.
    + (* Weakening *)
      apply bet_weakening.
        by apply IHHType.
Qed.
        
Lemma t_Relop_f_preserve: forall C v1 v2 be fop tf,
    be_typing C [::EConst v1; EConst v2; Relop_f (v_to_vt v1) fop] tf ->
    reduce_simple [:: Basic (EConst v1); Basic (EConst v2); Basic (Relop_f (v_to_vt v1) fop)] [::Basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 be fop tf HType HReduce.
  inversion HReduce; subst.
  (* f32 *)
  - dependent induction HType; subst.
    + (* Composition *)
      invert_be_typing.
      simpl in H. destruct H. subst.
      replace [:: T_f32; T_f32] with ([::T_f32] ++ [::T_f32]) in H => //=.
      repeat rewrite catA in H.
      repeat (apply concat_cancel_last in H; destruct H; subst).
      apply bet_weakening_empty_1.
      apply bet_const.
    + (* Weakening *)
      apply bet_weakening.
      by apply IHHType.
  (* f64 *)
  - dependent induction HType; subst.
    + (* Composition *)
      invert_be_typing.
      simpl in H. destruct H. subst.
      replace [:: T_f64; T_f64] with ([::T_f64] ++ [::T_f64]) in H => //=.
      repeat rewrite catA in H.
      repeat (apply concat_cancel_last in H; destruct H; subst).
      apply bet_weakening_empty_1.
      apply bet_const.
    + (* Weakening *)
      apply bet_weakening.
        by apply IHHType.
Qed.

(* deserialise is yet defined -- I think it's counted as an host operation.
   see Line 70 in operations.v. *)
Axiom typeof_deserialise: forall v t,
    typeof (wasm_deserialise v t) = t.

Lemma be_typing_const_deserialise: forall C v t,
    be_typing C [:: EConst (wasm_deserialise (bits v) t)] (Tf [::] [:: t]).
Proof.
  move => C v t.
  assert (be_typing C [:: EConst (wasm_deserialise (bits v) t)] (Tf [::] [:: typeof (wasm_deserialise (bits v) t)])); first by apply bet_const.
  by rewrite typeof_deserialise in H.
Qed.

Lemma t_Convert_preserve: forall C v t1 t2 sx be tf,
    be_typing C [::EConst v; Cvtop t2 Convert t1 sx] tf ->
    reduce_simple [::Basic (EConst v); Basic (Cvtop t2 Convert t1 sx)] [::Basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v t1 t2 sx be tf HType HReduce.
  inversion HReduce; subst.
  dependent induction HType; subst.
  - (* Composition *)
    invert_be_typing.
    apply concat_cancel_last in H0; destruct H0; subst.
    apply bet_weakening_empty_1.
    unfold cvt in H5.
    destruct t2; unfold option_map in H5.
    (* TODO: maybe refactor this destruct *)
    + destruct (cvt_i32 sx v) eqn:HDestruct => //=. inversion H5. by apply bet_const.
    + destruct (cvt_i64 sx v) eqn:HDestruct => //=. inversion H5. by apply bet_const.
    + destruct (cvt_f32 sx v) eqn:HDestruct => //=. inversion H5. by apply bet_const.
    + destruct (cvt_f64 sx v) eqn:HDestruct => //=. inversion H5. by apply bet_const.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType.
Qed.  
      
Lemma t_Reinterpret_preserve: forall C v t1 t2 be tf,
    be_typing C [::EConst v; Cvtop t2 Reinterpret t1 None] tf ->
    reduce_simple [::Basic (EConst v); Basic (Cvtop t2 Reinterpret t1 None)] [::Basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v t1 t2 be tf HType HReduce.
  inversion HReduce; subst.
  dependent induction HType; subst.
  - (* Composition *)
    invert_be_typing.
    apply concat_cancel_last in H1; destruct H1; subst.
    apply bet_weakening_empty_1.
    apply be_typing_const_deserialise.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType.
Qed.  

(* I think this is the correct statement for instructions within r_simple which do
     not change the typing context (no control flow instructions). *)

Theorem t_simple_preservation: forall s vs bes i bes' es es' C Cl tf,
    inst_typing s i C ->
    Cl = upd_local C (vs_to_vts vs) ->
    be_typing Cl bes tf ->
    reduce_simple es es' ->
    es' != [::Trap] ->
    b_to_a bes = es ->
    b_to_a bes' = es' ->
    be_typing Cl bes' tf.
Proof.
  move => s vs bes i bes' es es' C Cl tf HInstType HContext HType HReduce HNTrap HBES1 HBES2.
  dependent induction HReduce; b_to_a_revert; subst; simpl in HType => //.
  - (* Unop_i32 *)
    eapply t_Unop_i_preserve => //=.
    + replace T_i32 with (v_to_vt (ConstInt32 c)) in HType => //=.
      by apply HType.
    + by apply rs_unop_i32.
  - (* Unop_i64 *)
    eapply t_Unop_i_preserve.
    + replace T_i64 with (v_to_vt (ConstInt64 c)) in HType => //=.
      by apply HType.
    + by apply rs_unop_i64.
  - (* Unop_f32 *)
    eapply t_Unop_f_preserve => //=.
    + replace T_f32 with (v_to_vt (ConstFloat32 c)) in HType => //=.
      by apply HType.
    + by apply rs_unop_f32.
  - (* Unop_f64 *)
    eapply t_Unop_f_preserve => //=.
    + replace T_f64 with (v_to_vt (ConstFloat64 c)) in HType => //=.
      by apply HType.
    + by apply rs_unop_f64.
  - (* Binop_i32_success *)
    eapply t_Binop_i_preserve_success => //=.
    + replace T_i32 with (v_to_vt (ConstInt32 c1)) in HType => //=.
      by apply HType.
    + by apply rs_binop_i32_success.
  - (* Binop_i64_success *)
    eapply t_Binop_i_preserve_success => //=.
    + replace T_i64 with (v_to_vt (ConstInt64 c1)) in HType => //=.
      by apply HType.
    + by apply rs_binop_i64_success.
  - (* Binop_f32_success *)
    eapply t_Binop_f_preserve_success => //=.
    + replace T_f32 with (v_to_vt (ConstFloat32 c1)) in HType => //=.
      by apply HType.
    + by apply rs_binop_f32_success.
  - (* Binop_f64_success *)
    eapply t_Binop_f_preserve_success => //=.
    + replace T_f64 with (v_to_vt (ConstFloat64 c1)) in HType => //=.
      by apply HType.
    + by apply rs_binop_f64_success.
  - (* testop_i T_i32 *)
    apply t_Testop_i32_preserve => //.
  - (* testop_i T_i64 *)
    apply t_Testop_i64_preserve => //.
  - (* relop T_i32 *)
    eapply t_Relop_i_preserve => //=.
    + replace T_i32 with (v_to_vt (ConstInt32 c1)) in HType => //=.
      by apply HType.
    + by apply rs_relop_i32.
  - (* relop T_i64 *)
    eapply t_Relop_i_preserve => //=.
    + replace T_i64 with (v_to_vt (ConstInt64 c1)) in HType => //=.
      by apply HType.
    + by apply rs_relop_i64.
  - (* relop T_f32 *)
    eapply t_Relop_f_preserve => //=.
    + replace T_f32 with (v_to_vt (ConstFloat32 c1)) in HType => //=.
      by apply HType.
    + by apply rs_relop_f32.
  - (* relop T_f64 *)
    eapply t_Relop_f_preserve => //=.
    + replace T_f64 with (v_to_vt (ConstFloat64 c1)) in HType => //=.
      by apply HType.
    + by apply rs_relop_f64.
  - (* Cvtop Convert *)
    eapply t_Convert_preserve => //=.
    apply HType.
    by apply rs_convert_success => //=.
  - (* Cvtop Reinterpret *)
    eapply t_Reinterpret_preserve => //=.
    apply HType.
    by apply rs_reinterpret => //=.
    
    
        
    
      
    
    
    
Admitted.  
    
    
    

(* This has a 0% chance of being the correct statement. I just wanted to see
     how the opsem condition works when we do inversion on it. *)
Theorem t_be_preservation: forall s vs bes i s' vs' bes' C C' tf,
    reduce s vs (b_to_a bes) i s' vs' (b_to_a bes') ->
    be_typing C bes tf ->
    inst_typing s i C ->
    vs_to_vts vs = tc_local C ->
    inst_typing s' i C' ->
    vs_to_vts vs' = tc_local C' ->
    be_typing C' bes' tf.
Proof.
  move => s vs bes i s' vs' bes' C C' tf HOpsem HBET HInstT HLocalT HInstT' HLocalT'.
  inversion HOpsem; subst.
  - (* reduce_simple *)
Admitted.


