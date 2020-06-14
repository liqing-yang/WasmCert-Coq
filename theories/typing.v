(** Wasm typing rules **)
(* (C) J. Pichon - see LICENSE.txt *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import operations.

(**
There are three files related to typing:
  -- typing.v (this file): gives inductive definition of typing;
  -- type_checker.v: gives a fixpoint that determines whether something is of 
     a given type. This is somewhat like the interpreter, except that we need
     to prove that typing is unique. I think it is already done for this
     inductive definition but not for the type_checker yet? But that will follow
     from the following..
  -- type_checker_reflects_typing.v: gives a lemma that says the two above agree
     with each other.

  After all of these, we will need to prove preservation + progress with respect
    to definitions in opsem.v. This should be in a separate file.
**)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Print sx.

(* FIXME: To which function in the Wasm specification does this correspond to? *)

(** Answer to above

  I searched through the specification but couldn't find a direct link to this either.
    After some thoughts I think the only possibility is that this
    is related to section 2.4.1, where all possible Convert operations are defined.

  From my understanding, Cvtop is just a proxy for all the conversion operations, which
    are the following (given in 2.4.1):
    - i32.wrap_i64
    - i64.extend_i32_sx
    - inn.trunc_fmm_sx
    - f32.demote_f64
    - f64.promote_f32
    - fnn.convert_imm_sx
    - inn.reinterpret_fnn
    - fnn.reinterpret_inn

    where sx means the numbers are signed.

    I think the original author wrote this convert_helper function for:
      given two types t1, t2 and the sign option sx, if the function returns true,
      then there is one of the above eight conversion operations that is
      of the corresponding type (in fact one of the first six -- see below). 

    For example, consider when will convert_helper be true if sxo is not None. In that
      case we must have:
      - at least one of t1 or t2 is not float;
      - at least one of t1 or t2 is not int -- or if they are both int, then t1
          should have length at least equal to t2.

    Considering the fact that there are only 4 choices for t1,t2 (i/f 32/64), there
      are only the following possible combinations that will make this function true
      (noting that we need to have t1 and t2 being different):
      - t1 = fnn, t2 = imm;
      - t1 = inn, t2 = fmm;
      - t1 = i64, t2 = i32.
    These three combinations correspond exactly to the three signed conversions 
      among the eight listed above (to trunc/convert/extend respectively).

    When sx is unsigned, the helper function gives the three other conversions
      that are not reinterpret operations. This is where we've been doing
      differently from the official convention, since the official spec considers
      reinterpret to be part of the conversion operations under the same proxy
      (see 2.4.1.1). In our approach, Cvtop is only the proxy for the first 6 
      conversion operations; we deal with the reinterpret operations in a separate
      case (this is the case in both opsem.v and the be_typing function below).
    
    I guess it's fine if we keep it consistent within our own work, but I don't think
      I'm the best person to decide this.

    This might also answer some of the FIXMEs below.
   
**)
Definition convert_helper (sxo : option sx) t1 t2 : bool :=
  (sxo == None) ==
  ((is_float_t t1 && is_float_t t2) || (is_int_t t1 && is_int_t t2 && (t_length t1 < t_length t2))).

Definition convert_cond t1 t2 (sxo : option sx) : bool :=
  (t1 != t2) && convert_helper sxo t1 t2.

Print t_context.

Definition upd_label C lab :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    (tc_local C)
    lab
    (tc_return C).

(* FIXME: Change name *)
(** This definition corresponds to the sentence
    “The label C.labels[l] must be defined in the context.”
    in the specification. **)
Definition plop2 C i ts :=
  List.nth_error (tc_label C) i == Some ts.

(** Corresponding to section 3.3 **)
Inductive be_typing : t_context -> list basic_instruction -> function_type -> Prop :=
| bet_const : forall C v, be_typing C [::EConst v] (Tf [::] [::typeof v])
| bet_unop_i : forall C t op, is_int_t t -> be_typing C [::Unop_i t op] (Tf [::t] [::t])
| bet_unop_f : forall C t op, is_float_t t -> be_typing C [::Unop_f t op] (Tf [::t] [::t])
| bet_binop_i : forall C t op, is_int_t t -> be_typing C [::Binop_i t op] (Tf [::t; t] [::t])
| bet_binop_f : forall C t op, is_float_t t -> be_typing C [::Binop_f t op] (Tf [::t; t] [::t])
| bet_testop : forall C t op, is_int_t t -> be_typing C [::Testop t op] (Tf [::t] [::T_i32])
| bet_relop_i : forall C t op, is_int_t t -> be_typing C [::Relop_i t op] (Tf [::t; t] [::T_i32])
| bet_relop_f : forall C t op, is_float_t t -> be_typing C [::Relop_f t op] (Tf [::t; t] [::T_i32])
| bet_convert : forall C t1 t2 sx, t1 <> t2 -> convert_helper sx t1 t2 ->
  be_typing C [::Cvtop t1 Convert t2 sx] (Tf [::t2] [::t1]) (* FIXME: Difference from the Isabelle formalisation: why merge the two rules here? *)
| bet_reinterpret : forall C t1 t2, t1 <> t2 -> Nat.eqb (t_length t1) (t_length t2) ->
  be_typing C [::Cvtop t1 Reinterpret t2 None] (Tf [::t2] [::t1])
| bet_unreachable : forall C ts ts',
  be_typing C [::Unreachable] (Tf ts ts')
| bet_nop : forall C, be_typing C [::Nop] (Tf [::] [::])
| bet_drop : forall C t, be_typing C [::Drop] (Tf [::t] [::])
| bet_select : forall C t, be_typing C [::Select] (Tf [::t; t; T_i32] [::t])
| bet_block : forall C tn tm es,
  let tf := Tf tn tm in
  be_typing (upd_label C (app [::tm] (tc_label C))) es (Tf tn tm) ->
  be_typing C [::Block tf es] (Tf tn tm)
| bet_loop : forall C tn tm es,
  be_typing (upd_label C (app [::tm] (tc_label C))) es (Tf tn tm) ->
  be_typing C [::Loop (Tf tn tm) es] (Tf tn tm)
| bet_if_wasm : forall C tn tm es1 es2,
  be_typing (upd_label C (app [::tm] (tc_label C))) es1 (Tf tn tm) ->
  be_typing (upd_label C (app [::tm] (tc_label C))) es2 (Tf tn tm) ->
  be_typing C [::If (Tf tn tm) es1 es2] (Tf (app tn [::T_i32]) tm)
| bet_br : forall C i t1s ts t2s,
  i < length (tc_label C) ->
  plop2 C i ts ->
  be_typing C [::Br i] (Tf (app t1s ts) t2s)
| bet_br_if : forall C i ts,
  i < length (tc_label C) ->
  plop2 C i ts ->
  be_typing C [::Br_if i] (Tf (app ts [::T_i32]) ts)
| bet_br_table : forall C i ins ts t1s t2s,
  all (fun i => (i < length (tc_label C)) && (plop2 C i ts)) (app ins [::i])  ->
  be_typing C [::Br_table ins i] (Tf (app t1s (app ts [::T_i32])) t2s)
| bet_return : forall C ts t1s t2s,
  tc_return C = Some ts ->
  be_typing C [::Return] (Tf (app t1s ts) t2s)
| bet_call : forall C i tf,
  i < length (tc_func_t C) ->
  List.nth_error (tc_func_t C) i = Some tf ->
  be_typing C [::Call i] tf
| bet_call_indirect : forall C i t1s t2s,
  i < length (tc_types_t C) ->
  List.nth_error (tc_types_t C) i = Some (Tf t1s t2s) ->
  tc_table C <> None ->
  be_typing C [::Call_indirect i] (Tf (app t1s [::T_i32]) t2s)
| bet_get_local : forall C i t,
  i < length (tc_local C) ->
  List.nth_error (tc_local C) i = Some t ->
  be_typing C [::Get_local i] (Tf [::] [::t])
| bet_set_local : forall C i t,
  i < length (tc_local C) ->
  List.nth_error (tc_local C) i = Some t ->
  be_typing C [::Set_local i] (Tf [::t] [::])
| bet_tee_local : forall C i t,
  i < length (tc_local C) ->
  List.nth_error (tc_local C) i = Some t ->
  be_typing C [::Tee_local i] (Tf [::t] [::t])
| bet_get_global : forall C i t,
  i < length (tc_global C) ->
  option_map tg_t (List.nth_error (tc_global C) i) = Some t ->
  be_typing C [::Get_global i] (Tf [::] [::t])
| bet_set_global : forall C i t,
  i < length (tc_global C) ->
  option_map tg_t (List.nth_error (tc_global C) i) = Some t ->
  be_typing C [::Set_global i] (Tf [::t] [::])
| bet_load : forall C n a off tp_sx t,
  tc_memory C = Some n ->
  load_store_t_bounds a (option_projl tp_sx) t ->
  be_typing C [::Load t tp_sx a off] (Tf [::T_i32] [::t])
| bet_store : forall C n a off tp t,
  tc_memory C = Some n ->
  load_store_t_bounds a tp t ->
  be_typing C [::Store t tp a off] (Tf [::T_i32; t] [::]) (* FIXME: Same here: two Isabelle rules have been merged here. *)
| bet_current_memory : forall C n,
  tc_memory C = Some n ->
  be_typing C [::Current_memory] (Tf [::] [::T_i32])
| bet_grow_memory : forall C n,
  tc_memory C = Some n ->
  be_typing C [::Grow_memory] (Tf [::T_i32] [::T_i32])
| bet_empty : forall C,
  be_typing C [::] (Tf [::] [::])
| bet_composition : forall C es e t1s t2s t3s,
  be_typing C es (Tf t1s t2s) ->
  be_typing C [::e] (Tf t2s t3s) ->
  be_typing C (app es [::e]) (Tf t1s t3s)
| bet_weakening : forall C es ts t1s t2s,
  be_typing C es (Tf t1s t2s) ->
  be_typing C es (Tf (app ts t1s) (app ts t2s)).

Definition upd_local C loc :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    loc
    (tc_label C)
    (tc_return C).

Definition upd_local_return C loc ret :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    loc
    (tc_label C)
    ret.

Definition upd_local_label_return C loc lab ret :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    loc
    lab
    ret.

(**
 g_mut says whether the global is mutable; then it has another field g_val
   specifying the value (with type).
 **)

Definition global_agree (g : global) (tg : global_type) : bool :=
  (tg_mut tg == g_mut g) && (tg_t tg == typeof (g_val g)).

(**
 Determines if the nth element of gs is of global type tg. I felt that the first
   condition isn't necessary since List.nth_error take care of it. This has been
   the case for many other places as well. Maybe it's for eyeball-closeness?
**)
Definition globals_agree (gs : list global) (n : nat) (tg : global_type) : bool :=
  (n < length gs) && (option_map (fun g => global_agree g tg) (List.nth_error gs n) == Some true).

Definition memi_agree (sm : list memory) (j : option nat) (m : option nat) : bool :=
  match j, m with
  | None, None => true
  | None, Some _ => false
  | Some _, None => false
  | Some j', Some m' =>
    (j' < length sm) && (option_map mem_size (List.nth_error sm j') == Some m')
  end.

Definition functions_agree (fs : list function_closure) (n : nat) (f : function_type) : bool :=
  (n < length fs) && (option_map cl_type (List.nth_error fs n) == Some f).

Print instance.
Print immediate.
Print t_context.
Print plop2.
Print value_type.
Print store_record.
Print global_type.
Print global.
Print memory.
Print tabinst.
Print function_closure.
(*
  This is the main point where the typing context in the typing system and the 
    store in the operational semantics are connected. Writting my understanding down
    for future reference since I'll definitely forget the meaning of some of them
    at a point.

  store_record and instance are from the operational semantics. 
  Store_record contains 4 
    components: 
     - s_funcs, a sequence of function_closure;
        function_closure is either a host, whose behaviour seems to be out of our
          control; or a native function, which is of the form (Func_native i tf ts es).
          here i is an instance, tf is the function type of this closure, ts is a 
          sequence of value type (?) and es is a sequence of basic instruction.
        Currently I don't see what this ts does (since basic instruction has EConst).
          
     - s_tab, a sequence of tabinst (tables);
        Each table instance is basically a sequence of nat, with a limit on size.

     - s_memory, a sequence of memory;
        Similar to the above, though each memory is a sequence of byte instead of nat.

     - s_glob, a sequence of global (global variables).
        I think each is just one variable, could be either mutable/immutable, and could
          be of the four wasm basic types (i/f 32/64).

   Instance is for some reason very similar. It also has funcs, tab, memory and globs,
     although they are all natural numbers or sequence of natural numbers (and for
     some reason was named 'immediate'. There's an additional i_types which is a 
     sequence of function_type (Tf t1s t2s).

   t_context is the typing context used for the typing predicate. It contains
     tc_types_t and tc_func_t which are both sequence of function_type; it also
     contains tc_global, tc_table and tc_memory, although in t_context we only need
     to know the types of these components. Tables and memories are typed by its 
     size limit (TODO: need to update the definition in t_context), therefore 
     tc_table and tc_memory are option of nat. tc_global is a sequence of global_type,
     where each global_type is the type of one global (mutability + type).
   The main difference is that t_context also contains tc_local, tc_label and tc_return.
     I think this is what makes is really a 'context', as this implies that the current
     sequence of instructions were taken from a larger overall picture. tc_local is 
     a sequence of value_type (which turns out to be the 4 wasm basic types);
     tc_label is a sequence of sequence of value_type (????), and tc_return is an
     option on sequence of value_type.
   I think we can try to deduce that by looking at the typing predicate above.
   For tc_local we should probably look at instructions that manipulate local storage,
     e.g. get/set/tee_local. We see in bet_get_local that get_local i would result in
     function type [] -> [t] if the ith element of (tc_local C) is of type t. So
     t_local stores the type of all local variables.
   For tc_label, we should look at some control flow instructions that introduce new
     labels. From the instruction 'Block': if we have an instruction 'Block tf es', and
     tf = Tf tn tm, then the type of 'Block tf es' under context C is tn -> tm: but
     this is at the condition that, in the modified typing context C', where we prepend
     a 'tm' to tc_label of C, the instruction list es must be of type (Tf tn tm) as 
     well. So it seems that tc_label keeps track of the resulting type of each label
     in a stack?
   It's probably better to look at where it is actually used. Check 'br': when we
     see a 'Br i', we need that the length of tc_label C to be at least (i+1). This is
     consistent with the above understanding since we need to have at least i+1 labels
     present for the Br i instruction to be valid. We know Br i breaks from i labels and
     continue execution at the continuation of the (i+1)th label. Then we find the 
     ith entry of tc_label (0-indexed here), call it ts. The type of the break command
     is then actually Tf (t1s ++ ts) t2s for arbitrary t1s and t2s!!?? This is actually
     not a mistake (3.3.5.6). It is also weird that br_if doesn't have this 
     polymorphism: it is always of type ts ++ [i32] -> ts. br_table is, however,
     polymorphic again. ????????
   OK THIS ACTUALLY MAKES SENSE! br_if is the only command that might not actually
     break: if the top value is zero then we don't break. I think in Wasm, any if
     command of this type must have the same type in both cases, therefore the case
     that it actually breaks must also have the same type. The ts at the top of the
     consumption is only there to demonstrate that this label indeed finishes with
     a type of ts. The t2s can be whatever type that fits which makes the overall typing
     consistent (I think): it is like in the separation logic course, where we give
     br a reduction result of False (basically meaning that we never reach there, and
     false deduces everything -- so if there are later commands we could be consistent).
     The t1s part is to fit the accumulated type of the previous instructions, due to
     definition of types of instruction sequences (3.3.6.2). In practice t1s will only
     have one appropriate value that makes the overall typing work (and t2s also, if 
     I'm correct). I think I'm indeed correct: later in the proof I should be able to
     choose the correct t1s and t2s for the proof to work.

   Ok now tc_return becomes obvious: it is the return type of the current function.
     There is an analogy in the type of the return instruction which is very similar
     to the 'Br i' instruction, being also polymorphic.
*)
Definition inst_typing (s : store_record) (inst : instance) (C : t_context) :=
  if (inst, C) is (Build_instance ts fs i j gs, Build_t_context ts' tfs tgs n m [::] [::] None)
  then
    (ts == ts') &&
       (all2 (functions_agree (s_funcs s)) fs tfs) &&
       (all2 (globals_agree (s_globs s)) gs tgs) &&
          (match i, n with
             | None, None => true
             | None, Some _ => false
             | Some _, None => false
             | Some i', Some n' => (i' < length (s_tab s)) && (option_map tab_size (List.nth_error (s_tab s) i') == Some n')
             end) &&
          (memi_agree (s_memory s) j m)
  else false.

(**
  Main predicate used for typing, but most of the typing are done in be_typing
**)
Inductive cl_typing : store_record -> function_closure -> function_type -> Prop :=
| cl_typing_native : forall i s C C' ts t1s t2s es tf,
  inst_typing s i C ->
  tf = Tf t1s t2s ->
  C' = upd_local_label_return C (app (tc_local C) (app t1s ts)) (app [::t2s] (tc_label  C)) (Some t2s) ->
  be_typing C' es (Tf [::] t2s) ->
  cl_typing s (Func_native i tf ts es) (Tf t1s t2s)
| cl_typing_host : forall s tf h,
  cl_typing s (Func_host tf h) tf.

Definition cl_typing_self (s : store_record) (fc : function_closure) : Prop :=
  cl_typing s fc (cl_type fc).

Lemma cl_typing_unique : forall s cl tf, cl_typing s cl tf -> tf = cl_type cl.
Proof.
  move => s.
  case.
  { move => i tf ts bes t H.
    rewrite /=.
    by inversion H. }
  { move => f h tf H.
    inversion H.
    by rewrite /=. }
Qed.

