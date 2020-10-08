(** a typeclass for memory, with two implementations:
 - a list-based implementation
 - a lazy sparse array-based implementation *)
(* (C) J. Pichon - see LICENSE.txt *)

From mathcomp Require Import ssreflect eqtype seq.
Require Import BinNat Lia.
From Wasm Require Import numerics bytes array.

Class Memory (Mem_t : Type) := {
  mem_eqtype : unit; (* TODO: fix this *)
  mem_make : byte -> N -> Mem_t;
  mem_length : Mem_t -> N;
  mem_grow : N -> Mem_t -> Mem_t;
  mem_lookup : N -> Mem_t -> option byte;
  mem_update : N -> byte -> Mem_t -> option Mem_t;
  mem_ax_lookup_out_of_bounds : forall mem n, N.ge n (mem_length mem) -> mem_lookup n mem = None;
  mem_ax_lookup_make : forall n len b, N.lt n len -> mem_lookup n (mem_make b len) = Some b;
  mem_ax_lookup_update : forall mem mem' n b, N.lt n (mem_length mem) -> Some mem' = mem_update n b mem -> mem_lookup n mem' = Some b;
  mem_ax_lookup_skip : forall mem mem' n n' b, n <> n' -> Some mem' = mem_update n' b mem -> mem_lookup n mem' = mem_lookup n mem;
  (* TODO: probably need more, like length constancy *)
}.

Module Byte_Index <: array.Index_Sig.
Definition Index := N.
Definition Value := byte.
Definition index_eqb := N.eqb.
Definition index_eqb_eqP : Equality.axiom index_eqb.
apply ssrnat.eq_binP.
Defined.
End Byte_Index.

Module Byte_array := array.Make Byte_Index.

Record data_vec : Type := {
  dv_length : N;
  dv_array : Byte_array.array;
}.

Program Instance data_vec_Memory : Memory data_vec := {
mem_make := (fun v len => {| dv_length := len; dv_array := Byte_array.make v |} );
mem_length := (fun dv => dv.(dv_length));
mem_grow := (fun len_delta dv => {| dv_length := dv.(dv_length) + len_delta; dv_array := dv.(dv_array) |});
mem_lookup := (fun i dv => if N.ltb i dv.(dv_length) then Some (Byte_array.get dv.(dv_array) i) else None);
mem_update := (fun i v dv => if N.ltb i dv.(dv_length) then Some {| dv_length := dv.(dv_length); dv_array := Byte_array.set dv.(dv_array) i v |} else None);
}.
Next Obligation.
(* TODO: fragile names *)
have Hrw: (N.ltb n (dv_length mem) = false); last by rewrite Hrw.
apply/N.ltb_ge.
lia.
Defined.
Next Obligation.
apply N.ltb_lt in H.
by rewrite H.
Defined.
Next Obligation.
apply N.ltb_lt in H.
rewrite H in H0.
case: mem' H0 => dv_len dv_arr [Hlen Harr].
rewrite /= Hlen H Harr.
f_equal.
apply Byte_array.get_set.
Defined.
Next Obligation.
case: mem' H0 => dv_len dv_arr /=.
destruct (N.ltb n' (dv_length mem)) eqn:H2. (* TODO: style? *)
{ move => [Hlen Harr].
  rewrite /= Hlen.
  case (N.ltb n (dv_length mem)); last done.
  f_equal.
  rewrite Harr.
  rewrite Byte_array.get_skip; first by reflexivity.
  case: (Byte_Index.index_eqb_eqP n n'). (* TODO: this is silly *)
  { move => Hctr. exfalso.
  apply: H. apply Hctr. }
  { done. } 
}  
{ move => Hdisc. discriminate Hdisc. }
Defined.

Record data_list : Type := {
  dl_init : byte;
  dl_data : list byte;
}.

Lemma nth_repeat :
 forall A b i len, i < len ->
 @List.nth_error A (List.repeat b len) i = Some b.
Proof.
move => A b.
elim => [|i].
{ case => [|len]; first by lia.
  by move => _. }
{ move => IH len.
  case: len => [|len'].
  { move => Hctr.
    exfalso.
    lia. }
  { move => Hlen /=.
    apply: IH.
    lia. } }
Qed.

Lemma foo : forall A (l : list A) i b,
i < List.length l ->
List.nth_error
  (take i l ++ b :: drop (i+1) l) i =
Some b.
Proof.
move => A.
elim => [|x l].
{ move => i b /= Hlen.
  exfalso.
  lia. }
{ move => IH.
  case => [|i]; first by reflexivity.
  move => b /= Hlen.
  have Hlen': i < length l by lia.
  by apply: IH.
}
Qed.

Lemma bar : forall A n n' (l : list A) v,
n <> n' -> n' < List.length l ->
List.nth_error (take n' l ++ v :: drop (n' + 1) l) n =
List.nth_error l n.
Proof.
Admitted.

Program Instance data_list_Memory : Memory data_list := {
mem_make := (fun v len => {| dl_init := v; dl_data := List.repeat v (N.to_nat len) |});
mem_length := (fun dl => N.of_nat (List.length dl.(dl_data)));
mem_grow := (fun len_delta dl => {| dl_init := dl.(dl_init); dl_data := dl.(dl_data) ++ List.repeat dl.(dl_init) (N.to_nat len_delta) |});
mem_lookup := (fun i dl => List.nth_error dl.(dl_data) (N.to_nat i));
mem_update :=
  (fun i v dl =>
   if N.ltb i (N.of_nat (List.length dl.(dl_data)))
   then Some {| dl_init := dl.(dl_init);
                dl_data := take (N.to_nat i) dl.(dl_data) ++ [::v] ++ drop (N.to_nat i+1) dl.(dl_data) |}
   else None);
}.
Next Obligation.
apply (List.nth_error_None mem.(dl_data) (N.to_nat n)).
apply N.ge_le in H.
move: H.
set x := (length (dl_data mem)).
move => H.
lia.
Defined.
Next Obligation.
apply: nth_repeat.
lia.
Defined.
Next Obligation.
apply N.ltb_lt in H.
rewrite H in H0.
case: mem' H0 => init_ data_ [Hinit Hdata].
rewrite Hinit Hdata /= {init_ data_ Hinit Hdata}.
set nn := N.to_nat n.
have Hx: nn < length (dl_data mem).
apply N.ltb_lt in H.
lia.
by apply: foo.
Defined.
Next Obligation.
case: mem' H0 => init_ data_.
case_eq (N.ltb n' (N.of_nat (length (dl_data mem)))); last by discriminate.
move => Hlen [Hinit Hdata] /=.
rewrite Hdata => {Hdata}.
apply: bar.
lia.
apply N.ltb_lt in Hlen.
lia.
Defined.
