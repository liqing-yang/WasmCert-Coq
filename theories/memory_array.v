(** an implementation of Wasm memory based on a sparse array *)
(* (C) J. Pichon - see LICENSE.txt *)

From mathcomp Require Import ssreflect eqtype.
Require Import BinNat Lia.
From Wasm Require Import numerics bytes array memory.

Module Byte_Index <: array.Index_Sig.
  Definition Index := N.
  Definition Value := byte.
  Definition index_eqb := N.eqb.
  Definition index_eqb_eqP : Equality.axiom index_eqb.
  apply ssrnat.eq_binP.
  Defined.
End Byte_Index.

Module Byte_array := array.Make Byte_Index.

(** An implementation of Wasm memory based on a sparse array
*)
Record memory_array : Type := {
  ma_length : N;
  ma_array : Byte_array.array;
}.

Definition mem_make : Memory.mem_make_t memory_array :=
  fun v len => {| ma_length := len; ma_array := Byte_array.make v |}.

Definition mem_length : Memory.mem_length_t memory_array :=
  fun ma => ma.(ma_length).

Definition mem_grow : Memory.mem_grow_t memory_array :=
  fun len_delta ma =>
    {|
      ma_length := ma.(ma_length) + len_delta;
      ma_array := ma.(ma_array)
    |}.

Definition mem_lookup  : Memory.mem_lookup_t memory_array :=
  fun i ma =>
    if N.ltb i ma.(ma_length) then Some (Byte_array.get ma.(ma_array) i)
    else None.

Definition mem_update : Memory.mem_update_t memory_array :=
  fun i v ma =>
    if N.ltb i ma.(ma_length) then
      Some
        {|
          ma_length := ma.(ma_length);
          ma_array := Byte_array.set ma.(ma_array) i v |}
    else None.

Lemma memory_array_ax_lookup_out_of_bounds :
  Memory.mem_ax_lookup_out_of_bounds memory_array mem_make mem_length mem_grow mem_lookup mem_update.
Proof.
move => mem i H.
rewrite /mem_lookup.
have Hrw: (N.ltb i (ma_length mem) = false); last by rewrite Hrw.
rewrite /mem_length in H.
apply/N.ltb_ge.
lia.
Qed.

Lemma memory_array_ax_lookup_make : Memory.mem_ax_lookup_make memory_array mem_make mem_length mem_grow mem_lookup mem_update.
Proof.
move => i len b H.
rewrite /mem_lookup.
apply N.ltb_lt in H.
by rewrite H.
Qed.

Lemma memory_array_ax_lookup_update : Memory.mem_ax_lookup_update memory_array mem_make mem_length mem_grow mem_lookup mem_update.
Proof.
move => mem mem' i b H H0.
apply N.ltb_lt in H.
rewrite /mem_update H in H0.
case: mem' H0 => ma_len ma_arr [Hlen Harr].
rewrite /mem_lookup /= Hlen H Harr.
f_equal.
apply Byte_array.get_set.
Qed.

Lemma memory_array_ax_lookup_skip :
  Memory.mem_ax_lookup_skip memory_array mem_make mem_length mem_grow mem_lookup mem_update.
Proof.
move => mem mem' i i' b Hii'.
rewrite /mem_lookup /mem_update.
case: mem' => ma_len ma_arr /=.
destruct (N.ltb i' (ma_length mem)) eqn:H2. (* TODO: style? *)
{ move => [Hlen Harr].
  rewrite /= Hlen.
  case (N.ltb i (ma_length mem)); last done.
  f_equal.
  rewrite Harr.
  rewrite Byte_array.get_skip; first by reflexivity.
  case: (Byte_Index.index_eqb_eqP i i'). (* TODO: this is silly *)
  { move => Hctr. exfalso.
  apply: Hii'. apply Hctr. }
  { done. } 
}  
{ move => Hdisc. discriminate Hdisc. }
Qed.

Lemma memory_array_ax_length_constant_update :
  Memory.mem_ax_length_constant_update memory_array mem_make mem_length mem_grow mem_lookup mem_update.
Proof.
move => i b mem mem'.
rewrite /mem_update /mem_length.
case: mem => ma_len ma_arr.
case: mem' => ma_len' ma_arr'.
rewrite /=.
destruct (N.ltb i ma_len) eqn:H2. (* TODO: style? *)
{
move => [Hlen Harr].
assumption.
}
{ move => Hdisc. discriminate Hdisc. }
Qed.

Definition eqmemory_array (ma1 ma2 : memory_array) : bool.
(* TODO *)
Admitted.

Definition eqmemory_arrayP : Equality.axiom eqmemory_array.
(* TODO *)
Admitted.

Definition memory_array_eqMixin := Equality.Mixin eqmemory_arrayP.
Canonical memory_array_eqType := @Equality.Pack memory_array memory_array_eqMixin.

Definition array_memoryMixin :=
  Memory.Mixin
    memory_array
    mem_make
    mem_length
    mem_grow
    mem_lookup
    mem_update
    memory_array_ax_lookup_out_of_bounds
    memory_array_ax_lookup_make
    memory_array_ax_lookup_update
    memory_array_ax_lookup_skip
    memory_array_ax_length_constant_update.
Canonical array_memoryType := @Memory.Pack memory_array_eqType array_memoryMixin.