(** a naive functional representation of an array *)
(* (C) J. Pichon - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrbool eqtype.

(* this works well when there are few updates *)
Module Type Index_Sig.
Parameter Index : Type.
Parameter index_eqb : Index -> Index -> bool.
Parameter Value : Type.
Axiom index_eqb_eqP : Equality.axiom index_eqb.
End Index_Sig.

Module Make (X : Index_Sig).
  Import X.

Inductive array : Type :=
| A_init : Value -> array
| A_update : Index -> Value -> array -> array.

Definition make (v : Value) : array :=
  A_init v.

Fixpoint get (arr : array) (idx : Index) : Value :=
  match arr with
  | A_init a => a
  | A_update idx' a arr' =>
    if index_eqb idx idx' then a
    else get arr' idx
  end.

Fixpoint set (arr : array) (idx : Index) (a : Value) : array :=
  A_update idx a arr.

Lemma get_set : forall i v arr,
  get (set arr i v) i = v.
Proof.
move => i v.
rewrite /get /set.
case; rewrite (introT (index_eqb_eqP i i) (Logic.eq_refl i)); reflexivity.
Qed.

Lemma get_skip : forall i i' v arr,
  index_eqb i i' = false ->
  get (set arr i' v) i = get arr i.
Proof.
move => i i' v arr His.
case: arr.
{ move => v_init.
  by rewrite /get /set His. }
{ move => i'' v'' a.
  by rewrite /= His. }
Qed.

End Make.

