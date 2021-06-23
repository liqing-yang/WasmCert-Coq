From mathcomp Require Import ssreflect ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From stdpp Require Import gmap strings.
Require Export common operations_iris datatypes_iris datatypes_properties_iris properties_iris.

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

Lemma those_lookup: forall {T: Type} (l: list (option T)) (le: list T) n,
  list_extra.those l = Some le -> option_map (fun x => Some x) (le !! n) = l !! n.
Proof.
  move => T l le n Hthose.
  rewrite - those_those0 in Hthose.
  move : le n Hthose.
  induction l => //=; move => le n Hthose.
  - inversion Hthose; subst; clear Hthose.
    unfold option_map.
    by repeat rewrite list_lookup_empty.
  - destruct a => //=.
    unfold option_map in *.
    destruct le => //=; first by destruct (those0 l).
    destruct n => //=.
    + destruct (those0 l) => //.
      by inversion Hthose.
    + destruct (those0 l) => //.
      inversion Hthose; subst; clear Hthose.
      by apply IHl. 
Qed.
