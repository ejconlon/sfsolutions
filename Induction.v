Require Export Basics.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".  (* <----- here *)
    reflexivity.
  Case "b = false".  (* <---- and here *)
    rewrite <- H.
    reflexivity.
Qed.

(** **** Exercise: 2 stars (andb_true_elim2) *)
(** Prove [andb_true_elim2], marking cases (and subcases) when
    you use [destruct]. *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b.
  Case "b = true".
    rewrite andb_t_l.
    intros H.
    assumption.
  Case "b = false".
    rewrite andb_f_l.
    intros H.
    destruct c.
    SCase "c = true".
      reflexivity.
    SCase "c = false".
      assumption.
Qed.

Theorem sub_diag : forall n,
  sub n n = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite plus_assoc.
  symmetry.
  rewrite plus_assoc.
  assert (H: m + n = n + m).
    rewrite plus_comm.
    reflexivity.
  rewrite H.
  reflexivity.
Qed.

Theorem mult_0_r: forall m : nat, m * 0 = 0.
Proof.
  intros m.
  induction m as [|m'].
  Case "m = 0".
    rewrite mult_0_l.
    reflexivity.
  Case "m = S m'".
    simpl.
    assumption.
Qed.

Theorem add_eq_l : forall m n o : nat, m = n -> m + o = n + o.
Proof.
  intros m n o H.
  rewrite H.
  reflexivity.
Qed.

Theorem add_eq_r : forall m n o : nat, m = n -> o + m = o + n.
Proof.
  intros m n o H.
  rewrite H.
  reflexivity.
Qed.

Lemma plus_unassoc : forall n m o : nat, (n + m) + o = n + (m + o).
Proof.
  symmetry.
  rewrite plus_assoc.
  reflexivity.
Qed.

Theorem mult_dist_l : forall m n o: nat, m * (n + o) = (m * n) + (m * o).
Proof.
  intros m n o.
  induction m as [|m'].
  Case "m = 0".
    rewrite mult_0_l.
    rewrite mult_0_l.
    rewrite mult_0_l.
    symmetry.
    rewrite plus_0_l.
    reflexivity.
  Case "m = S m'".
    simpl.
    rewrite IHm'.
    remember (m' * n) as a.
    remember (m' * o) as b.
    rewrite plus_assoc.
    symmetry.
    rewrite plus_assoc.
    rewrite plus_comm.
    symmetry.
    rewrite plus_comm.
    assert (H: n + o + a = n + a + o).
      rewrite plus_unassoc.
      symmetry.
      rewrite plus_unassoc.
      assert (H2: a + o = o + a).
        rewrite plus_comm.
        reflexivity.
      rewrite H2.
      reflexivity.
    rewrite H.
    reflexivity.
Qed.

Theorem mult_dist_r : forall m n o: nat, (n + o) * m = (n * m) + (o * m).
Proof.
  intros m n o.
  induction m as [|m'].
  Case "m = 0".
    rewrite mult_0_r.
    rewrite mult_0_r.
    rewrite mult_0_r.
    reflexivity.
  Case "m = S m'".
Admitted.

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros m n.
  induction m as [|m'].
  Case "m = 0".
    rewrite mult_0_l.
    rewrite mult_0_r.
    reflexivity.
  Case "m = S m'".
Admitted.








