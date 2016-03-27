(* "Accept this definition without proof" *)
Definition admit {T: Type} : T.  Admitted.

Inductive day : Type :=
  | monday : day
  | tuesday: day
  | wednesday : day.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => monday
  end.

(*Eval compute in (next_weekday monday).*)

Example test_next_weekday:
  (next_weekday (next_weekday tuesday)) = monday.
Proof.
  simpl.
  reflexivity.
Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => negb b2
  | false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb2: (nandb false false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb3: (nandb false true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb4: (nandb true true) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (andb b1 (andb b2 b3)).

Example test_andb31: (andb3 true true true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_andb32: (andb3 false true true) = false.
Proof.
  simpl.
  reflexivity.
Qed.


Example test_andb33: (andb3 true false true) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_andb34: (andb3 true true false) = false.
Proof.
  simpl.
  reflexivity.
Qed.

(*
Check true.

Check (negb true).

Check test_andb34.
*)

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Fixpoint sub (n m : nat) : nat :=
  match n with
    | O => O
    | S n' =>
      match m with
        | O => n
        | S m' => sub n' m'
      end
  end.

Example plus_works: plus 2 3 = 5.
Proof. reflexivity. Qed.

Example sub_works: sub 5 3 = 2.
Proof. reflexivity. Qed.

Example sub_zero: sub 3 5 = 0.
Proof. reflexivity. Qed.

(* Eval compute in (plus (S (S (S O))) (S (S O))). *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (sub x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

(* Check ((0 + 1) + 1). *)

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
    | O => true
    | S n' =>
       match m with
         | O => false
         | S m' => ble_nat n' m'
       end
    end.

Example test_ble_nat1:             (ble_nat 2 2) = true.
Proof. reflexivity.  Qed.
Example test_ble_nat2:             (ble_nat 2 4) = true.
Proof. reflexivity.  Qed.
Example test_ble_nat3:             (ble_nat 4 2) = false.
Proof. reflexivity.  Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Definition blt_nat (n m : nat) : bool :=
  andb (ble_nat n m) (negb (beq_nat n m)).

Example test_blt_nat1:             (blt_nat 2 2) = false.
Proof. reflexivity.  Qed.

Example test_blt_nat2:             (blt_nat 2 4) = true.
Proof. reflexivity.  Qed.

Example test_blt_nat3:             (blt_nat 4 2) = false.
Proof. reflexivity.  Qed.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.  Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.  Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite H1.
  rewrite H2.
  reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.  Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
  reflexivity.
  reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n as [| n'].
  reflexivity.
  reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f H b.
  rewrite H.
  rewrite H.
  reflexivity.
Qed.

Theorem andb_f_l : forall (x : bool), andb false x = false.
Proof.
  intros x.
  reflexivity.
Qed.

Theorem andb_f_r : forall (x : bool), andb x false = false.
Proof.
  intros x.
  destruct x.
  reflexivity.
  reflexivity.
Qed.

Theorem andb_t_l : forall (x : bool), andb true x = x.
Proof.
  intros x.
  reflexivity.
Qed.

Theorem andb_t_r : forall (x : bool), andb x true = x.
Proof.
  intros x.
  destruct x.
  reflexivity.
  reflexivity.
Qed.

Theorem orb_t_l : forall (x : bool), orb true x = true.
Proof.
  intros x.
  reflexivity.
Qed.

Theorem orb_t_r : forall (x : bool), orb x true = true.
Proof.
  intros x.
  destruct x.
  reflexivity.
  reflexivity.
Qed.

Theorem orb_f_l : forall (x : bool), orb false x = x.
Proof.
  intros x.
  reflexivity.
Qed.

Theorem orb_f_r : forall (x : bool), orb x false = x.
Proof.
  intros x.
  destruct x.
  reflexivity.
  reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b.
  rewrite andb_t_l.
  rewrite orb_t_l.
  intros H.
  rewrite H.
  reflexivity.
  rewrite andb_f_l.
  rewrite orb_f_l.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Inductive bin : Type :=
  | B0 : bin
  | B1 : bin -> bin
  | B2 : bin -> bin.

Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
    | B0 => 0
    | B1 b' => 2 * (bin_to_nat b')
    | B2 b' => (2 * (bin_to_nat b')) + 1
  end.

Fixpoint bin_incr (b : bin) : bin :=
  match b with
    | B0 => B2 B0
    | B1 b' => B2 b'
    | B2 b' => B1 (bin_incr b')
  end.

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
    | 0 => B0
    | S n => bin_incr (nat_to_bin n)
  end.

Example nbn_0: bin_to_nat (nat_to_bin 0) = 0.
Proof. reflexivity. Qed.

Example nbn_1: bin_to_nat (nat_to_bin 1) = 1.
Proof. reflexivity. Qed.

Example nbn_2: bin_to_nat (nat_to_bin 2) = 2.
Proof. reflexivity. Qed.

Example nbn_3: bin_to_nat (nat_to_bin 3) = 3.
Proof. reflexivity. Qed.

Example nbn_4: bin_to_nat (nat_to_bin 4) = 4.
Proof. reflexivity. Qed.

Example nbn_5: bin_to_nat (nat_to_bin 5) = 5.
Proof. reflexivity. Qed.

Lemma plus_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [| n'].
  reflexivity.
  simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Lemma plus_0_l : forall n : nat, 0 + n = n.
Proof.
  intros n.
  induction n as [| n'].
  reflexivity.
  simpl.
  reflexivity.
Qed.

Lemma whatever: forall n m : nat, m + S n = S (m + n).
Proof.
  intros n m.
  induction m as [|m'].
  rewrite plus_0_l.
  rewrite plus_0_l.
  reflexivity.
  simpl.
  rewrite IHm'.
  reflexivity.
Qed.

Lemma plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros m n.
  induction n as [|n'].
  rewrite plus_0_r.
  rewrite plus_0_l.
  reflexivity.
  assert (H2: n' + m = m + n').
    symmetry.
    assumption.
  simpl.
  rewrite H2.
  simpl.
  rewrite whatever.
  reflexivity.
Qed.

Lemma plus_assoc : forall n m o : nat, n + (m + o) = (n + m) + o.
Proof.
  intros n m o.
  induction n as [|n'].
  rewrite plus_0_l.
  rewrite plus_0_l.
  reflexivity.
  simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Lemma binary_unary_inc_commute : forall b : bin,
  bin_to_nat (bin_incr b) = (bin_to_nat b) + 1.
Proof.
  intros b.
  induction b.
  reflexivity.
  simpl.
  rewrite plus_0_r.
  reflexivity.
  simpl.
  rewrite plus_0_r.
  rewrite plus_0_r.
  rewrite IHb.
  remember (bin_to_nat b) as x.
  rewrite plus_assoc.
  assert (H2: x + 1 + x = x + x + 1).
    rewrite plus_comm.
    rewrite plus_assoc.
    reflexivity.
  rewrite H2.
  reflexivity.
Qed.

Theorem nat_to_bin_to_nat: forall n : nat, bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n.
  reflexivity.
  simpl.
  rewrite binary_unary_inc_commute.
  rewrite IHn.
  rewrite plus_comm.
  reflexivity.
Qed.
