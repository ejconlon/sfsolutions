Require Export Poly.

Theorem silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros H.
  apply H.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros.
  assert (H0: l' = rev (rev l')).
    symmetry.
    apply rev_involutive.
  rewrite H.
  symmetry.  
  apply rev_involutive.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite eq1.
  apply eq2.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros.
  rewrite H.
  apply H0.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros.
  apply trans_eq with (m:=[c;d]).
  apply H.
  apply H0.
Qed.

Definition minustwo (n : nat) : nat := pred (pred n).

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o). 
Proof.
  intros.
  apply trans_eq with m.
  apply H0.
  apply H.
Qed.

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq.
  inversion eq.
  reflexivity.
Qed.

Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros.
  inversion H0.
  reflexivity.
Qed.

Theorem silly_contra :
     1 = 2 ->
     2 + 2 = 3.
Proof.
  intros.
  inversion H.
Qed.

Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros.
  inversion H.
Qed.

Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  intros.
  inversion H.
Qed.

Theorem f_equal : forall (X Y : Type) (f : X -> Y) (a b : X),
    a = b -> f a = f b.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros.
  induction n.
  reflexivity.
  inversion H.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b. 
Proof.
  intros.
  simpl in H.
  apply H.
Qed.

Theorem plus_eq_0_l : forall n m : nat, n + m = 0 -> n = 0.
Proof.
  intros.
  induction n as [| n'].
  reflexivity.
  simpl in H.
  inversion H.
Qed.

Theorem plus_S_out : forall n m : nat, n + S m = S (n + m).
Proof.
  intros.
  induction n as [| n'].
  reflexivity.
  simpl.
  rewrite IHn'.
  reflexivity.
Qed.

Theorem plus_S_eq : forall n m : nat, n = m -> S n = S m.
Proof.
  intros.
  induction n.
  rewrite H.
  reflexivity.
  rewrite H.
  reflexivity.
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intro n.
  induction n as [|n'].
  simpl.
  intros m H.
  symmetry in H.
  apply plus_eq_0_l in H.
  symmetry in H.
  assumption.
  intro m.
  destruct m as [|m'].
  simpl.
  intro contra.
  inversion contra.
  intro H.
  assert (H0: n' = m').
  apply IHn'.
  simpl in H.
  rewrite plus_S_out in H.
  rewrite plus_S_out in H.
  inversion H.
  reflexivity.
  apply plus_S_eq.
  assumption.
Qed.

Lemma s_eq : forall n m, n = m -> S n = S m.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.
  
Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  induction n as [|n'].
  intros.
  destruct m as [|m'].
  reflexivity.
  inversion H.
  destruct m as [|m'].
  intro H.
  inversion H.
  intro H.
  inversion H.
  specialize IHn' with m'.
  apply IHn' in H1.
  apply s_eq.
  assumption.
Qed.

Theorem length_p_1: forall (X : Type) (v : X) (l : list X),
    length (v :: l) = S (length l).
Proof.
  intros X v.
  destruct l.
  reflexivity.
  simpl.
  reflexivity.
Qed.  

(*Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
   length l = n -> index n l = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [|v l'].
  destruct n.
  reflexivity.
  reflexivity.
  intro n.
  intro H.
  assert (U: length (v :: l') = S (length l')).
    apply length_p_1.
  simpl.
  *)