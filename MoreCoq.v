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
