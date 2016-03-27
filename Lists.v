Require Export Induction.

Module NatList.

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat := 
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat := 
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod := 
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.
Qed.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [m n].
  simpl.
  reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros.
  destruct p as [m n].
  simpl.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros.
  destruct p as [m n].
  simpl.
  reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist := 
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat := 
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist := 
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) 
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil  
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | [] => []
  | x :: xs =>
    match x with
    | 0 => nonzeros xs
    | _ => x :: (nonzeros xs)
    end
  end.

Example test_nonzeros:            nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | [] => []
  | x :: xs =>
    match oddb x with
    | true => x :: (oddmembers xs)
    | false => oddmembers xs
    end
  end.

Example test_oddmembers:            oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist := 
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.

Fixpoint subalternate (n : nat) (ys l1 l2 : natlist) : natlist :=
  match n with
  | 0 => rev ys
  | S n' =>
    match l1 with
    | [] => (rev ys) ++ l2
    | x :: xs => subalternate n' (x :: ys) l2 xs
    end
  end.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  subalternate (length l1 + length l2) nil l1 l2.


(* Eval compute in alternate [1;2;3] [4;5;6]. *)

Example test_alternate1:        alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2:        alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3:        alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4:        alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Theorem nil_app_l : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'". 
    reflexivity.  Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist, 
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).   
Proof.
  intros.
  induction l1 as [|n l1'].
  reflexivity.
  simpl.
  rewrite IHl1'.
  reflexivity.
Qed.

Theorem nil_app_r : forall l:natlist,
  l ++ [] = l.
Proof.
  intros.
  induction l as [| n k].
  reflexivity.
  simpl.
  rewrite IHk.
  reflexivity.
Qed.

Theorem app_length : forall l1 l2 : natlist, 
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros.
  induction l1 as [| n l1'].
  reflexivity.
  simpl.
  rewrite IHl1'.
  reflexivity.
Qed.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros.
  induction l as [| n' l'].
  reflexivity.
  simpl.
  rewrite IHl'.
  reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros.
  induction l as [| n l'].
  reflexivity.
  simpl.
  rewrite length_snoc.
  rewrite IHl'.
  reflexivity.
Qed.

Theorem absorb_snoc : forall n m: nat, forall l : natlist, n :: (snoc l m) = snoc (n :: l) m.
Proof.
  intros.
  reflexivity.
Qed.

(* SearchAbout rev. *)

Theorem rev_snoc : forall n : nat, forall l : natlist, rev (snoc l n) = n :: rev l.
Proof.
  intros.
  induction l as [| n' l'].
  reflexivity.
  simpl.
  rewrite absorb_snoc.
  rewrite IHl'.
  reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist, rev (rev l) = l.
Proof.
  intros. induction l as [| n l'].
  reflexivity.
  simpl.
  rewrite rev_snoc.
  rewrite IHl'.
  reflexivity.
Qed.

Theorem cons_append : forall n : nat, forall l : natlist, cons n l = [n] ++ l.
Proof.
  intros.
  induction l as [|m k].
  reflexivity.
  simpl.
  reflexivity.
Qed.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros.
  induction l as [|m k].
  reflexivity.
  simpl.
  rewrite IHk.
  reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros.
  rewrite app_assoc.
  rewrite app_assoc.
  reflexivity.
Qed.

Theorem rev_injective : forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros.
  assert (H4: rev (rev l1) = l2).
    rewrite H.
    rewrite rev_involutive.
    reflexivity.
  rewrite rev_involutive in H4.
  assumption.
Qed.








