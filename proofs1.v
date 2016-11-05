Theorem plus_O_n: forall n : nat , (plus O n) = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_O_n': forall n : nat , (O + n) = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_O_n': forall n : nat, (plus O n) = n.
Proof.
  intros n. reflexivity. Qed.


Theorem plus_1_1 : forall n : nat, ((S O) + n) = (S n).
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_1: forall n:nat, (O * n) = O.
Proof.
  intros n. reflexivity. Qed.


Theorem mult_0_11: forall n:nat, (mult O n) = O.
Proof.
  intros n. reflexivity. Qed.


Theorem plus_n_0: forall n:nat, n = (plus n O).
Proof.
  intros n. simpl. 

Theorem plus_id_example: forall n m :nat,
n = m ->
n + n = m + m.

Theorem plus_id_exercise: forall n m o : nat,
n = m -> m = o -> n + m = m + o.
Proof.
intros n m o.
intros H.
intros J.
rewrite H.
rewrite J.
reflexivity.
Qed.


Theorem mult_0_plus : forall n m: nat,
(O + n) * m = n * m.
Proof.
intros n m.
simpl.
reflexivity.
Qed.

Theorem mult_0_plus' : forall n m: nat,
(O + n) * m = n * m.
Proof.
intros n m.
rewrite mult_0_plus.
reflexivity.
Qed.


Theorem mult_0_plus'' : forall n m: nat,
(O + n) * m = n * m.
Proof.
intros n m.
rewrite plus_O_n'.
reflexivity.
Qed.


