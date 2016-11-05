Theorem plus_O_n: forall n : nat , (plus O n) = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_O_n': forall n : nat, (plus O n) = n.
Proof.
  intros n. reflexivity. Qed.


Theorem plus_1_1 : forall n : nat, ((S O) + n) = (S n).
Proof.
  intros n. simpl. reflexivity. Qed.



