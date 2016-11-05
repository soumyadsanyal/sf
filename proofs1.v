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



Theorem mult_S_1 : forall n m : nat,
m = S n ->
m * ((S O) + n) = m * m.
Proof.
intros n m.
intros H.
rewrite plus_1_1.
rewrite <- H.
reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
beq_nat (n + (S O)) O = false.
Proof.
intros n.
destruct n as [| n'].
reflexivity.
reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry' : forall n : nat,
beq_nat (n + (S O)) O = false.
Proof.
intros n.
destruct n as [| n'].
- simpl.
- reflexivity.
- simpl.
- reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
(negb (negb b)) = b.
Proof.
intro b.
simpl.
destruct b.
- simpl.
- reflexivity.
- simpl.
- reflexivity.
Qed.

Theorem andb_commutative : forall b c: bool, 
andb b c = andb c b.
Proof.
intros b c.
destruct b.
destruct c.
- simpl.
- reflexivity.
- simpl.
- reflexivity.
- destruct c.
- simpl.
- reflexivity.
- simpl.
- reflexivity.
Qed.





