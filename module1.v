Module Playground1.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Definition pred (n : nat) : nat :=
match n with 
| O => O
| S n' => n'
end.

Definition succ (n:nat) :nat :=
match n with 
| O => (S O)
| S n' => S (S n')
end.

Definition minustwo (n: nat) : nat :=
match n with
| O => O
| S O => O
| S (S n') => n'
end.

Fixpoint evenb (n:nat) : bool :=
match n with 
| O => true
| S O => false
| S n' => negb (evenb n')
end.

Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.


End Playground1.

Module Playground2.

Fixpoint plus (n:nat) (m:nat) : nat :=
match n with
| O => m
| S n' => S (plus n' m)
end.

Fixpoint mult (n m :nat) : nat :=
match n with
| O => O
| S O => m
| S n' => plus m (mult n' m)
end.

Fixpoint minus (n m : nat) : nat :=
match n, m with 
| O, _ => O
| S n', O => n
| S n, S m => minus n m
end.

End Playground2.

Fixpoint exp (base power :nat) : nat :=
match power with
| O => S O
| S n => mult base (exp base n)
end.

Fixpoint factorial (n:nat) : nat :=
match n with 
| O => S O
| S O => S O
| S n' => mult n (factorial n')
end.



End Playground2.

