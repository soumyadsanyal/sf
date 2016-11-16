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

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.

Notation "x - y" := (minus x y)
                        (at level 50,left associativity)
                        : nat_scope.

Notation "x * y" := (mult x y)
                        (at level 40,left associativity)
                        : nat_scope.


Fixpoint beq_nat (n m : nat) : bool :=
match n with
| O => match m with 
  | O => true
  | S m' => false
end
| S n' => match m with
  | O => false
  | S m' => (beq_nat n' m')
end
end.

Fixpoint blt_nat (n m : nat) : bool :=
match n with
| O => match m with
  | O => false
  | S _ => true
end
| S n' => match m with
  | O => false
  | S m' => blt_nat n' m'
end
end.

Inductive bin : Type :=
| Z : bin
| T : bin -> bin
| T' : bin -> bin.

Fixpoint incr (n : bin) : bin :=
match n with
| Z => T' Z
| T n' => T' n'
| T' n' => T (incr n')
end.

Fixpoint bin_to_nat (n: bin) : nat :=
match n with 
| Z => O
| P n' => succ (bin_to_nat n')
| T n' => succ (succ (bin_to_nat n'))
end.



