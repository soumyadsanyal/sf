Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.



Definition next_weekday (d:day) : day :=
match d with 
| monday => tuesday
| tuesday => wednesday
| wednesday => thursday
| thursday => friday
| friday => monday
| saturday => monday
| sunday => monday
end.

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b: bool) : bool :=
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

Infix "&&" := andb.

Infix "||" := orb.

Definition nandb (b1:bool) (b2:bool) : bool := (negb (andb b1 b2)).

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






