Require Import well_order_of_nat.

Fixpoint mul (x : nat) (y : nat) : nat :=
  match y with
  | E => x
  | n ' => (mul x n) + x
end.

Notation "x * y" := (mul x y).

Example assert_mul : E + E ' ' * E ' = E ' ' ' ' ' '.
Proof. reflexivity. Qed.

Lemma e_mul_x : forall x : nat, x = E * x.
Proof.
  induction x.
  + reflexivity.
  + simpl. rewrite <- IHx. reflexivity.
Qed.

Lemma x_mul_e : forall x : nat, x = x * E.
Proof. reflexivity. Qed.

Theorem mul_right_dis : forall x y n : nat, (x + y) * n = (x * n) + (y * n).
Proof.
  intros.
  induction n.
  + reflexivity.
  + simpl.
    (* trivial algebra transformation *)
    rewrite -> (add_ass (x * n) x (y * n + y)).
    rewrite <- (add_ass x (y * n) y).
    rewrite -> (add_com x (y * n)).
    rewrite -> (add_ass (y * n) x y).
    rewrite <- (add_ass (x * n) (y * n) (x + y)).
    apply add_right_canc.
    assumption.
Qed.

Theorem mul_com : forall x y : nat, x * y = y * x.
Proof.
intros.
induction x.
+ rewrite <- e_mul_x. reflexivity.
+ simpl.
rewrite x_add_e.
rewrite mul_right_dis.
rewrite <- e_mul_x.
rewrite IHx.
reflexivity.
Qed.

Theorem mul_left_dis : forall x y n : nat, n * (x + y) = (n * x) + (n * y).
Proof.
  intros.
  rewrite (mul_com n (x + y)).
  rewrite (mul_com n x).
  rewrite (mul_com n y).
  rewrite mul_right_dis.
  reflexivity.
Qed.

Theorem mul_ass : forall x y z : nat, x * (y * z) = (x * y) * z.
Proof.
  intros.
  induction z.
  + rewrite <- x_mul_e. rewrite <- x_mul_e. reflexivity.
  + simpl.
    rewrite mul_left_dis.
    apply add_right_canc.
    assumption.
Qed.