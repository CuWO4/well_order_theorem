Require Import Ensembles.
Require Import Classical.

(* E represents 1 *)
Inductive nat : Type := | E | Nxt (n : nat).

Notation "x '" := (Nxt x) (at level 25, right associativity).

Axiom e_no_pred : forall n : nat, n ' <> E.
Axiom only_prec : forall x y : nat, x ' = y ' <-> x = y.
(* strictly speaking, induction axiom needs to be introduced, which means
  `Axiom induct : forall P : Prop, P E /\ (forall n : nat, P n -> P (n ')) -> forall n : nat, P n.`
  it's equivalent to induction keyword anyway, which says `induction n <=> apply (induct ...); split.`,
  and is more clear.
 *)

Lemma nxt_neq_self : forall n : nat, n ' <> n.
Proof.
  induction n.
  + apply e_no_pred.
  + unfold not. intros.
    apply -> only_prec in H.
    contradiction.
Qed.

Fixpoint add (x : nat) (y : nat) : nat :=
  match y with
  | E => x '
  | n ' => (add x n) '
end.

Notation "x + y" := (add x y).

Example assert_add : E ' ' + E ' = E ' ' ' '.
Proof. reflexivity. Qed.

Lemma x_add_e : forall x : nat, x ' = x + E.
Proof. reflexivity. Qed.

Lemma e_add_x : forall x : nat, x ' = E + x.
Proof.
  induction x.
  + reflexivity.
  + simpl. rewrite <- IHx. reflexivity.
Qed.

Lemma x_nxt_add_y : forall x y : nat, x ' + y = x + y '.
Proof.
  intros.
  induction y.
  + reflexivity.
  + simpl. rewrite IHy. reflexivity.
Qed.

Theorem add_com : forall x y : nat, x + y = y + x.
Proof.
  intros.
  induction x.
  + simpl. rewrite -> e_add_x. reflexivity.
  + rewrite x_nxt_add_y. simpl.
    rewrite IHx.
    reflexivity.
Qed.

Theorem add_ass : forall x y z : nat, (x + y) + z = x + (y + z).
Proof.
  intros.
  induction x.
  + rewrite <- e_add_x. rewrite <- e_add_x. simpl.
    rewrite x_nxt_add_y. simpl.
    reflexivity.
  + rewrite x_nxt_add_y. rewrite x_nxt_add_y. simpl. rewrite x_nxt_add_y. simpl.
    rewrite IHx.
    reflexivity.
Qed.

Theorem add_right_canc : forall x y n : nat, x + n = y + n <-> x = y.
Proof.
  intros.
  split.
  + induction n.
    - simpl. apply only_prec.
    - simpl. intros. apply -> only_prec in H. apply IHn in H.
      assumption.
  + induction n.
    - simpl. intros. rewrite H. reflexivity.
    - intros. apply IHn in H. simpl. rewrite H. reflexivity.
Qed.

Theorem add_left_canc : forall x y n : nat, n + x = n + y <-> x = y.
Proof.
  intros.
  rewrite (add_com n x). rewrite (add_com n y).
  apply add_right_canc.
Qed.

Lemma impossible_add_left : forall x n : nat, n + x <> x.
Proof.
  induction x.
  + intros. rewrite <- x_add_e. apply e_no_pred.
  + intros. intros. simpl. rewrite only_prec. apply IHx.
Qed.

Lemma impossible_add_right : forall x n : nat, x + n <> x.
Proof. intros. rewrite add_com. apply impossible_add_left. Qed.

Definition gt (x y : nat) : Prop := exists n, x = y + n.
Definition ge (x y : nat) : Prop := (gt x y) \/ x = y.

Notation "x > y" := (gt x y).
Notation "x >= y" := (ge x y).

Lemma not_gt : forall x y : nat, x > y -> ~(y >= x).
Proof.
  intros.
  unfold not. intros.
  destruct H.
  destruct H0.
  - destruct H0.
    rewrite H0 in H.
    rewrite add_ass in H.
    pose proof (impossible_add_right x (x1 + x0)) as H_contra.
    symmetry in H.
    contradiction.
  - rewrite H0 in H.
    pose proof (impossible_add_right x x0) as H_contra.
    symmetry in H.
    contradiction.
Qed.

Lemma e_min : forall n : nat, n >= E.
Proof.
  intros.
  destruct n.
  + right. reflexivity.
  + rewrite x_add_e.
    left.
    exists n.
    rewrite add_com.
    reflexivity.
Qed.

Lemma succ_gt : forall n : nat, n ' > n.
Proof. intros. exists E. reflexivity. Qed.

Lemma succ_ge_trans : forall x y : nat, x > y <-> x >= y '.
Proof.
  split.
  + intros.
    destruct H.
    destruct x0.
    - right. assumption.
    - left. rewrite x_add_e in H.
      rewrite (add_com x0 E) in H.
      rewrite <- add_ass in H.
      exists x0. assumption.
  + intros.
    destruct H.
    - destruct H.
      rewrite x_add_e in H. rewrite add_ass in H.
      exists (E + x0). assumption.
    - exists E. assumption.
Qed.

Theorem gt_trans : forall x y z : nat, x > y /\ y > z -> x > z.
Proof.
  intros.
  destruct H.
  destruct H. rewrite H.
  destruct H0. rewrite H0.
  exists (x1 + x0).
  rewrite add_ass.
  reflexivity.
Qed.

Lemma choose_from_non_empty :
  forall (T : Type) (S : Ensemble T), S <> Empty_set T -> exists x, S x.
Proof.
  intros.
  apply not_all_not_ex.
  unfold not at 1. intros H_contra.
  apply H.
  apply Extensionality_Ensembles.
  split; intros x Hx.
  - contradict Hx. apply H_contra.
  - contradiction.
Qed.

Theorem well_order_of_nat : forall S : Ensemble nat,
  S = Empty_set nat
  \/ (exists s0 : nat, S s0 /\ (forall s : nat, S s -> s >= s0)).
Proof.
  intros.
  destruct (classic (S = Empty_set nat)) as [H_empty | H_non_empty].
  + left. assumption.
  + right.
    (* let T := { t | forall s in S, s >= t } be all possible lower boundary of S *)
    set (T := fun t => forall s : nat, S s -> s >= t).

    (* prove there exists t0 in T s.t. t0 ' not in T, otherwise all nat will be in
      T, but S is empty, choose any s0 in S, s0 ' is not in T *)
    assert (H_t0 : exists t0, T t0 /\ ~ T (t0 ')). {
      (* prove by contradictory *)
      apply NNPP; unfold not at 1; intros.
      assert (forall n : nat, T n). {
        induction n.
        + unfold T. intros. apply e_min.
        + apply NNPP; unfold not at 1; intros.
          apply H. exists n.
          split. - assumption. - assumption.
      }
      destruct (choose_from_non_empty nat S H_non_empty) as [s0 H_s0].
      assert (H_s0_nxt_not_in_T: ~ T (s0 ')). {
        unfold T. apply ex_not_not_all.
        exists s0.
        unfold not. intros.
        apply H1 in H_s0.
        pose proof (succ_gt s0) as H_contra.
        apply not_gt in H_contra.
        contradiction.
      }
      specialize (H0 (s0 ')).
      contradiction.
    }

    (* prove t0 in S, otherwise for all s in S, s > t0 -> s >= t0 ' -> t0 ' in T,
      contradict with ~ T (t0 ') *)
    destruct H_t0 as [t0 [H_t0 H_t0_nxt]].
    assert (S t0). {
      apply NNPP; unfold not at 1; intros.
      assert (T (t0 ')). {
        unfold T in H_t0.
        assert (forall s : nat, S s -> s > t0). {
          assert (forall s : nat, S s -> s <> t0). {
            intros.
            apply NNPP; unfold not at 1; intros.
            apply NNPP in H1.
            rewrite <- H1 in H.
            contradiction.
          }
          intros.
          specialize (H_t0 s). specialize (H0 s).
          assert (s >= t0) by ( apply H_t0 in H1; assumption ).
          assert (s <> t0) by ( apply H0 in H1; assumption ).
          unfold ge in H2. destruct H2.
          - assumption.
          - contradiction.
        }
        unfold T. intros.
        apply succ_ge_trans.
        specialize (H0 s). apply H0 in H1.
        assumption.
      }
      contradiction.
    }

    (* therefore, t0 is needed s0 *)
    exists t0.
    split.
    - assumption.
    - unfold T in H_t0. assumption.
Qed.