From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Export Strings.String.
From Coq Require Import FunctionalExtensionality.
From Coq Require Import List.
Require Import Stdlib.Classes.EquivDec.
Import ListNotations.
Set Default Goal Selector "!".
Open Scope string_scope.
From SECF Require Import Utils.

Definition total_map (R A : Type) := R -> A.

Definition t_empty {R A : Type} (v : A) (x : R) : A := v.
Arguments t_empty {R A} _ _ /.

Definition t_update {R A : Type} `{EqDec R eq} (m : total_map R A)
                    (x : R) (v : A) (x' : R) : A :=
  if x ==b x' then v else m x'.
Arguments t_update {R A _ _} _ _ _ _ /.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true) "bar" true.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty: total_map string bool := (_ !-> false).


Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).

Example update_example1 : examplemap' "baz" = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap' "foo" = true.
Proof. reflexivity. Qed.

Example update_example3 : examplemap' "quux" = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap' "bar" = true.
Proof. reflexivity. Qed.

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof. reflexivity. Qed.

Lemma t_update_eq : forall (R A : Type) `{EqDec R eq} (m : total_map R A) x v,
  (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update.
  rewrite eqb_refl.
  reflexivity.
Qed.

Theorem t_update_neq : forall (R A : Type) `{EqDec R eq} (m : total_map R A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
  intros R A EQUIV EQDEC m x1 x2 v.
  intros Hneq.
  apply eqb_neq in Hneq.
  simpl. 
  rewrite -> Hneq.
  reflexivity.
Qed.

Lemma t_update_shadow : forall (R A : Type) `{EqDec R eq} (m : total_map R A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros R A EQUIV EQDEC m x v1 v2.
  apply functional_extensionality. intros x'.
  unfold t_update. destruct (x ==b x').
  - reflexivity.
  - reflexivity.
Qed.

Theorem t_update_same : forall (R A : Type) `{EqDec R eq} (m : total_map R A) x,
  (x !-> m x ; m) = m.
Proof.
  intros R A EQUIV EQDEC m x1. apply functional_extensionality. intros x2.
  unfold t_update.
  destruct (eqb_spec x1 x2) as [H | H].
  - rewrite H. reflexivity.
  - reflexivity.
Qed.

Theorem t_update_permute : forall (R A : Type) `{EqDec R eq} (m : total_map R A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros R A EQUIV EQDEC m v1 v2 x1 x2 H.
  apply functional_extensionality. intros x3.
  apply eqb_neq in H.
  unfold t_update.
  destruct (eqb_spec x1 x3) as [Heq | Hneq].
  - rewrite Heq in H. rewrite H. reflexivity.
  - reflexivity.
Qed.

Definition partial_map (R A : Type) := total_map R (option A).

Definition empty {R A : Type} : partial_map R A :=
  t_empty None.
Arguments empty {R A} _ /.

Definition update {R A : Type} `{EqDec R eq} (m : partial_map R A)
           (x : R) (v : A) :=
  (x !-> Some v ; m).
Arguments update {R A _ _} _ _ _ _ /.

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).

Definition examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).

Lemma apply_empty : forall (R A : Type) `{EqDec R eq} (x : R),
  @empty R A x = None.
Proof.
  reflexivity. 
Qed.

Lemma update_eq : forall (R A : Type) `{EqDec R eq} (m : partial_map R A) x v,
  (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

#[global] Hint Resolve update_eq : core.

Theorem update_neq : forall (R A : Type) `{EqDec R eq} (m : partial_map R A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Proof.
  intros R A EQUIV EQDEC m x1 x2 v H.
  apply eqb_neq in H. simpl. rewrite H. reflexivity.
Qed.

Lemma update_shadow : forall (R A : Type) `{EqDec R eq} (m : partial_map R A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros R A EQUIV EQDEC m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (R A : Type) `{EqDec R eq} (m : partial_map R A) x v,
  m x = Some v ->
  (x |-> v ; m) = m.
Proof.
  intros R A EQDEC EQUIV m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (R A : Type) `{EqDec R eq} (m : partial_map R A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros R A EQDEC EQUIV m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.

Definition includedin {R A : Type} `{EqDec R eq} (m m' : partial_map R A) :=
  forall x v, m x = Some v -> m' x = Some v.

Lemma includedin_update : forall (R A : Type) `{EqDec R eq} (m m' : partial_map R A)
                                 (x : R) (vx : A),
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold includedin.
  intros R A EQUIV EQDEC m m' x vx H.
  intros y vy.
  destruct (eqb_spec x y) as [Hxy | Hxy].
  - rewrite Hxy.
    rewrite update_eq. rewrite update_eq. intro H1. apply H1.
  - rewrite update_neq.
    + rewrite update_neq.
      * apply H.
      * apply Hxy.
    + apply Hxy.
Qed.

(* Definitions we use *)
Definition string_tmap := total_map string.
Definition string_map  := partial_map string.

Definition nat_tmap    := total_map nat.
Definition nat_map    := partial_map nat.