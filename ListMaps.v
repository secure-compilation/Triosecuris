From Stdlib Require Import Strings.String.
From Stdlib Require Import List. Import ListNotations.
Require Import Stdlib.Classes.EquivDec.
From SECF Require Import Utils.

Definition Map R A := list (R * A).

Fixpoint map_get {R A} `{EqDec R eq} (m : Map R A) x : option A :=
  match m with
  | [] => None
  | (k, v) :: m' => if x ==b k then Some v else map_get m' x
  end.
Definition map_set {R A} (m: Map R A) (x: R) (v:A) : Map R A := (x, v) :: m.

Fixpoint map_dom {R A} `{EqDec R eq} (m: Map R A) : list R :=
  match m with
  | [] => []
  | (k', v) :: m' => if existsb (fun p => k' ==b (fst p)) m'
                     then map_dom m'
                     else k' :: map_dom m'
  end.

Fixpoint union {R} `{EqDec R eq} (dom1 dom2 : list R) : list R :=
  match dom1 with
  | [] => dom2
  | x :: dom1' => if existsb (equiv_decb x) dom2
                  then union dom1' dom2
                  else x :: (union dom1' dom2)
  end.

Definition total_map (R X: Type) : Type := X * Map R X.

Definition t_empty {R A : Type} (d : A) : total_map R A :=
  (d, []).

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).


Definition t_update {R A : Type} (m : total_map R A)
                    (x : R) (v : A) :=
  match m with
  | (d, lm) => (d, map_set lm x v)
  end.

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).


Definition apply {R A: Type} `{EqDec R eq} (m : total_map R A) (x: R) : A :=
  match m with
  | (d, lm) => match map_get lm x with
               | Some v => v
               | None => d
               end
  end.

Definition lm_map {R A B: Type} (f: A -> B) (m: total_map R A) : total_map R B :=
  let '(d, sl) := m in
  let '(kl, vl) := split sl in
  (f d, combine kl (List.map f vl)).

Lemma t_update_eq : forall {R A : Type} `{EqDec R eq} (m : total_map R A) x v,
  apply (t_update m x v) x = v.
Proof. 
  intros.
  induction m. simpl. 
  rewrite eqb_refl.
  reflexivity.
Qed.

Lemma t_update_neq : forall {R A : Type} `{EqDec R eq} (m : total_map R A) x1 x2 v,
  x1 <> x2 ->
  apply (t_update m x1 v) x2 = apply m x2.
Proof.
  intros.
  induction m.
  simpl.
  apply eqb_neq in H0.
  rewrite eqb_symm.
  rewrite H0.
  reflexivity.
Qed.
