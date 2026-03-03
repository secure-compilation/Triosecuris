From Stdlib Require Import List Arith.
Import ListNotations.

Fixpoint rev_append {A:Type} (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | x :: l1 => rev_append l1 (x :: l2)
  end.
Definition rev {A : Type} (l : list A) := rev_append l [].
Definition app {A:Type} (l1:list A) := rev_append (rev l1).
Notation "x ++ y" := (app x y) (right associativity, at level 60).

Lemma rev_append_correct {A} (l1 l2 : list A) :
  rev_append l1 l2 = List.app (List.rev l1) l2.
Proof.
  induction l1 in l2 |-*.
  { reflexivity. }
  cbn. rewrite <- app_assoc. cbn.
  apply IHl1.
Qed.

Lemma tr_app_correct {A} (l1: list A) l2 :
  app l1 l2 = List.app l1 l2.
Proof.
  induction l1.
  {reflexivity. }
  cbn. do 2 rewrite rev_append_correct.
  change [a] with (List.rev [a]).
  rewrite <- rev_app_distr.
  rewrite rev_involutive. rewrite <- app_assoc.
  reflexivity.
Qed.

Fixpoint upd {A:Type} (i:nat) (ns:list A) (n:A) : list A :=
  match i, ns with
  | 0, _ :: ns' => n :: ns'
  | S i', n' :: ns' => n' :: upd i' ns' n
  | _, _ => ns
  end.

Lemma upd_length : forall {A:Type} (l:list A) i a,
  length (upd i l a) = length l.
Proof.
  induction l; destruct i; auto.
  intros. simpl. now f_equal.
Qed.

Definition add_index {a:Type} (xs:list a) : list (nat * a) :=
  combine (seq 0 (length xs)) xs.

Lemma length_add_index {A} (p: list A) :
  Datatypes.length (add_index p) = Datatypes.length p.
Proof.
  unfold add_index.
  rewrite length_combine, length_seq, Nat.min_id. auto.
Qed.

Fixpoint split_sum_list {A B : Type} (l : list (A + B)) : (list A * list B) :=
  match l with
  | [] => ([], [])
  | inl a :: xs => let (la, lb) := split_sum_list xs in (a :: la, lb)
  | inr b :: xs => let (la, lb) := split_sum_list xs in (la, b :: lb)
  end.

Fixpoint remove_dupes {A : Type} (eqb : A -> A -> bool) (t : list A) : list A :=
  match t with
  | [] => []
  | x :: xs => if existsb (eqb x) xs
               then      remove_dupes eqb xs
               else x :: remove_dupes eqb xs
  end.

Definition prefix {X:Type} (xs ys : list X) : Prop :=
  exists zs, List.app xs zs = ys.

Lemma prefix_refl : forall {X:Type} {ds : list X},
  prefix ds ds.
Proof. intros X ds. exists []. apply app_nil_r. Qed.

Lemma prefix_nil : forall {X:Type} (ds : list X),
  prefix [] ds.
Proof. intros X ds. unfold prefix. eexists. simpl. reflexivity. Qed.

Lemma prefix_heads_and_tails : forall {X:Type} (h1 h2 : X) (t1 t2 : list X),
  prefix (h1::t1) (h2::t2) -> h1 = h2 /\ prefix t1 t2.
Proof.
  intros X h1 h2 t1 t2. unfold prefix. intros Hpre.
  destruct Hpre as [zs Hpre]; simpl in Hpre.
  inversion Hpre; subst. eauto.
Qed.

Lemma prefix_heads : forall {X:Type} (h1 h2 : X) (t1 t2 : list X),
  prefix (h1::t1) (h2::t2) -> h1 = h2.
Proof.
  intros X h1 h2 t1 t2 H. apply prefix_heads_and_tails in H; tauto.
Qed.

Lemma prefix_or_heads : forall {X:Type} (x y : X) (xs ys : list X),
  prefix (x :: xs) (y :: ys) \/ prefix (y :: ys) (x :: xs) ->
  x = y.
Proof.
  intros X x y xs ys H.
  destruct H as [H | H]; apply prefix_heads in H; congruence.
Qed.

Lemma prefix_cons : forall {X:Type} (d :X) (ds1 ds2: list X),
 prefix ds1 ds2 <->
 prefix (d::ds1) (d::ds2).
Proof.
  intros X d ds1 ds2. split; [unfold prefix| ]; intros H.
  - destruct H; subst.
    eexists; simpl; eauto.
  - apply prefix_heads_and_tails in H. destruct H as [_ H]. assumption.
Qed.

Lemma prefix_app : forall {X:Type} {ds1 ds2 ds0 ds3 : list X},
  prefix (ds1 ++ ds2) (ds0 ++ ds3) ->
  prefix ds1 ds0 \/ prefix ds0 ds1.
Proof.
  intros X ds1. induction ds1 as [| d1 ds1' IH]; intros ds2 ds0 ds3 H.
  - left. apply prefix_nil.
  - destruct ds0 as [| d0 ds0'] eqn:D0.
    + right. apply prefix_nil.
    + simpl in H; apply prefix_heads_and_tails in H.
      destruct H as [Heq Hpre]; subst.
      apply IH in Hpre; destruct Hpre; [left | right];
      apply prefix_cons; assumption.
Qed.

Lemma prefix_append_front : forall {X:Type} {ds1 ds2 ds3 : list X},
  prefix (ds1 ++ ds2) (ds1 ++ ds3) <->
  prefix ds2 ds3.
Proof.
  intros X ds1. induction ds1 as [| d1 ds1' IH]; intros ds2 ds3; split; intro H; cbn in *.
  1, 2: assumption.
  - apply prefix_cons in H. apply -> IH in H. assumption.
  - apply prefix_cons, IH. assumption.
Qed.

Lemma app_eq_prefix : forall {X:Type} {ds1 ds2 ds1' ds2' : list X},
  List.app ds1 ds2 = List.app ds1' ds2' ->
  prefix ds1 ds1' \/ prefix ds1' ds1.
Proof.
  intros X ds1. induction ds1 as [| h1 t1 IH]; intros ds2 ds1' ds2' H.
  - left. apply prefix_nil.
  - destruct ds1' as [| h1' t1'] eqn:D1'.
    + right. apply prefix_nil.
    + simpl in H; inversion H; subst.
      apply IH in H2. destruct H2 as [HL | HR];
      [left | right]; apply prefix_cons; auto.
Qed.

From Stdlib Require Import String.


Definition untrace {A : Type} (s : string) (a : A) : A := a.



Definition is_some {A} (v : option A) : bool := match v with
  | Some _ => true
  | None => false
  end.

