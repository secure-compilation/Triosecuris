From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Export Strings.String.
From Coq Require Import FunctionalExtensionality.
From Coq.Classes Require Import EquivDec.
From Coq Require Import List.
From SECF Require Import Maps.
From SECF Require Import ListMaps.
From SECF Require Import Utils.

Import ListNotations.
Set Default Goal Selector "!".

Module Type TMap.
  Parameter t: Type -> Type -> Type.
  Parameter init: forall {R A: Type}, A -> t R A.
  Parameter t_apply: forall {R A: Type} `{EqDec R eq}, t R A -> R -> A.
  Parameter t_update: forall {R A: Type} `{EqDec R eq}, t R A -> R -> A -> t R A.
  Parameter t_map_values : forall {R A B : Type} `{EqDec R eq}, (A -> B) -> t R A -> t R B.

  Axiom t_update_eq : forall {R A : Type} `{EqDec R eq} (m : t R A) x v,
    t_apply (t_update m x v) x = v.

  Axiom t_update_neq : forall {R A : Type} `{EqDec R eq} (m : t R A) x1 x2 v,
    x1 <> x2 ->
    t_apply (t_update m x1 v) x2 = t_apply m x2.

End TMap.

Module TotalMap <: TMap.
  Definition t := Maps.total_map.
  Definition init:= @Maps.t_empty.
  Definition t_apply {R A: Type} `{EqDec R eq} (m: t R A) (i: R) : A := m i.
  Definition t_update {R A: Type} `{EqDec R eq} (m: t R A) (i: R) (v: A) := Maps.t_update m i v.
  Definition t_map_values {R A B : Type} `{EqDec R eq} (f : A -> B) (m : t R A) : t R B :=
    fun k => f (m k).

  Lemma t_update_eq : forall {R A : Type} `{EqDec R eq} (m : t R A) x v,
    t_apply (t_update m x v) x = v.
  Proof. intros. apply Maps.t_update_eq. Qed.

  Lemma t_update_neq : forall {R A : Type} `{EqDec R eq} (m : t R A) x1 x2 v,
    x1 <> x2 ->
    t_apply (t_update m x1 v) x2 = t_apply m x2.
  Proof. intros. apply Maps.t_update_neq. assumption. Qed.

End TotalMap.


Module ListTotalMap <: TMap.
  Definition t := ListMaps.total_map.
  Definition init := @ListMaps.t_empty.
  Definition t_apply {R A: Type} `{EqDec R eq} (m: t R A) (i: R) : A := ListMaps.apply m i.
  Definition t_update {R A: Type} `{EqDec R eq} (m: t R A) (i: R) (v: A) := ListMaps.t_update m i v.
  Definition t_map_values {R A B : Type} `{EqDec R eq} (f : A -> B) (m : t R A) : t R B :=
    let '(d, m) := m in
    (f d, map (fun '(k, v) => (k, f v)) m).

  Lemma t_update_eq : forall {R A : Type} `{EqDec R eq} (m : t R A) x v,
    t_apply (t_update m x v) x = v.
  Proof. intros. apply ListMaps.t_update_eq. Qed.

  Lemma t_update_neq : forall {R A : Type} `{EqDec R eq} (m : t R A) x1 x2 v,
    x1 <> x2 ->
    t_apply (t_update m x1 v) x2 = t_apply m x2.
  Proof. intros. apply ListMaps.t_update_neq. assumption. Qed.

End ListTotalMap.
