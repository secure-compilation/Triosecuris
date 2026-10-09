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
  Parameter t: Type -> Type.
  Parameter init: forall {A: Type}, A -> t A.
  Parameter t_apply: forall {A: Type}, t A -> string -> A.
  Parameter t_update: forall {A: Type}, t A -> string -> A -> t A.
  Parameter t_map_values : forall {A B : Type}, (A -> B) -> t A -> t B.

  Axiom t_update_eq : forall {A : Type} (m : t A) x v,
    t_apply (t_update m x v) x = v.

  Axiom t_update_neq : forall {A : Type} (m : t A) x1 x2 v,
    x1 <> x2 ->
    t_apply (t_update m x1 v) x2 = t_apply m x2.

End TMap.

Module TotalMap <: TMap.
  Definition t := Maps.total_map string.
  Definition init := @Maps.t_empty string.
  Definition t_apply {A: Type} (m: t A) (i: string) : A := m i.
  Definition t_update {A: Type} (m: t A) (i: string) (v: A) := Maps.t_update m i v.
  Definition t_map_values {A B : Type} (f : A -> B) (m : t A) : t B :=
    fun k => f (m k).

  Lemma t_update_eq : forall {A : Type} (m : t A) x v,
    t_apply (t_update m x v) x = v.
  Proof. intros. apply Maps.t_update_eq. Qed.

  Lemma t_update_neq : forall {A : Type} (m : t A) x1 x2 v,
    x1 <> x2 ->
    t_apply (t_update m x1 v) x2 = t_apply m x2.
  Proof. intros. apply Maps.t_update_neq. assumption. Qed.

End TotalMap.


Module ListTotalMap <: TMap.
  Definition t := ListMaps.total_map string.
  Definition init := @ListMaps.t_empty string.
  Definition t_apply {A: Type} (m: t A) (i: string) : A := ListMaps.apply m i.
  Definition t_update {A: Type} (m: t A) (i: string) (v: A) := ListMaps.t_update m i v.
  Definition t_map_values {A B : Type} (f : A -> B) (m : t A) : t B :=
    let '(d, m) := m in
    (f d, map (fun '(k, v) => (k, f v)) m).

  Lemma t_update_eq : forall {A : Type} (m : t A) x v,
    t_apply (t_update m x v) x = v.
  Proof. intros. apply ListMaps.t_update_eq. Qed.

  Lemma t_update_neq : forall {A : Type} (m : t A) x1 x2 v,
    x1 <> x2 ->
    t_apply (t_update m x1 v) x2 = t_apply m x2.
  Proof. intros. apply ListMaps.t_update_neq. assumption. Qed.

End ListTotalMap.
