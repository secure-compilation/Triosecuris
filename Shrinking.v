From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
Set Default Goal Selector "!".
Require Import Stdlib.Classes.EquivDec.

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Data.List.
Import MonadNotation.

From SECF Require Import MiniCET MapsFunctor ListMaps.

Definition fold_extra {A : Type} {B : Type} (f : A -> list B -> B -> list B -> A) (l : list B) (v : A) : A :=
  let fix aux (processed : list B) (incoming : list B) (acc : A) :=
    match incoming with
    | [] => acc
    | h::t =>
        let new_acc := f acc processed h t in
        aux (processed ++ [h]) t new_acc
    end
  in aux [] l v.

#[export] Instance shrinkTotalMap {X : Type} `{Shrink X}: Shrink (ListTotalMap.t string X) :=
  {shrink := fun '(d, m) =>

      (List.map (fun d' => (d', m)) (shrink d)) ++

      (List.map
         (fun m' => (d, m'))
         (fold_extra (fun acc before '(k, v) after =>
            let modified_entry := List.map (fun v' =>
                before ++ [(k, v')] ++ after
              ) (shrink v) in

            modified_entry ++ acc
         ) m [])
      ) ++

      (List.map
         (fun m' => (d, m'))
         (fold_extra (fun acc before '(k, v) after =>
            (before ++ after) :: acc
         ) m [])
      )
  }.

#[export] Instance shrinkId : Shrink string :=
  {shrink :=
    (fun s => match String.get 1 s with
           | Some a => match (nat_of_ascii a - nat_of_ascii "0") with
                      | S n => ["X" ++ show (S n / 2); "X" ++ show (S n - 1)]
                      | 0 => []
                      end
           | None => nil
           end)%string }.

Eval compute in (shrink "X5")%string.
Eval compute in (shrink "X0")%string.

Derive Shrink for binop.
Derive Shrink for exp.
Derive Shrink for inst.
