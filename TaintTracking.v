Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From SECF Require Import Maps.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
Set Default Goal Selector "!".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Data.List.
Import MonadNotation.
From Stdlib Require Import String.
From SECF Require Import ListMaps MapsFunctor MiniCET Utils TestingSemantics.
Require Import Stdlib.Classes.EquivDec.


Notation t_apply := ListTotalMap.t_apply.

Definition reg_id := string.
Definition mem_addr := nat.

Definition taint : Type := list (reg_id + mem_addr).

#[export] Instance showTaint : Show (reg_id + mem_addr) :=
  {show := fun x =>
     match x with
     | inl x => show x
     | inr a => show a
     end}.

Definition sum_eqb (s1 s2 : (reg_id + mem_addr)) : bool :=
  match s1, s2 with
  | inl x1, inl x2 => String.eqb x1 x2
  | inr x1, inr x2 => Nat.eqb x1 x2
  | _, _ => false
  end.

Definition join_taints t1 t2 := remove_dupes sum_eqb (t1 ++ t2).

Module TaintTracking (Import ST: Semantics ListTotalMap).

Definition tcptr := taint.
Definition treg := ListTotalMap.t taint.
Definition tamem := list taint.
Definition tstk := list tcptr.

Definition tcfg := (tcptr * treg * tamem * tstk)%type.
Definition input_st : Type := ST.cfg * tcfg * taint.



Variant output_st (A : Type) : Type :=
  | RStep : A -> obs -> input_st -> output_st A
  | RError : obs -> input_st -> output_st A
  | RTerm : obs -> input_st -> output_st A.

Record evaluator (A : Type) : Type := mkEvaluator
  { evaluate : input_st -> output_st A }.



Definition interpreter: Type := evaluator unit.


#[export] Instance monadEvaluator: Monad evaluator :=
  { ret := fun A value => mkEvaluator A (fun (ist : input_st) => RStep A value [] ist);
    bind := fun A B e f =>
      mkEvaluator B (fun (ist : input_st) =>
        match evaluate A e ist with
        | RStep _ value os1 ist'  =>
            match evaluate B (f value) ist' with
            | RStep _ value os2 ist'' => RStep B value (os1 ++ os2) ist''
            | RError _ os2 ist'' => RError B (os1 ++ os2) ist''
            | RTerm _ os2 ist'' => RTerm B (os1 ++ os2) ist''
            end
        | RError _ os ist' => RError B os ist'
        | RTerm _ os ist' => RTerm B os ist'
        end
      )
  }.

Fixpoint _calc_taint_exp (e: exp) (tr: treg) : taint :=
  match e with
  | ANum _ | FPtr _ => []
  | AId x => t_apply tr x
  | ABin _ e1 e2 => join_taints (_calc_taint_exp e1 tr) (_calc_taint_exp e2 tr)
  | ACTIf e1 e2 e3 => join_taints (_calc_taint_exp e1 tr)
                                 (join_taints (_calc_taint_exp e2 tr) (_calc_taint_exp e3 tr))
  end.

Variant taint_ctx :=
  | CMem (n: nat)
  | CDefault.

Definition taint_step (i: inst) (c: ST.cfg) (tc: tcfg) (tobs: taint) (tctx: taint_ctx) : option (tcfg * taint) :=
  let '(pc, rs, m, s) := c in
  let '(tpc, trs, tm, ts) := tc in
  match i with
  | <{ skip }> | <{ ctarget }> | <{ jump _ }> =>
      match tctx with
      | CDefault => Some (tc, tobs)
      | _ => None
      end
  | <{ x := e }> =>
      match tctx with
      | CDefault =>
          let te := (_calc_taint_exp e trs) in
          let tx := join_taints te tpc in
          let tc' := (tpc, (x !-> tx; trs), tm, ts) in
          Some (tc', tobs)
      | _ => None
      end

  | <{ x <- div e1, e2 }> =>
      match tctx with
      | CDefault =>
        let te1 := _calc_taint_exp e1 trs in
        let te2 := _calc_taint_exp e2 trs in
        let tx := join_taints (join_taints te1 te2) tpc in
        let tc' := (tpc, (x !-> tx; trs), tm, ts) in
        let tobs' := join_taints tobs (join_taints (join_taints te1 te2) tpc) in
        Some (tc', tobs')
      | _ => None
      end
  | <{ branch e to l }> =>
      match tctx with
      | CDefault =>
          let te := (_calc_taint_exp e trs) in
          let tpc' := join_taints te tpc in
          let tc' := (tpc', trs, tm, ts) in
          let tobs' := join_taints tobs tpc' in
          Some (tc', tobs')
      | _ => None
      end
  | <{ x <- load[e] }> =>
      match tctx with
      | CMem n =>
          let te := (_calc_taint_exp e trs) in
          let tv := nth n tm [] in
          let tx := (join_taints (join_taints te tv) tpc) in
          let tc' := (tpc, (x !-> tx; trs), tm, ts) in
          let tobs' := (join_taints (join_taints te tpc) tobs) in
          Some (tc', tobs')
      | _ => None
      end
  | <{ store[e] <- e' }> =>
      match tctx with
      | CMem n =>
          let te := (_calc_taint_exp e trs) in
          let te' := (_calc_taint_exp e' trs) in
          let tm_val := join_taints   te' tpc in
          let tc' := (tpc, trs, upd n tm tm_val, ts) in
          let tobs' := join_taints (join_taints te tpc) tobs in
          Some (tc', tobs')
      | _ => None
      end
  | <{ call e }> =>
      match tctx with
      | CDefault =>
          let te := (_calc_taint_exp e trs) in
          let ts' := tpc :: ts in
          let tpc' := join_taints te tpc in
          let tc' := (tpc', trs, tm, ts') in
          let tobs' := join_taints tobs tpc' in
          Some (tc', tobs')
      | _ => None
      end

  | <{ x <- peek }> =>
      match tctx with
      | CDefault =>
          let tx' := hd [] ts in
          let tc' := (tpc, (x !-> tx'; trs), tm, ts) in
          Some (tc', tobs)
      | _ => None
      end
  | <{ ret }> =>
      match tctx with
      | CDefault =>
          let tpc' := hd [] ts in
          let ts' := tl ts in
          let tc' := (tpc', trs, tm, ts') in
          Some (tc', tobs)
      | _ => None
      end
  end.

Definition get_ctx (rs: ST.reg) (i: inst) : option taint_ctx  :=
  match i with
  | <{ x <- load[e] }> => n <- to_nat (ST.eval rs e);;
                        Some (CMem n)
  | <{ store[e] <- e' }> => n <- to_nat (ST.eval rs e);;
                          Some (CMem n)
  | _ => Some CDefault
  end.


Definition final_cfg (p: prog) (c: ST.cfg) : bool :=
  let '(pc, rs, m, stk) := c in
  match ST.fetch p pc with
  | Some i => match i with
             | IRet => if seq.nilp stk then true else false
             | _ => false
             end
  | None => false
  end.

Definition step_taint_track (p: prog) : evaluator unit :=
  mkEvaluator _ (fun (ist : input_st) =>
    let '(c, tc, tobs) := ist in
    let '(pc, rs, m, s) := c in
    let '(tpc, trs, tm, ts) := tc in
    match ST.step p (S_Running c) with
    | (S_Running c', os) =>
        match (ST.fetch p pc) with
        | Some i => match get_ctx rs i with
                   | Some tctx => match taint_step i c tc tobs tctx with
                                 | Some (tc', tobs') => RStep _ tt os (c', tc', tobs')
                                 | _ => RError _ [] ist
                                 end
                   | _ => RError _ [] ist
                   end
        | _ => RError _ [] ist
        end
    | (S_Term, []) => RTerm _ [] ist
    | _ => RError _ [] ist
    end).

Variant exec_result : Type :=
  | ETerm (st: input_st) (os: obs)
  | EError (st: input_st) (os: obs)
  | EOutOfFuel (st: input_st) (os: obs).

Fixpoint steps_taint_track (f: nat) (p: prog) (ist: input_st) (os: obs) : exec_result :=
  match f with
  | O => EOutOfFuel ist os
  | S f' =>
      match evaluate unit (step_taint_track p) ist with
      | RTerm _ os' ist' => ETerm ist' (os ++ os')
      | RError _ os' ist' => EError ist' (os ++ os')
      | RStep _ _ os' ist' => steps_taint_track f' p ist' (os ++ os')
      end
  end.

Fixpoint _init_taint_mem (m: mem) (n: nat) : tamem :=
  match m with
  | [] => []
  | h :: m' => ([inr n]) :: _init_taint_mem m' (S n)
  end.

Definition init_taint_mem (m: mem) : tamem :=
  _init_taint_mem m 0.

Definition taint_tracking (f : nat) (p : prog) (c: cfg)
  : option (obs * list string * list nat) :=
  let '(pc, rs, m, ts) := c in
  let tpc := [] in
  let trs := ([], map (fun x => (x,[@inl reg_id mem_addr x])) (map_dom (snd rs))) in
  let tm := init_taint_mem m in
  let ts := [] in
  let tc := (tpc, trs, tm, ts) in
  let ist := (c, tc, []) in
  match (steps_taint_track f p ist []) with
  | ETerm (_, _, tobs) os | EOutOfFuel (_, _, tobs) os =>
      let (ids, mems) := split_sum_list tobs in
      Some (os, remove_dupes String.eqb ids,
                remove_dupes Nat.eqb mems)
  | _ => None
  end.

End TaintTracking.
