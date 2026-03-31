Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From SECF Require Import Maps.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import String.
Require Import Stdlib.Classes.EquivDec.
Set Default Goal Selector "!".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Import MonadNotation.

From SECF Require Import
  ListMaps
  MapsFunctor
  MiniCET
  Utils
  TaintTracking
  TestingSemantics.
From SECF Require Export Generation Printing Shrinking.


Definition max_block_size := 3.
Definition max_program_length := 8.

Module MCC := MiniCETCommon ListTotalMap.

Print Forall2.

Instance Forall2Dec {A B : Type} (R : A -> B -> Prop)
  (H : forall (a : A) (b : B), Dec (R a b))
  (l1 : list A) (l2 : list B) : Dec (Forall2 R l1 l2).
Proof.
  dec_eq. generalize dependent l2. induction l1.
  - destruct l2; [left; auto | right; intros contra; inversion contra].
  - intros l2.
    destruct l2.
    + right; intros contra; inversion contra.
    + destruct (IHl1 l2).
      -- set (H a b) as H1. inversion H1. destruct dec.
        ++ left. apply Forall2_cons; assumption.
        ++ right. intros contra. inversion contra; subst. contradiction.
      -- right. intros contra. inversion contra; subst. contradiction.
Qed.



Module TestingStrategies(Import ST : Semantics ListTotalMap).


Module Import MTT := TaintTracking(ST).




Variant sc_output_st : Type :=
  | SRStep : obs -> dirs -> spec_cfg -> sc_output_st
  | SRError : obs -> dirs -> spec_cfg -> sc_output_st
  | SRTerm : obs -> dirs -> spec_cfg -> sc_output_st.

Definition gen_step_direction (i: inst) (c: cfg) (pst: list nat)
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) : G dirs :=
  let '(pc, rs, m, s) := c in
  match i with
  | <{ branch e to l }> => db <- gen_dbr;; ret [db]
  | <{ call e }> =>  dc <- gen_dcall pst;; ret [dc]
  | _ => ret []
  end.

Definition gen_spec_step (p: prog) (sc:spec_cfg) (pst: list nat)
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) (gen_dret : prog -> G dir): G sc_output_st :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, sk) := c in
  match fetch p pc with
  | Some i =>
      match i with
      | <{{branch e to l}}> =>
          d <- gen_dbr;;
          ret (match spec_step p (S_Running sc) [d] with
               | (S_Running sc', dir', os') => SRStep os' [d] sc'
               | _ => SRError [] [] sc
               end)
      | <{{call e}}> =>
          d <- gen_dcall pst;;
          ret (match spec_step p (S_Running sc) [d] with
               | (S_Running sc', dir', os') => SRStep os' [d] sc'
               | _ => SRError [] [] sc
               end)
      | <{{ret}}> =>
          match sk with
          | [] =>
              ret (match spec_step p (S_Running sc) [] with
                   | (S_Term, _, _) => SRTerm [] [] sc
                   | (S_Running sc', dir', os') => SRStep os' [] sc'
                   | _ => SRError [] [] sc
                   end)
          | _ :: _ =>
              d <- gen_dret p;;
              ret (match spec_step p (S_Running sc) [d] with
                   | (S_Running sc', dir', os') => SRStep os' [d] sc'
                   | _ => SRError [] [] sc
                   end)
          end
      | ICTarget =>
          ret (match spec_step p (S_Running sc) [] with
               | (S_Running sc', dir', os') => SRStep os' [] sc'
               | (S_Term, _, _) => SRTerm [] [] sc
               | _ => SRError [] [] sc
               end)
      | _ =>
          ret (match spec_step p (S_Running sc) [] with
               | (S_Running sc', dir', os') => SRStep os' [ ] sc'
               | _ => SRError [] [] sc
               end)
      end
  | None => ret (SRError [] [] sc)
  end.

Variant spec_exec_result : Type :=
  | SETerm (sc: spec_cfg) (os: obs) (ds: dirs)
  | SEError (sc: spec_cfg) (os: obs) (ds: dirs)
  | SEOutOfFuel (sc: spec_cfg) (os: obs) (ds: dirs).

#[export] Instance showSER `{Show dir} : Show spec_exec_result :=
  {show :=fun ser =>
      match ser with
      | SETerm sc os ds => show ds
      | SEError _ _ ds => ("error!!"%string ++ show ds)%string
      | SEOutOfFuel _ _ ds => ("oof!!"%string ++ show ds)%string
      end
  }.

Fixpoint _gen_spec_steps_sized (f : nat) (p:prog) (pst: list nat) (sc: spec_cfg) (os: obs) (ds: dirs)
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) (gen_dret : prog -> G dir) : G (spec_exec_result) :=
  match f with
  | 0 => ret (SEOutOfFuel sc os ds)
  | S f' =>
      sr <- gen_spec_step p sc pst gen_dbr gen_dcall gen_dret;;
      match sr with
      | SRStep os1 ds1 sc1 =>
          _gen_spec_steps_sized f' p pst sc1 (os ++ os1) (ds ++ ds1) gen_dbr gen_dcall gen_dret
      | SRError os1 ds1 sc1 =>

          (ret (SEError sc1 (os ++ os1) (ds ++ ds1)))
      | SRTerm  os1 ds1 sc1 =>
          ret (SETerm sc1 (os ++ os1) (ds ++ ds1))
      end
  end.

Definition gen_spec_steps_sized (f : nat) (p:prog) (pst: list nat) (sc:spec_cfg)
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) (gen_dret : prog -> G dir) : G (spec_exec_result) :=
  _gen_spec_steps_sized f p pst sc [] [] gen_dbr gen_dcall gen_dret.


Definition spec_step_acc (p:prog) (sc:spec_cfg) (ds: dirs) : sc_output_st :=
  match spec_step p (S_Running sc) ds with
  | (S_Running sc', ds', os) => SRStep os ds' sc'
  | (S_Term, _, _) => SRTerm [] [] sc
  | _ => SRError [] [] sc
  end.

Fixpoint _spec_steps_acc (f : nat) (p:prog) (sc:spec_cfg) (os: obs) (ds: dirs) : spec_exec_result :=
  match f with
  | 0 => SEOutOfFuel sc os ds
  | S f' =>
      match spec_step_acc p sc ds with
      | SRStep os1 ds1 sc1 =>
          _spec_steps_acc f' p sc1 (os ++ os1) ds1
      | SRError os1 ds1 sc1 =>
          (SEError sc1 (os ++ os1) ds1)
      | SRTerm os1 ds1 sc1 =>
          (SETerm sc1 (os ++ os1) ds1)
      end
  end.

Definition spec_steps_acc (f : nat) (p:prog) (sc:spec_cfg) (ds: dirs) : spec_exec_result :=
  _spec_steps_acc f p sc [] ds.

Definition load_store_trans_basic_blk := (
    forAll (gen_prog_wt_with_basic_blk max_block_size max_program_length) (fun '(c, tm, pst, p) =>
      List.forallb basic_block_checker (map fst (transform_load_store_prog c tm p)))
).

Definition stuck_free (f : nat) (p : prog) (c: cfg) : exec_result :=
  let '(pc, rs, m, ts) := c in
  let tpc := [] in
  let trs := ([], map (fun x => (x,[@inl reg_id mem_addr x])) (map_dom (snd rs))) in
  let tm := init_taint_mem m in
  let ts := [] in
  let tc := (tpc, trs, tm, ts) in
  let ist := (c, tc, []) in
  steps_taint_track f p ist [].

Definition load_store_trans_stuck_free := (
  forAll (gen_prog_wt_with_basic_blk max_block_size max_program_length) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst 1000) (fun m =>
  let p' := transform_load_store_prog c tm p in
  let icfg := (ipc, "sp" !-> N (Datatypes.length m - 1000); rs, m, istk) in
  let r1 := stuck_free 1000 p' icfg in
  match r1 with
  | ETerm st os => checker true
  | EOutOfFuel st os => checker tt
  | EError st os => printTestCase (show p' ++ nl) (checker false)
  end)))).

Definition no_obs_prog_no_obs := (
  forAll gen_no_obs_prog (fun p =>
  let icfg := (ipc, empty_rs, empty_mem, istk) in
    match taint_tracking 10 p icfg with
    | Some (_, leaked_vars, leaked_mems) =>
        checker (seq.nilp leaked_vars && seq.nilp leaked_mems)
    | None => checker tt
    end
  )).

Definition gen_prog_and_unused_var : G (rctx * tmem * list nat * prog * string) :=
  '(c, tm, pst, p) <- (gen_prog_wt_with_basic_blk 3 5);;
  let used_vars := remove_dupes String.eqb (vars_prog p) in
  let unused_vars := filter (fun v => negb (existsb (String.eqb v) used_vars)) all_possible_vars in
  if seq.nilp unused_vars then
    ret (c, tm, pst, p, "X15"%string)
  else
    x <- elems_ "X0"%string unused_vars;;
    ret (c, tm, pst, p, x).

Definition unused_var_no_leak `{Show input_st}
  (transform_prog : rctx -> tmem -> prog -> prog) := (
  forAll gen_prog_and_unused_var (fun '(c, tm, pst, p, unused_var) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst 105) (fun m =>
  let icfg := (ipc, "sp" !-> N (Datatypes.length m - 100); rs, m, istk) in
  let p' := transform_prog c tm p in
  match stuck_free 100 p' icfg with
  | ETerm (_, _, tobs) os =>
      let (ids, mems) := split_sum_list tobs in
      let leaked_vars := remove_dupes String.eqb ids in
      checker (negb (existsb (String.eqb unused_var) leaked_vars))
  | EOutOfFuel st os => checker tt
  | EError st os => printTestCase (show st) (checker false)
  end)))).

Definition gen_pub_equiv_same_ty (P : total_map label) (s: total_map val) : G (total_map val) :=
  let f := fun v => match v with
                 | N _ => n <- arbitrary;; ret (N n)
                 | FP _ => l <- arbitrary;; ret (FP l)
                 | UV => ret UV
                 end in
  let '(d, m) := s in
  new_m <- List.fold_left (fun (acc : G (Map val)) (c : string * val) => let '(k, v) := c in
    new_m <- acc;;
    new_v <- (if t_apply P k then ret v else f v);;
    ret ((k, new_v)::new_m)
  ) m (ret []);;
  ret (d, new_m).

Definition gen_pub_equiv_is_pub_equiv := (forAll gen_pub_vars (fun P =>
    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv_same_ty P s1) (fun s2 =>
      pub_equivb P s1 s2
  )))).

Definition gen_reg_wt_is_wt := (
  forAll (gen_prog_ty_ctx_wt' max_block_size max_program_length) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs => rs_wtb rs c))).

Definition gen_pub_mem_equiv_is_pub_equiv := (forAll gen_pub_mem (fun P =>
    forAll gen_mem (fun s1 =>
    forAll (gen_pub_mem_equiv_same_ty P s1) (fun s2 =>
      (checker (pub_equiv_listb P s1 s2))
    )))).

Definition gen_mem_wt_is_wt := (
  forAll (gen_prog_ty_ctx_wt' max_block_size max_program_length) (fun '(c, tm, pst, p) =>
  forAll (gen_wt_mem tm pst 100) (fun m => m_wtb m tm))).

Definition test_ni (transform : rctx -> tmem -> prog -> prog) := (
  forAll (gen_prog_wt_with_basic_blk max_block_size max_program_length) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst 100) (fun m =>
  let icfg := (ipc, "sp" !-> N (Datatypes.length m - 100); rs, m, istk) in
  let p' := transform c tm p in
  let r1 := taint_tracking 100 p' icfg in
  match r1 with
  | Some (os1', tvars, tms) =>
      let P := (false, map (fun x => (x,true)) tvars) in
      let PM := tms_to_pm (Datatypes.length m) tms in
      forAll (gen_pub_equiv_same_ty P rs) (fun rs' =>
      forAll (gen_pub_mem_equiv_same_ty PM m) (fun m' =>
      let icfg' := (ipc, "sp" !-> N (Datatypes.length m - 100); rs', m', istk) in
      let r2 := taint_tracking 100 p' icfg' in
      match r2 with
      | Some (os2', _, _) => checker (obs_eqb os1' os2')
      | None => checker false
      end))
   | None => checker tt
  end)))).

Definition test_safety_preservation `{Show dir}
  (harden : prog -> prog)
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) (gen_dret : prog -> G dir) := (
  forAll (gen_prog_wt_with_basic_blk max_block_size max_program_length) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst 200) (fun m =>
  let rs := "sp" !-> N (Datatypes.length m - 200); rs in
  let icfg := (ipc, rs, m, istk) in
  let p' := transform_load_store_prog c tm p in
  let harden := harden p' in
  let rs' := spec_rs rs in
  let icfg' := (ipc, rs', m, istk) in
  let iscfg := (icfg', true, false) in
  let h_pst := pst_calc harden in
  forAll (gen_spec_steps_sized 200 harden h_pst iscfg gen_dbr gen_dcall gen_dret) (fun ods =>
  (match ods with
   | SETerm sc os ds => checker true
   | SEError (c', _, _) _ ds => checker false
   | SEOutOfFuel _ _ ds => checker tt
   end))
  )))).

Definition test_relative_security `{Show dir}
  (harden : prog -> prog)
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) (gen_dret : prog -> G dir) := (
  forAll (gen_prog_wt_with_basic_blk max_block_size max_program_length) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs1 =>
  forAll (gen_wt_mem tm pst 1000) (fun m1 =>
  let rs1 := "sp" !-> N (Datatypes.length m1 - 1000); rs1 in
  let icfg1 := (ipc, rs1, m1, istk) in
  let p' := transform_load_store_prog c tm p in
  let r1 := taint_tracking 1000 p' icfg1 in
  match r1 with
  | Some (os1', tvars, tms) =>
      let P := (false, map (fun x => (x,true)) tvars) in
      let PM := tms_to_pm (Datatypes.length m1) tms in
      forAll (gen_pub_equiv_same_ty P rs1) (fun rs2 =>
      let rs2 := "sp" !-> N (Datatypes.length m1 - 1000); rs2 in
      forAll (gen_pub_mem_equiv_same_ty PM m1) (fun m2 =>
      let icfg2 := (ipc, rs2, m2, istk) in
      let r2 := taint_tracking 1000 p' icfg2 in
      match r2 with
      | Some (os2', _, _) =>
          if (obs_eqb os1' os2')
          then (let harden := harden p' in
                let rs1' := spec_rs rs1 in
                let icfg1' := (ipc, rs1', m1, istk) in
                let iscfg1' := (icfg1', true, false) in
                let h_pst := pst_calc harden in
                forAll (gen_spec_steps_sized 1000 harden h_pst iscfg1' gen_dbr gen_dcall gen_dret) (fun ods1 =>
                (match ods1 with
                 | SETerm _ os1 ds =>

                     let rs2' := spec_rs rs2 in
                     let icfg2' := (ipc, rs2', m2, istk) in
                     let iscfg2' := (icfg2', true, false) in
                     let sc_r2 := spec_steps_acc 1000 harden iscfg2' ds in
                     match sc_r2 with
                     | SETerm _ os2 _ => printTestCase (show os1 ++ show os2) (checker (obs_eqb os1 os2))
                     | SEOutOfFuel _ _ _ => collect "se2 oof"%string (checker tt)
                     | _ => collect "2nd speculative execution fails!"%string (checker tt)
                     end
                 | SEOutOfFuel _ os1 ds =>
                     let rs2' := spec_rs rs2 in
                     let icfg2' := (ipc, rs2', m2, istk) in
                     let iscfg2' := (icfg2', true, false) in
                     let sc_r2 := spec_steps_acc 1000 harden iscfg2' ds in
                     match sc_r2 with
                     | SETerm _ os2 _ => collect "se1 oof but se2 term"%string (checker tt)
                     | SEOutOfFuel _ os2 _ => checker (obs_eqb os1 os2)
                     | _ => collect "2nd speculative execution fails!"%string (checker tt)
                     end
                 | _ =>  collect "1st speculative execution fails!"%string (checker tt)
                 end))
               )
          else collect "seq obs differ"%string (checker tt)
      | None => collect "tt2 failed"%string (checker tt)
      end))
   | None => collect "tt1 failed"%string (checker tt)
  end)))).

End TestingStrategies.
