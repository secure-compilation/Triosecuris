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


Definition max_block_size := 8.
Definition max_program_length := 5.

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
  let '(pc, rs, m) := c in
  match i with
  | <{ branch e to l }> => db <- gen_dbr;; ret [db]
  | <{ call e }> =>  dc <- gen_dcall pst;; ret [dc]
  | _ => ret []
  end.

Definition gen_spec_step (p: prog) (sc:spec_cfg) (pst: list nat)
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) (gen_dret : prog -> G dir): G sc_output_st :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m) := c in
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
          (* At the bottom of the in-memory stack the slot "sp" points at holds
             no return address, and the [ret] needs no directive. *)
          match MCC.ret_addr r m with
          | None =>
              ret (match spec_step p (S_Running sc) [] with
                   | (S_Term, _, _) => SRTerm [] [] sc
                   | (S_Running sc', dir', os') => SRStep os' [] sc'
                   | _ => SRError [] [] sc
                   end)
          | Some _ =>
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

(* The configuration a speculative run got stuck in says little on its own;
   what explains it is the stack around [sp] and the directives that led there.
   [pc] is abstract in this functor, so the position is reported by whoever
   applies it. *)
#[export] Instance showSER `{Show dir} : Show spec_exec_result :=
  {show :=fun ser =>
      match ser with
      | SETerm sc os ds => show_dirs ds
      | SEError cfg os ds =>
          let '((_, rs, m), ct, ms) := cfg in
          report "Speculative execution got stuck"%string
            (("directives"%string, show_dirs ds)
             :: ("observations"%string, show_obs os)
             :: ("mis-speculating"%string, show ms)
             :: ("registers"%string, show rs)
             :: mem_items m (t_apply rs "sp"%string))
      | SEOutOfFuel _ os ds =>
          report "Speculative execution ran out of fuel"%string
            [("directives"%string, show_dirs ds); ("observations"%string, show_obs os)]
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
    forAll (gen_prog_ty_ctx_wt max_block_size max_program_length) (fun '(c, tm, pst, p) =>
    forAll (gen_wt_mem tm pst 1000) (fun m =>
      List.forallb basic_block_checker (map fst (transform_load_store_prog c tm m p))))
).

Definition stuck_free (f : nat) (p : prog) (c: cfg) : exec_result :=
  let '(pc, rs, m) := c in
  let tpc := [] in
  let trs := ([], map (fun x => (x,[@inl reg_id mem_addr x])) (map_dom (snd rs))) in
  let tm := init_taint_mem m in
  let ts := [] in
  let tc := (tpc, trs, tm, ts) in
  let ist := (c, tc, []) in
  steps_taint_track f p ist [].

(* The next push would land outside the stack region [m] describes. *)
Definition is_stack_overflow (rs: reg) (m: mem) := match t_apply rs "sp"%string with
  | N n => (S n >= stack_top m)?
  | _ => false
  end.

Definition is_sp_fp_uv (rs: reg) := match t_apply rs "sp"%string, t_apply rs "fp"%string with
  | UV, _ => true
  | _, UV => true
  | _, _  => false
  end.

Definition load_store_trans_stuck_free := (
  forAll (gen_prog_ty_ctx_wt max_block_size max_program_length) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst 100) (fun m =>
  let p' := transform_load_store_prog c tm m p in
  let icfg := (ipc, "sp" !-> N (stack_base m); rs, m) in
  let r1 := stuck_free 1000 p' icfg in
  match r1 with
  | ETerm st os => checker true
  | EOutOfFuel st os => collect "Out-of-fuel"%string (checker tt)
  | EError st os => 
      let '((pc, rs, mem), _, _) := st in
      if is_stack_overflow rs mem then collect "Stack overflow"%string (checker tt) else (
        if is_sp_fp_uv rs then collect "Stack pointer undefined"%string (checker tt) else 
          (* the pc comes from running [p'], so the instruction does too *)
          match fetch p' pc with
          | Some <{ call _ }> => collect "Undef call"%string (checker tt)
          | Some <{ ret }>    => collect "Undef ret"%string (checker tt)
          | i => printTestCase
                  (report "The guarded program got stuck on an instruction that is not a call or a ret"%string
                     (inst_item "failing instruction"%string i
                      :: ("observations"%string, show_obs os)
                      :: ("registers"%string, show rs)
                      :: mem_items mem (t_apply rs "sp"%string)
                      ++ [prog_item "guarded program"%string None p']))
                  (checker false)
          end)
  end)))).

Definition no_obs_prog_no_obs := (
  forAll gen_no_obs_prog (fun p =>
  (* no heap, a small stack: sp starts at the stack base, which holds no return
     address, so a [ret] there terminates *)
  let m := {| heap_length := 0; stack_length := 10; memory := mkStk 10 |} in
  let icfg := (ipc, "sp" !-> N (stack_base m); empty_rs, m) in
    match taint_tracking 100 p icfg with
    | Some (_, leaked_vars, leaked_mems) =>
        checker (seq.nilp leaked_vars && seq.nilp leaked_mems)
    | None => checker tt
    end
  )).

Definition gen_prog_and_unused_var : G (rctx * tmem * list nat * prog * string) :=
  '(c, tm, pst, p) <- (gen_prog_ty_ctx_wt 3 5);;
  let used_vars := remove_dupes String.eqb (vars_prog p) in
  let unused_vars := filter (fun v => negb (existsb (String.eqb v) used_vars)) all_possible_vars in
  if seq.nilp unused_vars then
    ret (c, tm, pst, p, "X15"%string)
  else
    x <- elems_ "X0"%string unused_vars;;
    ret (c, tm, pst, p, x).

Definition unused_var_no_leak `{Show input_st}
  (transform_prog : rctx -> tmem -> mem -> prog -> prog) := (
  forAll gen_prog_and_unused_var (fun '(c, tm, pst, p, unused_var) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst 105) (fun m =>
  let icfg := (ipc, "sp" !-> N (stack_base m); rs, m) in
  let p' := transform_prog c tm m p in
  match stuck_free 100 p' icfg with
  | ETerm (_, _, tobs) os =>
      let (ids, mems) := split_sum_list tobs in
      let leaked_vars := remove_dupes String.eqb ids in
      printTestCase
        (report "A variable the program never reads was leaked"%string
           [ ("variable"%string, unused_var)
           ; ("leaked variables"%string, show leaked_vars)
           ; ("leaked addresses"%string, show mems)
           ; ("observations"%string, show_obs os)
           ; prog_item "guarded program"%string None p' ])
        (checker (negb (existsb (String.eqb unused_var) leaked_vars)))
  | EOutOfFuel st os => checker tt
  | EError st os =>
      let '((pc, rs, mem), _, _) := st in
      if is_stack_overflow rs mem then collect "Stack overflow"%string (checker tt) else
        printTestCase
          (report "Taint tracking got stuck for a reason other than stack overflow"%string
             (inst_item "failing instruction"%string (fetch p' pc)
              :: ("observations"%string, show_obs os)
              :: ("registers"%string, show rs)
              :: mem_items mem (t_apply rs "sp"%string)
              ++ [prog_item "guarded program"%string None p']))
          (checker false)
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
  forAll (gen_prog_ty_ctx_wt max_block_size max_program_length) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs => rs_wtb rs c))).

Definition gen_pub_mem_equiv_is_pub_equiv := (forAll gen_pub_mem (fun P =>
    forAll gen_mem (fun s1 =>
    forAll (gen_pub_mem_equiv_same_ty P s1) (fun s2 =>
      (checker (pub_equiv_listb P s1 s2))
    )))).

Definition gen_mem_wt_is_wt := (
  forAll (gen_prog_ty_ctx_wt max_block_size max_program_length) (fun '(c, tm, pst, p) =>
  forAll (gen_wt_mem tm pst 100) (fun m => m_wtb m tm))).

Definition test_ni (transform : rctx -> tmem -> mem -> prog -> prog) := (
  forAll (gen_prog_ty_ctx_wt max_block_size max_program_length) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst 100) (fun m =>
  let icfg := (ipc, "sp" !-> N (stack_base m); rs, m) in
  let p' := transform c tm m p in
  let r1 := taint_tracking 100 p' icfg in
  match r1 with
  | Some (os1', tvars, tms) =>
      let P := (false, map (fun x => (x,true)) tvars) in
      let PM := tms_to_pm (mem_length m) tms in
      forAll (gen_pub_equiv_same_ty P rs) (fun rs' =>
      (* the pub-equivalent run keeps the same layout, only the contents vary *)
      forAll (gen_pub_mem_equiv_same_ty PM m.(memory)) (fun m'vals =>
      let m' := with_memory m m'vals in
      let icfg' := (ipc, "sp" !-> N (stack_base m); rs', m') in
      let r2 := taint_tracking 100 p' icfg' in
      match r2 with
      | Some (os2', _, _) =>
          printTestCase
            (report "The two public-equivalent runs are distinguishable"%string
               (obs_items "run 1"%string os1' "run 2"%string os2'
                ++ [prog_item "guarded program"%string None p']))
            (checker (obs_eqb os1' os2'))
      | None =>
          printTestCase
            (report "The second public-equivalent run got stuck while the first one did not"%string
               [ ("run 1"%string, show_obs os1')
               ; prog_item "guarded program"%string None p' ])
            (checker false)
      end))
   | None => collect "tt failed"%string (checker tt)
  end)))).

Definition test_safety_preservation `{Show dir}
  (harden : prog -> prog)
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) (gen_dret : prog -> G dir) := (
  forAll (gen_prog_ty_ctx_wt max_block_size max_program_length) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs =>
  forAll (gen_wt_mem tm pst 200) (fun m =>
  let rs := "sp" !-> N (stack_base m); rs in
  let icfg := (ipc, rs, m) in
  let p' := transform_load_store_prog c tm m p in
  let harden := harden p' in
  let rs' := spec_rs rs in
  let icfg' := (ipc, rs', m) in
  let iscfg := (icfg', true, false) in
  let h_pst := pst_calc harden in
  forAll (gen_spec_steps_sized 200 harden h_pst iscfg gen_dbr gen_dcall gen_dret) (fun ods =>
  (match ods with
   | SETerm sc os ds => checker true
   | SEError c' os ds =>
      let '((pc, rs, mem), _, ms) := c' in
      if is_stack_overflow rs mem then collect "Stack overflow"%string  (checker tt) else
        (* the configuration, the directives and the trace are already in the
           [spec_exec_result] QuickChick prints *)
        printTestCase
          (report "The hardened program got stuck under speculation"%string
             [ inst_item "failing instruction"%string (fetch harden pc)
             ; prog_item "hardened program"%string None harden ])
          (checker false)
   | SEOutOfFuel _ _ ds => checker tt
   end))
  )))).

Definition test_relative_security `{Show dir}
  (harden : prog -> prog)
  (gen_dbr : G dir) (gen_dcall : list nat -> G dir) (gen_dret : prog -> G dir) := (
  forAll (gen_prog_ty_ctx_wt max_block_size max_program_length) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs1 =>
  forAll (gen_wt_mem tm pst 1000) (fun m1 =>
  let rs1 := "sp" !-> N (stack_base m1); rs1 in
  let icfg1 := (ipc, rs1, m1) in
  let p' := transform_load_store_prog c tm m1 p in
  let r1 := taint_tracking 1000 p' icfg1 in
  match r1 with
  | Some (os1', tvars, tms) =>
      let P := (false, map (fun x => (x,true)) tvars) in
      let PM := tms_to_pm (mem_length m1) tms in
      forAll (gen_pub_equiv_same_ty P rs1) (fun rs2 =>
      let rs2 := "sp" !-> N (stack_base m1); rs2 in
      (* same layout as [m1], only the contents differ *)
      forAll (gen_pub_mem_equiv_same_ty PM m1.(memory)) (fun m2vals =>
      let m2 := with_memory m1 m2vals in
      let icfg2 := (ipc, rs2, m2) in
      let r2 := taint_tracking 1000 p' icfg2 in
      match r2 with
      | Some (os2', _, _) =>
          if (obs_eqb os1' os2')
          then (let harden := harden p' in
                let rs1' := spec_rs rs1 in
                let icfg1' := (ipc, rs1', m1) in
                let iscfg1' := (icfg1', true, false) in
                let h_pst := pst_calc harden in
                forAll (gen_spec_steps_sized 1000 harden h_pst iscfg1' gen_dbr gen_dcall gen_dret) (fun ods1 =>
                (match ods1 with
                 | SETerm _ os1 ds =>

                     let rs2' := spec_rs rs2 in
                     let icfg2' := (ipc, rs2', m2) in
                     let iscfg2' := (icfg2', true, false) in
                     let sc_r2 := spec_steps_acc 1000 harden iscfg2' ds in
                     match sc_r2 with
                     | SETerm _ os2 _ =>
                         printTestCase
                           (report "The two runs agree sequentially but are distinguishable under speculation"%string
                              (obs_items "speculative run 1"%string os1
                                         "speculative run 2"%string os2
                               ++ [ ("sequential trace"%string, show_obs os1')
                                  ; prog_item "hardened program"%string None harden ]))
                           (checker (obs_eqb os1 os2))
                     | SEOutOfFuel _ _ _ => collect "se2 oof"%string (checker tt)
                     | _ => collect "2nd speculative execution fails!"%string (checker tt)
                     end
                 | SEOutOfFuel _ os1 ds =>
                     let rs2' := spec_rs rs2 in
                     let icfg2' := (ipc, rs2', m2) in
                     let iscfg2' := (icfg2', true, false) in
                     let sc_r2 := spec_steps_acc 1000 harden iscfg2' ds in
                     match sc_r2 with
                     | SETerm _ os2 _ => collect "se1 oof but se2 term"%string (checker tt)
                     | SEOutOfFuel _ os2 _ =>
                         printTestCase
                           (report "Both runs ran out of fuel, but their speculative traces differ"%string
                              [ ("speculative run 2"%string, show_obs os2)
                              ; obs_diff_item os1 os2
                              ; prog_item "hardened program"%string None harden ])
                           (checker (obs_eqb os1 os2))
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
