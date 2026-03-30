

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
Set Default Goal Selector "!".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Import MonadNotation.
From SECF Require Import MiniCET TaintTracking MapsFunctor TestingLib TestingSemantics.

(*! Section testing_ETE *)

Module Import MCC := MiniCETSemantics ListTotalMap.
Module Import TS := TestingStrategies MCC.
Module Import TT := TaintTracking MCC.

Definition max_block_size := 3.
Definition max_program_length := 8.

Definition gen_dbr : G dir :=
  b <- arbitrary;; ret (DBranch b).

Definition gen_dcall (pst: list nat) : G dir :=
  l <- (elems_ (0, 0) (proc_hd pst));; ret (DCall l).

Definition wf_ret_addrs (p: prog) : list cptr :=
  let fix all_cptrs (l: nat) (blocks: prog) :=
    match blocks with
    | [] => []
    | (blk, _) :: rest => map (fun o => (l, o)) (seq 0 (List.length blk)) ++ all_cptrs (S l) rest
    end
  in filter (wf_retb p) (all_cptrs 0 p).

Definition gen_dret (p: prog) : G dir :=
  l <- elems_ (0, 0) (wf_ret_addrs p);; ret (DRet l).

Instance ShowDirection : Show dir := {
  show dir := match dir with
    | DBranch b => ("DBranch " ++ show b)%string
    | DCall cptr => ("DCall " ++ show cptr)%string
    | DRet cptr => ("DRet" ++ show cptr)%string
  end
}.

QuickChick (forAll gen_pub_mem (fun P =>
    forAll gen_mem (fun s1 =>
    forAll (gen_pub_mem_equiv P s1) (fun s2 =>
      (checker (pub_equiv_listb P s1 s2))
    )))).

QuickChick (forAll gen_pub_vars (fun P =>
    forAll gen_state (fun s1 =>
    forAll (gen_pub_equiv P s1) (fun s2 =>
      pub_equivb P s1 s2
  )))).

Definition wt_exp_is_defined := (forAll arbitrary (fun (c : rctx) =>
            forAll (gen_reg_wt c [3; 3; 1; 1]) (fun (state: reg) =>
            forAll (gen_exp_wt 4 c [3; 3; 1; 1]) (fun (exp : exp) =>
            implication (is_defined (eval state exp)) true)))).
(*! QuickChick wt_exp_is_defined. *)

Definition basic_block_test := (forAll (basic_block_gen_example) (fun (blk: list inst) => (basic_block_checker blk))).
(*! QuickChick basic_block_test. *)

Definition wt_wf := (forAll (gen_prog_wt max_block_size max_program_length) (fun (p : prog) => (wf p))).
(*! QuickChick wt_wf. *)
Definition wt_uslh_wf := (forAll (gen_prog_wt max_block_size max_program_length) (fun (p : prog) => (wf (uslh_prog p)))).
(*! QuickChick wt_uslh_wf. *)


Definition wt_expr_is_defined := (
    forAll arbitrary (fun (c : rctx) =>
    forAll arbitrary (fun (pl : nat) =>
    forAll (choose (2, 5)) (fun (exp_sz : nat) =>
    pst <- gen_partition pl;;
    forAll (gen_reg_wt c pst) (fun (r : reg) =>
    forAll (gen_exp_wt exp_sz c pst) (fun (e : exp) =>
    is_defined (eval r e)
  )))))).
(*! QuickChick wt_expr_is_defined. *)

Definition ty_prog_wf :=
  (forAll (gen_prog_ty_ctx_wt max_block_size max_program_length) (fun '(c, tm, p) =>
    ((ty_prog c tm p) && (wf p)))).







Definition load_store_trans_basic_blk := TS.load_store_trans_basic_blk.

(*! QuickChick load_store_trans_basic_blk. *)



Definition load_store_trans_stuck_free := TS.load_store_trans_stuck_free.

(*! QuickChick load_store_trans_stuck_free. *)



Definition no_obs_prog_no_obs := TS.no_obs_prog_no_obs.

(*! QuickChick no_obs_prog_no_obs. *)



Example implicit_flow_test p rs icfg
  (P: p = [([ IBranch (AId "x") 1; IJump 1 ], true); ([ IAsgn "y"%string (ANum 1); IRet], false)])
  (RS: rs = (N 0, [("x"%string, N 10); ("y"%string, N 0)]))
  (ICFG: icfg = (ipc, rs, [], [])):
  match taint_tracking 10 p icfg with
  | Some (obs, leaked_vars, _) =>
      existsb (String.eqb "x") leaked_vars
  | None => false
  end = true.
Proof.
  remember (taint_tracking 10 p icfg).
  subst p rs icfg. simpl in Heqo.
  subst. simpl. reflexivity.
Qed.



Definition unused_var_no_leak_transform_load_store :=
  unused_var_no_leak (fun c tm p => transform_load_store_prog c tm p).

(*! QuickChick unused_var_no_leak_transform_load_store. *)



Definition gen_pub_equiv_same_ty := TS.gen_pub_equiv_same_ty.



Definition gen_pub_equiv_is_pub_equiv := TS.gen_pub_equiv_is_pub_equiv.

(*! QuickChick gen_pub_equiv_is_pub_equiv. *)

Definition gen_reg_wt_is_wt := TS.gen_reg_wt_is_wt.

(*! QuickChick gen_reg_wt_is_wt. *)



Definition gen_pub_mem_equiv_is_pub_equiv := TS.gen_pub_mem_equiv_is_pub_equiv.

(*! QuickChick gen_pub_mem_equiv_is_pub_equiv. *)



Definition gen_mem_wt_is_wt := TS.gen_mem_wt_is_wt.

(*! QuickChick gen_mem_wt_is_wt. *)





Definition test_ni_transform_load_store :=
  test_ni (fun c tm p => transform_load_store_prog c tm p).
(*! QuickChick test_ni_transform_load_store. *)




Definition test_safety_preservation_uslh := test_safety_preservation uslh_prog gen_dbr gen_dcall gen_dret.

(*! QuickChick test_safety_preservation_uslh. *)






Definition test_relative_security_uslh := test_relative_security uslh_prog gen_dbr gen_dcall gen_dret.

(*! QuickChick test_relative_security_uslh. *)



