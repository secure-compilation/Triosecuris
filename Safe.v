Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From SECF Require Import Utils.
From SECF Require Import MiniCET.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
Require Import ExtLib.Data.Monads.OptionMonad.
From SECF Require Import Maps.
From SECF Require Import MapsFunctor.
From SECF Require Import sflib.
From SECF Require Import MiniCET_Index.

Set Default Goal Selector "!".

Import FunctionalExtensionality.

Import MCC.

Notation t_update_eq := TotalMap.t_update_eq.
Notation t_update_neq := TotalMap.t_update_neq.


Definition safe_imm_seq (p: prog) (st: state cfg) : Prop :=
  match st with
  | S_Running c => exists os stt, p |- <(( S_Running c ))> -->^ os <(( stt ))>
  | S_Fault | S_Term => True
  | S_Undef => False
  end.

Definition safe_imm_ideal (p: prog) (st: state ideal_cfg) : Prop :=
  match st with
  | S_Running sc => exists ds os stt, p |- <(( S_Running sc ))> -->i_ ds ^^ os  <(( stt ))>
  | S_Fault | S_Term => True
  | S_Undef => False
  end.

Definition safe_imm_spec (p: prog) (st: state spec_cfg) : Prop :=
  match st with
  | S_Running sc => exists ds os stt, p |- <(( S_Running sc ))> -->_ ds ^^ os  <(( stt ))>
  | S_Fault | S_Term => True
  | S_Undef => False
  end.

Definition seq_nostep (p: prog) (st: state cfg) : Prop :=
  ~ (exists os stt, p |- <(( st ))> -->^ os <(( stt ))>).

Definition ideal_nostep (p: prog) (st: state ideal_cfg) : Prop :=
  ~ (exists ds os stt, p |- <(( st ))> -->i_ ds ^^ os  <(( stt ))>).

Definition spec_nostep (p: prog) (st: state spec_cfg) : Prop :=
  ~ (exists ds os stt, p |- <(( st ))> -->_ ds ^^ os  <(( stt ))>).


Definition seq_exec_safe (p: prog) (c: cfg) : Prop :=
  forall os ct,
    p |- <(( S_Running c ))> -->*^ os <(( S_Running ct ))> ->
    exists os' ctt, p |- <(( S_Running ct ))> -->^ os' <(( ctt ))>.

Definition ideal_exec_safe (p: prog) (ic: ideal_cfg) : Prop :=
  forall ds os ict,
    p |- <(( S_Running ic ))> -->i*_ ds ^^ os  <(( S_Running ict ))> ->
    exists ds' os' stt, p |- <(( S_Running ict ))> -->i_ ds' ^^ os'  <(( stt ))>.

Definition spec_exec_safe (p: prog) (sc: spec_cfg) : Prop :=
  forall ds os n sct (WFDS: wf_ds' p ds),
    p |- <(( S_Running sc ))> -->*_ ds ^^ os ^^ n <(( S_Running sct ))> ->
    exists ds' os' stt, p |- <(( S_Running sct ))> -->_ ds' ^^ os'  <(( stt ))>.

Definition seq_ideal_match (st1: state cfg) (st2: state ideal_cfg) : Prop :=
  match st1, st2 with
  | S_Term, S_Term => True
  | _, S_Fault => True
  | S_Undef, _ => True
  | S_Running c, S_Running (c', b) => c = c' /\ b = false
  | _, _ => False
  end.

Definition nonempty_mem (m: mem) : Prop :=
  0 < Datatypes.length m.

Lemma seq_ideal_nonspec
  p pc r m stk os stt
  (WF: wf_stk p stk)
  (SEQ: p |- <(( S_Running (pc, r, m, stk) ))> -->^ os <(( stt ))>) :
  exists ds stt',
    p |- <(( S_Running (pc, r, m, stk, false) ))> -->i_ ds ^^ os <(( stt' ))>.
  (* /\ seq_ideal_match stt stt'. *)
Proof.
  inv SEQ; try (sfby (esplits; try econs; eauto)).
  (* - exists [DBranch (not_zero n)]. esplits. *)
  (*   { econs; eauto. } *)
  (*   ss. split; auto. rewrite eqb_reflx. ss. *)
  - exists [DCall l].
    destruct (nth_error p (fst l)) eqn:PL; cycle 1.
    { esplits. eapply ISMI_Call_F; eauto. ii. ss; clarify. }
    destruct p0. destruct b; cycle 1.
    { esplits. eapply ISMI_Call_F; eauto. ii. ss; clarify. ss. auto. }
    destruct l. ss.
    destruct n0.
    + esplits. econs; eauto.
    + esplits. eapply ISMI_Call_F; eauto. ii. ss; clarify. right. auto.
  - exists [DRet pc'].
    esplits. econs; eauto. inv WF. auto.
Unshelve. econs.
Qed.

Lemma wf_stk_preserve_ideal
  p pc r m stk ms pc' r' m' stk' ms' ds os
  (WFP: wf_prog p)
  (WFSTK: wf_stk p stk)
  (STEP: p |- <(( S_Running (pc, r, m, stk, ms) ))> -->i_ ds ^^ os <((S_Running (pc', r', m', stk', ms') ))>):
  wf_stk p stk'.
Proof.
  inv STEP; eauto.
  { econs; eauto. red. ii. des_ifs_safe.
    destruct pc. simpl in Heq. clarify.
    rewrite <- add_sub_assoc; [|lia].
    rewrite sub_diag, add_0_r. esplits; eauto; try lia.
    ii. exploit block_always_terminator_prog; eauto.
    i. des. ss. clarify. }
  inv WFSTK. auto.
Qed.

Lemma nonempty_mem_preserve_ideal
  p pc r m stk ms pc' r' m' stk' ms' ds os
  (STEP: p |- <(( S_Running (pc, r, m, stk, ms) ))> -->i_ ds ^^ os <((S_Running (pc', r', m', stk', ms') ))>):
  Datatypes.length m = Datatypes.length m'.
Proof.
  inv STEP; eauto. rewrite upd_length. eauto.
Qed.

Require Import Stdlib.Program.Equality.

Lemma wf_stk_preserve_multi_ideal
  p pc r m stk ms pc' r' m' stk' ms' ds os
  (WFP: wf_prog p)
  (WFSTK: wf_stk p stk)
  (STEP: p |- <(( S_Running (pc, r, m, stk, ms) ))> -->i*_ ds ^^ os <((S_Running (pc', r', m', stk', ms') ))>):
  wf_stk p stk'.
Proof.
  dependent induction STEP; auto.
  destruct ic2. 2-4: inv STEP; inv H0.
  destruct a as [ [ [ [pc'' r''] m''] stk''] ms''].
  eapply wf_stk_preserve_ideal in H; eauto.
Qed.

Lemma ideal_res_pc_exists
  p pc r m stk ms pc' r' m' stk' ms' ds os
  (WFSTK: wf_stk p stk)
  (WFP: wf_prog p)
  (STEP: p |- <(( S_Running (pc, r, m, stk, ms) ))> -->i_ ds ^^ os <((S_Running (pc', r', m', stk', ms') ))>):
  exists i, p[[pc']] = Some i.
Proof.
  inv STEP.
  - exploit block_always_terminator_prog; try eapply H11; eauto.
  - exploit block_always_terminator_prog; try eapply H11; eauto.
  - exploit block_always_terminator_prog; try eapply H11; eauto.
  - exploit block_always_terminator_prog; try eapply H11; eauto.
    intros (i'' & PC').
    destruct pc as [b o]. ss. des_ifs_safe. destruct p0 as [blk ct].
    destruct b'.
    { inv WFP. rewrite Forall_forall in H0.
      eapply nth_error_In in Heq, H11. eapply H0 in Heq.
      red in Heq. des. rewrite Forall_forall in Heq1. eapply Heq1 in H11.
      simpl in H11. des. red in H1. des_ifs_safe. simpl.
      rewrite Heq2. destruct l0; simpl; eauto.
      eapply nth_error_In in Heq2. eapply H0 in Heq2. red in Heq2. des.
      red in Heq2. ss; lia. }
    ss. des_ifs; ss; eauto.
  - destruct pc as [b o]. ss. des_ifs_safe. destruct p0 as [blk ct].
    inv WFP. rewrite Forall_forall in H0.
    eapply nth_error_In in Heq, H11. eapply H0 in Heq. red in Heq. des.
    rewrite Forall_forall in Heq1. eapply Heq1 in H11.
    simpl in H11. des. red in H11. des_ifs_safe. simpl.
    destruct l0; simpl; eauto.
    eapply nth_error_In in Heq2. eapply H0 in Heq2. red in Heq2. des.
    red in Heq2. ss; lia.
  - exploit block_always_terminator_prog; try eapply H11; eauto.
  - exploit block_always_terminator_prog; try eapply H11; eauto.
  - destruct pc', blk. ss. subst. rewrite H14. ss. destruct l0; eauto.
    inv WFP. rewrite Forall_forall in H0.
    eapply nth_error_In in H14. eapply H0 in H14. red in H14. des.
    red in H14. ss.
  - destruct pc' as [b' o'].
    red in H12. des.
    exploit block_always_terminator_prog; try eapply H12; eauto.
    simpl. replace (add (o' - 1) 1) with o' by lia. auto.
  - exploit block_always_terminator_prog; try eapply H11; eauto.
Qed.

Lemma multi_ideal_res_pc_exists_aux :
  forall p ic1 ic2 ds os,
    p |- <(( ic1 ))>  -->i*_ ds ^^ os <(( ic2 ))> ->
    forall pc r m stk ms pc' r' m' stk' ms',
      ic1 = S_Running (pc, r, m, stk, ms) ->
      ic2 = S_Running (pc', r', m', stk', ms') ->
      wf_stk p stk -> wf_prog p -> p[[pc]] <> None -> exists i, p[[pc']] = Some i.
Proof.
  induction 1; subst; i.
  - subst. clarify. destruct (p[[pc']]); eauto. clarify.
  - destruct ic2. 2-4: inv H0; inv H7; inv H6.
    destruct a as [ [ [ [pc'' r''] m''] stk''] ms'']. subst.
    exploit IHmulti_ideal_inst.
    { eauto. }
    { eauto. }
    { eapply wf_stk_preserve_ideal in H; eauto. }
    { eauto. }
    { eapply ideal_res_pc_exists in H; eauto. des. ii. clarify. }
    eauto.
Qed.

Lemma multi_ideal_res_pc_exists
  p pc r m stk ms pc' r' m' stk' ms' ds os
  (WFSTK: wf_stk p stk)
  (WFP: wf_prog p)
  (PC: p[[pc]] <> None)
  (STEP: p |- <(( S_Running (pc, r, m, stk, ms) ))> -->i*_ ds ^^ os <((S_Running (pc', r', m', stk', ms') ))>):
  exists i, p[[pc']] = Some i.
Proof.
  eapply multi_ideal_res_pc_exists_aux; eauto.
Qed.

Lemma nonempty_mem_preserve_multi_ideal
  p pc r m stk ms pc' r' m' stk' ms' ds os
  (STEP: p |- <(( S_Running (pc, r, m, stk, ms) ))> -->i*_ ds ^^ os <((S_Running (pc', r', m', stk', ms') ))>):
  Datatypes.length m = Datatypes.length m'.
Proof.
  dependent induction STEP; eauto.
  destruct ic2. 2-4: inv STEP; inv H0.
  destruct a as [ [ [ [pc'' r''] m''] stk''] ms'']. subst.
  eapply nonempty_mem_preserve_ideal in H.
  rewrite H. eapply IHSTEP; eauto.
Qed.

Lemma seq_ideal_safety_preservation
  p c pc r m stk
  (CFG: c = (pc, r, m, stk))
  (MEM: nonempty_mem m)
  (WFSTK: wf_stk p stk)
  (WFP: wf_prog p)
  (NCT: no_ct_prog p)
  (SEQ: seq_exec_safe p c) :
  ideal_exec_safe p (c, false).
Proof.
  red. ii. destruct ict as [c' ms]. subst.

  destruct c' as [cl' stk']. destruct cl' as [cl' m']. destruct cl' as [pc' r'].
  destruct ms; cycle 1.
  { red in SEQ.
    exploit multi_ideal_nonspec_seq; eauto. i.
    eapply SEQ in x0. des. eapply seq_ideal_nonspec in x0.
    - des. eauto.
    - eapply wf_stk_preserve_multi_ideal; eauto. }
  destruct (p[[pc']]) eqn:PC'; cycle 1.
  { eapply multi_ideal_res_pc_exists in H; eauto; des; clarify.
    ii. red in SEQ. exploit SEQ; [econs|]. i. des. inv x0; clarify. }
  destruct i.
  - esplits. econs; eauto.
  - esplits. econs 2. eauto.
  - esplits. econs 3; eauto.
  - esplits. econs 4; eauto.
  - esplits. econs 5; eauto.
  - assert (MEM': nonempty_mem m').
    { eapply nonempty_mem_preserve_multi_ideal in H.
      unfold nonempty_mem in *. lia. }
    assert (exists v, nth_error m' 0 = Some v).
    { red in MEM'. erewrite <- nth_error_Some in MEM'.
      destruct (nth_error m' 0); eauto. clarify. }
    des. esplits. econs 6; ss; eauto.
  - esplits. econs 7; ss; eauto.
  - exists [DCall (0, 0)], [OCall (0, 0)].
    red in WFP. des. red in WFP.
    assert (exists blk b, nth_error p 0 = Some (blk, b)).
    { erewrite <- nth_error_Some in WFP. destruct (nth_error p 0); clarify.
      destruct p0. eauto. }
    des. destruct b.
    + esplits. econs; eauto.
    + esplits. eapply ISMI_Call_F; eauto. ii. ss. clarify.
      left. ss.
  - exfalso. eapply no_ct_prog_src; eauto.
  - esplits. eapply ISMI_Peek; eauto.
  - destruct stk'.
    + esplits. eapply ISMI_Term. eauto.
    + exists [DRet c].
      esplits. eapply ISMI_Ret; eauto.
      hexploit wf_stk_preserve_multi_ideal; eauto. i.
      inv H0. eauto.
Unshelve. econs.
Qed.

Lemma seq_spec_safety_preservation
  p b c c' pc r m stk
  (CFG: c = (pc, r, m, stk))
  (MEM: nonempty_mem m)
  (WFSTK: wf_stk p stk)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (SEQ: seq_exec_safe p c)
  (MATCH: match_cfgs_ext p (S_Running (c, false)) (S_Running (c', b, false))) :
  spec_exec_safe (uslh_prog p) (c', b, false).
Proof.
  ii. eapply seq_ideal_safety_preservation in SEQ; eauto.

  red in SEQ.
  exploit ultimate_slh_bcc'; eauto.
  i. des. destruct ic2.
  - exploit SEQ; eauto. i. des.
    inv x1.
    + inv MATCH0. inv x4.
      * exploit src_inv; eauto. i. des. inv x4. inv MATCH0.
        esplits. econs; eauto.
      * exploit src_inv; eauto. i. des. inv x1. inv MATCH0.
        esplits. econs 2; eauto.
      * exploit src_inv; eauto. i. des. inv x1. inv MATCH0.
        eapply unused_prog_lookup in UNUSED1; eauto.
        eapply unused_prog_lookup in UNUSED2; eauto. ss. des.
        esplits. econs 3; eauto.
        { erewrite <- H9. inv REG. ss. rewrite H1.
          destruct ms; ss.
          exploit eval_regs_eq; try eapply UNUSED4; eauto.
          { apply wf_expr_wf_exp. eapply wf_prog_lookup in WFP; eauto. apply WFP. }
          destruct (eval r0 e1), (eval r' e1); ss.
          congruence.
        }
        { erewrite <- H10. inv REG. ss. rewrite H1.
          destruct ms; ss.
          exploit eval_regs_eq; try eapply UNUSED5; eauto.
          { apply wf_expr_wf_exp. eapply wf_prog_lookup in WFP; eauto. apply WFP. }
          destruct (eval r0 e2), (eval r' e2); ss.
          congruence.
        }
      * exploit src_inv; eauto. i. des. inv x4; [ss|].
        eapply unused_prog_lookup in UNUSED1; eauto.
        eapply unused_prog_lookup in UNUSED2; eauto.

        assert (to_nat (eval r' <{{ (msf = 1) ? 0 : e }}>) = Some n').
        { ss. inv REG. rewrite H1. destruct ms; ss; eauto. rewrite <- H9.
          exploit eval_regs_eq; try eapply UNUSED4; eauto.
          { apply wf_expr_wf_exp. eapply wf_prog_lookup in WFP; eauto. apply WFP. }
          destruct (eval r0 e), (eval r' e); ss.
          congruence.
        }
        esplits. econs 4; eauto.
      * exploit src_inv; eauto. i. des. inv x4. inv MATCH0.
        esplits. econs 5; eauto.
      * exploit src_inv; eauto. i. des. inv x1. inv MATCH0.
        eapply unused_prog_lookup in UNUSED1; eauto.
        eapply unused_prog_lookup in UNUSED2; eauto. ss. des.

        red in MSC. specialize (MSC n0). des_ifs_safe.
        esplits. econs 6; eauto. rewrite <- H10.
        inv REG. simpl. rewrite H1. destruct ms; ss.
        exploit eval_regs_eq; eauto.
        { apply wf_expr_wf_exp. eapply wf_prog_lookup in WFP; eauto. apply WFP. }
        destruct (eval r0 e), (eval r' e); ss.
        congruence.
      * exploit src_inv; eauto. i. des. inv x4. inv MATCH0.
        eapply unused_prog_lookup in UNUSED1; eauto.
        eapply unused_prog_lookup in UNUSED2; eauto. ss. des.

        esplits. econs 7; eauto. erewrite <- H10.
        inv REG. simpl. rewrite H1. destruct ms; ss.
        exploit eval_regs_eq; try apply UNUSED1; eauto.
        { apply wf_expr_wf_exp. eapply wf_prog_lookup in WFP; eauto. apply WFP. }
        destruct (eval r0 e), (eval r' e); ss.
        congruence.
      * exploit src_inv; eauto. i. des. inv x4; [ss|].
        esplits. econs 2; eauto.
      * exploit src_inv; eauto. i. des. inv x4; [ss|].
        esplits. econs 2; eauto.
      * destruct stk'.
        { ss. des_ifs. }
        exploit src_inv; eauto. i. des. inv x4.
        { inv SIMPL. }
        esplits. econs 11; eauto.
      * exploit src_inv; eauto. i. des. inv x4. inv x1. inv MATCH0.
        esplits. econs 11. eauto.
      * destruct stk'; [|ss].
        exploit src_inv; eauto. i. des. inv x4.
        { inv SIMPL. }
        esplits. econs 11; eauto.
    + esplits. econs. eauto.
    + esplits. econs 2; eauto.
    + inv REG.
      eapply unused_prog_lookup in UNUSED1; eauto.
      eapply unused_prog_lookup in UNUSED2; eauto.

      destruct (to_fp (eval r' <{{ (msf = 1) ? & (0,0) : fp }}>)) eqn:FP.
      2:{ ss. rewrite H1 in FP. ss. destruct ms; ss.
        assert (exists l, to_fp (eval r0 fp) = Some l).
        { inv x4; clarify; eauto. }
        des. exploit eval_regs_eq; eauto. 1: apply wf_expr_wf_exp; eapply wf_prog_lookup in WFP; eauto; apply WFP.
        destruct (eval r' fp), (eval r0 fp); ss; destruct pc1; ss.
      }
      esplits. eapply SpecSMI_Call; eauto.
    + esplits. econs 2; eauto.
    + esplits. eapply SpecSMI_Jump; eauto.
    + esplits. econs 2; eauto.
    (* In this case, the callee register stores the return target. *)
    + destruct stk'.
      * esplits. eapply SpecSMI_Term; eauto.
      * destruct c as [l' o'].
        exists [DRet (l', o')].
        esplits. econs 10; eauto.
        unfold wf_ret.
        destruct stk0; ss.
        destruct (ret_sync p c) eqn: ?;  ss.
        destruct (map_opt (ret_sync p) stk0); ss. clarify.
        destruct c. exploit ret_sync_same_label; eauto. intros ->.
        destruct n1; ss.
        destruct (p [[(l', n1)]]) eqn:?; ss; rewrite Heqo0 in Heqo. 2: discriminate.
        destruct i; ss.
        destruct (pc_sync p (l', n1)) eqn:?; ss; rewrite Heqo1 in Heqo. 2: discriminate.
        exploit src_inv. 3: instantiate (2 := (l', n1)); exact Heqo1. all: eauto. i.
        destruct c; clarify. des. inv x5. 1: inv SIMPL.
        destruct tpc. simpl in SYNC. clarify. ss.
        rewrite IN'. assert (n2 + 2 - 1 = Nat.add n2 1) as -> by lia. rewrite IN.
        split; ss. econs. split; [reflexivity|lia].
    + esplits. eapply SpecSMI_Asgn. eauto.
  - clear - x0. exfalso. remember false. clear Heqb.
    dependent induction x0. destruct ic2. 3-4: inv x0; inv H0.
    2:{ inv H. }
    destruct a. eapply IHx0; eauto.
  - inv x1. exists [], [], S_Fault.
    eapply SpecSMI_Fault; eauto.
  - inv x1.
Unshelve. all: repeat econs.
Admitted.

Lemma seq_spec_safety_preservation_init_aux
  p c c' r r' m m'
  (FST: first_blk_call p)
  (CFG1: c = ((0,0), r, m, @nil cptr))
  (CFG2: c' = ((0,0), r', m', @nil cptr))
  (CALLEE: r' ! callee = FP (0, 0))
  (MEM: nonempty_mem m)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (SEQ: seq_exec_safe p c)
  (REG: Rsync p r r' false)
  (MSC: Msync p m m') :
  spec_exec_safe (uslh_prog p) (c', true, false).
Proof.
  red. i.
  assert (CT: (uslh_prog p)[[(0, 0)]] = Some <{{ ctarget }}>).
  { red in FST. des_ifs. eapply ctarget_exists; eauto. }
  exploit head_call_target; eauto. i. des; clarify.
  replace ((0,0) + 1) with (0,1) in x2 by ss.
  destruct n.
  { inv H. esplits. econs. eauto. }
  destruct n.
  { inv H. inv H6. inv H1. esplits. econs 2. eauto. }
  inv H. inv H1; clarify. inv H6. inv H0; clarify.
  replace ((0,1) + 1) with (0,2) in H5 by ss.
  eapply seq_spec_safety_preservation in SEQ; eauto.
  { ii. ss. }
  econs. econs.
  { red in FST. des_ifs_safe.
    unfold pc_sync. rewrite nth_error_map. rewrite Heq. simpl.
    destruct l.
    { red in WFP. des. eapply nth_error_In in Heq. rewrite Forall_forall in WFP0.
      eapply WFP0 in Heq. red in Heq. des. ss. }
    simpl. auto. }
  { red. inv REG. split.
    - i. des. rewrite t_update_neq; eauto.
    - ss. rewrite CALLEE. ss. }
  { ss. }
  { ss. }
Qed.

Lemma seq_spec_safety_preservation_init
  p r r' m m'
  (FST: first_blk_call p)
  (CALLEE: r' ! callee = FP (0,0))
  (MEM: nonempty_mem m)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (SEQ: seq_exec_safe p ((0,0), r, m, @nil cptr))
  (REG: Rsync p r r' false)
  (MSC: Msync p m m') :
  spec_exec_safe (uslh_prog p) (((0,0), r', m', @nil cptr), true, false).
Proof.
  eapply seq_spec_safety_preservation_init_aux; eauto.
Qed.
