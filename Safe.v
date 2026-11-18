Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From SECF Require Import Utils.
From SECF Require Import SimDiagrams.
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

Definition seq_nostep (p: prog) (st: state cfg) : Prop :=
  ~ (exists os stt, p |- <(( st ))> -->^ os <(( stt ))>).

Definition ideal_nostep (p: prog) (st: state ideal_cfg) : Prop :=
  ~ (exists ds os stt, p |- <(( st ))> -->i_ ds ^^ os  <(( stt ))>).

Definition spec_nostep (p: prog) (st: state spec_cfg) : Prop :=
  ~ (exists ds os stt, p |- <(( st ))> -->_ ds ^^ os  <(( stt ))>).

Definition seq_ideal_match (st1: state cfg) (st2: state ideal_cfg) : Prop :=
  match st1, st2 with
  | S_Term, S_Term => True
  | _, S_Fault => True
  | S_Undef, _ => True
  | S_Running c, S_Running (c', _, b) => c = c' /\ b = false
  | _, _ => False
  end.

Lemma val_match_N_l p n v
  (VM: val_match p (N n) v) :
  v = N n.
Proof. destruct v; ss; subst; auto. Qed.

Lemma val_match_FP_l p l v
  (VM: val_match p (FP l) v) :
  exists l', v = FP l'.
Proof. destruct l; destruct v; ss; eauto. Qed.

Lemma Msync_nth_src p m m' n v
  (MSC: Msync p m m')
  (NTH: nth_error m.(memory) n = Some v) :
  exists v', nth_error m'.(memory) n = Some v' /\ val_match p v v'.
Proof. destruct MSC as [MSC _]. specialize (MSC n). rewrite NTH in MSC. des_ifs. eauto. Qed.

Lemma seq_ideal_safety_preservation
  p pc r m sb n
  (SP: r ! sp = N n)
  (WFP: wf_prog p)
  (NCT: no_ct_prog p)
  (FST: first_blk_call p)
  (UNUSED: unused_prog sp p)
  (SEQ: sequential_safe (L := SeqLang) p (S_Running (pc, r, m))) :
  sequential_safe (L := IdealLang) p (S_Running (pc, r, m, sb, false)).
Proof.
  eapply seq_safe_ideal_safe; eauto.
Qed.

Lemma ultimate_slh_bcc_multi p sc ds os sc'
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (UNUSED3: unused_prog sp p)
  (RUN: uslh_prog p |- <(( sc ))> -->*_ ds ^^ os <(( sc' ))>) :
  forall h ic,
    uslh_sim p h ic sc ->
    sequential_safe (L := IdealLang) p ic ->
    exists h' ds' os' ic',
      p |- <(( ic ))> -->i*_ ds' ^^ os' <(( ic' ))> /\ uslh_sim p h' ic' sc'.
Proof.
  induction RUN as [sc | sc sci sc' ds1 os1 ds2 os2 STEP RUN IH]; intros h ic SIM SAFE.
  { exists h, [], [], ic. split; [apply (sem_refl (L := IdealLang))|exact SIM]. }
  destruct (uslh_safe_step_preserves_sim p 0 NCT WFP UNUSED1 UNUSED2 UNUSED3 ds1 h os1 ic sc sci SIM SAFE STEP)
    as (ici & osi & RUNi & _ & SIMi).
  destruct (IH _ ici SIMi (sequential_safe_sem SAFE RUNi)) as (h' & ds' & os' & ic' & RUN' & SIM').
  exists h'. do 2 eexists. exists ic'.
  split; [eapply sem_cat; [exact RUNi|exact RUN']|exact SIM'].
Qed.

Lemma seq_spec_safety_preservation
  p pc r m sb n h sc
  (SP: r ! sp = N n)
  (FST: first_blk_call p)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (UNUSED3: unused_prog sp p)
  (SEQ: sequential_safe (L := SeqLang) p (S_Running (pc, r, m)))
  (MATCH: uslh_sim p h (S_Running (pc, r, m, sb, false)) sc) :
  sequential_safe (L := SpecLang) (uslh_prog p) sc.
Proof.
  intros ds os sct RUN.
  exploit ultimate_slh_bcc_multi; eauto.
  { eapply seq_ideal_safety_preservation; eauto. }
  intros (h' & ds' & os' & ic & IRUN & _ & MATCH').
  assert (INV: ideal_safe_inv p ic).
  { eapply ideal_safe_inv_sem; [exact WFP|exact UNUSED3| |exact IRUN]. ss. eauto. }
  clear - INV MATCH' FST NCT WFP UNUSED1 UNUSED2 UNUSED3. simpl.
  inv MATCH'.
  (* Target matches source: the target executes the hardened source instruction. *)
  - inv MATCH. destruct INV as [ [spv SP] INV].
    destruct REG as [REGX MSF].
    exploit src_lookup; eauto. intros [i INST].
    exploit src_inv; eauto. intros (i' & TINST & MI).
    assert (TSP: r' ! sp = N spv).
    { exploit Rsync1_sp; [exact REGX|]. rewrite SP. apply val_match_N_l. }
    exploit unused_prog_lookup; [exact UNUSED1|exact INST|]. intros U1.
    exploit unused_prog_lookup; [exact UNUSED2|exact INST|]. intros U2.
    exploit wf_prog_lookup; [exact WFP|exact INST|]. intros WFI.
    destruct ms; simpl in MSF.
    (* Misspeculation: masked indices evaluate to 0. *)
    + inv MI.
      * match goal with H: match_simple_inst_uslh _ _ |- _ => inv H end.
        -- do 3 eexists. eapply SpecSMI_Skip; eauto.
        -- do 3 eexists. eapply SpecSMI_Jump; eauto.
        -- do 3 eexists. eapply SpecSMI_Load_Misspec; [exact TINST| |reflexivity].
           simpl. rewrite MSF. reflexivity.
        -- do 3 eexists. eapply SpecSMI_Store_Misspec; [exact TINST|].
           simpl. rewrite MSF. reflexivity.
        -- do 3 eexists. eapply SpecSMI_Asgn; eauto.
        -- do 3 eexists. eapply SpecSMI_Div; [exact TINST| |]; simpl; rewrite MSF; reflexivity.
        -- do 3 eexists. eapply SpecSMI_Term; eauto.
      * do 3 eexists. eapply SpecSMI_Branch with (b' := false); [exact TINST| |reflexivity|reflexivity|reflexivity].
        simpl. rewrite MSF. reflexivity.
      * do 3 eexists. eapply SpecSMI_Asgn; eauto.
      * do 3 eexists. eapply SpecSMI_Load_Misspec; [exact TINST| |reflexivity].
        simpl. rewrite TSP. reflexivity.
    (* No misspeculation: the source takes a sequential step, which the target mirrors. *)
    + destruct (INV [] [] _ (sem_refl (L := SeqLang) p _)) as (os0 & st0 & SSTEP).
      assert (EVAL: forall e, e_unused msf e -> e_unused callee e -> wf_expr p e ->
                     to_nat (eval r' <{{ (msf = 1) ? 0 : e }}>) = to_nat (eval r e)).
      { intros e UE1 UE2 WFE. simpl. rewrite MSF. simpl.
        symmetry. eapply eval_regs_eq_nat; eauto. apply wf_expr_wf_exp. auto. }
      inv MI.
      * match goal with H: match_simple_inst_uslh _ _ |- _ => inv H end.
        -- do 3 eexists. eapply SpecSMI_Skip; eauto.
        -- do 3 eexists. eapply SpecSMI_Jump; eauto.
        -- inv SSTEP; clarify. simpl in U1, U2, WFI. des.
           exploit Msync_nth_src; eauto. intros (tv & NTH' & _).
           do 3 eexists. eapply SpecSMI_Load; [exact TINST| |exact NTH'].
           rewrite EVAL; eauto.
        -- inv SSTEP; clarify. simpl in U1, U2, WFI. des.
           do 3 eexists. eapply SpecSMI_Store; [exact TINST|].
           rewrite EVAL; eauto.
        -- do 3 eexists. eapply SpecSMI_Asgn; eauto.
        -- inv SSTEP; clarify. simpl in U1, U2, WFI. des.
           do 3 eexists. eapply SpecSMI_Div; [exact TINST| |]; rewrite EVAL; eauto.
        -- do 3 eexists. eapply SpecSMI_Term; eauto.
      * inv SSTEP; clarify. simpl in U1, U2, WFI. des.
        do 3 eexists. eapply SpecSMI_Branch with (b' := false); [exact TINST| |reflexivity|reflexivity|reflexivity].
        rewrite EVAL; eauto.
      * do 3 eexists. eapply SpecSMI_Asgn; eauto.
      * inv SSTEP; clarify.
        exploit Msync_nth_src; eauto. intros (tv & NTH' & _).
        do 3 eexists. eapply SpecSMI_Load; [exact TINST| |exact NTH'].
        simpl. rewrite TSP. simpl. congruence.
  (* Procedure entry: the target executes ctarget. *)
  - do 3 eexists. eapply SpecSMI_CTarget; eauto.
  (* Procedure entry: the target updates msf. *)
  - do 3 eexists. eapply SpecSMI_Asgn; eauto.
  (* Call: the target executes the masked call. *)
  - destruct INV as [ [spv SP] INV].
    destruct REG as [REGX MSF].
    assert (TSP: r' ! sp = N spv).
    { exploit (REGX sp); [split; discriminate|auto|]. rewrite SP. apply val_match_N_l. }
    destruct ms; simpl in MSF.
    + do 3 eexists. eapply SpecSMI_Call_Misspec; [exact TCALL| |exact TSP].
      simpl. rewrite MSF. reflexivity.
    + destruct (INV [] [] _ (sem_refl (L := SeqLang) p _)) as (os0 & st0 & SSTEP).
      exploit unused_prog_lookup; [exact UNUSED1|exact CALL|]. intros U1.
      exploit unused_prog_lookup; [exact UNUSED2|exact CALL|]. intros U2.
      exploit wf_prog_lookup; [exact WFP|exact CALL|]. intros WFI.
      exploit eval_regs_eq; [exact U1|exact U2|apply wf_expr_wf_exp; exact WFI|exact REGX|]. intros VM.
      inv SSTEP; clarify. rewrite SP in *. clarify.
      match goal with H: to_fp (eval r fp) = Some _ |- _ => rename H into EFP end.
      destruct (eval r fp) eqn:EV; try discriminate EFP. simpl in EFP. clarify.
      exploit val_match_FP_l; [exact VM|]. intros [l' EV'].
      do 3 eexists. eapply SpecSMI_Call with (pc' := (0, 0)); [exact TCALL| |exact TSP| |reflexivity].
      * simpl. rewrite MSF. simpl. rewrite EV'. reflexivity.
      * destruct MSC as [_ TOP]. rewrite <- TOP. eauto.
  (* Faulty call: the target faults on a missing ctarget. *)
  - do 3 eexists. eapply SpecSMI_Fault; eauto.
  (* Branch hardening steps. *)
  - do 3 eexists. eapply SpecSMI_Asgn; eauto.
  - do 3 eexists. eapply SpecSMI_Jump; eauto.
  - do 3 eexists. eapply SpecSMI_Asgn; eauto.
  (* Return masking: the target stores the masked return address. *)
  - exploit src_inv; eauto. intros (i' & TINST & MI). inv MI; [inv SIMPL|].
    rewrite SYNC in PC. clarify.
    destruct REG as [REGX MSF].
    assert (TSP: r' ! sp = N spv).
    { exploit (REGX sp); [split; discriminate|auto|]. rewrite SP. apply val_match_N_l. }
    destruct ms.
    + do 3 eexists. eapply SpecSMI_Store_Misspec; [exact NXT1|]. simpl. rewrite TSP. reflexivity.
    + do 3 eexists. eapply SpecSMI_Store; [exact NXT1|]. simpl. rewrite TSP. reflexivity.
  (* Return masking: the target reloads the return address. *)
  - exploit src_inv; eauto. intros (i' & TINST & MI). inv MI; [inv SIMPL|].
    rewrite SYNC in PC. clarify.
    destruct REG as [REGX MSF].
    assert (TSP: r' ! sp = N spv).
    { exploit (REGX sp); [split; discriminate|auto|]. rewrite SP. apply val_match_N_l. }
    destruct ms.
    + do 3 eexists. eapply SpecSMI_Load_Misspec; [exact NXT2| |reflexivity]. simpl. rewrite TSP. reflexivity.
    + destruct INV as [_ INV].
      destruct (INV [] [] _ (sem_refl (L := SeqLang) p _)) as (os0 & st0 & SSTEP).
      inv SSTEP; clarify. rewrite SP in *. clarify.
      exploit Msync_nth_src; eauto. intros (tv & NTH' & _).
      do 3 eexists. eapply SpecSMI_Load; [exact NXT2| |exact NTH']. simpl. rewrite TSP. reflexivity.
  (* Return: the target returns to the (possibly masked) return address. *)
  - exploit src_inv; eauto. intros (i' & TINST & MI). inv MI; [inv SIMPL|].
    rewrite SYNC in PC. clarify.
    destruct REG as [REGX MSF].
    assert (TSP: r' ! sp = N spv).
    { exploit (REGX sp); [split; discriminate|auto|]. rewrite SP. apply val_match_N_l. }
    destruct ms.
    + destruct CALLEE as [SLOT _].
      do 3 eexists. eapply SpecSMI_Ret_Misspec_Step; [exact NXT3|exact TSP|exact SLOT].
    + destruct INV as [_ INV].
      destruct (INV [] [] _ (sem_refl (L := SeqLang) p _)) as (os0 & st0 & SSTEP).
      inv SSTEP; clarify. rewrite SP in *. clarify.
      exploit Msync_nth_src; eauto. intros (tv & NTH' & VM).
      rewrite CALLEE in NTH'. clarify.
      exploit val_match_FP_l; eauto. intros [l' CALLEE'].
      rewrite CALLEE' in CALLEE.
      do 3 eexists. eapply SpecSMI_Ret_Step; [exact NXT3|exact TSP| |exact CALLEE].
      destruct MSC as [_ TOP]. rewrite <- TOP. eauto.
  (* After return: the target updates msf. *)
  - do 3 eexists. eapply SpecSMI_Asgn; eauto.
  - auto.
  - auto.
Unshelve. repeat econs.
Qed.

Lemma seq_spec_safety_preservation_init_aux
  p r r' m m' isp
  (FST: first_blk_call p)
  (SYNC: uslh_sync isp p (r, m) (r', m')) :
  exists h, uslh_sim p h (initial_machine (L := IdealLang) p (r, m))
                         (initial_machine (L := SpecLang) (uslh_prog p) (r', m')).
Proof.
  destruct SYNC as (REG & MSC & _ & _). simpl in REG, MSC.
  red in FST. destruct (nth_error p 0) as [ [blk [|] ] | ] eqn:BLK; try contradiction.
  eexists. split; [reflexivity|].
  eapply match_cfgs_ext_ct1; [exact BLK|eapply ctarget_exists; eauto| |exact MSC|].
  - eapply Rsync1_upd_tgt; [eapply Rsync1_upd_tgt; [exact REG|left; reflexivity]|right; reflexivity].
  - reflexivity.
Qed.

Lemma seq_spec_safety_preservation_init
  p r r' m m' isp
  (FST: first_blk_call p)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (UNUSED3: unused_prog sp p)
  (SEQ: sequential_safe (L := SeqLang) p (initial_machine (L := SeqLang) p (r, m)))
  (SYNC: uslh_sync isp p (r, m) (r', m')) :
  sequential_safe (L := SpecLang) (uslh_prog p) (initial_machine (L := SpecLang) (uslh_prog p) (r', m')).
Proof.
  pose proof SYNC as (_ & _ & SP & _). simpl in SP.
  destruct (seq_spec_safety_preservation_init_aux p r r' m m' isp FST SYNC) as [h MATCH].
  exact (seq_spec_safety_preservation p (0, 0) r m (mirror_mem m) isp h _
           SP FST NCT WFP UNUSED1 UNUSED2 UNUSED3 SEQ MATCH).
Qed.
