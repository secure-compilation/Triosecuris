
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From SECF Require Import Utils.
From SECF Require Import MiniCET MiniCET_Index MoreLinear.
From SECF Require Import Safe.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
Require Import ExtLib.Data.Monads.OptionMonad.
From SECF Require Import Maps MapsFunctor.

Set Default Goal Selector "!".

Module MLCC := MoreLinearCommon(TotalMap).
Import MLCC.

Reserved Notation
  "p '|-' '<((' c '))>' '-->^' os '<((' ct '))>'"
  (at level 40, c constr, ct constr).

Inductive seq_eval_small_step_inst (p:prog) :
  state cfg -> state cfg -> obs -> Prop :=
  | SSMI_Skip : forall pc rs m stk,
      fetch p (Datatypes.length m) pc = Some <{{ skip }}> ->
      p |- <(( S_Running (pc, rs, m, stk) ))> -->^[] <(( S_Running (add pc 1, rs, m, stk) ))>
  | SSMI_Ctarget : forall pc rs m stk,
      fetch p (Datatypes.length m) pc = Some <{{ ctarget }}> ->
      p |- <(( S_Running (pc, rs, m, stk) ))> -->^[] <(( S_Running (add pc 1, rs, m, stk) ))>
  | SSMI_Asgn : forall pc r m sk e x,
      fetch p (Datatypes.length m) pc = Some <{{ x := e }}> ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[] <(( S_Running (add pc 1, (x !-> (eval r e); r), m, sk) ))>
  | SSMI_Div : forall pc r m sk e1 e2 x v1 v2,
      fetch p (Datatypes.length m) pc = Some <{{ x <- div e1, e2 }}> ->
      to_nat (eval r e1) = Some v1 ->
      to_nat (eval r e2) = Some v2 ->
      let res := match v2 with
                | 0 => UV
                | _ => N (div v1 v2)
                end
      in
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[ODiv v1 v2] <(( S_Running (add pc 1, (x !-> res; r), m, sk) ))>
  | SSMI_Branch : forall pc pc' r m sk e n l,
      fetch p (Datatypes.length m) pc = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      pc' = (if (not_zero n) then l else add pc 1) ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[OBranch (not_zero n)] <(( S_Running (pc', r, m, sk) ))>
  | SSMI_Jump : forall l pc r m sk,
      fetch p (Datatypes.length m) pc = Some <{{ jump l }}> ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[] <(( S_Running (l, r, m, sk) ))>
  | SSMI_Load : forall pc r m sk x e n v',
      fetch p (Datatypes.length m) pc = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m n = Some v' ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[OLoad n] <(( S_Running (add pc 1, (x !-> v'; r), m, sk) ))>
  | SSMI_Store : forall pc r m sk e e' n,
      fetch p (Datatypes.length m) pc = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[OStore n] <(( S_Running (add pc 1, r, upd n m (eval r e'), sk) ))>
  | SSMI_Call : forall pc r m sk e l,
      fetch p (Datatypes.length m) pc = Some <{{ call e }}> ->
      to_nat (eval r e) = Some l ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[OCall l] <(( S_Running (l, r, m, ((add pc 1)::sk)) ))>
  | SSMI_Ret : forall pc r m sk pc',
      fetch p (Datatypes.length m) pc = Some <{{ ret }}> ->
      p |- <(( S_Running (pc, r, m, pc'::sk) ))> -->^[] <(( S_Running (pc', r, m, sk) ))>
  | SSMI_Peek : forall pc r m sk x, (* YH: Maybe we can assume source program does not contain peek instruction. *)
      fetch p (Datatypes.length m) pc = Some <{{x <- peek}}> ->
      let val := match sk with
                | [] => UV
                | pc' :: sk' => N pc'
                end
      in
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[] <(( S_Running (add pc 1, (x !-> val; r), m, sk) ))>
  | SSMI_Term : forall pc r m,
      fetch p (Datatypes.length m) pc = Some <{{ ret }}> ->
      p |- <(( S_Running (pc, r, m, []) ))> -->^[] <(( S_Term ))>

  where "p |- <(( c ))> -->^ os <(( ct ))>" :=
      (seq_eval_small_step_inst p c ct os).


Reserved Notation
  "p '|-' '<((' c '))>' '-->*^' os '<((' ct '))>'"
      (at level 40, c constr, ct constr).

Inductive multi_seq_inst (p : prog) (c : @state cfg) : @state cfg -> obs -> Prop :=
  | multi_seq_inst_refl : p |- <(( c ))> -->*^[] <(( c ))>
  | multi_seq_inst_trans (c' c'' : @state cfg) (os1 os2 : obs) :
      p |- <(( c ))> -->^os1 <(( c' ))> ->
      p |- <(( c' ))> -->*^os2 <(( c'' ))> ->
      p |- <(( c ))> -->*^(os1 ++ os2) <(( c'' ))>

  where "p |- <(( c ))> -->*^ os <(( ct ))>" :=
      (multi_seq_inst p c ct os).

Definition wf_ret (p: prog) (len: nat) (pc: nat) : Prop :=
  exists e, fetch p len (pc - 1) = Some <{{ call e }}> /\ pc > 0.

Definition wf_stk (p: prog) (len: nat) (stk: list nat) : Prop :=
  Forall (fun pc => wf_ret p len pc) stk.

Definition call_return_targets (p: prog) : list nat :=
  let ip := add_index p in
  List.flat_map (fun '(o, i) => match i with
                             | ICall _ => [(add o 1)]
                             | _ => []
                             end) ip.

Reserved Notation
  "p '|-' '<((' sc '))>' '-->m_' ds '^^' os '<((' sct '))>'"
  (at level 40, sc constr, sct constr).

Inductive spec_eval_small_step (p:prog):
  @state MLCC.spec_cfg -> @state MLCC.spec_cfg -> dirs -> obs -> Prop :=
  | SpecSMI_Skip  :  forall pc r m sk ms,
      fetch p (Datatypes.length m) pc = Some <{{ skip }}> ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->m_[]^^[] <(( S_Running ((add pc 1, r, m, sk), false, ms) ))>
  | SpecSMI_Asgn : forall pc r m sk ms e x,
      fetch p (Datatypes.length m) pc = Some <{{ x := e }}> ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->m_[]^^[] <(( S_Running ((add pc 1, (x !-> (eval r e); r), m, sk), false, ms) ))>
  | SpecSMI_Div : forall pc r m sk ms e1 e2 x v1 v2,
      fetch p (Datatypes.length m) pc = Some <{{ x <- div e1, e2 }}> ->
      to_nat (eval r e1) = Some v1 ->
      to_nat (eval r e2) = Some v2 ->
      let res := match v2 with
                | 0 => UV
                | _ => N (div v1 v2)
                end
      in
      p |- <(( S_Running (pc, r, m, sk, false, ms) ))> -->m_[]^^[ODiv v1 v2] <(( S_Running (add pc 1, (x !-> res; r), m, sk, false, ms) ))>
  | SpecSMI_Branch : forall pc pc' r m sk ms ms' b (b': bool) e n l,
      fetch p (Datatypes.length m) pc = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      b = (not_zero n) ->
      pc' = (if b' then l else (add pc 1)) ->
      ms' = ms || negb (Bool.eqb b b') ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->m_[DBranch b']^^[OBranch b] <(( S_Running ((pc', r, m, sk), false, ms') ))>
  | SpecSMI_Jump : forall l pc r m sk ms,
      fetch p (Datatypes.length m) pc = Some <{{ jump l }}> ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->m_[]^^[] <(( S_Running ((l, r, m, sk), false, ms) ))>
  | SpecSMI_Load : forall pc r m sk x e n v' ms,
      fetch p (Datatypes.length m) pc = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m n = Some v' ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->m_[]^^[OLoad n] <(( S_Running ((add pc 1, (x !-> v'; r), m, sk), false, ms) ))>
  | SpecSMI_Store : forall pc r m sk e e' n ms,
      fetch p (Datatypes.length m) pc = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->m_[]^^[OStore n] <(( S_Running ((add pc 1, r, upd n m (eval r e'), sk), false, ms) ))>
  | SpecSMI_Call : forall pc pc' r m sk e l ms ms',
      fetch p (Datatypes.length m) pc = Some <{{ call e }}> ->
      to_nat (eval r e) = Some l ->
      ms' = ms || negb ((pc' =? l)) ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->m_[DCall pc']^^[OCall l] <(( S_Running ((pc', r, m, (add pc 1)::sk), true, ms') ))>
  | SpecSMI_CTarget : forall pc r m sk ct ms,
      fetch p (Datatypes.length m) pc = Some <{{ ctarget }}> ->
      p |- <(( S_Running ((pc, r, m, sk), ct, ms) ))> -->m_[]^^[] <(( S_Running ((add pc 1, r, m, sk), false, ms) ))>
  | SpecSMI_Ret : forall pc r m sk pc' pc'' ms ms',
      fetch p (Datatypes.length m) pc = Some <{{ ret }}> ->
      wf_ret p (Datatypes.length m) pc'' ->
      ms' = ms || negb (pc' =? pc'') ->
      p |- <(( S_Running ((pc, r, m, pc'::sk), false, ms) ))> -->m_[DRet pc'']^^[] <(( S_Running ((pc'', r, m, sk), false, ms') ))>
  | SpecSMI_Peek : forall pc r m sk ms x,
      fetch p (Datatypes.length m) pc = Some <{{x <- peek}}> ->
      let val := match sk with
                | [] => UV
                | pc' :: sk' => N pc'
                end
      in
      p |- <(( S_Running (pc, r, m, sk, false, ms) ))> -->m_[]^^[] <(( S_Running (add pc 1, (x !-> val; r), m, sk, false, ms) ))>
  | SpecSMI_Term : forall pc r m ms,
      fetch p (Datatypes.length m) pc = Some <{{ ret }}> ->
      p |- <(( S_Running ((pc, r, m, []), false, ms) ))> -->m_[]^^[] <(( S_Term ))>
  | SpecSMI_Fault : forall pc r m sk ms,
      fetch p (Datatypes.length m) pc <> Some <{{ ctarget }}> ->
      p |- <(( S_Running ((pc, r, m, sk), true, ms) ))> -->m_[]^^[] <(( S_Fault ))>

  where "p |- <(( sc ))> -->m_ ds ^^ os  <(( sct ))>" :=
    (spec_eval_small_step p sc sct ds os).

Reserved Notation
  "p '|-' '<((' sc '))>' '-->m*_' ds '^^' os '^^' n '<((' sct '))>'"
  (at level 40, sc constr, sct constr).

Inductive multi_spec_inst (p:prog) :
  @state spec_cfg -> @state spec_cfg -> dirs -> obs -> nat -> Prop :=
  |multi_spec_inst_refl sc : p |- <(( sc ))> -->m*_[]^^[]^^0 <(( sc ))>
  |multi_spec_inst_trans sc1 sc2 sc3 ds1 ds2 os1 os2 n :
      p |- <(( sc1 ))> -->m_ds1^^os1 <(( sc2 ))> ->
      p |- <(( sc2 ))> -->m*_ds2^^os2^^n <(( sc3 ))> ->
      p |- <(( sc1 ))> -->m*_(ds1++ds2)^^(os1++os2)^^(S n) <(( sc3 ))>

  where "p |- <(( sc ))> -->m*_ ds ^^ os ^^ n <(( sct ))>" :=
    (multi_spec_inst p sc sct ds os n).

From SECF Require Import sflib.

Definition match_reg (p: MiniCET.prog) (len: nat) (r: MCC.reg) (r': reg) : Prop :=
  forall x, val_inject p len (r ! x) (r' ! x).

Lemma eval_binop_inject p len o v1 v1' v2 v2'
  (INJ1: val_inject p len v1 v1')
  (INJ2: val_inject p len v2 v2') :
  val_inject p len (eval_binop o v1 v2) (eval_binop o v1' v2').
Proof.
  red in INJ1, INJ2. des_ifs. destruct o; ss.
  f_equal.
  destruct pc1 as [l1 o1]. destruct pc0 as [l0 o0]. ss.
  destruct (Nat.eq_dec l1 l0); clarify.
  2:{ hexploit pc_inj_inject; [| eapply Heq0| eapply Heq|].
      - ii. clarify.
      - ii. rewrite <- Nat.eqb_neq in *. rewrite n, H. ss. }
  destruct (Nat.eq_dec o1 o0); clarify.
  2:{ hexploit pc_inj_inject; [| eapply Heq0| eapply Heq|].
      - ii. clarify.
      - ii. rewrite <- Nat.eqb_neq in *. rewrite n, H.
        rewrite andb_false_r. auto. }
  do 3 rewrite Nat.eqb_refl. auto.
Qed.

Lemma eval_inject p len r1 r2 e1 e2
  (INJ: match_reg p len r1 r2)
  (TRANS: machine_exp p len e1 = Some e2) :
  val_inject p len (MCC.eval r1 e1) (eval r2 e2).
Proof.
  ginduction e1; ss; ii; clarify.
  - des_ifs. ss.
    hexploit IHe1_1; eauto. intros INJ1. hexploit IHe1_2; eauto. intros INJ2.
    eapply (eval_binop_inject p len o); eauto.
  - des_ifs_safe. hexploit IHe1_1; eauto. i. ss.
    destruct (MCC.eval r1 e1_1); ss; auto. des_ifs_safe. ss. clarify.
    des_ifs.
    + hexploit IHe1_2; eauto.
    + hexploit IHe1_3; eauto.
  - des_ifs. ss. clarify.
Qed.

Lemma asgn_match_reg p len v v' r r' x
  (INJ: val_inject p len v v')
  (MATCH: match_reg p len r r') :
  match_reg p len (x !-> v; r) (x !-> v'; r').
Proof.
  unfold match_reg in *. i.
  destruct (string_dec x x0); subst.
  { do 2 rewrite MiniCET_Index.t_update_eq. auto. }
  do 2 (rewrite MiniCET_Index.t_update_neq; eauto).
Qed.

Definition match_reg_src (p: MiniCET.prog) (len: nat) (r: MCC.reg) (r': reg) (ms: bool) : Prop :=
  (forall x, x <> msf /\ x <> callee -> val_inject p len (r ! x) (r' ! x))
/\ r' ! msf = N (if ms then 1 else 0).

Definition match_mem (p: MiniCET.prog) (len: nat) (m m': mem) : Prop :=
  forall i, match nth_error m i, nth_error m' i with
       | None, _ => True
       | Some v, Some v' => val_inject p len v v'
       | Some v, None => False
       end.

Lemma nth_error_upd_eq : forall {A : Type} (i: nat) (v : A) (l : list A),
  (exists x, nth_error l i = Some x) ->
  nth_error (upd i l v) i = Some v.
Proof.
  intros A i v l [x H].
  generalize dependent l.
  induction i.
  - intros l H. destruct l; auto. rewrite nth_error_nil in H. inversion H.
  - intros l H. simpl in *. destruct l.
    + inversion H.
    + apply IHi. assumption.
Qed.

Lemma nth_error_upd_beq : forall {A : Type} (i n : nat) (x v : A) (l : list A),
  i <> n ->
  nth_error l i = Some x ->
  nth_error (upd n l v) i = Some x.
Proof.
  intros A i n x v.
  generalize dependent n.
  induction i.
  - intros n l BEQ NTH. destruct l; auto.
    + rewrite nth_error_nil in NTH; inversion NTH.
    + simpl in *. destruct n.
      * contradiction.
      * assumption.
  - intros n l BEQ NTH. simpl. destruct l.
    + rewrite nth_error_nil in NTH. inversion NTH.
    + destruct n eqn:Heqb; auto.
      simpl. apply IHi.
      * ss.
        assert (HL : Datatypes.length (upd n (a :: l) v) > 0).
        { rewrite upd_length. simpl. lia. }
        rewrite Heqb in HL. ss. lia.
      * ss.
Qed.

Lemma store_match_mem p len v v' m m' n
  (MEM: match_mem p len m m')
  (INJ: val_inject p len v v') :
  match_mem p len (upd n m v) (upd n m' v').
Proof.
  red. i.
  destruct (nth_error m i) eqn:MSRC; cycle 1.
  { erewrite nth_error_None in MSRC.
    erewrite <- upd_length with (i:=n) (a:=v) in MSRC.
    erewrite <- nth_error_None in MSRC. rewrite MSRC. auto. }
  specialize (MEM i). des_ifs_safe.
  destruct (eq_decidable n i); subst.
  - destruct (nth_error (upd i m' v') i) eqn:Heqb.
    + rewrite nth_error_upd_eq in Heq.
      -- rewrite nth_error_upd_eq in Heqb.
        +++ inv Heq. inv Heqb. assumption.
        +++ exists v2. assumption.
      -- exists v0. assumption.
    + rewrite nth_error_upd_eq in Heqb.
      -- inversion Heqb.
      -- exists v2. assumption.
  - destruct (nth_error (upd n m' v') i) eqn:Heqb.
    + rewrite nth_error_upd_beq with (x := v0) in Heq; auto.
      rewrite nth_error_upd_beq with (x := v2) in Heqb; auto.
      inv Heq. inv Heqb. assumption.
    + rewrite nth_error_upd_beq with (x := v2) in Heqb; auto.
      inversion Heqb.
Qed.

Definition match_pc (p: MiniCET.prog) (len: nat) (pc: cptr) (pc': nat) : Prop :=
  p[[pc]] <> None -> pc_inj p len pc = Some pc'.

Definition match_stk (p: MiniCET.prog) (len: nat) (stk: list cptr) (stk': list nat) : Prop :=
  Forall2 (match_pc p len) stk stk'.

Variant match_states (p: MiniCET.prog) (tp: prog) (len: nat) : state MCC.spec_cfg -> state spec_cfg -> Prop :=
| match_states_intro pc r m stk ms pc' r' m' stk'
  (PC: p[[pc]] <> None -> pc_inj p len pc = Some pc')
  (MLEN: len = Datatypes.length m')
  (REG: match_reg p len r r')
  (MEM: match_mem p len m m')
  (STK: match_stk p len stk stk') :
  match_states p tp len (S_Running (pc, r, m, stk, false, ms)) (S_Running (pc', r', m', stk', false, ms))
| match_states_term :
  match_states p tp len S_Term S_Term
| match_states_fault :
  match_states p tp len S_Fault S_Fault
| match_states_call_fault pc r m stk ms pc' r' m' stk'
  (PC: p[[pc]] <> Some ICTarget)
  (TPC: fetch tp len pc' <> Some ICTarget)
  (MLEN: len = Datatypes.length m')
  (REG: match_reg p len r r')
  (MEM: match_mem p len m m')
  (STK: match_stk p len stk stk') :
  match_states p tp len (S_Running (pc, r, m, stk, true, ms)) (S_Running (pc', r', m', stk', true, ms))
| match_states_call pc r m stk ms pc' r' m' stk'
  (PC: p[[pc]] = Some ICTarget)
  (TPC: fetch tp len pc' = Some ICTarget)
  (MLEN: len = Datatypes.length m')
  (REG: match_reg p len r r')
  (MEM: match_mem p len m m')
  (STK: match_stk p len stk stk') :
  match_states p tp len (S_Running (pc, r, m, stk, true, ms)) (S_Running (pc', r', m', stk', true, ms)).

Definition match_dir (p: MiniCET.prog) (len: nat) (d: MiniCET.direction) (d': direction) : Prop :=
  match d, d' with
  | MiniCET.DCall pc, DCall l => pc_inj p len pc = Some l
  | MiniCET.DBranch b, DBranch b' => b = b'
  | MiniCET.DRet pc, DRet l => pc_inj p len pc = Some l
  | _, _ => False
  end.

Definition match_dirs (p: MiniCET.prog) (len: nat) (ds: MiniCET.dirs) (ds': dirs) : Prop :=
  Forall2 (match_dir p len) ds ds'.

Definition match_ob (p: MiniCET.prog) (len: nat) (o: MiniCET.observation) (o': observation) : Prop :=
  match o, o' with
  | MiniCET.OBranch b, OBranch b' => b = b'
  | MiniCET.OLoad n, OLoad n' => n = n'
  | MiniCET.OStore n, OStore n' => n = n'
  | MiniCET.OCall l, OCall l' => pc_inj p len l = Some l'
  | _, _ => False
  end.

Definition match_obs (p: MiniCET.prog) (len: nat) (ds: MiniCET.obs) (ds': obs) : Prop :=
  Forall2 (match_ob p len) ds ds'.



Definition wf_dir (p: prog) (len: nat) (d: direction) : Prop :=
  match d with
  | DCall pc' => is_some (nth_error p (pc' - len)) && (len <=? pc')%nat
  (* | DRet pc' => wf_ret p len pc' *)
  | _ => True
  end.

Definition wf_ds (p: prog) (len: nat) (ds: dirs) : Prop :=
  Forall (wf_dir p len) ds.

Lemma pc_inj_iff p len pc l (LE: l >= len):
  pc_inj p len pc = Some l <-> pc_inj_inv p len l = Some pc.
Proof.
  unfold pc_inj, pc_inj_inv. destruct pc. split; i.
  - des_ifs. eapply coord_flat_inverse.
    rewrite Heq. f_equal. lia.
  - exploit flat_coord_inverse; eauto. i. rewrite x0.
    f_equal. lia.
Qed.

Lemma transpose_len {X} (ol: list (option X)) l
  (TRNS: transpose ol = Some l) :
  Datatypes.length ol = Datatypes.length l.
Proof.
  ginduction ol; ss; ii; clarify.
  des_ifs. ss. erewrite IHol; eauto.
Qed.

Lemma machine_blk_len p_ctx len blk tblk b
  (MBLK: machine_blk p_ctx len (blk, b) = Some tblk) :
  Datatypes.length blk = Datatypes.length tblk.
Proof.
  unfold machine_blk in MBLK. ss. eapply transpose_len in MBLK.
  rewrite length_map in MBLK; eauto.
Qed.

Lemma machine_blk_inv p_ctx len blk ct blk' l ti
  (MBLK: machine_blk p_ctx len (blk, ct) = Some blk')
  (LK: nth_error blk' l = Some ti) :
  exists i, nth_error blk l = Some i /\ machine_inst p_ctx len i = Some ti.
Proof.
  ginduction blk; i.
  { unfold machine_blk in MBLK. ss. clarify.
    rewrite nth_error_nil in LK. clarify. }
  unfold machine_blk in MBLK. ss. des_ifs_safe.
  destruct l.
  { simpl in *. clarify. esplits; eauto. }
  simpl in *. exploit IHblk; eauto.
Unshelve. econs.
Qed.

Lemma lookup_from_target
  (p p_ctx: MiniCET.prog) len (tp: prog) l ti
  (LLEN: l >= len)
  (TRANSL: _machine_prog p_ctx p len = Some tp)
  (TGT: nth_error tp (l - len) = Some ti):
  exists pc, pc_inj p len pc = Some l.
Proof.
  ginduction p; ii.
  { ii. unfold _machine_prog in TRANSL. ss. clarify.
    rewrite nth_error_nil in TGT. clarify. }
  unfold _machine_prog in TRANSL. simpl in TRANSL. des_ifs_safe.
  simpl in TGT.
  rewrite nth_error_app in TGT. des_ifs.
  - exists (0, (l - len)). unfold pc_inj. simpl.
    eapply machine_blk_len in Heq0; [|econs]. rewrite Heq0. des_ifs.
    f_equal. lia.
  - exploit IHp.
    2:{ unfold _machine_prog. erewrite Heq1. eauto. }
    2:{ replace (l - len - Datatypes.length l1)
      with (l - Datatypes.length l1 - len) in TGT by lia. eauto. }
    { rewrite ltb_ge in Heq. lia. }
    i. des. destruct pc0 as [b o].
    exists (add b 1, o).
    unfold pc_inj in *. replace (add b 1) with (S b) by lia.
    simpl. des_ifs_safe. eapply machine_blk_len in Heq0; [|econs].
    rewrite Heq0. f_equal. rewrite ltb_ge in Heq. lia.
Qed.

Lemma tgt_inv_aux
  (p p_ctx: MiniCET.prog) len (tp: prog) pc l ti
  (TRANSL: _machine_prog p_ctx p len = Some tp)
  (TGT: nth_error tp (l - len) = Some ti)
  (INJ: pc_inj p len pc = Some l) :
  exists i, p[[pc]] = Some i /\ machine_inst p_ctx len i = Some ti.
Proof.
  ginduction p; ii.
  { ii. unfold _machine_prog in TRANSL. ss. clarify.
    rewrite nth_error_nil in TGT. clarify. }
  unfold _machine_prog in TRANSL. simpl in TRANSL. des_ifs_safe.
  simpl in TGT. destruct pc0 as [b o]. destruct a as [blk ct].
  destruct b as [|b].
  { ss. unfold pc_inj in INJ. simpl in INJ.
    des_ifs_safe. rewrite ltb_lt in Heq2.
    replace (n + len - len) with n in TGT by lia.
    exploit machine_blk_len; eauto. i. rewrite x0 in Heq2.
    rewrite nth_error_app1 in TGT; [|lia].
    exploit machine_blk_inv; eauto. }
  replace (((blk, ct) :: p) [[(S b, o)]]) with p[[(b, o)]] by ss.
  unfold pc_inj in INJ. simpl in INJ. des_ifs_safe.
  assert (Datatypes.length blk + n0 + len - len = Datatypes.length blk + n0) by lia.
  rewrite H in TGT. clear H.
  exploit machine_blk_len; eauto. i. rewrite x0 in TGT.
  rewrite nth_error_app2 in TGT; [|lia].
  rewrite add_comm, add_sub in TGT.
  exploit IHp.
  { unfold _machine_prog. erewrite Heq1. eauto. }
  { replace n0 with (n0 + len - len) in TGT by lia. eauto. }
  { unfold pc_inj. erewrite Heq2. eauto. }
  eauto.
Qed.

Lemma tgt_inv
  (p: MiniCET.prog) len (tp: prog) pc l ti
  (TRANSL: machine_prog p len = Some tp)
  (TGT: nth_error tp (l - len) = Some ti)
  (INJ: pc_inj p len pc = Some l) :
  exists i, p[[pc]] = Some i /\ machine_inst p len i = Some ti.
Proof.
  eapply tgt_inv_aux; eauto.
Qed.

Lemma wf_dir_inj
  (p: MiniCET.prog) len (tp: prog) d td
  (TRANSL: machine_prog p len = Some tp)
  (WFT: wf_dir tp len td)
  (MATCH: match_dir p len d td):
  wf_dir' p d.
Proof.
  unfold wf_dir, wf_dir' in *. des_ifs.
  red in MATCH. unfold is_some in *. des_ifs_safe.
  exploit tgt_inv; eauto.
  i. des; clarify.
Qed.

Lemma wf_ds_inj
  (p: MiniCET.prog) len (tp: prog) ds tds
  (TRANSL: machine_prog p len = Some tp)
  (WFT: wf_ds tp len tds)
  (MATCH: match_dirs p len ds tds):
  wf_ds' p ds.
Proof.
  ginduction MATCH; i.
  { econs. }
  inv WFT. econs; eauto.
  { eapply wf_dir_inj; eauto. }
  exploit IHMATCH; eauto.
Qed.

Lemma match_dir_unique p len d1 d2 dt
  (MATCH1: match_dir p len d1 dt)
  (MATCH2: match_dir p len d2 dt):
  d1 = d2.
Proof.
  unfold match_dir in *. des_ifs.
  - assert (l >= len).
    { unfold pc_inj in *. des_ifs. lia. }
    rewrite pc_inj_iff in *; clarify.
  - assert (l >= len).
    { unfold pc_inj in *. des_ifs. lia. }
    rewrite pc_inj_iff in *; clarify.
Qed.

Lemma match_dirs_unique p len ds1 ds2 dst
  (MATCH1: match_dirs p len ds1 dst)
  (MATCH2: match_dirs p len ds2 dst):
  ds1 = ds2.
Proof.
  ginduction dst; i; inv MATCH1; inv MATCH2; auto.
  exploit (match_dir_unique p len x x0); eauto. i. subst.
  exploit (IHdst _ _ l l0); eauto. i. clarify.
Qed.

Lemma match_ob_unique_src p len o1 o2 ot
  (MATCH1: match_ob p len o1 ot)
  (MATCH2: match_ob p len o2 ot):
  o1 = o2.
Proof.
  unfold match_ob in *. des_ifs.
  assert (l0 >= len).
  { unfold pc_inj in *. des_ifs. lia. }
  rewrite pc_inj_iff in *; clarify.
Qed.

Lemma match_obs_unique_src p len os1 os2 ost
  (MATCH1: match_obs p len os1 ost)
  (MATCH2: match_obs p len os2 ost):
  os1 = os2.
Proof.
  ginduction ost; i; inv MATCH1; inv MATCH2; auto.
  exploit (match_ob_unique_src p len x x0); eauto. i. subst.
  exploit (IHost _ len l l0); eauto. i. clarify.
Qed.

Lemma match_ob_unique_tgt p len o ot1 ot2
  (MATCH1: match_ob p len o ot1)
  (MATCH2: match_ob p len o ot2):
  ot1 = ot2.
Proof.
  unfold match_ob in *. des_ifs.
Qed.

Lemma match_obs_unique_tgt p len os ost1 ost2
  (MATCH1: match_obs p len os ost1)
  (MATCH2: match_obs p len os ost2):
  ost1 = ost2.
Proof.
  ginduction os; i; inv MATCH1; inv MATCH2; auto.
  exploit (match_ob_unique_tgt p _ _ y y0); eauto. i. subst.
  exploit (IHos _ _ l' l'0); eauto. i. clarify.
Qed.

Lemma prefix_match_obs
  p len os1 os2 os os0
  (MATCH1: match_obs p len os os1)
  (MATCH2: match_obs p len os0 os2)
  (OBS: Utils.prefix os os0 \/ Utils.prefix os0 os) :
  Utils.prefix os1 os2 \/ Utils.prefix os2 os1.
Proof.
  des.
  - left. unfold Utils.prefix in *. des.
    subst. exploit Forall2_app_inv_l; eauto. i. des.
    subst. exists l2'. exploit (match_obs_unique_tgt _ _ os os1 l1'); eauto.
    i. subst. auto.
  - right. unfold Utils.prefix in *. des.
    subst. exploit Forall2_app_inv_l; eauto. i. des.
    subst. exists l2'. exploit (match_obs_unique_tgt _ _ os0 os2 l1'); eauto.
    i. subst. auto.
Qed.

Lemma pc_inj_inc p len pc pc'
  (INJ: pc_inj p len pc = Some pc')
  (PC: p [[pc + 1]] <> None) :
  pc_inj p len (pc + 1) = Some (add pc' 1).
Proof.
  unfold pc_inj in *. ginduction p; ii.
  { exfalso. eapply PC. destruct pc0. ss. }
  destruct pc0 as [b o]. destruct a as [blk ct].
  destruct b as [|b].
  { simpl in *. des_ifs_safe.
    rewrite nth_error_Some in PC.
    rewrite <- ltb_lt in PC. rewrite PC. f_equal. lia. }
  ss. des_ifs_safe.
  specialize (IHp len (b, o)). des_ifs_safe.
  exploit IHp; eauto.
  { ii. ss. des_ifs. }
  i. des_ifs_safe.
  assert (n = add n0 1) by lia. subst. ss. des_ifs_safe.
  f_equal. lia.
Qed.

Lemma minicet_linear_bcc_single
  (p: MiniCET.prog) len (tp: prog) sc tc tct tds tos
  (TRANSL: machine_prog p len = Some tp)
  (SAFE: exists ds os sct, p |- <(( S_Running sc ))> -->_ ds ^^ os  <(( sct ))>)
  (MATCH: match_states p tp len (S_Running sc) (S_Running tc))
  (WFDS: wf_ds tp len tds)
  (TGT: tp |- <(( S_Running tc ))> -->m_ tds ^^ tos  <(( tct ))>) :
  exists ds os sct, p |- <(( S_Running sc ))> -->_ ds ^^ os  <(( sct ))>
             /\ match_states p tp len sct tct
             /\ match_dirs p len ds tds /\ match_obs p len os tos.
Proof.
  inv MATCH; cycle 1.
  (* fault *)
  { inv TGT; clarify.
    esplits; try sfby econs. }
  (* call *)
  { admit. }
  destruct (p[[pc0]]) eqn:ISRC.
  2:{ des. inv SAFE; clarify. }
  des. exploit PC; [ii; clarify|]. clear PC. intros PC. inv TGT.
  - exploit tgt_inv; eauto. i. des. unfold machine_inst in x1. des_ifs.
    esplits; econs; eauto. unfold pc_inj. intro PC'.
    destruct pc0 as [b o]. simpl.
    exploit pc_inj_inc; eauto.
  - exploit tgt_inv; eauto. i. des. unfold machine_inst in x0. des_ifs.
    esplits. 3-4: econs.
    { econs 2; eauto. }
    econs; eauto.
    { i. exploit pc_inj_inc; eauto. }
    red. i.
    destruct (string_dec x x0); subst.
    { do 2 rewrite MiniCET_Index.t_update_eq. eapply eval_inject; eauto. }
    do 2 (rewrite MiniCET_Index.t_update_neq; eauto).
  - admit. (* div *)
  - exploit tgt_inv; eauto. i. des. unfold machine_inst in x1.
    destruct i0; ss; clarify; try sfby des_ifs. des_ifs_safe.
    esplits.
    { econs 4; eauto. rewrite <- H8.
      exploit eval_inject; eauto. i.
      red in x1. des_ifs; ss.
      { inv SAFE; clarify. rewrite Heq1 in H10. ss. }
      { inv SAFE; clarify. rewrite Heq1 in H10. ss. } }
    2:{ repeat econs. }
    2:{ repeat econs. }
    econs; eauto. i. destruct b'; auto.
    exploit pc_inj_inc; try eapply PC; eauto.
  - exploit tgt_inv; eauto. i. des. unfold machine_inst in x1. des_ifs.
    esplits; try sfby (repeat econs).
    { econs 5; eauto. }
    econs; eauto.
  - exploit tgt_inv; eauto. i. des. unfold machine_inst in x0. des_ifs.
    inv SAFE; clarify.
    assert (n0 = n).
    { exploit eval_inject; eauto. i. unfold to_nat in *. des_ifs. }
    subst.

    assert (exists v, nth_error m n = Some v /\ val_inject p (Datatypes.length m') v v').
    { red in MEM. specialize (MEM n). des_ifs. esplits; eauto. }

    des. clarify. esplits.
    { econs 6; eauto. }
    2:{ econs. }
    2:{ econs; eauto. red. auto. }
    econs; eauto.
    { i. exploit pc_inj_inc; try eapply PC; eauto. }
    { red. i. unfold match_mem in MEM.
      esplits; try sfby (repeat econs).
      { eapply asgn_match_reg; eauto. } }
  - exploit tgt_inv; eauto. i. des. unfold machine_inst in x1. des_ifs.
    inv SAFE; clarify.
    assert (n0 = n).
    { exploit eval_inject; try eapply Heq; eauto. i. unfold to_nat in *. des_ifs. }
    subst.

    assert (VAL: val_inject p (Datatypes.length m') (MCC.eval r e0) (eval r' e')).
    { eapply eval_inject; eauto. }

    esplits.
    { econs 7; eauto. }
    2-3: repeat econs.
    econs; eauto.
    { i. exploit pc_inj_inc; try eapply PC; eauto. }
    { rewrite upd_length. auto. }
    eapply store_match_mem; eauto.
  - exploit tgt_inv; eauto. i. des. unfold machine_inst in x1. des_ifs.
    inv SAFE; clarify.

    assert (exists pc'_src, pc_inj p (Datatypes.length m') pc'_src = Some (pc'0)).
    { red in WFDS. inv WFDS. red in H1. unfold is_some in H1.
      des_ifs. eapply lookup_from_target; eauto. eapply leb_complete in H1. lia. }
    des.

    exploit wf_ds_inj; eauto; i.
    { instantiate (1:= [MiniCET.DCall pc'_src]).
      repeat econs. red. eauto. }

    assert (VINJ: val_inject p (Datatypes.length m') (FP l0) (N l)).
    { unfold to_fp, to_nat in *. des_ifs; clarify.
      rewrite <- Heq1, <- Heq0. eapply eval_inject; eauto. }

    esplits.
    { eapply MiniCET_Index.SpecSMI_Call; eauto. }
    { instantiate (1:=pc'_src). admit.
      (* assert (((fst pc'_src =? l0)%nat && (snd pc'_src =? 0)%nat) = (pc'0 =? l)%nat). *)
      (* { red in VINJ. des_ifs. *)
      (*   destruct pc'_src as [b o]. rename pc'0 into n0. simpl. *)
      (*   destruct (Nat.eq_dec b l0); subst. *)
      (*   { destruct (Nat.eq_dec o 0); clarify. *)
      (*     { repeat rewrite Nat.eqb_refl. simpl. auto. } *)
      (*     hexploit pc_inj_inject. 2: eapply H. 2: eapply Heq0. *)
      (*     { ii. clarify. } *)
      (*     ii. rewrite <- Nat.eqb_neq in *. rewrite n1. *)
      (*     rewrite andb_false_r. auto. } *)
      (*   { hexploit pc_inj_inject. 2: eapply H. 2: eapply Heq0. *)
      (*     { ii. clarify. } *)
      (*     ii. rewrite <- Nat.eqb_neq in *. rewrite n1. ss. } } *)
      (* rewrite H0. eapply match_states_intro; i; eauto. *)
      (* econs; eauto. *)
      (* red. i. *)
      (* exploit pc_inj_inc; try eapply H1; eauto. *)
    }
    { repeat econs. red. eauto. }
    { repeat econs. unfold match_ob, val_inject in *. des_ifs. }
  - exploit tgt_inv; eauto. i. des. unfold machine_inst in x1. des_ifs.
    inv SAFE; clarify.
    esplits; eauto. 3-4: repeat econs.
    { eapply MiniCET_Index.SpecSMI_CTarget. eauto. }
    econs; eauto. ii. exploit pc_inj_inc; try eapply PC; eauto.
  - exploit tgt_inv; eauto. i. des. unfold machine_inst in x1. des_ifs.
    inv STK. inv SAFE; clarify.

    assert (SRCT: exists pc''_src, pc_inj p (Datatypes.length m') pc''_src = Some (pc'')
                           /\ In pc''_src (MiniCET_Index.call_return_targets p)).
    { admit. }
    des.

    esplits; eauto. 3-4: repeat econs.
    { eapply MiniCET_Index.SpecSMI_Ret; eauto. }
    + admit.
    + admit. (* red. eauto. *)

  - exploit tgt_inv; eauto. i. des. unfold machine_inst in x0. des_ifs.
    esplits; try sfby econs.
    { eapply MiniCET_Index.SpecSMI_Peek. eauto. }
    { econs; eauto.
      - ii. admit.
      - destruct stk'.
        + inv STK. red. ii.
          destruct (string_dec x x0); subst.
          { do 2 rewrite MiniCET_Index.t_update_eq. ss. }
          do 2 (rewrite MiniCET_Index.t_update_neq; eauto).
        + inv STK. red. ii.
          subst val.
          destruct (string_dec x x2); subst.
          { do 2 rewrite MiniCET_Index.t_update_eq.
            hexploit H2; ii; clarify. admit. (* stack match *) }
          do 2 (rewrite MiniCET_Index.t_update_neq; eauto). }
  - exploit tgt_inv; eauto. i. des. unfold machine_inst in x1. des_ifs.
    clear SAFE. inv STK.
    esplits; eauto. 2-4: repeat econs.
    { eapply MiniCET_Index.SpecSMI_Term. eauto. }
  (* - destruct (fetch tp (Datatypes.length m') pc') eqn:ITGT. *)
  (*   2:{ admit. } (* TODO: YH *) *)
  (*   exploit tgt_inv; eauto. i. des. *)
  (*   clear SAFE. *)
  (*   assert (i1 <> <{{ ctarget }}>). *)
  (*   { ii. eapply H8. subst. unfold machine_inst in x1. clarify. } *)
  (*   esplits; eauto. 2-4: repeat econs. *)
  (*   eapply MiniCET_Index.SpecSMI_Fault; eauto. ii. clarify. *)
Admitted.

Lemma minicet_linear_bcc
  (p: MiniCET.prog) len (tp: prog) sc tc tct tds tos n
  (TRANSL: machine_prog p len = Some tp)
  (SAFE: spec_exec_safe p sc)
  (MATCH: match_states p tp len (S_Running sc) (S_Running tc))
  (WFDS: wf_ds tp len tds)
  (TGT: tp |- <(( S_Running tc ))> -->m*_ tds ^^ tos ^^ n  <(( tct ))>) :
  exists ds os sct, p |- <(( S_Running sc ))> -->*_ ds ^^ os ^^ n  <(( sct ))>
             /\ match_states p tp len sct tct
             /\ match_dirs p len ds tds /\ match_obs p len os tos.
Proof.
  ginduction n; ii.
  { inv TGT. esplits; try econs. eauto. }
  assert (SAFE1: exists ds os sct, p |- <(( S_Running sc ))> -->_ ds ^^ os  <(( sct ))>).
  { eapply SAFE with (ds := []); econs. }
  inv TGT.
  eapply Forall_app in WFDS. destruct WFDS.
  exploit minicet_linear_bcc_single; try eapply H0; eauto. i. des.
  destruct sct; cycle 1.
  { inv x0. }
  { inv x1. inv H5; [|inv H2].
    exists (ds ++ []), (os ++ []), S_Fault.
    esplits; try repeat econs; auto.
    - do 2 rewrite app_nil_r; auto.
    - do 2 rewrite app_nil_r; auto. }
  { inv x1. inv H5;[|inv H2].
    exists (ds ++ []), (os ++ []), S_Term.
    esplits; try repeat econs; auto.
    - do 2 rewrite app_nil_r; auto.
    - do 2 rewrite app_nil_r; auto. }
  destruct sc2; try sfby inv x1.

  assert (WFDS: wf_ds' p ds).
  { eapply wf_ds_inj; try eapply x2; eauto. }

  assert (SAFE2: spec_exec_safe p a).
  { red. i. exploit SAFE.
    2:{ econs 2; [eapply x0|eapply H2]. }
    { red. rewrite Forall_app; eauto. }
    eauto. }
  exploit IHn; try eapply H5; eauto.
  i. des. esplits; try eapply x5.
  { econs; eauto. }
  { red. eapply Forall2_app; eauto. }
  { red. eapply Forall2_app; eauto. }
Qed.


Definition spec_same_obs_machine p pc r1 r2 len m1 m2 stk b : Prop :=
  forall ds n m os1 os2 c1 c2 (WFDS: wf_ds p len ds),
  p |- <(( S_Running (pc, r1, m1, stk, b, false) ))> -->m*_ds^^os1^^n <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, stk, b, false) ))> -->m*_ds^^ os2^^m <(( c2 ))> ->
  (Utils.prefix os1 os2) \/ (Utils.prefix os2 os1).

Definition relative_secure_spec_mir_mc (p:MiniCET.prog) (len:nat) (tp: prog) (trans : MiniCET.prog -> option prog)
  (r1 r2 r1' r2' : reg) (m1 m2 m1' m2' : mem) : Prop :=
  spec_same_obs p (0,0) r1 r2 m1 m2 [] true ->
  match_reg p len r1 r1' -> match_reg p len r2 r2' ->
  match_mem p len m1 m1' -> match_mem p len m2 m2' ->
  trans p = Some tp ->
  spec_same_obs_machine tp len r1' r2' len m1' m2' [] true.

Lemma spec_eval_relative_secure_spec_mir_mc_aux
  p r1 r2 r1' r2' m1 m2 m1' m2' tp
  (LEN1: Datatypes.length m1' = Datatypes.length m2')
  (REG1: match_reg p (Datatypes.length m1') r1 r1')
  (REG2: match_reg p (Datatypes.length m1') r2 r2')
  (MEM1: match_mem p (Datatypes.length m1') m1 m1')
  (MEM2: match_mem p (Datatypes.length m1') m2 m2')
  (TRANS: machine_prog p (Datatypes.length m1') = Some tp)
  (SPEC: spec_same_obs p (0, 0) r1 r2 m1 m2 [] true)
  (ISAFE1: spec_exec_safe p (0, 0, r1, m1, [], true, false))
  (ISAFE2: spec_exec_safe p (0, 0, r2, m2, [], true, false)):
  spec_same_obs_machine tp (Datatypes.length m1') r1' r2' (Datatypes.length m1') m1' m2' [] true.
Proof.
  assert (INITSAFE: p[[(0,0)]] <> None).
  { red in ISAFE1. exploit ISAFE1; [econs|econs|]. i. des. inv x0; ii; clarify. }

  assert (ISYNC: pc_inj p (Datatypes.length m1') (0, 0) = Some (Datatypes.length m1')).
  { clear -INITSAFE. ss. des_ifs. destruct p0. ss. clarify. }

  red. i.
  hexploit minicet_linear_bcc; [|eapply ISAFE1| | |eapply H|]; eauto.
  { econs; try sfby ss. }
  i. des.

  hexploit minicet_linear_bcc; [|eapply ISAFE2| | |eapply H0|]; eauto.
  { econs; try sfby ss. }
  i. des.

  assert (UNIQ: ds0 = ds1); subst.
  { eapply match_dirs_unique; eauto. }

  red in SPEC. hexploit SPEC.
  { eapply H1. }
  { eapply H5. }
  i. clear - H4 H8 H9.
  eapply prefix_match_obs; eauto.
Qed.

Lemma spec_eval_relative_secure_spec_mir_mc
  p r1 r2 r1' r2' m1 m2 m1' m2' tp
  (LEN1: Datatypes.length m1' = Datatypes.length m2')
  (SPEC: spec_same_obs p (0, 0) r1 r2 m1 m2 [] true)
  (ISAFE1: spec_exec_safe p (0, 0, r1, m1, [], true, false))
  (ISAFE2: spec_exec_safe p (0, 0, r2, m2, [], true, false)):
  relative_secure_spec_mir_mc p (Datatypes.length m1') tp (fun p => machine_prog p (Datatypes.length m1')) r1 r2 r1' r2' m1 m2 m1' m2'.
Proof.
  red. i. eapply spec_eval_relative_secure_spec_mir_mc_aux; eauto.
Qed.

Definition relative_secure_machine (p:MiniCET.prog) (len:nat) (tp: prog) (trans : MiniCET.prog -> option prog)
  (r1 r2 r1' r2' : reg) (m1 m2 m1' m2' : mem) : Prop :=
  seq_same_obs p (0,0) r1 r2 m1 m2 [] ->

  match_reg_src (uslh_prog p) len r1 r1' false -> match_reg_src (uslh_prog p) len r2 r2' false ->
  match_mem (uslh_prog p) len m1 m1' -> match_mem (uslh_prog p) len m2 m2' ->
  trans (uslh_prog p) = Some tp ->
  spec_same_obs_machine tp len r1' r2' len m1' m2' [] true.

Lemma spec_eval_relative_secure_machine
  p r1 r2 r1' r2' m1 m2 m1' m2' tp
  (FST: first_blk_call p)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (LEN1: Datatypes.length m1' = Datatypes.length m2')
  (NEM1: nonempty_mem m1)
  (NEM2: nonempty_mem m2)
  (CALLEE1: r1' ! callee = N (Datatypes.length m1'))
  (CALLEE2: r2' ! callee = N (Datatypes.length m2'))
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (SAFE1: seq_exec_safe p ((0,0), r1, m1, []))
  (SAFE2: seq_exec_safe p ((0,0), r2, m2, [])) :
  relative_secure_machine p (Datatypes.length m1') tp (fun p => machine_prog p (Datatypes.length m1')) r1 r2 r1' r2' m1 m2 m1' m2'.
Proof.
  red. i.
  set (ir1 := (msf !-> N 0; callee !-> (FP 0); r1)).
  set (ir2 := (msf !-> N 0; callee !-> (FP 0); r2)).

  hexploit (spec_eval_relative_secure p r1 r2 ir1 ir2 m1 m2); eauto.
  intros REL. red in REL.

  assert (IREG1: Rsync r1 ir1 false).
  { split; subst ir1; ss. ii. des.
    do 2 (rewrite MiniCET_Index.t_update_neq; eauto). }

  assert (IREG2: Rsync r2 ir2 false).
  { split; subst ir2; ss. ii. des.
    do 2 (rewrite MiniCET_Index.t_update_neq; eauto). }

  hexploit REL; eauto. intros SPEC.

  hexploit seq_spec_safety_preservation_init; try eapply SAFE1; eauto.
  { subst ir1. rewrite MiniCET_Index.t_update_neq; eauto. ii; clarify. }
  intros ISAFE1.

  hexploit seq_spec_safety_preservation_init; try eapply SAFE2; eauto.
  { subst ir2. rewrite MiniCET_Index.t_update_neq; eauto. ii; clarify. }
  intros ISAFE2.

  assert (INITSAFE: (uslh_prog p)[[(0,0)]] <> None).
  { red in ISAFE1. exploit ISAFE1; [econs|econs|]. i. des. inv x0; ii; clarify. }

  assert (ISYNC: pc_inj (uslh_prog p) (Datatypes.length m1') (0, 0) = Some (Datatypes.length m1')).
  { clear -INITSAFE. destruct (uslh_prog p); ss.
    destruct p0. ss. des_ifs. }

  eapply spec_eval_relative_secure_spec_mir_mc_aux; try eapply SPEC; eauto.
  - subst ir1. red in H0. des. red. i.
    destruct (string_dec x callee).
    { subst. rewrite CALLEE1. ss. rewrite ISYNC. ss. }
    destruct (string_dec x msf).
    { des. subst. rewrite H5. ss. }
    do 2 (rewrite TotalMap.t_update_neq; eauto).
  - subst ir2. red in H1. des. red. i.
    destruct (string_dec x callee).
    { subst. rewrite CALLEE2. ss. rewrite ISYNC. ss. }
    destruct (string_dec x msf).
    { des. subst. rewrite H5. ss. }
    do 2 (rewrite TotalMap.t_update_neq; eauto).
Qed.
