
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From SECF Require Import Utils.
From SECF Require Import SimDiagrams.
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
  | SSMI_Skip : forall pc rs m,
      fetch p (mem_length m) pc = Some <{{ skip }}> ->
      p |- <(( S_Running (pc, rs, m) ))> -->^[] <(( S_Running (add pc 1, rs, m) ))>
  | SSMI_Ctarget : forall pc rs m,
      fetch p (mem_length m) pc = Some <{{ ctarget }}> ->
      p |- <(( S_Running (pc, rs, m) ))> -->^[] <(( S_Running (add pc 1, rs, m) ))>
  | SSMI_Asgn : forall pc r m e x,
      fetch p (mem_length m) pc = Some <{{ x := e }}> ->
      p |- <(( S_Running (pc, r, m) ))> -->^[] <(( S_Running (add pc 1, (x !-> (eval r e); r), m) ))>
  | SSMI_Div : forall pc r m e1 e2 x v1 v2,
      fetch p (mem_length m) pc = Some <{{ x <- div e1, e2 }}> ->
      to_nat (eval r e1) = Some v1 ->
      to_nat (eval r e2) = Some v2 ->
      let res := match v2 with
                | 0 => UV
                | _ => N (div v1 v2)
                end
      in
      p |- <(( S_Running (pc, r, m) ))> -->^[ODiv v1 v2] <(( S_Running (add pc 1, (x !-> res; r), m) ))>
  | SSMI_Branch : forall pc pc' r m e n l,
      fetch p (mem_length m) pc = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      pc' = (if (not_zero n) then l else add pc 1) ->
      p |- <(( S_Running (pc, r, m) ))> -->^[OBranch (not_zero n)] <(( S_Running (pc', r, m) ))>
  | SSMI_Jump : forall l pc r m,
      fetch p (mem_length m) pc = Some <{{ jump l }}> ->
      p |- <(( S_Running (pc, r, m) ))> -->^[] <(( S_Running (l, r, m) ))>
  | SSMI_Load : forall pc r m x e n v',
      fetch p (mem_length m) pc = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m.(memory) n = Some v' ->
      p |- <(( S_Running (pc, r, m) ))> -->^[OLoad n] <(( S_Running (add pc 1, (x !-> v'; r), m) ))>
  | SSMI_Store : forall pc r m e e' n,
      fetch p (mem_length m) pc = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( S_Running (pc, r, m) ))> -->^[OStore n] <(( S_Running (add pc 1, r, upd_mem n m (eval r e')) ))>
  | SSMI_Call : forall pc r m e sp_val l,
      fetch p (mem_length m) pc = Some <{{ call e }}> ->
      to_nat (eval r e) = Some l ->
      r ! sp = N sp_val ->
      S sp_val < stack_top m ->
      p |- <(( S_Running (pc, r, m) ))> -->^[OCall l sp_val] <(( S_Running (l, sp !-> N (S sp_val); r, upd_mem (S sp_val) m (N (add pc 1))) ))>
  | SSMI_Ret : forall pc r m sp_val pc',
      fetch p (mem_length m) pc = Some <{{ ret }}> ->
      r ! sp = N sp_val ->
      sp_val < stack_top m ->
      nth_error m.(memory) sp_val = Some (N pc') ->
      p |- <(( S_Running (pc, r, m) ))> -->^[ORet pc' sp_val] <(( S_Running (pc', sp !-> N (sp_val - 1); r, m) ))>
  | SSMI_Term : forall pc r m,
      fetch p (mem_length m) pc = Some <{{ exit }}> ->
      p |- <(( S_Running (pc, r, m) ))> -->^[] <(( S_Term ))>

  where "p |- <(( c ))> -->^ os <(( ct ))>" :=
      (seq_eval_small_step_inst p c ct os).

Definition wf_ret (p: prog) (len: nat) (pc: nat) : Prop :=
  exists e, MoreLinear.fetch p len (pc - 1) = Some <{{ call e }}> /\ Nat.le (Nat.add len 1) pc.

Definition prog_terminator (p: prog) : Prop :=
  match rev p with
  | [] => False
  | h :: _ => is_terminator h
  end.

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
  | SpecSMI_Skip  :  forall pc r m ms sb,
      fetch p (mem_length m) pc = Some <{{ skip }}> ->
      p |- <(( S_Running ((pc, r, m), sb, false, ms) ))> -->m_[]^^[] <(( S_Running ((add pc 1, r, m), sb, false, ms) ))>
  | SpecSMI_Asgn : forall pc r m ms e x sb,
      fetch p (mem_length m) pc = Some <{{ x := e }}> ->
      p |- <(( S_Running ((pc, r, m), sb, false, ms) ))> -->m_[]^^[] <(( S_Running ((add pc 1, (x !-> (eval r e); r), m), sb, false, ms) ))>
  | SpecSMI_Div : forall pc r m ms e1 e2 x v1 v2 sb,
      fetch p (mem_length m) pc = Some <{{ x <- div e1, e2 }}> ->
      to_nat (eval r e1) = Some v1 ->
      to_nat (eval r e2) = Some v2 ->
      let res := match v2 with
                | 0 => UV
                | _ => N (div v1 v2)
                end
      in
      p |- <(( S_Running ((pc, r, m), sb, false, ms) ))> -->m_[]^^[ODiv v1 v2] <(( S_Running ((add pc 1, (x !-> res; r), m), sb, false, ms) ))>
  | SpecSMI_Branch : forall pc pc' r m ms ms' b (b': bool) e n l sb,
      fetch p (mem_length m) pc = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      b = (not_zero n) ->
      pc' = (if b' then l else (add pc 1)) ->
      ms' = ms || negb (Bool.eqb b b') ->
      p |- <(( S_Running ((pc, r, m), sb, false, ms) ))> -->m_[DBranch b']^^[OBranch b] <(( S_Running ((pc', r, m), sb, false, ms') ))>
  | SpecSMI_Jump : forall l pc r m ms sb,
      fetch p (mem_length m) pc = Some <{{ jump l }}> ->
      p |- <(( S_Running ((pc, r, m), sb, false, ms) ))> -->m_[]^^[] <(( S_Running ((l, r, m), sb, false, ms) ))>
  | SpecSMI_Load : forall pc r m x e n v' sb,
      fetch p (mem_length m) pc = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m.(memory) n = Some v' ->
      p |- <(( S_Running ((pc, r, m), sb, false, false) ))> -->m_[]^^[OLoad n] <(( S_Running ((add pc 1, (x !-> v'; r), m), sb, false, false) ))>
  | SpecSMI_Load_Misspec : forall pc r m x e n v' sb,
      fetch p (mem_length m) pc = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      v' = sb ! n ->
      p |- <(( S_Running ((pc, r, m), sb, false, true) ))> -->m_[]^^[OLoad n] <(( S_Running ((add pc 1, (x !-> v'; r), m), sb, false, true) ))>
  | SpecSMI_Store : forall pc r m e e' n sb,
      fetch p (mem_length m) pc = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( S_Running ((pc, r, m), sb, false, false) ))> -->m_[]^^[OStore n] <(( S_Running ((add pc 1, r, upd_mem n m (eval r e')), n !-> eval r e'; sb, false, false) ))>
  | SpecSMI_Store_Misspec : forall pc r m e e' n sb,
      fetch p (mem_length m) pc = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( S_Running ((pc, r, m), sb, false, true) ))> -->m_[]^^[OStore n] <(( S_Running ((add pc 1, r, m), n !-> eval r e'; sb, false, true) ))>
  | SpecSMI_Call : forall pc pc' r m e l ms' sp_val sb,
      fetch p (mem_length m) pc = Some <{{ call e }}> ->
      to_nat (eval r e) = Some l ->
      r ! sp = N sp_val ->
      S sp_val < stack_top m ->
      ms' = negb (pc' =? l)%nat ->
      p |- <(( S_Running ((pc, r, m), sb, false, false) ))> -->m_[DCall pc']^^[OCall l sp_val] <(( S_Running ((pc', sp !-> N (S sp_val); r, upd_mem (S sp_val) m (N (add pc 1))), S sp_val !-> N (add pc 1); sb, true, ms') ))>
  | SpecSMI_Call_Misspec : forall pc pc' r m e l sp_val sb,
      fetch p (mem_length m) pc = Some <{{ call e }}> ->
      to_nat (eval r e) = Some l ->
      r ! sp = N sp_val ->
      p |- <(( S_Running ((pc, r, m), sb, false, true) ))> -->m_[DCall pc']^^[OCall l sp_val] <(( S_Running ((pc', sp !-> N (S sp_val); r, m), S sp_val !-> N (add pc 1); sb, true, true) ))>
  | SpecSMI_Ret_Dir : forall pc r m pc' pc'' ms' sp_val sb,
      fetch p (mem_length m) pc = Some <{{ ret }}> ->
      wf_ret p (mem_length m) pc'' ->
      r ! sp = N sp_val ->
      sp_val < stack_top m ->
      ms' = negb (pc' =? pc'')%nat ->
      nth_error m.(memory) sp_val = Some (N pc') ->
      p |- <(( S_Running ((pc, r, m), sb, false, false) ))> -->m_[DRet (Some pc'')]^^[ORet pc' sp_val] <(( S_Running ((pc'', sp !-> N (sp_val - 1); r, m), sb, false, ms') ))>
  | SpecSMI_Ret_Step : forall pc r m pc' sp_val sb,
      fetch p (mem_length m) pc = Some <{{ ret }}> ->
      r ! sp = N sp_val ->
      sp_val < stack_top m ->
      nth_error m.(memory) sp_val = Some (N pc') ->
      p |- <(( S_Running ((pc, r, m), sb, false, false) ))> -->m_[DRet None]^^[ORet pc' sp_val] <(( S_Running ((pc', sp !-> N (sp_val - 1); r, m), sb, false, false) ))>
  | SpecSMI_Ret_Misspec_Dir : forall pc r m pc' pc'' sp_val sb,
      fetch p (mem_length m) pc = Some <{{ ret }}> ->
      wf_ret p (mem_length m) pc'' ->
      r ! sp = N sp_val ->
      sb ! sp_val = N pc' ->
      p |- <(( S_Running ((pc, r, m), sb, false, true) ))> -->m_[DRet (Some pc'')]^^[ORet pc' sp_val] <(( S_Running ((pc'', sp !-> N (sp_val - 1); r, m), sb, false, true) ))>
  | SpecSMI_Ret_Misspec_Step : forall pc r m pc' sp_val sb,
      fetch p (mem_length m) pc = Some <{{ ret }}> ->
      r ! sp = N sp_val ->
      sb ! sp_val = N pc' ->
      p |- <(( S_Running ((pc, r, m), sb, false, true) ))> -->m_[DRet None]^^[ORet pc' sp_val] <(( S_Running ((pc', sp !-> N (sp_val - 1); r, m), sb, false, true) ))>
  | SpecSMI_Term : forall pc r m ms sb,
      fetch p (mem_length m) pc = Some <{{ exit }}> ->
      p |- <(( S_Running ((pc, r, m), sb, false, ms) ))> -->m_[]^^[] <(( S_Term ))>
  | SpecSMI_CTarget : forall pc r m ct ms sb,
      fetch p (mem_length m) pc = Some <{{ ctarget }}> ->
      p |- <(( S_Running ((pc, r, m), sb, ct, ms) ))> -->m_[]^^[] <(( S_Running ((add pc 1, r, m), sb, false, ms) ))>
  | SpecSMI_Fault : forall pc r m ms sb,
      fetch p (mem_length m) pc <> Some <{{ ctarget }}> ->
      p |- <(( S_Running ((pc, r, m), sb, true, ms) ))> -->m_[]^^[] <(( S_Fault ))>

  where "p |- <(( sc ))> -->m_ ds ^^ os  <(( sct ))>" :=
    (spec_eval_small_step p sc sct ds os).

Definition safe_imm_lin (p: prog) (st: state spec_cfg) : Prop :=
  match st with
  | S_Running sc => exists ds os stt, p |- <(( S_Running sc ))> -->m_ ds ^^ os  <(( stt ))>
  | S_Fault | S_Term => True
  | S_Undef => False
  end.

Definition lin_initial (p : prog) (inp : MiniCET_Index.input) : state spec_cfg :=
  let '(r, m) := inp in
  S_Running ((mem_length m, (callee !-> N (mem_length m); msf !-> N 0; r), m), mirror_mem m, true, false).

#[local]
Instance LinSpecLang : SimDiagrams.Language MiniCET_Index.input :=
  {|
    SimDiagrams.prog := prog;
    SimDiagrams.directive := direction;
    SimDiagrams.observation := observation;
    SimDiagrams.machine := state spec_cfg;
    SimDiagrams.initial_machine := lin_initial;
    SimDiagrams.step := fun p st ds os st' => spec_eval_small_step p st st' ds os;
    SimDiagrams.sequential_safe1 := safe_imm_lin;
  |}.

Notation "p |- <(( sc ))> -->m*_ ds ^^ os <(( sct ))>" :=
  (sem (L := LinSpecLang) p sc ds os sct) (at level 40, sc constr, sct constr).

(* -------------------------------------------------------------------------- *)
(* Transformers *)

Definition pc_of (p: MiniCET.prog) (len: nat) (n: nat) : cptr :=
  if (n <? len)%nat then (Datatypes.length p, 0)
  else match pc_inj_inv p len n with
       | Some pc => pc
       | None => (Datatypes.length p, 0)
       end.

Definition lin_dir (p: MiniCET.prog) (len: nat) (d: direction) : MiniCET.direction :=
  match d with
  | DBranch b => MiniCET.DBranch b
  | DCall n => MiniCET.DCall (pc_of p len n)
  | DRet on => MiniCET.DRet (option_map (pc_of p len) on)
  end.

Definition lin_Tdir (p: MiniCET.prog) (len: nat) (ds: dirs) : MiniCET.dirs :=
  map (lin_dir p len) ds.

Definition inj_pc (p: MiniCET.prog) (len: nat) (pc: cptr) : nat :=
  match pc_inj p len pc with
  | Some n => n
  | None => 0
  end.

Definition lin_ob (p: MiniCET.prog) (len: nat) (o: MiniCET.observation) : observation :=
  match o with
  | MiniCET.ODiv n1 n2 => ODiv n1 n2
  | MiniCET.OBranch b => OBranch b
  | MiniCET.OLoad n => OLoad n
  | MiniCET.OStore n => OStore n
  | MiniCET.OCall l n => OCall (inj_pc p len l) n
  | MiniCET.ORet l n => ORet (inj_pc p len l) n
  end.

Definition lin_Tobs (p: MiniCET.prog) (len: nat) (os: MiniCET.obs) : obs :=
  map (lin_ob p len) os.

Record lin_hstate := {
  pc : nat;
  ct : bool
}.

Definition tctrl_lin (st: state spec_cfg) : option lin_hstate :=
  match st with
  | S_Running ((pc, _, _), _, ct, _) => Some {| pc := pc; ct := ct |}
  | _ => None
  end.

Definition lin_step (tp: prog) (len: nat) (h: option lin_hstate) (ds: dirs) (os: obs) : option lin_hstate :=
  match h with
  | None => None
  | Some h =>
      if ct h then
        match fetch tp len (pc h) with
        | Some ICTarget => Some {| pc := add (pc h) 1; ct := false |}
        | _ => None
        end
      else
        match fetch tp len (pc h), ds, os with
        | Some (IBranch _ l), [DBranch b], _ => Some {| pc := if b then l else add (pc h) 1; ct := false |}
        | Some (IJump l), _, _ => Some {| pc := l; ct := false |}
        | Some (ICall _), [DCall pc'], _ => Some {| pc := pc'; ct := true |}
        | Some IRet, [DRet (Some pc'')], _ => Some {| pc := pc''; ct := false |}
        | Some IRet, [DRet None], [ORet pc' _] => Some {| pc := pc'; ct := false |}
        | Some IExit, _, _ => None
        | Some _, _, _ => Some {| pc := add (pc h) 1; ct := false |}
        | None, _, _ => None
        end
  end.

Definition lin_hist (tp: prog) (len: nat) : History (Lt := LinSpecLang) :=
  {| SimDiagrams.history := option lin_hstate;
     SimDiagrams.init_hist := Some {| pc := len; ct := true |};
     SimDiagrams.This := lin_step tp len |}.

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
  (forall x, x <> msf /\ x <> callee ->
        exists iv, val_match p (r ! x) iv /\ val_inject (uslh_prog p) len iv (r' ! x))
/\ r' ! msf = N (if ms then 1 else 0).

Definition match_mem_list (p: MiniCET.prog) (len: nat) (m m': list val) : Prop :=
  forall i, match nth_error m i, nth_error m' i with
       | None, _ => True
       | Some v, Some v' => val_inject p len v v'
       | Some v, None => False
       end.

Definition match_mem (p: MiniCET.prog) (len: nat) (m m': mem) : Prop :=
  match_mem_list p len m.(memory) m'.(memory) /\ stack_top m = stack_top m'.

Definition match_smem (p: MiniCET.prog) (len: nat) (sb: MCC.spec_mem) (sb': spec_mem) : Prop :=
  forall n, val_inject p len (sb ! n) (sb' ! n).

Definition match_mem_src (p: MiniCET.prog) (len: nat) (m m': mem) : Prop :=
  (forall i, match nth_error m.(memory) i, nth_error m'.(memory) i with
       | None, _ => True
       | Some v, Some v' => exists iv, val_match p v iv /\ val_inject (uslh_prog p) len iv v'
       | Some v, None => False
       end)
  /\ stack_top m = stack_top m'.

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

Lemma store_match_mem_list p len v v' m m' n
  (MEM: match_mem_list p len m m')
  (INJ: val_inject p len v v') :
  match_mem_list p len (upd n m v) (upd n m' v').
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

Lemma store_match_mem p len v v' m m' n
  (MEM: match_mem p len m m')
  (INJ: val_inject p len v v') :
  match_mem p len (upd_mem n m v) (upd_mem n m' v').
Proof.
  destruct MEM as [MEM TOP]. split; [|exact TOP].
  eapply store_match_mem_list; eauto.
Qed.

Lemma store_match_smem p len v v' sb sb' n
  (SMEM: match_smem p len sb sb')
  (INJ: val_inject p len v v') :
  match_smem p len (n !-> v; sb) (n !-> v'; sb').
Proof.
  intros k. destruct (Nat.eq_dec n k); subst.
  - rewrite !MiniCET_Index.t_update_eq. auto.
  - rewrite !MiniCET_Index.t_update_neq; auto.
Qed.

Variant match_states (p: MiniCET.prog) (tp: prog) (len: nat) : state MCC.spec_cfg -> state spec_cfg -> Prop :=
| match_states_intro pc r m sb ms pc' r' m' sb'
  (PC: p[[pc]] <> None -> pc_inj p len pc = Some pc')
  (MLEN: len = mem_length m')
  (REG: match_reg p len r r')
  (MEM: match_mem p len m m')
  (SMEM: match_smem p len sb sb') :
  match_states p tp len (S_Running (pc, r, m, sb, false, ms)) (S_Running (pc', r', m', sb', false, ms))
| match_states_term :
  match_states p tp len S_Term S_Term
| match_states_fault :
  match_states p tp len S_Fault S_Fault
| match_states_call_fault pc r m sb ms pc' r' m' sb'
  (PC: p[[pc]] <> Some ICTarget)
  (TPC: fetch tp len pc' <> Some ICTarget)
  (MLEN: len = mem_length m')
  (REG: match_reg p len r r')
  (MEM: match_mem p len m m')
  (SMEM: match_smem p len sb sb') :
  match_states p tp len (S_Running (pc, r, m, sb, true, ms)) (S_Running (pc', r', m', sb', true, ms))
| match_states_call pc r m sb ms pc' r' m' sb'
  (PC: p[[pc]] = Some ICTarget)
  (TPC: fetch tp len pc' = Some ICTarget)
  (SYNC: pc_inj p len pc = Some pc')
  (MLEN: len = mem_length m')
  (REG: match_reg p len r r')
  (MEM: match_mem p len m m')
  (SMEM: match_smem p len sb sb') :
  match_states p tp len (S_Running (pc, r, m, sb, true, ms)) (S_Running (pc', r', m', sb', true, ms)).

Definition lin_sim (p: MiniCET.prog) (tp: prog) (len: nat) (h: option lin_hstate)
  (s: state MCC.spec_cfg) (t: state spec_cfg) : Prop :=
  h = tctrl_lin t /\ match_states p tp len s t.

Definition lin_sync (len: nat) : input_sync (Ls := SpecLang) :=
  fun p inp inp' =>
    match_reg p len (fst inp) (fst inp')
    /\ match_mem p len (snd inp) (snd inp')
    /\ mem_length (snd inp') = len.

Definition lin_compiler (len: nat) : compiler (Ls := SpecLang) (Lt := LinSpecLang) :=
  fun p tp =>
    machine_prog p len = Some tp
    /\ Forall MiniCET_Index.last_inst_terminator p
    /\ p[[(0, 0)]] <> None.

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

Lemma machine_blk_inv_src p_ctx len blk ct blk' l i
  (MBLK: machine_blk p_ctx len (blk, ct) = Some blk')
  (LK: nth_error blk l = Some i) :
  exists ti, nth_error blk' l = Some ti /\ machine_inst p_ctx len i = Some ti.
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

Lemma not_terminator_has_next blk ct n i
  (TERM: last_inst_terminator (blk, ct))
  (NTH: nth_error blk n = Some i)
  (NT: ~ is_terminator i) :
  S n < Datatypes.length blk.
Proof.
  assert (NLEN: n < Datatypes.length blk).
  { eapply nth_error_Some. rewrite NTH. discriminate. }
  unfold last_inst_terminator in TERM. simpl in TERM.
  destruct (rev blk) as [|hd tl] eqn:Heq; [contradiction|].
  destruct (Nat.eq_dec n (Datatypes.length blk - 1)).
  - exfalso. subst.
    assert (BLK: blk = rev tl ++ [hd]).
    { rewrite <- (rev_involutive blk). rewrite Heq. ss. }
    assert (BLEN: Datatypes.length blk = S (Datatypes.length tl)).
    { rewrite BLK. rewrite app_length. simpl. rewrite length_rev. lia. }
    replace (Datatypes.length blk - 1) with (Datatypes.length tl) in NTH by lia.
    rewrite BLK in NTH.
    rewrite nth_error_app2 in NTH; [|rewrite length_rev; lia].
    rewrite length_rev in NTH.
    replace (Datatypes.length tl - Datatypes.length tl) with 0 in NTH by lia.
    ss. clarify.
  - lia.
Qed.

Lemma _machine_prog_call_has_next p_ctx p len ttp n e
  (MC: _machine_prog p_ctx p len = Some ttp)
  (BLKS: Forall last_inst_terminator p)
  (NTH: nth_error ttp n = Some (ICall e)) :
  exists i, nth_error ttp (S n) = Some i.
Proof.
  ginduction p; ii.
  { unfold _machine_prog in MC. ss. clarify.
    rewrite nth_error_nil in NTH. clarify. }
  unfold _machine_prog in MC. simpl in MC. des_ifs_safe.
  inv BLKS. destruct a as [blk ct_a].
  (* Heq0: machine_blk p_ctx len (blk, ct_a) = Some l0 *)
  (* Heq1: transpose (map (machine_blk p_ctx len) p) = Some l1 *)
  assert (MC_REST: _machine_prog p_ctx p len = Some (List.concat l1)).
  { unfold _machine_prog. rewrite Heq1. auto. }
  (* NTH is about concat (l0 :: l1) = l0 ++ concat l1 *)
  change (List.concat (l0 :: l1)) with (l0 ++ List.concat l1) in NTH.
  rewrite nth_error_app in NTH. des_ifs.
  - (* Call is in first block l0 *)
    exploit machine_blk_inv; eauto.
    intros (isrc & NTH_SRC & MINST).
    assert (exists e_src, isrc = ICall e_src).
    { destruct isrc; ss; des_ifs; eauto. }
    des. subst.
    assert (NT_CALL: ~ is_terminator (ICall e_src)) by ss.
    exploit not_terminator_has_next; eauto.
    intros SNLT.
    exploit machine_blk_len; eauto. intros BLEN.
    assert (S n < Datatypes.length l0) by lia.
    assert (nth_error l0 (S n) <> None).
    { rewrite nth_error_Some. auto. }
    destruct (nth_error l0 (S n)) eqn:E; [|contradiction].
    eexists.
    change (List.concat (l0 :: l1)) with (l0 ++ List.concat l1).
    rewrite nth_error_app1; eauto.
  - (* Call is in remaining blocks *)
    assert (NLE: Datatypes.length l0 <= n).
    { rewrite ltb_ge in *. lia. }
    exploit IHp; eauto.
    intros (i' & NXT).
    eexists.
    change (List.concat (l0 :: l1)) with (l0 ++ List.concat l1).
    rewrite nth_error_app2; [|lia].
    replace (S n - Datatypes.length l0) with (S (n - Datatypes.length l0)) by lia.
    eauto.
Qed.

Lemma last_inst_terminator_app_r (l1 l2: list inst) (b: bool)
  (TERM: last_inst_terminator (l2, b)) :
  last_inst_terminator (l1 ++ l2, b).
Proof.
  unfold last_inst_terminator in *. simpl fst in *.
  rewrite List.rev_app_distr.
  destruct (List.rev l2) eqn:E; [contradiction|].
  simpl. auto.
Qed.

Lemma uslh_inst_terminator_res i l o c res np
  (USLH: uslh_inst i l o c = (res, np))
  (TERM: is_terminator i) :
  last_inst_terminator (res, false).
Proof.
  destruct i; ss; unfold MiniCET.uslh_ret in *; clarify; ss.
Qed.

Lemma uslh_inst_newp_terminator i l o c res np
  (USLH: uslh_inst i l o c = (res, np)) :
  Forall last_inst_terminator np.
Proof.
  destruct i; ss; unfold MiniCET.uslh_ret in *; clarify; try econs.
  eapply bind_inv in USLH. des. subst.
  unfold add_block_M, add_block in USLH. clarify.
  ss. unfold MiniCET.uslh_ret in *. clarify.
  econs; [|econs]. ss.
Qed.

Lemma last_inst_terminator_tail a bl b
  (TERM: last_inst_terminator (a :: bl, b))
  (NE: bl <> []) :
  last_inst_terminator (bl, b).
Proof.
  unfold last_inst_terminator in *. simpl fst in *.
  destruct (List.rev bl) eqn:E.
  { exfalso. apply NE. apply List.length_zero_iff_nil.
    rewrite <- List.length_rev. rewrite E. ss. }
  assert (HR: List.rev (a :: bl) = i :: l ++ [a]).
  { simpl. rewrite E. auto. }
  rewrite HR in TERM. simpl in TERM. auto.
Qed.

Lemma concat_mapM_uslh_last_terminator bl ll n c results np
  (LEN: Datatypes.length ll = Datatypes.length bl)
  (MM: mapM (fun '(o, i) => uslh_inst i n o) (combine ll bl) c = (results, np))
  (TERM: last_inst_terminator (bl, false)) :
  last_inst_terminator (List.concat results, false).
Proof.
  ginduction bl; i.
  - unfold last_inst_terminator in TERM. ss.
  - destruct ll. { simpl in LEN. lia. }
    simpl in MM.
    exploit mapM_cons_inv; eauto. i. des. subst.
    destruct bl as [|b bl'].
    + (* singleton: [a] — last element is a terminator *)
      destruct ll. 2:{ simpl in LEN. lia. }
      unfold mapM in x1. ss. unfold MiniCET.uslh_ret in x1. clarify.
      simpl. rewrite List.app_nil_r.
      unfold last_inst_terminator in TERM. simpl fst in TERM.
      eapply uslh_inst_terminator_res; eauto.
    + (* cons: a :: b :: bl' *)
      assert (TERM': last_inst_terminator (b :: bl', false)).
      { eapply last_inst_terminator_tail; eauto. discriminate. }
      assert (LEN': Datatypes.length ll = Datatypes.length (b :: bl')).
      { simpl in *. lia. }
      specialize (IHbl ll n _ _ _ LEN' x1 TERM').
      simpl. eapply last_inst_terminator_app_r. auto.
Qed.

Lemma uslh_blk_last_terminator_res blk n c res np
  (TERM: last_inst_terminator blk)
  (NE: 0 < Datatypes.length (fst blk))
  (USLH: uslh_blk (n, blk) c = (res, np)) :
  last_inst_terminator res.
Proof.
  destruct blk as [insts is_proc].
  unfold uslh_blk in USLH. des_ifs_safe.
  eapply bind_inv in USLH. des. subst. unfold concatM in USLH.
  eapply bind_inv in USLH. des. subst. ss. unfold MiniCET.uslh_ret in *. clarify.
  assert (LIT: last_inst_terminator (List.concat a0, false)).
  { unfold add_index_uslh in USLH.
    eapply concat_mapM_uslh_last_terminator; try eapply USLH; eauto.
    eapply _offset_uslh_length. }
  destruct is_proc; ss; clarify; unfold MiniCET.uslh_ret in *; clarify.
  - change (last_inst_terminator
      ([<{{ ctarget }}>; <{{ msf := (callee = (& (n, 0))) ? msf : 1 }}>] ++ List.concat a0, true)).
    eapply last_inst_terminator_app_r. auto.
Qed.

Lemma uslh_blk_np_last_terminator blk n c res np
  (USLH: uslh_blk (n, blk) c = (res, np)) :
  Forall last_inst_terminator np.
Proof.
  unfold uslh_blk in USLH. des_ifs_safe.
  eapply bind_inv in USLH. des. subst. unfold concatM in USLH.
  eapply bind_inv in USLH. des. subst. ss. unfold MiniCET.uslh_ret in *. clarify.
  assert (Forall last_inst_terminator pm0).
  { clear -USLH. unfold add_index_uslh in *.
    assert (Datatypes.length (_offset_uslh l (if b then 2 else 0)) = Datatypes.length l).
    { eapply _offset_uslh_length. }
    remember (_offset_uslh l (if b then 2 else 0)) as ll. clear Heqll.
    ginduction l; ii.
    - destruct ll; ss. unfold mapM in USLH. ss. unfold MiniCET.uslh_ret in USLH. clarify.
    - destruct ll; ss. eapply mapM_cons_inv in USLH. des. subst.
      exploit IHl; try eapply USLH0; eauto. i.
      assert (Forall last_inst_terminator np_hd).
      { eapply uslh_inst_newp_terminator; eauto. }
      rewrite Forall_app. split; eauto. }
  rewrite app_nil_r. rewrite Forall_app. split; auto. des_ifs; ss.
Qed.

Lemma new_prog_last_terminator p c p' np
  (USLH: mapM uslh_blk (add_index p) c = (p', np)) :
  Forall last_inst_terminator np.
Proof.
  unfold add_index in USLH. remember 0 in USLH. clear Heqn.
  ginduction p; ss; ii.
  - unfold mapM in USLH. ss. unfold MiniCET.uslh_ret in USLH. clarify.
  - exploit mapM_cons_inv; eauto. i. des. subst.
    exploit IHp; eauto. i.
    assert (Forall last_inst_terminator np_hd).
    { eapply uslh_blk_np_last_terminator; eauto. }
    rewrite Forall_app. split; eauto.
Qed.

Lemma uslh_prog_last_inst_terminator p
  (WFP: wf_prog p) :
  Forall last_inst_terminator (uslh_prog p).
Proof.
  unfold uslh_prog. des_ifs_safe.
  rewrite Forall_app. split.
  - (* transformed blocks p' *)
    exploit mapM_perserve_len; eauto. intros LEN. rewrite length_add_index in LEN.
    rewrite Forall_forall. intros blk IN.
    eapply In_nth_error in IN. des.
    assert (NLT: n < Datatypes.length p).
    { assert (nth_error l n <> None) by (rewrite IN; discriminate).
      rewrite nth_error_Some in H. lia. }
    assert (exists src, nth_error p n = Some src) as [src SRC].
    { destruct (nth_error p n) eqn:E; [eauto|].
      exfalso. rewrite nth_error_None in E. lia. }
    exploit nth_error_add_index; eauto. intros AI.
    exploit mapM_nth_error; try eapply Heq; try eapply AI.
    intros (blk' & c' & np' & NTH' & USLH').
    rewrite NTH' in IN. clarify.
    assert (WFB: wf_block p src).
    { inv WFP. rewrite Forall_forall in H0.
      eapply nth_error_In in SRC. eapply H0 in SRC. auto. }
    red in WFB. des.
    eapply uslh_blk_last_terminator_res; eauto.
  - (* new blocks *)
    eapply new_prog_last_terminator; eauto.
Qed.

Lemma uslh_prog_nonempty_aux p
  (WFP: nonempty_program p) :
  nonempty_program (uslh_prog p).
Proof.
  destruct p.
  { i. red in WFP. ss; lia. }
  i. unfold uslh_prog. des_ifs. ss.
  unfold add_index in Heq. ss. eapply mapM_cons_inv in Heq.
  des. ss. des_ifs_safe. simpl. red. ss. lia.
Qed.

Lemma uslh_prog_nonempty p
  (WFP: wf_prog p) :
  nonempty_program (uslh_prog p).
Proof.
  eapply uslh_prog_nonempty_aux. red in WFP.
  des. eauto.
Qed.

Lemma uslh_prog_nonempty_blk_aux p
  (WFP: Forall nonempty_block p) :
  Forall nonempty_block (uslh_prog p).
Proof.
  unfold uslh_prog. des_ifs_safe.
  rewrite Forall_app. split.
  - remember (Datatypes.length p). clear Heqn.
    unfold add_index in Heq. remember 0 in Heq. clear Heqn0.
    ginduction p; ss; ii.
    { unfold mapM in Heq. ss.
      unfold MiniCET.uslh_ret in *. clarify. }
    exploit mapM_cons_inv; eauto. i. des. subst.
    exploit IHp; eauto; i.
    { inv WFP. eauto. }
    econs; eauto.
    inv WFP. clear - H1 x0.
    eapply uslh_blk_nonempty_res in x0; eauto.
  - remember (Datatypes.length p). clear Heqn.
    unfold add_index in Heq. remember 0 in Heq. clear Heqn0.
    ginduction p; ss; ii.
    { unfold mapM in Heq. ss.
      unfold MiniCET.uslh_ret in *. clarify. }
    exploit mapM_cons_inv; eauto. i. des. subst.
    exploit IHp; eauto; i.
    { inv WFP; eauto. }
    eapply uslh_blk_np_nonempty in x0.
    rewrite Forall_app. split; auto.
Qed.

Lemma uslh_prog_nonempty_blk p
  (WFP: wf_prog p) :
  Forall nonempty_block (uslh_prog p).
Proof.
  eapply uslh_prog_nonempty_blk_aux. red in WFP.
  des. unfold wf_block in WFP0.
  eapply Forall_and_inv in WFP0. des. eauto.
Qed.

Lemma fetch_inv tp len pc i
  (FETCH: fetch tp len pc = Some i) :
  len <= pc /\ nth_error tp (pc - len) = Some i.
Proof.
  unfold fetch, MoreLinear.fetch in FETCH.
  destruct (pc <? len)%nat eqn:LT; [discriminate|].
  rewrite ltb_ge in LT. auto.
Qed.

Lemma wf_ret_exists p tp ttp len pc
  (WFP: wf_prog p)
  (USLH: tp = uslh_prog p)
  (MC: machine_prog tp len = Some ttp)
  (WFR: wf_ret ttp len pc) :
  fetch ttp len pc <> None.
Proof.
  red in WFR. des. exploit fetch_inv; eauto. intros (_ & NTH).
  unfold fetch, MoreLinear.fetch.
  destruct (pc <? len)%nat eqn:LT; [rewrite ltb_lt in LT; lia|].
  replace (pc - len) with (S (pc - 1 - len)) by lia.
  subst tp.
  exploit _machine_prog_call_has_next.
  { unfold machine_prog in MC. eauto. }
  { eapply uslh_prog_last_inst_terminator. auto. }
  { eauto. }
  i. des. rewrite x0. discriminate.
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
  (TGT: fetch tp len l = Some ti)
  (INJ: pc_inj p len pc = Some l) :
  exists i, p[[pc]] = Some i /\ machine_inst p len i = Some ti.
Proof.
  exploit fetch_inv; eauto. intros (_ & NTH).
  eapply tgt_inv_aux; eauto.
Qed.

Lemma src_inv_aux
  (p p_ctx: MiniCET.prog) len (tp: prog) pc l i
  (TRANSL: _machine_prog p_ctx p len = Some tp)
  (SRC: p[[pc]] = Some i)
  (INJ: pc_inj p len pc = Some l) :
  exists ti, nth_error tp (l - len) = Some ti /\ machine_inst p_ctx len i = Some ti.
Proof.
  ginduction p; ii.
  { ii. unfold _machine_prog in TRANSL. ss. clarify.
    destruct pc0; ss. }
  unfold _machine_prog in TRANSL. simpl in TRANSL. des_ifs_safe.
  simpl in SRC. destruct pc0 as [b o]. destruct a as [blk ct].
  destruct b as [|b].
  { ss. unfold pc_inj in INJ. simpl in INJ.
    des_ifs_safe. rewrite ltb_lt in Heq2.
    replace (n + len - len) with n by lia.
    exploit machine_blk_len; eauto. i. rewrite x0 in Heq2.
    rewrite nth_error_app1; [|lia].
    exploit machine_blk_inv_src; eauto. }
  replace (((blk, ct) :: p) [[(S b, o)]]) with p[[(b, o)]] by ss.
  unfold pc_inj in INJ. simpl in INJ. des_ifs_safe.
  assert (Datatypes.length blk + n0 + len - len = Datatypes.length blk + n0) by lia.
  rewrite H. clear H.
  exploit machine_blk_len; eauto. i. rewrite x0. ss.
  rewrite nth_error_app2; [|lia].
  rewrite add_comm, add_sub.
  exploit IHp.
  { unfold _machine_prog. erewrite Heq1. eauto. }
  { instantiate (2:= (b, o)). ss. eauto. }
  { unfold pc_inj. erewrite Heq2. eauto. }
  replace(n0 + len - len) with n0 by lia. eauto.
Qed.

Lemma pc_inj_ge p len pc n
  (INJ: pc_inj p len pc = Some n) :
  len <= n.
Proof. unfold pc_inj in INJ. des_ifs. lia. Qed.

Lemma src_inv
  (p: MiniCET.prog) len (tp: prog) pc l i
  (TRANSL: machine_prog p len = Some tp)
  (SRC: p[[pc]] = Some i)
  (INJ: pc_inj p len pc = Some l) :
  exists ti, fetch tp len l = Some ti /\ machine_inst p len i = Some ti.
Proof.
  exploit src_inv_aux; eauto. intros (ti & NTH & MI).
  exists ti. split; [|exact MI].
  exploit pc_inj_ge; eauto. intros GE.
  unfold fetch, MoreLinear.fetch.
  destruct (l <? len)%nat eqn:LT; [rewrite ltb_lt in LT; lia|]. exact NTH.
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

Lemma coord_to_flat_idx_out {X} (ll: list (list X)) b :
  coord_to_flat_idx ll (Datatypes.length ll, b) = None.
Proof. induction ll; ss. rewrite IHll. auto. Qed.

Lemma pc_inj_out p len :
  pc_inj p len (Datatypes.length p, 0) = None.
Proof.
  unfold pc_inj. replace (Datatypes.length p) with (Datatypes.length (map fst p)) by apply length_map.
  rewrite coord_to_flat_idx_out. auto.
Qed.

Lemma fetch_out (p: MiniCET.prog) :
  p[[(Datatypes.length p, 0)]] = None.
Proof. simpl. rewrite (proj2 (nth_error_None p (Datatypes.length p)) (le_n _)). auto. Qed.

Lemma pc_inj_init p len
  (INIT: p[[(0, 0)]] <> None) :
  pc_inj p len (0, 0) = Some len.
Proof.
  destruct p as [|[blk b] p]; [exfalso; apply INIT; reflexivity|].
  destruct blk; [exfalso; apply INIT; reflexivity|]. reflexivity.
Qed.

Lemma pc_of_inj p len pc n
  (INJ: pc_inj p len pc = Some n) :
  pc_of p len n = pc.
Proof.
  exploit pc_inj_ge; eauto. intros GE.
  unfold pc_of. destruct (n <? len)%nat eqn:LT; [rewrite ltb_lt in LT; lia|].
  rewrite (proj1 (pc_inj_iff p len pc n GE) INJ). auto.
Qed.

Lemma pc_of_spec p len n k
  (INJ: pc_inj p len (pc_of p len n) = Some k) :
  k = n.
Proof.
  unfold pc_of in INJ. destruct (n <? len)%nat eqn:LT.
  { rewrite pc_inj_out in INJ. discriminate. }
  destruct (pc_inj_inv p len n) as [pc|] eqn:INV.
  - rewrite ltb_ge in LT. rewrite <- pc_inj_iff in INV; [|lia]. congruence.
  - rewrite pc_inj_out in INJ. discriminate.
Qed.

Lemma pc_of_valid p len n
  (VALID: p[[pc_of p len n]] <> None) :
  pc_inj p len (pc_of p len n) = Some n.
Proof.
  unfold pc_of in *. destruct (n <? len)%nat eqn:LT.
  { exfalso. apply VALID. apply fetch_out. }
  destruct (pc_inj_inv p len n) as [pc|] eqn:INV.
  - rewrite ltb_ge in LT. rewrite pc_inj_iff; [exact INV|lia].
  - exfalso. apply VALID. apply fetch_out.
Qed.

Lemma pc_of_eq_iff p len n l0 l
  (INJ: pc_inj p len l0 = Some l) :
  pc_of p len n = l0 <-> n = l.
Proof.
  split; intros EQ.
  - subst l0. exploit pc_of_spec; eauto.
  - subst n. eapply pc_of_inj; eauto.
Qed.

Lemma pc_of_eqb_l p len n l0 l
  (INJ: pc_inj p len l0 = Some l) :
  ((fst (pc_of p len n) =? fst l0) && (snd (pc_of p len n) =? snd l0))%nat = (n =? l)%nat.
Proof.
  destruct ((fst (pc_of p len n) =? fst l0) && (snd (pc_of p len n) =? snd l0))%nat eqn:E;
  destruct (n =? l)%nat eqn:E'; auto; exfalso.
  - rewrite cptr_eqb_spec in E. rewrite (pc_of_eq_iff _ _ _ _ _ INJ) in E.
    rewrite Nat.eqb_neq in E'. auto.
  - rewrite Nat.eqb_eq in E'. rewrite <- (pc_of_eq_iff _ _ _ _ _ INJ) in E'.
    rewrite <- cptr_eqb_spec in E'. congruence.
Qed.

Lemma pc_of_eqb_r p len n l0 l
  (INJ: pc_inj p len l0 = Some l) :
  ((fst l0 =? fst (pc_of p len n)) && (snd l0 =? snd (pc_of p len n)))%nat = (l =? n)%nat.
Proof.
  rewrite (Nat.eqb_sym (fst l0)), (Nat.eqb_sym (snd l0)), (Nat.eqb_sym l).
  eapply pc_of_eqb_l; eauto.
Qed.

Lemma wf_ret_pc_of p len tp n
  (TRANSL: machine_prog p len = Some tp)
  (WFP: Forall MiniCET_Index.last_inst_terminator p)
  (WFR: wf_ret tp len n) :
  MiniCET_Index.wf_ret p (pc_of p len n) /\ pc_inj p len (pc_of p len n) = Some n.
Proof.
  red in WFR. des.
  exploit fetch_inv; eauto. intros (_ & NTH).
  exploit lookup_from_target; [|unfold machine_prog in TRANSL; eauto|eauto|]; [lia|].
  intros (pc_call & INJ_CALL).
  exploit tgt_inv; eauto. intros (i_call & ISRC_CALL & MINST_CALL).
  unfold machine_inst in MINST_CALL. destruct i_call; ss; clarify; try des_ifs.
  exploit MiniCET_Index.block_always_terminator_prog_aux; [exact WFP|exact ISRC_CALL|intros X; exact X|].
  intros (i_next & INXT).
  exploit pc_inj_inc; eauto.
  { intro H_nxt. rewrite H_nxt in INXT. discriminate. }
  replace (add (n - 1) 1) with n by lia. intros INJ_RET.
  rewrite (pc_of_inj _ _ _ _ INJ_RET). split; [|auto].
  destruct pc_call as [lc oc].
  unfold MiniCET_Index.wf_ret. simpl. split.
  - unfold MiniCET.inc in INXT. simpl in INXT. rewrite INXT. discriminate.
  - exists fp. split.
    + replace (Nat.sub (Nat.add oc 1) 1) with oc by lia. exact ISRC_CALL.
    + lia.
Qed.

Lemma match_states_ct p tp len n spc r m sb ms r' m' sb'
  (TRANSL: machine_prog p len = Some tp)
  (SPC: pc_of p len n = spc)
  (MLEN: len = mem_length m')
  (REG: match_reg p len r r')
  (MEM: match_mem p len m m')
  (SMEM: match_smem p len sb sb') :
  match_states p tp len (S_Running (spc, r, m, sb, true, ms)) (S_Running (n, r', m', sb', true, ms)).
Proof.
  subst spc.
  assert (TCT: fetch tp len n = Some ICTarget -> p[[pc_of p len n]] = Some ICTarget).
  { intros F. exploit fetch_inv; eauto. intros (GE & NTH).
    exploit lookup_from_target; [exact GE|unfold machine_prog in TRANSL; exact TRANSL|exact NTH|].
    intros (pc & INJ). rewrite (pc_of_inj _ _ _ _ INJ).
    exploit tgt_inv; [exact TRANSL|exact F|exact INJ|]. intros (i & SRC & MI).
    rewrite SRC. destruct i; ss; des_ifs. }
  destruct (p[[pc_of p len n]]) as [i|] eqn:SRC; [destruct i|].
  all: try (eapply match_states_call_fault;
            [|intros F; apply TCT in F; congruence|exact MLEN|exact REG|exact MEM|exact SMEM];
            congruence).
  exploit pc_of_valid; [rewrite SRC; discriminate|]. intros INJ.
  exploit src_inv; eauto. intros (ti & F & MI). ss. clarify.
  eapply match_states_call; eauto.
Qed.

Lemma mirror_fold_lookup (l: list val) k (sb: MCC.spec_mem) n :
  (fold_left (fun sb '(i, v) => (i !-> v; sb)) (combine (seq k (Datatypes.length l)) l) sb) ! n =
  if (n <? k)%nat then sb ! n
  else match nth_error l (n - k) with Some v => v | None => sb ! n end.
Proof.
  revert k sb. induction l as [|a l IH]; intros k sb; simpl.
  - destruct (n <? k)%nat; auto. destruct (n - k); auto.
  - rewrite IH.
    destruct (Nat.lt_trichotomy n k) as [HLT|[HEQ|HGT] ].
    + assert (L1: (n <? S k)%nat = true) by (rewrite ltb_lt; lia).
      assert (L2: (n <? k)%nat = true) by (rewrite ltb_lt; lia).
      rewrite L1, L2. rewrite MiniCET_Index.t_update_neq; auto. lia.
    + subst. assert (L1: (k <? S k)%nat = true) by (rewrite ltb_lt; lia).
      rewrite L1, ltb_irrefl, sub_diag. simpl. rewrite MiniCET_Index.t_update_eq. auto.
    + assert (L1: (n <? S k)%nat = false) by (rewrite ltb_ge; lia).
      assert (L2: (n <? k)%nat = false) by (rewrite ltb_ge; lia).
      rewrite L1, L2. replace (n - k) with (S (n - S k)) by lia. simpl.
      destruct (nth_error l (n - S k)); auto.
      rewrite MiniCET_Index.t_update_neq; auto. lia.
Qed.

Lemma mirror_mem_lookup m n :
  (mirror_mem m) ! n = match nth_error m.(memory) n with Some v => v | None => UV end.
Proof.
  unfold mirror_mem, add_index. rewrite mirror_fold_lookup. simpl.
  rewrite sub_0_r. destruct (nth_error (memory m) n); auto.
Qed.

Lemma match_smem_mirror p len m m'
  (MEM: match_mem p len m m') :
  match_smem p len (mirror_mem m) (mirror_mem m').
Proof.
  destruct MEM as [MEM _]. intros n. rewrite !mirror_mem_lookup.
  specialize (MEM n). des_ifs; ss.
Qed.

Lemma mem_length_upd n m v :
  mem_length (upd_mem n m v) = mem_length m.
Proof. unfold mem_length, upd_mem. simpl. apply upd_length. Qed.

Lemma mem_inject p len m m' n v v'
  (MEM: match_mem p len m m')
  (SRC: nth_error m.(memory) n = Some v)
  (TGT: nth_error m'.(memory) n = Some v') :
  val_inject p len v v'.
Proof. destruct MEM as [MEM _]. specialize (MEM n). rewrite SRC, TGT in MEM. exact MEM. Qed.

Lemma val_inject_fp_n p len l n
  (VI: val_inject p len (FP l) (N n)) :
  pc_inj p len l = Some n.
Proof. simpl in VI. des_ifs. Qed.

Lemma match_reg_N p len r r' x n
  (REG: match_reg p len r r')
  (SRC: r ! x = N n) :
  r' ! x = N n.
Proof.
  specialize (REG x). rewrite SRC in REG.
  destruct (r' ! x); ss; subst; auto.
Qed.

Lemma eval_inject_nat p len r r' e e' n
  (REG: match_reg p len r r')
  (TRANS: machine_exp p len e = Some e')
  (SRC: to_nat (MCC.eval r e) = Some n) :
  to_nat (eval r' e') = Some n.
Proof.
  exploit eval_inject; eauto. intros VI.
  destruct (MCC.eval r e); ss; clarify.
  destruct (eval r' e'); ss; subst; auto.
Qed.

Lemma eval_inject_fp p len r r' e e' l0 l
  (REG: match_reg p len r r')
  (TRANS: machine_exp p len e = Some e')
  (SRC: to_fp (MCC.eval r e) = Some l0)
  (TGT: to_nat (eval r' e') = Some l) :
  pc_inj p len l0 = Some l.
Proof.
  exploit eval_inject; eauto. intros VI.
  destruct (MCC.eval r e); ss; clarify.
  destruct (eval r' e'); ss; clarify.
  eapply val_inject_fp_n; eauto.
Qed.

Lemma src_div_inv p pc r m sb ms x e1 e2 ds os st
  (INST: p[[pc]] = Some <{{ x <- div e1, e2 }}>)
  (STEP: p |- <(( S_Running ((pc, r, m), sb, false, ms) ))> -->_ ds ^^ os <(( st ))>) :
  exists n1 n2, to_nat (MCC.eval r e1) = Some n1 /\ to_nat (MCC.eval r e2) = Some n2.
Proof. inv STEP; clarify; esplits; eauto. Qed.

Lemma src_branch_inv p pc r m sb ms e l ds os st
  (INST: p[[pc]] = Some <{{ branch e to l }}>)
  (STEP: p |- <(( S_Running ((pc, r, m), sb, false, ms) ))> -->_ ds ^^ os <(( st ))>) :
  exists n, to_nat (MCC.eval r e) = Some n.
Proof. inv STEP; clarify; esplits; eauto. Qed.

Lemma src_load_inv p pc r m sb x e ds os st
  (INST: p[[pc]] = Some <{{ x <- load[e] }}>)
  (STEP: p |- <(( S_Running ((pc, r, m), sb, false, false) ))> -->_ ds ^^ os <(( st ))>) :
  exists n v, to_nat (MCC.eval r e) = Some n /\ nth_error m.(memory) n = Some v.
Proof. inv STEP; clarify; esplits; eauto. Qed.

Lemma src_load_misspec_inv p pc r m sb x e ds os st
  (INST: p[[pc]] = Some <{{ x <- load[e] }}>)
  (STEP: p |- <(( S_Running ((pc, r, m), sb, false, true) ))> -->_ ds ^^ os <(( st ))>) :
  exists n, to_nat (MCC.eval r e) = Some n.
Proof. inv STEP; clarify; esplits; eauto. Qed.

Lemma src_store_inv p pc r m sb ms e e' ds os st
  (INST: p[[pc]] = Some <{{ store[e] <- e' }}>)
  (STEP: p |- <(( S_Running ((pc, r, m), sb, false, ms) ))> -->_ ds ^^ os <(( st ))>) :
  exists n, to_nat (MCC.eval r e) = Some n.
Proof. inv STEP; clarify; esplits; eauto. Qed.

Lemma src_call_inv p pc r m sb e ds os st
  (INST: p[[pc]] = Some <{{ call e }}>)
  (STEP: p |- <(( S_Running ((pc, r, m), sb, false, false) ))> -->_ ds ^^ os <(( st ))>) :
  exists l spv, to_fp (MCC.eval r e) = Some l /\ r ! sp = N spv /\ S spv < stack_top m.
Proof. inv STEP; clarify; esplits; eauto. Qed.

Lemma src_call_misspec_inv p pc r m sb e ds os st
  (INST: p[[pc]] = Some <{{ call e }}>)
  (STEP: p |- <(( S_Running ((pc, r, m), sb, false, true) ))> -->_ ds ^^ os <(( st ))>) :
  exists l spv, to_fp (MCC.eval r e) = Some l /\ r ! sp = N spv.
Proof. inv STEP; clarify; esplits; eauto. Qed.

Lemma src_ret_inv p pc r m sb ds os st
  (INST: p[[pc]] = Some <{{ ret }}>)
  (STEP: p |- <(( S_Running ((pc, r, m), sb, false, false) ))> -->_ ds ^^ os <(( st ))>) :
  exists spv pc', r ! sp = N spv /\ spv < stack_top m /\ nth_error m.(memory) spv = Some (FP pc').
Proof. inv STEP; clarify; esplits; eauto. Qed.

Lemma src_ret_misspec_inv p pc r m sb ds os st
  (INST: p[[pc]] = Some <{{ ret }}>)
  (STEP: p |- <(( S_Running ((pc, r, m), sb, false, true) ))> -->_ ds ^^ os <(( st ))>) :
  exists spv pc', r ! sp = N spv /\ sb ! spv = FP pc'.
Proof. inv STEP; clarify; esplits; eauto. Qed.

Lemma minicet_linear_bcc_single
  (p: MiniCET.prog) len (tp: prog) sc tc tct tds tos
  (TRANSL: machine_prog p len = Some tp)
  (WFP: Forall MiniCET_Index.last_inst_terminator p)
  (SAFE: exists ds os sct, p |- <(( S_Running sc ))> -->_ ds ^^ os  <(( sct ))>)
  (MATCH: match_states p tp len (S_Running sc) (S_Running tc))
  (TGT: tp |- <(( S_Running tc ))> -->m_ tds ^^ tos  <(( tct ))>) :
  exists os sct, p |- <(( S_Running sc ))> -->_ (lin_Tdir p len tds) ^^ os  <(( sct ))>
             /\ match_states p tp len sct tct
             /\ tos = lin_Tobs p len os.
Proof.
  unfold lin_Tdir, lin_Tobs.
  inv MATCH; cycle 1.
  (* fault *)
  { inv TGT; try congruence.
    esplits; [eapply MiniCET_Index.SpecSMI_Fault; eauto|econs|reflexivity]. }
  (* call *)
  { inv TGT; try congruence.
    esplits.
    - eapply MiniCET_Index.SpecSMI_CTarget; eauto.
    - econs; eauto. i. exploit pc_inj_inc; try eapply SYNC; eauto.
    - reflexivity. }
  destruct (p[[pc0]]) eqn:ISRC.
  2:{ des. inv SAFE; clarify. }
  exploit PC; [ii; clarify|]. clear PC. intros PC.
  des. inv TGT.
  (* skip *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    esplits.
    + eapply MiniCET_Index.SpecSMI_Skip; eauto.
    + econs; eauto. i. exploit pc_inj_inc; eauto.
    + reflexivity.
  (* asgn *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    esplits.
    + eapply MiniCET_Index.SpecSMI_Asgn; eauto.
    + econs; [i; exploit pc_inj_inc; eauto|reflexivity| |exact MEM|exact SMEM].
      eapply asgn_match_reg; eauto. eapply eval_inject; eauto.
    + reflexivity.
  (* div *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    exploit src_div_inv; eauto. intros (n1 & n2 & EV1 & EV2).
    exploit (eval_inject_nat p (mem_length m') r r' e0 e1); eauto. intros TEV1.
    exploit (eval_inject_nat p (mem_length m') r r' e3 e2); eauto. intros TEV2.
    rewrite TEV1, TEV2 in *. clarify.
    esplits.
    + eapply MiniCET_Index.SpecSMI_Div; eauto.
    + econs; [i; exploit pc_inj_inc; eauto|reflexivity| |exact MEM|exact SMEM].
      eapply asgn_match_reg; eauto. des_ifs; ss.
    + reflexivity.
  (* branch *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    all: exploit src_branch_inv; eauto; intros (n0 & EV).
    all: exploit eval_inject_nat; eauto; intros TEV.
    all: rewrite TEV in *; clarify.
    all: esplits; [eapply MiniCET_Index.SpecSMI_Branch; eauto
                  |econs; [|reflexivity|exact REG|exact MEM|exact SMEM]
                  |reflexivity].
    all: first [intros _; eauto; fail | i; eapply pc_inj_inc; eauto].
  (* jump *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    esplits.
    + eapply MiniCET_Index.SpecSMI_Jump; eauto.
    + econs; eauto.
    + reflexivity.
  (* load *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    exploit src_load_inv; eauto. intros (n0 & v & EV & NTH).
    exploit eval_inject_nat; eauto. intros TEV.
    rewrite TEV in *. clarify.
    exploit mem_inject; eauto. intros VI.
    esplits.
    + eapply MiniCET_Index.SpecSMI_Load; eauto.
    + econs; [i; exploit pc_inj_inc; eauto|reflexivity| |exact MEM|exact SMEM].
      eapply asgn_match_reg; eauto.
    + reflexivity.
  (* load misspec *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    exploit src_load_misspec_inv; eauto. intros (n0 & EV).
    exploit eval_inject_nat; eauto. intros TEV.
    rewrite TEV in *. clarify.
    esplits.
    + eapply MiniCET_Index.SpecSMI_Load_Misspec; eauto.
    + econs; [i; exploit pc_inj_inc; eauto|reflexivity| |exact MEM|exact SMEM].
      eapply asgn_match_reg; eauto.
    + reflexivity.
  (* store *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    exploit src_store_inv; eauto. intros (n0 & EV).
    match goal with H: machine_exp _ _ ?a = Some _, E: to_nat (MCC.eval _ ?a) = Some _ |- _ =>
      pose proof (eval_inject_nat _ _ _ _ _ _ _ REG H E) as TEV end.
    rewrite TEV in *. clarify.
    match goal with H: machine_exp _ _ _ = Some e' |- _ =>
      pose proof (eval_inject _ _ _ _ _ _ REG H) as VI end.
    esplits.
    + eapply MiniCET_Index.SpecSMI_Store; eauto.
    + econs; [i; exploit pc_inj_inc; eauto| |exact REG| |].
      * rewrite mem_length_upd. auto.
      * eapply store_match_mem; eauto.
      * eapply store_match_smem; eauto.
    + reflexivity.
  (* store misspec *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    exploit src_store_inv; eauto. intros (n0 & EV).
    match goal with H: machine_exp _ _ ?a = Some _, E: to_nat (MCC.eval _ ?a) = Some _ |- _ =>
      pose proof (eval_inject_nat _ _ _ _ _ _ _ REG H E) as TEV end.
    rewrite TEV in *. clarify.
    match goal with H: machine_exp _ _ _ = Some e' |- _ =>
      pose proof (eval_inject _ _ _ _ _ _ REG H) as VI end.
    esplits.
    + eapply MiniCET_Index.SpecSMI_Store_Misspec; eauto.
    + econs; [i; exploit pc_inj_inc; eauto|reflexivity|exact REG|exact MEM|].
      eapply store_match_smem; eauto.
    + reflexivity.
  (* call *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    exploit src_call_inv; eauto. intros (l0 & spv & EFP & SP & TOP).
    exploit eval_inject_fp; eauto. intros INJL.
    exploit match_reg_N; eauto. intros TSP. rewrite TSP in *. clarify.
    exploit MiniCET_Index.block_always_terminator_prog_aux; [exact WFP|exact ISRC|intros X; exact X|].
    intros (i_next & INXT).
    exploit (pc_inj_inc p (mem_length m') pc0 pc' PC); [rewrite INXT; discriminate|]. intros RA.
    erewrite <- pc_of_eqb_l; [|exact INJL].
    esplits.
    + eapply MiniCET_Index.SpecSMI_Call; eauto.
    + eapply match_states_ct; eauto.
      * rewrite mem_length_upd. auto.
      * eapply asgn_match_reg; eauto. ss.
      * eapply store_match_mem; eauto. ss. rewrite RA. auto.
      * eapply store_match_smem; eauto. ss. rewrite RA. auto.
    + ss. unfold inj_pc. rewrite INJL. reflexivity.
  (* call misspec *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    exploit src_call_misspec_inv; eauto. intros (l0 & spv & EFP & SP).
    exploit eval_inject_fp; eauto. intros INJL.
    exploit match_reg_N; eauto. intros TSP. rewrite TSP in *. clarify.
    exploit MiniCET_Index.block_always_terminator_prog_aux; [exact WFP|exact ISRC|intros X; exact X|].
    intros (i_next & INXT).
    exploit (pc_inj_inc p (mem_length m') pc0 pc' PC); [rewrite INXT; discriminate|]. intros RA.
    esplits.
    + eapply MiniCET_Index.SpecSMI_Call_Misspec; eauto.
    + eapply match_states_ct; eauto.
      * eapply asgn_match_reg; eauto. ss.
      * eapply store_match_smem; eauto. ss. rewrite RA. auto.
    + ss. unfold inj_pc. rewrite INJL. reflexivity.
  (* ret dir *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    exploit src_ret_inv; eauto. intros (spv & pcs & SP & TOP & NTH).
    exploit match_reg_N; eauto. intros TSP. rewrite TSP in *. clarify.
    exploit mem_inject; eauto. intros VI. eapply val_inject_fp_n in VI.
    exploit wf_ret_pc_of; eauto. intros (WFRS & INJD).
    erewrite <- pc_of_eqb_r; [|exact VI].
    esplits.
    + eapply MiniCET_Index.SpecSMI_Ret_Dir; eauto.
    + econs; [intros _; exact INJD|reflexivity| |exact MEM|exact SMEM].
      eapply asgn_match_reg; eauto. ss.
    + ss. unfold inj_pc. rewrite VI. reflexivity.
  (* ret step *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    exploit src_ret_inv; eauto. intros (spv & pcs & SP & TOP & NTH).
    exploit match_reg_N; eauto. intros TSP. rewrite TSP in *. clarify.
    exploit mem_inject; eauto. intros VI. eapply val_inject_fp_n in VI.
    esplits.
    + eapply MiniCET_Index.SpecSMI_Ret_Step; eauto.
    + econs; [intros _; exact VI|reflexivity| |exact MEM|exact SMEM].
      eapply asgn_match_reg; eauto. ss.
    + ss. unfold inj_pc. rewrite VI. reflexivity.
  (* ret misspec dir *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    exploit src_ret_misspec_inv; eauto. intros (spv & pcs & SP & SLOT).
    exploit match_reg_N; eauto. intros TSP. rewrite TSP in *. clarify.
    match goal with S: sb ! ?k = FP _, T: sb' ! ?k = N _ |- _ =>
      pose proof (SMEM k) as VI; rewrite S, T in VI end.
    eapply val_inject_fp_n in VI.
    exploit wf_ret_pc_of; eauto. intros (WFRS & INJD).
    esplits.
    + eapply MiniCET_Index.SpecSMI_Ret_Misspec_Dir; eauto.
    + econs; [intros _; exact INJD|reflexivity| |exact MEM|exact SMEM].
      eapply asgn_match_reg; eauto. ss.
    + ss. unfold inj_pc. rewrite VI. reflexivity.
  (* ret misspec step *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    exploit src_ret_misspec_inv; eauto. intros (spv & pcs & SP & SLOT).
    exploit match_reg_N; eauto. intros TSP. rewrite TSP in *. clarify.
    match goal with S: sb ! ?k = FP _, T: sb' ! ?k = N _ |- _ =>
      pose proof (SMEM k) as VI; rewrite S, T in VI end.
    eapply val_inject_fp_n in VI.
    esplits.
    + eapply MiniCET_Index.SpecSMI_Ret_Misspec_Step; eauto.
    + econs; [intros _; exact VI|reflexivity| |exact MEM|exact SMEM].
      eapply asgn_match_reg; eauto. ss.
    + ss. unfold inj_pc. rewrite VI. reflexivity.
  (* term *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    esplits.
    + eapply MiniCET_Index.SpecSMI_Term; eauto.
    + econs.
    + reflexivity.
  (* ctarget *)
  - exploit tgt_inv; eauto. intros (i0 & SRC & MI). rewrite ISRC in SRC. inv SRC.
    unfold machine_inst in MI. des_ifs.
    esplits.
    + eapply MiniCET_Index.SpecSMI_CTarget; eauto.
    + econs; eauto. i. exploit pc_inj_inc; eauto.
    + reflexivity.
Qed.

Lemma tctrl_lin_step tp len tpc r m sb tct ms ds os t'
  (LEN: len = mem_length m)
  (STEP: tp |- <(( S_Running ((tpc, r, m), sb, tct, ms) ))> -->m_ ds ^^ os <(( t' ))>) :
  lin_step tp len (Some {| pc := tpc; ct := tct |}) ds os = tctrl_lin t'.
Proof.
  subst len. inv STEP; unfold lin_step, tctrl_lin; cbn [pc ct].
  all: try (match goal with H: fetch _ _ _ = Some _ |- _ => rewrite H end; try destruct tct; reflexivity).
  destruct (fetch tp (mem_length m) tpc) as [ [] |]; auto. congruence.
Qed.

Lemma lin_step_shape tp pc r1 m1 sb1 ct ms1 r2 m2 sb2 ms2 st1' st2' ds1 ds2 os1 os2
  (LEN: mem_length m1 = mem_length m2)
  (S1: tp |- <(( S_Running ((pc, r1, m1), sb1, ct, ms1) ))> -->m_ ds1 ^^ os1 <(( st1' ))>)
  (S2: tp |- <(( S_Running ((pc, r2, m2), sb2, ct, ms2) ))> -->m_ ds2 ^^ os2 <(( st2' ))>) :
  Datatypes.length ds1 = Datatypes.length ds2 /\ Datatypes.length os1 = Datatypes.length os2.
Proof.
  inversion S1; inversion S2; subst; try (split; reflexivity); try rewrite LEN in *; congruence.
Qed.

Lemma lin_safe_step_preserves_sim p tp len
  (TRANSL: machine_prog p len = Some tp)
  (WFP: Forall MiniCET_Index.last_inst_terminator p) :
  safe_step_preserves_sim (Ls := SpecLang) (Lt := LinSpecLang) (hist := lin_hist tp len)
    p tp (lin_sim p tp len) (fun _ ds => lin_Tdir p len ds) (fun _ _ os => lin_Tobs p len os).
Proof.
  intros ds h os_t s t t' [HT MATCH] SAFE STEP.
  destruct t as [tc| | |]; try (inv STEP; fail).
  destruct s as [sc| | |]; try (inv MATCH; fail).
  exploit (SAFE [] [] (S_Running sc)); [apply (sem_refl (L := SpecLang))|]. intros SAFE1.
  exploit minicet_linear_bcc_single; [exact TRANSL|exact WFP|exact SAFE1|exact MATCH|exact STEP|].
  intros (os & sct & SSTEP & MATCH' & OBS).
  exists sct, os. splits.
  - apply (sem_step1 (L := SpecLang)). exact SSTEP.
  - exact OBS.
  - split; [|exact MATCH']. subst h.
    destruct tc as [ [ [ [ [pc r'] m'] sb'] ct] ms].
    assert (LEN: len = mem_length m') by (inv MATCH; auto).
    exact (tctrl_lin_step tp len pc r' m' sb' ct ms ds os_t t' LEN STEP).
Qed.

Lemma minicet_linear_safe_bw_simulation len :
  has_safe_bw_simulation (lin_compiler len) (lin_sync len).
Proof.
  intros p tp (TRANSL & WFP & INIT).
  exists (lin_hist tp len), (lin_sim p tp len),
    (fun _ ds => lin_Tdir p len ds), (fun _ _ os => lin_Tobs p len os).
  splits.
  - intros [r m] [r' m'] (REG & MEM & MLEN). simpl in REG, MEM, MLEN. subst len.
    exploit (pc_inj_init p (mem_length m')); eauto. intros INJ0.
    split; [reflexivity|].
    eapply match_states_ct; eauto.
    + eapply pc_of_inj; eauto.
    + eapply asgn_match_reg; [ss; rewrite INJ0; auto|].
      eapply asgn_match_reg; [ss|exact REG].
    + eapply match_smem_mirror; eauto.
  - eapply lin_safe_step_preserves_sim; eauto.
  - intros h s1 s2 t1 t2 t1' t2' ds1 ds2 os1 os2 [H1 M1] [H2 M2] ST1 ST2 PRE.
    rewrite H1 in H2.
    destruct t1 as [ [ [ [ [ [pc1 r1] m1] sb1] ct1] ms1] | | | ]; try (inv ST1; fail).
    destruct t2 as [ [ [ [ [ [pc2 r2] m2] sb2] ct2] ms2] | | | ]; try (inv ST2; fail);
      simpl in H2; try discriminate.
    inv H2.
    assert (L1: len = mem_length m1) by (inv M1; auto).
    assert (L2: len = mem_length m2) by (inv M2; auto).
    destruct (lin_step_shape tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (eq_trans (eq_sym L1) L2) ST1 ST2) as [LD LO].
    split; [apply prefix_same_length; assumption | exact LO].
  - intros h ds os1 os2 LEN. cbv beta in LEN. unfold lin_Tobs in LEN.
    rewrite !length_map in LEN. exact LEN.
Qed.

Lemma spec_eval_relative_secure_spec_mir_mc p tp len inp1 inp2
  (ISAFE1: sequential_safe (L := SpecLang) p (initial_machine (L := SpecLang) p inp1))
  (ISAFE2: sequential_safe (L := SpecLang) p (initial_machine (L := SpecLang) p inp2)) :
  relative_secure (Ls := SpecLang) (Lt := LinSpecLang) (lin_compiler len) (lin_sync len) p tp inp1 inp2.
Proof.
  eapply (obs_eq_safe_bw_relsec (Ls := SpecLang) (Lt := LinSpecLang) (p_s := p) (p_t := tp)
            (inp1 := inp1) (inp2 := inp2) (minicet_linear_safe_bw_simulation len)); eauto.
Qed.

Definition relative_secure_machine (p:MiniCET.prog) (len:nat) (tp: prog) (trans : MiniCET.prog -> option prog)
  (r1 r2 r1' r2' : reg) (m1 m2 m1' m2' : mem) : Prop :=
  same_obs (L := SeqLang) p (r1, m1) (r2, m2) ->
  match_reg_src p len r1 r1' false -> match_reg_src p len r2 r2' false ->
  match_mem_src p len m1 m1' -> match_mem_src p len m2 m2' ->
  trans (uslh_prog p) = Some tp ->
  same_obs (L := LinSpecLang) tp (r1', m1') (r2', m2').

Definition wf_reg (p:MiniCET.prog) (r: MCC.reg) : Prop :=
  forall x, match r ! x with
       | FP (l, S o) => MiniCET_Index.wf_ret p (l, S o)
       | _ => True
       end.

Definition wf_mem (p:MiniCET.prog) (m: list val) : Prop :=
  forall i, match nth_error m i with
       | Some (FP (l, S o)) => MiniCET_Index.wf_ret p (l, S o)
       | _ => True
       end.

Definition val_sync (p:MiniCET.prog) (v: val) : val :=
  match v with
  | FP (l, S o) => match ret_sync p (l, S o) with
                  | Some pc => FP pc
                  | _ => UV (* unreachable *)
                  end
  | _ => v
  end.

Lemma map_mem_top_valid (f: val -> val) (m: mem) :
  stack_top m <= Datatypes.length (map f m.(memory)).
Proof. rewrite length_map. apply stack_top_valid. Qed.

Definition map_mem (f: val -> val) (m: mem) : mem :=
  {| memory := map f m.(memory)
   ; stack_top := stack_top m
   ; stack_base := stack_base m
   ; stack_top_valid := map_mem_top_valid f m
   ; stack_base_valid := stack_base_valid m |}.

Lemma val_match_sync p v
  (WF: match v with
       | FP (l, S o) => MiniCET_Index.wf_ret p (l, S o)
       | _ => True
       end) :
  val_match p v (val_sync p v).
Proof.
  destruct v; try sfby ss.
  destruct pc0 as [l o]. destruct o; [ss|].
  unfold val_sync. red in WF. des. unfold ret_sync.
  replace (S o - 1) with o in WF0 by lia. rewrite WF0.
  des_ifs.
  2:{ unfold pc_sync in Heq0.
      rewrite nth_error_map in Heq0.
      ss. des_ifs_safe.
      destruct p0. ss. destruct l2; ss. clarify.
      rewrite nth_error_None in Heq3.
      rewrite offset_uslh_length in Heq3.
      rewrite <- nth_error_None in Heq3. clarify. }
  ss. des_ifs_safe. des_ifs.
Qed.

Lemma val_match_functional p v iv1 iv2
  (VM1: val_match p v iv1)
  (VM2: val_match p v iv2) :
  iv1 = iv2.
Proof.
  destruct v; unfold val_match in *; try (sfby des_ifs).
  destruct pc0. des_ifs. des; clarify.
Qed.

Lemma spec_eval_relative_secure_machine
  p r1 r2 r1' r2' m1 m2 m1' m2' tp isp
  (FST: first_blk_call p)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (LEN1: mem_length m1' = mem_length m2')
  (SP1: r1 ! sp = N isp)
  (SP2: r2 ! sp = N isp)
  (CALLEE1: r1' ! callee = N (mem_length m1'))
  (CALLEE2: r2' ! callee = N (mem_length m2'))
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (UNUSED3: unused_prog sp p)
  (WFREG1: wf_reg p r1)
  (WFREG2: wf_reg p r2)
  (WFMEM1: wf_mem p m1.(memory))
  (WFMEM2: wf_mem p m2.(memory))
  (SAFE1: sequential_safe (L := SeqLang) p (initial_machine (L := SeqLang) p (r1, m1)))
  (SAFE2: sequential_safe (L := SeqLang) p (initial_machine (L := SeqLang) p (r2, m2))) :
  relative_secure_machine p (mem_length m1') tp (fun p => machine_prog p (mem_length m1')) r1 r2 r1' r2' m1 m2 m1' m2'.
Proof.
  red; i.
  set (iir1 := fun x => val_sync p (r1 ! x)).
  set (iir2 := fun x => val_sync p (r2 ! x)).
  set (ir1 := (msf !-> N 0; callee !-> (FP (0, 0)); iir1)).
  set (ir2 := (msf !-> N 0; callee !-> (FP (0, 0)); iir2)).

  set (im1 := map_mem (val_sync p) m1).
  set (im2 := map_mem (val_sync p) m2).

  hexploit (spec_eval_relative_secure p r1 r2 m1 m2 isp SAFE1 SAFE2).
  intros REL.

  assert (IREG1: Rsync1 p r1 ir1 false).
  { subst ir1; subst iir1; ss. ii. des.
    all: do 2 (rewrite MiniCET_Index.t_update_neq; eauto).
    all: eapply val_match_sync; eapply WFREG1. }

  assert (IREG2: Rsync1 p r2 ir2 false).
  { subst ir2; subst iir2; ss. ii. des.
    all: do 2 (rewrite MiniCET_Index.t_update_neq; eauto).
    all: eapply val_match_sync; eapply WFREG2. }

  assert (IMEG1: Msync p m1 im1).
  { split; [|reflexivity].
    subst im1; ss. i. rewrite nth_error_map in *.
    des_ifs. unfold option_map in Heq0. clarify.
    eapply val_match_sync. specialize (WFMEM1 i). des_ifs. }

  assert (IMEG2: Msync p m2 im2).
  { split; [|reflexivity].
    subst im2; ss. i. rewrite nth_error_map in *.
    des_ifs. unfold option_map in Heq0. clarify.
    eapply val_match_sync. specialize (WFMEM2 i). des_ifs. }

  assert (ICALLEE1: ir1 ! callee = FP (0, 0)).
  { subst ir1. rewrite MiniCET_Index.t_update_neq; [|ii; clarify].
    rewrite MiniCET_Index.t_update_eq. auto. }
  assert (ICALLEE2: ir2 ! callee = FP (0, 0)).
  { subst ir2. rewrite MiniCET_Index.t_update_neq; [|ii; clarify].
    rewrite MiniCET_Index.t_update_eq. auto. }

  assert (SYNC1: uslh_sync isp p (r1, m1) (ir1, im1)) by (unfold uslh_sync; simpl; splits; eauto).
  assert (SYNC2: uslh_sync isp p (r2, m2) (ir2, im2)) by (unfold uslh_sync; simpl; splits; eauto).

  assert (COMP: uslh_full_compiler p (uslh_prog p)).
  { exists p; [reflexivity|]. red. splits; auto. }

  pose proof (REL (ir1, im1) (ir2, im2) H SYNC1 SYNC2 COMP) as SPEC.

  hexploit seq_spec_safety_preservation_init; try eapply SAFE1; eauto.
  intros ISAFE1.

  hexploit seq_spec_safety_preservation_init; try eapply SAFE2; eauto.
  intros ISAFE2.

  assert (INITSAFE: (uslh_prog p)[[(0,0)]] <> None).
  { clear - WFP.
    hexploit uslh_prog_nonempty; eauto. i.
    hexploit uslh_prog_nonempty_blk; eauto. i.
    remember (uslh_prog p). clear Heqp0. destruct p0.
    { red in H. ss. lia. }
    simpl. destruct p0. destruct l; ss.
    inv H0. red in H3. ss. lia. }

  assert (ISYNC: pc_inj (uslh_prog p) (mem_length m1') (0, 0) = Some (mem_length m1')).
  { eapply pc_inj_init; eauto. }

  assert (LCOMP: lin_compiler (mem_length m1') (uslh_prog p) tp).
  { red. splits; auto. eapply uslh_prog_last_inst_terminator. auto. }

  assert (LSYNC1: lin_sync (mem_length m1') (uslh_prog p) (ir1, im1) (r1', m1')).
  { unfold lin_sync. simpl. splits; [| |reflexivity].
    - subst ir1. subst iir1. red in H0. des. red. i.
      destruct (string_dec x callee).
      { subst. rewrite CALLEE1. ss. rewrite ISYNC. ss. }
      destruct (string_dec x msf).
      { des. subst. rewrite H5. ss. }
      do 2 (rewrite TotalMap.t_update_neq; eauto).
      red. i. ss. hexploit H0; eauto. i. des.
      exploit val_match_sync.
      { eapply (WFREG1 x). }
      i. exploit val_match_functional; [eapply H6|eapply x1|].
      i. subst. clear - H7. ss.
    - subst im1. red in H2. des. split; [|ss].
      red. i. specialize (H2 i). specialize (WFMEM1 i).
      ss. rewrite nth_error_map. des_ifs_safe. simpl in Heq. clarify. des.
      exploit val_match_sync.
      { eapply WFMEM1. }
      i. exploit val_match_functional; [eapply H2|eapply x0|].
      i. subst. ss. }

  assert (LSYNC2: lin_sync (mem_length m1') (uslh_prog p) (ir2, im2) (r2', m2')).
  { unfold lin_sync. simpl. splits; [| |symmetry; exact LEN1].
    - subst ir2. subst iir2. red in H1. des. red. i.
      destruct (string_dec x callee).
      { subst. rewrite CALLEE2. ss. rewrite <- LEN1. rewrite ISYNC. ss. }
      destruct (string_dec x msf).
      { des. subst. rewrite H5. ss. }
      do 2 (rewrite TotalMap.t_update_neq; eauto).
      red. i. ss. hexploit H1; eauto. i. des.
      exploit val_match_sync.
      { eapply (WFREG2 x). }
      i. exploit val_match_functional; [eapply H6|eapply x1|].
      i. subst. clear - H7. ss.
    - subst im2. red in H3. des. split; [|ss].
      red. i. specialize (H3 i). specialize (WFMEM2 i).
      ss. rewrite nth_error_map. des_ifs_safe. simpl in Heq. clarify. des.
      exploit val_match_sync.
      { eapply WFMEM2. }
      i. exploit val_match_functional; [eapply H3|eapply x0|].
      i. subst. ss. }

  exact (spec_eval_relative_secure_spec_mir_mc (uslh_prog p) tp (mem_length m1') (ir1, im1) (ir2, im2)
           ISAFE1 ISAFE2 (r1', m1') (r2', m2') SPEC LSYNC1 LSYNC2 LCOMP).
Qed.
