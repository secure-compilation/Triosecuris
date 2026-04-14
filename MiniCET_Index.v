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

Set Default Goal Selector "!".


Module MCC := MiniCETCommon(TotalMap).
Import MCC.
Import FunctionalExtensionality.

Notation t_update_eq := TotalMap.t_update_eq.
Notation t_update_neq := TotalMap.t_update_neq.

Reserved Notation
  "p '|-' '<((' c '))>' '-->^' os '<((' ct '))>'"
  (at level 40, c constr, ct constr).

Inductive seq_eval_small_step_inst (p:prog) :
  @state cfg -> @state cfg -> obs -> Prop :=
  | SSMI_Skip : forall pc rs m stk,
      p[[pc]] = Some <{{ skip }}> ->
      p |- <(( S_Running (pc, rs, m, stk) ))> -->^[] <(( S_Running (pc+1, rs, m, stk) ))>
  | SSMI_Asgn : forall pc r m sk e x,
      p[[pc]] = Some <{{ x := e }}> ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[] <(( S_Running (pc+1, (x !-> (eval r e); r), m, sk) ))>
  | SSMI_Div : forall pc r m sk e1 e2 x v1 v2,
      p[[pc]] = Some <{{ x <- div e1, e2 }}> ->
      to_nat (eval r e1) = Some v1 ->
      to_nat (eval r e2) = Some v2 ->
      let res := match v2 with
                | 0 => UV
                | _ => N (div v1 v2)
                end
      in
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[ODiv v1 v2] <(( S_Running (pc+1, (x !-> res; r), m, sk) ))>
  | SSMI_Branch : forall pc pc' r m sk e n l,
      p[[pc]] = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      pc' = (if (not_zero n) then (l,0) else pc+1) ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[OBranch (not_zero n)] <(( S_Running (pc', r, m, sk) ))>
  | SSMI_Jump : forall l pc r m sk,
      p[[pc]] = Some <{{ jump l }}> ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[] <(( S_Running ((l,0), r, m, sk) ))>
  | SSMI_Load : forall pc r m sk x e n v',
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m n = Some v' ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[OLoad n] <(( S_Running (pc+1, (x !-> v'; r), m, sk) ))>
  | SSMI_Store : forall pc r m sk e e' n,
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[OStore n] <(( S_Running (pc+1, r, upd n m (eval r e'), sk) ))>
  | SSMI_Call : forall pc r m sk e l,
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[OCall l] <(( S_Running (l, r, m, ((pc+1)::sk)) ))>
  | SSMI_Ret : forall pc r m sk pc',
      p[[pc]] = Some <{{ ret }}> ->
      p |- <(( S_Running (pc, r, m, pc'::sk) ))> -->^[] <(( S_Running (pc', r, m, sk) ))>
  | SSMI_Peek : forall pc r m sk x,
      p[[pc]] = Some <{{x <- peek}}> ->
      let val := match sk with
                | [] => UV
                | pc' :: sk' => FP pc'
                end
      in
      p |- <(( S_Running (pc, r, m, sk) ))> -->^[] <(( S_Running (pc+1, (x !-> val; r), m, sk) ))>
  | SSMI_Term : forall pc r m,
      p[[pc]] = Some <{{ ret }}> ->
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

Definition wf_ret (p: prog) (pc: cptr) : Prop :=
  let '(l, o) := pc in
  p[[(l, o)]] <> None /\ exists e, p[[(l, o - 1)]] = Some <{{ call e }}> /\ o > 0.

Definition wf_retb (p: prog) (pc: cptr) : bool :=
  let '(l, o) := pc in
  match p[[(l, o)]] with
  | Some _ => match o with
             | 0 => false
             | S o' => match p[[(l, o')]] with
                      | Some (ICall e) => true
                      | _ => false
                      end
             end
  | _ => false
  end.

Lemma wf_ret_wf_retb p pc:
  wf_ret p pc <-> wf_retb p pc = true.
Proof.
  destruct pc as [l o]. ss. split; i.
  - des_ifs; des; ss; try lia; clarify.
    all : rewrite sub_0_r in *; clarify.
  - des_ifs; des; ss; try lia; clarify.
    rewrite sub_0_r. esplits; eauto; ii; clarify. lia.
Qed.

Definition wf_stk (p: prog) (stk: list cptr) : Prop :=
  Forall (fun pc => wf_ret p pc) stk.

Definition call_return_targets (p: prog) : list cptr :=
  let ip := add_index p in
  List.concat
    (List.map (fun '(l, (bl, _)) =>
                 List.flat_map (fun '(o, i) => match i with
                                            | ICall _ => [(l, add o 1)]
                                            | _ => []
                                            end) (add_index bl)) ip).

Reserved Notation
  "p '|-' '<((' sc '))>' '-->_' ds '^^' os '<((' sct '))>'"
  (at level 40, sc constr, sct constr).

Inductive spec_eval_small_step (p:prog):
  @state spec_cfg -> @state spec_cfg -> dirs -> obs -> Prop :=
  | SpecSMI_Skip  :  forall pc r m sk ms,
      p[[pc]] = Some <{{ skip }}> ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( S_Running ((pc+1, r, m, sk), false, ms) ))>
  | SpecSMI_Asgn : forall pc r m sk ms e x,
      p[[pc]] = Some <{{ x := e }}> ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( S_Running ((pc+1, (x !-> (eval r e); r), m, sk), false, ms) ))>
  | SpecSMI_Div : forall pc r m sk ms e1 e2 x v1 v2,
      p[[pc]] = Some <{{ x <- div e1, e2 }}> ->
      to_nat (eval r e1) = Some v1 ->
      to_nat (eval r e2) = Some v2 ->
      let res := match v2 with
                | 0 => UV
                | _ => N (div v1 v2)
                end
      in
      p |- <(( S_Running (pc, r, m, sk, false, ms) ))> -->_[]^^[ODiv v1 v2] <(( S_Running (pc+1, (x !-> res; r), m, sk, false, ms) ))>
  | SpecSMI_Branch : forall pc pc' r m sk ms ms' b (b': bool) e n l,
      p[[pc]] = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      b = (not_zero n) ->
      pc' = (if b' then (l, 0) else (pc+1)) ->
      ms' = ms || negb (Bool.eqb b b') ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[DBranch b']^^[OBranch b] <(( S_Running ((pc', r, m, sk), false, ms') ))>
  | SpecSMI_Jump : forall l pc r m sk ms,
      p[[pc]] = Some <{{ jump l }}> ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[]^^[] <(( S_Running (((l,0), r, m, sk), false, ms) ))>
  | SpecSMI_Load : forall pc r m sk x e n v' ms,
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m n = Some v' ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[]^^[OLoad n] <(( S_Running ((pc+1, (x !-> v'; r), m, sk), false, ms) ))>
  | SpecSMI_Store : forall pc r m sk e e' n ms,
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[]^^[OStore n] <(( S_Running ((pc+1, r, upd n m (eval r e'), sk), false, ms) ))>
  | SpecSMI_Call : forall pc pc' r m sk e l ms ms',
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      ms' = ms || negb ((fst pc' =? fst l)%nat && (snd pc' =? snd l)%nat) ->
      p |- <(( S_Running ((pc, r, m, sk), false, ms) ))> -->_[DCall pc']^^[OCall l] <(( S_Running ((pc', r, m, (pc + 1)::sk), true, ms') ))>
  | SpecSMI_CTarget : forall pc r m sk ct ms,
      p[[pc]] = Some <{{ ctarget }}> ->
      p |- <(( S_Running ((pc, r, m, sk), ct, ms) ))> -->_[]^^[] <(( S_Running ((pc+1, r, m, sk), false, ms) ))>
  | SpecSMI_Ret : forall pc r m sk pc' pc'' ms ms',
      p[[pc]] = Some <{{ ret }}> ->
      wf_ret p pc'' ->
      ms' = ms || negb ((fst pc' =? fst pc'')%nat && (snd pc' =? snd pc'')%nat) ->
      p |- <(( S_Running ((pc, r, m, pc'::sk), false, ms) ))> -->_[DRet pc'']^^[] <(( S_Running ((pc'', r, m, sk), false, ms') ))>
  | SpecSMI_Peek : forall pc r m sk ms x,
      p[[pc]] = Some <{{x <- peek}}> ->
      let val := match sk with
                | [] => UV
                | pc' :: sk' => FP pc'
                end
      in
      p |- <(( S_Running (pc, r, m, sk, false, ms) ))> -->_[]^^[] <(( S_Running (pc+1, (x !-> val; r), m, sk, false, ms) ))>
  | SpecSMI_Term : forall pc r m ms,
      p[[pc]] = Some <{{ ret }}> ->
      p |- <(( S_Running ((pc, r, m, []), false, ms) ))> -->_[]^^[] <(( S_Term ))>
  | SpecSMI_Fault : forall pc r m sk ms,
      p[[pc]] <> Some <{{ ctarget }}> ->
      p |- <(( S_Running ((pc, r, m, sk), true, ms) ))> -->_[]^^[] <(( S_Fault ))>

  where "p |- <(( sc ))> -->_ ds ^^ os  <(( sct ))>" :=
    (spec_eval_small_step p sc sct ds os).


Reserved Notation
  "p '|-' '<((' sc '))>' '-->*_' ds '^^' os '^^' n '<((' sct '))>'"
  (at level 40, sc constr, sct constr).

Inductive multi_spec_inst (p:prog) :
  @state spec_cfg -> @state spec_cfg -> dirs -> obs -> nat -> Prop :=
  |multi_spec_inst_refl sc : p |- <(( sc ))> -->*_[]^^[]^^0 <(( sc ))>
  |multi_spec_inst_trans sc1 sc2 sc3 ds1 ds2 os1 os2 n :
      p |- <(( sc1 ))> -->_ds1^^os1 <(( sc2 ))> ->
      p |- <(( sc2 ))> -->*_ds2^^os2^^n <(( sc3 ))> ->
      p |- <(( sc1 ))> -->*_(ds1++ds2)^^(os1++os2)^^(S n) <(( sc3 ))>

  where "p |- <(( sc ))> -->*_ ds ^^ os ^^ n <(( sct ))>" :=
    (multi_spec_inst p sc sct ds os n).

Reserved Notation
  "p '|-' '<((' ic '))>' '-->i_' ds '^^' os '<((' ict '))>'"
  (at level 40, ic constr, ict constr).

Inductive ideal_eval_small_step_inst (p:prog) :
  @state ideal_cfg -> @state ideal_cfg -> dirs -> obs -> Prop :=
  | ISMI_Skip  :  forall pc r m sk ms,
      p[[pc]] = Some <{{ skip }}> ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[]^^[] <(( S_Running ((pc+1, r, m, sk), ms) ))>
  | ISMI_Asgn : forall pc r m sk ms e x,
      p[[pc]] = Some <{{ x := e }}> ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[]^^[] <(( S_Running ((pc+1, (x !-> (eval r e); r), m, sk), ms) ))>
  | ISMI_Div : forall pc r m sk (ms: bool) e1 e2 x v1 v2,
      p[[pc]] = Some <{{ x <- div e1, e2 }}> ->
      (if ms then Some 0 else to_nat (eval r e1)) = Some v1 ->
      (if ms then Some 0 else to_nat (eval r e2)) = Some v2 ->
      let res := match v2 with
                | 0 => UV
                | _ => N (div v1 v2)
                end
      in
      p |- <(( S_Running (pc, r, m, sk, ms) ))> -->i_[]^^[ODiv v1 v2] <(( S_Running (pc+1, (x !-> res; r), m, sk, ms) ))>
  | ISMI_Branch : forall pc pc' r m sk (ms ms' b b' : bool) e n' l,
      p[[pc]] = Some <{{ branch e to l }}> ->
      (if ms then Some 0 else to_nat (eval r e)) = Some n' ->
      b = (not_zero n') ->
      pc' = (if b' then (l,0) else pc+1) ->
      ms' = (ms || (negb (Bool.eqb b b'))) ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[DBranch b']^^[OBranch b] <(( S_Running ((pc', r, m, sk), ms') ))>
  | ISMI_Jump : forall l pc r m sk ms,
      p[[pc]] = Some <{{ jump l }}> ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[]^^[] <(( S_Running (((l,0), r, m, sk), ms) ))>
  | ISMI_Load : forall pc r m sk x e n me v' (ms : bool),
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      me = (if ms then (ANum 0) else e) ->
      to_nat (eval r me) = Some n ->
      nth_error m n = Some v' ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[]^^[OLoad n] <(( S_Running ((pc+1, (x !-> v'; r), m, sk), ms) ))>
  | ISMI_Store : forall pc r m sk e e' me n (ms : bool),
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      me = (if ms then (ANum 0) else e) ->
      to_nat (eval r me) = Some n ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[]^^[OStore n] <(( S_Running ((pc+1, r, upd n m (eval r e'), sk), ms) ))>
  | ISMI_Call : forall pc pc' r m sk e l (ms ms' : bool) blk,
      p[[pc]] = Some <{{ call e }}> ->
      (if ms then Some (0,0) else to_fp (eval r e)) = Some l ->
      ms' = ms || negb ((fst pc' =? fst l)%nat && (snd pc' =? snd l)%nat) ->
      nth_error p (fst pc') = Some blk ->
      snd blk = true ->
      snd pc' = 0 ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[DCall pc']^^[OCall l] <(( S_Running ((pc', r, m, (pc+1)::sk), ms') ))>
  | ISMI_Call_F : forall pc pc' r m sk e l (ms : bool),
      p[[pc]] = Some <{{ call e }}> ->
      (if ms then Some (0,0) else to_fp (eval r e)) = Some l ->
      (forall blk, nth_error p (fst pc') = Some blk -> snd blk = false \/ snd pc' <> 0) ->
      p |- <(( S_Running ((pc, r, m, sk), ms) ))> -->i_[DCall pc']^^[OCall l] <(( S_Fault ))>
  | ISMI_Ret : forall pc r m sk pc' pc'' ms ms',
      p[[pc]] = Some <{{ ret }}> ->
      wf_ret p pc'' ->
      ms' = ms || negb ((fst pc' =? fst pc'')%nat && (snd pc' =? snd pc'')%nat) ->
      p |- <(( S_Running ((pc, r, m, pc'::sk), ms) ))> -->i_[DRet pc'']^^[] <(( S_Running ((pc'', r, m, sk), ms') ))>
  | ISMI_Peek : forall pc r m sk ms x,
      p[[pc]] = Some <{{x <- peek}}> ->
      let val := match sk with
                | [] => UV
                | pc' :: sk' => FP pc'
                end
      in
      p |- <(( S_Running (pc, r, m, sk, ms) ))> -->i_[]^^[] <(( S_Running (pc+1, (x !-> val; r), m, sk, ms) ))>
  | ISMI_Term : forall pc r m ms,
      p[[pc]] = Some <{{ ret }}> ->
      p |- <(( S_Running ((pc, r, m, []), ms) ))> -->i_[]^^[] <(( S_Term ))>

  where "p |- <(( ic ))> -->i_ ds ^^ os  <(( ict ))>" :=
    (ideal_eval_small_step_inst p ic ict ds os).

Reserved Notation
  "p '|-' '<((' ic '))>' '-->i*_' ds '^^' os '<((' ict '))>'"
  (at level 40, ic constr, ict constr).

Inductive multi_ideal_inst (p:prog) :
  @state ideal_cfg -> @state ideal_cfg -> dirs -> obs -> Prop :=
  | multi_ideal_inst_refl ic : p |- <(( ic ))> -->i*_[]^^[] <(( ic ))>
  | multi_ideal_inst_trans ic1 ic2 ic3 ds1 ds2 os1 os2 :
      p |- <(( ic1 ))> -->i_ds1^^os1 <(( ic2 ))> ->
      p |- <(( ic2 ))> -->i*_ds2^^os2 <(( ic3 ))> ->
      p |- <(( ic1 ))> -->i*_(ds1++ds2)^^(os1++os2) <(( ic3 ))>
  where "p |- <(( ic ))> -->i*_ ds ^^ os <(( ict ))>" :=
    (multi_ideal_inst p ic ict ds os).

Definition msf_lookup_sc (sc: spec_cfg) : val :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, stk) := c in
  r ! msf.

Definition msf_lookup_ic (ic: ideal_cfg) : val :=
let '(c, ms) := ic in
  let '(pc, r, m, stk) := c in
  r ! msf.

Definition callee_lookup_sc (sc: spec_cfg) : val :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, stk) := c in
  r ! callee.

Definition callee_lookup_ic (ic: ideal_cfg) : val :=
  let '(c, ms) := ic in
  let '(pc, r, m, stk) := c in
  r ! callee.

Definition ms_true_sc (sc: spec_cfg) : bool :=
  let '(c, ct, ms) := sc in ms.

Definition ms_true_ic (ic: ideal_cfg) : bool :=
  let '(c, ms) := ic in ms.























Definition offset_uslh (bl: list inst * bool) : list nat :=
  _offset_uslh (fst bl) (if snd bl then 2 else 0).


Definition pc_sync (p: prog) (pc: cptr) : option cptr :=
  let ip := map offset_uslh p in
  let '(l, o) := pc in
  match nth_error ip l with
  | Some ib => match nth_error ib o with
              | Some io => Some (l, io)
              | _ => None
              end
  | _ => None
  end.

Definition r_sync (r: reg) (ms: bool) : reg :=
   msf !-> N (if ms then 1 else 0); r.

Lemma eval_unused_update : forall (x : string) (r: reg) (e: exp) (v: val),
  e_unused x e -> eval (x !-> v; r) e = eval r e.
Proof.
  intros until v. induction e; intros; simpl in *; try reflexivity.
  - eapply t_update_neq; auto.
  - destruct H. specialize (IHe1 H). specialize (IHe2 H0).
    rewrite IHe1, IHe2. auto.
  - destruct H, H0. specialize (IHe1 H). specialize (IHe2 H0).
    specialize (IHe3 H1). rewrite IHe1, IHe2, IHe3.
    destruct (to_nat (eval r e1)) eqn:Heval1; auto.
Qed.

Fixpoint map_opt {S T} (f: S -> option T) l : option (list T):=
  match l with
  | [] => Some []
  | a :: l' => match f a with
             | Some a' =>
                 match map_opt f l' with
                 | Some l'' => Some (a' :: l'')
                 | _ => None
                 end
             | _ => None
             end
  end.

Definition ret_sync (p: prog) (pc: cptr) : option cptr :=
  match pc with
  | (l, S o) => match p[[(l, o)]] with
               | Some (ICall _) => match (pc_sync p (l, o)) with
                                  | Some (l', o') => Some (l', o'+2)
                                  | None => None
                                  end
               | _ => None
               end
  | _ => None
  end.

Definition val_match (p: prog) (v1 v2: val) : Prop :=
  match v1, v2 with
  | N n1, N n2 => n1 = n2
  | FP (l1, o1), FP (l2, o2) => if (o1 =? 0)%nat
                               then l1 = l2 /\ (o2 = 0)
                               else ret_sync p (l1, o1) = Some (l2, o2)
  | UV, UV => True
  | _, _ => False
  end.

Definition Rsync (p: prog) (sr tr: reg) (ms: bool) : Prop :=
   (forall x, x <> msf /\ x <> callee -> val_match p (sr ! x) (tr ! x)) /\
   (tr ! msf = N (if ms then 1 else 0)).

Definition Msync (p: prog) (sm tm: mem) : Prop :=
  forall i, match nth_error sm i, nth_error tm i with
       | Some sv, Some tv => val_match p sv tv
       | None, None => True
       | _, _ => False
       end.

Definition Rsync1 (p: prog) (sr tr: reg) : Prop :=
  (forall x, x <> msf /\ x <> callee -> val_match p (sr ! x) (tr ! x)).

Definition ms_msf_match (tr: reg) (ms: bool) : Prop :=
  (tr ! msf = N (if ms then 1 else 0)).

Variant match_cfgs (p: prog) : ideal_cfg -> spec_cfg -> Prop :=
| match_cfgs_intro pc r m stk ms pc' r' m' stk'
  (PC: pc_sync p pc = Some pc')
  (REG: Rsync p r r' ms)
  (MSC: Msync p m m')
  (STK: map_opt (ret_sync p) stk = Some stk') :
  match_cfgs p ((pc, r, m, stk), ms) ((pc', r', m', stk'), false, ms)
.



















Definition get_reg_sc (sc: spec_cfg) : reg :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, sk) := c in
  r.

Definition get_reg_ic (ic: ideal_cfg) : reg :=
  let '(c, ms) := ic in
  let '(pc, r, m, sk) := c in
  r.

Definition get_pc_sc (sc: spec_cfg) : cptr :=
  let '(c, ct, ms) := sc in
  let '(pc, r, m, sk) := c in
  pc.

Definition get_pc_ic (ic: ideal_cfg) : cptr :=
  let '(c, ms) := ic in
  let '(pc, r, m, sk) := c in
  pc.

Definition wf_dir' (p: prog) (d: direction) : Prop :=
  match d with
  | DCall pc' => is_some p[[pc']] = true

  | _ => True
  end.

Definition wf_ds' (p: prog) (ds: dirs) : Prop :=
  Forall (wf_dir' p) ds.

Definition match_ob (p: prog) (o1 o2: observation) : Prop :=
  match o1, o2 with
  | ODiv _ _, ODiv _ _ | OBranch _, OBranch _ | OLoad _, OLoad _ | OStore _, OStore _ => o1 = o2
  | OCall (l1, 0), OCall (l2, 0) => l1 = l2
  | OCall (l1, S o1), OCall (l2, S o2) => ret_sync p (l1, S o1) = Some (l2, S o2)



  | _, _ => False
  end.

Definition match_obs (p: prog) (os1 os2: obs) : Prop :=
  Forall2 (match_ob p) os1 os2.

Definition match_dir (p: prog) (d1 d2: direction) : Prop :=
  match d1, d2 with
  | DBranch b1, DBranch b2 => b1 = b2
  | DCall pc1, DCall pc2 => pc1 = pc2
  | DRet pc1, DRet pc2 => ret_sync p pc1 = Some pc2
  | _, _ => False
  end.

Definition match_ds (p: prog) (ds1 ds2: dirs) : Prop :=
  Forall2 (match_dir p) ds1 ds2.

Definition nonempty_block (blk : (list inst * bool)) : Prop :=
  0 < Datatypes.length (fst blk).

Definition is_terminator (i: inst) : Prop :=
  match i with
  | <{{ ret }}> | <{{ jump _}}> => True
  | _ => False
  end.

Definition last_inst_terminator (blk: (list inst * bool)) : Prop :=
  match (rev (fst blk)) with
  | [] => False
  | h::t => is_terminator h
  end.

Definition wf_lbl (p: prog) (is_proc: bool) (l: nat) : Prop :=
  match nth_error p l with
  | Some (_, b) => is_proc = b
  | None => False
  end.


Fixpoint wf_expr (p: prog) (e: exp) : Prop :=
  match e with
  | ANum _ | AId _ => True
  | ABin _ e1 e2 => wf_expr p e1 /\ wf_expr p e2
  | <{b ? e1 : e2}> => wf_expr p b /\ wf_expr p e1 /\ wf_expr p e2
  | <{&l}> => snd l = 0 /\ wf_lbl p true (fst l)
  end.

Lemma wf_expr_wf_exp p e:
  wf_expr p e <-> wf_exp p e = true.
Proof.
    induction e; ss; rewrite! andb_true_iff; firstorder.
    1, 3: now apply Nat.eqb_eq.
    all: unfold wf_lbl, wf_label in *; destruct (nth_error p (fst l)).
    2: contradiction. 3: discriminate.
    all: destruct p0; ss; clarify. now destruct b.
Qed.

Definition wf_instr (p: prog) (i: inst) : Prop :=
  match i with
  | <{{skip}}> | <{{ctarget}}> | <{{ret}}> | <{{_<-peek}}> => True
  | <{{_:=e}}> | ILoad _ e | <{{call e}}> => wf_expr p e
  | <{{store[e]<-e'}}> => wf_expr p e /\ wf_expr p e'
  | <{{_<-div e1, e2}}> => wf_expr p e1 /\ wf_expr p e2
  | <{{branch e to l}}> => wf_expr p e /\ wf_lbl p false l
  | <{{jump l}}> => wf_lbl p false l
  end.

Definition wf_block (p: prog) (blk : (list inst * bool)) : Prop :=
   nonempty_block blk /\ last_inst_terminator blk /\ Forall (wf_instr p) (fst blk).

Definition nonempty_program (p: prog) : Prop :=
  0 < Datatypes.length p.

Definition wf_prog (p: prog) : Prop :=
  nonempty_program p /\ Forall (wf_block p) p.


Lemma wf_ds_app p ds1 ds2
    (WF: wf_ds' p (ds1 ++ ds2)) :
  wf_ds' p ds1 /\ wf_ds' p ds2.
Proof. eapply Forall_app. eauto. Qed.

Lemma multi_spec_splitting p sc ds os n sct m
    (LEN: n >= m)
    (STEPS: p |- <(( sc ))> -->*_ ds ^^ os ^^ n <(( sct ))>) :
  exists scm ds1 ds2 os1 os2,
    p |- <(( sc ))> -->*_ ds1 ^^ os1 ^^ m <(( scm ))>
  /\ p |- <(( scm ))> -->*_ ds2 ^^ os2 ^^ (n - m) <(( sct ))>
  /\ ds = ds1 ++ ds2 /\ os = os1 ++ os2.
Proof.
  ginduction m; ii.
  - esplits; try econs. rewrite sub_0_r. auto.
  - destruct n as [|n]; try lia. inv STEPS.
    exploit IHm; try eapply H5; eauto; [lia|]. i. des.
    replace (S n - S m) with (n - m) by lia.
    esplits; eauto.
    { econs; eauto. }
    { subst. rewrite app_assoc. auto. }
    { subst. rewrite app_assoc. auto. }
Qed.

Lemma rev_fetch : forall (p: prog) (pc: cptr) (blk: list inst * bool) (i: inst),
  nth_error p (fst pc) = Some blk ->
  nth_error (fst blk) (snd pc) = Some i ->
  p[[pc]] = Some i.
Proof.
  intros. destruct pc as (l & o) eqn:Hpc.
  destruct (nth_error p (fst pc)) eqn:Hblk.
  - unfold fetch. ss. des_ifs.
  - rewrite Hpc in *. ss. des_ifs.
Qed.

Lemma blk_not_empty_list : forall (blk: list inst * bool),
  nonempty_block blk -> (fst blk) <> [].
Proof.
  intros. unfold nonempty_block in H. unfold not; intros. rewrite H0 in H.
  simpl in H. apply nlt_0_r in H. destruct H.
Qed.

Lemma prog_not_empty_list (p: prog) : nonempty_program p -> p <> [].
Proof.
  intros. unfold nonempty_program in H. unfold not; intros. rewrite H0 in H.
  simpl in H. apply nlt_0_r in H. destruct H.
Qed.

Lemma cons_app : forall {A} (l: list A) (a: A),
  a :: l = [a] ++ l.
Proof.
  intros. destruct l; [rewrite app_nil_r|]; reflexivity.
Qed.

Lemma rev_cons : forall {A} (l: list A) (a: A),
  rev (a :: l) = rev l ++ [a].
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma utils_rev_append_and_rev : forall {X : Type} (l1 l2 : list X),
  Utils.rev_append l1 l2 = rev l1 ++ l2.
Proof.
  intros X. induction l1 as [|h1 t1 IHl1].
  - reflexivity.
  - simpl. rewrite <- IHl1. apply functional_extensionality in IHl1.
    rewrite IHl1. intros l2. rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma revs : forall {A}, @Utils.rev A = @rev A.
Proof.
  intros. apply functional_extensionality. intros.
  rename x into l. induction l as [|h t IHl]; auto.
  unfold Utils.rev in *. simpl. rewrite <- IHl.
  rewrite utils_rev_append_and_rev. rewrite IHl. reflexivity.
Qed.

Lemma block_always_terminator b o i
  (WFB: last_inst_terminator b)
  (INST: nth_error (fst b) o = Some i)
  (NT: ~ is_terminator i) :
  exists i', nth_error (fst b) (add o 1) = Some i'.
Proof.
  red in WFB. des_ifs.
  destruct (le_dec o (Datatypes.length (fst b) - 1)).

  { assert (i <> i0).
    { unfold not; intros. unfold is_terminator in *.
      destruct i eqn:Hi; destruct i0 eqn:Hi0; clarify. }
  destruct (eq_dec o (Datatypes.length (fst b) - 1)).

    { assert (rev (i0 :: l) = rev l ++ [i0]). { simpl. auto. }
      assert (rev (rev (fst b)) = rev (i0 :: l)). { rewrite Heq. simpl. auto. }
      rewrite rev_involutive in H1. simpl in H1.
      assert (nth_error (fst b) o = Some i0).
      { rewrite H1, e. simpl. rewrite H1. simpl. rewrite nth_error_app.
        assert ((Datatypes.length (rev l ++ [i0]) - 1 <? Datatypes.length (rev l))%nat = false).
        { induction l as [|h t]; clarify. simpl in *.
          assert (add 1 (Datatypes.length (rev t ++ [h])) = Datatypes.length ((rev t ++ [h]) ++ [i0])).
          { repeat rewrite length_app. assert (Datatypes.length [i0] = 1). { auto. } rewrite H2. rewrite add_comm. auto. }
          rewrite <- H2. simpl. rewrite sub_0_r. apply ltb_irrefl.
        }
        rewrite H2.
        assert (forall (n: nat), ((add n 1) - 1) - n = 0). { lia. }
        specialize (H3 (Datatypes.length (rev l))).
        rewrite length_app. assert (Datatypes.length [i0] = 1). { simpl. auto. }
        rewrite H4.
        assert (((add 1 (Datatypes.length (rev l))) - 1) = Datatypes.length (rev l)). { simpl. rewrite sub_0_r. auto. }
        rewrite add_comm. rewrite H5. simpl.
        assert ( ((Datatypes.length (rev l)) - (Datatypes.length (rev l))) = 0 ). { lia. }
        rewrite H6. simpl. auto.
      }
      rewrite INST in H2. injection H2; intros. clarify.
    }

    assert (rev (i0 :: l) = rev l ++ [i0]) by ss.
    assert (rev (rev (fst b)) = rev (i0 :: l)) by (rewrite Heq; ss).
    rewrite rev_involutive in H1. simpl in H1. rewrite H1 in INST, l0, n. rewrite H1.
    assert (o <= Datatypes.length (rev l ++ [i0]) - 1
            -> o <> Datatypes.length (rev l ++ [i0]) - 1
            -> o < Datatypes.length (rev l ++ [i0]) - 1 ).
    { lia. }
    specialize (H2 l0 n); intros.
    assert ((add o 1) <= (Datatypes.length (rev l ++ [i0]) - 1)). { lia. }
    assert ((add o 1) < (Datatypes.length (rev l ++ [i0]))). { lia. }
    rewrite <- nth_error_Some in H4.
    destruct (nth_error (rev l ++ [i0]) (add o 1)); clarify. exists i1. auto.
  }

  exfalso. clear - n INST. eapply not_le in n.
  assert (nth_error (fst b) o <> None).
  { ii. clarify. }
  rewrite nth_error_Some in H. lia.
Qed.

Lemma block_always_terminator_prog_aux p pc i
  (WF: Forall last_inst_terminator p)
  (INST: p[[pc]] = Some i)
  (NT: ~ is_terminator i) :
  exists i', p[[pc+1]] = Some i'.
Proof.
  destruct pc as [l o]. ss. des_ifs_safe.
  exploit block_always_terminator; eauto.
  rewrite Forall_forall in WF. eapply WF.
  eapply nth_error_In; eauto.
Qed.

Lemma block_always_terminator_prog p pc i
  (WF: wf_prog p)
  (INST: p[[pc]] = Some i)
  (NT: ~ is_terminator i) :
  exists i', p[[pc+1]] = Some i'.
Proof.
  inv WF. des. eapply block_always_terminator_prog_aux; eauto.
  eapply Forall_and_inv in H0. des. eapply Forall_and_inv in H1. des.
  eauto.
Qed.

Import MonadNotation.
Open Scope monad_scope.

Definition simple_inst (i: inst) : Prop :=
  match i with
  | ISkip | IJump _ | ILoad _ _ | IStore _ _ | IAsgn _ _ | IDiv _ _ _ | IPeek _ => True
  | _ => False
  end.


Variant match_simple_inst_uslh : inst -> inst -> Prop :=
| uslh_skip :
  match_simple_inst_uslh ISkip ISkip
| uslh_jump l:
  match_simple_inst_uslh (IJump l) (IJump l)
| uslh_load x e e'
  (IDX: e' = <{{ (msf = 1) ? 0 : e }}>) :
  match_simple_inst_uslh (ILoad x e) (ILoad x e')
| uslh_store e e' e1
  (IDX: e' = <{{ (msf = 1) ? 0 : e }}>) :
  match_simple_inst_uslh (IStore e e1) (IStore e' e1)
| uslh_asgn x e:
  match_simple_inst_uslh (IAsgn x e) (IAsgn x e)
| uslh_div x e1 e2 e1' e2'
  (IDe1: e1' = <{{ (msf = 1) ? 0 : e1}}>)
  (IDe2: e2' = <{{ (msf = 1) ? 0 : e2}}>):
  match_simple_inst_uslh (IDiv x e1 e2) (IDiv x e1' e2')
| uslh_peek x:
  match_simple_inst_uslh (IPeek x) (IPeek x)
.

Definition _branch_in_block (blk: list inst) : nat :=
  fold_left (fun acc i => add acc (match i with
                                | IBranch _ _ => 1
                                | _ => 0
                                end)) blk 0.

Definition branch_in_block (bb: list inst * bool) : nat :=
  _branch_in_block (fst bb).

Definition branch_in_prog (p: prog) : nat :=
  fold_left (fun acc b => add acc (branch_in_block b)) p 0.

Definition branch_in_prog_before (p: prog) (l: nat) : nat :=
  branch_in_prog (firstn l p).

Definition _offset_branch_before (blk: list inst) (ofs: nat) : nat :=
  _branch_in_block (firstn ofs blk).

Definition offset_branch_before (blk: list inst * bool) (ofs: nat) : nat :=
  _offset_branch_before (fst blk) ofs.

Definition match_branch_target (p: prog) (pc: nat * nat) : option nat :=
  let '(l, o) := pc in
  match nth_error p l with
  | Some blk => Some (Datatypes.length p + branch_in_prog_before p l + offset_branch_before blk o)
  | _ => None
  end.

Variant match_inst_uslh (p: prog) (pc: cptr) : inst -> inst -> Prop :=
| uslh_simple i i'
  (SIMPL: simple_inst i)
  (MATCH: match_simple_inst_uslh i i') :
  match_inst_uslh p pc i i'
| uslh_branch e e' l l' tpc
  (COND: e' = <{{ (msf = 1) ? 0 : e }}>)
  (LB: match_branch_target p pc = Some l')
  (IN: nth_error (uslh_prog p) l' =
         Some ([<{{ msf := (~ e') ? 1 : msf }}>; <{{ jump l }}>], false))
  (SYNC: pc_sync p pc = Some tpc)
  (NXT: (uslh_prog p)[[tpc + 1]] = Some <{{ msf := e' ? 1 : msf }}>) :
  match_inst_uslh p pc (IBranch e l) (IBranch e' l')
| uslh_call e e' e'' tpc
  (CALL: e' = <{{ (msf = 1) ? & (0,0) : e }}>)
  (SYNC: pc_sync p pc = Some tpc)
  (RET: e'' = <{ callee = &(fst tpc, snd tpc + 2) }>)
  (IN: (uslh_prog p)[[ tpc + 1 ]] = Some (ICall e'))
  (IN': (uslh_prog p)[[ (fst tpc, snd tpc + 2) ]] = Some <{{ msf := e'' ? msf : 1 }}>) :
  match_inst_uslh p pc (ICall e) (IAsgn callee e')
| uslh_ret tpc
  (SYNC: pc_sync p pc = Some tpc)
  (NXT: (uslh_prog p)[[tpc + 1]] = Some IRet) :
  match_inst_uslh p pc IRet (IPeek callee)
.

Lemma uslh_inst_simple i l o c iss np
  (SIMP: simple_inst i)
  (USLH: uslh_inst i l o c = (iss, np)) :
  exists i', iss = [i'] /\ match_simple_inst_uslh i i' /\ np = [].
Proof.
  ii. unfold uslh_inst in USLH. ss.
  des_ifs; ss; unfold MiniCET.uslh_ret in *; clarify; esplits; econs; eauto.
Qed.

Lemma mapM_nth_error {A B} (f: A -> M B) l c l' np o blk
  (MM: mapM f l c = (l', np))
  (SRC: nth_error l o = Some blk) :
  exists blk' c' np', nth_error l' o = Some blk' /\ f blk c' = (blk', np').
Proof.
  ginduction l; ss; ii.
  { rewrite nth_error_nil in SRC. clarify. }
  rewrite unfold_mapM in MM.
  destruct o as [|o].
  { ss; clarify. unfold uslh_bind in MM.
    destruct (f blk c) eqn:F.
    destruct (mapM f l (c + Datatypes.length p)) eqn:MF.
    ss. clarify. esplits; eauto. }
  ss. unfold uslh_bind in MM.
  destruct (f a c) eqn:F.
  destruct (mapM f l (c + Datatypes.length p)) eqn:MF. ss. clarify.
  exploit IHl; eauto.
Qed.

Definition len_before {A B} (f: A -> M B) (l: list A) (o c: nat) : nat :=
  let '(_, np) := mapM f (firstn o l) c in
  Datatypes.length np.

Lemma mapM_nth_error_strong {A B} (f: A -> M B) l c l' np o blk
  (MM: mapM f l c = (l', np))
  (SRC: nth_error l o = Some blk) :
  exists blk' c' np',
    nth_error l' o = Some blk'
  /\ f blk c' = (blk', np')
  /\ c' = c + len_before f l o c.
Proof.
  ginduction l; ss; ii.
  { rewrite nth_error_nil in SRC. clarify. }
  rewrite unfold_mapM in MM.
  destruct o as [|o].
  { ss; clarify. unfold uslh_bind in MM.
    destruct (f blk c) eqn:F.
    destruct (mapM f l (c + Datatypes.length p)) eqn:MF.
    ss. clarify. esplits; eauto.
    unfold len_before, mapM. des_ifs. ss.
    unfold MiniCET.uslh_ret in Heq. clarify. ss. lia. }
  ss. unfold uslh_bind in MM.
  destruct (f a c) eqn:F.
  destruct (mapM f l (c + Datatypes.length p)) eqn:MF. ss. clarify.
  exploit IHl; eauto. i. des.
  esplits; eauto.
  unfold len_before. ss. des_ifs.
  rewrite unfold_mapM in Heq. eapply bind_inv in Heq. des. subst.
  eapply bind_inv in Heq0. des. subst.
  unfold len_before. rewrite Heq in F. clarify. rewrite Heq0.
  ss. unfold MiniCET.uslh_ret in Heq1. clarify.
  do 2 rewrite length_app. ss. lia.
Qed.





Definition prefix_offset {A} (ll: list (list A)) (i: nat) (base: nat) :=
  fold_left (fun acc l => acc + (Datatypes.length l)) (firstn i ll) base.

Definition fold_left_add_init {A} (f: A -> nat) (l: list A) (n k: nat) :
  fold_left (fun acc x => acc + f x) l (n + k) = (fold_left (fun acc x => acc + f x) l n) + k.
Proof.
  ginduction l; ss; ii.
  replace (n + k + f a) with ((n + f a) + k) by lia. eauto.
Qed.

Definition fold_left_init_0 {A} (f: A -> nat) (l: list A) (n: nat) :
  fold_left (fun acc x => acc + f x) l n = (fold_left (fun acc x => acc + f x) l 0) + n.
Proof.
  replace n with (0 + n) by lia.
  rewrite fold_left_add_init. lia.
Qed.

Lemma concat_nth_error {A} (ll: list (list A)) l i j ii
  (LL: nth_error ll i = Some l)
  (L: nth_error l j = Some ii) :
  nth_error (List.concat ll) ((prefix_offset ll i 0) + j)%nat = Some ii.
Proof.
  ginduction ll; ss; ii.
  { rewrite nth_error_nil in LL. clarify. }
  destruct i; ss.
  { clarify. rewrite nth_error_app1; auto.
    rewrite <- nth_error_Some. ii; clarify. }

  exploit IHll; eauto. i.
  replace (prefix_offset (a :: ll) (S i) 0) with ((Datatypes.length a) + (prefix_offset ll i 0)).
  2:{ unfold prefix_offset. ss. rewrite add_comm. rewrite <- fold_left_add_init.
      rewrite add_0_l. auto. }
  rewrite nth_error_app2.
  2:{ lia. }
  replace (Datatypes.length a + prefix_offset ll i 0 + j - Datatypes.length a) with
    (prefix_offset ll i 0 + j) by lia.
  auto.
Qed.

Lemma uslh_inst_inst_sz i l n c i' pm
  (USLH: uslh_inst i l n c = (i', pm)) :
  Datatypes.length i' = uslh_inst_sz i.
Proof.
  destruct i; ss; unfold MiniCET.uslh_ret in *; clarify.
  eapply bind_inv in USLH. des. ss. clarify.
Qed.

Lemma offset_eq_aux
  l blk n c blk' pn o o'
  (TRANSL: mapM (fun '(o, i) => uslh_inst i l o)
             (combine (_offset_uslh blk n) blk) c = (blk', pn))
  (OFS: nth_error (_offset_uslh blk n) o = Some o')
  (BDD: o < Datatypes.length blk) :
  prefix_offset blk' o n = o'.
Proof.
  ginduction blk; ii.
  { ss. lia. }

  exploit mapM_perserve_len; eauto. intros LEN.
  ss. rewrite unfold_mapM in TRANSL. eapply bind_inv in TRANSL. des.
  eapply bind_inv in TRANSL0. des. clarify.
  ss. unfold MiniCET.uslh_ret in *. clarify.
  destruct o.
  { ss. clarify. }
  ss. hexploit IHblk; eauto.
  { lia. }
  i. subst. unfold prefix_offset. rewrite firstn_cons.
  simpl. erewrite uslh_inst_inst_sz; eauto.
Qed.



































Lemma nth_error_add_index {A} (p: list A) l i
  (NTH: nth_error p l = Some i) :
  nth_error (add_index p) l = Some (l, i).
Proof.
  erewrite nth_error_nth'.
  2:{ rewrite length_add_index. rewrite <- nth_error_Some. ii. clarify. }
  instantiate (1:=(l, i)).
  f_equal. unfold add_index.
  rewrite combine_nth.
  2:{ eapply length_seq. }
  rewrite seq_nth.
  2:{ rewrite <- nth_error_Some. ii. clarify. }
  ss. f_equal. eapply nth_error_nth. auto.
Qed.































Lemma uslh_offset_uslh_add_index bl is_proc l1 l2
  (L1: l1 = offset_uslh (bl, is_proc))
  (L2: l2 = bl) :
  (add_index_uslh bl is_proc) = combine l1 l2.
Proof.
  unfold add_index_uslh, offset_uslh in *. subst. auto.
Qed.

Lemma _offset_uslh_combine blk n o o' i
  (NTH: nth_error (_offset_uslh blk n) o = Some o')
  (INST: nth_error blk o = Some i) :
  nth_error (combine (_offset_uslh blk n) blk) o = Some (o', i).
Proof.
  ginduction blk; ss; i.
  { rewrite nth_error_nil in NTH; clarify. }
  destruct o.
  { ss. clarify. }
  rewrite nth_error_cons_succ in *. eauto.
Qed.






Lemma src_skip_inv p tp pc tpc
  (TRP: uslh_prog p = tp)
  (PS: pc_sync p pc = Some tpc)
  (INST: p[[pc]] = Some <{{ skip }}>) :
  tp[[tpc]] = Some <{{ skip }}>.
Proof.
  destruct pc as [l o].
  destruct tpc as [l' o'].
  assert (l' = l).
  { clear -PS. unfold pc_sync in *. des_ifs. }
  subst. ss. des_ifs_safe.
  destruct p0 as [blk is_proc]. ss.
  unfold uslh_prog.
  destruct (mapM uslh_blk (add_index p) (Datatypes.length p)) as [p' newp] eqn:Huslh.
  exploit mapM_perserve_len; eauto. intros LEN.
  replace (nth_error (p' ++ newp) l) with (nth_error p' l); cycle 1.
  { symmetry. eapply nth_error_app1. rewrite <- LEN.
    unfold add_index. rewrite length_combine, length_seq, min_id.
    erewrite <- nth_error_Some. ii. clarify. }
  exploit mapM_nth_error; eauto.
  { instantiate (2:= l). instantiate (1:= (l, (blk, is_proc))).
    eapply nth_error_add_index. auto. }
  i. des. rewrite x0. destruct blk' as [blk' is_proc'].
  simpl.
  ss. unfold uslh_bind in x1. ss.
  des_ifs_safe. rename Heq2 into X.

  unfold pc_sync in *. ss. des_ifs_safe.


  erewrite uslh_offset_uslh_add_index in X; eauto.
  unfold concatM in X. exploit bind_inv; eauto. i. des; subst.
  exploit mapM_nth_error; try eapply x1; eauto.
  { instantiate (2:=o). instantiate (1:= (o', ISkip)).
    eapply _offset_uslh_combine; eauto. ss.
    rewrite nth_error_map in Heq0. unfold option_map in Heq0.
    rewrite Heq in Heq0. clarify. }
  i. des.
  ss. unfold MiniCET.uslh_ret in *. ss. clarify.
  eapply bind_inv in X. des. subst. clarify. rewrite X in x1. clarify.
  rewrite nth_error_map in Heq0. unfold option_map in Heq0. des_ifs_safe.
  hexploit offset_eq_aux; eauto.
  { ss. rewrite <- nth_error_Some. ii. clarify. }
  i. subst. simpl. des_ifs.
  - unfold prefix_offset. rewrite fold_left_init_0.
    replace 2 with (add 1 1) by lia. rewrite add_assoc. repeat rewrite add_1_r.
    do 2 rewrite nth_error_cons_succ.
    exploit (concat_nth_error _ _ _ 0); eauto; ss.
    i. rewrite <- plus_n_O in x1. auto.
  - rewrite plus_n_O with (n:=(prefix_offset a o 0)).
    eapply concat_nth_error; eauto.
Qed.

Lemma label_inv p tp l blk
  (TRP: uslh_prog p = tp)
  (SRC: nth_error p l = Some blk) :
  exists blk' c np', nth_error tp l = Some blk'
             /\ uslh_blk (l, blk) c = (blk', np')
             /\ c = Datatypes.length p + len_before uslh_blk (add_index p) l (Datatypes.length p).
Proof.
  subst. unfold uslh_prog. des_ifs_safe.
  exploit mapM_perserve_len; eauto. intros LEN.

  replace (nth_error (l0 ++ p0) l) with (nth_error l0 l); cycle 1.
  { symmetry. eapply nth_error_app1. rewrite <- LEN.
    unfold add_index. rewrite length_combine, length_seq, min_id.
    erewrite <- nth_error_Some. ii. clarify. }

  exploit mapM_nth_error_strong; eauto.
  eapply nth_error_add_index. eauto.
Qed.

Lemma src_simple_inv p tp pc tpc i
  (SIMP: simple_inst i)
  (TRP: uslh_prog p = tp)
  (PS: pc_sync p pc = Some tpc)
  (INST: p[[pc]] = Some <{{ i }}>) :
  exists i', tp[[tpc]] = Some <{{ i' }}> /\ match_simple_inst_uslh i i'.
Proof.
  destruct pc as [l o]. destruct tpc as [l' o'].
  assert (l' = l).
  { clear -PS. unfold pc_sync in *. des_ifs. }
  subst. ss. des_ifs_safe.
  destruct p0 as [blk is_proc]. ss.

  hexploit label_inv; eauto. i. des. rewrite H.
  ss. unfold uslh_bind in H0. ss. des_ifs_safe.

  erewrite uslh_offset_uslh_add_index in Heq2; eauto.
  unfold concatM in Heq2. exploit bind_inv; eauto. i. des; subst.
  exploit mapM_nth_error; try eapply x0; eauto.
  { instantiate (2:=o). instantiate (1:= (o', i)).
    eapply _offset_uslh_combine; eauto. ss.
    rewrite nth_error_map in Heq0. unfold option_map in Heq0.
    rewrite Heq in Heq0. clarify. }
  i. des.

  ss. unfold MiniCET.uslh_ret in *. ss. clarify.
  eapply bind_inv in Heq2. des. subst. clarify. rewrite Heq2 in x0. clarify.
  rewrite nth_error_map in Heq0. unfold option_map in Heq0. des_ifs_safe.
  hexploit offset_eq_aux; eauto; i.
  { ss. rewrite <- nth_error_Some. ii. clarify. }

  des_ifs.
  - unfold prefix_offset. rewrite fold_left_init_0.
    replace 2 with (add 1 1) by lia.
    rewrite add_assoc. do 2 rewrite add_1_r. simpl.
    destruct i; ss; unfold MiniCET.uslh_ret in *; clarify.
    + exists ISkip; split; [|econs]. rewrite plus_n_O at 1.
      eapply concat_nth_error; eauto.
    + exists (IAsgn x e); split; [|econs]. rewrite plus_n_O at 1.
      eapply concat_nth_error; eauto.
    + esplits; [|econs]; eauto. rewrite plus_n_O at 1.
      eapply concat_nth_error; eauto.
    + esplits; [|econs]; eauto. rewrite plus_n_O at 1.
      exploit concat_nth_error; ss; eauto. ss.
    + esplits; [|econs]; eauto. rewrite plus_n_O at 1.
      exploit concat_nth_error; ss; eauto. ss.
    + esplits; [|econs]; eauto. rewrite plus_n_O at 1.
      exploit concat_nth_error; ss; eauto. ss.
    + esplits; [|econs]; eauto. rewrite plus_n_O at 1.
      exploit concat_nth_error; ss; eauto. ss.
  - destruct i; ss; unfold MiniCET.uslh_ret in *; clarify.
    + exists ISkip; split; [|econs]. rewrite plus_n_O at 1.
      exploit concat_nth_error; ss; eauto. ss.
    + exists (IAsgn x e); split; [|econs]. rewrite plus_n_O at 1.
      exploit concat_nth_error; ss; eauto. ss.
    + esplits; [|econs]; eauto. rewrite plus_n_O at 1.
      exploit concat_nth_error; ss; eauto. ss.
    + esplits; [|econs]; eauto. rewrite plus_n_O at 1.
      exploit concat_nth_error; ss; eauto. ss.
    + esplits; [|econs]; eauto. rewrite plus_n_O at 1.
      exploit concat_nth_error; ss; eauto. ss.
    + esplits; [|econs]; eauto. rewrite plus_n_O at 1.
      exploit concat_nth_error; ss; eauto. ss.
    + esplits; [|econs]; eauto. rewrite plus_n_O at 1.
      exploit concat_nth_error; ss; eauto. ss.
Qed.

Lemma uslh_inst_np_length_aux
    i l o c is' np
  (USLH: uslh_inst i l o c = (is', np)):
  Datatypes.length np = match i with
                        | <{{ branch _ to _ }}> => 1
                        | _ => 0
                        end.
Proof.
  destruct i; ss; unfold MiniCET.uslh_ret in *; clarify.
  eapply bind_inv in USLH. des. subst.
  unfold add_block_M, add_block in USLH. ss. clarify.
Qed.

Lemma uslh_blk_np_length_aux1
  l blk n c blk' np
  (USLH: mapM (fun '(o, i) => uslh_inst i l o)
              (combine (_offset_uslh blk n) blk) c = (blk', np)):
  Datatypes.length np = _branch_in_block blk.
Proof.
  ginduction blk; ss; ii.
  { unfold mapM in *. ss. unfold MiniCET.uslh_ret in *; ss. clarify. }
  exploit mapM_cons_inv; eauto. i. des. subst.
  exploit IHblk; eauto. i. rewrite length_app.
  rewrite x2. unfold _branch_in_block at 2. ss.
  rewrite fold_left_init_0.
  clear -x0. eapply uslh_inst_np_length_aux in x0.
  rewrite x0. unfold _branch_in_block. lia.
Qed.

Lemma uslh_blk_np_length_aux2
  n blk c res_hd np_hd
  (USLH: uslh_blk (n, blk) c = (res_hd, np_hd)):
  branch_in_block blk = Datatypes.length np_hd.
Proof.
  destruct blk. unfold uslh_blk in USLH.
  eapply bind_inv in USLH. des. subst.
  unfold branch_in_block. ss.
  assert (Datatypes.length pm = _branch_in_block l).
  { clear -USLH. ii. unfold concatM in *. eapply bind_inv in USLH. des.
    ss. unfold MiniCET.uslh_ret in *. clarify.
    rewrite app_nil_r. eapply uslh_blk_np_length_aux1.
    erewrite <- uslh_offset_uslh_add_index; eauto.
    unfold offset_uslh. eauto. }
  rewrite app_length. rewrite <- H; eauto.
  des_ifs; unfold MiniCET.uslh_ret in *; clarify; ss; lia.
Qed.

Lemma mapM_nil {A B} (f: A -> M B) (l:list A) c l' np
  (NIL: l = [])
  (MM: mapM f l c = (l', np)) :
  l' = [] /\ np = [].
Proof.
  subst. unfold mapM in *. ss. unfold MiniCET.uslh_ret in *. clarify.
Qed.

Lemma uslh_blk_np_length_aux p c p' np
  (USLH: mapM uslh_blk (add_index p) c = (p', np)) :
  branch_in_prog p = Datatypes.length np.
Proof.
  unfold add_index in *. remember 0. clear Heqn.
  ginduction p; ss; ii.
  - eapply mapM_nil in USLH; eauto. des; subst; ss.
  - exploit mapM_cons_inv; eauto. i. des. subst.
    exploit IHp; eauto. i.
    unfold branch_in_prog. simpl. rewrite fold_left_init_0.
    rewrite app_length.
    eapply uslh_blk_np_length_aux2 in x0.
    rewrite x0, <- x2. unfold branch_in_prog. lia.
Qed.

Lemma firstn_add_index_comm {A} (p: list A) n:
  firstn n (add_index p) = add_index (firstn n p).
Proof.
  unfold add_index. remember 0. clear Heqn0.
  ginduction p; ss; ii.
  { destruct n; ss. }
  destruct n; [ss|].
  do 2 rewrite firstn_cons. erewrite IHp. ss.
Qed.

Lemma uslh_blk_np_length p l:
  branch_in_prog_before p l = len_before uslh_blk (add_index p) l (Datatypes.length p).
Proof.
  unfold branch_in_prog_before, len_before.
  des_ifs. rewrite firstn_add_index_comm in Heq.
  eapply uslh_blk_np_length_aux in Heq. auto.
Qed.

Lemma uslh_inst_np_length blk is_proc o lpc opc c :
  offset_branch_before (blk, is_proc) o = len_before (fun i => uslh_inst i lpc opc) blk o c.
Proof.
  unfold offset_branch_before. ss.
  ginduction blk; ss; ii.
  { unfold _offset_branch_before, len_before. destruct o; ss. }
  destruct o; ss.
  unfold _offset_branch_before, len_before. ss. des_ifs.
  eapply mapM_cons_inv in Heq. des. subst.
  exploit IHblk; eauto. unfold _offset_branch_before.
  instantiate (2:=o). instantiate (1:= (c + Datatypes.length np_hd)).
  unfold len_before. des_ifs. i.
  unfold _branch_in_block. ss. rewrite fold_left_init_0.
  rewrite length_app. unfold _branch_in_block in x0.
  rewrite x0. erewrite Heq1 in Heq0. clarify. clear - Heq.
  eapply uslh_inst_np_length_aux in Heq. rewrite Heq. lia.
Qed.

Lemma uslh_inst_np_length_same blk ll o lpc opc c (LEN: Datatypes.length ll = Datatypes.length blk) :
  len_before (fun i => uslh_inst i lpc opc) blk o c =
  len_before (fun '(opc', i) => uslh_inst i lpc opc') (combine ll blk) o c.
Proof.
  ginduction blk; ss; i.
  { unfold len_before. rewrite combine_nil. do 2 rewrite firstn_nil. unfold mapM in *. ss. }
  destruct ll; ss. destruct o.
  { unfold len_before. ss. }
  unfold len_before. do 2 rewrite firstn_cons. des_ifs_safe.
  eapply mapM_cons_inv in Heq. des. subst.
  eapply mapM_cons_inv in Heq0. des. subst.
  unfold len_before in *.
  specialize (IHblk ll o lpc opc (c + Datatypes.length np_hd)).
  rewrite Heq1 in IHblk. ss.
  eapply uslh_inst_np_length_aux in Heq0, Heq. rewrite <- Heq in Heq0.
  rewrite Heq0 in Heq2. unfold offset_uslh in IHblk. ss. rewrite Heq2 in IHblk.
  do 2 rewrite length_app. lia.
Qed.

Lemma _offset_uslh_length blk n :
  Datatypes.length (_offset_uslh blk n) = Datatypes.length blk.
Proof. ginduction blk; ss; i; eauto. Qed.

Lemma offset_uslh_length blk b :
  Datatypes.length (offset_uslh (blk, b)) = Datatypes.length blk.
Proof. eapply _offset_uslh_length; eauto. Qed.

Lemma src_inv_branch_blk
  blk o e l lpc n c blk' np
  (INST: nth_error blk o = Some <{{ branch e to l }}>)
  (USLH: mapM (fun '(o, i) => uslh_inst i lpc o)
              (combine (_offset_uslh blk n) blk) c = (blk', np)):
  nth_error np (_offset_branch_before blk o) =
    Some ([<{{ msf := (~ (msf = 1) ? 0 : e) ? 1 : msf }}>; <{{ jump l }}>], false).
Proof.
  ginduction blk; ii.
  { rewrite nth_error_nil in INST. clarify. }
  destruct o; ss; clarify.
  - eapply mapM_cons_inv in USLH. des. subst.
    ss. eapply bind_inv in USLH. des. subst.
    unfold add_block_M, add_block in USLH. clarify.
  - exploit mapM_cons_inv; eauto. i. des. subst.
    unfold _offset_branch_before. rewrite firstn_cons.
    unfold _branch_in_block. ss. rewrite fold_left_init_0.
    rewrite add_comm. exploit uslh_inst_np_length_aux; eauto. i.
    rewrite nth_error_app2; try lia.
    rewrite add_comm, x2, add_sub. eapply IHblk; eauto.
Qed.

Lemma src_inv_branch_prog p tp pc tpc e l e' l'
  (TRP: uslh_prog p = tp)
  (PS: pc_sync p pc = Some tpc)
  (INST: p[[pc]] = Some <{{ branch e to l }}>)
  (NTH: match_branch_target p pc = Some l')
  (COND: e' = <{{ (msf = 1) ? 0 : e }}>) :
  nth_error tp l' = Some ([<{{ msf := (~ e') ? 1 : msf }}>; <{{ jump l }}>], false).
Proof.
  destruct pc as [b o]. ss. des_ifs.
  destruct p0 as [blk is_proc]. ss.
  unfold uslh_prog. des_ifs.

  assert(LENP: Datatypes.length p = Datatypes.length l1).
  { eapply mapM_perserve_len in Heq2. rewrite <- Heq2. symmetry. eapply length_add_index. }

  rewrite LENP.
  rewrite nth_error_app. des_ifs.
  { rewrite ltb_lt in Heq3. lia. }
  rewrite <- add_assoc, add_comm. rewrite add_sub.

  exploit nth_error_add_index; try eapply Heq. i.
  exploit firstn_skipn_middle; eauto. i.
  rewrite <- x1 in Heq2.
  exploit mapM_app_inv; eauto. i. des; subst.
  exploit mapM_cons_inv; eauto. i. des; subst.

  rewrite firstn_add_index_comm in x2.
  exploit uslh_blk_np_length_aux; try eapply x2. i.
  unfold branch_in_prog_before. rewrite x6.

  rewrite nth_error_app2; try lia. rewrite add_comm, add_sub.
  rewrite nth_error_app1.
  2:{ erewrite uslh_inst_np_length.
      instantiate (1:=(Datatypes.length p + Datatypes.length np1)).
      erewrite <- uslh_inst_np_length. instantiate (1:= is_proc).
      eapply uslh_blk_np_length_aux2 in x4. rewrite <- x4.
      unfold offset_branch_before, branch_in_block. simpl.
      clear - INST. ginduction blk; ss; ii.
      - rewrite nth_error_nil in INST. clarify.
      - destruct o; ss; clarify.
        + unfold _offset_branch_before, _branch_in_block. ss.
          rewrite fold_left_init_0. lia.
        + unfold _branch_in_block. ss. rewrite fold_left_init_0.
          unfold _offset_branch_before, _branch_in_block. ss.
          rewrite fold_left_init_0. exploit IHblk; eauto. i.
          unfold _offset_branch_before, _branch_in_block in x0. lia. }
  unfold uslh_blk in x4. exploit bind_inv; try eapply x4. i. des; subst.
  assert (pf = []).
  { des_ifs; ss; unfold MiniCET.uslh_ret in *; clarify. }
  subst. rewrite app_nil_r.

  eapply bind_inv in x7. des. subst.
  assert (pf = []).
  { ss; unfold MiniCET.uslh_ret in *; clarify. }
  subst. rewrite app_nil_r. eapply src_inv_branch_blk; eauto.
Unshelve. all: econs.
Qed.

Lemma no_ct_prog_src p pc
  (NCT: no_ct_prog p)
  (INST: p[[pc]] = Some <{{ ctarget }}>) :
  False.
Proof.
  unfold no_ct_prog in NCT.
  destruct (split p) as (bs & bools) eqn:Hsplitp.
  rewrite Forall_forall in NCT. destruct pc; ss. des_ifs.
  exploit nth_error_In; try eapply Heq. i.
  eapply in_split_l in x0. rewrite Hsplitp in x0. ss.
  apply NCT in x0. unfold no_ct_blk in x0. rewrite Forall_forall in x0.
  exploit nth_error_In; eauto. i. eapply x0 in x1. ss.
Qed.

Lemma src_inv p tp pc tpc i
  (NCT: no_ct_prog p)
  (TRP: uslh_prog p = tp)
  (PS: pc_sync p pc = Some tpc)
  (INST: p[[pc]] = Some <{{ i }}>) :
  exists i', tp[[tpc]] = Some <{{ i' }}> /\ match_inst_uslh p pc i i'.
Proof.
  assert (SDEC: simple_inst i \/ ~ (simple_inst i)).
  { destruct i; ss; auto. }
  destruct SDEC as [SIMP | SIMP].
  { exploit src_simple_inv; eauto. i. des. esplits; eauto.
    econs; eauto. }

  destruct pc as [l o]. simpl in INST. des_ifs. destruct p0 as [blk is_proc].
  hexploit label_inv; eauto. i. des.
  simpl in PS. des_ifs_safe. simpl in INST. simpl. rewrite H.
  destruct blk' as [blk' is_proc']. simpl.
  eapply bind_inv in H0. des. clarify.
  unfold concatM in H0. eapply bind_inv in H0. des.
  ss. unfold MiniCET.uslh_ret in *. clarify.
  erewrite uslh_offset_uslh_add_index in H0; eauto.

  hexploit offset_eq_aux; eauto.
  { simpl. rewrite nth_error_map in Heq0. unfold option_map in Heq0. des_ifs_safe.
    unfold offset_uslh in Heq1. eauto. }
  { simpl. rewrite <- nth_error_Some. ii. clarify. }
  i. subst. simpl.
  destruct i; try (sfby (ss; clarify)).
  3:{ clear -NCT Heq INST. exfalso. red in NCT. des_ifs.
      eapply nth_error_In in Heq. eapply in_split_l in Heq. rewrite Heq0 in *. ss.
      eapply nth_error_In in INST. eapply Forall_forall in NCT; eauto.
      red in NCT. eapply Forall_forall in NCT; eauto. red in NCT. clarify. }


  - dup Heq0. rename Heq2 into TRNTH.
    rewrite nth_error_map in Heq0. unfold option_map in Heq0.
    des_ifs_safe. unfold offset_uslh in Heq1.

    exploit mapM_nth_error_strong; eauto.
    { eapply _offset_uslh_combine; eauto. }
    i. des.

    assert (exists i', nth_error (List.concat a0) (prefix_offset a0 o 0) = Some i'
               /\ match_inst_uslh p (l, o) <{{ branch e to l1 }}> i').
    { replace (prefix_offset a0 o 0) with (prefix_offset a0 o 0 + 0) by lia.
      simpl in x1. eapply bind_inv in x1. des. subst. unfold MiniCET.uslh_ret in *. clarify.
      exploit (concat_nth_error a0 _ _ 0); eauto; [ss|]. i.
      esplits; eauto.
      assert (match_branch_target p (l, o) = Some a).
      { ss. rewrite Heq2.
        unfold add_block_M, add_block in x1. clarify.
        rewrite uslh_blk_np_length.
        f_equal. f_equal.
        erewrite <- uslh_inst_np_length_same with (opc := 0).
        2:{ eapply offset_uslh_length. }
        erewrite uslh_inst_np_length; eauto. }
      econs 2; eauto.
      { eapply src_inv_branch_prog; eauto; cycle 1.
        { ss. des_ifs. }
        { simpl. rewrite TRNTH. unfold offset_uslh. ss. rewrite Heq1. eauto. } }
      { simpl. rewrite TRNTH. unfold offset_uslh. ss. rewrite Heq1. eauto. }
      simpl. rewrite H. ss. des_ifs.
      - replace (prefix_offset a0 o 2) with (S (S (prefix_offset a0 o 0))); simpl.
        2:{ unfold prefix_offset at 2. rewrite fold_left_init_0 at 1. unfold prefix_offset. lia. }
        eapply concat_nth_error; eauto.
      - eapply concat_nth_error; eauto. }
    des_ifs; eauto.
    replace (prefix_offset a0 o 2) with (S (S (prefix_offset a0 o 0))); simpl; eauto.
    unfold prefix_offset at 2. rewrite fold_left_init_0 at 1. unfold prefix_offset. lia.

  - dup Heq0. rename Heq2 into TRNTH.
    rewrite nth_error_map in Heq0. unfold option_map in Heq0.
    des_ifs_safe. unfold offset_uslh in Heq1.

    exploit mapM_nth_error_strong; eauto.
    { eapply _offset_uslh_combine; eauto. }
    i. des.

    assert (exists i', nth_error (List.concat a0) (prefix_offset a0 o 0) = Some i'
              /\  match_inst_uslh p (l, o) <{{ call fp }}> i').
    { replace (prefix_offset a0 o 0) with (prefix_offset a0 o 0 + 0) by lia.
      ss. unfold MiniCET.uslh_ret in *. clarify.

      exploit (concat_nth_error a0 _ _ 0); eauto; [ss|]. i.
      esplits; eauto.
      econs 3; eauto.
      { ss. rewrite TRNTH. unfold offset_uslh. ss. rewrite Heq1. eauto. }
      { simpl. rewrite H. simpl. des_ifs.
        - replace (prefix_offset a0 o 2) with (S (S (prefix_offset a0 o 0))); simpl.
          2:{ unfold prefix_offset at 2. rewrite fold_left_init_0 at 1. unfold prefix_offset. lia. }
          eapply concat_nth_error; eauto.
        - eapply concat_nth_error; eauto. }
      { simpl. rewrite H. simpl. des_ifs.
        - replace (prefix_offset a0 o 2) with (S (S (prefix_offset a0 o 0))); simpl.
          2:{ unfold prefix_offset at 2. rewrite fold_left_init_0 at 1. unfold prefix_offset. lia. }
          eapply concat_nth_error; eauto.
          simpl. repeat f_equal. unfold prefix_offset. rewrite fold_left_init_0. lia.
        - eapply concat_nth_error; eauto. } }
    des_ifs; eauto.
    replace (prefix_offset a0 o 2) with (S (S (prefix_offset a0 o 0))); simpl; eauto.
    unfold prefix_offset at 2. rewrite fold_left_init_0 at 1. unfold prefix_offset. lia.

  - dup Heq0. rename Heq2 into TRNTH.
    rewrite nth_error_map in Heq0. unfold option_map in Heq0.
    des_ifs_safe. unfold offset_uslh in Heq1.

    exploit mapM_nth_error_strong; eauto.
    { eapply _offset_uslh_combine; eauto. }
    i. des.

    assert (exists i', nth_error (List.concat a0) (prefix_offset a0 o 0) = Some i'
                /\ match_inst_uslh p (l, o) <{{ ret }}> i').
    {
        replace (prefix_offset a0 o 0) with (prefix_offset a0 o 0 + 0) by lia.
        ss. unfold MiniCET.uslh_ret in *. clarify.

        exploit (concat_nth_error a0 _ _ 0); eauto; [ss|]. i.
        esplits; eauto.
        econs 4; eauto.
        { ss. rewrite TRNTH. unfold offset_uslh. ss. rewrite Heq1. eauto. }
        {
            simpl. rewrite H. simpl. des_ifs.
            - replace (prefix_offset a0 o 2) with (S (S (prefix_offset a0 o 0))); simpl.
              2:{ unfold prefix_offset at 2. rewrite fold_left_init_0 at 1. unfold prefix_offset. lia. }
              eapply concat_nth_error; eauto.
            - eapply concat_nth_error; eauto.
        }
    }
    des_ifs; eauto.
    replace (prefix_offset a0 o 2) with (S (S (prefix_offset a0 o 0))); simpl; eauto.
    unfold prefix_offset at 2. rewrite fold_left_init_0 at 1. unfold prefix_offset. lia.
Qed.

Lemma firstnth_error : forall (l: list inst) (n: nat) (i: inst),
  nth_error l n = Some i ->
  firstn (S n) l = firstn n l ++ [i].
Proof.
  induction l as [|h t IHl]; intros.
  - rewrite nth_error_nil in H; discriminate.
  - rewrite firstn_cons. replace (h :: t) with ([h] ++ t) by auto.
    replace (h :: firstn n t) with ([h] ++ (firstn n t)) by auto.
    rewrite firstn_app. simpl.
    rewrite nth_error_cons in H. destruct n as [|n']; clarify.
    specialize IHl with (n:=n') (i:=i). specialize (IHl H).
    rewrite IHl. simpl. rewrite firstn_nil. simpl. rewrite sub_0_r. auto.
Qed.

Lemma ret_sync_same_label p l1 o1 l2 o2:
    ret_sync p (l1, o1) = Some (l2, o2) ->
    l1 = l2.
Proof.
    unfold ret_sync, pc_sync. i.
    destruct o1. 1: discriminate.
    destruct (p [[(l1, o1)]]). 2: discriminate.
    destruct i; try discriminate.
    destruct (nth_error (map offset_uslh p) l1). 2: discriminate.
    destruct (nth_error l o1). 2: discriminate.
    now inv H.
Qed.

Lemma ret_sync_nonzero p l1 o1 l2 o2:
    ret_sync p (l1, o1) = Some (l2, o2) ->
    o2 <> 0.
Proof.
    unfold ret_sync, pc_sync. i.
    destruct o1. 1: discriminate.
    destruct (p [[(l1, o1)]]). 2: discriminate.
    destruct i; try discriminate.
    destruct (nth_error (map offset_uslh p) l1). 2: discriminate.
    destruct (nth_error l o1). 2: discriminate.
    inv H. lia.
Qed.

Lemma ret_sync_inj p l1 o1 l1' o1' l2 o2:
    ret_sync p (l1, o1) = Some (l2, o2) ->
    ret_sync p (l1', o1') = Some (l2, o2) ->
    l1 = l1' /\ o1 = o1'.
Proof.
    i. dup H. dup H0.
    apply ret_sync_same_label in H1 as ->, H2 as ->. split; [reflexivity|].
    unfold ret_sync in *.
    destruct o1, o1'; try discriminate. f_equal.
    destruct (p [[(l2, o1)]]), (p [[(l2, o1')]]); try discriminate.
    destruct i, i0; try discriminate.
    unfold pc_sync in *. rewrite nth_error_map in H, H0.
    destruct (nth_error p l2). 2: discriminate.
    ss.
    assert (o1 < Datatypes.length (offset_uslh p0)).
    { clear - H. apply nth_error_Some. destruct (nth_error (offset_uslh p0) o1); discriminate. }
    rewrite <- H0 in H. clear H0.
    assert (nth_error (offset_uslh p0) o1 = nth_error (offset_uslh p0) o1').
    { destruct (nth_error (offset_uslh p0) o1), (nth_error (offset_uslh p0) o1'); try discriminate. 2: reflexivity. inv H. f_equal. lia. }
    exploit NoDup_nth_error. i. des. apply x0; eauto.
    clear.
    destruct p0. unfold offset_uslh.
    generalize (if snd (l, b) then 2 else 0) as x.
    enough (forall x, NoDup (_offset_uslh l x) /\ Forall (fun y => y >= x) (_offset_uslh l x)).
    { i. now apply H. }
    induction l.
    - i. split; constructor.
    - i. cbn. split.
      + constructor. 2: apply IHl.
        specialize (IHl (x + uslh_inst_sz a)) as [_ IHl]. rewrite Forall_forall in IHl.
        intro H. apply IHl in H.
        assert (uslh_inst_sz a > 0). { destruct a; ss; lia. }
        lia.
      + specialize (IHl (x + uslh_inst_sz a)) as [_ IHl].
        constructor. 1: auto.
        eapply Forall_impl. 2: eassumption.
        ss. lia.
Qed.

Lemma match_dir_inj p d1 d2 d':
    match_dir p d1 d' ->
    match_dir p d2 d' ->
    d1 = d2.
Proof.
    destruct d1, d2, d'; ss; try congruence.
    destruct lo, lo0, lo1. i.
    exploit ret_sync_inj; [exact H | exact H0 |].
    i. des. subst. reflexivity.
Qed.

Lemma match_ob_inj p o1 o2 o':
    match_ob p o1 o' ->
    match_ob p o2 o' ->
    o1 = o2.
Proof.
    destruct o1, o2, o'; try contradiction; try congruence.
    all: destruct l.
    all: try (destruct n4; contradiction).
    all: try (destruct n2; contradiction).
    all: try (destruct n0; contradiction).
    all: try (destruct n1; contradiction).
    destruct l0, l1. unfold match_ob. destruct n0, n4, n2; try contradiction.
    1: congruence.
    i. exploit ret_sync_inj; [exact H|exact H0|].
    now intros [-> ->%succ_inj].
Qed.

Lemma match_ob_functional p o o'1 o'2:
    match_ob p o o'1 ->
    match_ob p o o'2 ->
    o'1 = o'2.
Proof.
    destruct o, o'1, o'2; try contradiction; try congruence.
    all: destruct l.
    all: match goal with
         | |- match_ob _ (OCall (_, ?n)) _ -> _ => try (destruct n; contradiction)
         end.
    destruct l0, l1. unfold match_ob. destruct n0, n4, n2; try contradiction.
    - congruence.
    - unfold ret_sync.
      destruct (p [[(n, n0)]]); try discriminate.
      destruct i; try discriminate.
      destruct (pc_sync p (n, n0)); try discriminate.
      destruct c. i. inv H. inv H0. reflexivity.
Qed.

Lemma eval_regs_eq : forall p (r r': reg) (e: exp),
   e_unused msf e ->
   e_unused callee e ->
   wf_exp p e = true ->
   Rsync1 p r r' ->
   val_match p (eval r e) (eval r' e).
Proof.
  intros. ginduction e; ss; ii.
  - ss. assert (x <> msf /\ x <> callee) by (split; auto).
    apply H2 in H3. simpl. eauto.
  - apply andb_prop in H1. des.
    exploit IHe1; eauto. i.
    exploit IHe2; eauto. i.
    unfold eval_binop.
    destruct (eval r e1), (eval r e2), (eval r' e1), (eval r' e2); ss; subst.
    all: try (destruct pc; contradiction). 1: reflexivity.
    + destruct pc0; contradiction.
    + destruct o; ss. destruct pc, pc0, pc1, pc2. ss. destruct (n0 =? 0)%nat eqn:?, (n2 =? 0)%nat eqn:?; des; subst.
      * apply Nat.eqb_eq in Heqb, Heqb0. subst. reflexivity.
* assert ((n0 =? n2)%nat = false) as ->. { destruct n0, n2; ss. }
        rewrite andb_false_r. apply ret_sync_nonzero in x1.
        destruct n6; ss. now rewrite andb_false_r.
      * assert ((n0 =? n2)%nat = false) as ->. { destruct n0, n2; ss. }
        rewrite andb_false_r. apply ret_sync_nonzero in x0.
        destruct n4; ss. now rewrite andb_false_r.
      * destruct (n =? n1)%nat eqn:?, (n0 =? n2)%nat eqn:?; ss.
        { apply Nat.eqb_eq in Heqb1, Heqb2. subst. rewrite x1 in x0. inv x0. rewrite! Nat.eqb_refl. reflexivity. }
        { assert ((n3, n4) <> (n5, n6)).
          - intro. clarify. eapply ret_sync_inj in x1. 2: exact x0.
            des. clarify. rewrite Nat.eqb_refl in Heqb2. discriminate.
          - destruct (n3 =? n5)%nat eqn: ?. 2: reflexivity.
            destruct (n4 =? n6)%nat eqn: ?. 2: reflexivity.
            rewrite Nat.eqb_eq in Heqb3, Heqb4. clarify.
        }
        { apply ret_sync_same_label in x0, x1. clarify. }
        { apply ret_sync_same_label in x0, x1. clarify. }
    + destruct pc0; contradiction.
  - ss. destruct H, H0, H3, H4.
    eapply andb_prop in H1. des. eapply andb_prop in H1. des.
    exploit IHe1; eauto. exploit IHe2; eauto. exploit IHe3; eauto. i.
    destruct (eval r e1), (eval r' e1); ss; subst.
    2: (destruct pc; contradiction).
    destruct (not_zero n0); assumption.
  - des_ifs.
    { split; auto. rewrite Nat.eqb_eq in Heq. auto. }
Qed.

Lemma eval_regs_eq_nat : forall p (r r': reg) (e: exp),
   e_unused msf e ->
   e_unused callee e ->
   wf_exp p e = true ->
   Rsync1 p r r' ->
   to_nat (eval r e) = to_nat (eval r' e).
Proof.
  i. exploit eval_regs_eq; eauto. i.
  unfold val_match in x0. des_ifs; ss.
Qed.

Lemma wf_prog_lookup p pc i
  (WF: wf_prog p)
  (INST: p [[pc]] = Some i) :
  wf_instr p i.
Proof.
  destruct pc; ss. des_ifs_safe. inv WF.
  rewrite Forall_forall in H0. eapply nth_error_In in Heq.
  eapply H0 in Heq. unfold wf_block in Heq. des.
  rewrite Forall_forall in Heq1. eapply nth_error_In in INST. eauto.
Qed.

Lemma unused_prog_lookup x p pc i
  (UNUSED: unused_prog x p)
  (INST: p [[pc]] = Some i) :
  i_unused x i.
Proof.
  unfold unused_prog in *. destruct pc; ss. des_ifs_safe.
  rewrite Forall_forall in UNUSED. eapply nth_error_In in Heq.
  exploit in_split_l; eauto. i. rewrite Heq0 in x1. ss.
  exploit UNUSED; eauto. i. unfold b_unused in x2.
  rewrite Forall_forall in x2. eapply nth_error_In in INST. eauto.
Qed.

Lemma no_ct_prog_cons b p
  (NCT: no_ct_prog (b::p)) :
  no_ct_blk (fst b) /\ no_ct_prog p.
Proof.
  destruct b. ss. unfold no_ct_prog in *. des_ifs.
  assert (l2 = l::l0 /\ l3 = b::l1).
  { clear -Heq0 Heq. ginduction p; ss; ii; clarify.
    des_ifs. }
  des; subst. inv NCT. eauto.
Qed.

Lemma no_ct_prog_In blk is_ct p
  (IN: In (blk, is_ct) p)
  (NCT: no_ct_prog p) :
  no_ct_blk blk.
Proof.
  ginduction p; ss; ii. eapply no_ct_prog_cons in NCT.
  des; subst; eauto.
Qed.

Lemma split_app
  {A B} (l1 l2: list (A * B))
  sl sl' sl1 sl1' sl2 sl2'
  (SP1: split (l1 ++ l2) = (sl, sl'))
  (SP2: split l1 = (sl1, sl1'))
  (SP3: split l2 = (sl2, sl2')) :
  sl = sl1 ++ sl2 /\ sl' = sl1' ++ sl2'.
Proof.
  ginduction l1; ii.
  { ss. clarify. rewrite SP1 in SP3. clarify. }
  destruct a as [a b]. ss. des_ifs_safe.
  exploit IHl1; eauto. i. des. subst; auto.
Qed.

Lemma no_ct_prog_app l1 l2:
  no_ct_prog (l1 ++ l2) <-> (no_ct_prog l1 /\ no_ct_prog l2).
Proof.
  unfold no_ct_prog. des_ifs.
  exploit split_app; try eapply Heq; eauto. i. des; subst.
  rewrite Forall_app. auto.
Qed.

Lemma new_prog_no_ct_blk blk n c res np
  (USLH: uslh_blk (n, blk) c = (res, np)):
  no_ct_prog np.
Proof.
  unfold uslh_blk in USLH. des_ifs_safe.
  eapply bind_inv in USLH. des. subst. unfold concatM in USLH.
  eapply bind_inv in USLH. des. subst. ss. unfold MiniCET.uslh_ret in *. clarify.
  assert (no_ct_prog pm0).
  { clear -USLH. unfold add_index_uslh in *.
    assert (Datatypes.length (_offset_uslh l (if b then 2 else 0)) = Datatypes.length l).
    { eapply _offset_uslh_length. }
    remember (_offset_uslh l (if b then 2 else 0)) as ll. clear Heqll.
    ginduction l; (try sfby ss); ii.
    - destruct ll; ss. unfold mapM in *. ss. unfold MiniCET.uslh_ret in *. clarify.
    - destruct ll; ss. unfold add_index_uslh in *. simpl in USLH.
      eapply mapM_cons_inv in USLH. des. subst.
      exploit IHl; try eapply USLH0; eauto. i. destruct a; ss; unfold MiniCET.uslh_ret in *; clarify. ss.
      eapply bind_inv in USLH. des. ss. subst. clarify.
      unfold add_block_M, add_block in USLH.
      rewrite app_nil_r. rewrite no_ct_prog_app. split; auto. clarify.
      red. des_ifs. ss. clarify. econs; eauto. repeat econs. }
  rewrite app_nil_r. rewrite no_ct_prog_app. split; auto. des_ifs; ss.
Qed.

Lemma new_prog_no_ct p c p' np
  (USLH: mapM uslh_blk (add_index p) c = (p', np)):
  no_ct_prog np.
Proof.
  unfold add_index in USLH. remember 0. clear Heqn.
  ginduction p; ss; ii.
  - unfold mapM in *. ss. unfold MiniCET.uslh_ret in USLH. clarify.
  - exploit mapM_cons_inv; eauto. i. des. subst.
    exploit IHp; eauto. i.
    assert (no_ct_prog np_hd).
    { eapply new_prog_no_ct_blk; eauto. }
    rewrite no_ct_prog_app. auto.
Qed.

Lemma uslh_blk_np_nonempty blk n c res np
  (USLH: uslh_blk (n, blk) c = (res, np)):
  Forall (fun b : list inst * bool => 0 < Datatypes.length (fst b)) np.
Proof.
  unfold uslh_blk in USLH. des_ifs_safe.
  eapply bind_inv in USLH. des. subst. unfold concatM in USLH.
  eapply bind_inv in USLH. des. subst. ss. unfold MiniCET.uslh_ret in *. clarify.
  assert (Forall (fun b : list inst * bool => 0 < Datatypes.length (fst b)) pm0).
  { clear -USLH. unfold add_index_uslh in *.
    assert (Datatypes.length (_offset_uslh l (if b then 2 else 0)) = Datatypes.length l).
    { eapply _offset_uslh_length. }
    remember (_offset_uslh l (if b then 2 else 0)) as ll. clear Heqll.
    ginduction l; (try sfby ss); ii.
    - destruct ll; ss. unfold mapM in *. ss. unfold MiniCET.uslh_ret in *. clarify.
    - destruct ll; ss. unfold add_index_uslh in *. simpl in USLH.
      eapply mapM_cons_inv in USLH. des. subst.
      exploit IHl; try eapply USLH0; eauto. i. destruct a; ss; unfold MiniCET.uslh_ret in *; clarify. ss.
      eapply bind_inv in USLH. des. ss. subst. clarify.
      unfold add_block_M, add_block in USLH.
      rewrite app_nil_r. rewrite Forall_app. split; auto. clarify.
      econs; [|econs]. ss. lia. }
  rewrite app_nil_r. rewrite Forall_app. split; auto. des_ifs; ss.
Qed.

Lemma new_prog_nonempty p c p' np
  (USLH: mapM uslh_blk (add_index p) c = (p', np)):
  Forall (fun b : list inst * bool => 0 < Datatypes.length (fst b)) np.
Proof.
  unfold add_index in USLH. remember 0 in USLH. clear Heqn.
  ginduction p; ss; ii.
  - unfold mapM in *. ss. unfold MiniCET.uslh_ret in USLH. clarify.
  - exploit mapM_cons_inv; eauto. i. des. subst.
    exploit IHp; eauto. i.
    assert (Forall (fun b : list inst * bool => 0 < Datatypes.length (fst b)) np_hd).
    { eapply uslh_blk_np_nonempty; eauto. }
    rewrite Forall_app. split; eauto.
Qed.

Lemma uslh_blk_nonempty_res blk n c res np
  (NE: 0 < Datatypes.length (fst blk))
  (USLH: uslh_blk (n, blk) c = (res, np)):
  0 < Datatypes.length (fst res).
Proof.
  destruct blk as [insts is_proc].
  unfold uslh_blk in USLH. des_ifs_safe.
  eapply bind_inv in USLH. des. subst. unfold concatM in USLH.
  eapply bind_inv in USLH. des. subst. ss. unfold MiniCET.uslh_ret in *. clarify.
  destruct is_proc.
  - clarify. ss. lia.
  - ss. clarify. ss. destruct insts; try (ss; lia).
    erewrite uslh_offset_uslh_add_index in USLH; eauto. ss.
    exploit mapM_cons_inv; try eapply USLH. i. des. clarify.
    destruct i; ss; unfold MiniCET.uslh_ret in *; clarify; ss; try lia.
    eapply bind_inv in x0. des. clarify. ss. lia.
Qed.

Lemma uslh_prog_nonempty_block p l blk
  (WFP: wf_prog p)
  (NTH: nth_error (uslh_prog p) l = Some blk) :
  0 < Datatypes.length (fst blk).
Proof.
  unfold uslh_prog in NTH. des_ifs_safe.
  exploit mapM_perserve_len; eauto. intros LEN. rewrite length_add_index in LEN.
  assert (l < Datatypes.length l0 \/ Datatypes.length l0 <= l) as [LT|GE] by lia.
  - rewrite nth_error_app1 in NTH; auto.
    assert (exists src, nth_error p l = Some src) as [src SRC].
    { destruct (nth_error p l) eqn:E; [eauto|].
      exfalso. rewrite nth_error_None in E. lia. }
    exploit nth_error_add_index; eauto. intros AI.
    exploit mapM_nth_error; try eapply Heq; try eapply AI.
    intros (blk' & c' & np' & NTH' & USLH').
    rewrite NTH' in NTH. clarify.
    eapply uslh_blk_nonempty_res; eauto.
    inv WFP. rewrite Forall_forall in H0.
    eapply nth_error_In in SRC. eapply H0 in SRC.
    red in SRC. des. auto.
  - rewrite nth_error_app2 in NTH; auto.
    exploit new_prog_nonempty; eauto. intros NE.
    rewrite Forall_forall in NE. eapply nth_error_In in NTH.
    eapply NE in NTH. auto.
Qed.

Lemma new_prog_ct_cut p c p' np l o
    (USLH: mapM uslh_blk (add_index p) c = (p', np))
    (INST: (p' ++ np) [[(l, o)]] = Some <{{ ctarget }}>)
    (NCT: no_ct_prog np):
  p'[[(l, o)]] = Some <{{ ctarget }}>.
Proof.
  ss. des_ifs_safe.
  assert (l < Datatypes.length p' \/ Datatypes.length p' <= l) by lia.
  des.
  - rewrite nth_error_app1 in Heq; eauto. rewrite Heq; auto.
  - exfalso. rewrite nth_error_app2 in Heq; auto.
    eapply nth_error_In in Heq, INST. red in NCT. des_ifs.
    eapply in_split_l in Heq. rewrite Heq0 in Heq. ss.
    rewrite Forall_forall in NCT. eapply NCT in Heq. red in Heq.
    rewrite Forall_forall in Heq. eapply Heq in INST. ss.
Qed.

Lemma no_ctarget_exists_blk blk l c blk' np'
    (NCT: no_ct_blk blk)
    (USLH: uslh_blk (l, (blk, false)) c = (blk', np')) :
  no_ct_blk (fst blk') /\ snd blk' = false.
Proof.
  unfold uslh_blk in USLH. eapply bind_inv in USLH. des. subst.
  ss. unfold MiniCET.uslh_ret in USLH0. clarify. simpl. split; auto.
  unfold concatM in USLH. eapply bind_inv in USLH. des. ss.
  unfold MiniCET.uslh_ret in *. clarify.
  red. rewrite Forall_concat.
  unfold add_index_uslh in *.
  assert (Datatypes.length (_offset_uslh blk 0) = Datatypes.length blk).
  { eapply _offset_uslh_length. }
  remember (_offset_uslh blk 0) as ll. clear Heqll.
  ginduction blk; ii.
  - destruct ll; ss. unfold mapM in USLH. ss. unfold MiniCET.uslh_ret in USLH. clarify.
  - destruct ll; ss. exploit mapM_cons_inv; eauto. i. des; subst.
    inv NCT. eapply IHblk in H3; try eapply x1; eauto.
    econs; eauto. clear - x0 H2.
    destruct a; ss; unfold MiniCET.uslh_ret in *; clarify; repeat econs.
    eapply bind_inv in x0. des. clarify. repeat econs.
Qed.

Lemma no_ctarget_exists p l blk
  (NCT : no_ct_prog p)
  (LTH: nth_error p l = Some (blk, false)) :
  forall o, (uslh_prog p)[[(l, o)]] <> Some <{{ ctarget }}>.
Proof.
  unfold uslh_prog. des_ifs. ii.

  assert (NCT0: no_ct_prog p0).
  { eapply new_prog_no_ct; eauto. }
  eapply new_prog_ct_cut in H; eauto.
  des. exploit mapM_nth_error_strong; eauto.
  { eapply nth_error_add_index; eauto. }
  i. des.
  assert (no_ct_blk (fst blk') /\ snd blk' = false).
  { eapply no_ctarget_exists_blk; eauto. eapply no_ct_prog_In in NCT; eauto.
    eapply nth_error_In; eauto. }
  des. ss. des_ifs. eapply nth_error_In in H.
  red in H0. rewrite Forall_forall in H0. eapply H0 in H. ss.
Qed.

Lemma head_call_target p pc
    (UNUSED: unused_prog callee p)
    (NCT: no_ct_prog p)
    (INST: (uslh_prog p)[[pc]] = Some <{{ ctarget }}>) :
  exists l blk, pc = (l, 0)
  /\ nth_error (uslh_prog p) l = Some (blk, true)
  /\ (uslh_prog p)[[pc+1]] = Some <{{ msf := (callee = (& pc)) ? msf : 1 }}>.
Proof.
  destruct pc as [l o]. exists l.
  unfold uslh_prog in *. des_ifs_safe.
  assert (no_ct_prog p0).
  { eapply new_prog_no_ct; eauto. }
  assert (INST': l0[[(l, o)]] = Some <{{ ctarget }}>).
  { eapply new_prog_ct_cut; eauto. }
  clear INST.
  destruct (nth_error p l) eqn:LTH; cycle 1.
  { exfalso. exploit mapM_perserve_len; eauto. i.
    rewrite length_add_index in x0. ss. des_ifs_safe.
    rewrite nth_error_None, x0, <- nth_error_None in LTH. clarify. }
  destruct p1 as [blk is_proc].
  exploit nth_error_add_index; eauto. i.
  exploit mapM_nth_error_strong; eauto. i. des.
  destruct is_proc; cycle 1.
  { exfalso. hexploit no_ctarget_exists; try eapply NCT; eauto.
    instantiate (1:=o). ii. unfold uslh_prog in H0. des_ifs_safe.
    assert (nth_error (l0 ++ p0) l = Some blk').
    { erewrite nth_error_app1; eauto.
      rewrite <- nth_error_Some. ii; clarify. }
    ss. des_ifs. }
  unfold uslh_blk in x2.
  eapply bind_inv in x2. des. subst.
  assert (NCTS: no_ct_blk blk).
  { eapply nth_error_In in LTH. eapply no_ct_prog_In; eauto. }
  assert (no_ct_blk a).
  { clear - x2 NCTS. unfold concatM in x2. eapply bind_inv in x2. des; subst.
    ss. unfold MiniCET.uslh_ret in x0. clarify.
    remember (Datatypes.length p + len_before uslh_blk (add_index p) l (Datatypes.length p)).
    clear Heqn. clear -x2 NCTS.
    unfold add_index_uslh in *.
    assert (Datatypes.length (_offset_uslh blk 2) = Datatypes.length blk).
    { eapply _offset_uslh_length. }
    remember (_offset_uslh blk 2) as ll. clear Heqll.

    ginduction blk; ss; ii.
    - destruct ll; ss. unfold mapM in x2. ss. unfold MiniCET.uslh_ret in x2. clarify.
    - destruct ll; ss. inv NCTS. eapply mapM_cons_inv in x2. des; subst.
      exploit IHblk; try eapply x0; eauto. i.
      unfold no_ct_blk in *. rewrite Forall_concat in *. econs; eauto.
      clear - H2 x2.
      destruct a; ss; unfold MiniCET.uslh_ret in *; clarify; try econs; ss.
      + eapply bind_inv in x2. des. clarify. econs; eauto.
      + econs; eauto.
      + repeat econs. }
  ss. unfold MiniCET.uslh_ret in x4. clarify.
  exists (<{{ ctarget }}> :: <{{ msf := (callee = (& (l,0))) ? msf : 1 }}> :: a).
  rewrite nth_error_app1.
  2:{ rewrite <- nth_error_Some. ii; clarify. }
  destruct (eq_decidable o 0); subst; auto; cycle 1.
  { des_ifs_safe. ss.
    clear - H0 H INST'. destruct o; ss. destruct o; ss.
    eapply nth_error_In in INST'. eapply Forall_forall in H0; eauto. ss. }
  des_ifs.
Qed.

Lemma ctarget_exists p l blk
  (LTH: nth_error p l = Some (blk, true)) :
  (uslh_prog p)[[(l, 0)]] = Some <{{ ctarget }}>.
Proof.
  unfold uslh_prog. des_ifs_safe.
  exploit mapM_nth_error_strong; eauto.
  { eapply nth_error_add_index; eauto. }
  i. des.
  eapply bind_inv in x1. des. clarify. subst.
  ss. erewrite nth_error_app1.
  2:{ rewrite <- nth_error_Some. ii. clarify. }
  rewrite x0. unfold MiniCET.uslh_ret in x3. clarify.
Qed.

Variant match_cfgs_ext (p: prog) : state ideal_cfg -> state spec_cfg -> Prop :=
| match_cfgs_ext_intro ic sc
  (MATCH: match_cfgs p ic sc) :
  match_cfgs_ext p (S_Running ic) (S_Running sc)
| match_cfgs_ext_ct1
  l blk r m stk (ms:bool) r' m' stk'
  (CT: nth_error p l = Some (blk, true))
  (CT1: (uslh_prog p)[[(l, 0)]] = Some <{{ ctarget }}>)
  (REG: Rsync1 p r r')
  (MSC: Msync p m m')
  (STK: map_opt (ret_sync p) stk = Some stk')
  (MS: eval r' <{{ (callee = (&(l, 0))) ? msf : 1 }}> = N (if ms then 1 else 0)) :
  match_cfgs_ext p (S_Running (((l, 0), r, m, stk), ms))
                   (S_Running (((l, 0), r', m', stk'), true, ms))
| match_cfgs_ext_ct2
  l blk r m stk (ms:bool) r' m' stk'
  (CT: nth_error p l = Some (blk, true))
  (CT1: (uslh_prog p)[[(l, 0)]] = Some <{{ ctarget }}>)
  (CT2: (uslh_prog p)[[(l, 1)]] = Some <{{ msf := (callee = (& (l, 0))) ? msf : 1 }}>)
  (REG: Rsync1 p r r')
  (MSC: Msync p m m')
  (STK: map_opt (ret_sync p) stk = Some stk')
  (MS: eval r' <{{ (callee = (& (l, 0))) ? msf : 1 }}> = N (if ms then 1 else 0)) :
  match_cfgs_ext p (S_Running (((l, 0), r, m, stk), ms))
                   (S_Running (((l, 1), r', m', stk'), false, ms))
| match_cfgs_ext_call
  pc fp r m stk ms pc' r' m' stk'
  (CALL: p[[pc]] = Some <{{ call fp }}>)
  (TCALL: (uslh_prog p)[[pc' + 1]] = Some <{{ call ((msf = 1) ? &(0, 0) : fp) }}>)
  (PC: pc_sync p pc = Some pc')
  (REG: Rsync p r r' ms)
  (MSC: Msync p m m')
  (STK: map_opt (ret_sync p) stk = Some stk')
  (MS: r' ! callee = (eval r' <{{ (msf = 1) ? &(0, 0) : fp }}>)) :
  match_cfgs_ext p (S_Running ((pc, r, m, stk), ms))
                   (S_Running ((pc' + 1, r', m', stk'), false, ms))
| match_cfgs_ext_call_fault
  pc r m stk ms
  (CT: (uslh_prog p)[[pc]] <> Some <{{ ctarget }}>):
  match_cfgs_ext p S_Fault
                   (S_Running ((pc, r, m, stk), true, ms))
| match_cfgs_ext_br_true1
  l l' r m stk (ms: bool) r' m' stk'
  pc fl fo e
  (BR: p[[pc]] = Some <{{ branch e to l }}>)
  (FROM: (uslh_prog p) [[(fl, fo)]] = Some <{{ branch ((msf = 1) ? 0 : e) to l' }}>)
  (TO: (uslh_prog p) [[(l', 0)]] =
         Some <{{ msf := (~((msf = 1) ? 0 : e)) ? 1 : msf }}>)
  (MS: eval r' <{{ (~ ((msf = 1) ? 0 : e)) ? 1 : msf }}> = N (if ms then 1 else 0))

  (BT2: (uslh_prog p)[[(l', 1)]] = Some <{{ jump l }}>)
  (REG: Rsync1 p r r')
  (MSC: Msync p m m')
  (STK: map_opt (ret_sync p) stk = Some stk') :
  match_cfgs_ext p (S_Running (((l, 0), r, m, stk), ms))
                   (S_Running (((l', 0), r', m', stk'), false, ms))
| match_cfgs_ext_br_true2
  pc e l l' r m stk ms r' m' stk'
  (BR: p[[pc]] = Some <{{ branch e to l }}>)
  (BT2: (uslh_prog p)[[(l', 1)]] = Some <{{ jump l }}>)
  (REG: Rsync p r r' ms)
  (MSC: Msync p m m')
  (STK: map_opt (ret_sync p) stk = Some stk') :
  match_cfgs_ext p (S_Running (((l, 0), r, m, stk), ms))
                   (S_Running (((l', 1), r', m', stk'), false, ms))
| match_cfgs_ext_br_false
  pc pc' l e  r r' m m' stk stk' (ms:bool)
  (FROM: (uslh_prog p) [[pc']] = Some <{{ branch ((msf = 1) ? 0 : e) to l }}>)
  (TO: (uslh_prog p) [[pc'+1]] = Some <{{ msf := ((msf = 1) ? 0 : e) ? 1 : msf }}>)
  (MS: eval r' <{{ ((msf = 1) ? 0 : e) ? 1 : msf }}> = N (if ms then 1 else 0))
  (PC: pc_sync p pc = Some pc')
  (REG: Rsync1 p r r')
  (MSC: Msync p m m')
  (STK: map_opt (ret_sync p) stk = Some stk') :
  match_cfgs_ext p (S_Running ((pc + 1, r, m, stk), ms))
                   (S_Running ((pc' + 1, r', m', stk'), false, ms))
| match_cfgs_ext_ret1
  pc pc' r r' m m' stk stk' (ms: bool)
  (PC: pc_sync p pc = Some pc')
  (FROM: (uslh_prog p) [[pc']] = Some <{{ callee <- peek }}>)
  (TO: (uslh_prog p) [[pc'+1]] = Some <{{ ret }}>)
  (REG: Rsync p r r' ms)
  (MSC: Msync p m m')
  (STK: map_opt (ret_sync p) stk = Some stk')
  (MS: r' ! callee = match stk' with
                     | [] => UV
                     | (l, o)::sttl => FP (l, o)
                     end) :
  match_cfgs_ext p (S_Running ((pc, r, m, stk), ms))
                   (S_Running ((pc' + 1, r', m', stk'), false, ms))
| match_cfgs_ext_ret2
  l o l' o' r r' m m' stk stk' (ms:bool) e
  (PC: pc_sync p (l, o - 1) = Some (l', o'))
  (FROM: p[[(l, o - 1)]] = Some (ICall e))
  (POS: o > 0)
  (TO: (uslh_prog p) [[(l', o' + 2)]] = Some <{{ msf := (callee = (& (l', o' + 2))) ? msf : 1 }}>)
  (REG: Rsync1 p r r')
  (MSC: Msync p m m')
  (STK: map_opt (ret_sync p) stk = Some stk')
  (MS: eval r' <{{ (callee = (& (l', o' + 2))) ? msf : 1 }}> = N (if ms then 1 else 0)) :
  match_cfgs_ext p (S_Running (((l, o), r, m, stk), ms))
                   (S_Running (((l', o' + 2), r', m', stk'), false, ms))
| match_cfgs_ext_fault :
  match_cfgs_ext p S_Fault S_Fault
| match_cfgs_ext_term :
  match_cfgs_ext p S_Term S_Term
.

Lemma src_lookup p pc pc'
  (SYNC: pc_sync p pc = Some pc') :
  exists i, p[[pc]] = Some i.
Proof.
  unfold pc_sync in SYNC. des_ifs.
  ss. des_ifs; cycle 1.
  { exfalso. rewrite nth_error_None in Heq1.
    erewrite <- length_map with (f:=offset_uslh) in Heq1.
    rewrite <- nth_error_None in Heq1. clarify. }
  destruct p0.
  rewrite nth_error_map in Heq. unfold option_map in Heq.
  rewrite Heq1 in Heq. clarify. ss.
  destruct (nth_error l0 n0) eqn:X; eauto.
  exfalso. rewrite nth_error_None in X.
  rewrite <- (offset_uslh_length _ b) in X.
  rewrite <- nth_error_None in X. clarify.
Qed.

Lemma tgt_inv
  p pc pc' i'
  (NCT: no_ct_prog p)
  (TGT: (uslh_prog p) [[pc']] = Some i')
  (SYNC: pc_sync p pc = Some pc') :
  exists i, p[[pc]] = Some i /\ match_inst_uslh p pc i i'.
Proof.
  exploit src_lookup; eauto. i. des.
  exploit src_inv; eauto. i. des; clarify. eauto.
Qed.

Lemma _offset_uslh_next blk n o io i j
  (OFS: nth_error (_offset_uslh blk n) o = Some io)
  (INST: nth_error blk o = Some i)
  (NEXT: nth_error blk (S o) = Some j) :
  nth_error (_offset_uslh blk n) (S o) = Some (io + uslh_inst_sz i).
Proof.
  ginduction blk; ss; i.
  destruct o; ss; clarify.
  - destruct blk; ss; clarify.
  - eapply IHblk; eauto.
Qed.

Lemma pc_sync_next p pc tpc i j
  (CUR: pc_sync p pc = Some tpc)
  (INST: p[[pc]] = Some i)
  (NXT: p[[pc + 1]] = Some j):
  pc_sync p (pc + 1) = Some (fst tpc, snd tpc + uslh_inst_sz i).
Proof.
  destruct pc as [l o]. destruct tpc as [l' io]. ss.
  unfold fetch in INST, NXT.
  des_ifs_safe.
  apply map_nth_error with (f := offset_uslh) in Heq0.
  rewrite Heq in Heq0. clarify.
  unfold offset_uslh in *.
  rewrite Nat.add_1_r in NXT.
  eapply _offset_uslh_next in Heq1; [| exact INST | exact NXT].
  rewrite Nat.add_1_r.
  rewrite Heq1. reflexivity.
Qed.

Lemma new_prog_no_call_blk blk n c res np
  (USLH: uslh_blk (n, blk) c = (res, np)) :
  forall b, In b np -> forall j e, nth_error (fst b) j <> Some (ICall e).
Proof.
  unfold uslh_blk in USLH. des_ifs_safe.
  eapply bind_inv in USLH. des. subst. unfold concatM in USLH.
  eapply bind_inv in USLH. des. subst. ss. unfold MiniCET.uslh_ret in *. clarify.
  assert (H: forall b0, In b0 pm0 -> forall j e, nth_error (fst b0) j <> Some (ICall e)).
  { clear -USLH. unfold add_index_uslh in *.
    assert (Datatypes.length (_offset_uslh l (if b then 2 else 0)) = Datatypes.length l).
    { eapply _offset_uslh_length. }
    remember (_offset_uslh l (if b then 2 else 0)) as ll. clear Heqll.
    ginduction l; ii.
    - destruct ll; ss. unfold mapM in *. ss. unfold MiniCET.uslh_ret in *. clarify.
    - destruct ll; ss. unfold add_index_uslh in *. simpl in USLH.
      eapply mapM_cons_inv in USLH. des. subst.
      exploit IHl; try eapply USLH0; eauto. i.
      destruct a; ss; unfold MiniCET.uslh_ret in *; clarify;
      try (intros; eapply x; ss; eauto; fail).
      eapply bind_inv in USLH. des.
      unfold add_block_M, add_block in *. clarify.
      simpl in H0. destruct H0 as [H0 | H0].
      { exfalso. rewrite <- H0 in H1.
        destruct j; simpl in H1; [discriminate H1|].
        destruct j; simpl in H1; [discriminate H1|].
        rewrite nth_error_nil in H1. discriminate H1. }
      { assumption. } }
  intros b1 IN1 j1 e1.
  rewrite in_app_iff in IN1. destruct IN1.
  { rewrite app_nil_r in H0. eapply H; eauto. }
  { des_ifs; ss; des; contradiction. }
Qed.

Lemma new_prog_no_call p c p' np
  (USLH: mapM uslh_blk (add_index p) c = (p', np)) :
  forall b, In b np -> forall j e, nth_error (fst b) j <> Some (ICall e).
Proof.
  unfold add_index in USLH. remember 0. clear Heqn.
  ginduction p; ss; ii.
  - unfold mapM in *. ss. unfold MiniCET.uslh_ret in *. clarify.
  - exploit mapM_cons_inv; eauto. i. des. subst.
    rewrite in_app_iff in H. destruct H.
    + eapply new_prog_no_call_blk; eauto.
    + eapply IHp; eauto.
Qed.

Lemma concat_call_find blk l n c expanded np pos e
  (MAP: mapM (fun '(o, i) => uslh_inst i l o)
    (combine (_offset_uslh blk n) blk) c = (expanded, np))
  (NTH: nth_error (List.concat expanded) pos = Some (ICall e)) :
  exists o_src src_e,
    nth_error blk o_src = Some (ICall src_e) /\
    pos = add (prefix_offset expanded o_src 0) 1.
Proof.
  ginduction blk; ss; i.
  { unfold mapM in MAP. ss. unfold MiniCET.uslh_ret in MAP. clarify.
    ss. rewrite nth_error_nil in NTH. discriminate. }
  eapply mapM_cons_inv in MAP. des. subst.
  simpl in NTH.
  destruct (lt_dec pos (Datatypes.length res_hd)).
  -
    rewrite nth_error_app1 in NTH; auto.
    destruct a; ss; unfold MiniCET.uslh_ret in *; clarify;
    try (exfalso;
         destruct pos; simpl in NTH; try discriminate NTH;
         destruct pos; simpl in NTH; try discriminate NTH;
         rewrite nth_error_nil in NTH; discriminate NTH).

    + exfalso. eapply bind_inv in MAP. des.
      unfold add_block_M, add_block in MAP. clarify.
      destruct pos; simpl in NTH; [discriminate NTH|].
      destruct pos; simpl in NTH; [discriminate NTH|].
      rewrite nth_error_nil in NTH. discriminate NTH.

    + exists 0, fp. split; [auto|].
      destruct pos; [exfalso; simpl in NTH; discriminate NTH|].
      destruct pos; [simpl in NTH; clarify; auto|].
      exfalso. destruct pos; simpl in NTH; [discriminate NTH|].
      rewrite nth_error_nil in NTH. discriminate NTH.
  -
    rewrite nth_error_app2 in NTH; [|lia].
    exploit IHblk; eauto. i. des.
    exists (S o_src), src_e. split; [auto|].
    unfold prefix_offset in *. simpl firstn. simpl fold_left.
    rewrite fold_left_init_0. lia.
Qed.

Lemma wf_ret_uslh_src p pc
  (WFP: wf_prog p)
  (NCT: no_ct_prog p)
  (WFR: wf_ret (uslh_prog p) pc) :
  exists o_src,
    wf_ret p (fst pc, S o_src) /\
    ret_sync p (fst pc, S o_src) = Some pc /\
    pc_sync p (fst pc, o_src) = Some (fst pc, snd pc - 2) /\
    (uslh_prog p)[[pc]] = Some <{{ msf := (callee = (& pc)) ? msf : 1 }}> /\
    snd pc >= 2.
Proof.
  destruct pc as [l o]. red in WFR. des.
  simpl in WFR, WFR0. des_ifs_safe.
  destruct p0 as [tblk is_proc]. simpl in WFR, WFR0.
  rename Heq into TBLK.
  des. rename WFR0 into CALL_AT. rename WFR1 into OGT0.


  assert (LBD: l < Datatypes.length p).
  { unfold uslh_prog in TBLK. des_ifs_safe.
    exploit mapM_perserve_len; eauto. i.
    destruct (lt_dec l (Datatypes.length p)); auto.
    exfalso.
    assert (LEN: Datatypes.length l0 = Datatypes.length p).
    { rewrite <- x0. unfold add_index. rewrite length_combine, length_seq, min_id. auto. }
    rewrite nth_error_app2 in TBLK; [|lia].
    eapply nth_error_In in TBLK.
    eapply (new_prog_no_call _ _ _ _ Heq) in TBLK.
    eapply TBLK. simpl. eauto. }


  assert (SRC_BLK: exists sblk, nth_error p l = Some sblk).
  { destruct (nth_error p l) eqn:E; [eauto|].
    exfalso. eapply nth_error_None in E. lia. }
  des.


  hexploit label_inv; eauto. i. des.
  rename H into TBLK'. rename H0 into USLH_BLK. rename H1 into C_EQ.



  rewrite TBLK in TBLK'. injection TBLK' as TBLK'. subst.


  destruct sblk as [sbl s_proc]. simpl in USLH_BLK.
  eapply bind_inv in USLH_BLK. des. subst.
  unfold concatM in USLH_BLK. eapply bind_inv in USLH_BLK. des.
  ss. unfold MiniCET.uslh_ret in *. clarify.
  erewrite uslh_offset_uslh_add_index in USLH_BLK; eauto.





  assert (CALL_IN_CONCAT: exists pos', nth_error (List.concat a0) pos' = Some (ICall e) /\
          (if s_proc then add pos' 2 = o - 1 else pos' = o - 1)).
  { des_ifs; simpl in CALL_AT.
    - destruct (o - 1) eqn:EQ; [simpl in CALL_AT; discriminate|].
      destruct n eqn:EQ2; [simpl in CALL_AT; discriminate|].
      simpl in CALL_AT. exists n0. split; auto. lia.
    - exists (o - 1). split; auto. }

  des.
  exploit concat_call_find; eauto. i. des.


  assert (OFS: exists io, nth_error (_offset_uslh sbl (if s_proc then 2 else 0)) o_src = Some io).
  { destruct (nth_error (_offset_uslh sbl (if s_proc then 2 else 0)) o_src) eqn:E; [eauto|].
    exfalso. eapply nth_error_None in E. rewrite _offset_uslh_length in E.
    simpl in x0. assert (o_src < Datatypes.length sbl) by (eapply nth_error_Some; ii; clarify). lia. }
  des.

  hexploit offset_eq_aux; eauto.
  { pose proof (proj1 (nth_error_Some (_offset_uslh sbl (if s_proc then 2 else 0)) o_src)) as HH. rewrite _offset_uslh_length in HH. simpl. apply HH. rewrite OFS. discriminate. }
  i.


  assert (IO_EQ: io = (if s_proc then add (prefix_offset a0 o_src 0) 2 else prefix_offset a0 o_src 0)).
  { unfold prefix_offset in H |- *. rewrite fold_left_init_0 in H.
    destruct s_proc.
    - rewrite <- H. simpl. lia.
    - rewrite <- H. simpl. lia. }


  assert (O_EQ: o - 1 = add io 1).
  { subst. des_ifs; lia. }


  assert (O_EQ2: o = add io 2).
  { lia. }


  assert (PCSYNC: pc_sync p (l, o_src) = Some (l, io)).
  { unfold pc_sync. simpl. rewrite nth_error_map. rewrite SRC_BLK.
    simpl. unfold offset_uslh. simpl. rewrite OFS. auto. }


  assert (RETSYNC: ret_sync p (l, S o_src) = Some (l, o)).
  { simpl in x0. unfold ret_sync. simpl.
    change (p[[(l, o_src)]]) with (fetch p (l, o_src)).
    unfold fetch. rewrite SRC_BLK. simpl. rewrite x0.
    fold (pc_sync p (l, o_src)). rewrite PCSYNC. f_equal. f_equal. lia. }


  assert (WF_RET_SRC: wf_ret p (l, S o_src)).
  { red. simpl. split.
    -
      assert (FETCH_SRC: fetch p (l, o_src) = Some (ICall src_e)).
      { unfold fetch. rewrite SRC_BLK. simpl. auto. }
      exploit (block_always_terminator_prog p (l, o_src) (ICall src_e) WFP FETCH_SRC).
      { simpl. intro HH; exact HH. }
      intros [next_i NEXT]. unfold inc in NEXT.
      replace (Nat.add o_src 1) with (S o_src) in NEXT by lia.
      unfold fetch in NEXT |- *. rewrite SRC_BLK in NEXT |- *. simpl in NEXT |- *.
      rewrite NEXT. discriminate.
    - exists src_e. simpl. split; [|lia].
      unfold fetch. rewrite SRC_BLK. simpl. simpl in x0. rewrite Nat.sub_0_r. exact x0. }


  assert (TGT_FETCH: (uslh_prog p)[[(l, o)]] =
    Some <{{ msf := (callee = (& (l, o))) ? msf : 1 }}>).
  { rename H into PFX. clear O_EQ2 RETSYNC PCSYNC.
    exploit mapM_nth_error_strong; eauto.
    { eapply _offset_uslh_combine; eauto. }
    i. des.
    ss. unfold MiniCET.uslh_ret in *. clarify.
    exploit (concat_nth_error a0 _ _ 2); eauto; [ss|]. intro CNE. des.
    destruct s_proc; ss; unfold MiniCET.uslh_ret in *; clarify.
    +
      unfold fetch. rewrite TBLK. simpl.
      destruct o; [lia|]. destruct o; [lia|]. simpl.
        assert (OO: o = prefix_offset a0 o_src 0 + 2) by lia.
        rewrite OO. rewrite CNE.
        assert (PP: prefix_offset a0 o_src 2 + 2 = S (S (prefix_offset a0 o_src 0 + 2))) by
          (unfold prefix_offset; rewrite fold_left_init_0; lia).
        rewrite PP. reflexivity.
    +
      unfold fetch. rewrite TBLK. simpl.
      assert (OO: o = prefix_offset a0 o_src 0 + 2) by lia.
      rewrite OO. rewrite CNE. reflexivity. }


  exists o_src.
  refine (conj WF_RET_SRC (conj RETSYNC (conj _ (conj TGT_FETCH _)))).
  - unfold pc_sync in PCSYNC. rewrite PCSYNC. do 2 f_equal. lia.
  - simpl. lia.
Qed.

Lemma pc_sync_same_label p l o l' o'
  (PC: pc_sync p (l, o) = Some (l', o')) :
  l = l'.
Proof. ss. des_ifs. Qed.

Lemma wf_ret_src p pc tpc
  (WFP: wf_prog p)

  (RET: ret_sync p pc = Some tpc) :
  wf_ret p pc.
Proof.
  destruct pc as [l o]. unfold ret_sync in RET. des_ifs_safe.
  red. split.
  { hexploit block_always_terminator_prog; eauto. i. des.
    replace (S n) with (add n 1) by lia. ss. ii. clarify. }
  esplits; [|lia]. replace (S n - 1) with n by lia. eauto.
Qed.

Lemma wf_ret_tgt p pc tpc
  (WFP: wf_prog p)
  (NCT: no_ct_prog p)
  (RET: ret_sync p pc = Some tpc) :
  wf_ret (uslh_prog p) tpc.
Proof.
  destruct pc as [l o]. unfold ret_sync in RET. des_ifs_safe.
  hexploit src_inv; eauto. i. des.
  inv H0; [inv SIMPL|]. clarify.
  hexploit pc_sync_same_label; eauto. i. subst.
  red. split.
  { ii. simpl in *. clarify. }
  esplits; [|lia]. replace (n1 + 2 - 1) with (add n1 1) by lia.
  ss. eauto.
Qed.

Lemma wf_ret_rsync_src p sr tr b x l o
  (WFP: wf_prog p)
  (RET: Rsync p sr tr b)
  (MSF: x <> msf)
  (CALLEE: x <> callee)
  (PTR: sr ! x = FP (l, o))
  (NZR: o <> 0) :
  wf_ret p (l, o).
Proof.
  unfold Rsync in *. des.
  hexploit RET; eauto. i. rewrite PTR in H.
  unfold val_match in H. des_ifs_safe.
  clear RET0. des_ifs.
  { des; subst. rewrite Nat.eqb_eq in Heq0. subst. clarify. }
  eapply wf_ret_src; eauto.
Qed.

Lemma wf_ret_rsync_tgt p sr tr b x l o
  (WFP: wf_prog p)
  (NCT: no_ct_prog p)
  (RET: Rsync p sr tr b)
  (MSF: x <> msf)
  (CALLEE: x <> callee)
  (PTR: tr ! x = FP (l, o))
  (NZR: o <> 0) :
  wf_ret (uslh_prog p) (l, o).
Proof.
  unfold Rsync in *. des.
  hexploit RET; eauto. i. rewrite PTR in H.
  unfold val_match in H. des_ifs_safe.
  clear RET0. des_ifs.
  { des; subst. clarify. }
  eapply wf_ret_tgt; eauto.
Qed.


Lemma wf_ret_msync_src p m m' i l o
  (WFP: wf_prog p)
  (MREL: Msync p m m')
  (PTR: nth_error m i = Some (FP (l, o)))
  (NZR: o <> 0) :
  wf_ret p (l, o).
Proof.
  specialize (MREL i). rewrite PTR in MREL. des_ifs.
  unfold val_match in MREL. des_ifs.
  { des; subst. rewrite Nat.eqb_eq in Heq0. subst. clarify. }
  eapply wf_ret_src; eauto.
Qed.

Lemma wf_ret_msync_tgt p m m' i l o
  (WFP: wf_prog p)
  (NCT: no_ct_prog p)
  (MREL: Msync p m m')
  (PTR: nth_error m' i = Some (FP (l, o)))
  (NZR: o <> 0) :
  wf_ret (uslh_prog p) (l, o).
Proof.
  specialize (MREL i). rewrite PTR in MREL. des_ifs.
  unfold val_match in MREL. des_ifs.
  { des; subst. clarify. }
  eapply wf_ret_tgt; eauto.
Qed.

Lemma wf_ret_expr_src p sr tr b e l o
  (WFP: wf_prog p)
  (RET: Rsync p sr tr b)
  (WFE: wf_expr p e)
  (UNUSED1: e_unused msf e)
  (UNUSED2: e_unused callee e )
  (PTR: eval sr e = FP (l, o))
  (NZR: o <> 0) :
  wf_ret p (l, o).
Proof.
  ginduction e; (try sfby ss); i.
  - eapply wf_ret_rsync_src; eauto.
  - ss. exfalso. unfold eval_binop in PTR. clear -PTR.
    des_ifs.
  - simpl in UNUSED1, UNUSED2, PTR, WFE. des. des_ifs.
    + hexploit IHe2; eauto.
    + hexploit IHe3; eauto.
  - simpl in PTR, WFE. clarify. ss. des; clarify.
Qed.

Lemma wf_ret_expr_tgt p sr tr b e l o
  (WFP: wf_prog p)
  (NCT: no_ct_prog p)
  (RET: Rsync p sr tr b)
  (WFE: wf_expr p e)
  (UNUSED1: e_unused msf e)
  (UNUSED2: e_unused callee e )
  (PTR: eval tr e = FP (l, o))
  (NZR: o <> 0) :
  wf_ret (uslh_prog p) (l, o).
Proof.
  ginduction e; (try sfby ss); i.
  - eapply wf_ret_rsync_tgt; eauto.
  - ss. exfalso. unfold eval_binop in PTR. clear -PTR.
    des_ifs.
  - simpl in UNUSED1, UNUSED2, PTR, WFE. des. des_ifs.
    + hexploit IHe2; eauto.
    + hexploit IHe3; eauto.
  - simpl in PTR, WFE. clarify. ss. des; clarify.
Qed.

Lemma ultimate_slh_bcc_single (p: prog) ic1 sc1 sc2 ds os
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (MATCH: match_cfgs_ext p ic1 sc1)
  (TGT: uslh_prog p |- <(( sc1 ))> -->_ ds^^os <(( sc2 ))>) :
  exists ds' os' ic2, p |- <(( ic1 ))> -->i*_ ds' ^^ os' <(( ic2 ))>
               /\ match_cfgs_ext p ic2 sc2
               /\ match_ds p ds' ds
               /\ match_obs p os' os.
Proof.
  inv MATCH; try sfby inv TGT.

  - inv TGT; inv MATCH0; clarify.
    + exploit tgt_inv; eauto. i. des. inv x1. inv MATCH.
      replace (@nil direction) with ((@nil direction) ++ []) by ss.
      replace (@nil observation) with ((@nil observation) ++ []) by ss.
      esplits.
      { econs 2; econs. eauto. }
      { econs. econs; eauto.
        exploit block_always_terminator_prog; try eapply x0; eauto. i. des.
        destruct pc0.
        exploit pc_sync_next; [exact PC | exact x0 | exact x1 | i; rewrite x2; destruct pc; ss]. }
      { ss. }
      { ss. }
    + exploit tgt_inv; eauto. i. des. inv x0.
      * inv MATCH.
        replace (@nil direction) with ((@nil direction) ++ []) by ss.
        replace (@nil observation) with ((@nil observation) ++ []) by ss.
        esplits.
        { econs 2; [econs 2|econs]. eauto. }
        {econs. econs; eauto.
         { exploit block_always_terminator_prog; try eapply x1; eauto. i. des.
           destruct pc0.
           exploit pc_sync_next; [exact PC | exact x1 | exact x2 | i; rewrite x3; destruct pc; ss].
         }
         { eapply unused_prog_lookup in UNUSED1; eauto.
           eapply unused_prog_lookup in UNUSED2; eauto. ss; des.
           inv REG. econs.
           - i. exploit eval_regs_eq; eauto.
             { exploit wf_prog_lookup; eauto. ss. clear. apply wf_expr_wf_exp. }
             i. destruct (x =? x0) eqn:Heq; [apply eqb_eq in Heq | apply eqb_neq in Heq].
             { subst. now rewrite! t_update_eq. }
             { rewrite t_update_neq; eauto. rewrite t_update_neq; eauto. }
           - erewrite t_update_neq; eauto. } }
        { ss. }
        { ss. }
      * clarify. esplits; [econs| |ss|ss].
        eapply match_cfgs_ext_call; eauto.
        { inv REG. split; i.
          - des. rewrite t_update_neq; eauto.
          - rewrite t_update_neq; eauto. ii; clarify. }
        { rewrite t_update_eq. rewrite eval_unused_update; eauto.
          exploit unused_prog_lookup; try eapply x1; eauto. i. ss. }

    + exploit tgt_inv; eauto. i. des. inv x0.
      inv MATCH.
      replace (@nil direction) with ((@nil direction) ++ []) by ss.
      replace ([ODiv v1 v2]) with (([ODiv v1 v2]) ++ []) by ss.
      esplits.
      { econs 2; [|econs].
        eapply ISMI_Div. 1: eassumption.
        - inv REG. simpl in H1. rewrite H3 in H1. simpl in H1. rewrite <- H1. destruct ms; simpl; [reflexivity|].
          eapply unused_prog_lookup in UNUSED1; eauto.
          eapply unused_prog_lookup in UNUSED2; eauto.
          inv UNUSED1. inv UNUSED2. des.
          eapply eval_regs_eq_nat; eauto.
          apply wf_expr_wf_exp. exploit wf_prog_lookup; eauto. i. ss. apply x2.
        - inv REG. simpl in H2. rewrite H3 in H2. simpl in H2. rewrite <- H2. destruct ms; simpl; [reflexivity|].
          eapply unused_prog_lookup in UNUSED1, UNUSED2; eauto.
          inv UNUSED1. inv UNUSED2. des.
          eapply eval_regs_eq_nat; eauto.
          apply wf_expr_wf_exp. exploit wf_prog_lookup; eauto. i. ss. apply x2.
      }
      { fold res. econs. econs. 3: assumption.
        - exploit block_always_terminator_prog; try eapply x1; eauto. i. des.
          exploit pc_sync_next; eauto. now destruct pc.
        - econs.
          + i. destruct (string_dec x x0).
            * subst. rewrite! t_update_eq. destruct v2; ss.
            * do 2 (rewrite t_update_neq; [|assumption]). now apply REG.
          + eapply unused_prog_lookup in UNUSED1; eauto.
            inv UNUSED1. rewrite t_update_neq; [|easy]. now apply REG.
        - eauto.
      }
      { ss. }
      { repeat econs. }

    + exploit tgt_inv; eauto. i. des. inv x1.
      { inv MATCH. }
      clarify.
      eapply unused_prog_lookup in UNUSED1; eauto.
      eapply unused_prog_lookup in UNUSED2; eauto. ss; des.

      replace [DBranch b'] with ([DBranch b'] ++ []) by ss.
      replace [OBranch (not_zero n)] with ([OBranch (not_zero n)] ++ []) by ss.
      exists ([DBranch b'] ++ []), ([OBranch (not_zero n)] ++ []).
      esplits; cycle 2.
      { repeat econs. }
      { repeat econs. }
      { econs; econs; eauto. simpl in H1. inv REG. rewrite H2 in H1.
        ss. rewrite <- H1. destruct ms; ss. erewrite eval_regs_eq_nat; eauto.
        apply wf_expr_wf_exp. exploit wf_prog_lookup; eauto. i. apply x1. }
      destruct pc as [b o]. destruct pc0 as [b0 o0].
      destruct b'.
      * eapply match_cfgs_ext_br_true1; eauto.
        { simpl. rewrite IN. ss. }
        { clear -H1 REG. inv REG. rewrite H0 in H1. ss. rewrite H0. ss.
          destruct ms; ss. unfold to_nat in H1. des_ifs_safe.
          destruct n; ss; clarify. }
        { ss. rewrite IN. ss. }
        { inv REG. red. eauto. }
      * eapply match_cfgs_ext_br_false; try eapply H0; eauto.
        { clear -H1 REG. inv REG. rewrite H0 in H1. ss. rewrite H0. ss.
          destruct ms; ss. unfold to_nat in H1. des_ifs_safe.
          destruct n; ss; clarify. }
        { inv REG. red. eauto. }

    + exploit tgt_inv; eauto. i. des. inv x1. inv MATCH.
      replace (@nil direction) with ((@nil direction) ++ []) by ss.
      replace (@nil observation) with ((@nil observation) ++ []) by ss.

      exists ([] ++ []), ([] ++ []), (S_Running (l, 0, r0, m0, stk, ms)). splits; econs; [|econs|].
      * eapply ISMI_Jump; eauto.
      * econs; eauto.
        exploit wf_prog_lookup; try eapply x0; eauto. i.
        ss. unfold wf_lbl in x1. des_ifs_safe.
        inv WFP. rewrite Forall_forall in H1.
        pose proof Heq as BLK.
        eapply nth_error_In in Heq. eapply H1 in Heq.
        red in Heq. des.
        unfold nonempty_block in Heq. ss.
        destruct l0; [ss; lia|].
        unfold pc_sync. ss.
        rewrite nth_error_map. rewrite BLK. ss.

    + exploit tgt_inv; eauto. i. des. inv x0. inv MATCH.
      dup MSC. specialize (MSC0 n). rewrite H2 in MSC0. des_ifs_safe.
      exists ([] ++ []), ([OLoad n] ++ []), (S_Running ((pc0 + 1), x !-> v; r0, m0, stk, ms)).

      eapply unused_prog_lookup in UNUSED1; eauto.
      eapply unused_prog_lookup in UNUSED2; eauto. ss; des.
      exploit wf_prog_lookup; eauto. i.
      destruct pc as [b o]. destruct pc0 as [b0 o0].
      replace (@nil direction) with ((@nil direction) ++ []) by ss.
      replace [OLoad n] with ([OLoad n] ++ []) by ss.
      splits; econs; eauto; [|econs| |econs].
      * econs; eauto.
        inv REG. rewrite <- H1. ss.
        rewrite H3. ss. destruct ms; ss.
        erewrite eval_regs_eq_nat; eauto.
        now apply wf_expr_wf_exp.
      * econs; eauto.
        { exploit block_always_terminator_prog; try eapply x1; eauto. i. des.
          exploit pc_sync_next; eauto.

            }
        { red. splits; i.
          - destruct (string_dec x x0); subst.
            { do 2 rewrite t_update_eq; eauto. }
            { rewrite t_update_neq; eauto. rewrite t_update_neq; eauto. now apply REG. }
          - inv REG. ss. des. rewrite t_update_neq; eauto. }

    + exploit tgt_inv; eauto. i. des. inv x1. inv MATCH.
      eapply unused_prog_lookup in UNUSED1; eauto.
      eapply unused_prog_lookup in UNUSED2; eauto. ss. des.
      exploit wf_prog_lookup; eauto. i.

      exists ([] ++ []), ([OStore n] ++ []), (S_Running (pc0+1, r0, (upd n m0 (eval r0 e')), stk, ms)).

      destruct pc as [b o]. destruct pc0 as [b0 o0].
      replace (@nil direction) with ((@nil direction) ++ []) by ss.
      replace [OStore n] with ([OStore n] ++ []) by ss.

      splits; [ | |econs|repeat econs].
      * econs; [|econs]. simpl. eapply ISMI_Store; eauto.
        inv REG. rewrite <- H1. rewrite H2. destruct ms; ss.
        erewrite eval_regs_eq_nat; eauto. apply wf_expr_wf_exp. apply x1.
      * dup REG. inv REG. econs.

        econs; eauto.
        { exploit block_always_terminator_prog; try eapply x0; eauto. i. des.
          exploit pc_sync_next; eauto. }
        { exploit eval_regs_eq; eauto. 1: apply wf_expr_wf_exp, x1. i.
          unfold Msync. i. destruct (i =? n)%nat eqn:Heq.
          - apply Nat.eqb_eq in Heq.  subst.
            assert (Datatypes.length (upd n m (eval r e')) = Datatypes.length (upd n m0 (eval r0 e'))).
            { clear - MSC. rewrite! upd_length. unfold Msync in MSC.
              induction m in m0, MSC |-*; i; destruct m0; ss. 1, 2: specialize (MSC 0); ss.
              f_equal. apply IHm. i. specialize (MSC (S i)); ss. }
            pose proof (ge_dec n (Datatypes.length (upd n m (eval r e')))) as [Hlen | Hlen].
            + exploit nth_error_None. i. dup Hlen. apply x3 in Hlen.
              rewrite H3 in Hlen0. exploit nth_error_None. i. apply x4 in Hlen0.
              now rewrite Hlen, Hlen0.
            + apply not_ge in Hlen.
              rewrite upd_eq. 2: erewrite <- upd_length, <- H3; eauto.
              rewrite upd_eq. 2: erewrite <- upd_length; eauto.
              apply eval_regs_eq; auto. apply wf_expr_wf_exp. apply wf_prog_lookup in x0; eauto. apply x0.
          - apply Nat.eqb_neq in Heq. rewrite! upd_neq; eauto.
            apply MSC.
        }


    + exploit tgt_inv; eauto. i. des. inv x1. inv MATCH.


    + exploit tgt_inv; eauto. i. des. inv x1. inv MATCH.


    + exploit tgt_inv; eauto. i. des. inv x1. inv MATCH.


    + exploit tgt_inv; eauto. i. des. inv x0.
      { inv MATCH.
        replace (@nil direction) with ((@nil direction) ++ []) by ss.
        replace (@nil observation) with ((@nil observation) ++ []) by ss.
        esplits.
        { econs 2; econs; eassumption. }
        { unfold val. econs. econs; eauto.
          1: exploit block_always_terminator_prog; eauto; i; des.
          1: exploit pc_sync_next; eauto; destruct pc; ss.
          unfold Rsync. split.
          - i. destruct stk.
            + ss. inv STK. destruct (string_dec x x0).
              * subst. rewrite! t_update_eq. ss.
              * rewrite! t_update_neq; eauto. now apply REG.
            + ss. destruct (ret_sync p c) eqn:?; [|discriminate].
              destruct (map_opt (ret_sync p) stk) eqn:?; [|discriminate].
              inv STK.
              destruct (string_dec x x0).
              * subst. rewrite! t_update_eq. destruct c, c0. ss.
                destruct n0; [discriminate|]. ss.
              * rewrite! t_update_neq; eauto. now apply REG.
          - rewrite t_update_neq.
            2: eapply unused_prog_lookup in UNUSED1; eauto; apply UNUSED1.
            apply REG.
        }
        { econs. }
        { econs. }
      }
      { clarify. esplits; [econs| |econs|econs].
        eapply match_cfgs_ext_ret1; eauto. 2: rewrite t_update_eq; unfold val; destruct sk; [|destruct c]; reflexivity.
        econs. 2: rewrite t_update_neq; [now apply REG | discriminate].
        i; rewrite t_update_neq; [now apply REG | des; symmetry; eauto].
      }


    + exploit tgt_inv; eauto. i. des. inv x1. inv MATCH.


  - inv TGT; clarify. esplits.
    + econs.
    + eapply match_cfgs_ext_ct2; eauto.
      exploit head_call_target; eauto. i. des; clarify; eauto.
    + econs.
    + econs.


  - inv TGT; clarify.
    esplits; econs.
    econs; eauto.
    + unfold pc_sync.
      simpl. rewrite nth_error_map.
      rewrite CT. destruct blk.
      { inv WFP. rewrite Forall_forall in H0. eapply nth_error_In in CT.
        eapply H0 in CT. red in CT. des; ss. }
      simpl. eauto.
    + red in REG. econs.
      * i. des. rewrite t_update_neq; eauto.
      * rewrite t_update_eq. eauto.


  - inv TGT; clarify.
    destruct pc'0 as [l' o'].
    exploit unused_prog_lookup; try eapply UNUSED1; eauto.
    exploit unused_prog_lookup; try eapply UNUSED2; eauto. i.
    destruct ((uslh_prog p)[[(l', o')]]) eqn:NXT.

    2:{ replace [DCall(l', o')] with ([DCall (l', o')] ++ []) by ss.
        replace [OCall l] with ([OCall l] ++ []) by ss.
        destruct l as [l o]. destruct o.

        - exists ([DCall (l', o')] ++ []), ([OCall (l, 0)] ++ []). esplits.
          { econs; [|econs].
            eapply ISMI_Call_F; eauto.
            - unfold cptr in *. rewrite <- H8. inv REG. ss. rewrite H0. destruct ms; ss.
              rewrite H0 in *. ss.
              f_equal. exploit (eval_regs_eq); eauto.
              { apply wf_expr_wf_exp; eapply wf_prog_lookup in WFP; eauto; apply WFP. }
              i. unfold to_fp in H8. des_ifs_safe. red in x2.
              des_ifs_safe; des; subst; auto. clear NXT.
              des_ifs.
              { des. rewrite Nat.eqb_eq in Heq1. subst. auto. }
              { eapply ret_sync_nonzero in x2. clarify. }

            - i. simpl in H, NXT. des_ifs.
              2:{ clear - H Heq. exploit label_inv; eauto. i. des. clarify. }
              simpl. right. ii. subst. clear -Heq NXT WFP.
              exploit uslh_prog_nonempty_block; eauto. i.
              rewrite nth_error_None in NXT. lia. }
          { econs. ii. clarify. }
          { repeat econs. }
          { repeat econs. }

        - assert (WFRT: wf_ret (uslh_prog p) (l, S o)).
          { dup REG. inv REG. simpl in H8. rewrite H0 in H8.
            unfold to_fp in H8. des_ifs.
            eapply wf_ret_expr_tgt; eauto.
            exploit wf_prog_lookup; eauto. }
          hexploit wf_ret_uslh_src; eauto. i. des.
          assert (ms = false); subst.
          { destruct ms; auto. inv REG. des. simpl in H8.
            rewrite H5 in H8. ss. }

          exists ([DCall (l', o')] ++ []), ([OCall (l, S o_src)] ++ []).
          esplits.
          { econs; [|econs].
            eapply ISMI_Call_F; eauto.
            - dup REG. inv REG. simpl in H8. rewrite H5 in H8. simpl in H8.
              simpl in x1, x0. hexploit eval_regs_eq; eauto.
              { exploit wf_prog_lookup; eauto. ss. clear. apply wf_expr_wf_exp. }
              i. unfold to_fp in *. des_ifs_safe. red in H6.
              destruct pc0. des_ifs.
              { des; clarify. }
              hexploit ret_sync_inj; [eapply H0|eapply H6|]. i. des. clarify.
            - i. simpl in H4, NXT. des_ifs.
              2:{ clear - H4 Heq. exploit label_inv; eauto. i. des. clarify. }
              simpl. right. ii. subst. clear -Heq NXT WFP.
              exploit uslh_prog_nonempty_block; eauto. i.
              rewrite nth_error_None in NXT. lia. }
          { econs. ii. clarify. }
          { repeat econs. }
          { repeat econs. red. eauto. } }
    assert (i = ICTarget \/ i <> ICTarget).
    { destruct i; try (sfby (right; ii; clarify)). auto. }
    des; subst.

    + exploit head_call_target; eauto. i. des; clarify.
      replace [DCall(l0, 0)] with ([DCall (l0, 0)] ++ []) by ss.
      replace [OCall l] with ([OCall l] ++ []) by ss.

      exploit unused_prog_lookup; try eapply UNUSED1; eauto.
      exploit unused_prog_lookup; try eapply UNUSED2; eauto.

      destruct (nth_error p l0) as [|blk' b'] eqn:CTSRC; cycle 1.
      {  unfold uslh_prog in NXT. des_ifs.
         hexploit new_prog_ct_cut; try eapply Heq; eauto.
         { eapply new_prog_no_ct. eauto. }
         i. simpl in H. des_ifs_safe.
         rewrite nth_error_None in CTSRC.
         assert (l0 < Datatypes.length l1) by (rewrite <- nth_error_Some; ii; clarify).

         eapply mapM_perserve_len in Heq. rewrite length_add_index in Heq. lia. }

      destruct p0 as [blk' b']. destruct b'; cycle 1.
      { eapply no_ctarget_exists with (o:=0) in CTSRC; eauto. clarify. }
      i. des.
      destruct l as [l o]. destruct o.
      * exists ([DCall (l0, 0)] ++ []), ([OCall (l, 0)] ++ []). esplits.
        { econs; [|econs].
          eapply ISMI_Call; eauto.
          - unfold cptr in *. rewrite <- H8. inv REG. ss. rewrite H0. destruct ms; ss.
            rewrite H0 in *. ss.
            f_equal. exploit (eval_regs_eq); eauto.
            { apply wf_expr_wf_exp; eapply wf_prog_lookup in WFP; eauto; apply WFP. }
            i. unfold to_fp in H8. des_ifs_safe. red in x6.
            des_ifs; cycle 1.
            { eapply ret_sync_nonzero in x6. clarify. }
            des; subst. rewrite Nat.eqb_eq in Heq3. subst. auto. }
        { eapply match_cfgs_ext_ct1; eauto.
          { red. inv REG. eauto. }
          { inv REG. simpl. rewrite STK.
            exploit block_always_terminator_prog; try eapply CALL; eauto. i. des.
            destruct pc as [b o].
            hexploit pc_sync_next; eauto. i. unfold ret_sync.
            ss. rewrite add_1_r. des_ifs_safe. ss.
            do 3 f_equal. lia. }
          inv REG. simpl. rewrite MS. ss. rewrite H0.
          destruct ms; ss.
          { des_ifs. }
          { rewrite H0 in H8. ss. unfold to_fp in H8. des_ifs_safe.
            ss. clarify. do 2 rewrite andb_true_r. unfold not_zero.
            destruct (l =? l0)%nat eqn:EQUIV; ss.
            { rewrite Nat.eqb_sym, EQUIV. auto. }
            { rewrite Nat.eqb_sym, EQUIV. auto. } } }
        { repeat econs. }
        { repeat econs. }
      * assert (WFRT: wf_ret (uslh_prog p) (l, S o)).
        { dup REG. inv REG. simpl in H8. rewrite H0 in H8.
          unfold to_fp in H8. des_ifs.
          eapply wf_ret_expr_tgt; eauto.
          exploit wf_prog_lookup; eauto. }
        hexploit wf_ret_uslh_src; eauto. i. des.
        assert (ms = false); subst.
        { destruct ms; auto. inv REG. des. simpl in H8.
          rewrite H5 in H8. ss. }

        exists ([DCall (l0, 0)] ++ []), ([OCall (l, S o_src)] ++ []).
        esplits.
        { econs; [|econs].
          eapply ISMI_Call; eauto.
          dup REG. inv REG. simpl in H8. rewrite H5 in H8. simpl in H8.
          simpl in x1, x0. hexploit eval_regs_eq; eauto.
          { exploit wf_prog_lookup; eauto. ss. clear. apply wf_expr_wf_exp. }
          i. unfold to_fp in *. des_ifs_safe. red in H6.
          destruct pc0. des_ifs.
          { des; clarify. }
          hexploit ret_sync_inj; [eapply H0|eapply H6|]. i. des. clarify. }
        { simpl in NXT. des_ifs_safe. simpl in Heq0.
          eapply match_cfgs_ext_ct1; eauto.
          - simpl. des_ifs.
          - inv REG. auto.
          - simpl. rewrite STK.
            exploit block_always_terminator_prog; try eapply CALL; eauto. i. des.
            destruct pc as [b1 o1].
            hexploit pc_sync_next; try eapply PC; eauto. i. unfold ret_sync.
            ss. rewrite add_1_r. des_ifs_safe. ss.
            do 3 f_equal. lia.
          - inv REG. simpl. rewrite MS. ss. rewrite H5 in *.
            ss. unfold to_fp in H8. des_ifs_safe.
            ss. clarify. do 2 rewrite andb_false_r. simpl. auto. }
        { repeat econs. }
        { repeat econs. red. eauto. }

    + replace [DCall(l', o')] with ([DCall (l', o')] ++ []) by ss.
      replace [OCall l] with ([OCall l] ++ []) by ss.
      destruct l as [l o]. destruct o.

      * exists ([DCall (l', o')] ++ []), ([OCall (l, 0)] ++ []). esplits.
        { econs; [|econs].
          eapply ISMI_Call_F; eauto.
          - unfold cptr in *. rewrite <- H8. inv REG. ss. rewrite H1.
            destruct ms; ss. rewrite H1 in *. ss.
            f_equal. exploit (eval_regs_eq); eauto.
            { apply wf_expr_wf_exp; eapply wf_prog_lookup in WFP; eauto; apply WFP. }
            i. unfold to_fp in H8. des_ifs_safe. red in x2.
            des_ifs_safe; des; subst; auto. clear NXT.
            des_ifs.
            { des. rewrite Nat.eqb_eq in Heq2. subst. auto. }
            { eapply ret_sync_nonzero in x2. clarify. }
          - i. destruct blk; destruct b; auto. right.
            simpl. ii. subst. hexploit ctarget_exists; eauto. i.
            ss. clarify. }
          { econs. ii. clarify. }
          { repeat econs. }
          { repeat econs. }

      * assert (WFRT: wf_ret (uslh_prog p) (l, S o)).
        { dup REG. inv REG. simpl in H8. rewrite H1 in H8.
          unfold to_fp in H8. des_ifs.
          eapply wf_ret_expr_tgt; eauto.
          exploit wf_prog_lookup; eauto. }
        hexploit wf_ret_uslh_src; eauto. i. des.
        assert (ms = false); subst.
        { destruct ms; auto. inv REG. des. simpl in H8.
          rewrite H6 in H8. ss. }

        exists ([DCall (l', o')] ++ []), ([OCall (l, S o_src)] ++ []).
        esplits.
        { econs; [|econs].
          eapply ISMI_Call_F; eauto.
          - dup REG. inv REG. simpl in H8. rewrite H6 in H8. simpl in H8.
            simpl in x1, x0. hexploit eval_regs_eq; eauto.
            { exploit wf_prog_lookup; eauto. ss. clear. apply wf_expr_wf_exp. }
            i. unfold to_fp in *. des_ifs_safe. red in H9.
            destruct pc0. des_ifs.
            { des; clarify. }
            hexploit ret_sync_inj; [eapply H1|eapply H9|]. i. des. clarify.
          - ii. destruct o'; [| right; ii; ss; clarify].
            destruct blk; destruct b; auto. right.
            ss. hexploit ctarget_exists; eauto. i. ss; clarify. }
        { econs. ii. clarify. }
        { repeat econs. }
        { repeat econs. red. eauto. }
  - inv TGT; clarify. esplits; econs.
  - inv TGT; clarify.
    esplits.
    + econs.
    + eapply match_cfgs_ext_br_true2; eauto.
      red. split.
      * ii. des. rewrite t_update_neq; eauto.
      * rewrite t_update_eq. simpl. ss.
    + econs.
    + econs.
  - inv TGT; clarify. esplits.
    + econs.
    + econs. econs; eauto.
      assert (exists blk, nth_error p l = Some (blk, false)).
      { inv WFP. rewrite Forall_forall in H0.
        destruct pc as [b o].
        simpl in BR. des_ifs_safe. destruct p0 as [blk' b'].
        simpl in BR. eapply nth_error_In in Heq.
        eapply H0 in Heq. red in Heq. des. simpl in Heq1.
        rewrite Forall_forall in Heq1. eapply nth_error_In in BR.
        eapply Heq1 in BR. simpl in BR. des.
        red in BR0. des_ifs. eauto. }
      des. unfold pc_sync.
      rewrite nth_error_map. rewrite H. simpl.
      destruct blk as [|i blk].
      { inv WFP. rewrite Forall_forall in H1.
        eapply nth_error_In in H. eapply H1 in H. inv H.
        red in H2. ss; lia. }
      simpl. auto.
    + econs.
    + econs.
  - inv TGT; clarify. esplits.
    + econs.
    + econs. econs; eauto.
      * exploit tgt_inv; try eapply FROM; eauto. i. des.
        inv x1; [inv MATCH|]. clarify.
        destruct pc as [b o]. destruct pc' as [b' o'].
        exploit block_always_terminator_prog; try eapply x0; eauto. i. des.
        exploit pc_sync_next; eauto. simpl. i. rewrite x2.
        replace (add (add o' 1) 1)%nat with (o' + 2) by lia. auto.
      * split; ii.
        { des. rewrite t_update_neq; eauto. }
        { rewrite t_update_eq. eauto. }
    + econs.
    + econs.


  - inv TGT; clarify. 1: destruct stk. 1: cbn in STK; inv STK.
    +
      simpl in STK.
      destruct (ret_sync p c) eqn:RET_C; [|discriminate].
      destruct (map_opt (ret_sync p) stk) eqn:MAP_REST; [|discriminate].
      inv STK.

      exploit tgt_inv; try eapply FROM; eauto. i. des.
      inv x1.
      {
        inv MATCH. eapply unused_prog_lookup in UNUSED2; eauto. ss. }

      exploit wf_ret_uslh_src; eauto. i. des.

      assert (C_IFF: c = (fst pc'', S o_src) <-> pc'0 = pc'').
      { split; intro; subst.
        - assert (ret_sync p (fst pc'', S o_src) = Some pc'0) by exact RET_C.
          rewrite x2 in H. congruence.
        - destruct c, pc''. exploit ret_sync_inj; [exact RET_C | exact x2 |]. i. des. subst. auto. }
      destruct pc'' as [l_tgt o_tgt].
      simpl in C_IFF, x1, x2, x3, x4, x5.

      assert (MS_EQ: (fst c =? l_tgt)%nat && (snd c =? S o_src)%nat =
                      (fst pc'0 =? l_tgt)%nat && (snd pc'0 =? o_tgt)%nat).
      { destruct c as [c1 c2]. destruct pc'0 as [p1 p2]. simpl in *.
        destruct C_IFF as [CF1 CF2].
        destruct (Nat.eqb_spec c1 l_tgt); destruct (Nat.eqb_spec c2 (S o_src));
        destruct (Nat.eqb_spec p1 l_tgt); destruct (Nat.eqb_spec p2 o_tgt);
        subst; simpl; auto;
        exfalso;
        try (assert (H_eq: (l_tgt, S o_src) = (l_tgt, S o_src)) by auto;
             apply CF1 in H_eq; congruence);
        try (assert (H_eq: (l_tgt, o_tgt) = (l_tgt, o_tgt)) by auto;
             apply CF2 in H_eq; congruence). }
      exists ([DRet (l_tgt, S o_src)]), [].
      exists (S_Running ((l_tgt, S o_src), r, m, stk,
               ms || negb ((fst c =? l_tgt)%nat && (snd c =? S o_src)%nat))).
      split; [|split].
      { replace ([DRet (l_tgt, S o_src)] : list direction) with ([DRet (l_tgt, S o_src)] ++ (@nil direction)) by apply app_nil_r.
        replace ([] : list observation) with ([] ++ @nil observation) by auto.
        econs; [eapply ISMI_Ret; eauto | econs]. }
      { rewrite MS_EQ.
        replace o_tgt with ((o_tgt - 2) + 2) at 2 by lia.
        destruct x1 as [A SCALL]. des.
        eapply match_cfgs_ext_ret2.
        - simpl. rewrite Nat.sub_0_r. exact x3.
        - replace (S o_src - 1) with (o_src - 0) by lia. eauto.
        - lia.
        - replace (o_tgt - 2 + 2) with o_tgt by lia. exact x4.
        - inv REG. eauto.
        - exact MSC.
        - exact MAP_REST.
        -
          replace (o_tgt - 2 + 2) with o_tgt by lia.
          destruct pc'0 as [p1 p2]. simpl in MS.

          ss. rewrite MS. ss.
          destruct ((p1 =? l_tgt)%nat && (p2 =? o_tgt)%nat) eqn:CMP; simpl.
          {
            red in REG. destruct REG as [_ MSF_EQ]. rewrite MSF_EQ.
            destruct ms; auto. }
          {
            destruct ms; auto. } }
      { repeat econs. unfold match_dir. simpl. eauto. }
    + exists [], [], S_Term. split.
      * change (@nil direction) with (@nil direction ++ []).
        change (@nil observation) with (@nil observation ++ []).
        econs 2. 2: econs.
        destruct stk; ss. 2: destruct (ret_sync p c); [destruct (map_opt (ret_sync p) stk); discriminate |discriminate].
        econs. exploit tgt_inv; try eapply FROM; eauto. i. des. inv x1. 2: assumption.
        inv MATCH. eapply unused_prog_lookup in UNUSED2; eauto. now destruct UNUSED2.
      * split; repeat econs.

  - inv TGT; clarify.
    exists [], []. esplits; try sfby (repeat econs).
    econs. econs.
    + hexploit block_always_terminator_prog; eauto. i. des.
      hexploit pc_sync_next; eauto. i. simpl in H0.
      replace o with (add (o - 1) 1) by lia. simpl.
      replace (add (o' + 2) 1) with (o' + 3) by lia. auto.
    + split; [|ss].
      i. des. rewrite t_update_neq; eauto.
    + eauto.
    + eauto.
Qed.

Lemma multi_ideal_inst_trans2
  p ic1 ic2 ic3 ds1 ds2 os1 os2
  (STEPS1: p |- <(( ic1 ))> -->i*_ ds1 ^^ os1 <(( ic2 ))>)
  (STEPS2: p |- <(( ic2 ))> -->i*_ ds2 ^^ os2 <(( ic3 ))>) :
  p |- <(( ic1 ))> -->i*_ ds1 ++ ds2 ^^ os1 ++ os2 <(( ic3 ))>.
Proof.
  ginduction STEPS1; ii; ss.
  do 2 rewrite <- app_assoc. econs; eauto.
Qed.

Lemma ultimate_slh_bcc' (p: prog) ic1 sc1 sc2 ds os
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (MATCH: match_cfgs_ext p ic1 sc1)
  n
  (TGT: uslh_prog p |- <(( sc1 ))> -->*_ ds^^os^^n <(( sc2 ))>) :
  exists os' ds' ic2, p |- <(( ic1 ))> -->i*_ ds' ^^ os' <(( ic2 ))>
      /\ match_cfgs_ext p ic2 sc2 /\ match_ds p ds' ds /\ match_obs p os' os.
Proof.
  ginduction n; ii.
  { inv TGT. esplits; eauto; econs. }
  inv TGT.
  exploit ultimate_slh_bcc_single; try eapply H0; eauto.
  i. des.
  exploit IHn; try eapply H5; eauto.
  i. des. esplits.
  - eapply multi_ideal_inst_trans2; eauto.
  - eauto.
  - clear - x2 x6.
    unfold match_ds.
    apply Forall2_app; assumption.
  - clear - x3 x7.
    apply Forall2_app; assumption.
Qed.

Lemma ultimate_slh_bcc (p: prog) : forall n ic1 sc1 sc2 ds os,
  no_ct_prog p ->
  wf_prog p ->
  unused_prog msf p ->
  unused_prog callee p ->
  match_cfgs p ic1 sc1 ->
  uslh_prog p |- <(( S_Running sc1 ))> -->*_ds^^os^^n <(( sc2 ))> ->
  exists os' ds' ic2, p |- <(( S_Running ic1 ))> -->i*_ ds' ^^ os' <(( ic2 ))>
               /\ match_ds p ds' ds /\ match_obs p os' os.
Proof.
  ii. exploit ultimate_slh_bcc'; try eapply H5; eauto.
  { econs. eauto. }
  i. des. esplits; eauto.
Qed.

Definition first_blk_call (p: prog) : Prop :=
  match nth_error p 0 with
  | None => False
  | Some (blk, b) => if b then True else False
  end.

Lemma ultimate_slh_bcc_init
  (p: prog) n ir im sc1 sr sm sc2 ds os
  (NCT: no_ct_prog p)
  (FST: first_blk_call p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (SC1: sc1 = ((0,0), sr, sm, @nil cptr, true, false))
  (INIT1: Rsync p ir sr false)
  (INIT2: sr ! callee = FP (0,0))
  (INIT3: Msync p im sm)
  (TGT: uslh_prog p |- <(( S_Running sc1 ))> -->*_ds^^os^^n <(( sc2 ))>) :
  exists os' ds' ic2, p |- <(( S_Running ((0,0), ir, im, [], false) ))> -->i*_ ds' ^^ os' <(( ic2 ))>
               /\ match_ds p ds' ds /\ match_obs p os' os.
Proof.
  destruct n.
  { inv TGT. esplits; econs. }
  assert (CT: (uslh_prog p)[[(0, 0)]] = Some <{{ ctarget }}>).
  { red in FST. des_ifs. eapply ctarget_exists; eauto. }
  destruct n.
  { inv TGT. inv H5. inv H0; clarify. ss. esplits; do 3 econs. }
  exploit head_call_target; eauto. i. des; clarify.
  replace ((0,0) + 1) with (0, 1) in x2 by ss.
  inv TGT. inv H0; clarify. inv H5. inv H0; clarify. simpl.
  exploit ultimate_slh_bcc; try eapply H6; eauto.
  econs; try sfby ss.
  - red in FST. des_ifs_safe.
    unfold pc_sync. rewrite nth_error_map. rewrite Heq. simpl.
    destruct l.
    { red in WFP. des. eapply nth_error_In in Heq. rewrite Forall_forall in WFP0.
      eapply WFP0 in Heq. red in Heq. des. ss. }
    simpl. auto.
  - inv INIT1. split; ii.
    + des. rewrite t_update_neq; eauto.
    + rewrite t_update_eq. simpl. rewrite INIT2. ss.
Qed.

Definition seq_same_obs p pc r1 r2 m1 m2 stk : Prop :=
  forall os1 os2 c1 c2,
  p |- <(( S_Running (pc, r1, m1, stk) ))> -->*^ os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, stk) ))> -->*^ os2 <(( c2 ))> ->
  (Utils.prefix os1 os2) \/ (Utils.prefix os2 os1).

Definition spec_same_obs p pc r1 r2 m1 m2 stk b : Prop :=
  forall ds n m os1 os2 c1 c2,
  p |- <(( S_Running (pc, r1, m1, stk, b, false) ))> -->*_ds^^os1^^n <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, stk, b, false) ))> -->*_ds^^ os2^^m <(( c2 ))> ->
  (Utils.prefix os1 os2) \/ (Utils.prefix os2 os1).

Definition ideal_same_obs p pc r1 r2 m1 m2 stk : Prop :=
  forall ds os1 os2 c1 c2,
  p |- <(( S_Running (pc, r1, m1, stk, false) ))> -->i*_ds^^os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, stk, false) ))> -->i*_ds^^ os2 <(( c2 ))> ->
  (Utils.prefix os1 os2) \/ (Utils.prefix os2 os1).

Definition relative_secure (p:prog) (trans1 : prog -> prog)
  (r1 r2 r1' r2' : reg) (m1 m2 m1' m2' : mem): Prop :=
  seq_same_obs p (0,0) r1 r2 m1 m2 [] ->
  Rsync p r1 r1' false -> Rsync p r2 r2' false ->
  Msync p m1 m1' -> Msync p m2 m2' ->
  spec_same_obs (trans1 p) (0,0) r1' r2' m1' m2' [] true.



Require Import Stdlib.Program.Equality.

Lemma multi_seq_app p c1 os1 c2 os2 c3:
  p |- <(( c1 ))> -->*^ os1 <(( c2 ))> ->
  p |- <(( c2 ))> -->*^ os2 <(( c3 ))> ->
  p |- <(( c1 ))> -->*^ os1 ++ os2 <(( c3 ))>.
Proof.
  intro H. dependent induction H.
  - intro H. cbn. assumption.
  - intro Hlast. apply IHmulti_seq_inst in Hlast.
    rewrite <- app_assoc. econstructor; eassumption.
Qed.

Lemma multi_seq_rcons p c1 os1 c2 os2 c3:
  p |- <(( c1 ))> -->*^ os1 <(( c2 ))> ->
  p |- <(( c2 ))> -->^ os2 <(( c3 ))> ->
  p |- <(( c1 ))> -->*^ os1 ++ os2 <(( c3 ))>.
Proof.
  intros Hmulti Hstep.
  eapply multi_seq_inst_trans in Hstep. 2: constructor.
  rewrite app_nil_r in Hstep.
  eapply multi_seq_app; eassumption.
Qed.

Lemma ideal_step_one_or_no_directive p pc r m stk b ds os c:
  p |- <(( S_Running (pc, r, m, stk, b) ))> -->i_ ds ^^ os <(( c ))> ->
  ds = [] \/ exists d, ds = [d].
Proof.
  inversion 1; subst; try now left.
  all: right; eexists; reflexivity.
Qed.

Lemma ideal_pc_determines_dir_obs_count p pc r1 r2 m1 m2 stk b ds1 ds2 os1 os2 c1 c2:
  p |- <(( S_Running (pc, r1, m1, stk, b) ))> -->i_ ds1 ^^ os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, stk, b) ))> -->i_ ds2 ^^ os2 <(( c2 ))> ->
  Datatypes.length ds1 = Datatypes.length ds2 /\ Datatypes.length os1 = Datatypes.length os2.
Proof.
  inversion 1; inversion 1; subst; split; try reflexivity.
  all: try congruence.
Qed.

Lemma seq_pc_determines_obs_count p pc r1 r2 m1 m2 stk os1 os2 c1 c2:
  p |- <(( S_Running (pc, r1, m1, stk) ))> -->^ os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, stk) ))> -->^ os2 <(( c2 ))> ->
      Datatypes.length os1 = Datatypes.length os2.
Proof.
  inversion 1 ; inversion 1; try congruence. all: reflexivity.
Qed.

Lemma app_eq_len_tail_eq A (l1a l1b  l2a l2b: list A):
  l1a ++ l1b = l2a ++ l2b ->
  Datatypes.length l1a = Datatypes.length l2a ->
  l1b = l2b.
Proof.
  intros Heq Hlen.
  induction l1a in l2a, Heq, Hlen |- *; destruct l2a.
  - assumption.
  - cbn in *. congruence.
  - cbn in *. congruence.
  - cbn in Heq. inv Heq.
    eapply IHl1a. 1: eassumption.
    cbn in Hlen. now inv Hlen.
Qed.

Lemma seq_steps_preserves_seq_same_obs p pc r1 r2 m1 m2 stk os1 os2 pc' r1' r2' m1' m2' stk':
  seq_same_obs p pc r1 r2 m1 m2 stk ->
  p |- <(( S_Running (pc, r1, m1, stk) ))> -->^ os1 <(( S_Running (pc', r1', m1', stk') ))> ->
  p |- <(( S_Running (pc, r2, m2, stk) ))> -->^ os2 <(( S_Running (pc', r2', m2', stk') ))> ->
  seq_same_obs p pc' r1' r2' m1' m2' stk'.
Proof.
  intros Hseq_same_obs Hstep1 Hstep2.
  unfold seq_same_obs.
  intros os1' os2' c1 c2 Hmulti1 Hmulti2.
  eapply multi_seq_inst_trans in Hmulti1, Hmulti2. 2,3: eassumption.
  specialize (Hseq_same_obs _ _ _ _ Hmulti1 Hmulti2).
  destruct Hseq_same_obs as [ [or1 H] | [or2 H] ].
  - left. exists or1. rewrite <- app_assoc in H.
    eapply app_eq_len_tail_eq. 1: eassumption.
    eapply seq_pc_determines_obs_count; eassumption.
  - right. exists or2. rewrite <- app_assoc in H.
    eapply app_eq_len_tail_eq. 1: eassumption.
    eapply seq_pc_determines_obs_count; eassumption.
Qed.

Lemma ideal_nonspec_seq p pc r m stk ds os pc' r' m' stk':
  p |- <(( S_Running (pc, r, m, stk, false) ))> -->i_ ds ^^ os <(( S_Running (pc', r', m', stk', false) ))> ->
  p |- <(( S_Running (pc, r, m, stk) ))> -->^ os <(( S_Running (pc', r', m', stk') ))>.
Proof.
  inversion 1; subst; try (econstructor; eassumption).
  - eapply SSMI_Branch. 1,2: eassumption.
    cbn in H16. apply (f_equal negb) in H16. cbn in H16.
    rewrite negb_involutive in H16.
    symmetry in H16. apply eqb_prop in H16 as ->. reflexivity.
  - cbn in H14. apply (f_equal negb) in H14. cbn in H14. rewrite negb_involutive in H14.
    symmetry in H14.
    apply andb_prop in H14. rewrite! Nat.eqb_eq in H14. des.
    destruct pc', l; cbn in *; subst.
    econstructor; eassumption.
  - inv H. ss. symmetry in H10. rewrite negb_false_iff in H10.
    apply andb_prop in H10. des. destruct pc', pc'0; ss.
    rewrite Nat.eqb_eq in H0, H10. clarify. econs; eauto.
Qed.

Lemma multi_ideal_ms_monotonic {p pc r m stk ms ds os pc' r' m' stk'}:
  p |- <(( S_Running (pc, r, m, stk, ms) ))> -->i*_ ds ^^ os <(( S_Running (pc', r', m', stk', false) ))> ->
  ms = false.
Proof.
  intro Hmulti.
  dependent induction Hmulti.
  - reflexivity.
  - destruct ic2. 2-4: inv Hmulti; inv H0.
    destruct a as [ [ [ [pc'' r''] m''] stk''] ms''].
    erewrite IHHmulti with (ms := ms'') in H. 2, 3: reflexivity.
    inv H; try reflexivity.
    + symmetry in H16. now apply orb_false_elim in H16.
    + symmetry in H14. now apply orb_false_elim in H14.
    + symmetry in H14. now apply orb_false_elim in H14.
Qed.

Lemma multi_ideal_nonspec_seq p pc r m stk ds os pc' r' m' stk':
  p |- <(( S_Running (pc, r, m, stk, false) ))> -->i*_ ds ^^ os <(( S_Running (pc', r', m', stk', false) ))> ->
  p |- <(( S_Running (pc, r, m, stk) ))> -->*^ os <(( S_Running (pc', r', m', stk') ))>.
Proof.
  intro H. dependent induction H.
  - constructor.
  - assert (exists pc'' r'' m'' stk'', ic2 = S_Running (pc'', r'', m'', stk'', false)).
    {
      inv H0. 1: repeat eexists; reflexivity.
      inv H1; repeat eexists.
      all: try (rewrite (multi_ideal_ms_monotonic H2); reflexivity).
      3, 5: inv H2; inv H1.
      all: apply multi_ideal_ms_monotonic, orb_false_elim in H2 as [-> _].
      all: reflexivity.
      Unshelve.
      all: assumption.
    }
    destruct H1 as (pc'' & r'' & m'' & stk'' & ->).
    econstructor.
    + eapply ideal_nonspec_seq. eassumption.
    + eapply IHmulti_ideal_inst; reflexivity.
Qed.

Lemma ideal_nonspec_step_preserves_seq_same_obs p pc r1 r2 m1 m2 stk ds os1 os2 pc' r1' r2' m1' m2' stk':
  seq_same_obs p pc r1 r2 m1 m2 stk ->
  p |- <(( S_Running (pc, r1, m1, stk, false ) ))> -->i_ ds ^^ os1 <(( S_Running (pc', r1', m1', stk', false) ))> ->
  p |- <(( S_Running (pc, r2, m2, stk, false ) ))> -->i_ ds ^^ os2 <(( S_Running (pc', r2', m2', stk', false) ))> ->
  seq_same_obs p pc' r1' r2' m1' m2' stk'.
Proof.
  intros Hsso Hst1 Hst2.
  eapply seq_steps_preserves_seq_same_obs. 1: eassumption.
  all: eapply ideal_nonspec_seq; eassumption.
Qed.

Lemma multi_ideal_nonspec_step_preserves_seq_same_obs p pc r1 r2 m1 m2 stk ds os1 os2 pc' r1' r2' m1' m2' stk':
  seq_same_obs p pc r1 r2 m1 m2 stk ->
  p |- <(( S_Running (pc, r1, m1, stk, false ) ))> -->i*_ ds ^^ os1 <(( S_Running (pc', r1', m1', stk', false) ))> ->
  p |- <(( S_Running (pc, r2, m2, stk, false ) ))> -->i*_ ds ^^ os2 <(( S_Running (pc', r2', m2', stk', false) ))> ->
  Datatypes.length os1 = Datatypes.length os2 ->
  seq_same_obs p pc' r1' r2' m1' m2' stk'.
Proof.
  intros Hsso Hsteps1%multi_ideal_nonspec_seq Hsteps2%multi_ideal_nonspec_seq Hlen.
  intros os1' os2' c1' c2 Hsteps1' Hsteps2'.
  edestruct Hsso. 1, 2: eapply multi_seq_app; eassumption.
  - left.
    destruct H. exists x.
    rewrite <- app_assoc in H.
    eapply app_eq_len_tail_eq. all: eassumption.
  - right.
    destruct H. exists x.
    rewrite <- app_assoc in H.
    eapply app_eq_len_tail_eq. 1: eassumption.
    symmetry. assumption.
Qed.

Lemma ideal_multi_no_dirs_run_or_term p pc r m stk b os ic:
  p |- <(( S_Running (pc, r, m, stk, b) ))> -->i*_ [] ^^ os <(( ic ))> ->
  exists pc' r' m' stk', p |- <(( S_Running (pc, r, m, stk, b) ))> -->i*_ [] ^^ os <(( S_Running (pc', r', m', stk', b) ))>
                 /\  (ic = S_Running (pc', r', m', stk', b) \/ ic = S_Term /\ p |- <(( S_Running (pc', r', m', stk', b) ))> -->i_ [] ^^ [] <(( S_Term ))>).
Proof.
  intros H. dependent induction H.
  - repeat eexists. 2: left; reflexivity.
    constructor.
  - apply app_eq_nil in x as [-> ->].
    inv H.
    + edestruct IHmulti_ideal_inst as (pc' & r' & m' & stk' & Hsteps & H). 1, 2: reflexivity.
      repeat eexists. 2: exact H.
      change (@nil direction) with ((@nil direction) ++ []).
      econstructor. 2: eassumption.
      now constructor.
    + edestruct IHmulti_ideal_inst as (pc' & r' & m' & stk' & Hsteps & H). 1, 2: reflexivity.
      repeat eexists. 2: exact H.
      change (@nil direction) with ((@nil direction) ++ []).
      econstructor. 2: eassumption.
      now constructor.
    + edestruct IHmulti_ideal_inst as (pc' & r' & m' & stk' & Hsteps & H). 1, 2: reflexivity.
      repeat eexists. 2: exact H.
      change (@nil direction) with ((@nil direction) ++ []).
      econstructor. 2: eassumption.
      econstructor 3; eauto.
    + edestruct IHmulti_ideal_inst as (pc' & r' & m' & stk' & Hsteps & H). 1, 2: reflexivity.
      repeat eexists. 2: exact H.
      change (@nil direction) with ((@nil direction) ++ []).
      econstructor. 2: eassumption.
      now constructor.
    + edestruct IHmulti_ideal_inst as (pc' & r' & m' & stk' & Hsteps & H). 1, 2: reflexivity.
      repeat eexists. 2: exact H.
      change (@nil direction) with ((@nil direction) ++ []).
      econstructor. 2: eassumption.
      econstructor; try eassumption. reflexivity.
    + edestruct IHmulti_ideal_inst as (pc' & r' & m' & stk' & Hsteps & H). 1, 2: reflexivity.
      repeat eexists. 2: exact H.
      change (@nil direction) with ((@nil direction) ++ []).
      econstructor. 2: eassumption.
      econstructor; try eassumption. reflexivity.
    + edestruct IHmulti_ideal_inst as (pc'' & r' & m' & stk' & Hsteps & H). 1, 2: reflexivity.
      repeat eexists. 2: exact H.
      change (@nil direction) with ((@nil direction) ++ []).
      econstructor. 2: eassumption.
      now constructor.





    + inv H0. 2: inv H1.
      repeat eexists. 2: right; split.
      * cbn; constructor.
      * reflexivity.
      * now constructor.
Qed.

Lemma ideal_eval_multi_exec_split {p pc r1 r2 m1 m2 stk ds os1 os2 c1 c2}:
  seq_same_obs p pc r1 r2 m1 m2 stk ->
  p |- <(( S_Running (pc, r1, m1, stk, false) ))> -->i*_ ds ^^ os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, stk, false) ))> -->i*_ ds ^^ os2 <(( c2 ))> ->
  exists pc1' pc2' r1' r2' m1' m2' stk1' stk2' ds' os1' os2',
    p |- <(( S_Running (pc, r1, m1, stk, false) ))> -->i*_ ds' ^^ os1' <(( S_Running (pc1', r1', m1', stk1', false) ))> /\
    p |- <(( S_Running (pc, r2, m2, stk, false) ))> -->i*_ ds' ^^ os2' <(( S_Running (pc2', r2', m2', stk2', false) ))> /\
   (ds' = ds /\ os1' = os1 /\ os2' = os2
    /\ (c1 = S_Running (pc1', r1', m1', stk1', false) \/ c1 = S_Term /\ p |- <(( S_Running (pc1', r1', m1', stk1', false) ))> -->i_ [] ^^ [] <(( S_Term ))>)
    /\ (c2 = S_Running (pc2', r2', m2', stk2', false) \/ c2 = S_Term /\ p |- <(( S_Running (pc2', r2', m2', stk2', false) ))> -->i_ [] ^^ [] <(( S_Term))>)
    \/ exists ds'' os1'' os2'',
       ds = ds' ++ ds'' /\ os1 = os1' ++ os1'' /\ os2 = os2' ++ os2'' /\ pc1' = pc2' /\ stk1' = stk2' /\ Datatypes.length os1' = Datatypes.length os2' /\
       (
        c1 = S_Fault /\ c2 = S_Fault /\ p |- <(( S_Running (pc1', r1', m1', stk1', false) ))> -->i_ ds'' ^^ os1'' <(( S_Fault ))> /\ p |- <(( S_Running (pc2', r2', m2', stk2', false) ))> -->i_ ds'' ^^os2'' <(( S_Fault))>
        \/
        exists pc'' r1'' r2'' m1'' m2'' stk'' d ds''' o1 os1''' o2 os2''',
        ds'' = d :: ds''' /\ os1'' = o1 ++ os1''' /\ os2'' = o2 ++ os2''' /\
        p |- <(( S_Running (pc1', r1', m1', stk1', false) ))> -->i_ [d] ^^ o1 <(( S_Running (pc'', r1'', m1'', stk'', true) ))> /\ p |- <(( S_Running (pc'', r1'', m1'', stk'', true) ))> -->i*_ ds''' ^^ os1''' <(( c1 ))> /\
        p |- <(( S_Running (pc2', r2', m2', stk2', false) ))> -->i_ [d] ^^ o2 <(( S_Running (pc'', r2'', m2'', stk'', true) ))> /\ p |- <(( S_Running (pc'', r2'', m2'', stk'', true) ))> -->i*_ ds''' ^^ os2''' <(( c2 ))>
       )
   ).
Proof.
  intros Hseq_same Hexec1 Hexec2.
  dependent induction Hexec1 generalizing pc r1 r2 m1 m2 stk os2 Hseq_same; dependent destruction Hexec2.
  - repeat eexists. 1, 2: eapply multi_ideal_inst_refl.
    left. repeat split; try left; reflexivity.
  - apply app_eq_nil in x as [-> ->].
    eapply multi_ideal_inst_trans in Hexec2. 2: eassumption.
    apply ideal_multi_no_dirs_run_or_term in Hexec2 as (pc' & r' & m' & stk' & Hstp & Hrt).
    repeat eexists.
    1: eapply multi_ideal_inst_refl.
    2: left; repeat split.
    2: now left.
    all: eassumption.
  - symmetry in x. apply app_eq_nil in x as [-> ->].
    eapply multi_ideal_inst_trans in Hexec1. 2: eassumption.
    apply ideal_multi_no_dirs_run_or_term in Hexec1 as (pc' & r' & m' & stk' & Hstp & Hrt).
    repeat eexists.
    2: eapply multi_ideal_inst_refl.
    2: left; repeat split.
    3: now left.
    all: eassumption.
  - inversion H; inversion H0; try congruence; subst; cbn in *; subst.

    + eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
      destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      destruct H3 as [H3 | H3].
      * repeat destruct H3 as [-> H3].
        repeat eexists. 3: left; repeat split; try reflexivity; apply H3.
        all: change ds2 with ([] ++ ds2).
        1: change os0 with ([] ++ os0).
        2: change os3 with ([] ++ os3).
        all: econstructor; eassumption.
      * repeat eexists. 3: right; eassumption.
        all: change x7 with ([] ++ x7).
        1: change x8 with ([] ++ x8).
        2: change x9 with ([] ++ x9).
        all: econstructor; eassumption.
    + eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
      destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      destruct H3 as [H3 | H3].
      * repeat destruct H3 as [-> H3].
        repeat eexists. 3: left; repeat split; try reflexivity; apply H3.
        all: change ds2 with ([] ++ ds2).
        1: change os0 with ([] ++ os0).
        2: change os3 with ([] ++ os3).
        all: econstructor; eassumption.
      * repeat eexists. 3: right; eassumption.
        all: change x9 with ([] ++ x9).
        1: change x10 with ([] ++ x10).
        2: change x11 with ([] ++ x11).
        all: econstructor; eassumption.
    + eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
      destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      destruct H3 as [H3 | H3].
      * repeat destruct H3 as [-> H3].
        repeat eexists. 3: left; repeat split; try reflexivity; apply H3.
        all: change ds2 with ([] ++ ds2).
        1: change (ODiv v1 v2 :: os0) with ([ODiv v1 v2] ++ os0).
        2: change (ODiv v0 v3 :: os3) with ([ODiv v0 v3] ++ os3).
        all: econstructor; eassumption.
        * repeat destruct H3 as [? H3]. subst. repeat eexists.
          3: {
              right. do 3 eexists. repeat (match goal with | |- ?A /\ ?B => split end). 7: eassumption. 2, 3: rewrite app_comm_cons; reflexivity. all: try reflexivity. simpl. f_equal. assumption.
            }
          all: change x9 with ([] ++ x9).
            1: change (ODiv v1 v2 :: x10) with ([ODiv v1 v2] ++ x10).
            2: change (ODiv v0 v3 :: x11) with ([ODiv v0 v3] ++ x11).
            all: econstructor; eassumption.
    + rewrite H6 in H19. inv H19. inv x.
      assert (not_zero n' = not_zero n'0).
      {
        clear Hexec1 IHHexec1 Hexec2.
        unfold seq_same_obs in Hseq_same.
        specialize (Hseq_same ([OBranch (not_zero n')]) ([OBranch (not_zero n'0)])).
        edestruct Hseq_same.
        - rewrite <- app_nil_r. econstructor. 2: constructor.
          eapply SSMI_Branch. 1,2: eassumption. reflexivity.
        - rewrite <- app_nil_r. econstructor. 2: constructor.
          eapply SSMI_Branch. 1,2: eassumption. reflexivity.
        - destruct H1 as [? H1]. now inv H1.
        - destruct H1 as [? H1]. now inv H1.
      }
      rewrite H1 in *. clear H1.
      destruct (Bool.eqb (not_zero n'0) b').
      * cbn in *.
        eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
        destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
        repeat eexists.
        1,2: change (DBranch b' :: ds2) with ([DBranch b'] ++ ds2).
        1: change (OBranch (not_zero n'0) :: os0) with ([OBranch (not_zero n'0)] ++ os0).
        2: change (OBranch (not_zero n'0) :: os3) with ([OBranch (not_zero n'0)] ++ os3).
        1,2: econstructor 2; eassumption.
        destruct H3 as [H3 | H3].
        -- repeat destruct H3 as [-> H3]. left. repeat split; try reflexivity; apply H3.
        -- right. repeat destruct H3 as [? H3]. subst.
           repeat eexists. 2: exact H3.
           simpl. f_equal. assumption.
      * repeat eexists. 1, 2: econstructor.
        right. repeat eexists.
        right.
        repeat eexists. 1, 2: rewrite cons_app; reflexivity. all: eassumption.
    + rewrite H9 in H18. inv H18.
      eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
      destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      destruct H3 as [H3 | H3].
      * repeat destruct H3 as [-> H3].
        repeat eexists. 3: left; repeat split; try reflexivity; apply H3.
        all: change ds2 with ([] ++ ds2).
        1: change os0 with ([] ++ os0).
        2: change os3 with ([] ++ os3).
        all: econstructor; eassumption.
      * repeat eexists. 3: right; eassumption.
        all: change x7 with ([] ++ x7).
        1: change x8 with ([] ++ x8).
        2: change x9 with ([] ++ x9).
        all: econstructor; eassumption.
    + eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
      destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      destruct H3 as [H3 | H3].
      * repeat destruct H3 as [-> H3].
        repeat eexists. 3: left; repeat split; try reflexivity; apply H3.
        all: change ds2 with ([] ++ ds2).
        1: change (OLoad n :: os0) with ([OLoad n] ++ os0).
        2: change (OLoad n0 :: os3) with ([OLoad n0] ++ os3).
        all: econstructor; eassumption.
      * repeat destruct H3 as [? H3]. subst. repeat eexists. 3: {
                                                             right. do 3 eexists. repeat (match goal with | |- ?A /\ ?B => split end). 7: eassumption. 2, 3: rewrite app_comm_cons; reflexivity. all: try reflexivity. simpl. f_equal. assumption.
                                                           }
                                                           all: change x9 with ([] ++ x9).
        1: change (OLoad n :: x10) with ([OLoad n] ++ x10).
        2: change (OLoad n0 :: x11) with ([OLoad n0] ++ x11).
        all: econstructor; eassumption.
    + eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
      destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      destruct H3 as [H3 | H3].
      * repeat destruct H3 as [-> H3].
        repeat eexists. 3: left; repeat split; try reflexivity; apply H3.
        all: change ds2 with ([] ++ ds2).
        1: change (OStore n :: os0) with ([OStore n] ++ os0).
        2: change (OStore n0 :: os3) with ([OStore n0] ++ os3).
        all: econstructor; eassumption.
      * repeat destruct H3 as [? H3]. subst. repeat eexists. 3: {
                                                             right. do 3 eexists. repeat (match goal with |- ?A /\ ?B => split end). 7: eassumption. 2, 3: rewrite app_comm_cons; reflexivity.
                                                             all: try reflexivity.
                                                             simpl. f_equal. assumption.
                                                           }
                                                           all: change x7 with ([] ++ x7).
        1: change (OStore n :: x8) with ([OStore n] ++ x8).
        2: change (OStore n0 :: x9) with ([OStore n0] ++ x9).
        all: econstructor; eassumption.
    +
       inv x. rewrite H20 in H6. inv H6.
       assert (l = l0).
       {
         clear Hexec1 IHHexec1 Hexec2.
         unfold seq_same_obs in Hseq_same.
         specialize (Hseq_same ([OCall l]) ([OCall l0])).
         edestruct Hseq_same.
         - rewrite <- app_nil_r. econstructor. 2: constructor.
           eapply SSMI_Call. all: eassumption.
         - rewrite <- app_nil_r. econstructor. 2: constructor.
           eapply SSMI_Call. all: eassumption.
         - destruct H1 as [? H1]. now inv H1.
         - destruct H1 as [? H1]. now inv H1.
       }
       rewrite <- H1 in *.
       destruct ((fst pc' =? fst l) && (snd pc' =? snd l))%nat.
         * cbn in *.
           eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
           destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
           repeat eexists.
           1,2: change (DCall pc' :: ds2) with ([DCall pc'] ++ ds2).
           1: change (OCall l :: os0) with ([OCall l] ++ os0).
           2: change (OCall l :: os3) with ([OCall l] ++ os3).
           1,2: econstructor 2. 2: exact H2. 1: exact H. 2: exact H3. 1: exact H0.
           destruct H4 as [H4 | H4].
           -- repeat destruct H4 as [-> H4]. left. repeat split ; try reflexivity;  apply H4.
           -- right. repeat destruct H4 as [? H4]. subst.
              repeat eexists. 2: exact H4.
              simpl. f_equal. assumption.
         * repeat eexists. 1, 2: econstructor.
           right. repeat eexists. right.
           repeat eexists. 1, 2: rewrite cons_app; reflexivity. all: eassumption.
    +
      inv x. apply H25 in H12 as [H12 | H12].
      all: congruence.
    +
      inv x. apply H11 in H23 as [H23 | H23].
      all: congruence.
    +
      repeat eexists. 1, 2: constructor.
      right. repeat eexists.
      left.
      inv Hexec1. 2: inv H1.
      inv Hexec2. 2: inv H1.
      repeat split; try reflexivity. 1: assumption.
      inv x. assumption.
    +
       inv H16. inv x.
       destruct ((fst pc' =? fst pc'')%nat && (snd pc' =? snd pc'')%nat); cbn in *.
         *
           eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
           destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
           destruct H3 as [H3 | H3].
           -- repeat destruct H3 as [-> H3].
              repeat eexists. 3: left; repeat split; try reflexivity; apply H3.
              all: change (DRet pc'' :: ds2) with ([DRet pc''] ++ ds2).
              1: change os0 with ([] ++ os0).
              2: change os3 with ([] ++ os3).
              all: econstructor; eassumption.
           -- repeat destruct H3 as [? H3]. subst.
              repeat eexists. 3: {
                  right. repeat eexists. 1: rewrite app_comm_cons; reflexivity. 1: assumption.
                  exact H3.
              }
              all: change (DRet pc'' :: x7) with ([DRet pc''] ++ x7).
              all: change x9 with ([] ++ x9).
              all: change x8 with ([] ++ x8).
              all: econstructor; eassumption.
         * repeat eexists. 1, 2: econstructor.
           right. repeat eexists. right.
           repeat eexists. 1, 2: rewrite app_nil_l; reflexivity. all: eassumption.
    +
      rewrite H9 in H18. inv H18.
      eapply IHHexec1 in Hexec2. 3: reflexivity. 2: eapply ideal_nonspec_step_preserves_seq_same_obs; eassumption.
      destruct Hexec2 as (?&?&?&?&?&?&?&?&?&?&?&?&?&?).
      destruct H3 as [H3 | H3].
      * repeat destruct H3 as [-> H3].
        repeat eexists. 3: left; repeat split; try reflexivity; apply H3.
        all: change ds2 with ([] ++ ds2).
        1: change os0 with ([] ++ os0).
        2: change os3 with ([] ++ os3).
        all: econstructor; eassumption.
      * repeat eexists. 3: right; eassumption.
        all: change x8 with ([] ++ x8).
        1: change x9 with ([] ++ x9).
        2: change x10 with ([] ++ x10).
        all: econstructor; eassumption.
    +
      repeat eexists.
      1, 2: econstructor.
      left. inv Hexec1. 2: inv H1.
      inv Hexec2. 2: inv H2.
      repeat split; try reflexivity. all: right; split; [reflexivity |].
      all: assumption.
Qed.

Lemma prefix_eq_length_eq {A} {os1 os2 : list A}:
  Utils.prefix os1 os2 \/ Utils.prefix os2 os1 ->
  Datatypes.length os1 = Datatypes.length os2 ->
  os1 = os2.
Proof.
  intros [H | H].
  - intro Hlen. destruct H.
    apply (f_equal (@Datatypes.length _)) in H as H'.
    rewrite length_app in H'.
    assert (Datatypes.length x = 0) by lia.
    destruct x; [|cbn in H0; lia].
    now rewrite app_nil_r in H.
  - intro Hlen. destruct H.
    apply (f_equal (@Datatypes.length _)) in H as H'.
    rewrite length_app in H'.
    assert (Datatypes.length x = 0) by lia.
    destruct x; [|cbn in H0; lia].
    now rewrite app_nil_r in H.
Qed.

Lemma ideal_misspec_unwinding {p pc r1 r2 m1 m2 stk ds os1 os2 c1 c2}:
  p |- <(( S_Running (pc, r1, m1, stk, true) ))> -->i*_ ds ^^ os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, stk, true) ))> -->i*_ ds ^^ os2 <(( c2 ))> ->
  Utils.prefix os1 os2 \/ Utils.prefix os2 os1.
Proof.
  intros Hexec1 Hexec2.
  dependent induction Hexec1 generalizing pc r1 r2 m1 m2 stk os2; dependent destruction Hexec2.
  - left. exists []. reflexivity.
  - left. exists (os1 ++ os2). reflexivity.
  - right. exists (os1 ++ os0). reflexivity.
  - inv H; inv H0; try congruence; cbn in *; subst.
    + eapply IHHexec1; try eassumption. reflexivity.
    + eapply IHHexec1; try eassumption. reflexivity.
    + inv H10. inv H11. inv H12. inv H13.
      edestruct IHHexec1. 1: reflexivity. 1: eassumption.
      * left. now apply prefix_cons.
      * right. now apply prefix_cons.
    + inv x. rewrite H6 in H5; inv H5. inv H10. inv  H11.
      edestruct IHHexec1. 1: reflexivity. 1: eassumption.
      * left. now apply prefix_cons.
      * right. now apply prefix_cons.
    + eapply IHHexec1; try eassumption. rewrite H9 in H8. inv H8. reflexivity.
    + rewrite H9 in H8. inv H8. inv H11. inv H13.
      edestruct IHHexec1. 1: reflexivity. 1: eassumption.
      * left. now apply prefix_cons.
      * right. now apply prefix_cons.
    + rewrite H9 in H8. inv H8. inv H11. inv H12.
      edestruct IHHexec1. 1: reflexivity. 1: eassumption.
      * left. now apply prefix_cons.
      * right. now apply prefix_cons.
    + inv x. rewrite H6 in H5. inv H5. inv H7. inv H8.
      edestruct IHHexec1. 1: reflexivity. 1: eassumption.
      * left. now apply prefix_cons.
      * right. now apply prefix_cons.
    + inv H7. inv H11. inv Hexec2.
      * right. exists os0. reflexivity.
      * inv H.
    + inv H6. inv H10. inv Hexec1.
      * left. exists os3. reflexivity.
      * inv H.
    + inv Hexec1. 2: inv H.
      inv Hexec2. 2: inv H.
      inv H12. inv H10.
      left. exists []. reflexivity.
    + inv x. eapply IHHexec1; try eassumption. reflexivity.
    + eapply IHHexec1; try eassumption. reflexivity.
    + inv Hexec2. 2: inv H.
      right. exists os0. reflexivity.
Qed.

Lemma ideal_eval_relative_secure: forall p pc r1 r2 m1 m2 stk,
  seq_same_obs p pc r1 r2 m1 m2 stk ->
  ideal_same_obs p pc r1 r2 m1 m2 stk.
Proof.
  unfold ideal_same_obs. intros p pc r1 r2 m1 m2 stk Hsso ds os1 os2 c1 c2 Hexec1 Hexec2.
  pose proof (ideal_eval_multi_exec_split Hsso Hexec1 Hexec2) as (pc1' & pc2' & r1' & r2' & m1' & m2' & stk1' & stk2' & ds' & os1' & os2' & Hns1 & Hns2 & Hsplit).
  clear Hexec1 Hexec2.
  destruct Hsplit.
  2: destruct H as (ds'' & os1'' & os2''& -> & -> & -> & -> & -> & Hobslen & H); destruct H.
  - repeat destruct H as [-> H].
    apply multi_ideal_nonspec_seq in Hns1, Hns2.
    eapply Hsso; eassumption.
  - destruct H as (-> & -> & Hf1 & Hf2).
    inv Hf1; inv Hf2. rewrite H6 in H9. inv H9.
    apply multi_ideal_nonspec_seq in Hns1, Hns2.
    eapply multi_seq_rcons in Hns1, Hns2.
    2, 3: econstructor; eassumption.
    eapply Hsso; eassumption.
  - destruct H as (pc'' & r1'' & r2'' & m1'' & m2'' & stk'' & d & ds''' & o1 & os1''' & o2 & os2''' & -> & -> & ->  & Hmp1 & Hspec1 & Hmp2 & Hspec2).
    apply prefix_eq_length_eq in Hobslen. 2: eapply Hsso; eapply multi_ideal_nonspec_seq; eassumption.
    subst.
    assert (o1 = o2) as ->.
    {
      eapply multi_ideal_nonspec_step_preserves_seq_same_obs in Hsso. 2-3: eassumption. 2: reflexivity.
      clear - Hsso Hmp1 Hmp2.
      inv Hmp1; inv Hmp2.
      - rewrite H11 in H10. inv H10.
        edestruct Hsso. 1, 2: econstructor 2; [|constructor].
        1, 2: eapply SSMI_Branch; try eassumption.
        1, 2: reflexivity.
        all: do 2 rewrite app_nil_r in H.
        all: destruct H.
        all: now inv H.
      - rewrite H11 in H9. inv H9.
        edestruct Hsso. 1, 2: econstructor 2; [|econstructor].
        1, 2: eapply SSMI_Call; try eassumption.
        all: do 2 rewrite app_nil_r in H.
        all: destruct H.
        all: now inv H.
      - reflexivity.
    }
    edestruct (ideal_misspec_unwinding Hspec1 Hspec2).
    + left. now do 2 apply prefix_append_front.
    + right. now do 2 apply prefix_append_front.
Qed.

Lemma spec_eval_relative_secure_aux
  p pc r1 r2 m1 m2 stk ic1 ic2
  (ICFG1: ic1 = (pc, r1, m1, stk, false))
  (ICFG2: ic2 = (pc, r2, m2, stk, false))
  (SEQ: seq_same_obs p pc r1 r2 m1 m2 stk)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  pc' r1' r2' m1' m2' stk' sc1 sc2 b
  (SCFG1: sc1 = (pc', r1', m1', stk', b, false))
  (SCFG2: sc2 = (pc', r2', m2', stk', b, false))
  (LK1: msf_lookup_sc sc1 = N (if (ms_true_sc sc1) then 1 else 0))
  (LK2: msf_lookup_sc sc2 = N (if (ms_true_sc sc2) then 1 else 0))
  (MATCH1: match_cfgs p ic1 sc1)
  (MATCH2: match_cfgs p ic2 sc2)
  ds os1 os2 n m c1 c2
  (SSTEP1: (uslh_prog p) |- <(( S_Running sc1 ))> -->*_ds^^os1^^n <(( c1 ))>)
  (SSTEP2: (uslh_prog p) |- <(( S_Running sc2 ))> -->*_ds^^ os2^^m <(( c2 ))>):
  (Utils.prefix os1 os2) \/ (Utils.prefix os2 os1).
Proof.
  eapply ultimate_slh_bcc' in SSTEP1; eauto.
  2:{ econs. eauto. }
  des.
  eapply ultimate_slh_bcc' in SSTEP2; eauto.
  2:{ econs. eauto. }
  des. subst.
  assert (ds' = ds'0).
  { clear - SSTEP3 SSTEP6.
    induction ds in ds', ds'0, SSTEP3, SSTEP6 |-*; destruct ds', ds'0; ss.
    all: try inv SSTEP3; try inv SSTEP6.
    exploit match_dir_inj; [exact H2 | exact H3 |]. i. subst. f_equal.
    apply IHds; eauto.
  }
  subst.
  exploit (ideal_eval_relative_secure); eauto.
  clear - SSTEP4 SSTEP7.
  induction os' in os'0, os1, os2, SSTEP4, SSTEP7 |-* ; destruct os'0, os1, os2; ss.
  all: try inv SSTEP4; try inv SSTEP7.
  - left. exists (o0 :: os2). reflexivity.
  - right. exists (o :: os1). reflexivity.
  - i. assert (a = o) as ->.
    { destruct x0; inv H; inv H0; reflexivity. }
    rewrite <- !prefix_cons in x0. eapply IHos' in x0; [|exact H4 | exact H6].
    enough (o0 = o1) as ->.
    { rewrite <- !prefix_cons. assumption. }
    eapply match_ob_functional; eauto.
Qed.

Lemma spec_eval_relative_secure_init_aux
  p r1 r2 m1 m2
  (FST: first_blk_call p)
  (SEQ: seq_same_obs p (0,0) r1 r2 m1 m2 [])
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  r1' r2' m1' m2' sc1 sc2
  (SCFG1: sc1 = ((0,0), r1', m1', [], true, false))
  (SCFG2: sc2 = ((0,0), r2', m2', [], true, false))
  (INIT1: r1' ! callee = FP (0, 0))
  (INIT2: r2' ! callee = FP (0, 0))
  (MATCH1: Rsync p r1 r1' false)
  (MATCH2: Rsync p r2 r2' false)
  (MMATCH1: Msync p m1 m1')
  (MMATCH2: Msync p m2 m2')
  ds os1 os2 n m sc1' sc2'
  (SSTEP1: (uslh_prog p) |- <(( S_Running sc1 ))> -->*_ds^^os1^^n <(( sc1' ))>)
  (SSTEP2: (uslh_prog p) |- <(( S_Running sc2 ))> -->*_ds^^ os2^^m <(( sc2' ))>):
  (Utils.prefix os1 os2) \/ (Utils.prefix os2 os1).
Proof.
  eapply ultimate_slh_bcc_init in SSTEP1; eauto. des.
  eapply ultimate_slh_bcc_init in SSTEP2; eauto. des. subst.
  assert (ds'0 = ds') as ->.
  { clear - SSTEP0 SSTEP4. induction SSTEP0 in ds'0, SSTEP4 |-*; inv SSTEP4. 1: reflexivity.
    exploit match_dir_inj; [exact H | exact H3|]. i. subst. f_equal. apply IHSSTEP0. exact H4. }
  exploit ideal_eval_relative_secure; eauto. i.
  clear - x0 SSTEP3 SSTEP5.
  induction SSTEP3 in os'0, os2, SSTEP5, x0 |-*; inv SSTEP5.
  - assumption.
  - left. now exists (y :: l').
  - right. now exists (y :: l').
  - assert (x = x1) as ->.
    { destruct x0, H2; inv H2; reflexivity. }
    enough (y = y0) as ->.
    { rewrite <- !prefix_cons in x0 |- *. firstorder. }
    eapply match_ob_functional; eauto.
Qed.

Lemma spec_eval_relative_secure
  p r1 r2 r1' r2' m1 m2 m1' m2'
  (FST: first_blk_call p)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (CALLEE1: r1' ! callee = FP (0, 0))
  (CALLEE2: r2' ! callee = FP (0, 0))
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p) :
  relative_secure p (uslh_prog) r1 r2 r1' r2' m1 m2 m1' m2'.
Proof.
  red. ii. eapply spec_eval_relative_secure_init_aux.
  11:{ eapply H0. }
  11:{ eapply H1. }
  all: eauto.
Qed.

