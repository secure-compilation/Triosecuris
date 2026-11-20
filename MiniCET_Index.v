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
Set Default Goal Selector "!".


Module MCC := MiniCETCommon(TotalMap).
Import MCC.
Import FunctionalExtensionality.

Notation t_update_eq := TotalMap.t_update_eq.
Notation t_update_neq := TotalMap.t_update_neq.

Reserved Notation
  "p '|-' '<((' c '))>' '-->^' os '<((' ct '))>'"
  (at level 40, c constr, ct constr).

Inductive seq_eval_small_step_inst (p: prog) :
  @state cfg -> @state cfg -> obs -> Prop :=
  | SSMI_Skip : forall pc rs m,
      p[[pc]] = Some <{{ skip }}> ->
      p |- <(( S_Running (pc, rs, m) ))> -->^[] <(( S_Running (pc+1, rs, m) ))>
  | SSMI_Asgn : forall pc r m e x,
      p[[pc]] = Some <{{ x := e }}> ->
      p |- <(( S_Running (pc, r, m) ))> -->^[] <(( S_Running (pc+1, (x !-> (eval r e); r), m) ))>
  | SSMI_Div : forall pc r m e1 e2 x v1 v2,
      p[[pc]] = Some <{{ x <- div e1, e2 }}> ->
      to_nat (eval r e1) = Some v1 ->
      to_nat (eval r e2) = Some v2 ->
      let res := match v2 with
                | 0 => UV
                | _ => N (div v1 v2)
                end
      in
      p |- <(( S_Running (pc, r, m) ))> -->^[ODiv v1 v2] <(( S_Running (pc+1, (x !-> res; r), m) ))>
  | SSMI_Branch : forall pc pc' r m e n l,
      p[[pc]] = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      pc' = (if (not_zero n) then (l,0) else pc+1) ->
      p |- <(( S_Running (pc, r, m) ))> -->^[OBranch (not_zero n)] <(( S_Running (pc', r, m) ))>
  | SSMI_Jump : forall l pc r m,
      p[[pc]] = Some <{{ jump l }}> ->
      p |- <(( S_Running (pc, r, m) ))> -->^[] <(( S_Running ((l,0), r, m) ))>
  | SSMI_Load : forall pc r m x e n v',
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m.(memory) n = Some v' ->
      p |- <(( S_Running (pc, r, m) ))> -->^[OLoad n] <(( S_Running (pc+1, (x !-> v'; r), m) ))>
  | SSMI_Store : forall pc r m e e' n,
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( S_Running (pc, r, m) ))> -->^[OStore n] <(( S_Running (pc+1, r, upd_mem n m (eval r e')) ))>
  | SSMI_Call : forall pc r (m : mem) e sp_val l,
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      (* Call should lead to the procedure entry *)
      wf_label p true (fst l) ->
      snd l = 0 ->
      r ! sp = N sp_val ->
      S sp_val < stack_top m ->
      p |- <(( S_Running (pc, r, m) ))> -->^[OCall l sp_val] <(( S_Running (l, sp !-> N (S sp_val); r, upd_mem (S sp_val) m (FP (pc + 1)))))>
  (* How to handle arithmetic of sp_val here? And where to incorporate the wrapping around sp? *)
  | SSMI_Ret : forall pc r (m: mem) sp_val pc',
      p[[pc]] = Some <{{ ret }}> ->
      r ! sp = N sp_val ->
      sp_val < stack_top m ->
      nth_error m.(memory) sp_val = Some (FP pc') ->
      p |- <(( S_Running (pc, r, m) ))> -->^[ORet pc' sp_val] <(( S_Running (pc', sp !-> N (sp_val - 1) ; r, m) ))>
  | SSMI_Term : forall pc r m,
      p[[pc]] = Some <{{ exit }}> ->
      p |- <(( S_Running (pc, r, m) ))> -->^[] <(( S_Term ))>
  where "p '|-' '<((' c '))>' '-->^' os '<((' ct '))>'" :=
      (seq_eval_small_step_inst p c ct os).

Reserved Notation "p '|-' '<((' c '))>' '-->*^' os '<((' ct '))>'"
      (at level 40, c constr, ct constr).

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

Definition read_buffered (sbuffer : spec_mem) (m : mem) (index : nat) : val := match sbuffer ! index with
  | UV => get_mem index m
  | x => x
  end.

Inductive spec_eval_small_step (p:prog):
  @state spec_cfg -> @state spec_cfg -> dirs -> obs -> Prop :=
  | SpecSMI_Skip  :  forall pc r m ms sbuffer,
      p[[pc]] = Some <{{ skip }}> ->
      p |- <(( S_Running ((pc, r, m), sbuffer, false, ms) ))> -->_[]^^[] <(( S_Running ((pc+1, r, m), sbuffer, false, ms) ))>
  | SpecSMI_Asgn : forall pc r m ms e x sbuffer,
      p[[pc]] = Some <{{ x := e }}> ->
      p |- <(( S_Running ((pc, r, m), sbuffer, false, ms) ))> -->_[]^^[] <(( S_Running ((pc+1, (x !-> (eval r e); r), m), sbuffer, false, ms) ))>
  | SpecSMI_Div : forall pc r m ms e1 e2 x v1 v2 sbuffer,
      p[[pc]] = Some <{{ x <- div e1, e2 }}> ->
      to_nat (eval r e1) = Some v1 ->
      to_nat (eval r e2) = Some v2 ->
      let res := match v2 with
                | 0 => UV
                | _ => N (div v1 v2)
                end
      in
      p |- <(( S_Running (pc, r, m, sbuffer, false, ms) ))> -->_[]^^[ODiv v1 v2] <(( S_Running (pc+1, (x !-> res; r), m, sbuffer, false, ms) ))>
  | SpecSMI_Branch : forall pc pc' r m ms ms' b (b': bool) e n l sbuffer,
      p[[pc]] = Some <{{ branch e to l }}> ->
      to_nat (eval r e) = Some n ->
      b = (not_zero n) ->
      pc' = (if b' then (l, 0) else (pc+1)) ->
      ms' = ms || negb (Bool.eqb b b') ->
      p |- <(( S_Running ((pc, r, m), sbuffer, false, ms) ))> -->_[DBranch b']^^[OBranch b] <(( S_Running ((pc', r, m), sbuffer, false, ms') ))>
  | SpecSMI_Jump : forall l pc r m ms sbuffer,
      p[[pc]] = Some <{{ jump l }}> ->
      p |- <(( S_Running ((pc, r, m), sbuffer, false, ms) ))> -->_[]^^[] <(( S_Running (((l,0), r, m), sbuffer, false, ms) ))>
  | SpecSMI_Load : forall pc r m x e n v' sbuffer,
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m.(memory) n = Some v' ->
      p |- <(( S_Running ((pc, r, m), sbuffer, false, false) ))> -->_[]^^[OLoad n] <(( S_Running ((pc+1, (x !-> v'; r), m), sbuffer, false, false) ))>
  | SpecSMI_Load_Misspec : forall pc r m x e n v' sbuffer,
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      (* If we are misspeculating, we can use speculative buffer *)
      v' = sbuffer ! n ->
      (* nth_error m.(memory) n = None -> *)
      p |- <(( S_Running ((pc, r, m), sbuffer, false, true) ))> -->_[]^^[OLoad n] <(( S_Running ((pc+1, (x !-> v'; r), m), sbuffer, false, true) ))>
  | SpecSMI_Store : forall pc r m e e' n sbuffer,
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( S_Running ((pc, r, m), sbuffer, false, false) ))> -->_[]^^[OStore n] <(( S_Running ((pc+1, r, upd_mem n m (eval r e')), n !-> eval r e' ; sbuffer, false, false) ))>
  | SpecSMI_Store_Misspec : forall pc r m e e' n sbuffer,
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( S_Running ((pc, r, m), sbuffer, false, true) ))> -->_[]^^[OStore n] <(( S_Running ((pc+1, r, m), n !-> (eval r e') ; sbuffer, false, true) ))>
  | SpecSMI_Call : forall pc pc' r m e l ms' sp_val sbuffer,
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      r ! sp = N sp_val ->
      S sp_val < stack_top m ->
      ms' = negb ((fst pc' =? fst l)%nat && (snd pc' =? snd l)%nat) ->
      p |- <(( S_Running ((pc, r, m), sbuffer, false, false) ))> -->_[DCall pc']^^[OCall l sp_val] <(( S_Running ((pc', sp !-> N (S sp_val) ; r, upd_mem (S sp_val) m (FP (pc + 1))), S sp_val !-> FP (pc + 1); sbuffer, true, ms') ))>
  | SpecSMI_Call_Misspec : forall pc pc' r m e l sp_val sbuffer,
      p[[pc]] = Some <{{ call e }}> ->
      to_fp (eval r e) = Some l ->
      r ! sp = N sp_val ->
      (* S sp_val >= stack_top m -> *)
      (* YF: test if we can require this step only under known speculation *)
      (* ms' = ms || negb ((fst pc' =? fst l)%nat && (snd pc' =? snd l)%nat) -> *)
      p |- <(( S_Running ((pc, r, m), sbuffer, false, true) ))> -->_[DCall pc']^^[OCall l sp_val] <(( S_Running ((pc', sp !-> N (S sp_val) ; r, m), S sp_val !-> FP (pc + 1) ; sbuffer, true, true) ))>
  | SpecSMI_Ret_Dir : forall pc r m pc' pc'' ms' sp_val sbuffer,
      p[[pc]] = Some <{{ ret }}> ->
      wf_ret p pc'' ->
      r ! sp = N sp_val ->
      sp_val < stack_top m ->
      ms' = negb ((fst pc' =? fst pc'')%nat && (snd pc' =? snd pc'')%nat)->
      nth_error m.(memory) sp_val = Some (FP pc') ->
      p |- <(( S_Running ((pc, r, m), sbuffer, false, false) ))> -->_[DRet (Some pc'')]^^[ORet pc' sp_val] <(( S_Running ((pc'', sp !-> N (sp_val - 1) ; r, m), sbuffer, false, ms') ))>
  (* "DRet None" means "follow sequential ret" *)
  | SpecSMI_Ret_Step : forall pc r m pc' sp_val sbuffer,
      p[[pc]] = Some <{{ ret }}> ->
      r ! sp = N sp_val ->
      sp_val < stack_top m ->
      (* ms' = negb ((fst pc' =? fst pc'')%nat && (snd pc' =? snd pc'')%nat)-> *)
      (*** ***)
      (* wf_ret p pc' -> *) (* YF: do we need this? *)
      nth_error m.(memory) sp_val = Some (FP pc') ->
      p |- <(( S_Running ((pc, r, m), sbuffer, false, false) ))> -->_[DRet None]^^[ORet pc' sp_val] <(( S_Running ((pc', sp !-> N (sp_val - 1) ; r, m), sbuffer, false, false) ))>
  (* "DRet None" means "follow sequential ret" *)
  | SpecSMI_Ret_Misspec_Dir : forall pc r m pc' pc'' sp_val sbuffer,
      p[[pc]] = Some <{{ ret }}> ->
      wf_ret p pc'' ->
      r ! sp = N sp_val ->
      sbuffer ! sp_val = FP pc' ->
      (* sp_val >= stack_top m -> *)
      (* ms' = ms || negb ((fst pc' =? fst pc'')%nat && (snd pc' =? snd pc'')%nat) -> *)
      p |- <(( S_Running ((pc, r, m), sbuffer, false, true) ))> -->_[DRet (Some pc'')]^^[ORet pc' sp_val] <(( S_Running ((pc'', sp !-> N (sp_val - 1) ; r, m), sbuffer, false, true) ))>
  (* "DRet None" means "follow sequential ret" *)
  | SpecSMI_Ret_Misspec_Step : forall pc r m pc' sp_val sbuffer,
      p[[pc]] = Some <{{ ret }}> ->
      r ! sp = N sp_val ->
      sbuffer ! sp_val = FP pc' ->
      (* sp_val >= stack_top m -> *)
      (* ms' = ms || negb ((fst pc' =? fst pc'')%nat && (snd pc' =? snd pc'')%nat) -> *)
      p |- <(( S_Running ((pc, r, m), sbuffer, false, true) ))> -->_[DRet None]^^[ORet pc' sp_val] <(( S_Running ((pc', sp !-> N (sp_val - 1) ; r, m), sbuffer, false, true) ))>
  | SpecSMI_Term : forall pc r m ms sbuffer,
      p[[pc]] = Some <{{ exit }}> ->
      p |- <(( S_Running ((pc, r, m), sbuffer, false, ms) ))> -->_[]^^[] <(( S_Term ))>
  | SpecSMI_CTarget : forall pc r m ct ms sbuffer,
    p[[pc]] = Some <{{ ctarget }}> ->
    p |- <(( S_Running ((pc, r, m), sbuffer, ct, ms) ))> -->_[]^^[] <(( S_Running ((pc+1, r, m), sbuffer, false, ms) ))>
  | SpecSMI_Fault : forall pc r m ms sbuffer,
      p[[pc]] <> Some <{{ ctarget }}> ->
      p |- <(( S_Running ((pc, r, m), sbuffer, true, ms) ))> -->_[]^^[] <(( S_Fault ))>

  where "p |- <(( sc ))> -->_ ds ^^ os  <(( sct ))>" :=
    (spec_eval_small_step p sc sct ds os).

Reserved Notation
  "p '|-' '<((' sc '))>' '-->*_' ds '^^' os '<((' sct '))>'"
  (at level 40, sc constr, sct constr).

Definition mirrors (m : mem) (sb : spec_mem) : Prop :=
  forall n v, nth_error m.(memory) n = Some v -> sb ! n = v.

Theorem mem_is_subset_of_sbuffer_while_no_misspec : forall p m m' (sb sb' : spec_mem) pc pc' r r' os ds ct ct' ms',
  mirrors m sb ->
  p |- <(( (S_Running ((pc, r, m), sb, ct, false))))> -->_ ds ^^ os <(( S_Running ((pc', r', m'), sb', ct', ms') ))> ->
  mirrors m' sb'.
Proof.
  intros p m m' sb sb' pc pc' r r' os ds ct ct' ms' Hsubset Htrace n v.
  inv Htrace; intros Hmem; eauto; unfold upd_mem in *; cbn [memory] in *.
  (* store seq *)
  - destruct (Nat.eq_dec n0 n) as [<-|Hneq].
    + rewrite t_update_eq.
      assert (Hlt : n0 < Datatypes.length (upd n0 (memory m) (eval r' e'))).
      { apply nth_error_Some. congruence. }
      rewrite upd_length in Hlt.
      rewrite upd_eq in Hmem by assumption. congruence.
    + rewrite t_update_neq by assumption.
      apply Hsubset. rewrite upd_neq in Hmem by assumption. assumption.
  (* call seq *)
  - destruct (Nat.eq_dec (S sp_val) n) as [<-|Hneq].
    + rewrite t_update_eq.
      assert (Hlt : S sp_val < Datatypes.length (upd (S sp_val) (memory m) (FP (pc + 1)))).
      { apply nth_error_Some. congruence. }
      rewrite upd_length in Hlt.
      rewrite upd_eq in Hmem by assumption. congruence.
    + rewrite t_update_neq by assumption.
      apply Hsubset. rewrite upd_neq in Hmem by assumption. assumption.
Qed.

Reserved Notation
  "p '|-' '<((' ic '))>' '-->i_' ds '^^' os '<((' ict '))>'"
  (at level 40, ic constr, ict constr).

Inductive ideal_eval_small_step_inst (p:prog) :
  @state ideal_cfg -> @state ideal_cfg -> dirs -> obs -> Prop :=
  | ISMI_Skip  :  forall pc r m ms sbuffer,
      p[[pc]] = Some <{{ skip }}> ->
      p |- <(( S_Running ((pc, r, m), sbuffer, ms) ))> -->i_[]^^[] <(( S_Running ((pc+1, r, m), sbuffer, ms) ))>
  | ISMI_Asgn : forall pc r m ms e x sbuffer,
      p[[pc]] = Some <{{ x := e }}> ->
      p |- <(( S_Running ((pc, r, m), sbuffer, ms) ))> -->i_[]^^[] <(( S_Running ((pc+1, (x !-> (eval r e); r), m), sbuffer, ms) ))>
  | ISMI_Div : forall pc r m (ms: bool) e1 e2 x v1 v2 sbuffer,
      p[[pc]] = Some <{{ x <- div e1, e2 }}> ->
      (if ms then Some 0 else to_nat (eval r e1)) = Some v1 ->
      (if ms then Some 0 else to_nat (eval r e2)) = Some v2 ->
      let res := match v2 with
                | 0 => UV
                | _ => N (div v1 v2)
                end
      in
      p |- <(( S_Running ((pc, r, m), sbuffer, ms) ))> -->i_[]^^[ODiv v1 v2] <(( S_Running ((pc+1, (x !-> res; r), m), sbuffer, ms) ))>
  | ISMI_Branch : forall pc pc' r m (ms ms' b b' : bool) e n' l sbuffer,
      p[[pc]] = Some <{{ branch e to l }}> ->
      (if ms then Some 0 else to_nat (eval r e)) = Some n' ->
      b = (not_zero n') ->
      pc' = (if b' then (l,0) else pc+1) ->
      ms' = (ms || (negb (Bool.eqb b b'))) ->
      p |- <(( S_Running ((pc, r, m), sbuffer, ms) ))> -->i_[DBranch b']^^[OBranch b] <(( S_Running ((pc', r, m), sbuffer, ms') ))>
  | ISMI_Jump : forall l pc r m ms sbuffer,
      p[[pc]] = Some <{{ jump l }}> ->
      p |- <(( S_Running ((pc, r, m), sbuffer, ms) ))> -->i_[]^^[] <(( S_Running (((l,0), r, m), sbuffer, ms) ))>
  | ISMI_Load : forall pc r m x e n v' sbuffer,
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      to_nat (eval r e) = Some n ->
      nth_error m.(memory) n = Some v' ->
      p |- <(( S_Running ((pc, r, m), sbuffer, false) ))> -->i_[]^^[OLoad n] <(( S_Running ((pc+1, (x !-> v'; r), m), sbuffer, false) ))>
  | ISMI_Load_Misspec : forall pc r m x e v' (sbuffer : spec_mem),
      p[[pc]] = Some <{{ x <- load[e] }}> ->
      sbuffer ! 0 = v' ->
      p |- <(( S_Running ((pc, r, m), sbuffer, true) ))> -->i_[]^^[OLoad 0] <(( S_Running ((pc+1, (x !-> v'; r), m), sbuffer, true) ))>
  | ISMI_Store : forall pc r m e e' n sbuffer,
      p[[pc]] = Some <{{ store[e] <- e' }}> ->
      to_nat (eval r e) = Some n ->
      p |- <(( S_Running ((pc, r, m), sbuffer, false) ))> -->i_[]^^[OStore n] <(( S_Running ((pc+1, r, upd_mem n m (eval r e')), n !-> eval r e' ; sbuffer, false) ))>
  | ISMI_Store_Misspec : forall pc r m e e' sbuffer,
    p[[pc]] = Some <{{ store[e] <- e' }}> ->
    p |- <(( S_Running ((pc, r, m), sbuffer, true) ))> -->i_[]^^[OStore 0] <(( S_Running ((pc+1, r, m), 0 !-> eval r e' ; sbuffer, true) ))>
  | ISMI_Call : forall pc pc' r m e l (ms' : bool) blk sp_val sbuffer,
      p[[pc]] = Some <{{ call e }}> ->
      r ! sp = N sp_val ->
      S sp_val < stack_top m ->
      to_fp (eval r e) = Some l ->
      ms' = negb ((fst pc' =? fst l)%nat && (snd pc' =? snd l)%nat) ->
      nth_error p (fst pc') = Some blk ->
      snd blk = true ->
      snd pc' = 0 ->
      p |- <(( S_Running ((pc, r, m), sbuffer, false) ))> -->i_[DCall pc']^^[OCall l sp_val] <(( S_Running ((pc', sp !-> N (S sp_val) ; r, upd_mem (S sp_val) m (FP (pc + 1))), S sp_val !-> FP (pc + 1) ; sbuffer, ms') ))>
  | ISMI_Call_Misspec : forall pc pc' r m e blk sp_val sbuffer,
      p[[pc]] = Some <{{ call e }}> ->
      r ! sp = N sp_val ->
      (* ms' = negb ((fst pc' =? 0)%nat && (snd pc' =? 0)%nat) -> *)
      nth_error p (fst pc') = Some blk ->
      snd blk = true ->
      snd pc' = 0 ->
      p |- <(( S_Running ((pc, r, m), sbuffer, true) ))> -->i_[DCall pc']^^[OCall (0, 0) sp_val] <(( S_Running ((pc', sp !-> N (S sp_val) ; r, m), S sp_val !-> FP (pc + 1) ; sbuffer, true) ))>
  | ISMI_Call_F : forall pc pc' r m e l (ms : bool) sp_val sbuffer,
      p[[pc]] = Some <{{ call e }}> ->
      (if ms then Some (0,0) else to_fp (eval r e)) = Some l ->
      r ! sp = N sp_val ->
      (forall blk, nth_error p (fst pc') = Some blk -> snd blk = false \/ snd pc' <> 0) ->
      p |- <(( S_Running ((pc, r, m), sbuffer, ms) ))> -->i_[DCall pc']^^[OCall l sp_val] <(( S_Fault ))>
  | ISMI_Ret_Dir : forall pc r m pc' pc'' ms' sp_val sbuffer,
      p[[pc]] = Some <{{ ret }}> ->
      wf_ret p pc'' ->
      r ! sp = N sp_val ->
      sp_val < stack_top m ->
      nth_error m.(memory) sp_val = Some (FP pc') ->
      ms' = negb ((fst pc' =? fst pc'')%nat && (snd pc' =? snd pc'')%nat) ->
      p |- <(( S_Running ((pc, r, m), sbuffer, false) ))> -->i_[DRet (Some pc'')]^^[ORet pc' sp_val] <(( S_Running ((pc'', sp !-> N (sp_val - 1) ; r, m), sbuffer, ms') ))>
  (* "DRet None" means "follow sequential ret" *)
  | ISMI_Ret_Step : forall pc r m pc' sp_val sbuffer,
      p[[pc]] = Some <{{ ret }}> ->
      r ! sp = N sp_val ->
      sp_val < stack_top m ->
      nth_error m.(memory) sp_val = Some (FP pc') ->
      p |- <(( S_Running ((pc, r, m), sbuffer, false) ))> -->i_[DRet None]^^[ORet pc' sp_val] <(( S_Running ((pc', sp !-> N (sp_val - 1) ; r, m), sbuffer, false) ))>
  | ISMI_Ret_Misspec_Dir : forall pc r m (pc'' : cptr) sp_val sbuffer,
      p[[pc]] = Some <{{ ret }}> ->
      r ! sp = N sp_val ->
      (* sbuffer ! sp_val = FP (0, 0) -> *) (* YF: I think we cannot assume it here, since it happens only after masking *)
      wf_ret p pc'' ->
      (* ms' = ms || negb ((fst pc' =? fst pc'')%nat && (snd pc' =? snd pc'')%nat) -> *)
      p |- <(( S_Running ((pc, r, m), sbuffer, true) ))> -->i_[DRet (Some pc'')]^^[ORet (0, 0) sp_val] <(( S_Running ((pc'', sp !-> N (sp_val - 1) ; r, m), sp_val !-> FP (0, 0) ; sbuffer, true) ))>
  | ISMI_Ret_Misspec_Step : forall pc r m sp_val sbuffer,
      p[[pc]] = Some <{{ ret }}> ->
      r ! sp = N sp_val ->
      (* sbuffer ! sp_val = FP (0, 0) -> *) (* YF: I think we cannot assume it here, since it happens only after masking *)
      (* ms' = ms || negb ((fst pc' =? fst pc'')%nat && (snd pc' =? snd pc'')%nat) -> *)
      p |- <(( S_Running ((pc, r, m), sbuffer, true) ))> -->i_[DRet None]^^[ORet (0, 0) sp_val] <(( S_Running (((0, 0), sp !-> N (sp_val - 1) ; r, m), sp_val !-> FP (0, 0) ; sbuffer, true) ))>
  | ISMI_Term : forall pc r m ms sbuffer,
      p[[pc]] = Some <{{ exit }}> ->
      p |- <(( S_Running ((pc, r, m), sbuffer, ms) ))> -->i_[]^^[] <(( S_Term ))>

  where "p |- <(( ic ))> -->i_ ds ^^ os  <(( ict ))>" :=
    (ideal_eval_small_step_inst p ic ict ds os).


Theorem mem_is_subset_of_sbuffer_while_no_misspec_ideal : forall p m m' (sb sb' : spec_mem) pc pc' r r' os ds ms',
  mirrors m sb ->
  p |- <(( (S_Running ((pc, r, m), sb, false))))> -->i_ ds ^^ os <(( S_Running ((pc', r', m'), sb', ms') ))> ->
  mirrors m' sb'.
Proof.
  intros p m m' sb sb' pc pc' r r' os ds ms' Hsubset Htrace n v.
  inv Htrace; intros Hmem; eauto; unfold upd_mem in *; cbn [memory] in *.
  (* store seq *)
  - destruct (Nat.eq_dec n0 n) as [<-|Hneq].
    + rewrite t_update_eq.
      assert (Hlt : n0 < Datatypes.length (upd n0 (memory m) (eval r' e'))).
      { apply nth_error_Some. congruence. }
      rewrite upd_length in Hlt.
      rewrite upd_eq in Hmem by assumption. congruence.
    + rewrite t_update_neq by assumption.
      apply Hsubset. rewrite upd_neq in Hmem by assumption. assumption.
  (* call seq *)
  - destruct (Nat.eq_dec (S sp_val) n) as [<-|Hneq].
    + rewrite t_update_eq.
      assert (Hlt : S sp_val < Datatypes.length (upd (S sp_val) (memory m) (FP (pc + 1)))).
      { apply nth_error_Some. congruence. }
      rewrite upd_length in Hlt.
      rewrite upd_eq in Hmem by assumption. congruence.
    + rewrite t_update_neq by assumption.
      apply Hsubset. rewrite upd_neq in Hmem by assumption. assumption.
Qed.

Reserved Notation
  "p '|-' '<((' ic '))>' '-->i*_' ds '^^' os '<((' ict '))>'"
  (at level 40, ic constr, ict constr).

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

(* Definition is_br_or_call (i : inst) := *)
(*   match i with *)
(*   | <{{branch _ to _}}> | <{{call _}}> => true *)
(*   | _                                  => false *)
(*   end. *)

(* Definition pc_sync (p: prog) (pc: cptr) : option cptr := *)
(*   match nth_error p (fst pc) with *)
(*   | Some blk => match nth_error (fst blk) (snd pc) with *)
(*                | Some i => *)
(*                    let acc1 := if (Bool.eqb (snd blk) true) then 2 else 0 in *)
(*                    let insts_before_pc := (firstn (snd pc) (fst blk)) in *)
(*                    let acc2 := fold_left (fun acc (i: inst) => if (is_br_or_call i) *)
(*                                                             then (add acc 1) *)
(*                                                             else acc) *)
(*                                  insts_before_pc acc1 *)
(*                    in Some ((fst pc), add (snd pc) acc2) *)
(*                | _ => None *)
(*                end *)
(*   | _ => None *)
(*   end. *)

Definition offset_uslh (bl: list inst * bool) : list nat :=
  _offset_uslh (fst bl) (if snd bl then 2 else 0).

(* pc - the first element of uslh_inst result *)
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
   (forall x, x <> msf /\ x <> callee -> (ms = false \/ x = sp) -> val_match p (sr ! x) (tr ! x)) /\
   (tr ! msf = N (if ms then 1 else 0)).

Definition Rsync1 (p: prog) (sr tr: reg) (ms: bool) : Prop :=
  (forall x, x <> msf /\ x <> callee -> (ms = false \/ x = sp) -> val_match p (sr ! x) (tr ! x)).

Definition Msync (p: prog) (sm tm: mem) : Prop :=
  (forall i, match nth_error sm.(memory) i, nth_error tm.(memory) i with
       | Some sv, Some tv => val_match p sv tv
       | None, None => True
       | _, _ => False
       end)
  /\ stack_top sm = stack_top tm.

Definition ms_msf_match (tr: reg) (ms: bool) : Prop :=
  (tr ! msf = N (if ms then 1 else 0)).

Variant match_cfgs (p: prog) : ideal_cfg -> spec_cfg -> Prop :=
| match_cfgs_intro pc r m sb ms pc' r' m' sb'
  (PC: pc_sync p pc = Some pc')
  (REG: Rsync p r r' ms)
  (MSC: Msync p m m') :
  match_cfgs p ((pc, r, m), sb, ms) ((pc', r', m'), sb', false, ms)
.

(* Definition steps_to_sync_point' (p: prog) (ic: ideal_cfg) (ds: dirs) : option nat := *)
(*   let '(c, ms) := ic in *)
(*   let '(pc, r, m, sk) := c in *)
(*   match p[[pc]] with *)
(*   | Some i => match i with *)
(*              | IBranch e l => match ds with *)
(*                              | DBranch b :: ds' => Some (if b then 3 else 2) *)
(*                              | _ => None *)
(*                              end *)
(*              | ICall e => match ds with *)
(*                          | DCall pc' :: ds' => Some 4 *)
(*                          | _ => None *)
(*                          end *)
(*              | _ => Some 1 *)
(*              end *)
(*   | _ => None *)
(*   end. *)

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
  (* | DRet pc' => wf_ret p pc' *)
  | _ => True
  end.

Definition wf_ds' (p: prog) (ds: dirs) : Prop :=
  Forall (wf_dir' p) ds.

Definition match_ob (p: prog) (o1 o2: observation) : Prop :=
  match o1, o2 with
  | ODiv _ _, ODiv _ _ | OBranch _, OBranch _ | OLoad _, OLoad _ | OStore _, OStore _ => o1 = o2
  | OCall l1 n1, OCall l2 n2 | ORet l1 n1, ORet l2 n2 => n1 = n2 /\ val_match p (FP l1) (FP l2)
  | _, _ => False
  end.

Definition match_obs (p: prog) (os1 os2: obs) : Prop :=
  Forall2 (match_ob p) os1 os2.

Definition nonempty_block (blk : (list inst * bool)) : Prop :=
  0 < Datatypes.length (fst blk).

Definition is_terminator (i: inst) : Prop :=
  match i with
  | <{{ ret }}> | <{{ jump _}}> | <{{ exit }}> => True
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

(* JB: can we maybe deduplicate these w.r.t. MiniCET, where they are defined for bool? YH: Yes. We can. *)
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
  | <{{skip}}> | <{{ctarget}}> | <{{ret}}> | <{{exit}}> => True
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

(* -------------------------------------------------------------------------- *)
(* Immediate safety *)
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

(*--------- End Safety ----------- *)

Definition input : Type := reg * mem.

Definition mirror_mem (m : mem) : spec_mem :=
  fold_left (fun sb '(n, v) => (n !-> v; sb)) (add_index m.(memory)) spec_mem_init.

(* -------------------------------------------------------------------------- *)
(* Sequential semantics. *)

Definition seq_initial (p : prog) (inp : input) : state cfg :=
  let '(r, m) := inp in S_Running ((0, 0), r, m).

#[local]
Instance SeqLang : SimDiagrams.Language input :=
  {|
    SimDiagrams.prog := prog;
    SimDiagrams.directive := unit;
    SimDiagrams.observation := observation;
    SimDiagrams.machine := state cfg;
    SimDiagrams.initial_machine := seq_initial;
    SimDiagrams.step := fun p st _ os st' => seq_eval_small_step_inst p st st' os;
    SimDiagrams.sequential_safe1 := safe_imm_seq;
  |}.

Notation "p |- <(( c ))> -->*^ os <(( ct ))>" :=
  (sem (L := SeqLang) p c [] os ct).

Lemma multi_seq_cons p c1 c2 c3 os1 os2 :
  p |- <(( c1 ))> -->^ os1 <(( c2 ))> ->
  p |- <(( c2 ))> -->*^ os2 <(( c3 ))> ->
  p |- <(( c1 ))> -->*^ os1 ++ os2 <(( c3 ))>.
Proof. intros H1 H2. exact (sem_step (L := SeqLang) (ds1 := []) (ds2 := []) H1 H2). Qed.

Lemma multi_seq_ind p (P : state cfg -> obs -> state cfg -> Prop)
  (REFL: forall c, P c [] c)
  (STEP: forall c1 c2 c3 os1 os2,
      p |- <(( c1 ))> -->^ os1 <(( c2 ))> ->
      p |- <(( c2 ))> -->*^ os2 <(( c3 ))> ->
      P c2 os2 c3 ->
      P c1 (os1 ++ os2) c3) :
  forall c os c', p |- <(( c ))> -->*^ os <(( c' ))> -> P c os c'.
Proof.
  intros c os c' H.
  remember (@nil (SimDiagrams.directive (L := SeqLang))) as ds eqn:Hds.
  induction H as [c | c1 c2 c3 ds1 os1 ds2 os2 Hs Hr IH]; [apply REFL|].
  destruct ds1; [|discriminate]. simpl in Hds. subst ds2.
  eapply STEP; [exact Hs | exact Hr | auto].
Qed.

(* -------------------------------------------------------------------------- *)
(* Ideal semantics. *)

Definition ideal_initial (p : prog) (inp : input) : state ideal_cfg :=
  let '(r, m) := inp in S_Running ((0, 0), r, m, mirror_mem m, false).

#[local]
Instance IdealLang : SimDiagrams.Language input :=
  {|
    SimDiagrams.prog := prog;
    SimDiagrams.directive := direction;
    SimDiagrams.observation := observation;
    SimDiagrams.machine := state ideal_cfg;
    SimDiagrams.initial_machine := ideal_initial;
    SimDiagrams.step := fun p st ds os st' => ideal_eval_small_step_inst p st st' ds os;
    SimDiagrams.sequential_safe1 := safe_imm_ideal;
  |}.

Notation "p |- <(( ic ))> -->i*_ ds ^^ os <(( ict ))>" :=
  (sem (L := IdealLang) p ic ds os ict).

(* -------------------------------------------------------------------------- *)
(* Speculative semantics. *)

Definition spec_initial (p : prog) (inp : input) : state spec_cfg :=
  let '(r, m) := inp in
  S_Running ((0, 0), (callee !-> FP (0, 0); msf !-> N 0; r), m, mirror_mem m, true, false).

#[local]
Instance SpecLang : SimDiagrams.Language input :=
  {|
    SimDiagrams.prog := prog;
    SimDiagrams.directive := direction;
    SimDiagrams.observation := observation;
    SimDiagrams.machine := state spec_cfg;
    SimDiagrams.initial_machine := spec_initial;
    SimDiagrams.step := fun p st ds os st' => spec_eval_small_step p st st' ds os;
    SimDiagrams.sequential_safe1 := safe_imm_spec;
  |}.


Notation "p |- <(( sc ))> -->*_ ds ^^ os <(( sct ))>" :=
  (sem (L := SpecLang) p sc ds os sct).

(* -------------------------------------------------------------------------- *)
(* USLH as a compiler from the ideal to the speculative semantics. *)

Definition first_blk_call (p: prog) : Prop :=
  match nth_error p 0 with
  | None => False
  | Some (blk, b) => if b then True else False
  end.

Definition uslh_compiler : SimDiagrams.compiler (Ls := IdealLang) (Lt := SpecLang) :=
  fun p_s p_t =>
    p_t = uslh_prog p_s
    /\ wf_prog p_s
    /\ no_ct_prog p_s
    /\ unused_prog msf p_s
    /\ unused_prog callee p_s
    /\ unused_prog sp p_s
    /\ first_blk_call p_s.

Definition ideal_compiler : compiler (Ls := SeqLang) (Lt := IdealLang) := fun p_s p_t =>
  p_s = p_t.

Definition uslh_full_compiler := compose uslh_compiler ideal_compiler.

Definition ideal_safe_inv (p: prog) (st: state ideal_cfg) : Prop :=
  match st with
  | S_Running ((pc, r, m), _, ms) =>
      (exists n, r ! sp = N n)
      /\ (if ms then exists i, p[[pc]] = Some i
          else sequential_safe (L := SeqLang) p (S_Running (pc, r, m)))
  | S_Undef => False
  | _ => True
  end.

(* -------------------------------------------------------------------------- *)
(* Transformers *)

(* State of the USLH leakage transformer *)
Record uslh_hstate := {
  hs_src : prog; (* source program *)
  hs_tgt : prog; (* target program *)
  hs_tpc : cptr; (* target pc *)
  hs_ct : bool; (* target ct *)
  hs_sp : val (* target sp *)
}.

Definition hs_set (h: uslh_hstate) (tpc: cptr) (ct: bool) (v: val) : uslh_hstate :=
  {| hs_src := hs_src h; hs_tgt := hs_tgt h; hs_tpc := tpc; hs_ct := ct; hs_sp := v |}.

Definition tctrl (p_s p_t: prog) (st: state spec_cfg) : option uslh_hstate :=
  match st with
  | S_Running ((pc, r, _), _, ct, _) =>
      Some {| hs_src := p_s; hs_tgt := p_t; hs_tpc := pc; hs_ct := ct; hs_sp := r ! sp |}
  | _ => None
  end.

(* Implementation of This -- update of the history after one step, given target dir and target obs *)
(* We use target observations to retrieve current sp *)
Definition tctrl_step (h: option uslh_hstate) (ds: dirs) (os: obs) : option uslh_hstate :=
  match h with
  | None => None
  | Some h =>
      if hs_ct h then
        match (hs_tgt h)[[hs_tpc h]] with
        | Some ICTarget => Some (hs_set h (hs_tpc h + 1) false (hs_sp h))
        | _ => None
        end
      else
        match (hs_tgt h)[[hs_tpc h]], ds, os with
        | Some (IBranch _ l), [DBranch b], _ =>
            Some (hs_set h (if b then (l, 0) else hs_tpc h + 1) false (hs_sp h))
        | Some (IJump l), _, _ => Some (hs_set h (l, 0) false (hs_sp h))
        | Some (ICall _), [DCall pc'], [OCall _ n] => Some (hs_set h pc' true (N (S n)))
        | Some IRet, [DRet (Some pc'')], [ORet _ n] => Some (hs_set h pc'' false (N (n - 1)))
        | Some IRet, [DRet None], [ORet pc' n] => Some (hs_set h pc' false (N (n - 1)))
        | Some IExit, _, _ => None
        | Some _, _, _ => Some (hs_set h (hs_tpc h + 1) false (hs_sp h))
        | None, _, _ => None
        end
  end.

Definition ret_unsync (p: prog) (tpc: cptr) : cptr :=
  let '(l, o') := tpc in
  match nth_error p l with
  | Some blk => match index_of (o' - 2) (offset_uslh blk) with
               | Some o => (l, S o)
               | None => tpc
               end
  | None => tpc
  end.

Definition sync_fp (p: prog) (pc: cptr) : cptr :=
  match pc with
  | (l, 0) => (l, 0)
  | _ => match ret_sync p pc with
        | Some tpc => tpc
        | None => pc
        end
  end.

Definition sync_ob (p: prog) (o: observation) : observation :=
  match o with
  | OCall l n => OCall (sync_fp p l) n
  | ORet l n => ORet (sync_fp p l) n
  | _ => o
  end.

(* Kinds of instructions in the target: *)
(* - TSrc - the instruction from the source *)
(* - TSilent - the instruction inserted by USLH which doesn't produce observation. *)
(* - TMask - the instruction inserted by USLH which produces observation. *)
Variant tkind := TSrc | TSilent | TMask.

Definition uslh_kind (p: prog) (tpc: cptr) (i: inst) : tkind :=
  match i with
  | IAsgn x _ => if (String.eqb x msf || String.eqb x callee)%bool then TSilent else TSrc
  | ILoad x _ => if String.eqb x callee then TMask else TSrc
  | IStore (AId x) _ => if String.eqb x sp then TMask else TSrc
  | IJump _ => if (fst tpc <? Datatypes.length p)%nat then TSrc else TSilent
  | ICTarget => TSilent
  | _ => TSrc
  end.

Definition unsync_dirs (p: prog) (ds: dirs) : dirs :=
  match ds with
  | [DRet (Some x)] => [DRet (Some (ret_unsync p x))]
  | _ => ds
  end.

Definition uslh_Tdir (h: option uslh_hstate) (ds: dirs) : dirs :=
  match h with
  | Some h =>
      if hs_ct h then []
      else match (hs_tgt h)[[hs_tpc h]] with
           | Some i => match uslh_kind (hs_src h) (hs_tpc h) i with
                      | TSrc => unsync_dirs (hs_src h) ds
                      | _ => []
                      end
           | None => []
           end
  | None => []
  end.

Definition uslh_mask (h: uslh_hstate) : obs :=
  if hs_ct h then []
  else match (hs_tgt h)[[hs_tpc h]] with
       | Some i =>
           match uslh_kind (hs_src h) (hs_tpc h) i with
           | TMask =>
               match hs_sp h, i with
               | N n, ILoad _ _ => [OLoad n]
               | N n, IStore _ _ => [OStore n]
               | _, _ => []
               end
           | _ => []
           end
       | None => []
       end.

Definition uslh_Tobs (h: option uslh_hstate) (ds: dirs) (os: obs) : obs :=
  match h with
  | Some h => uslh_mask h ++ map (sync_ob (hs_src h)) os
  | None => os
  end.

Definition uslh_hist (p_s p_t: prog) (isp: nat) : History (Lt := SpecLang) :=
  {| SimDiagrams.history := option uslh_hstate;
     SimDiagrams.init_hist :=
       Some {| hs_src := p_s; hs_tgt := p_t; hs_tpc := (0, 0); hs_ct := true; hs_sp := N isp |};
     SimDiagrams.This := tctrl_step |}.

Definition uslh_sync (isp: nat) : SimDiagrams.input_sync (input := input) :=
  fun p inp inp' =>
    let r := fst inp in
    let r' := fst inp' in
    Rsync1 p (fst inp) (fst inp') false
    /\ Msync p (snd inp) (snd inp')
    /\ r ! sp = N isp
    /\ r' ! callee = FP (0, 0).
(* -------------------------------------------------------------------------- *)

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
  | ISkip | IJump _ | ILoad _ _ | IStore _ _ | IAsgn _ _ | IDiv _ _ _ | IExit => True
  | _ => False
  end.

(* lock-step instructions *)
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
| uslh_exit :
  match_simple_inst_uslh IExit IExit
(*| uslh_peek x:*)
  (*match_simple_inst_uslh (IPeek x) (IPeek x)*)
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
  (NXT1: (uslh_prog p)[[tpc + 1]] = Some <{{ store[sp] <- (msf=1) ? &(0,0) : callee }}>)
  (NXT2: (uslh_prog p)[[(tpc + 1) + 1]] = Some <{{ callee <- load[sp] }}>)
  (NXT3: (uslh_prog p)[[((tpc + 1) + 1) + 1]] = Some IRet) :
  match_inst_uslh p pc IRet (<{{ callee <- load[sp] }}>)
.

Lemma uslh_inst_simple i l o c iss np
  (SIMP: simple_inst i)
  (UNUSED: i_unused sp i)
  (USLH: uslh_inst i l o c = (iss, np)) :
  exists i', iss = [i'] /\ match_simple_inst_uslh i i' /\ np = [].
Proof.
  ii. destruct i; ss; des;
  unfold MiniCET.uslh_ret in *; clarify; esplits; econs; eauto.
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

(* Definition blk_offset (blk: list inst * bool) (o: nat) := *)
(*   fold_left (fun (acc : nat) (i0 : inst) => if is_br_or_call i0 then add acc 1 else acc) (firstn o (fst blk)) *)
(*     (if Bool.eqb (snd blk) true then 2 else 0). *)

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

(* Lemma offset_eq_aux blk c' l0 p1 n o *)
(*     (BLK: mapM uslh_inst blk c' = (l0, p1)) *)
(*     (BDD: o <= Datatypes.length blk) : *)
(*   prefix_offset l0 o n = *)
(*   o + fold_left (fun (acc : nat) (i0 : inst) => if is_br_or_call i0 then add acc 1 else acc) (firstn o blk) n. *)
(* Proof. *)
(*   ginduction o; ii. *)
(*   { ss. } *)
(*   unfold prefix_offset. *)

(*   exploit mapM_perserve_len; eauto. intros LEN. *)
(*   destruct blk. *)
(*   { ss. des_ifs. lia. } *)
(*   destruct l0. *)
(*   { ss. } *)
(*   do 2 rewrite firstn_cons. *)
(*   rewrite unfold_mapM in BLK. *)
(*   exploit bind_inv; eauto. i. des. subst. ss. *)
(*   unfold uslh_bind in x1. *)
(*   destruct (mapM uslh_inst blk (c' + Datatypes.length pm)) eqn:X. ss. clarify. *)
(*   exploit IHo. *)
(*   { eauto. } *)
(*   { lia. } *)
(*   i. rewrite <- x1. *)

(*   unfold prefix_offset. *)
(*   replace (n + Datatypes.length l) with *)
(*     (add (if is_br_or_call i then add n 1 else n) 1); auto. *)
(*   2:{ destruct i; ss; unfold MiniCET.uslh_ret in *; ss; clarify; ss. *)
(*       - unfold uslh_bind in x0. ss. clarify. ss. lia. *)
(*       - lia. } *)
(*   rewrite fold_left_add_init. lia. *)
(* Qed. *)

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

(* Lemma add_index_uslh_offset_uslh_aux bl s l1 l2 *)
(*   (IDX: split (_add_index_uslh bl s) = (l1, l2)) : *)
(*   l1 = _offset_uslh bl s /\ l2 = bl. *)
(* Proof. *)
(*   unfold add_index_uslh, offset_uslh in *. *)
(*   ginduction bl; ii. *)
(*   { ss. clarify. } *)
(*   unfold _offset_uslh. ss. des_ifs_safe. *)
(*   exploit IHbl; eauto. i. des. subst. auto. *)
(* Qed. *)

(* Lemma uslh_offset_uslh_add_index_aux bl s l1 l2 *)
(*   (L1: l1 = _offset_uslh bl s) *)
(*   (L2: l2 = bl) : *)
(*   split (_add_index_uslh bl s) = (l1, l2). *)
(* Proof. *)
(*   ginduction bl; ii; try (sfby ss; clarify). *)
(*   subst. ss. des_ifs_safe. *)
(*   erewrite IHbl in Heq; eauto. clarify. *)
(* Qed. *)

(* Lemma add_index_uslh_offset_uslh bl is_proc l1 l2 *)
(*   (IDX: split (add_index_uslh bl is_proc) = (l1, l2)) : *)
(*   l1 = offset_uslh (bl, is_proc) /\ l2 = bl. *)
(* Proof. *)
(*   unfold add_index_uslh, offset_uslh in *. *)
(*   eapply split_combine in IDX.  *)
(*   eapply add_index_uslh_offset_uslh_aux; eauto. *)
(* Qed. *)

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

(* Lemma offset_uslh *)
(* : nth_error (map offset_uslh p) l = Some oblk *)
(*   Heq1 : nth_error oblk o = Some o' *)
(*   Heq : nth_error p l = Some (blk, is_proc) : *)
(*   nth_error (offset_uslh (blk, is_proc)) o = Some o' *)
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
  (* destruct (concatM (mapM uslh_inst blk) c') eqn:X. *)
  unfold pc_sync in *. ss. des_ifs_safe.
  (* replace (fold_left (fun (acc : nat) (i0 : inst) => if is_br_or_call i0 then add acc 1 else acc) (firstn o blk) *)
  (*            (if Bool.eqb is_proc true then 2 else 0)) with (blk_offset (blk, is_proc) o) by ss. *)
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

Lemma src_simple_inv p tp pc tpc i
  (UNUSED: unused_prog sp p)
  (SIMP: simple_inst i)
  (TRP: uslh_prog p = tp)
  (PS: pc_sync p pc = Some tpc)
  (INST: p[[pc]] = Some <{{ i }}>) :
  exists i', tp[[tpc]] = Some <{{ i' }}> /\ match_simple_inst_uslh i i'.
Proof.
  exploit unused_prog_lookup; eauto. intros UNUSEDI.
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
    destruct i; ss; des;
    unfold MiniCET.uslh_ret in *; clarify.
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
    (*+ esplits; [|econs]; eauto. rewrite plus_n_O at 1.*)
      (*exploit concat_nth_error; ss; eauto. ss.*)
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
    (*+ esplits; [|econs]; eauto. rewrite plus_n_O at 1.*)
      (*exploit concat_nth_error; ss; eauto. ss.*)
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
  (UNUSED: unused_prog sp p)
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

  (* branch *)
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
        erewrite <- uslh_inst_np_length_same with (opc := 0). (* opc does not matter, so it would not be resolved by anything *)
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
  (* call *)
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
  (* ret *)
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
        all: simpl; rewrite H; simpl; des_ifs; [replace (prefix_offset a0 o 2) with (S (S (prefix_offset a0 o 0)));
               [|unfold prefix_offset at 2; rewrite fold_left_init_0 at 1; unfold prefix_offset; lia]|];
          simpl; rewrite <- ?add_assoc; simpl; eapply concat_nth_error; eauto.
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

Lemma val_match_fp_inj p l1 l2 l':
    val_match p (FP l1) (FP l') ->
    val_match p (FP l2) (FP l') ->
    l1 = l2.
Proof.
    destruct l1 as [a1 b1], l2 as [a2 b2], l' as [c d]. unfold val_match.
    destruct b1, b2; cbn [Nat.eqb]; i; des; subst; auto.
    - eapply ret_sync_nonzero in H0. clarify.
    - eapply ret_sync_nonzero in H. clarify.
    - exploit ret_sync_inj; [exact H | exact H0 |]. i. des. subst. auto.
Qed.

Lemma val_match_fp_functional p l l1' l2':
    val_match p (FP l) (FP l1') ->
    val_match p (FP l) (FP l2') ->
    l1' = l2'.
Proof.
    destruct l as [a b], l1' as [c1 d1], l2' as [c2 d2]. unfold val_match.
    destruct b; cbn [Nat.eqb]; i; des; subst; congruence.
Qed.

Lemma eval_regs_eq : forall p (r r': reg) (e: exp),
   e_unused msf e ->
   e_unused callee e ->
   wf_exp p e = true ->
   Rsync1 p r r' false ->
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
   Rsync1 p r r' false ->
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
(* Target matches source *)
| match_cfgs_ext_intro ic sc
  (MATCH: match_cfgs p ic sc) :
  match_cfgs_ext p (S_Running ic) (S_Running sc)
(* Match source beginning of procedure to target <{{ ctarget }}> beggining of procedure. *)
(* Matches on both ct, as we now may enter procedures without calling (on masked return) *)
| match_cfgs_ext_ct1
  l blk r m sb (ms:bool) r' m' sb' (ct:bool)
  (CT: nth_error p l = Some (blk, true))
  (CT1: (uslh_prog p)[[(l, 0)]] = Some <{{ ctarget }}>)
  (REG: Rsync1 p r r' ms)
  (MSC: Msync p m m')
  (MS: eval r' <{{ (callee = (&(l, 0))) ? msf : 1 }}> = N (if ms then 1 else 0)) :
  match_cfgs_ext p (S_Running (((l, 0), r, m), sb, ms))
                   (S_Running (((l, 0), r', m'), sb', ct, ms))
(* Stuttering on the source procedure entry *)
| match_cfgs_ext_ct2
  l blk r m sb (ms:bool) r' m' sb'
  (CT: nth_error p l = Some (blk, true))
  (CT1: (uslh_prog p)[[(l, 0)]] = Some <{{ ctarget }}>)
  (CT2: (uslh_prog p)[[(l, 1)]] = Some <{{ msf := (callee = (& (l, 0))) ? msf : 1 }}>)
  (REG: Rsync1 p r r' ms)
  (MSC: Msync p m m')
  (MS: eval r' <{{ (callee = (& (l, 0))) ? msf : 1 }}> = N (if ms then 1 else 0)) :
  match_cfgs_ext p (S_Running (((l, 0), r, m), sb, ms))
                   (S_Running (((l, 1), r', m'), sb', false, ms))
(* Match source call with target call *)
| match_cfgs_ext_call
  pc fp r m sb ms pc' r' m' sb'
  (CALL: p[[pc]] = Some <{{ call fp }}>)
  (TCALL: (uslh_prog p)[[pc' + 1]] = Some <{{ call ((msf = 1) ? &(0, 0) : fp) }}>)
  (PC: pc_sync p pc = Some pc')
  (REG: Rsync p r r' ms)
  (MSC: Msync p m m')
  (MS: r' ! callee = (eval r' <{{ (msf = 1) ? &(0, 0) : fp }}>)) :
  match_cfgs_ext p (S_Running ((pc, r, m), sb, ms))
                   (S_Running ((pc' + 1, r', m'), sb', false, ms))
(* Match source fault with target fault on faulted call *)
| match_cfgs_ext_call_fault
  pc r m sb ms
  (CT: (uslh_prog p)[[pc]] <> Some <{{ ctarget }}>):
  match_cfgs_ext p S_Fault
                   (S_Running ((pc, r, m), sb, true, ms))
(* Match source branch with target branch *)
| match_cfgs_ext_br_true1
  l l' r m sb (ms: bool) r' m' sb'
  pc fl fo e
  (BR: p[[pc]] = Some <{{ branch e to l }}>)
  (FROM: (uslh_prog p) [[(fl, fo)]] = Some <{{ branch ((msf = 1) ? 0 : e) to l' }}>)
  (TO: (uslh_prog p) [[(l', 0)]] =
         Some <{{ msf := (~((msf = 1) ? 0 : e)) ? 1 : msf }}>)
  (MS: eval r' <{{ (~ ((msf = 1) ? 0 : e)) ? 1 : msf }}> = N (if ms then 1 else 0))

  (BT2: (uslh_prog p)[[(l', 1)]] = Some <{{ jump l }}>)
  (REG: Rsync1 p r r' ms)
  (MSC: Msync p m m') :
  match_cfgs_ext p (S_Running (((l, 0), r, m), sb, ms))
                   (S_Running (((l', 0), r', m'), sb', false, ms))
(* Match source branch with target hardening *)
| match_cfgs_ext_br_true2
  pc e l l' r m sb ms r' m' sb'
  (BR: p[[pc]] = Some <{{ branch e to l }}>)
  (BT2: (uslh_prog p)[[(l', 1)]] = Some <{{ jump l }}>)
  (REG: Rsync p r r' ms)
  (MSC: Msync p m m') :
  match_cfgs_ext p (S_Running (((l, 0), r, m), sb, ms))
                   (S_Running (((l', 1), r', m'), sb', false, ms))
(* Match source branch false with target branch false (fall-through) *)
| match_cfgs_ext_br_false
  pc pc' l e r r' m m' sb sb' (ms:bool)
  (FROM: (uslh_prog p) [[pc']] = Some <{{ branch ((msf = 1) ? 0 : e) to l }}>)
  (TO: (uslh_prog p) [[pc'+1]] = Some <{{ msf := ((msf = 1) ? 0 : e) ? 1 : msf }}>)
  (MS: eval r' <{{ ((msf = 1) ? 0 : e) ? 1 : msf }}> = N (if ms then 1 else 0))
  (PC: pc_sync p pc = Some pc')
  (REG: Rsync1 p r r' ms)
  (MSC: Msync p m m') :
  match_cfgs_ext p (S_Running ((pc + 1, r, m), sb, ms))
                   (S_Running ((pc' + 1, r', m'), sb', false, ms))
(* Match source ret with first step of target return masking (loading current value at "sp") *)
| match_cfgs_ext_ret1
  pc pc' r r' m m' sb sb' (ms: bool) spv
  (RET: p[[pc]] = Some <{{ ret }}>)
  (PC: pc_sync p pc = Some pc')
  (REG: Rsync p r r' ms)
  (MSC: Msync p m m')
  (SP: r ! sp = N spv)
  (CALLEE: ms = false -> nth_error m'.(memory) spv = Some (r' ! callee)) :
  match_cfgs_ext p (S_Running ((pc, r, m), sb, ms))
                   (S_Running ((pc' + 1, r', m'), sb', false, ms))
(* Match source ret with second step of target return masking (after potentially masking at "sp" value) *)
| match_cfgs_ext_ret2
  pc pc' r r' m m' sb sb' (ms: bool) spv
  (RET: p[[pc]] = Some <{{ ret }}>)
  (PC: pc_sync p pc = Some pc')
  (REG: Rsync p r r' ms)
  (MSC: Msync p m m')
  (SP: r ! sp = N spv)
  (SLOT: ms = true -> sb' ! spv = FP (0, 0)) :
  match_cfgs_ext p (S_Running ((pc, r, m), sb, ms))
                   (S_Running (((pc' + 1) + 1, r', m'), sb', false, ms))
(* Match source ret with third step of target return masking (loading "callee" potentially masked) *)
| match_cfgs_ext_ret3
  pc pc' r r' m m' sb sb' (ms: bool) spv
  (RET: p[[pc]] = Some <{{ ret }}>)
  (PC: pc_sync p pc = Some pc')
  (REG: Rsync p r r' ms)
  (MSC: Msync p m m')
  (SP: r ! sp = N spv)
  (CALLEE: if ms then sb' ! spv = FP (0, 0) /\ r' ! callee = FP (0, 0)
           else nth_error m'.(memory) spv = Some (r' ! callee)) :
  match_cfgs_ext p (S_Running ((pc, r, m), sb, ms))
                   (S_Running ((((pc' + 1) + 1) + 1, r', m'), sb', false, ms))
(* Match after return step in target with source: either (0, 0) on misspeculation, or the actual return target *)
| match_cfgs_ext_ret4 (* after return *)
  l o l' o' r r' m m' sb sb' (ms:bool) e
  (PC: pc_sync p (l, o - 1) = Some (l', o')) (* call - callee asgn match *)
  (FROM: p[[(l, o - 1)]] = Some (ICall e))
  (POS: o > 0)
  (TO: (uslh_prog p) [[(l', o' + 2)]] = Some <{{ msf := (callee = (& (l', o' + 2))) ? msf : 1 }}>)
  (REG: Rsync1 p r r' ms)
  (MSC: Msync p m m')
  (MS: eval r' <{{ (callee = (& (l', o' + 2))) ? msf : 1 }}> = N (if ms then 1 else 0)) :
  match_cfgs_ext p (S_Running (((l, o), r, m), sb, ms))
                   (S_Running (((l', o' + 2), r', m'), sb', false, ms))
(* Match fault to fault *)
| match_cfgs_ext_fault :
  match_cfgs_ext p S_Fault S_Fault
(* Match term to term *)
| match_cfgs_ext_term :
  match_cfgs_ext p S_Term S_Term
.

(* USLH simulation relation between ideal and hardened speculative programs *)
Definition uslh_sim (p : prog) (h : option uslh_hstate) ic sc :=
  h = tctrl p (uslh_prog p) sc /\ match_cfgs_ext p ic sc.

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
  (UNUSED: unused_prog sp p)
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
  - (* ICall is in the expansion of instruction a *)
    rewrite nth_error_app1 in NTH; auto.
    destruct a; ss; unfold MiniCET.uslh_ret in *; clarify;
    try (exfalso; eapply nth_error_In in NTH; ss; des; clarify; fail).
    (* branch case *)
    + exfalso. eapply bind_inv in MAP. des.
      unfold add_block_M, add_block in MAP. clarify.
      destruct pos; simpl in NTH; [discriminate NTH|].
      destruct pos; simpl in NTH; [discriminate NTH|].
      rewrite nth_error_nil in NTH. discriminate NTH.
    (* call case *)
    + exists 0, fp. split; [auto|].
      destruct pos; [exfalso; simpl in NTH; discriminate NTH|].
      destruct pos; [simpl in NTH; clarify; auto|].
      exfalso. destruct pos; simpl in NTH; [discriminate NTH|].
      rewrite nth_error_nil in NTH. discriminate NTH.
  - (* ICall is in the rest *)
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

  (* Step 1: show l < length p *)
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

  (* Step 2: get source block *)
  assert (SRC_BLK: exists sblk, nth_error p l = Some sblk).
  { destruct (nth_error p l) eqn:E; [eauto|].
    exfalso. eapply nth_error_None in E. lia. }
  des.

  (* Step 3: use label_inv *)
  hexploit label_inv; eauto. i. des.
  rename H into TBLK'. rename H0 into USLH_BLK. rename H1 into C_EQ.

  (* TBLK': nth_error (uslh_prog p) l = Some blk' *)
  (* USLH_BLK: uslh_blk (l, sblk) c = (blk', np') *)
  rewrite TBLK in TBLK'. injection TBLK' as TBLK'. subst.

  (* Now unfold uslh_blk *)
  destruct sblk as [sbl s_proc]. simpl in USLH_BLK.
  eapply bind_inv in USLH_BLK. des. subst.
  unfold concatM in USLH_BLK. eapply bind_inv in USLH_BLK. des.
  ss. unfold MiniCET.uslh_ret in *. clarify.
  erewrite uslh_offset_uslh_add_index in USLH_BLK; eauto.

  (* Now tblk = (if s_proc then [ctarget; msf_init] ++ concat a else concat a, s_proc)
     CALL_AT: nth_error tblk (o-1) = Some (ICall e) *)
  (* The ICall must be in concat a (not in ctarget/msf_init header) *)

  (* Step 4: use concat_call_find *)
  assert (CALL_IN_CONCAT: exists pos', nth_error (List.concat a0) pos' = Some (ICall e) /\
          (if s_proc then add pos' 2 = o - 1 else pos' = o - 1)).
  { des_ifs; simpl in CALL_AT.
    - destruct (o - 1) eqn:EQ; [simpl in CALL_AT; discriminate|].
      destruct n eqn:EQ2; [simpl in CALL_AT; discriminate|].
      simpl in CALL_AT. exists n0. split; auto. lia.
    - exists (o - 1). split; auto. }

  des.
  exploit concat_call_find; eauto. i. des.

  (* Step 5: establish pc_sync *)
  assert (OFS: exists io, nth_error (_offset_uslh sbl (if s_proc then 2 else 0)) o_src = Some io).
  { destruct (nth_error (_offset_uslh sbl (if s_proc then 2 else 0)) o_src) eqn:E; [eauto|].
    exfalso. eapply nth_error_None in E. rewrite _offset_uslh_length in E.
    simpl in x0. assert (o_src < Datatypes.length sbl) by (eapply nth_error_Some; ii; clarify). lia. }
  des.

  hexploit offset_eq_aux; eauto.
  { pose proof (proj1 (nth_error_Some (_offset_uslh sbl (if s_proc then 2 else 0)) o_src)) as HH. rewrite _offset_uslh_length in HH. simpl. apply HH. rewrite OFS. discriminate. }
  i. (* H: prefix_offset a0 o_src (if s_proc then 2 else 0) = io *)

  (* From prefix_offset a0 o_src base = io and pos' = prefix_offset a0 o_src 0 + 1 *)
  assert (IO_EQ: io = (if s_proc then add (prefix_offset a0 o_src 0) 2 else prefix_offset a0 o_src 0)).
  { unfold prefix_offset in H |- *. rewrite fold_left_init_0 in H.
    destruct s_proc.
    - rewrite <- H. simpl. lia.
    - rewrite <- H. simpl. lia. }

  (* The ICall in tblk is at position o-1 which equals io+1 *)
  assert (O_EQ: o - 1 = add io 1).
  { subst. des_ifs; lia. }

  (* So o = io + 2 *)
  assert (O_EQ2: o = add io 2).
  { lia. }

  (* pc_sync p (l, o_src) maps to (l, io) *)
  assert (PCSYNC: pc_sync p (l, o_src) = Some (l, io)).
  { unfold pc_sync. simpl. rewrite nth_error_map. rewrite SRC_BLK.
    simpl. unfold offset_uslh. simpl. rewrite OFS. auto. }

  (* ret_sync p (l, S o_src) = Some (l, io + 2) = Some (l, o) *)
  assert (RETSYNC: ret_sync p (l, S o_src) = Some (l, o)).
  { simpl in x0. unfold ret_sync. simpl.
    change (p[[(l, o_src)]]) with (fetch p (l, o_src)).
    unfold fetch. rewrite SRC_BLK. simpl. rewrite x0.
    fold (pc_sync p (l, o_src)). rewrite PCSYNC. f_equal. f_equal. lia. }

  (* wf_ret p (l, S o_src) *)
  assert (WF_RET_SRC: wf_ret p (l, S o_src)).
  { red. simpl. split.
    - (* p[[(l, S o_src)]] <> None *)
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

  (* (uslh_prog p)[[l, o]] *)
  assert (TGT_FETCH: (uslh_prog p)[[(l, o)]] =
    Some <{{ msf := (callee = (& (l, o))) ? msf : 1 }}>).
  { rename H into PFX. clear O_EQ2 RETSYNC PCSYNC.
    exploit mapM_nth_error_strong; eauto.
    { eapply _offset_uslh_combine; eauto. }
    i. des.
    ss. unfold MiniCET.uslh_ret in *. clarify.
    exploit (concat_nth_error a0 _ _ 2); eauto; [ss|]. intro CNE. des.
    destruct s_proc; ss; unfold MiniCET.uslh_ret in *; clarify.
    + (* s_proc = true: header [ctarget; msf_init] ++ concat a0 *)
      unfold fetch. rewrite TBLK. simpl.
      destruct o; [lia|]. destruct o; [lia|]. simpl.
        assert (OO: o = prefix_offset a0 o_src 0 + 2) by lia.
        rewrite OO. rewrite CNE.
        assert (PP: prefix_offset a0 o_src 2 + 2 = S (S (prefix_offset a0 o_src 0 + 2))) by
          (unfold prefix_offset; rewrite fold_left_init_0; lia).
        rewrite PP. reflexivity.
    + (* s_proc = false *)
      unfold fetch. rewrite TBLK. simpl.
      assert (OO: o = prefix_offset a0 o_src 0 + 2) by lia.
      rewrite OO. rewrite CNE. reflexivity. }

  (* Now assemble *)
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
  (* (NCT: no_ct_prog p) *)
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
  (UNUSED: unused_prog sp p)
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

Lemma wf_ret_rsync_src p sr tr x l o
  (WFP: wf_prog p)
  (RET: Rsync p sr tr false)
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

Lemma wf_ret_rsync_tgt p sr tr x l o
  (WFP: wf_prog p)
  (NCT: no_ct_prog p)
  (UNUSED: unused_prog sp p)
  (RET: Rsync p sr tr false)
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


Lemma nth_error_upd_same {A} (l: list A) i a :
  nth_error (upd i l a) i = option_map (fun _ => a) (nth_error l i).
Proof. induction l in i |- *; destruct i; ss. Qed.

Lemma Msync_nth p m m' n v'
  (MSC: Msync p m m')
  (NTH: nth_error m'.(memory) n = Some v') :
  exists v, nth_error m.(memory) n = Some v /\ val_match p v v'.
Proof. destruct MSC as [MSC _]. specialize (MSC n). rewrite NTH in MSC. des_ifs. eauto. Qed.

Lemma Msync_upd p m m' n v v'
  (MSC: Msync p m m')
  (VAL: val_match p v v') :
  Msync p (upd_mem n m v) (upd_mem n m' v').
Proof.
  unfold Msync, upd_mem in *. ss. destruct MSC as [MSC TOP]. split; [|exact TOP].
  i. specialize (MSC i).
  destruct (Nat.eq_dec n i); subst.
  - rewrite! nth_error_upd_same.
    destruct (nth_error (memory m) i), (nth_error (memory m') i); ss.
  - rewrite! upd_neq; auto.
Qed.

Lemma Msync_upd_same p m m' n v'
  (MSC: Msync p m m')
  (NTH: nth_error m'.(memory) n = Some v') :
  Msync p m (upd_mem n m' v').
Proof.
  unfold Msync, upd_mem in *. ss. destruct MSC as [MSC TOP]. split; [|exact TOP].
  i. specialize (MSC i).
  destruct (Nat.eq_dec n i); subst.
  - rewrite nth_error_upd_same. rewrite NTH in *. ss.
  - rewrite upd_neq; auto.
Qed.

Lemma Rsync_Rsync1 p r r' ms
  (REG: Rsync p r r' ms) :
  Rsync1 p r r' ms.
Proof. red in REG. des. red. auto. Qed.

Lemma Rsync1_Rsync p r r' ms
  (REG: Rsync1 p r r' ms)
  (MSF: r' ! msf = N (if ms then 1 else 0)) :
  Rsync p r r' ms.
Proof. red. auto. Qed.

Lemma Rsync1_sp p r r' ms
  (REG: Rsync1 p r r' ms) :
  val_match p (r ! sp) (r' ! sp).
Proof. eapply REG; [split; discriminate | auto]. Qed.

Lemma Rsync1_mono p r r' ms ms'
  (REG: Rsync1 p r r' ms)
  (MS: ms = true -> ms' = true) :
  Rsync1 p r r' ms'.
Proof.
  ii. eapply REG; [eauto|].
  destruct H0 as [H0|H0]; auto.
  left. destruct ms; auto. exploit MS; [reflexivity|]. congruence.
Qed.

Lemma Rsync1_upd p r r' ms x v v'
  (REG: Rsync1 p r r' ms)
  (VAL: ms = false \/ x = sp -> val_match p v v') :
  Rsync1 p (x !-> v; r) (x !-> v'; r') ms.
Proof.
  ii. destruct (string_dec x x0); subst.
  - rewrite! t_update_eq. eauto.
  - rewrite! t_update_neq; eauto.
Qed.

Lemma Rsync1_upd_tgt p r r' ms x v'
  (REG: Rsync1 p r r' ms)
  (X: x = msf \/ x = callee) :
  Rsync1 p r (x !-> v'; r') ms.
Proof.
  ii. des; subst; rewrite t_update_neq; eauto.
Qed.

Lemma pc_sync_next' p pc tpc i
  (WFP: wf_prog p)
  (SYNC: pc_sync p pc = Some tpc)
  (INST: p[[pc]] = Some i)
  (NT: ~ is_terminator i) :
  pc_sync p (pc + 1) = Some (fst tpc, snd tpc + uslh_inst_sz i).
Proof.
  exploit block_always_terminator_prog; eauto. i. des.
  eapply pc_sync_next; eauto.
Qed.

Lemma pc_sync_next_simple p pc tpc i
  (WFP: wf_prog p)
  (SYNC: pc_sync p pc = Some tpc)
  (INST: p[[pc]] = Some i)
  (SIMP: simple_inst i)
  (NT: ~ is_terminator i) :
  pc_sync p (pc + 1) = Some (tpc + 1).
Proof.
  erewrite pc_sync_next'; eauto. destruct tpc. destruct i; ss.
Qed.

Lemma pc_sync_entry p l blk
  (WFP: wf_prog p)
  (BLK: nth_error p l = Some (blk, false)) :
  pc_sync p (l, 0) = Some (l, 0).
Proof.
  inv WFP. rewrite Forall_forall in H0. exploit H0; [eapply nth_error_In; eauto|]. i.
  red in x0. des. unfold nonempty_block in x0. ss.
  destruct blk; [ss; lia|].
  unfold pc_sync. ss. rewrite nth_error_map. rewrite BLK. ss.
Qed.

Lemma eval_masked_nat p r r' ms e n
  (REG: Rsync p r r' ms)
  (U1: e_unused msf e)
  (U2: e_unused callee e)
  (WFE: wf_expr p e)
  (TGT: to_nat (eval r' <{{ (msf = 1) ? 0 : e }}>) = Some n) :
  (if ms then Some 0 else to_nat (eval r e)) = Some n.
Proof.
  dup REG. destruct REG0 as [REGX MSF].
  simpl in TGT. rewrite MSF in TGT. destruct ms; ss.
  rewrite <- TGT. eapply (eval_regs_eq_nat p);
    [eauto | eauto | apply wf_expr_wf_exp; auto | eapply Rsync_Rsync1; eauto].
Qed.

Lemma ctarget_src p pc
  (NCT: no_ct_prog p)
  (UNUSED: unused_prog callee p)
  (CT: (uslh_prog p)[[pc]] = Some <{{ ctarget }}>) :
  exists l blk, pc = (l, 0) /\ nth_error p l = Some (blk, true).
Proof.
  exploit head_call_target; eauto. i. des. subst. exists l.
  destruct (nth_error p l) as [ [blk' b'] | ] eqn:CTSRC.
  - destruct b'; eauto.
    eapply no_ctarget_exists with (o:=0) in CTSRC; eauto. clarify.
  - exfalso. rewrite nth_error_None in CTSRC.
    assert (CT0: nth_error blk 0 = Some <{{ ctarget }}>).
    { simpl in CT. rewrite x1 in CT. ss. }
    clear CT x2. unfold uslh_prog in x1. des_ifs.
    exploit mapM_perserve_len; eauto. rewrite length_add_index. intros LEN.
    rewrite nth_error_app2 in x1; [|lia].
    eapply nth_error_In in x1.
    exploit new_prog_no_ct; eauto. intros NCTN.
    eapply no_ct_prog_In in NCTN; eauto.
    unfold no_ct_blk in NCTN. rewrite Forall_forall in NCTN.
    eapply nth_error_In in CT0. eapply NCTN in CT0. ss.
Qed.

Lemma val_match_fp_entry p l1 l2 a
  (VM: val_match p (FP l1) (FP l2)) :
  ((a =? fst l1) && (0 =? snd l1))%nat = ((a =? fst l2) && (0 =? snd l2))%nat.
Proof.
  destruct l1 as [x1 y1], l2 as [x2 y2]. unfold val_match in VM.
  destruct y1; cbn [Nat.eqb] in VM.
  - des; subst. auto.
  - destruct y2.
    + eapply ret_sync_nonzero in VM. clarify.
    + cbn [fst snd Nat.eqb]. rewrite! andb_false_r. auto.
Qed.

Lemma val_match_ret_addr p pc tpc e
  (CALL: p[[pc]] = Some <{{ call e }}>)
  (PC: pc_sync p pc = Some tpc) :
  val_match p (FP (pc + 1)) (FP ((tpc + 1) + 1)).
Proof.
  destruct pc as [a b], tpc as [a' b']. unfold inc, val_match.
  replace (Nat.add b 1) with (S b) by lia. cbn [Nat.eqb].
  unfold ret_sync. rewrite CALL. rewrite PC. rewrite <- add_assoc. reflexivity.
Qed.

Lemma val_match_fp_inv p v l
  (VM: val_match p v (FP l)) :
  exists l0, v = FP l0 /\ val_match p (FP l0) (FP l).
Proof. destruct v; ss; eauto; destruct pc; ss. Qed.

Lemma val_match_n_inv p v n
  (VM: val_match p v (N n)) :
  v = N n.
Proof. destruct v; ss; subst; auto; destruct pc; ss. Qed.

Lemma cptr_eqb_spec (x y: cptr) :
  ((fst x =? fst y) && (snd x =? snd y))%nat = true <-> x = y.
Proof.
  destruct x, y; ss. rewrite andb_true_iff, !Nat.eqb_eq.
  split; i; des; subst; clarify.
Qed.

Lemma val_match_fp_eqb p a a' b b'
  (VA: val_match p (FP a) (FP a'))
  (VB: val_match p (FP b) (FP b')) :
  ((fst a =? fst b) && (snd a =? snd b))%nat = ((fst a' =? fst b') && (snd a' =? snd b'))%nat.
Proof.
  destruct ((fst a =? fst b) && (snd a =? snd b))%nat eqn:E1;
  destruct ((fst a' =? fst b') && (snd a' =? snd b'))%nat eqn:E2; auto; exfalso.
  - rewrite cptr_eqb_spec in E1. subst.
    exploit val_match_fp_functional; [exact VA|exact VB|]. i. subst.
    assert (((fst b' =? fst b') && (snd b' =? snd b'))%nat = true) by (apply cptr_eqb_spec; auto).
    congruence.
  - rewrite cptr_eqb_spec in E2. subst.
    exploit val_match_fp_inj; [exact VA|exact VB|]. i. subst.
    assert (((fst b =? fst b) && (snd b =? snd b))%nat = true) by (apply cptr_eqb_spec; auto).
    congruence.
Qed.

Lemma ret_sync_inv p l o tpc
  (RS: ret_sync p (l, S o) = Some tpc) :
  exists e l' o', p[[(l, o)]] = Some (ICall e) /\ pc_sync p (l, o) = Some (l', o') /\ tpc = (l', o' + 2).
Proof.
  unfold ret_sync in RS. cbn -[fetch pc_sync] in RS.
  destruct (p[[(l, o)]]) as [i|] eqn:INST; [|discriminate].
  destruct i; try discriminate.
  destruct (pc_sync p (l, o)) as [ [l' o'] | ] eqn:PS; [|discriminate].
  injection RS as <-. exists fp, l', o'. splits; reflexivity.
Qed.

Definition writes_reg (x: string) (i: inst) : Prop :=
  match i with
  | IAsgn y _ | IDiv y _ _ | ILoad y _ => y = x
  | _ => False
  end.

Lemma tctrl_spec_step p_s p st st' ds os
  (STEP: p |- <(( st ))> -->_ ds ^^ os <(( st' ))>)
  (NOSP: forall pc r m sb ms i,
      st = S_Running ((pc, r, m), sb, false, ms) ->
      p[[pc]] = Some i -> ~ writes_reg sp i) :
  tctrl_step (tctrl p_s p st) ds os = tctrl p_s p st'.
Proof.
  inv STEP; cbn [tctrl]; unfold tctrl_step; cbn [hs_ct hs_tgt hs_tpc hs_sp].
  all: try match goal with
           | H: fetch ?q ?x <> Some _ |- _ => destruct (fetch q x) as [ [] | ]; congruence
           end.
  all: try destruct ct.
  all: match goal with
       | H: fetch _ _ = Some _ |- _ => rewrite H
       end;
       unfold hs_set; cbn [hs_src hs_tgt]; try rewrite t_update_eq; try reflexivity.
  all: rewrite t_update_neq; [reflexivity|].
  all: intros ->; eapply NOSP; [reflexivity|eassumption|ss].
Qed.

Lemma val_match_sync_fp p a b
  (VM: val_match p (FP a) (FP b)) :
  b = sync_fp p a.
Proof.
  destruct a as [l [|o] ], b as [l' o']; unfold val_match in VM; cbn [Nat.eqb] in VM.
  - des; subst. reflexivity.
  - unfold sync_fp. rewrite VM. reflexivity.
Qed.

Lemma match_obs_sync_ob p os1 os2
  (MO: match_obs p os1 os2) :
  os2 = map (sync_ob p) os1.
Proof.
  induction MO as [|o1 o2 os1 os2 MO1 MO2 IH]; ss. f_equal; auto.
  destruct o1, o2; ss; des; clarify.
  all: f_equal; eapply val_match_sync_fp; eauto.
Qed.

Lemma offset_uslh_NoDup blk :
  NoDup (offset_uslh blk).
Proof.
  destruct blk as [l b]. unfold offset_uslh.
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

Lemma index_of_nth_error n l o
  (ND: NoDup l)
  (NTH: nth_error l o = Some n) :
  index_of n l = Some o.
Proof.
  induction l as [|x tl IH] in o, ND, NTH |- *; destruct o; ss; clarify.
  - rewrite Nat.eqb_refl. reflexivity.
  - inversion ND as [|? ? NIN ND']; subst.
    destruct (x =? n)%nat eqn:E.
    + rewrite Nat.eqb_eq in E. subst. exfalso. eapply NIN. eapply nth_error_In; eauto.
    + rewrite (IH o ND' NTH). reflexivity.
Qed.

Lemma ret_unsync_ret_sync p pc tpc
  (RS: ret_sync p pc = Some tpc) :
  ret_unsync p tpc = pc.
Proof.
  destruct pc as [l [|o] ]; [ss|].
  exploit ret_sync_inv; eauto. intros (e & l' & o' & CALL & PS & ->).
  exploit pc_sync_same_label; eauto. intros <-.
  unfold pc_sync in PS. rewrite nth_error_map in PS.
  destruct (nth_error p l) as [blk|] eqn:BLK; ss.
  destruct (nth_error (offset_uslh blk) o) as [io|] eqn:OFS; clarify.
  unfold ret_unsync. rewrite BLK, Nat.add_sub.
  erewrite index_of_nth_error; eauto. apply offset_uslh_NoDup.
Qed.

Lemma pc_sync_lt p pc tpc
  (SYNC: pc_sync p pc = Some tpc) :
  (fst tpc < Datatypes.length p)%nat.
Proof.
  destruct pc as [l o], tpc as [l' o']. unfold pc_sync in SYNC.
  rewrite nth_error_map in SYNC.
  destruct (nth_error p l) eqn:BLK; ss; des_ifs.
  apply nth_error_Some. congruence.
Qed.

Lemma ideal_safe_ret_bound p pc r m spv sb
  (SAFE: sequential_safe (L := IdealLang) p (S_Running (pc, r, m, sb, false)))
  (RET: p[[pc]] = Some <{{ ret }}>)
  (SP: r ! sp = N spv) :
  spv < stack_top m.
Proof.
  exploit SAFE; [exact (sem_refl (L := IdealLang) p _)|].
  intros (ds1 & os1 & st1 & STEP1).
  inv STEP1; rewrite RET in *; clarify; rewrite SP in *; clarify.
Qed.

Lemma ideal_safe_ret_target p pc r m spv pc' sb
  (SAFE: sequential_safe (L := IdealLang) p (S_Running (pc, r, m, sb, false)))
  (RET: p[[pc]] = Some <{{ ret }}>)
  (SP: r ! sp = N spv)
  (NTH: nth_error m.(memory) spv = Some (FP pc')) :
  exists i, p[[pc']] = Some i.
Proof.
  assert (STACK_TOP: spv < stack_top m) by (eapply ideal_safe_ret_bound; eauto).
  assert (STEP: p |- <(( S_Running (pc, r, m, sb, false) ))> -->i_ [DRet None] ^^ [ORet pc' spv]
                     <(( S_Running (pc', sp !-> N (spv - 1); r, m, sb, false) ))>)
    by (eapply ISMI_Ret_Step; eauto).
  exploit SAFE; [exact (sem_step1 (L := IdealLang) STEP)|].
  intros (ds1 & os1 & st1 & STEP1). inv STEP1; eauto.
Qed.

Lemma match_cfgs_ext_no_sp_write p s t
  (NCT: no_ct_prog p)
  (UNUSED3: unused_prog sp p)
  (MATCH: match_cfgs_ext p s t) :
  forall pc r m sb ms i,
    t = S_Running ((pc, r, m), sb, false, ms) ->
    (uslh_prog p)[[pc]] = Some i -> ~ writes_reg sp i.
Proof.
  intros pc0 r0 m0 sb0 ms0 i0 EQ FETCH.
  inv MATCH; clarify.
  { inv MATCH0.
    exploit tgt_inv; eauto. intros (si & SRC & MI).
    exploit unused_prog_lookup; try eapply UNUSED3; eauto. intros U3.
    inv MI; [inv MATCH; ss; des; auto| | |]; ss; intro X; inv X. }
  all: exploit src_inv; try eapply RET; eauto; intros (ti & TI & MI);
       inv MI; [inv SIMPL|]; rewrite SYNC in PC; clarify.
  all: ss; intro X; inv X.
Qed.

Arguments tctrl : simpl never.
Arguments uslh_Tdir : simpl never.
Arguments uslh_Tobs : simpl never.
Arguments ret_unsync : simpl never.

Lemma bcc_stay p ic sc ds os sc2
  (TDIR: uslh_Tdir (tctrl p (uslh_prog p) sc) ds = [])
  (TOBS: uslh_Tobs (tctrl p (uslh_prog p) sc) ds [] = os)
  (MATCH: match_cfgs_ext p ic sc2) :
  exists os' ic2, p |- <(( ic ))> -->i*_ (uslh_Tdir (tctrl p (uslh_prog p) sc) ds) ^^ os' <(( ic2 ))>
    /\ match_cfgs_ext p ic2 sc2
    /\ os = uslh_Tobs (tctrl p (uslh_prog p) sc) ds os'.
Proof.
  exists [], ic. subst os. rewrite TDIR. splits; auto. apply (sem_refl (L := IdealLang)).
Qed.

Lemma bcc_step p ic sc ds os sc2 ds_s os_s ic2
  (STEP: p |- <(( ic ))> -->i_ ds_s ^^ os_s <(( ic2 ))>)
  (TDIR: uslh_Tdir (tctrl p (uslh_prog p) sc) ds = ds_s)
  (TOBS: uslh_Tobs (tctrl p (uslh_prog p) sc) ds os_s = map (sync_ob p) os_s)
  (OBS: match_obs p os_s os)
  (MATCH: match_cfgs_ext p ic2 sc2) :
  exists os' ic2, p |- <(( ic ))> -->i*_ (uslh_Tdir (tctrl p (uslh_prog p) sc) ds) ^^ os' <(( ic2 ))>
    /\ match_cfgs_ext p ic2 sc2
    /\ os = uslh_Tobs (tctrl p (uslh_prog p) sc) ds os'.
Proof.
  exists os_s, ic2. subst ds_s. splits; auto.
  - apply (sem_step1 (L := IdealLang)). exact STEP.
  - rewrite (match_obs_sync_ob p os_s os OBS). symmetry. exact TOBS.
Qed.

Ltac tcomp :=
  unfold uslh_Tdir, uslh_Tobs, uslh_mask, unsync_dirs, uslh_kind, tctrl;
  cbn [hs_ct hs_tgt hs_tpc hs_sp hs_src];
  repeat match goal with
         | H: fetch _ ?x = Some _ |- context [fetch _ ?x] => rewrite H
         end;
  simpl;
  repeat match goal with
         | H: ?x <> ?y |- context [String.eqb ?x ?y] => rewrite (proj2 (String.eqb_neq x y) H)
         | H: (?a < ?b)%nat |- context [Nat.ltb ?a ?b] => rewrite (proj2 (Nat.ltb_lt a b) H)
         | H: Nat.ltb ?a ?b = _ |- context [Nat.ltb ?a ?b] => rewrite H
         | H: ?r ! sp = N _ |- context [?r ! sp] => rewrite H
         end;
  simpl; rewrite ?app_nil_r; try reflexivity.

Lemma ultimate_slh_bcc_single (p: prog) ic1 sc1 sc2 ds os (h : option uslh_hstate)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (UNUSED3: unused_prog sp p)
  (MATCH: uslh_sim p h ic1 sc1)
  (TGT: uslh_prog p |- <(( sc1 ))> -->_ ds^^os <(( sc2 ))>)
  (SAFE: sequential_safe (L := IdealLang) p ic1) :
  exists os' ic2, p |- <(( ic1 ))> -->i*_ (uslh_Tdir h ds) ^^ os' <(( ic2 ))>
               /\ uslh_sim p (tctrl_step h ds os) ic2 sc2
               /\ os = uslh_Tobs h ds os'.
Proof.
  destruct MATCH as [-> MATCH].
  rewrite (tctrl_spec_step p (uslh_prog p) sc1 sc2 ds os TGT
             (match_cfgs_ext_no_sp_write p ic1 sc1 NCT UNUSED3 MATCH)).
  enough (CORE: exists os' ic2,
             p |- <(( ic1 ))> -->i*_ (uslh_Tdir (tctrl p (uslh_prog p) sc1) ds) ^^ os' <(( ic2 ))>
             /\ match_cfgs_ext p ic2 sc2
             /\ os = uslh_Tobs (tctrl p (uslh_prog p) sc1) ds os').
  { destruct CORE as (os' & ic2 & RUN & M & O). exists os', ic2.
    split; [exact RUN|]. split; [split; [reflexivity|exact M]|exact O]. }
  inv MATCH; try sfby inv TGT.
  (* pc_sync match *)
  - inv MATCH0. inv TGT; clarify;
      try (exploit tgt_inv; eauto; intros (si & SRC & MI); inv MI; inv MATCH; fail).
    (* skip *)
    + exploit tgt_inv; eauto. intros (si & SRC & MI). inv MI. inv MATCH.
      eapply bcc_step with (ic2 := S_Running ((pc+1, r, m), sb, ms));
        [econs; eauto|tcomp|tcomp|ss; econs|].
      econs. econs; eauto.
      eapply pc_sync_next_simple; eauto; ss; ii; ss.
    (* asgn *)
    + exploit tgt_inv; eauto. intros (si & SRC & MI). inv MI.
      * inv MATCH.
        exploit unused_prog_lookup; try eapply UNUSED1; eauto. intros U1.
        exploit unused_prog_lookup; try eapply UNUSED2; eauto. intros U2.
        exploit unused_prog_lookup; try eapply UNUSED3; eauto. intros U3. ss. des.
        eapply bcc_step with (ic2 := S_Running ((pc+1, x !-> eval r e; r, m), sb, ms));
          [econs; eauto|tcomp|tcomp|ss; econs|].
        econs. econs; eauto.
        { eapply pc_sync_next_simple; eauto; ss; ii; ss. }
        { inv REG. eapply Rsync1_Rsync.
          - eapply Rsync1_upd; eauto. i. des; clarify.
            eapply eval_regs_eq; eauto.
            exploit wf_prog_lookup; eauto. ss. clear. apply wf_expr_wf_exp.
          - rewrite t_update_neq; eauto. }
      * rewrite SYNC in PC. clarify.
        eapply bcc_stay; [tcomp|tcomp|].
        eapply match_cfgs_ext_call; eauto.
        { inv REG. eapply Rsync1_Rsync.
          - eapply Rsync1_upd_tgt; eauto.
          - rewrite t_update_neq; eauto. ii; clarify. }
        { rewrite t_update_eq. rewrite eval_unused_update; eauto.
          exploit unused_prog_lookup; try eapply UNUSED2; eauto. i. ss. }
    (* div *)
    + exploit tgt_inv; eauto. intros (si & SRC & MI). inv MI. inv MATCH.
      exploit unused_prog_lookup; try eapply UNUSED1; eauto. intros U1.
      exploit unused_prog_lookup; try eapply UNUSED2; eauto. intros U2.
      exploit unused_prog_lookup; try eapply UNUSED3; eauto. intros U3.
      exploit wf_prog_lookup; eauto. intros WFI. ss. des.
      eapply bcc_step with (ds_s := []) (os_s := [ODiv v1 v2])
        (ic2 := S_Running ((pc+1, x !-> res; r, m), sb, ms));
        [econs; eauto|tcomp|tcomp|ss; repeat econs|].
      1-2: eapply eval_masked_nat; eauto.
      dup REG. destruct REG0 as [REGX MSF].
      econs. econs; eauto.
      { eapply pc_sync_next_simple; eauto; ss; ii; ss. }
      { eapply Rsync1_Rsync.
        - eapply Rsync1_upd; [eapply Rsync_Rsync1; eauto|]. i. subst res. destruct v2; ss.
        - rewrite t_update_neq; eauto. }
    (* branch *)
    + exploit tgt_inv; eauto. intros (si & SRC & MI). inv MI; [inv MATCH|].
      rewrite SYNC in PC. clarify.
      exploit unused_prog_lookup; try eapply UNUSED1; eauto. intros U1.
      exploit unused_prog_lookup; try eapply UNUSED2; eauto. intros U2.
      exploit wf_prog_lookup; eauto. intros WFI. ss. des.
      exploit eval_masked_nat; try eapply H8; eauto. intros N'.
      dup REG. destruct REG0 as [REGX MSF].
      eapply bcc_step with (ds_s := [DBranch b']) (os_s := [OBranch (not_zero n)])
        (ic2 := S_Running (((if b' then (l0, 0) else pc+1), r, m), sb, ms || negb (Bool.eqb (not_zero n) b')));
        [econs; eauto|tcomp|tcomp|ss; repeat econs|].
      destruct b'.
      * destruct pc' as [fl fo]. eapply match_cfgs_ext_br_true1; eauto.
        { ss. rewrite IN. ss. }
        { clear -H8 MSF. simpl in H8 |- *. rewrite MSF in *. destruct ms; ss.
          destruct (eval r' e0); ss. clarify. destruct n; ss. }
        { ss. rewrite IN. ss. }
        { eapply Rsync1_mono; [eapply Rsync_Rsync1; eauto|]. i. subst. ss. }
      * eapply match_cfgs_ext_br_false; eauto.
        { clear -H8 MSF. simpl in H8 |- *. rewrite MSF in *. destruct ms; ss.
          destruct (eval r' e0); ss. clarify. destruct n; ss. }
        { eapply Rsync1_mono; [eapply Rsync_Rsync1; eauto|]. i. subst. ss. }
    (* jump *)
    + exploit tgt_inv; eauto. intros (si & SRC & MI). inv MI. inv MATCH.
      exploit wf_prog_lookup; eauto. intros WFI. ss.
      unfold wf_lbl in WFI. des_ifs.
      exploit pc_sync_lt; eauto. intros LT.
      eapply bcc_step with (ic2 := S_Running (((l, 0), r, m), sb, ms));
        [econs; eauto|tcomp|tcomp|ss; econs|].
      econs. econs; eauto. eapply pc_sync_entry; eauto.
    (* load *)
    + exploit tgt_inv; eauto. intros (si & SRC & MI). inv MI.
      * inv MATCH.
        exploit unused_prog_lookup; try eapply UNUSED1; eauto. intros U1.
        exploit unused_prog_lookup; try eapply UNUSED2; eauto. intros U2.
        exploit unused_prog_lookup; try eapply UNUSED3; eauto. intros U3.
        exploit wf_prog_lookup; eauto. intros WFI. ss. des.
        exploit eval_masked_nat; try eapply H8; eauto. intros N'. ss.
        exploit Msync_nth; eauto. intros (v & NTH & VM).
        eapply bcc_step with (ds_s := []) (os_s := [OLoad n])
          (ic2 := S_Running ((pc+1, x !-> v; r, m), sb, false));
          [econs; eauto|tcomp|tcomp|ss; repeat econs|].
        dup REG. destruct REG0 as [REGX MSF].
        econs. econs; eauto.
        { eapply pc_sync_next_simple; eauto; ss; ii; ss. }
        { eapply Rsync1_Rsync.
          - eapply Rsync1_upd; [eapply Rsync_Rsync1; eauto|]. auto.
          - rewrite t_update_neq; eauto. }
      * rewrite SYNC in PC. clarify.
        dup REG. destruct REG0 as [REGX MSF].
        exploit Rsync1_sp; [eapply Rsync_Rsync1; eauto|]. intros VSP.
        ss. unfold to_nat in H8. des_ifs.
        eapply bcc_stay; [tcomp|tcomp|].
        eapply match_cfgs_ext_ret1; eauto.
        { eapply Rsync1_Rsync.
          - eapply Rsync1_upd_tgt; [eapply Rsync_Rsync1; eauto|]. auto.
          - rewrite t_update_neq; eauto. ii; clarify. }
        { unfold val_match in VSP. des_ifs. }
    (* load misspec *)
    + exploit tgt_inv; eauto. intros (si & SRC & MI). inv MI.
      * inv MATCH.
        exploit unused_prog_lookup; try eapply UNUSED1; eauto. intros U1.
        exploit unused_prog_lookup; try eapply UNUSED2; eauto. intros U2.
        exploit unused_prog_lookup; try eapply UNUSED3; eauto. intros U3.
        exploit wf_prog_lookup; eauto. intros WFI. ss. des.
        exploit eval_masked_nat; try eapply H8; eauto. intros N'. ss. clarify.
        eapply bcc_step with (ds_s := []) (os_s := [OLoad 0])
          (ic2 := S_Running ((pc+1, x !-> sb ! 0; r, m), sb, true));
          [econs; eauto|tcomp|tcomp|ss; repeat econs|].
        dup REG. destruct REG0 as [REGX MSF].
        econs. econs; eauto.
        { eapply pc_sync_next_simple; eauto; ss; ii; ss. }
        { eapply Rsync1_Rsync.
          - eapply Rsync1_upd; [eapply Rsync_Rsync1; eauto|]. i. des; clarify.
          - rewrite t_update_neq; eauto. }
      * rewrite SYNC in PC. clarify.
        dup REG. destruct REG0 as [REGX MSF].
        exploit Rsync1_sp; [eapply Rsync_Rsync1; eauto|]. intros VSP.
        ss. unfold to_nat in H8. des_ifs.
        eapply bcc_stay; [tcomp|tcomp|].
        eapply match_cfgs_ext_ret1; eauto.
        { eapply Rsync1_Rsync.
          - eapply Rsync1_upd_tgt; [eapply Rsync_Rsync1; eauto|]. auto.
          - rewrite t_update_neq; eauto. ii; clarify. }
        { unfold val_match in VSP. des_ifs. }
        { clarify. }
    (* store *)
    + exploit tgt_inv; eauto. intros (si & SRC & MI). inv MI. inv MATCH.
      exploit unused_prog_lookup; try eapply UNUSED1; eauto. intros U1.
      exploit unused_prog_lookup; try eapply UNUSED2; eauto. intros U2.
      exploit wf_prog_lookup; eauto. intros WFI. ss. des.
      exploit eval_masked_nat; try eapply H8; eauto. intros N'. ss.
      eapply bcc_step with (ds_s := []) (os_s := [OStore n])
        (ic2 := S_Running ((pc+1, r, upd_mem n m (eval r e')), n !-> eval r e'; sb, false));
        [econs; eauto|tcomp|tcomp|ss; repeat econs|].
      econs. econs; eauto.
      { eapply pc_sync_next_simple; eauto; ss; ii; ss. }
      { eapply Msync_upd; eauto.
        eapply (eval_regs_eq p); [eauto | eauto | apply wf_expr_wf_exp; auto | eapply Rsync_Rsync1; eauto]. }
    (* store misspec *)
    + exploit tgt_inv; eauto. intros (si & SRC & MI). inv MI. inv MATCH.
      exploit unused_prog_lookup; try eapply UNUSED1; eauto. intros U1.
      exploit unused_prog_lookup; try eapply UNUSED2; eauto. intros U2.
      exploit wf_prog_lookup; eauto. intros WFI. ss. des.
      exploit eval_masked_nat; try eapply H8; eauto. intros N'. ss. clarify.
      eapply bcc_step with (ds_s := []) (os_s := [OStore 0])
        (ic2 := S_Running ((pc+1, r, m), 0 !-> eval r e'; sb, true));
        [econs; eauto|tcomp|tcomp|ss; repeat econs|].
      econs. econs; eauto.
      eapply pc_sync_next_simple; eauto; ss; ii; ss.
    (* exit *)
    + exploit tgt_inv; eauto. intros (si & SRC & MI). inv MI. inv MATCH.
      eapply bcc_step with (ic2 := S_Term); [econs; eauto|tcomp|tcomp|ss; econs|econs].
  (* procedure entry - ctarget *)
  - inv TGT; rewrite CT1 in *; clarify.
    eapply bcc_stay; [destruct ct; tcomp|destruct ct; tcomp|].
    eapply match_cfgs_ext_ct2; eauto.
    exploit head_call_target; eauto. i. des; clarify; eauto.
  (* procedure entry - msf update *)
  - inv TGT; rewrite CT2 in *; clarify.
    eapply bcc_stay; [tcomp|tcomp|].
    econs. econs; eauto.
    + unfold pc_sync. simpl. rewrite nth_error_map. rewrite CT. destruct blk.
      { inv WFP. rewrite Forall_forall in H0. eapply nth_error_In in CT.
        eapply H0 in CT. red in CT. des; ss. }
      simpl. eauto.
    + eapply Rsync1_Rsync.
      * eapply Rsync1_upd_tgt; eauto.
      * rewrite t_update_eq. eauto.
  (* call *)
  - inv TGT; rewrite TCALL in *; clarify.
    + match goal with H: to_fp (eval r' _) = Some _ |- _ => rename H into TFP end.
      match goal with H: r' ! sp = N _ |- _ => rename H into RSP end.
      exploit unused_prog_lookup; try eapply UNUSED1; eauto. intros U1.
      exploit unused_prog_lookup; try eapply UNUSED2; eauto. intros U2.
      exploit wf_prog_lookup; eauto. intros WFI. ss.
      dup REG. destruct REG0 as [REGX MSF].
      assert (EV': eval r' fp = FP l).
      { simpl in TFP. rewrite MSF in TFP. ss. unfold to_fp in TFP. des_ifs. }
      exploit (eval_regs_eq p r r' fp);
        [eauto|eauto|apply wf_expr_wf_exp; auto|eapply Rsync_Rsync1; eauto|].
      rewrite EV'. intros VFP.
      exploit val_match_fp_inv; eauto. intros (l_src & EV & VML).
      exploit Rsync1_sp; [eapply Rsync_Rsync1; eauto|]. rewrite RSP. intros VSP.
      eapply val_match_n_inv in VSP.
      assert (CTD: (uslh_prog p)[[pc'0]] = Some <{{ ctarget }}> \/ (uslh_prog p)[[pc'0]] <> Some <{{ ctarget }}>).
      { destruct ((uslh_prog p)[[pc'0]]) as [ [] | ]; try (right; ii; clarify; fail); auto. }
      destruct CTD as [CTD|CTD].
      * exploit ctarget_src; eauto. intros (l0 & blk & PC0 & BLK). subst pc'0.
        assert (MSEQ: ((l0 =? fst l_src) && (0 =? snd l_src))%nat = ((l0 =? fst l) && (0 =? snd l))%nat)
          by (eapply val_match_fp_entry; eauto).
        eapply bcc_step with (ds_s := [DCall (l0, 0)]) (os_s := [OCall l_src sp_val])
          (ic2 := S_Running (((l0, 0), sp !-> N (S sp_val); r, upd_mem (S sp_val) m (FP (pc + 1))), S sp_val !-> FP (pc + 1); sb,
                       negb ((l0 =? fst l) && (0 =? snd l))%nat)).
        { eapply ISMI_Call; eauto.
          - destruct MSC as [_ TOP]. rewrite TOP. assumption.
          - rewrite EV. ss.
          - ss. rewrite MSEQ. auto. }
        { tcomp. }
        { tcomp. }
        { ss. repeat econs; ss. }
        { eapply match_cfgs_ext_ct1;
            [eauto|eauto
            |eapply Rsync1_upd; [|ss]; eapply Rsync1_mono; [eapply Rsync_Rsync1; eauto|]; i; clarify
            |eapply Msync_upd; eauto; eapply val_match_ret_addr; eauto|].
          simpl. rewrite t_update_neq by discriminate. rewrite MS.
          rewrite t_update_neq by discriminate. simpl. rewrite MSF. simpl. rewrite EV'.
          destruct l as [a b]. ss. rewrite (Nat.eqb_sym a l0).
          destruct (l0 =? a)%nat; destruct b; ss. }
      * eapply bcc_step with (ds_s := [DCall pc'0]) (os_s := [OCall l_src sp_val]) (ic2 := S_Fault).
        { eapply ISMI_Call_F; eauto.
          - rewrite EV. ss.
          - i. destruct blk as [b0 bb]. destruct bb; auto. right. ii. destruct pc'0; ss. subst.
            eapply CTD. eapply ctarget_exists; eauto. }
        { tcomp. }
        { tcomp. }
        { ss. repeat econs; ss. }
        { econs. auto. }
    + match goal with H: to_fp (eval r' _) = Some _ |- _ => rename H into TFP end.
      match goal with H: r' ! sp = N _ |- _ => rename H into RSP end.
      dup REG. destruct REG0 as [REGX MSF].
      assert (L00: l = (0, 0)).
      { simpl in TFP. rewrite MSF in TFP. ss. clarify. }
      subst l.
      exploit Rsync1_sp; [eapply Rsync_Rsync1; eauto|]. rewrite RSP. intros VSP.
      eapply val_match_n_inv in VSP.
      assert (CTD: (uslh_prog p)[[pc'0]] = Some <{{ ctarget }}> \/ (uslh_prog p)[[pc'0]] <> Some <{{ ctarget }}>).
      { destruct ((uslh_prog p)[[pc'0]]) as [ [] | ]; try (right; ii; clarify; fail); auto. }
      destruct CTD as [CTD|CTD].
      * exploit ctarget_src; eauto. intros (l0 & blk & PC0 & BLK). subst pc'0.
        eapply bcc_step with (ds_s := [DCall (l0, 0)]) (os_s := [OCall (0, 0) sp_val])
          (ic2 := S_Running (((l0, 0), sp !-> N (S sp_val); r, m), S sp_val !-> FP (pc + 1); sb, true)).
        { eapply ISMI_Call_Misspec; eauto. }
        { tcomp. }
        { tcomp. }
        { ss. repeat econs; ss. }
        { eapply match_cfgs_ext_ct1;
            [eauto|eauto|eapply Rsync1_upd; [|ss]; eapply Rsync_Rsync1; eauto|eauto|].
          simpl. rewrite t_update_neq by discriminate. rewrite MS.
          rewrite t_update_neq by discriminate. simpl. rewrite MSF. simpl. des_ifs. }
      * eapply bcc_step with (ds_s := [DCall pc'0]) (os_s := [OCall (0, 0) sp_val]) (ic2 := S_Fault).
        { eapply ISMI_Call_F; eauto.
          i. destruct blk as [b0 bb]. destruct bb; auto. right. ii. destruct pc'0; ss. subst.
          eapply CTD. eapply ctarget_exists; eauto. }
        { tcomp. }
        { tcomp. }
        { ss. repeat econs; ss. }
        { econs. auto. }
  (* call - fault *)
  - inv TGT; clarify.
    eapply bcc_stay; [tcomp|tcomp|econs].
  (* branch true - msf update *)
  - inv TGT; rewrite TO in *; clarify.
    eapply bcc_stay; [tcomp|tcomp|].
    eapply match_cfgs_ext_br_true2; eauto.
    eapply Rsync1_Rsync.
    + eapply Rsync1_upd_tgt; eauto.
    + rewrite t_update_eq. eauto.
  (* branch true - jump *)
  - inv TGT; rewrite BT2 in *; clarify.
    destruct (l' <? Datatypes.length p)%nat eqn:NEWB;
      (eapply bcc_stay; [tcomp|tcomp|]).
    all: econs; econs; eauto.
    all: exploit wf_prog_lookup; try eapply BR; eauto; intros WFI; simpl in WFI;
      destruct WFI as [_ WFL].
    all: unfold wf_lbl in WFL; des_ifs; eapply pc_sync_entry; eauto.
  (* branch false - msf update *)
  - inv TGT; rewrite TO in *; clarify.
    exploit tgt_inv; try eapply FROM; eauto. intros (si & SRC & MI).
    inv MI; [inv MATCH|]. clarify.
    eapply bcc_stay; [tcomp|tcomp|].
    econs. econs; eauto.
    + rewrite (pc_sync_next' _ _ _ _ WFP SYNC SRC (fun H => H)).
      destruct pc'. ss. rewrite <- add_assoc. reflexivity.
    + eapply Rsync1_Rsync.
      * eapply Rsync1_upd_tgt; eauto.
      * rewrite t_update_eq. eauto.
  - exploit src_inv; try eapply RET; eauto. intros (ti & TI & MI).
    inv MI; [inv SIMPL|]. rewrite SYNC in PC. clarify.
    dup REG. destruct REG0 as [REGX MSF].
    exploit Rsync1_sp; [eapply Rsync_Rsync1; eauto|]. rewrite SP. intros VSP.
    inv TGT; rewrite NXT1 in *; clarify.
    + match goal with H: to_nat (eval r' _) = Some _ |- _ => rename H into TN end.
      simpl in TN. destruct (r' ! sp) eqn:RSP; ss. clarify.
      eapply bcc_stay; [tcomp|tcomp|].
      eapply match_cfgs_ext_ret2; eauto.
      { eapply Msync_upd_same; eauto. simpl. rewrite MSF. ss. eapply CALLEE; eauto. }
      { i; clarify. }
    + match goal with H: to_nat (eval r' _) = Some _ |- _ => rename H into TN end.
      simpl in TN. destruct (r' ! sp) eqn:RSP; ss. clarify.
      eapply bcc_stay; [tcomp|tcomp|].
      eapply match_cfgs_ext_ret2; eauto.
      i. rewrite t_update_eq. simpl. rewrite MSF. ss.
  - exploit src_inv; try eapply RET; eauto. intros (ti & TI & MI).
    inv MI; [inv SIMPL|]. rewrite SYNC in PC. clarify.
    dup REG. destruct REG0 as [REGX MSF].
    exploit Rsync1_sp; [eapply Rsync_Rsync1; eauto|]. rewrite SP. intros VSP.
    inv TGT; rewrite NXT2 in *; clarify.
    + match goal with H: to_nat (eval r' _) = Some _ |- _ => rename H into TN end.
      simpl in TN. destruct (r' ! sp) eqn:RSP; ss. clarify.
      eapply bcc_stay; [tcomp|tcomp|].
      eapply match_cfgs_ext_ret3;
        [eauto|eauto| |eauto|eauto|ss; rewrite t_update_eq; auto].
      eapply Rsync1_Rsync.
      * eapply Rsync1_upd_tgt; [eapply Rsync_Rsync1; eauto|]. auto.
      * rewrite t_update_neq; eauto. ii; clarify.
    + match goal with H: to_nat (eval r' _) = Some _ |- _ => rename H into TN end.
      simpl in TN. destruct (r' ! sp) eqn:RSP; ss. clarify.
      eapply bcc_stay; [tcomp|tcomp|].
      eapply match_cfgs_ext_ret3;
        [eauto|eauto| |eauto|eauto|ss; rewrite t_update_eq; split; auto].
      eapply Rsync1_Rsync.
      * eapply Rsync1_upd_tgt; [eapply Rsync_Rsync1; eauto|]. auto.
      * rewrite t_update_neq; eauto. ii; clarify.
  - exploit src_inv; try eapply RET; eauto. intros (ti & TI & MI).
    inv MI; [inv SIMPL|]. rewrite SYNC in PC. clarify.
    dup REG. destruct REG0 as [REGX MSF].
    exploit Rsync1_sp; [eapply Rsync_Rsync1; eauto|]. rewrite SP. intros VSP.
    inv TGT; rewrite NXT3 in *; clarify.
    + match goal with H: wf_ret (uslh_prog p) _ |- _ => rename H into WFR end.
      match goal with H: r' ! sp = N _ |- _ => rename H into RSP end.
      match goal with H: nth_error (memory m') _ = Some (FP _) |- _ => rename H into NTH end.
      rewrite RSP in VSP. simpl in VSP. subst sp_val.
      rewrite NTH in CALLEE. injection CALLEE as CALLEE.
      exploit Msync_nth; eauto. intros (v & NTHS & VMR).
      exploit val_match_fp_inv; eauto. intros (ra & ? & VRA). subst v.
      exploit wf_ret_uslh_src; eauto. intros (o_src & WFRS & RS & PCS & TOS & GE2).
      dup WFRS. destruct WFRS0 as [_ [e [CALLSRC _] ] ].
      destruct pc'' as [lt ot]. simpl in RS, PCS, TOS, GE2, CALLSRC.
      assert (exists o', ot = o' + 2) as [o' ->] by (exists (ot - 2); lia).
      replace (o' + 2 - 2) with o' in PCS by lia.
      assert (VR: val_match p (FP (lt, S o_src)) (FP (lt, o' + 2))) by (ss; auto).
      assert (MSEQ: ((fst ra =? lt) && (snd ra =? S o_src))%nat = ((fst pc'0 =? lt) && (snd pc'0 =? o' + 2))%nat)
        by (exact (val_match_fp_eqb p ra pc'0 (lt, S o_src) (lt, o' + 2) VRA VR)).
      eapply bcc_step with (ds_s := [DRet (Some (lt, S o_src))]) (os_s := [ORet ra spv])
        (ic2 := S_Running (((lt, S o_src), sp !-> N (spv - 1); r, m), sb, negb ((fst pc'0 =? lt) && (snd pc'0 =? o' + 2))%nat)).
      { eapply ISMI_Ret_Dir; eauto.
        - eapply ideal_safe_ret_bound; eauto.
        - ss. rewrite MSEQ. auto. }
      { tcomp. rewrite (ret_unsync_ret_sync p (lt, S o_src) (lt, o' + 2) RS). reflexivity. }
      { tcomp. }
      { ss. repeat econs; ss. }
      { eapply match_cfgs_ext_ret4 with (e := e);
          [replace (S o_src - 1) with o_src by lia; exact PCS|exact CALLSRC|lia|exact TOS| |eauto| ].
        - eapply Rsync1_upd; [|ss]. eapply Rsync1_mono; [eapply Rsync_Rsync1; eauto|]. i; clarify.
        - simpl. rewrite t_update_neq by discriminate. rewrite <- CALLEE.
          rewrite t_update_neq by discriminate. rewrite MSF. ss.
          destruct ((fst pc'0 =? lt) && (snd pc'0 =? o' + 2))%nat eqn:E; ss. }
    + match goal with H: r' ! sp = N _ |- _ => rename H into RSP end.
      match goal with H: nth_error (memory m') _ = Some (FP _) |- _ => rename H into NTH end.
      rewrite RSP in VSP. simpl in VSP. subst sp_val.
      rewrite NTH in CALLEE. injection CALLEE as CALLEE.
      exploit Msync_nth; eauto. intros (v & NTHS & VMR).
      exploit val_match_fp_inv; eauto. intros (ra & ? & VRA). subst v.
      assert (VRA' := VRA).
      destruct ra as [la oa]. destruct oa as [|k].
      * unfold val_match in VRA. destruct pc'0 as [la' oa']. cbn [Nat.eqb] in VRA.
        destruct VRA as [EQL EQO]. subst la' oa'.
        destruct (nth_error p la) as [ [blk [|] ] | ] eqn:BLK.
        { eapply bcc_step with (ds_s := [DRet None]) (os_s := [ORet (la, 0) spv])
            (ic2 := S_Running (((la, 0), sp !-> N (spv - 1); r, m), sb, false)).
          { eapply ISMI_Ret_Step; eauto. eapply ideal_safe_ret_bound; eauto. }
          { tcomp. }
          { tcomp. }
          { ss. repeat econs; ss. }
          { eapply match_cfgs_ext_ct1; [eauto|eapply ctarget_exists; eauto| |eauto| ].
            - eapply Rsync1_upd; [|ss]. eapply Rsync_Rsync1; eauto.
            - simpl. rewrite t_update_neq by discriminate. rewrite <- CALLEE.
              rewrite t_update_neq by discriminate. rewrite MSF. ss.
              rewrite! Nat.eqb_refl. ss. } }
        { eapply bcc_step with (ds_s := [DRet None]) (os_s := [ORet (la, 0) spv])
            (ic2 := S_Running (((la, 0), sp !-> N (spv - 1); r, m), sb, false)).
          { eapply ISMI_Ret_Step; eauto. eapply ideal_safe_ret_bound; eauto. }
          { tcomp. }
          { tcomp. }
          { ss. repeat econs; ss. }
          { econs. econs; eauto.
            - eapply pc_sync_entry; eauto.
            - eapply Rsync1_Rsync.
              + eapply Rsync1_upd; [|ss]. eapply Rsync_Rsync1; eauto.
              + rewrite! t_update_neq by discriminate. auto. } }
        { exfalso. exploit ideal_safe_ret_target; eauto.
          intros (inst&CONTRA). unfold fetch in CONTRA.
          simpl in CONTRA. rewrite BLK in CONTRA.
          discriminate. }
      * destruct pc'0 as [la0 oa0]. unfold val_match in VRA. cbn [Nat.eqb] in VRA.
        exploit ret_sync_inv; eauto. intros (e & la' & ok & CALLK & PCK & EQ).
        injection EQ as -> ->.
        exploit src_inv; try eapply CALLK; eauto. intros (ti2 & TI2 & MI2).
        inv MI2; [inv SIMPL|]. rewrite SYNC0 in PCK. injection PCK as PCK. subst tpc.
        eapply bcc_step with (ds_s := [DRet None]) (os_s := [ORet (la, S k) spv])
          (ic2 := S_Running (((la, S k), sp !-> N (spv - 1); r, m), sb, false)).
        { eapply ISMI_Ret_Step; eauto. eapply ideal_safe_ret_bound; eauto. }
        { tcomp. }
        { tcomp. }
        { ss. repeat econs; ss. }
        { eapply match_cfgs_ext_ret4 with (e := e);
            [replace (S k - 1) with k by lia; exact SYNC0
            |replace (S k - 1) with k by lia; exact CALLK|lia|exact IN'| |eauto| ].
          - eapply Rsync1_upd; [|ss]. eapply Rsync_Rsync1; eauto.
          - simpl. rewrite t_update_neq by discriminate. rewrite <- CALLEE.
            rewrite t_update_neq by discriminate. rewrite MSF. ss.
            rewrite! Nat.eqb_refl. ss. }
    + match goal with H: wf_ret (uslh_prog p) _ |- _ => rename H into WFR end.
      match goal with H: r' ! sp = N _ |- _ => rename H into RSP end.
      match goal with H: sb' ! _ = FP _ |- _ => rename H into SBV end.
      rewrite RSP in VSP. simpl in VSP. subst sp_val.
      destruct CALLEE as [SLOT CALLEE]. rewrite SLOT in SBV. injection SBV as SBV. subst pc'0.
      exploit wf_ret_uslh_src; eauto. intros (o_src & WFRS & RS & PCS & TOS & GE2).
      dup WFRS. destruct WFRS0 as [_ [e [CALLSRC _] ] ].
      destruct pc'' as [lt ot]. simpl in RS, PCS, TOS, GE2, CALLSRC.
      assert (exists o', ot = o' + 2) as [o' ->] by (exists (ot - 2); lia).
      replace (o' + 2 - 2) with o' in PCS by lia.
      eapply bcc_step with (ds_s := [DRet (Some (lt, S o_src))]) (os_s := [ORet (0, 0) spv])
        (ic2 := S_Running (((lt, S o_src), sp !-> N (spv - 1); r, m), spv !-> FP (0, 0); sb, true)).
      { eapply ISMI_Ret_Misspec_Dir; eauto. }
      { tcomp. rewrite (ret_unsync_ret_sync p (lt, S o_src) (lt, o' + 2) RS). reflexivity. }
      { tcomp. }
      { ss. repeat econs; ss. }
      { eapply match_cfgs_ext_ret4 with (e := e);
          [replace (S o_src - 1) with o_src by lia; exact PCS|exact CALLSRC|lia|exact TOS| |eauto| ].
        - eapply Rsync1_upd; [|ss]. eapply Rsync_Rsync1; eauto.
        - simpl. rewrite t_update_neq by discriminate. rewrite CALLEE.
          rewrite t_update_neq by discriminate. rewrite MSF. ss. des_ifs. }
    + match goal with H: r' ! sp = N _ |- _ => rename H into RSP end.
      match goal with H: sb' ! _ = FP _ |- _ => rename H into SBV end.
      rewrite RSP in VSP. simpl in VSP. subst sp_val.
      destruct CALLEE as [SLOT CALLEE]. rewrite SLOT in SBV. injection SBV as SBV. subst pc'0.
      destruct (nth_error p 0) as [ [blk [|] ] | ] eqn:BLK0.
      * eapply bcc_step with (ds_s := [DRet None]) (os_s := [ORet (0, 0) spv])
          (ic2 := S_Running (((0, 0), sp !-> N (spv - 1); r, m), spv !-> FP (0, 0); sb, true)).
        { eapply ISMI_Ret_Misspec_Step; eauto. }
        { tcomp. }
        { tcomp. }
        { ss. repeat econs; ss. }
        { eapply match_cfgs_ext_ct1; [eauto|eapply ctarget_exists; eauto| |eauto| ].
          - eapply Rsync1_upd; [|ss]. eapply Rsync_Rsync1; eauto.
          - simpl. rewrite t_update_neq by discriminate. rewrite CALLEE.
            rewrite t_update_neq by discriminate. rewrite MSF. ss. }
      * eapply bcc_step with (ds_s := [DRet None]) (os_s := [ORet (0, 0) spv])
          (ic2 := S_Running (((0, 0), sp !-> N (spv - 1); r, m), spv !-> FP (0, 0); sb, true)).
        { eapply ISMI_Ret_Misspec_Step; eauto. }
        { tcomp. }
        { tcomp. }
        { ss. repeat econs; ss. }
        { econs. econs; eauto.
          - eapply pc_sync_entry; eauto.
          - eapply Rsync1_Rsync.
            + eapply Rsync1_upd; [|ss]. eapply Rsync_Rsync1; eauto.
            + rewrite! t_update_neq by discriminate. auto. }
      * exfalso. destruct WFP as [NEP _]. red in NEP.
        eapply nth_error_None in BLK0. lia.
  (* after return *)
  - inv TGT; rewrite TO in *; clarify.
    eapply bcc_stay; [tcomp|tcomp|].
    econs. econs; eauto.
    + replace (l, o) with ((l, o - 1) + 1) by (ss; f_equal; lia).
      rewrite (pc_sync_next' _ _ _ _ WFP PC FROM (fun H => H)).
      ss. rewrite <- add_assoc. reflexivity.
    + eapply Rsync1_Rsync.
      * eapply Rsync1_upd_tgt; eauto.
      * rewrite t_update_eq. eauto.
Qed.

(* The glue lemma to connect ultimate_slh_bcc_single to the leakage transformers framework *)
Lemma uslh_safe_step_preserves_sim (p: prog) (isp: nat)
  (NCT: no_ct_prog p)
  (WFP: wf_prog p)
  (UNUSED1: unused_prog msf p)
  (UNUSED2: unused_prog callee p)
  (UNUSED3: unused_prog sp p) :
  safe_step_preserves_sim (Ls := IdealLang) (Lt := SpecLang) (hist := uslh_hist p (uslh_prog p) isp)
    p (uslh_prog p) (uslh_sim p) uslh_Tdir uslh_Tobs.
Proof.
  intros ds h os_t s t t' SIM SAFE STEP.
  destruct (ultimate_slh_bcc_single p s t t' ds os_t h NCT WFP UNUSED1 UNUSED2 UNUSED3 SIM STEP SAFE)
    as (os' & ic2 & RUN & SIM' & OBS).
  exists ic2, os'. split; [exact RUN|]. split; [exact OBS|exact SIM'].
Qed.

Lemma spec_step_shape p pc r1 m1 sb1 ct ms1 r2 m2 sb2 ms2 st1' st2' ds1 ds2 os1 os2 :
  p |- <(( S_Running ((pc, r1, m1), sb1, ct, ms1) ))> -->_ds1^^os1 <(( st1' ))> ->
  p |- <(( S_Running ((pc, r2, m2), sb2, ct, ms2) ))> -->_ds2^^os2 <(( st2' ))> ->
  Datatypes.length ds1 = Datatypes.length ds2 /\ Datatypes.length os1 = Datatypes.length os2.
Proof.
  intros H1 H2.
  inversion H1; inversion H2; subst; try (split; reflexivity); congruence.
Qed.

Lemma ultimate_slh_safe_bw_simulation (isp : nat) :
  has_safe_bw_simulation uslh_compiler (uslh_sync isp).
Proof.
  intros p_s p_t (-> & WFP & NCT & UNUSED1 & UNUSED2 & UNUSED3 & FST).
  (* Witnesses: the history tracks the target pc, ct flag and sp (starting from isp);
     the transformers translate directions/observations by the target instruction kind. *)
  exists (uslh_hist p_s (uslh_prog p_s) isp), (uslh_sim p_s), uslh_Tdir, uslh_Tobs.
  splits.
  (* initial_sim: both runs start at (0,0); the target is at the ctarget of the entry
     procedure (block 0 is a procedure by first_blk_call), which is match_cfgs_ext_ct1. *)
  - intros [r m] [r' m'] (REG & MSC & SPV & CALLEEV). simpl in REG, MSC, SPV.
    red in FST. destruct (nth_error p_s 0) as [ [blk [|] ] | ] eqn:BLK; try contradiction.
    (* The synced target sp equals the source sp, i.e. isp. *)
    assert (VSP: r' ! sp = N isp).
    { pose proof (Rsync1_sp p_s r r' false REG) as V. rewrite SPV in V.
      destruct (r' ! sp); ss; subst; auto. }
    unfold uslh_sim. simpl. split.
    (* The initial history is exactly tctrl of the initial target state. *)
    + unfold tctrl. rewrite !t_update_neq by discriminate. rewrite VSP. reflexivity.
    + eapply match_cfgs_ext_ct1; [exact BLK|eapply ctarget_exists; eauto| |exact MSC|].
      (* spec_initial only sets the target-only registers msf and callee. *)
      * eapply Rsync1_upd_tgt; [eapply Rsync1_upd_tgt; [exact REG|left; reflexivity]|right; reflexivity].
      (* callee = &(0,0), so the entry check keeps msf = 0. *)
      * reflexivity.
  (* The step diagram is the single-step backward compiler correctness lemma. *)
  - exact (uslh_safe_step_preserves_sim p_s isp NCT WFP UNUSED1 UNUSED2 UNUSED3).
  (* step_shape_det: the same history means the same target pc and ct flag, and a
     speculative step's numbers of directions and observations depend only on those. *)
  - intros h s1 s2 t1 t2 t1' t2' ds1 ds2 os1 os2 [H1 _] [H2 _] ST1 ST2 PRE.
    rewrite H1 in H2.
    destruct t1 as [ [ [ [ [ [pc1 r1] m1] sb1] ct1] ms1] | | | ]; try (inv ST1; fail).
    destruct t2 as [ [ [ [ [ [pc2 r2] m2] sb2] ct2] ms2] | | | ]; try (inv ST2; fail);
      unfold tctrl in H2; try discriminate.
    inversion H2; subst.
    destruct (spec_step_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ST1 ST2) as [LD LO].
    (* Comparable directive chunks of equal length are equal. *)
    split; [apply prefix_same_length; assumption | exact LO].
  (* Tobs_length_inj: Tobs prepends the masking observations (fixed by the history)
     to an element-wise translation of the source observations. *)
  - intros [h|] ds os1 os2 LEN; unfold uslh_Tobs in LEN; [|exact LEN].
    rewrite !length_app, !length_map in LEN. apply Nat.add_cancel_l in LEN. exact LEN.
Qed.

Definition seq_same_obs p pc r1 r2 m1 m2 : Prop :=
  forall os1 os2 c1 c2,
  p |- <(( S_Running (pc, r1, m1) ))> -->*^ os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2) ))> -->*^ os2 <(( c2 ))> ->
  (Utils.prefix os1 os2) \/ (Utils.prefix os2 os1).

Definition ideal_same_obs p pc r1 r2 m1 m2 sb1 sb2 : Prop :=
  forall ds os1 os2 c1 c2,
  p |- <(( S_Running (pc, r1, m1, sb1, false) ))> -->i*_ds^^os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, sb2, false) ))> -->i*_ds^^ os2 <(( c2 ))> ->
  (Utils.prefix os1 os2) \/ (Utils.prefix os2 os1).

Require Import Stdlib.Program.Equality.

Lemma multi_seq_app p c1 os1 c2 os2 c3:
  p |- <(( c1 ))> -->*^ os1 <(( c2 ))> ->
  p |- <(( c2 ))> -->*^ os2 <(( c3 ))> ->
  p |- <(( c1 ))> -->*^ os1 ++ os2 <(( c3 ))>.
Proof. intros H1 H2. exact (sem_cat (L := SeqLang) H1 H2). Qed.

Lemma multi_seq_rcons p c1 os1 c2 os2 c3:
  p |- <(( c1 ))> -->*^ os1 <(( c2 ))> ->
  p |- <(( c2 ))> -->^ os2 <(( c3 ))> ->
  p |- <(( c1 ))> -->*^ os1 ++ os2 <(( c3 ))>.
Proof.
  intros Hmulti Hstep.
  eapply multi_seq_app; [exact Hmulti|]. exact (sem_step1 (L := SeqLang) (ds := []) Hstep).
Qed.

Lemma ideal_step_one_or_no_directive p pc r m sb b ds os c:
  p |- <(( S_Running (pc, r, m, sb, b) ))> -->i_ ds ^^ os <(( c ))> ->
  ds = [] \/ exists d, ds = [d].
Proof.
  inversion 1; subst; try now left.
  all: right; eexists; reflexivity.
Qed.

Lemma ideal_pc_determines_dir_obs_count p pc r1 r2 m1 m2 sb1 sb2 b ds1 ds2 os1 os2 c1 c2:
  p |- <(( S_Running (pc, r1, m1, sb1, b) ))> -->i_ ds1 ^^ os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, sb2, b) ))> -->i_ ds2 ^^ os2 <(( c2 ))> ->
  Datatypes.length ds1 = Datatypes.length ds2 /\ Datatypes.length os1 = Datatypes.length os2.
Proof.
  inversion 1; inversion 1; subst; split; try reflexivity.
  all: try congruence.
Qed.

Lemma seq_pc_determines_obs_count p pc r1 r2 m1 m2 os1 os2 c1 c2:
  p |- <(( S_Running (pc, r1, m1) ))> -->^ os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2) ))> -->^ os2 <(( c2 ))> ->
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

Lemma seq_steps_preserves_seq_same_obs p pc r1 r2 m1 m2 os1 os2 pc' r1' r2' m1' m2':
  seq_same_obs p pc r1 r2 m1 m2 ->
  p |- <(( S_Running (pc, r1, m1) ))> -->^ os1 <(( S_Running (pc', r1', m1') ))> ->
  p |- <(( S_Running (pc, r2, m2) ))> -->^ os2 <(( S_Running (pc', r2', m2') ))> ->
  seq_same_obs p pc' r1' r2' m1' m2'.
Proof.
  intros Hseq_same_obs Hstep1 Hstep2.
  unfold seq_same_obs.
  intros os1' os2' c1 c2 Hmulti1 Hmulti2.
  pose proof (multi_seq_cons _ _ _ _ _ _ Hstep1 Hmulti1) as H1.
  pose proof (multi_seq_cons _ _ _ _ _ _ Hstep2 Hmulti2) as H2.
  specialize (Hseq_same_obs _ _ _ _ H1 H2).
  destruct Hseq_same_obs as [ [or1 H] | [or2 H] ].
  - left. exists or1. rewrite <- app_assoc in H.
    eapply app_eq_len_tail_eq. 1: eassumption.
    eapply seq_pc_determines_obs_count; eassumption.
  - right. exists or2. rewrite <- app_assoc in H.
    eapply app_eq_len_tail_eq. 1: eassumption.
    eapply seq_pc_determines_obs_count; eassumption.
Qed.

Lemma ideal_nonspec_seq p pc r m sb ds os pc' r' m' sb':
  p |- <(( S_Running (pc, r, m, sb, false) ))> -->i_ ds ^^ os <(( S_Running (pc', r', m', sb', false) ))> ->
  p |- <(( S_Running (pc, r, m) ))> -->^ os <(( S_Running (pc', r', m') ))>.
Proof.
  inversion 1; subst; try (econstructor; eassumption).
  - eapply SSMI_Branch; [eassumption|eassumption|].
    match goal with H: false = (false || negb (Bool.eqb (not_zero ?n) ?b))%bool |- _ =>
      simpl in H; destruct (not_zero n), b; simpl in H; congruence end.
  - match goal with H: false = negb _ |- _ =>
      symmetry in H; apply negb_false_iff in H; apply andb_prop in H as [E1 E2] end.
    apply Nat.eqb_eq in E1, E2. destruct pc' as [a b], l as [a' b']; simpl in E1, E2; subst.
    eapply SSMI_Call; eauto.
    unfold wf_label. simpl in *.
    match goal with H: nth_error p a' = Some ?blk |- _ => rewrite H; destruct blk as [? bb]; simpl in *; subst; reflexivity end.
  - match goal with H: false = negb _ |- _ =>
      symmetry in H; apply negb_false_iff in H; apply andb_prop in H as [E1 E2] end.
    apply Nat.eqb_eq in E1, E2. destruct pc' as [a b], pc'0 as [a' b']; simpl in E1, E2; subst.
    eapply SSMI_Ret; eauto.
Qed.

Lemma multi_ideal_ms_monotonic {p pc r m sb ms ds os pc' r' m' sb'}:
  p |- <(( S_Running (pc, r, m, sb, ms) ))> -->i*_ ds ^^ os <(( S_Running (pc', r', m', sb', false) ))> ->
  ms = false.
Proof.
  intro Hmulti.
  remember (S_Running (pc, r, m, sb, ms)) as st eqn:Est.
  remember (S_Running (pc', r', m', sb', false)) as st' eqn:Est'.
  revert pc r m sb ms Est.
  induction Hmulti as [st0 | st0 st1 st2 ds1 os1 ds2 os2 STEP REST IH]; intros pc0 r0 m0 sb0 ms0 Est; subst.
  - inv Est. reflexivity.
  - destruct st1 as [ [ [ [ [pc1 r1] m1] sb1] ms1] | | | ];
      [|inversion REST as [|? ? ? ? ? ? ? STEPF ?]; subst; inversion STEPF..].
    specialize (IH ltac:(reflexivity) pc1 r1 m1 sb1 ms1 ltac:(reflexivity)). subst ms1.
    inversion STEP; subst; try reflexivity.
    match goal with H: false = (?b || _)%bool |- _ => symmetry in H; apply orb_false_elim in H; tauto end.
Qed.

Lemma multi_ideal_nonspec_seq p pc r m sb ds os pc' r' m' sb':
  p |- <(( S_Running (pc, r, m, sb, false) ))> -->i*_ ds ^^ os <(( S_Running (pc', r', m', sb', false) ))> ->
  p |- <(( S_Running (pc, r, m) ))> -->*^ os <(( S_Running (pc', r', m') ))>.
Proof.
  intro H.
  remember (S_Running (pc, r, m, sb, false)) as st eqn:Est.
  remember (S_Running (pc', r', m', sb', false)) as st' eqn:Est'.
  revert pc r m sb Est.
  induction H as [st0 | st0 st1 st2 ds1 os1 ds2 os2 STEP REST IH]; intros pc0 r0 m0 sb0 Est; subst.
  - inv Est. apply (sem_refl (L := SeqLang)).
  - destruct st1 as [ [ [ [ [pc1 r1] m1] sb1] ms1] | | | ];
      [|inversion REST as [|? ? ? ? ? ? ? STEPF ?]; subst; inversion STEPF..].
    pose proof (multi_ideal_ms_monotonic REST). subst ms1.
    eapply multi_seq_cons.
    + eapply ideal_nonspec_seq. exact STEP.
    + eapply IH; reflexivity.
Qed.

Lemma ideal_nonspec_step_preserves_seq_same_obs p pc r1 r2 m1 m2 sb1 sb2 ds os1 os2 pc' r1' r2' m1' m2' sb1' sb2':
  seq_same_obs p pc r1 r2 m1 m2 ->
  p |- <(( S_Running (pc, r1, m1, sb1, false ) ))> -->i_ ds ^^ os1 <(( S_Running (pc', r1', m1', sb1', false) ))> ->
  p |- <(( S_Running (pc, r2, m2, sb2, false ) ))> -->i_ ds ^^ os2 <(( S_Running (pc', r2', m2', sb2', false) ))> ->
  seq_same_obs p pc' r1' r2' m1' m2'.
Proof.
  intros Hsso Hst1 Hst2.
  eapply seq_steps_preserves_seq_same_obs. 1: eassumption.
  all: eapply ideal_nonspec_seq; eassumption.
Qed.

Lemma multi_ideal_nonspec_step_preserves_seq_same_obs p pc r1 r2 m1 m2 sb1 sb2 ds os1 os2 pc' r1' r2' m1' m2' sb1' sb2':
  seq_same_obs p pc r1 r2 m1 m2 ->
  p |- <(( S_Running (pc, r1, m1, sb1, false ) ))> -->i*_ ds ^^ os1 <(( S_Running (pc', r1', m1', sb1', false) ))> ->
  p |- <(( S_Running (pc, r2, m2, sb2, false ) ))> -->i*_ ds ^^ os2 <(( S_Running (pc', r2', m2', sb2', false) ))> ->
  Datatypes.length os1 = Datatypes.length os2 ->
  seq_same_obs p pc' r1' r2' m1' m2'.
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

Lemma ideal_multi_no_dirs_run_or_term p pc r m sb b os ic:
  p |- <(( S_Running (pc, r, m, sb, b) ))> -->i*_ [] ^^ os <(( ic ))> ->
  exists pc' r' m' sb', p |- <(( S_Running (pc, r, m, sb, b) ))> -->i*_ [] ^^ os <(( S_Running (pc', r', m', sb', b) ))>
                 /\  (ic = S_Running (pc', r', m', sb', b) \/ ic = S_Term /\ p |- <(( S_Running (pc', r', m', sb', b) ))> -->i_ [] ^^ [] <(( S_Term ))>).
Proof.
  intros H.
  remember (@nil (SimDiagrams.directive (L := IdealLang))) as ds eqn:Hds.
  remember (S_Running (pc, r, m, sb, b)) as st eqn:Est.
  revert Hds pc r m sb Est.
  induction H as [st0 | st0 st1 st2 ds1 os1 ds2 os2 STEP REST IH]; intros Hds pc0 r0 m0 sb0 Est; subst.
  - exists pc0, r0, m0, sb0. split; [apply (sem_refl (L := IdealLang))|left; reflexivity].
  - apply app_eq_nil in Hds as [-> ->].
    destruct st1 as [ [ [ [ [pc1 r1] m1] sb1] ms1] | | | ].
    + assert (ms1 = b) by (inversion STEP; subst; reflexivity). subst ms1.
      destruct (IH ltac:(reflexivity) pc1 r1 m1 sb1 ltac:(reflexivity)) as (pc' & r' & m' & sb' & RUN & OUT).
      exists pc', r', m', sb'. split; [|exact OUT].
      exact (sem_step (L := IdealLang) STEP RUN).
    + inversion STEP.
    + inversion STEP.
    + inversion REST as [|? ? ? ? ? ? ? STEPF ?]; subst; [|inversion STEPF].
      assert (os1 = []) by (inversion STEP; reflexivity). subst os1.
      exists pc0, r0, m0, sb0. split; [apply (sem_refl (L := IdealLang))|right; split; [reflexivity|exact STEP] ].
Qed.

Lemma ideal_eval_multi_exec_split {p pc r1 r2 m1 m2 sb1 sb2 ds os1 os2 c1 c2}:
  seq_same_obs p pc r1 r2 m1 m2 ->
  sequential_safe (L := SeqLang) p (S_Running (pc, r1, m1)) ->
  sequential_safe (L := SeqLang) p (S_Running (pc, r2, m2)) ->
  r1 ! sp = r2 ! sp ->
  unused_prog sp p ->
  p |- <(( S_Running (pc, r1, m1, sb1, false) ))> -->i*_ ds ^^ os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, sb2, false) ))> -->i*_ ds ^^ os2 <(( c2 ))> ->
  exists pc1' pc2' r1' r2' m1' m2' sb1' sb2' ds' os1' os2',
    p |- <(( S_Running (pc, r1, m1, sb1, false) ))> -->i*_ ds' ^^ os1' <(( S_Running (pc1', r1', m1', sb1', false) ))> /\
    p |- <(( S_Running (pc, r2, m2, sb2, false) ))> -->i*_ ds' ^^ os2' <(( S_Running (pc2', r2', m2', sb2', false) ))> /\
   (ds' = ds /\ os1' = os1 /\ os2' = os2
    /\ (c1 = S_Running (pc1', r1', m1', sb1', false) \/ c1 = S_Term /\ p |- <(( S_Running (pc1', r1', m1', sb1', false) ))> -->i_ [] ^^ [] <(( S_Term ))>)
    /\ (c2 = S_Running (pc2', r2', m2', sb2', false) \/ c2 = S_Term /\ p |- <(( S_Running (pc2', r2', m2', sb2', false) ))> -->i_ [] ^^ [] <(( S_Term))>)
    \/ exists ds'' os1'' os2'',
       ds = ds' ++ ds'' /\ os1 = os1' ++ os1'' /\ os2 = os2' ++ os2'' /\ pc1' = pc2' /\ r1' ! sp = r2' ! sp /\ Datatypes.length os1' = Datatypes.length os2' /\
       (
        c1 = S_Fault /\ c2 = S_Fault /\ p |- <(( S_Running (pc1', r1', m1', sb1', false) ))> -->i_ ds'' ^^ os1'' <(( S_Fault ))> /\ p |- <(( S_Running (pc2', r2', m2', sb2', false) ))> -->i_ ds'' ^^os2'' <(( S_Fault))>
        \/
        exists pc'' r1'' r2'' m1'' m2'' sb1'' sb2'' d ds''' o1 os1''' o2 os2''',
        ds'' = d :: ds''' /\ os1'' = o1 ++ os1''' /\ os2'' = o2 ++ os2''' /\ r1'' ! sp = r2'' ! sp /\
        p |- <(( S_Running (pc1', r1', m1', sb1', false) ))> -->i_ [d] ^^ o1 <(( S_Running (pc'', r1'', m1'', sb1'', true) ))> /\ p |- <(( S_Running (pc'', r1'', m1'', sb1'', true) ))> -->i*_ ds''' ^^ os1''' <(( c1 ))> /\
        p |- <(( S_Running (pc2', r2', m2', sb2', false) ))> -->i_ [d] ^^ o2 <(( S_Running (pc'', r2'', m2'', sb2'', true) ))> /\ p |- <(( S_Running (pc'', r2'', m2'', sb2'', true) ))> -->i*_ ds''' ^^ os2''' <(( c2 ))>
       )
   ).
Proof.
  intros Hseq_same SAFE1 SAFE2 SPEQ UNUSED Hexec1 Hexec2.
  remember (S_Running (pc, r1, m1, sb1, false)) as st eqn:Est.
  revert pc r1 r2 m1 m2 sb1 sb2 os2 Hseq_same SAFE1 SAFE2 SPEQ Est Hexec2.
  induction Hexec1 as [st | st st' st'' ds1 os1a ds1' os1b STEP1 REST1 IH];
    intros pc r1 r2 m1 m2 sb1 sb2 os2 Hseq_same SAFE1 SAFE2 SPEQ Est Hexec2; subst.
  - exploit ideal_multi_no_dirs_run_or_term; [exact Hexec2|].
    intros (pc' & r' & m' & sb' & RUN2 & OUT2).
    exists pc, pc', r1, r', m1, m', sb1, sb', [], [], os2.
    split; [apply (sem_refl (L := IdealLang))|]. split; [exact RUN2|].
    left. splits; auto.
  - destruct (semI Hexec2) as [ (HDS & HOS & HC2) | (ds2 & os2a & st2' & ds2' & os2b & HDS & HOS & STEP2 & REST2) ].
    + apply app_eq_nil in HDS as [-> ->]. subst.
      pose proof (sem_step (L := IdealLang) STEP1 REST1) as RUN1.
      exploit ideal_multi_no_dirs_run_or_term; [exact RUN1|].
      intros (pc' & r' & m' & sb' & RUN1' & OUT1).
      exists pc', pc, r', r2, m', m2, sb', sb2, [], (os1a ++ os1b), [].
      split; [exact RUN1'|]. split; [apply (sem_refl (L := IdealLang))|].
      left. splits; auto.
    + subst.
      (* Both first steps consume the same directions. *)
      exploit ideal_pc_determines_dir_obs_count; [exact STEP1|exact STEP2|]. intros [LD LO].
      assert (ds1 = ds2) as <-.
      { destruct (app_eq_prefix HDS) as [hp|hp];
          [apply prefix_same_length; auto|symmetry; apply prefix_same_length; auto]. }
      apply app_inv_head in HDS. subst ds2'.
      (* Both first steps emit the same observations: they are those of the sequential
         steps (which exist by sequential safety), and these agree by seq_same_obs. *)
      destruct (SAFE1 [] [] _ (sem_refl (L := SeqLang) p _)) as (os1s & c1s & SS1).
      destruct (SAFE2 [] [] _ (sem_refl (L := SeqLang) p _)) as (os2s & c2s & SS2).
      assert (os1a = os1s) by (inversion STEP1; inversion SS1; subst; simpl in *; congruence).
      assert (os2a = os2s) by (inversion STEP2; inversion SS2; subst; simpl in *; congruence).
      subst os1s os2s.
      assert (OEQ: os1a = os2a).
      { destruct (Hseq_same _ _ _ _ (sem_step1 (L := SeqLang) (ds := []) SS1) (sem_step1 (L := SeqLang) (ds := []) SS2)) as [hp|hp];
          [apply prefix_same_length; [exact hp|exact LO]|symmetry; apply prefix_same_length; [exact hp|symmetry; exact LO] ]. }
      subst os2a.
      (* Hence both runs reach the same pc and misspeculation flag, keep sp equal,
         or both fault, or both terminate. *)
      assert (LOCK: (exists pc' r1' r2' m1' m2' sb1' sb2' ms', st' = S_Running (pc', r1', m1', sb1', ms')
                       /\ st2' = S_Running (pc', r2', m2', sb2', ms') /\ r1' ! sp = r2' ! sp)
                    \/ (st' = S_Fault /\ st2' = S_Fault) \/ (st' = S_Term /\ st2' = S_Term)).
      { clear - SPEQ UNUSED STEP1 STEP2.
        inversion STEP1; inversion STEP2; subst; simpl in *; try congruence.
        all: clarify.
        all: try (match goal with HF: forall blk, nth_error _ _ = Some blk -> _, H: nth_error _ _ = Some ?b |- _ =>
                 exfalso; destruct (HF _ H); congruence end).
        all: try match goal with H: not_zero ?a = not_zero ?b |- _ => rewrite H in * end.
        all: try (right; right; split; reflexivity); try (right; left; split; reflexivity).
        all: left; do 8 eexists; split; [reflexivity|split; [reflexivity|] ].
        all: try rewrite !t_update_eq; try reflexivity; try assumption.
        all: match goal with H: fetch _ _ = Some _ |- _ => pose proof (unused_prog_lookup _ _ _ _ UNUSED H) as U end.
        all: simpl in U; des; rewrite !t_update_neq by auto; assumption. }
      destruct LOCK as [ (pc' & r1' & r2' & m1' & m2' & sb1' & sb2' & ms' & -> & -> & SPEQ')
                       | [ [-> ->] | [-> ->] ] ].
      * destruct ms'.
        (* Both runs start misspeculating at this step. *)
        -- exists pc, pc, r1, r2, m1, m2, sb1, sb2, [], [], [].
           split; [apply (sem_refl (L := IdealLang))|]. split; [apply (sem_refl (L := IdealLang))|].
           right. exists (ds1 ++ ds1'), (os1a ++ os1b), (os1a ++ os2b). splits; auto.
           right.
           destruct (ideal_step_one_or_no_directive _ _ _ _ _ _ _ _ _ STEP1) as [-> | [d ->] ];
             [inversion STEP1|].
           exists pc', r1', r2', m1', m2', sb1', sb2', d, ds1', os1a, os1b, os1a, os2b. splits; auto.
        (* Both runs stay non-misspeculating: continue by induction. *)
        -- exploit (IH pc' r1' r2' m1' m2' sb1' sb2' os2b).
           ++ eapply ideal_nonspec_step_preserves_seq_same_obs; [exact Hseq_same|exact STEP1|exact STEP2].
           ++ exact (sequential_safe_step (L := SeqLang) (ds := []) SAFE1 (ideal_nonspec_seq _ _ _ _ _ _ _ _ _ _ _ STEP1)).
           ++ exact (sequential_safe_step (L := SeqLang) (ds := []) SAFE2 (ideal_nonspec_seq _ _ _ _ _ _ _ _ _ _ _ STEP2)).
           ++ exact SPEQ'.
           ++ reflexivity.
           ++ exact REST2.
           ++ intros (pc1' & pc2' & r1'' & r2'' & m1'' & m2'' & sb1'' & sb2'' & dsx & os1x & os2x & RUN1 & RUN2 & OUT).
              exists pc1', pc2', r1'', r2'', m1'', m2'', sb1'', sb2'', (ds1 ++ dsx), (os1a ++ os1x), (os1a ++ os2x).
              split; [exact (sem_step (L := IdealLang) STEP1 RUN1)|].
              split; [exact (sem_step (L := IdealLang) STEP2 RUN2)|].
              destruct OUT as [ (-> & -> & -> & C1 & C2) | (ds'' & os1'' & os2'' & -> & -> & -> & PC & SP & LEN & OUT) ].
              ** left. splits; auto.
              ** right. exists ds'', os1'', os2''.
                 splits; auto; try apply app_assoc.
                 rewrite !length_app, LEN. reflexivity.
      (* Both runs fault. *)
      * destruct (semI REST1) as [ HH | (? & ? & ? & ? & ? & _ & _ & STEPF & _) ]; [destruct HH as (? & ? & ?); subst|inversion STEPF].
        destruct (semI REST2) as [ HH | (? & ? & ? & ? & ? & _ & _ & STEPF & _) ]; [destruct HH as (? & ? & ?); subst|inversion STEPF].
        exists pc, pc, r1, r2, m1, m2, sb1, sb2, [], [], [].
        split; [apply (sem_refl (L := IdealLang))|]. split; [apply (sem_refl (L := IdealLang))|].
        right. exists ds1, os1a, os1a. splits; auto.
        all: simpl; apply app_nil_r.
      (* Both runs terminate. *)
      * destruct (semI REST1) as [ HH | (? & ? & ? & ? & ? & _ & _ & STEPF & _) ]; [destruct HH as (? & ? & ?); subst|inversion STEPF].
        destruct (semI REST2) as [ HH | (? & ? & ? & ? & ? & _ & _ & STEPF & _) ]; [destruct HH as (? & ? & ?); subst|inversion STEPF].
        assert (ds1 = [] /\ os1a = []) as [-> ->] by (inversion STEP1; split; reflexivity).
        exists pc, pc, r1, r2, m1, m2, sb1, sb2, [], [], [].
        split; [apply (sem_refl (L := IdealLang))|]. split; [apply (sem_refl (L := IdealLang))|].
        left. splits; auto.
Qed.

Lemma ideal_misspec_unwinding {p pc r1 r2 m1 m2 sb1 sb2 ds os1 os2 c1 c2}:
  r1 ! sp = r2 ! sp ->
  unused_prog sp p ->
  p |- <(( S_Running (pc, r1, m1, sb1, true) ))> -->i*_ ds ^^ os1 <(( c1 ))> ->
  p |- <(( S_Running (pc, r2, m2, sb2, true) ))> -->i*_ ds ^^ os2 <(( c2 ))> ->
  Utils.prefix os1 os2 \/ Utils.prefix os2 os1.
Proof.
  intros SPEQ UNUSED Hexec1 Hexec2.
  remember (S_Running (pc, r1, m1, sb1, true)) as st eqn:Est.
  revert pc r1 r2 m1 m2 sb1 sb2 os2 SPEQ Est Hexec2.
  induction Hexec1 as [st | st st' st'' ds1 os1a ds1' os1b STEP1 REST1 IH];
    intros pc r1 r2 m1 m2 sb1 sb2 os2 SPEQ Est Hexec2; subst.
  - left. apply prefix_nil.
  - destruct (semI Hexec2) as [ (HDS & HOS & HC2) | (ds2 & os2a & st2' & ds2' & os2b & HDS & HOS & STEP2 & REST2) ].
    + subst. right. apply prefix_nil.
    + subst.
      exploit ideal_pc_determines_dir_obs_count; [exact STEP1|exact STEP2|]. intros [LD LO].
      assert (ds1 = ds2) as <-.
      { destruct (app_eq_prefix HDS) as [hp|hp];
          [apply prefix_same_length; auto|symmetry; apply prefix_same_length; auto]. }
      apply app_inv_head in HDS. subst ds2'.
      (* While misspeculating, observations only depend on the pc and sp, which agree. *)
      assert (LOCK: os1a = os2a /\
                    ((exists pc' r1' r2' m1' m2' sb1' sb2', st' = S_Running (pc', r1', m1', sb1', true)
                       /\ st2' = S_Running (pc', r2', m2', sb2', true) /\ r1' ! sp = r2' ! sp)
                    \/ (st' = S_Fault /\ st2' = S_Fault) \/ (st' = S_Term /\ st2' = S_Term))).
      { clear - SPEQ UNUSED STEP1 STEP2.
        inversion STEP1; inversion STEP2; subst; simpl in *; try congruence.
        all: rewrite ?SPEQ in *.
        all: clarify.
        all: try (match goal with H: ?x = N ?a, H': ?x = N ?b |- _ => rewrite H in H'; injection H' as H'; subst end).
        all: try (match goal with HF: forall blk, nth_error _ _ = Some blk -> _, H: nth_error _ _ = Some ?b |- _ =>
                 exfalso; destruct (HF _ H); congruence end).
        all: split; [reflexivity|].
        all: try (right; right; split; reflexivity); try (right; left; split; reflexivity).
        all: left; do 7 eexists; split; [reflexivity|split; [reflexivity|] ].
        all: try rewrite !t_update_eq; try reflexivity; try assumption.
        all: match goal with H: fetch _ _ = Some _ |- _ => pose proof (unused_prog_lookup _ _ _ _ UNUSED H) as U end.
        all: simpl in U; des; rewrite !t_update_neq by auto; assumption. }
      destruct LOCK as [<- [ (pc' & r1' & r2' & m1' & m2' & sb1' & sb2' & -> & -> & SPEQ')
                           | [ [-> ->] | [-> ->] ] ] ].
      * destruct (IH pc' r1' r2' m1' m2' sb1' sb2' os2b SPEQ' ltac:(reflexivity) REST2) as [hp|hp];
          [left|right]; apply (proj2 prefix_append_front); exact hp.
      * destruct (semI REST1) as [ HH | (? & ? & ? & ? & ? & _ & _ & STEPF & _) ]; [destruct HH as (? & ? & ?); subst|inversion STEPF].
        destruct (semI REST2) as [ HH | (? & ? & ? & ? & ? & _ & _ & STEPF & _) ]; [destruct HH as (? & ? & ?); subst|inversion STEPF].
        left. apply prefix_refl.
      * destruct (semI REST1) as [ HH | (? & ? & ? & ? & ? & _ & _ & STEPF & _) ]; [destruct HH as (? & ? & ?); subst|inversion STEPF].
        destruct (semI REST2) as [ HH | (? & ? & ? & ? & ? & _ & _ & STEPF & _) ]; [destruct HH as (? & ? & ?); subst|inversion STEPF].
        left. apply prefix_refl.
Qed.

Lemma ideal_eval_relative_secure: forall p pc r1 r2 m1 m2 sb1 sb2,
  seq_same_obs p pc r1 r2 m1 m2 ->
  sequential_safe (L := SeqLang) p (S_Running (pc, r1, m1)) ->
  sequential_safe (L := SeqLang) p (S_Running (pc, r2, m2)) ->
  r1 ! sp = r2 ! sp ->
  unused_prog sp p ->
  ideal_same_obs p pc r1 r2 m1 m2 sb1 sb2.
Proof.
  unfold ideal_same_obs.
  intros p pc r1 r2 m1 m2 sb1 sb2 Hsso SAFE1 SAFE2 SPEQ UNUSED ds os1 os2 c1 c2 Hexec1 Hexec2.
  pose proof (ideal_eval_multi_exec_split Hsso SAFE1 SAFE2 SPEQ UNUSED Hexec1 Hexec2)
    as (pc1' & pc2' & r1' & r2' & m1' & m2' & sb1' & sb2' & ds' & os1' & os2' & Hns1 & Hns2 & Hsplit).
  clear Hexec1 Hexec2.
  pose proof (multi_ideal_nonspec_seq _ _ _ _ _ _ _ _ _ _ _ Hns1) as S1.
  pose proof (multi_ideal_nonspec_seq _ _ _ _ _ _ _ _ _ _ _ Hns2) as S2.
  destruct Hsplit as [H | H].
  2: destruct H as (ds'' & os1'' & os2'' & -> & -> & -> & -> & SP' & Hobslen & H).
  - repeat destruct H as [-> H].
    eapply Hsso; eassumption.
  (* At the split point both sequential runs can still step (sequential safety);
     their observations are those of the ideal steps. *)
  - pose proof (sequential_safe_sem (L := SeqLang) SAFE1 S1) as SAFE1'.
    pose proof (sequential_safe_sem (L := SeqLang) SAFE2 S2) as SAFE2'.
    destruct (SAFE1' [] [] _ (sem_refl (L := SeqLang) p _)) as (os1s & c1s & SS1).
    destruct (SAFE2' [] [] _ (sem_refl (L := SeqLang) p _)) as (os2s & c2s & SS2).
    destruct H as [H | H].
    + destruct H as (-> & -> & Hf1 & Hf2).
      assert (os1'' = os1s) by (inversion Hf1; inversion SS1; subst; simpl in *; congruence).
      assert (os2'' = os2s) by (inversion Hf2; inversion SS2; subst; simpl in *; congruence).
      subst.
      eapply Hsso; eapply multi_seq_rcons; eassumption.
    + destruct H as (pc'' & r1'' & r2'' & m1'' & m2'' & sb1'' & sb2'' & d & ds''' & o1 & os1''' & o2 & os2'''
                     & -> & -> & -> & SP'' & Hmp1 & Hspec1 & Hmp2 & Hspec2).
      assert (EOS: os1' = os2').
      { destruct (Hsso _ _ _ _ S1 S2) as [hp|hp];
          [apply prefix_same_length; [exact hp|exact Hobslen]|symmetry; apply prefix_same_length; [exact hp|symmetry; exact Hobslen] ]. }
      subst os2'.
      assert (o1 = os1s) by (inversion Hmp1; inversion SS1; subst; simpl in *; congruence).
      assert (o2 = os2s) by (inversion Hmp2; inversion SS2; subst; simpl in *; congruence).
      subst o1 o2.
      assert (os1s = os2s) as <-.
      { pose proof (multi_ideal_nonspec_step_preserves_seq_same_obs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hsso Hns1 Hns2 ltac:(reflexivity)) as Hsso'.
        assert (LS: Datatypes.length os1s = Datatypes.length os2s) by (eapply seq_pc_determines_obs_count; eassumption).
        destruct (Hsso' _ _ _ _ (sem_step1 (L := SeqLang) (ds := []) SS1) (sem_step1 (L := SeqLang) (ds := []) SS2)) as [hp|hp];
          [apply prefix_same_length; [exact hp|exact LS]|symmetry; apply prefix_same_length; [exact hp|symmetry; exact LS] ]. }
      edestruct (ideal_misspec_unwinding SP'' UNUSED Hspec1 Hspec2).
      * left. now do 2 apply prefix_append_front.
      * right. now do 2 apply prefix_append_front.
Qed.

Lemma wf_prog_entry_fetch p l blk
  (WFP: wf_prog p)
  (BLK: nth_error p l = Some blk) :
  exists i, p[[(l, 0)]] = Some i.
Proof.
  destruct WFP as [_ WFB]. rewrite Forall_forall in WFB.
  destruct (WFB _ (nth_error_In _ _ BLK)) as (NE & _ & _). red in NE.
  ss. rewrite BLK. ss. destruct (fst blk); ss; [lia|eauto].
Qed.

Lemma ideal_step_sp_N p pc r m sb ms ds os pc' r' m' sb' ms' n
  (UNUSED: unused_prog sp p)
  (SP: r ! sp = N n)
  (STEP: p |- <(( S_Running (pc, r, m, sb, ms) ))> -->i_ ds ^^ os <(( S_Running (pc', r', m', sb', ms') ))>) :
  exists n', r' ! sp = N n'.
Proof.
  inv STEP; try (exists n; assumption); try (eexists; rewrite t_update_eq; reflexivity).
  all: exploit unused_prog_lookup; try eapply UNUSED; eauto; intros U; ss; des.
  all: exists n; rewrite t_update_neq; auto.
Qed.

Lemma ideal_step_misspec_fetch p pc r m sb ms ds os pc' r' m' sb'
  (WFP: wf_prog p)
  (STEP: p |- <(( S_Running (pc, r, m, sb, ms) ))> -->i_ ds ^^ os <(( S_Running (pc', r', m', sb', true) ))>) :
  exists i, p[[pc']] = Some i.
Proof.
  inv STEP; try (eapply block_always_terminator_prog; eauto; intros X; inv X; fail).
  - destruct b'; [|eapply block_always_terminator_prog; eauto; intros X; inv X].
    exploit wf_prog_lookup; eauto. intros (_ & LBL). red in LBL.
    destruct (nth_error p l) eqn:BLK; [|contradiction]. eapply wf_prog_entry_fetch; eauto.
  - exploit wf_prog_lookup; eauto. intros LBL. simpl in LBL. red in LBL.
    destruct (nth_error p l) eqn:BLK; [|contradiction]. eapply wf_prog_entry_fetch; eauto.
  - destruct pc'; ss; subst. eapply wf_prog_entry_fetch; eauto.
  - destruct pc'; ss; subst. eapply wf_prog_entry_fetch; eauto.
  - match goal with H: wf_ret _ _ |- _ => destruct pc' as [l o]; destruct H as [RET _] end.
    destruct (p[[(l, o)]]); eauto. congruence.
  - match goal with H: wf_ret _ _ |- _ => destruct pc' as [l o]; destruct H as [RET _] end.
    destruct (p[[(l, o)]]); eauto. congruence.
  - destruct p as [|blk p']; [destruct WFP as [NE _]; red in NE; ss; lia|].
    eapply (wf_prog_entry_fetch _ 0 blk); eauto.
Qed.

Lemma seq_step_ideal_step p pc r m sb os st
  (STEP: p |- <(( S_Running (pc, r, m) ))> -->^ os <(( st ))>) :
  exists ds os' st', p |- <(( S_Running (pc, r, m, sb, false) ))> -->i_ ds ^^ os' <(( st' ))>.
Proof.
  inv STEP; try (do 3 eexists; econs; eauto; fail).
  match goal with H: context [wf_label] |- _ => unfold wf_label in H; des_ifs end.
  destruct b; [|ss; clarify].
  do 3 eexists. eapply ISMI_Call with (pc' := (fst l, 0)); eauto.
  Unshelve. exact false.
Qed.

Lemma ideal_misspec_progress p pc r m sb n i
  (NCT: no_ct_prog p)
  (FST: first_blk_call p)
  (FETCH: p[[pc]] = Some i)
  (SP: r ! sp = N n) :
  exists ds os st', p |- <(( S_Running (pc, r, m, sb, true) ))> -->i_ ds ^^ os <(( st' ))>.
Proof.
  destruct i; try (do 3 eexists; econs; eauto; fail).
  all: try (exfalso; eapply no_ct_prog_src; eauto; fail).
  all: try (do 3 eexists; eapply ISMI_Ret_Misspec_Step; eauto; fail).
  red in FST. des_ifs. do 3 eexists. eapply ISMI_Call_Misspec with (pc' := (0, 0)); eauto.
  Unshelve. exact false.
Qed.

Lemma ideal_safe_inv_step p st ds os st'
  (WFP: wf_prog p)
  (UNUSED: unused_prog sp p)
  (INV: ideal_safe_inv p st)
  (STEP: p |- <(( st ))> -->i_ ds ^^ os <(( st' ))>) :
  ideal_safe_inv p st'.
Proof.
  destruct st as [ [ [ [ [pc r] m] sb] ms] | | | ]; try (inv STEP; fail).
  destruct st' as [ [ [ [ [pc' r'] m'] sb'] ms'] | | | ]; ss; [|inv STEP].
  destruct INV as [ [n SP] INV].
  split; [eapply ideal_step_sp_N; eauto|].
  destruct ms'; [eapply ideal_step_misspec_fetch; eauto|].
  destruct ms; [discriminate (multi_ideal_ms_monotonic (sem_step1 (L := IdealLang) STEP))|].
  eapply (sequential_safe_step (L := SeqLang) (ds := [])); [exact INV|].
  exact (ideal_nonspec_seq _ _ _ _ _ _ _ _ _ _ _ STEP).
Qed.

Lemma ideal_safe_inv_sem p st ds os st'
  (WFP: wf_prog p)
  (UNUSED: unused_prog sp p)
  (INV: ideal_safe_inv p st)
  (RUN: p |- <(( st ))> -->i*_ ds ^^ os <(( st' ))>) :
  ideal_safe_inv p st'.
Proof.
  revert INV. induction RUN; intros INV; [exact INV|].
  apply IHRUN. eapply ideal_safe_inv_step; [exact WFP|exact UNUSED|exact INV|exact H].
Qed.

Lemma ideal_safe_inv_safe p st
  (NCT: no_ct_prog p)
  (FST: first_blk_call p)
  (INV: ideal_safe_inv p st) :
  safe_imm_ideal p st.
Proof.
  destruct st as [ [ [ [ [pc r] m] sb] ms] | | | ]; ss.
  destruct INV as [ [n SP] INV]. destruct ms.
  - destruct INV as [i FETCH]. eapply ideal_misspec_progress; eauto.
  - destruct (INV [] [] _ (sem_refl (L := SeqLang) p _)) as (os & st' & STEP).
    eapply seq_step_ideal_step; eauto.
Qed.

Lemma seq_safe_ideal_safe p pc r m sb n
  (WFP: wf_prog p)
  (NCT: no_ct_prog p)
  (FST: first_blk_call p)
  (UNUSED: unused_prog sp p)
  (SP: r ! sp = N n)
  (SAFE: sequential_safe (L := SeqLang) p (S_Running (pc, r, m))) :
  sequential_safe (L := IdealLang) p (S_Running (pc, r, m, sb, false)).
Proof.
  intros ds os st' RUN.
  eapply ideal_safe_inv_safe; eauto.
  eapply ideal_safe_inv_sem; eauto. ss. eauto.
Qed.

Lemma spec_eval_relative_secure
  (p : prog)
  (r1 r2 : reg)
  (m1 m2 : mem)
  (initial_sp : nat)
  (SAFE1 : sequential_safe (L := SeqLang) p (initial_machine (L := SeqLang) p (r1, m1)))
  (SAFE2 : sequential_safe (L := SeqLang) p (initial_machine (L := SeqLang) p (r2, m2))) :
  relative_secure (Ls := SeqLang) (Lt := SpecLang) 
    uslh_full_compiler (uslh_sync initial_sp) p (uslh_prog p) (r1, m1) (r2, m2).
Proof.
  intros inp1' inp2' SAME SYNC1 SYNC2 [p_i <- COMP].
  pose proof SYNC1 as (_ & _ & SP1 & _). pose proof SYNC2 as (_ & _ & SP2 & _).
  simpl in SP1, SP2.
  eapply (obs_eq_safe_bw_relsec (Ls := IdealLang) (Lt := SpecLang) (p_s := p) (p_t := uslh_prog p) (inp1 := (r1, m1)) (inp2 := (r2, m2))
            (ultimate_slh_safe_bw_simulation initial_sp)); [| | |exact SYNC1|exact SYNC2|exact COMP];
  destruct COMP as (COMP & WFP & NCT & UNUSED1 & UNUSED2 & UNUSED3 & FST).
  - exact (seq_safe_ideal_safe p (0, 0) r1 m1 (mirror_mem m1) initial_sp WFP NCT FST UNUSED3 SP1 SAFE1).
  - exact (seq_safe_ideal_safe p (0, 0) r2 m2 (mirror_mem m2) initial_sp WFP NCT FST UNUSED3 SP2 SAFE2).
  - intros ds os1 os2 c1 c2 RUN1 RUN2.
    eapply (ideal_eval_relative_secure p (0, 0) r1 r2 m1 m2 (mirror_mem m1) (mirror_mem m2));
      [|exact SAFE1|exact SAFE2|congruence|exact UNUSED3|exact RUN1|exact RUN2].
    intros os1' os2' c1' c2' S1 S2. exact (SAME [] os1' os2' c1' c2' S1 S2).
Qed.

(* -------------------------------------------------------------------------- *)
(* Case study: Spectre 1.1 *)

Definition cet_prog (p: prog) : prog :=
  map (fun '((bl, is_proc) : list inst * bool) => (if is_proc then ICTarget :: bl else bl, is_proc)) p.

Definition spectre11_prog : prog := [
  (<{{ i[ call &(1,0); exit ] }}>, true);
  (<{{ i[ branch (X < 1) to 2; ret ] }}>, true);
  (<{{ i[ store[X] <- Y; ret ] }}>, false);
  (<{{ i[ Z <- load[W]; exit ] }}>, false)
].

Definition spectre11_mem : mem :=
  {| memory := [N 0; N 0; N 0];
     stack_top := 3;
     stack_base := 1;
     stack_top_valid := ltac:(simpl; lia);
     stack_base_valid := ltac:(lia) |}.

Definition spectre11_regs (s: nat) : reg :=
  (callee !-> FP (0, 0); sp !-> N 1; X !-> N 2; Y !-> FP (3, 0); W !-> N s; reg_init).

Definition spectre11_input (s: nat) : input := (spectre11_regs s, spectre11_mem).

Definition seq_bounded (p: prog) (st: state cfg) (T: obs) : Prop :=
  forall ds os st', sem (L := SeqLang) p st ds os st' -> Utils.prefix os T /\ safe_imm_seq p st'.

Lemma seq_bounded_term p T : seq_bounded p S_Term T.
Proof.
  intros ds os st' RUN. inv RUN; [split; [apply prefix_nil|ss]|]. inv H.
Qed.

Lemma seq_step_deterministic p st st1 st2 os1 os2
  (STEP1: p |- <(( st ))> -->^ os1 <(( st1 ))>)
  (STEP2: p |- <(( st ))> -->^ os2 <(( st2 ))>) :
  os1 = os2 /\ st1 = st2.
Proof.
  inv STEP1; inv STEP2;
    match goal with H1: fetch _ _ = Some _, H2: fetch _ _ = Some _ |- _ => rewrite H1 in H2; inv H2 end;
    clarify.
  all: repeat match goal with
         | H1: ?a = ?b, H2: ?a = ?c |- _ => assert_fails (constr_eq b c); rewrite H1 in H2; inv H2
         end; auto.
Qed.

Lemma seq_bounded_step p c st o T T'
  (STEP: p |- <(( S_Running c ))> -->^ o <(( st ))>)
  (EQ: T' = o ++ T)
  (NEXT: seq_bounded p st T) :
  seq_bounded p (S_Running c) T'.
Proof.
  subst. intros ds os st' RUN. inv RUN; [split; [apply prefix_nil|ss; eauto]|].
  ss. exploit seq_step_deterministic; [exact STEP|exact H|]. intros [EQ1 EQ2]; subst.
  exploit NEXT; eauto. intros [PRE SAFE]. destruct PRE as [zs PRE]. subst. split; auto.
  exists zs. rewrite app_assoc. auto.
Qed.

Lemma spectre11_seq_bounded s :
  seq_bounded spectre11_prog (initial_machine (L := SeqLang) spectre11_prog (spectre11_input s))
    [OCall (1, 0) 1; OBranch false; ORet (0, 1) 2].
Proof.
  ss.
  eapply seq_bounded_step; [eapply SSMI_Call with (sp_val := 1); ss|reflexivity|].
  eapply seq_bounded_step; [eapply SSMI_Branch with (n := 0); ss|reflexivity|].
  eapply seq_bounded_step; [eapply SSMI_Ret with (sp_val := 2); ss|reflexivity|].
  eapply seq_bounded_step; [eapply SSMI_Term; ss|reflexivity|].
  apply seq_bounded_term.
Qed.

Lemma spectre11_seq_safe s :
  sequential_safe (L := SeqLang) spectre11_prog (initial_machine (L := SeqLang) spectre11_prog (spectre11_input s)).
Proof. intros ds os st' RUN. eapply spectre11_seq_bounded; eauto. Qed.

Lemma spectre11_seq_same_obs s1 s2 :
  same_obs (L := SeqLang) spectre11_prog (spectre11_input s1) (spectre11_input s2).
Proof.
  intros ds os1 os2 st1 st2 RUN1 RUN2.
  exploit spectre11_seq_bounded; [exact RUN1|]. intros [PRE1 _]. destruct PRE1 as [zs1 PRE1].
  exploit spectre11_seq_bounded; [exact RUN2|]. intros [PRE2 _]. destruct PRE2 as [zs2 PRE2].
  rewrite <- PRE2 in PRE1. exact (app_eq_prefix PRE1).
Qed.

Lemma sem_step_eq {inp: Type} {L: Language inp} p m m' m'' ds1 os1 ds2 os2 ds os
  (STEP: step p m ds1 os1 m')
  (RUN: sem p m' ds2 os2 m'')
  (DS: ds = ds1 ++ ds2)
  (OS: os = os1 ++ os2) :
  sem p m ds os m''.
Proof. subst. eapply sem_step; eauto. Qed.

Lemma spectre11_cet_leak_run s :
  exists st, sem_p (L := SpecLang) (cet_prog spectre11_prog) (spectre11_input s)
    [DCall (1, 0); DBranch true; DRet None]
    [OCall (1, 0) 1; OBranch false; OStore 2; ORet (3, 0) 2; OLoad s] st.
Proof.
  eexists. unfold sem_p. ss.
  eapply sem_step_eq; [eapply SpecSMI_CTarget; ss| | |].
  1: eapply sem_step_eq; [eapply SpecSMI_Call with (sp_val := 1) (pc' := (1, 0)); ss| | |].
  1: eapply sem_step_eq; [eapply SpecSMI_CTarget; ss| | |].
  1: eapply sem_step_eq; [eapply SpecSMI_Branch with (n := 0) (b' := true); ss| | |].
  1: eapply sem_step_eq; [eapply SpecSMI_Store_Misspec with (n := 2); ss| | |].
  1: eapply sem_step_eq; [eapply SpecSMI_Ret_Misspec_Step with (sp_val := 2) (pc' := (3, 0));
                          try (rewrite t_update_eq; reflexivity); ss| | |].
  1: eapply sem_step_eq; [eapply SpecSMI_Load_Misspec with (n := s); ss| | |].
  1: eapply sem_refl.
  all: reflexivity.
Qed.

Lemma spectre11_cet_leak s1 s2 (NEQ: s1 <> s2) :
  ~ same_obs (L := SpecLang) (cet_prog spectre11_prog) (spectre11_input s1) (spectre11_input s2).
Proof.
  intros SAME.
  destruct (spectre11_cet_leak_run s1) as [st1 RUN1].
  destruct (spectre11_cet_leak_run s2) as [st2 RUN2].
  exploit SAME; [exact RUN1|exact RUN2|]. intros CMP.
  assert (EQ: [OCall (1, 0) 1; OBranch false; OStore 2; ORet (3, 0) 2; OLoad s1]
            = [OCall (1, 0) 1; OBranch false; OStore 2; ORet (3, 0) 2; OLoad s2]).
  { destruct CMP as [CMP|CMP]; [|symmetry]; eapply prefix_same_length; eauto. }
  clarify.
Qed.

Theorem spectre11_unhardened_insecure s1 s2 (NEQ: s1 <> s2) :
  ~ relative_secure (Ls := SeqLang) (Lt := SpecLang)
      (fun p_s p_t => p_t = cet_prog p_s) (fun _ inp inp' => inp' = inp)
      spectre11_prog (cet_prog spectre11_prog) (spectre11_input s1) (spectre11_input s2).
Proof.
  intros SEC. eapply (spectre11_cet_leak s1 s2 NEQ).
  eapply SEC; [eapply spectre11_seq_same_obs|reflexivity|reflexivity|reflexivity].
Qed.

Lemma spectre11_compile :
  uslh_full_compiler spectre11_prog (uslh_prog spectre11_prog).
Proof.
  exists spectre11_prog; [reflexivity|].
  unfold uslh_compiler. splits; [reflexivity| | | | | |ss].
  - unfold wf_prog, nonempty_program. split; [ss; lia|].
    repeat econs; unfold nonempty_block, last_inst_terminator, wf_lbl; ss; lia.
  - repeat econs.
  - repeat econs; ss.
  - repeat econs; ss.
  - repeat econs; ss.
Qed.

Lemma spectre11_sync s :
  uslh_sync 1 spectre11_prog (spectre11_input s) (spectre11_input s).
Proof.
  unfold uslh_sync, Rsync1, Msync. splits; ss.
  - intros x _ _. unfold spectre11_regs, TotalMap.t_apply, TotalMap.t_update, Maps.t_update.
    des_ifs; ss; auto.
  - intros i. do 4 (destruct i as [|i]; ss).
Qed.

Theorem spectre11_hardened_secure s1 s2 :
  relative_secure (Ls := SeqLang) (Lt := SpecLang) uslh_full_compiler (uslh_sync 1)
    spectre11_prog (uslh_prog spectre11_prog) (spectre11_input s1) (spectre11_input s2).
Proof. eapply spec_eval_relative_secure; eapply spectre11_seq_safe. Qed.

Corollary spectre11_hardened_same_obs s1 s2 :
  same_obs (L := SpecLang) (uslh_prog spectre11_prog) (spectre11_input s1) (spectre11_input s2).
Proof.
  eapply spectre11_hardened_secure;
    [eapply spectre11_seq_same_obs|eapply spectre11_sync|eapply spectre11_sync|eapply spectre11_compile].
Qed.
