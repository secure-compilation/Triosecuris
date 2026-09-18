From Stdlib Require Import List
  Strings.String String
  Bool.Bool
  Arith.EqNat
  Arith.PeanoNat
  Lia.
Import Nat ListNotations.
Set Default Goal Selector "!".
From SECF Require Import
    MapsFunctor
    MiniCET
    Utils
    ListMaps
    Printing.
Require Import Stdlib.Classes.EquivDec.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Export ExtLib.Data.Monads.OptionMonad.
Import MonadNotation. Open Scope monad_scope.

Module Type Semantics(M : TMap).
  Parameter pc : Type.
  Definition reg := M.t val.
  Definition cfg : Type := (pc * reg) * mem.
  Definition spec_cfg : Type := (cfg * bool) * bool.
  Definition ideal_cfg : Type := cfg * bool.

  Definition dir := direction.
  Definition dirs := list dir.

  Parameter ipc : pc.
  Parameter icfg : pc -> reg -> mem -> cfg.

  Parameter eval : reg -> exp -> val.
  Parameter fetch : prog -> pc -> option inst.
  Parameter step : prog -> state cfg -> state cfg * obs.
  Parameter steps : nat -> prog -> state cfg -> state cfg * obs.
  Parameter spec_step : prog -> state spec_cfg -> dirs -> state spec_cfg * dirs * obs.
  Parameter spec_steps : nat -> prog -> state spec_cfg -> dirs -> state spec_cfg * dirs * obs.
End Semantics.

Module MiniCETSemantics (M : TMap) <: Semantics M.
Module Import Common := MiniCETCommon(M).

Definition reg := M.t val.
Definition cfg : Type := (cptr*reg)*mem.
Definition spec_cfg : Type := ((cfg * bool) * bool).
Definition ideal_cfg : Type := cfg * bool.

Definition pc := cptr.
Definition ipc : cptr := (0, 0).
Definition icfg (ipc : pc) (ireg : reg) (mem : mem) : cfg :=
  (ipc, ireg, mem).

Definition dir := direction.
Definition dirs := dirs.
Definition fetch := MiniCET.fetch.

Fixpoint eval (st : reg) (e: exp) : val :=
  match e with
  | ANum n => N n
  | AId x => M.t_apply st x
  | ABin b e1 e2 => eval_binop b (eval st e1) (eval st e2)
  | <{b ? e1 : e2}> =>
      match to_nat (eval st b) with
      | Some n1 => if not_zero n1 then eval st e1 else eval st e2
      | None => UV
      end
  | <{&l}> => FP l
  end.

  Definition step (p:prog) (sc:state cfg) : (state cfg * obs) :=
    match sc with
    | S_Running c =>
        let '(pc, r, m) := c in
        match p[[pc]] with
        | Some i =>
            match i with
            | <{{skip}}> | <{{ctarget}}> =>
              (S_Running (pc+1, r, m), [])
            | <{{x:=e}}> =>
              (S_Running (pc+1, (x !-> eval r e; r), m), [])
            | <{{x <- div e1, e2}}> =>
              match
                v1 <- to_nat (eval r e1);;
                v2 <- to_nat (eval r e2);;
                let res: val := match v2 with
                  | 0 => UV
                  | _ => N (div v1 v2)
                  end
                in
                Some ((pc + 1, (x !-> res; r), m), [ODiv v1 v2])
              with
              | Some (c, o) =>
                (S_Running c, o)
              | None =>
                (S_Undef, [])
              end
            | <{{branch e to l}}> =>
              match
                n <- to_nat (eval r e);;
                let b := not_zero n in
                ret ((if b then (l,0) else pc+1, r, m), [OBranch b])
              with
              | Some (c, o) => (S_Running c, o)
              | None => (S_Undef, [])
              end
            | <{{jump l}}> =>
              (S_Running ((l,0), r, m), [])
            | <{{x<-load[e]}}> =>
              match
                n <- to_nat (eval r e);;
                v' <- nth_error m n;;
                ret ((pc+1, (x !-> v'; r), m), [OLoad n])
              with
              | Some (c, o) => (S_Running c, o)
              | None => (S_Undef, [])
              end
            | <{{store[e]<-e'}}> =>
              match
                n <- to_nat (eval r e);;
                ret ((pc+1, r, upd n m (eval r e')), [OStore n])
              with
              | Some (c, o) => (S_Running c, o)
              | None => (S_Undef, [])
              end
            | <{{call e}}> =>
              match
                l <- to_fp (eval r e);;
                sp <- to_nat (M.t_apply r "sp");;
                ret ((l, "sp" !-> N (S sp); r, upd (S sp) m (FP (pc+1))), [OCall l])
              with
              | Some (c, o) => (S_Running c, o)
              | None => (S_Undef, [])
              end
            (*| <{{x <- peek}}> =>*)
              (*let val := *)
                (*match sk with*)
                (*| [] => UV*)
                (*| pc' :: _ => FP pc'*)
                (*end*)
              (*in*)
              (*(S_Running (pc + 1, (x !-> val; r), m), [])*)
            | <{{ret}}> =>
              match
                sp <- to_nat (M.t_apply r "sp");;
                _pc' <- nth_error m sp;;
                ret (sp, _pc')
              with
              | None => (S_Undef, [])
              | Some (sp, _pc') =>
                match to_fp _pc' with
                (* bottom of the stack: nothing was pushed there, so this
                   returns out of the program *)
                | None => (S_Term, [])
                | Some pc' => (S_Running (pc', "sp" !-> N(sp - 1); r, m), [])
                end
              end
            end
        | None => (S_Fault, [])
        end
    | s => (s, [])
    end.

  Definition spec_step (p:prog) (ssc: state spec_cfg) (ds: dirs) : (state spec_cfg * dirs * obs) :=
    match ssc with
    | S_Running sc =>
        let '(c, ct, ms) := sc in
        let '(pc, r, m) := c in
        match p[[pc]] with
        | None => untrace "lookup fail" (S_Undef, ds, [])
        | Some i =>
            match i with
            | <{{branch e to l}}> =>
              if ct then   (S_Fault, ds, []) else
              match
                if seq.nilp ds then
                  untrace "Branch: Directions are empty!" None
                else
                  d <- hd_error ds;;
                  b' <- is_dbranch d;;
                  n <- to_nat (eval r e);;
                  let b := not_zero n in
                  let ms' := ms || negb (Bool.eqb b b') in
                  let pc' := if b' then (l, 0) else (pc+1) in
                  ret ((S_Running ((pc', r, m), ct, ms'), tl ds), [OBranch b])
              with
              | None => untrace "branch fail" (S_Undef, ds, [])
              | Some (c, ds, os) => (c, ds, os)
              end
            | <{{call e}}> =>
              if ct then   (S_Fault, ds, []) else
              match
                if seq.nilp ds then
                  untrace "Call: Directions are empty!" None
                else
                  d <- hd_error ds;;
                  pc' <- is_dcall d;;
                  l <- to_fp (eval r e);;
                  sp <- to_nat (M.t_apply r "sp");;
                  let ms' := ms || negb ((fst pc' =? fst l) && (snd l =? (snd pc')%nat)) in
                  (*! *)
                  ret ((S_Running ((pc', "sp" !-> N (S sp); r, upd (S sp) m (FP (pc+1))), true, ms'), tl ds), [OCall l])
                  (*!! spec-call-no-set-ct *)
                  (*! ret ((S_Running ((pc', "sp" !-> N (S sp); r, upd (S sp) m (FP (pc+1))), ct, ms'), tl ds), [OCall l]) *)
                  (*!! spec-call-push-pc *)
                  (*! ret ((S_Running ((pc', "sp" !-> N (S sp); r, upd (S sp) m (FP pc)), true, ms'), tl ds), [OCall l]) *)
                  (*!! spec-call-no-sp-bump *)
                  (*! ret ((S_Running ((pc', r, upd (S sp) m (FP (pc+1))), true, ms'), tl ds), [OCall l]) *)
              with
              | None => untrace "call fail" (S_Undef, ds, [])
              | Some (c, ds, os) => (c, ds, os)
              end
            | <{{ctarget}}> =>
              match
                is_true ct;;
                (*! *)
                (ret (S_Running ((pc+1, r, m), false, ms), ds, []))
                (*!! spec_ctarget_no_clear *)
                (*! (ret (S_Running ((pc+1, r, m), ct, ms), ds, [])) *)
              with
              | None => untrace "ctarget fail!" (S_Undef, ds, [])
              | Some (c, ds, os) => (c, ds, os)
              end
            | <{{ret}}> =>
              if ct then (S_Fault, ds, []) else
              match
                sp <- to_nat (M.t_apply r "sp");;
                _pc' <- nth_error m sp;;
                ret (sp, _pc')
              with
              | None => untrace "ret: no return slot" (S_Undef, ds, [])
              | Some (sp, _pc') =>
                match to_fp _pc' with
                (* bottom of the stack: nothing was pushed there *)
                | None => (S_Term, ds, [])
                | Some pc' =>
                  match
                    if seq.nilp ds then
                      untrace "Ret: Directions are empty!" None
                    else
                      d <- hd_error ds;;
                      pc'' <- is_dret d;;
                      is_true (wf_retb p pc'');;
                      let ms' := ms || negb ((fst pc' =? fst pc'')%nat && (snd pc' =? snd pc'')%nat) in
                      (*! *)
                      ret ((S_Running ((pc'', "sp" !-> N(sp - 1); r, m), false, ms'), tl ds), [])
                      (*!! spec-ret-no-sp-restore *)
                      (*! ret ((S_Running ((pc'', r, m), false, ms'), tl ds), []) *)
                  with
                  | None => untrace "ret fail" (S_Undef, ds, [])
                  | Some (c, ds, os) => (c, ds, os)
                  end
                end
              end
            | _ =>
              if ct then   (S_Fault, ds, [])
              else
                match step p (S_Running c) with
                | (S_Running c', o) => (S_Running (c', false, ms), ds, o)
                | (S_Undef, o) => (S_Undef, ds, o)
                | (S_Fault, o) => (S_Fault, ds, o)
                | (S_Term, o) => (S_Term, ds, o)
                end
            end
        end
    | s => (s, ds, [])
    end.

  Fixpoint spec_steps (f:nat) (p:prog) (sc: state spec_cfg) (ds: dirs)
    : (state spec_cfg * dirs * obs) :=
    match f with
    | S f' =>
        match sc with
        | S_Running c =>
            let '(c1,ds1,o1) := spec_step p sc ds in
            let '(c2,ds2,o2) := spec_steps f' p c1 ds1 in
            (c2,ds2,o1++o2)
        | s => (s, ds, [])
        end
    | 0 =>
        (sc, ds, [])
    end.


  Fixpoint steps (f:nat) (p:prog) (sc: state cfg) : (state cfg * obs) :=
    match f with
    | S f' =>
        match sc with
        | S_Running c =>
            let '(c1, o1) := step p sc in
            let '(c2, o2) := steps f' p c1 in
            (c2, o1++o2)
        | s => (s, [])
        end
    | 0 =>
        (sc, [])
    end.

End MiniCETSemantics.

Module IdealStepSemantics (Import ST : Semantics ListTotalMap with Definition pc := cptr).

From QuickChick Require Import QuickChick.

Definition ideal_step (p: prog) (sic: state ideal_cfg) (ds: dirs): (state ideal_cfg * dirs * obs) :=
  match sic with
  | S_Running ic =>
      let '(c, ms) := ic in
      let '(pc, r, m) := c in
      match fetch p pc with
        None => untrace ("lookup fail" ++ nl) (S_Undef, ds, [])
      | Some i =>
          match i with
            | <{{branch e to l}}> =>
              if seq.nilp ds then
                untrace ("idealBranch: directions are empty!" ++ nl) (S_Undef, ds, [])
              else
                match
                  d <- hd_error ds;;
                  b' <- is_dbranch d;;
                  n <- to_nat (eval r e);;
                  let b := (negb ms) && not_zero n in
                  (*! *)
                  let ms' := ms || negb (Bool.eqb b b') in
                  (*!! ideal_branch_bad_update_ms *)
                  (*! let ms' := negb (Bool.eqb b b') in *)
                  let _ := I in
                  (*! *)
                  let pc' := if b' then (l, 0) else (pc+1) in
                  (*!! ideal_branch_ignore_directive *)
                  (*! let pc' := if b then (l, 0) else (pc+1) in *)
                  ret ((S_Running ((pc', r, m), ms'), tl ds), [OBranch b])
                with
                | None => (S_Undef, ds, [])
                | Some (c, ds, os) => (c, ds, os)
                end
            | <{{call e}}> =>
              if seq.nilp ds then
                untrace ("idealCall: directions are empty!" ++ nl) (S_Undef, ds, [])
              else
                match
                  d <- hd_error ds;;
                  pc' <- is_dcall d;;
                  l <- (if ms then Some (0, 0) else to_fp (eval r e));;
                  sp <- to_nat (ListTotalMap.t_apply r "sp");;
                  blk <- nth_error p (fst pc');;
                  (*! *)
                  if (snd blk && (snd pc' ==b 0)) then
                  (*!! ideal_call_no_check_target *)
                  (*! if true then *)
                    let ms' := ms || negb ((fst pc' =? fst l) && (snd pc' =? snd l)) in
                    (*! *)
                    ret ((S_Running ((pc', "sp" !-> N (S sp); r, upd (S sp) m (FP (pc+1))), ms'), tl ds), [OCall l])
                    (*!! ideal-call-push-at-sp *)
                    (*! ret ((S_Running ((pc', "sp" !-> N (S sp); r, upd sp m (FP (pc+1))), ms'), tl ds), [OCall l]) *)
                    (*!! ideal-call-no-sp-bump *)
                    (*! ret ((S_Running ((pc', r, upd (S sp) m (FP (pc+1))), ms'), tl ds), [OCall l]) *)
                  else Some (S_Fault, ds, [OCall l])
                with
                | None => (S_Undef, ds, [])
                | Some (c, ds, os) => (c, ds, os)
                end
            | <{{x<-load[e]}}> =>
              match
                (*! *)
                let i := if ms then (ANum 0) else e in
                (*!! ideal-load-no-mask *)
                (*! let i := e in *)
                n <- to_nat (eval r i);;
                v' <- nth_error m n;;
                let c := (pc+1, (x !-> v'; r), m) in
                ret (S_Running (c, ms), ds, [OLoad n])
              with
              | None => (S_Undef, ds, [])
              | Some (c, ds, os) => (c, ds, os)
              end
            | <{{store[e]<-e'}}> =>
              match
                (*! *)
                let i := if ms then (ANum 0) else e in
                (*!! ideal-store-no-mask *)
                (*! let i := e in *)
                n <- to_nat (eval r i);;
                let c:= (pc+1, r, upd n m (eval r e')) in
                ret (S_Running (c, ms), ds, [OStore n])
              with
              | None => (S_Undef, ds, [])
              | Some (c, ds, os) => (c, ds, os)
              end
            | <{{ret}}> =>
              match
                sp <- to_nat (ListTotalMap.t_apply r "sp");;
                (*! *)
                _pc' <- nth_error m sp;;
                (*!! ideal-ret-read-above-sp *)
                (*! _pc' <- nth_error m (S sp);; *)
                ret (sp, _pc')
              with
              | None => untrace ("ideal ret: no return slot. PC: " ++ show pc ++ nl) (S_Undef, ds, [])
              | Some (sp, _pc') =>
                match to_fp _pc' with
                (* bottom of the stack: nothing was pushed there *)
                | None => (S_Term, ds, [])
                | Some pc' =>
                  match
                    if seq.nilp ds then
                      untrace ("ideal ret: Directions are empty!" ++ nl) None
                    else
                      d <- hd_error ds;;
                      pc'' <- is_dret d;;
                      MiniCET.is_true (wf_retb p pc'');;
                      let ms' := ms || negb ((fst pc' =? fst pc'')%nat && (snd pc' =? snd pc'')%nat) in
                      (*! *)
                      ret ((S_Running ((pc'', "sp" !-> N (sp - 1); r, m), ms'), tl ds), [])
                      (*!! ideal-ret-no-sp-restore *)
                      (*! ret ((S_Running ((pc'', r, m), ms'), tl ds), []) *)
                  with
                  | None => untrace ("ideal ret failed. PC: " ++ show pc ++ "; PROGRAM: " ++ show p ++ nl) (S_Undef, ds, [])
                  | Some (c, ds, os) => (c, ds, os)
                  end
                end
              end
          | _ =>
              match step p (S_Running c) with
              | (S_Running c', o) => (S_Running (c', ms), ds, o)
              | (S_Undef, o) => (S_Undef, ds, o)
              | (S_Fault, o) => (S_Fault, ds, o)
              | (S_Term, o) => (S_Term, ds, o)
              end
          end
      end
  | s => (s, ds, [])
  end.

Fixpoint ideal_steps (f: nat) (p: prog) (sic: state ideal_cfg) (ds: dirs)
  : (state ideal_cfg * dirs * obs) :=
  match f with
  | S f' =>
      match sic with
      | S_Running ic =>
          let '(c1, ds1, o1) := ideal_step p sic ds in
          let '(c2, ds2, o2) := ideal_steps f' p c1 ds1 in
          (c2, ds2, o1++o2)
      | s => (s, ds, [])
      end
  | 0 =>
      (sic, ds, [])
  end.

End IdealStepSemantics.