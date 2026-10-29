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
    Printing
    Code.
Require Import Stdlib.Classes.EquivDec.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Export ExtLib.Data.Monads.OptionMonad.
Import MonadNotation. Open Scope monad_scope.
From QuickChick Require Import QuickChick.

(* The configuration types and the pc-free helpers, shared verbatim by the
   signature and by every implementation.  [Include]ing this on both sides is
   what stops the two from drifting apart. *)
Module SemTypes (M : TMap) (C : Code).

Notation "p '[[' pc ']]'" := (C.fetch p pc) : com_scope.
Notation "pc '+' '1'" := (C.next pc) : com_scope.
Notation "'_' '!->' v" := (M.init v)
    (at level 100, right associativity).
Notation "x '!->' v ';' m" := (M.t_update m x v)
    (at level 100, v at next level, right associativity).
Notation "m '!' x" := (M.t_apply m x)
    (at level 20, left associativity).

#[local] Existing Instance C.show_pc.

Definition pc := C.pc.
Definition fetch := C.fetch.
Definition ipc : pc := C.ipc.

Definition reg := M.t string val.
Definition cfg : Type := (pc * reg) * mem.
Definition spec_mem := M.t nat val.
Definition spec_cfg : Type := ((cfg * spec_mem) * bool) * bool.
Definition ideal_cfg : Type := ((cfg * spec_mem)) * bool.

Definition dir := direction.
Definition dirs := list dir.

Definition ismem : spec_mem := @M.init nat val UV.
Definition icfg (q : pc) (ireg : reg) (m : mem) : cfg := (q, ireg, m).

Definition smem_of_mem (m : mem) : spec_mem :=
  fold_left (fun sb '(n, v) => match v with UV => sb | _ => (n !-> v; sb) end)
    (add_index m.(memory)) ismem.

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
  | <{&l}> => C.eval_fptr l
  end.

Definition ret_addr (r : reg) (m : mem) : option pc :=
  sp <- to_nat (M.t_apply r sp);;
  C.of_val (get_mem sp m).

End SemTypes.

Module Type Semantics(M : TMap).
  Declare Module C : Code.
  Include SemTypes M C.

  Parameter step : prog -> state cfg -> state cfg * obs.
  Parameter steps : nat -> prog -> state cfg -> state cfg * obs.
  Parameter spec_step : prog -> state spec_cfg -> dirs -> state spec_cfg * dirs * obs.
  Parameter spec_steps : nat -> prog -> state spec_cfg -> dirs -> state spec_cfg * dirs * obs.
  Parameter ideal_step : prog -> state ideal_cfg -> dirs -> state ideal_cfg * dirs * obs.
  Parameter ideal_steps : nat -> prog -> state ideal_cfg -> dirs -> state ideal_cfg * dirs * obs.
End Semantics.

Module MachineSemantics (M : TMap) (CC : Code) <: Semantics M.
Module C := CC.
Include SemTypes M C.

Existing Instance C.show_pc.

Definition or_undef {A : Type} (o : option (state A * obs)) : state A * obs :=
  match o with
  | Some res => res
  | None => (S_Undef, [])
  end.

Definition or_undef_ds {A : Type} (ds : dirs) (o : option (state A * dirs * obs))
  : state A * dirs * obs :=
  match o with
  | Some res => res
  | None => (S_Undef, ds, [])
  end.

Definition step (p:prog) (sc:state cfg) : (state cfg * obs) :=
  match sc with
  | S_Running (pc, r, m) =>
      match p[[pc]] with
      | Some <{{skip}}> =>
        (S_Running (pc+1, r, m), [])
      | Some <{{x:=e}}> =>
        (S_Running (pc+1, (x !-> eval r e; r), m), [])
      | Some <{{x <- div e1, e2}}> =>
        or_undef (
          v1 <- to_nat (eval r e1);;
          v2 <- to_nat (eval r e2);;
          let res: val := match v2 with
            | 0 => UV
            | _ => N (div v1 v2)
            end
          in
          ret (S_Running (pc+1, (x !-> res; r), m), [ODiv v1 v2]))
      | Some <{{branch e to l}}> =>
        or_undef (
          n <- to_nat (eval r e);;
          let b := not_zero n in
          ret (S_Running (if b then C.of_label l else pc+1, r, m), [OBranch b]))
      | Some <{{jump l}}> =>
        (S_Running (C.of_label l, r, m), [])
      | Some <{{x<-load[e]}}> =>
        or_undef (
          n <- to_nat (eval r e);;
          v <- nth_error m.(memory) n;;
          ret (S_Running (pc+1, (x !-> v; r), m), [OLoad n]))
      | Some <{{store[e]<-e'}}> =>
        or_undef (
          n <- to_nat (eval r e);;
          ret (S_Running (pc+1, r, upd_mem n m (eval r e')), [OStore n]))
      | Some <{{call e}}> =>
        or_undef (
          l <- C.of_val (eval r e);;
          _sp <- to_nat (r ! sp);;
          is_true (S _sp <? stack_top m);;
          ret (S_Running (l, sp !-> N (S _sp); r, upd_mem (S _sp) m (C.to_val (pc+1))), [OCall (C.to_cptr p l) _sp]))
      | Some <{{ret}}> =>
        or_undef (
          _sp <- to_nat (r ! sp);;
          is_true (_sp <? stack_top m);;
          v <- nth_error m.(memory) _sp;;
          (* no code pointer in the slot: [exit] is the only terminator *)
          pc' <- C.of_val v;;
          ret (S_Running (pc', sp !-> N (_sp - 1); r, m), [ORet (C.to_cptr p pc') _sp]))
      | Some <{{exit}}> =>
        (S_Term, [])
      | _ =>
        (S_Undef, [])
      end
  | s => (s, [])
  end.

Definition spec_step (p:prog) (ssc: state spec_cfg) (ds: dirs) : (state spec_cfg * dirs * obs) :=
  match ssc with
  | S_Running ((pc, r, m), smem, ct, ms) =>
      match p[[pc]] with
      | Some <{{ctarget}}> =>
        (*! *)
        (S_Running ((pc+1, r, m), smem, false, ms), ds, [])
        (*!! spec_ctarget_no_clear *)
        (*! (S_Running ((pc+1, r, m), smem, ct, ms), ds, []) *)
      | i =>
        if ct then (S_Fault, ds, []) else
        match i with
        | Some <{{branch e to l}}> =>
          or_undef_ds ds (
            d <- hd_error ds;;
            b' <- is_dbranch d;;
            n <- to_nat (eval r e);;
            let b := not_zero n in
            let ms' := ms || negb (Bool.eqb b b') in
            let pc' := if b' then C.of_label l else (pc+1) in
            ret (S_Running ((pc', r, m), smem, false, ms'), tl ds, [OBranch b]))
        | Some <{{x<-load[e]}}> =>
          or_undef_ds ds (
            n <- to_nat (eval r e);;
            v <- (if ms then Some (smem ! n) else nth_error m.(memory) n);;
            ret (S_Running ((pc+1, (x !-> v; r), m), smem, false, ms), ds, [OLoad n]))
        | Some <{{store[e]<-e'}}> =>
          or_undef_ds ds (
            n <- to_nat (eval r e);;
            let v := eval r e' in
            let m' := if ms then m else upd_mem n m v in
            ret (S_Running ((pc+1, r, m'), n !-> v; smem, false, ms), ds, [OStore n]))
        | Some <{{call e}}> =>
          or_undef_ds ds (
            d <- hd_error ds;;
            dpc <- is_dcall d;;
            pc' <- C.of_cptr p dpc;;
            l <- C.of_val (eval r e);;
            _sp <- to_nat (r ! sp);;
            let ra := C.to_val (pc+1) in
            let m' := if ms then m else upd_mem (S _sp) m ra in
            let ms' := ms || negb (C.pc_eqb pc' l) in
            (*! *)
            ret (S_Running ((pc', sp !-> N (S _sp); r, m'), S _sp !-> ra; smem, true, ms'), tl ds, [OCall (C.to_cptr p l) _sp])
            (*!! spec-call-no-set-ct *)
            (*! ret (S_Running ((pc', sp !-> N (S _sp); r, m'), S _sp !-> ra; smem, ct, ms'), tl ds, [OCall (C.to_cptr p l) _sp]) *)
            (*!! spec-call-push-pc *)
            (*! ret (S_Running ((pc', sp !-> N (S _sp); r, (if ms then m else upd_mem (S _sp) m (C.to_val pc))), S _sp !-> C.to_val pc; smem, true, ms'), tl ds, [OCall (C.to_cptr p l) _sp]) *)
            (*!! spec-call-no-sp-bump *)
            (*! ret (S_Running ((pc', r, m'), S _sp !-> ra; smem, true, ms'), tl ds, [OCall (C.to_cptr p l) _sp]) *)
            )
        | Some <{{ret}}> =>
          or_undef_ds ds (
            _sp <- to_nat (r ! sp);;
            v <- (if ms then Some (smem ! _sp) else nth_error m.(memory) _sp);;
            (* no code pointer in the slot: [exit] is the only terminator *)
            pc' <- C.of_val v;;
            d <- hd_error ds;;
            dpc <- is_dret d;;
            match dpc with
            (* If attacker issues DRet None, then we follow the sequential path *)
            | None =>
              ret (S_Running ((pc', sp !-> N (_sp - 1); r, m), smem, false, ms), tl ds, [ORet (C.to_cptr p pc') _sp])
            | Some dpc =>
              pc'' <- C.of_cptr p dpc;;
              is_true (C.wf_retb p pc'');;
              let ms' := ms || negb (C.pc_eqb pc' pc'') in
              (*! *)
              ret (S_Running ((pc'', sp !-> N (_sp - 1); r, m), smem, false, ms'), tl ds, [ORet (C.to_cptr p pc') _sp])
              (*!! spec-ret-no-sp-restore *)
              (*! ret (S_Running ((pc'', r, m), smem, false, ms'), tl ds, [ORet (C.to_cptr p pc') _sp]) *)
              (*!! spec-ret-observes-directive *)
              (*! ret (S_Running ((pc'', sp !-> N (_sp - 1); r, m), smem, false, ms'), tl ds, [ORet (C.to_cptr p pc'') _sp]) *)
            end)
        | Some _ =>
          match step p (S_Running (pc, r, m)) with
          | (S_Running c', o) => (S_Running (c', smem, false, ms), ds, o)
          | (S_Undef, o) => (S_Undef, ds, o)
          | (S_Fault, o) => (S_Fault, ds, o)
          | (S_Term, o) => (S_Term, ds, o)
          end
        | None => (S_Undef, ds, [])
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

Definition ideal_step (p: prog) (sic: state ideal_cfg) (ds: dirs): (state ideal_cfg * dirs * obs) :=
  match sic with
  | S_Running ((pc, r, m), smem, ms) =>
      match p[[pc]] with
      | Some <{{x <- div e1, e2}}> =>
        or_undef_ds ds (
          v1 <- (if ms then Some 0 else to_nat (eval r e1));;
          v2 <- (if ms then Some 0 else to_nat (eval r e2));;
          let res: val := match v2 with
            | 0 => UV
            | _ => N (div v1 v2)
            end
          in
          ret (S_Running ((pc+1, (x !-> res; r), m), smem, ms), ds, [ODiv v1 v2]))
      | Some <{{branch e to l}}> =>
        or_undef_ds ds (
          d <- hd_error ds;;
          b' <- is_dbranch d;;
          n <- (if ms then Some 0 else to_nat (eval r e));;
          let b := not_zero n in
          (*! *)
          let ms' := ms || negb (Bool.eqb b b') in
          (*!! ideal_branch_bad_update_ms *)
          (*! let ms' := negb (Bool.eqb b b') in *)
          let _ := I in
          (*! *)
          let pc' := if b' then C.of_label l else (pc+1) in
          (*!! ideal_branch_ignore_directive *)
          (*! let pc' := if b then C.of_label l else (pc+1) in *)
          ret (S_Running ((pc', r, m), smem, ms'), tl ds, [OBranch b]))
      | Some <{{call e}}> =>
        or_undef_ds ds (
          d <- hd_error ds;;
          dpc <- is_dcall d;;
          pc' <- C.of_cptr p dpc;;
          l <- (if ms then Some C.null_pc else C.of_val (eval r e));;
          _sp <- to_nat (r ! sp);;
          let entry := match C.is_proc_entry p pc' with Some b => b | None => false end in
          (*! *)
          if entry then
          (*!! ideal_call_no_check_target *)
          (*! if true then *)
            let ra := C.to_val (pc+1) in
            let m' := if ms then m else upd_mem (S _sp) m ra in
            let ms' := ms || negb (C.pc_eqb pc' l) in
            (*! *)
            ret (S_Running ((pc', sp !-> N (S _sp); r, m'), S _sp !-> ra; smem, ms'), tl ds, [OCall (C.to_cptr p l) _sp])
            (*!! ideal-call-push-at-sp *)
            (*! ret (S_Running ((pc', sp !-> N (S _sp); r, (if ms then m else upd_mem _sp m ra)), _sp !-> ra; smem, ms'), tl ds, [OCall (C.to_cptr p l) _sp]) *)
            (*!! ideal-call-no-sp-bump *)
            (*! ret (S_Running ((pc', r, m'), S _sp !-> ra; smem, ms'), tl ds, [OCall (C.to_cptr p l) _sp]) *)
          else ret (S_Fault, ds, [OCall (C.to_cptr p l) _sp]))
      | Some <{{x<-load[e]}}> =>
        or_undef_ds ds (
          (*! *)
          (* Don't mask loads from unmasked addresses (in particular, from stack) *)
          let i := if ms && negb (unmasked_addr e) then (ANum 0) else e in
          (*!! ideal-load-no-mask *)
          (*! let i := e in *)
          (*!! ideal-load-masks-spill-slot *)
          (*! let i := if ms then (ANum 0) else e in *)
          n <- to_nat (eval r i);;
          v <- (if ms then Some (smem ! n) else nth_error m.(memory) n);;
          ret (S_Running ((pc+1, (x !-> v; r), m), smem, ms), ds, [OLoad n]))
      | Some <{{store[e]<-e'}}> =>
        or_undef_ds ds (
          (* same exception as the load above *)
          (*! *)
          let i := if ms && negb (unmasked_addr e) then (ANum 0) else e in
          (*!! ideal-store-no-mask *)
          (*! let i := e in *)
          (*!! ideal-store-masks-spill-slot *)
          (*! let i := if ms then (ANum 0) else e in *)
          n <- to_nat (eval r i);;
          let v := eval r e' in
          let m' := if ms then m else upd_mem n m v in
          ret (S_Running ((pc+1, r, m'), n !-> v; smem, ms), ds, [OStore n]))
      | Some <{{ret}}> =>
        or_undef_ds ds (
          _sp <- to_nat (r ! sp);;
          (*! *)
          v <- (if ms then Some (C.to_val C.null_pc) else nth_error m.(memory) _sp);;
          (*!! ideal-ret-read-above-sp *)
          (*! v <- (if ms then Some (C.to_val C.null_pc) else nth_error m.(memory) (S _sp));; *)
          (*!! ideal-ret-no-mask *)
          (*! v <- (if ms then Some (smem ! _sp) else nth_error m.(memory) _sp);; *)
          (* no code pointer in the slot -- same rule as [step] and
             [spec_step]; [exit] is the only terminator *)
          pc' <- C.of_val v;;
          d <- hd_error ds;;
          dpc <- is_dret d;;
          let smem' := if ms then (_sp !-> v; smem) else smem in
          match dpc with
          | None =>
            ret (S_Running ((pc', sp !-> N (_sp - 1); r, m), smem', ms), tl ds, [ORet (C.to_cptr p pc') _sp])
          | Some dpc =>
            pc'' <- C.of_cptr p dpc;;
            MiniCET.is_true (C.wf_retb p pc'');;
            let ms' := ms || negb (C.pc_eqb pc' pc'') in
            (* the architectural target, as in [spec_step] *)
            (*! *)
            ret (S_Running ((pc'', sp !-> N (_sp - 1); r, m), smem', ms'), tl ds, [ORet (C.to_cptr p pc') _sp])
            (*!! ideal-ret-no-sp-restore *)
            (*! ret (S_Running ((pc'', r, m), smem', ms'), tl ds, [ORet (C.to_cptr p pc') _sp]) *)
            (*!! ideal-ret-observes-directive *)
            (*! ret (S_Running ((pc'', sp !-> N (_sp - 1); r, m), smem', ms'), tl ds, [ORet (C.to_cptr p pc'') _sp]) *)
            (*!! ideal-ret-no-slot-writeback *)
            (*! ret (S_Running ((pc'', sp !-> N (_sp - 1); r, m), smem, ms'), tl ds, [ORet (C.to_cptr p pc') _sp]) *)
          end)
      | Some _ =>
        match step p (S_Running (pc, r, m)) with
        | (S_Running c', o) => (S_Running (c', smem, ms), ds, o)
        | (S_Undef, o) => (S_Undef, ds, o)
        | (S_Fault, o) => (S_Fault, ds, o)
        | (S_Term, o) => (S_Term, ds, o)
        end
      | None => (S_Undef, ds, [])
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

End MachineSemantics.

Module MiniCETSemantics (M : TMap) := MachineSemantics M BlockCode.
