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

Notation "'_' '!->' v" := (M.init v)
    (at level 100, right associativity).
Notation "x '!->' v ';' m" := (M.t_update m x v)
    (at level 100, v at next level, right associativity).
Notation "m '!' x" := (M.t_apply m x)
    (at level 20, left associativity).
Notation "p '[[' pc ']]'" := (C.fetch p pc) : com_scope.
Notation "pc '+' '1'" := (C.next pc) : com_scope.

(* The speculative store buffer is keyed by address, so it cannot share the
   register notations above, which [M.t_update] fixes to string keys. *)
Notation "x '!s->' v ';' m" := (ListMaps.t_update m x v)
    (at level 100, v at next level, right associativity).
Notation "m '!s' x" := (ListMaps.apply m x)
    (at level 20, left associativity).

#[local] Existing Instance C.show_pc.

Definition pc := C.pc.
Definition fetch := C.fetch.
Definition ipc : pc := C.ipc.

Definition reg := M.t val.
Definition cfg : Type := (pc * reg) * mem.
Definition spec_mem := total_map nat val.
Definition spec_cfg : Type := ((cfg * spec_mem) * bool) * bool.
Definition ideal_cfg : Type := ((cfg * spec_mem)) * bool.

Definition dir := direction.
Definition dirs := list dir.

Definition ismem : spec_mem := @ListMaps.t_empty nat val UV.
Definition icfg (q : pc) (ireg : reg) (m : mem) : cfg := (q, ireg, m).

(* An address a real write cannot reach: [upd_mem] past the end is a silent
   no-op, so a speculative write there goes to the buffer instead. *)
Definition addr_oob (n : nat) (m : mem) : bool := stack_top m <=? n.

(* [UV] is the buffer's default, so it doubles as "nothing buffered here". *)
Definition read_buffered (n : nat) (m : mem) (smem : spec_mem) : option val :=
  if addr_oob n m
  then match smem !s n with UV => None | v => Some v end
  else get_mem n m.

Fixpoint eval (st : reg) (e: exp) : val :=
  match e with
  | ANum n => N n
  | AId x => M.t_apply st x
  | ABin b e1 e2 => eval_binop b (eval st e1) (eval st e2) C.max_in_domain
  | <{b ? e1 : e2}> =>
      match to_nat (eval st b) with
      | Some n1 => if not_zero n1 then eval st e1 else eval st e2
      | None => UV
      end
  | <{&l}> => C.eval_fptr l
  end.

(* The return address of the current frame, or None at the bottom of the
   stack.  Reads a code pointer through [C.of_val], so it keeps working for a
   machine whose code pointers are not [FP]. *)
Definition ret_addr (r : reg) (m : mem) : option pc :=
  sp <- to_nat (M.t_apply r "sp"%string);;
  v <- get_mem sp m;;
  C.of_val v.

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
              ret ((if b then C.of_label l else pc+1, r, m), [OBranch b])
            with
            | Some (c, o) => (S_Running c, o)
            | None => (S_Undef, [])
            end
          | <{{jump l}}> =>
            (S_Running (C.of_label l, r, m), [])
          | <{{x<-load[e]}}> =>
            match
              n <- to_nat (eval r e);;
              v' <- get_mem n m;;
              ret ((pc+1, (x !-> v'; r), m), [OLoad n])
            with
            | Some (c, o) => (S_Running c, o)
            | None => (S_Undef, [])
            end
          | <{{store[e]<-e'}}> =>
            match
              n <- to_nat (eval r e);;
              ret ((pc+1, r, upd_mem n m (eval r e')), [OStore n])
            with
            | Some (c, o) => (S_Running c, o)
            | None => (S_Undef, [])
            end
          | <{{call e}}> =>
            match
              l <- C.of_val (eval r e);;
              sp <- to_nat (M.t_apply r "sp");;
              ret ((l, "sp" !-> N (S sp); r, upd_mem (S sp) m (C.to_val (pc+1))), [OCall (C.to_cptr p l) sp])
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
              _pc' <- get_mem sp m;;
              ret (sp, _pc')
            with
            | None => (S_Undef, [])
            | Some (n, _pc') =>
              match C.of_val _pc' with
              (* bottom of the stack: this returns out of the program *)
              | None => if stack_empty n m then (S_Term, []) else (S_Undef, [])
              | Some pc' => (S_Running (pc', "sp" !-> N (eval_binop_nat BinMinus n 1 C.max_in_domain); r, m), [ORet (C.to_cptr p pc') n])
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
      let '(c, smem, ct, ms) := sc in
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
                let pc' := if b' then C.of_label l else (pc+1) in
                ret ((S_Running ((pc', r, m), smem, ct, ms'), tl ds), [OBranch b])
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
                dpc <- is_dcall d;;
                pc' <- C.of_cptr p dpc;;
                l <- C.of_val (eval r e);;
                sp <- to_nat (M.t_apply r "sp");;
                let ms' := ms || negb (C.pc_eqb pc' l) in
                if stack_top m <=? S sp then
                (* Update spec mem if stack out of bounds *)
                  ret ((S_Running ((pc', "sp" !-> N (S sp); r, m), ListMaps.t_update smem (S sp) (C.to_val (pc + 1)), true, ms'), tl ds), [OCall (C.to_cptr p l) sp])
                (*! *)
                else
                  ret ((S_Running ((pc', "sp" !-> N (S sp); r, upd_mem (S sp) m (C.to_val (pc+1))), smem, true, ms'), tl ds), [OCall (C.to_cptr p l) sp])
                (*!! spec-call-no-set-ct *)
                (*! ret ((S_Running ((pc', "sp" !-> N (S sp); r, upd_mem (S sp) m (C.to_val (pc+1))), smem, ct, ms'), tl ds), [OCall (C.to_cptr p l) sp]) *)
                (*!! spec-call-push-pc *)
                (*! ret ((S_Running ((pc', "sp" !-> N (S sp); r, upd_mem (S sp) m (C.to_val pc)), smem, true, ms'), tl ds), [OCall (C.to_cptr p l) sp]) *)
                (*!! spec-call-no-sp-bump *)
                (*! ret ((S_Running ((pc', r, upd_mem (S sp) m (C.to_val (pc+1))), smem, true, ms'), tl ds), [OCall (C.to_cptr p l) sp]) *)
            with
            | None => untrace "call fail" (S_Undef, ds, [])
            | Some (c, ds, os) => (c, ds, os)
            end
          | <{{ctarget}}> =>
            match
              (* is_true ct;; *)
              (*! *)
              (ret (S_Running ((pc+1, r, m), smem, false, ms), ds, []))
              (*!! spec_ctarget_no_clear *)
              (*! (ret (S_Running ((pc+1, r, m), smem, ct, ms), ds, [])) *)
            with
            | None => untrace "ctarget fail!" (S_Undef, ds, [])
            | Some (c, ds, os) => (c, ds, os)
            end
          | <{{ret}}> =>
            if ct then (S_Fault, ds, []) else
            match
              sp <- to_nat (M.t_apply r "sp");;
              (* Check the speculative cache *)
              _pc' <- match ListMaps.apply smem sp with
                | UV => get_mem sp m
                | pc' => Some pc'
              end;;
              ret (sp, _pc')
            with
            | None => untrace "ret: no return slot" (S_Undef, ds, [])
            | Some (n, _pc') =>
              match C.of_val _pc' with
              (* bottom of the stack: nothing was pushed there *)
              | None => if stack_empty n m then (S_Term, ds, []) else (S_Undef, ds, [])
              | Some pc' =>
                match
                  if seq.nilp ds then
                    untrace "Ret: Directions are empty!" None
                  else
                    d <- hd_error ds;;
                    dpc <- is_dret d;;
                    pc'' <- C.of_cptr p dpc;;
                    is_true (C.wf_retb p pc'');;
                    let ms' := ms || negb (C.pc_eqb pc' pc'') in
                    (*! *)
                    ret ((S_Running ((pc'', "sp" !-> N (eval_binop_nat BinMinus n 1 C.max_in_domain); r, m), smem, false, ms'), tl ds), [ORet (C.to_cptr p pc') n])
                    (*!! spec-ret-no-sp-restore *)
                    (*! ret ((S_Running ((pc'', r, m), smem, false, ms'), tl ds), []) *)
                    (*!! spec-ret-observes-directive *)
                    (*! ret ((S_Running ((pc'', "sp" !-> N (eval_binop_nat BinMinus n 1 C.max_in_domain); r, m), smem, false, ms'), tl ds), [ORet (C.to_cptr p pc'') n]) *)
                with
                | None => untrace "ret fail" (S_Undef, ds, [])
                | Some (c, ds, os) => (c, ds, os)
                end
              end
            end
          | <{{x<-load[e]}}> =>
            if ct then (S_Fault, ds, []) else
            match
              n <- to_nat (eval r e);;
              v' <- read_buffered n m smem;;
              ret ((S_Running ((pc+1, (x !-> v'; r), m), smem, false, ms), ds), [OLoad n])
            with
            | None => untrace "load fail" (S_Undef, ds, [])
            | Some (c, ds, os) => (c, ds, os)
            end
          | <{{store[e]<-e'}}> =>
            if ct then (S_Fault, ds, []) else
            match
              n <- to_nat (eval r e);;
              let v := eval r e' in
              if addr_oob n m then
                ret ((S_Running ((pc+1, r, m), n !s-> v ; smem, false, ms), ds), [OStore n])
              else
                ret ((S_Running ((pc+1, r, upd_mem n m v), smem, false, ms), ds), [OStore n])
            with
            | None => untrace "store fail" (S_Undef, ds, [])
            | Some (c, ds, os) => (c, ds, os)
            end
          | _ =>
            if ct then  (S_Fault, ds, [])
            else
              match step p (S_Running c) with
              | (S_Running c', o) => (S_Running (c', smem, false, ms), ds, o)
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

Definition ideal_step (p: prog) (sic: state ideal_cfg) (ds: dirs): (state ideal_cfg * dirs * obs) :=
  match sic with
  | S_Running ic =>
      let '(c, smem, ms) := ic in
      let '(pc, r, m) := c in
      match C.fetch p pc with
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
                  let pc' := if b' then C.of_label l else (pc+1) in
                  (*!! ideal_branch_ignore_directive *)
                  (*! let pc' := if b then C.of_label l else (pc+1) in *)
                  ret ((S_Running ((pc', r, m), smem, ms'), tl ds), [OBranch b])
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
                  dpc <- is_dcall d;;
                  pc' <- C.of_cptr p dpc;;
                  l <- (if ms then Some C.null_pc else C.of_val (eval r e));;
                  sp <- to_nat (M.t_apply r "sp"%string);;
                  entry <- C.is_proc_entry p pc';;
                  (*! *)
                  if (entry : bool) then
                  (*!! ideal_call_no_check_target *)
                  (*! if true then *)
                    let ms' := ms || negb (C.pc_eqb pc' l) in
                    if addr_oob (S sp) m then
                      ret ((S_Running ((pc', "sp"%string !-> N (S sp); r, m), S sp !s-> C.to_val (pc + 1); smem, ms'), tl ds), [OCall (C.to_cptr p l) sp])
                    else
                    (*! *)
                      ret ((S_Running ((pc', "sp"%string !-> N (S sp); r, upd_mem (S sp) m (C.to_val (pc+1))), smem, ms'), tl ds), [OCall (C.to_cptr p l) sp])
                    (*!! ideal-call-push-at-sp *)
                  (*! ret ((S_Running ((pc', "sp"%string !-> N (S sp); r, upd_mem sp m (C.to_val (pc+1))), ms'), tl ds), [OCall (C.to_cptr p l) sp]) *)
                    (*!! ideal-call-no-sp-bump *)
                    (*! ret ((S_Running ((pc', r, upd_mem (S sp) m (C.to_val (pc+1))), ms'), tl ds), [OCall (C.to_cptr p l) sp]) *)
                  else Some (S_Fault, ds, [OCall (C.to_cptr p l) sp])
                with
                | None => (S_Undef, ds, [])
                | Some (c, ds, os) => (c, ds, os)
                end
            | <{{x<-load[e]}}> =>
              match
                (*! *)
                (* Don't mask loads from unmasked addresses (in particular, from stack) *)
                let i := if ms && negb (unmasked_addr e) then (ANum 0) else e in
                (*!! ideal-load-no-mask *)
                (*! let i := e in *)
                (*!! ideal-load-masks-spill-slot *)
                (*! let i := if ms then (ANum 0) else e in *)
                n <- to_nat (eval r i);;
                v' <- read_buffered n m smem;;
                let c := (pc+1, (x !-> v'; r), m) in
                ret (S_Running (c, smem, ms), ds, [OLoad n])
              with
              | None => (S_Undef, ds, [])
              | Some (c, ds, os) => (c, ds, os)
              end
            | <{{store[e]<-e'}}> =>
              match
                (* same exception as the load above *)
                (*! *)
                let i := if ms && negb (unmasked_addr e) then (ANum 0) else e in
                (*!! ideal-store-no-mask *)
                (*! let i := e in *)
                (*!! ideal-store-masks-spill-slot *)
                (*! let i := if ms then (ANum 0) else e in *)
                n <- to_nat (eval r i);;
                let v := eval r e' in
                if addr_oob n m then
                  ret (S_Running ((pc+1, r, m), n !s-> v ; smem, ms), ds, [OStore n])
                else
                  ret (S_Running ((pc+1, r, upd_mem n m v), smem, ms), ds, [OStore n])
              with
              | None => (S_Undef, ds, [])
              | Some (c, ds, os) => (c, ds, os)
              end
            | <{{ret}}> =>
              match
                sp <- to_nat (M.t_apply r "sp"%string);;
                (*! *)
                _pc' <- read_buffered sp m smem;;
                (*!! ideal-ret-read-above-sp *)
                (*! _pc' <- get_mem (S sp) m;; *)
                ret (sp, _pc')
              with
              | None => untrace ("ideal ret: no return slot. PC: " ++ show pc ++ nl) (S_Undef, ds, [])
              | Some (n, _pc') =>
                let v := if ms then C.to_val C.null_pc else _pc' in
                (*!! ideal-ret-no-mask *)
                (*! let v := _pc' in *)
                match C.of_val v with
                (* bottom of the stack: nothing was pushed there -- same rule as
                   [step] and [spec_step] *)
                | None => if stack_empty n m then (S_Term, ds, []) else (S_Undef, ds, [])
                | Some pc' =>
                  match
                    if seq.nilp ds then
                      untrace ("ideal ret: Directions are empty!" ++ nl) None
                    else
                      d <- hd_error ds;;
                      dpc <- is_dret d;;
                      pc'' <- C.of_cptr p dpc;;
                      MiniCET.is_true (C.wf_retb p pc'');;
                      let ms' := ms || negb (C.pc_eqb pc' pc'') in
                      let m' := if addr_oob n m then m else upd_mem n m v in
                      let smem' := if addr_oob n m then n !s-> v ; smem else smem in
                      (* the architectural target, as in [spec_step] *)
                      (*! *)
                      ret ((S_Running ((pc'', "sp"%string !-> N (eval_binop_nat BinMinus n 1 C.max_in_domain); r, m'), smem', ms'), tl ds), [ORet (C.to_cptr p pc') n])
                      (*!! ideal-ret-no-sp-restore *)
                      (*! ret ((S_Running ((pc'', r, m'), smem', ms'), tl ds), []) *)
                      (*!! ideal-ret-observes-directive *)
                      (*! ret ((S_Running ((pc'', "sp"%string !-> N (eval_binop_nat BinMinus n 1 C.max_in_domain); r, m'), smem', ms'), tl ds), [ORet (C.to_cptr p pc'') n]) *)
                      (*!! ideal-ret-no-slot-writeback *)
                      (*! ret ((S_Running ((pc'', "sp"%string !-> N (eval_binop_nat BinMinus n 1 C.max_in_domain); r, m), smem, ms'), tl ds), [ORet (C.to_cptr p pc') n]) *)
                  with
                  | None => untrace ("ideal ret failed. PC: " ++ show pc ++ "; PROGRAM: " ++ show p ++ nl) (S_Undef, ds, [])
                  | Some (c, ds, os) => (c, ds, os)
                  end
                end
              end
          | _ =>
              match step p (S_Running c) with
              | (S_Running c', o) => (S_Running (c', smem, ms), ds, o)
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

End MachineSemantics.

Module MiniCETSemantics (M : TMap) := MachineSemantics M BlockCode.
