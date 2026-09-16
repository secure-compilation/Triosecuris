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
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Import MonadNotation. Open Scope monad_scope.
From SECF Require Import TestingLib.
From Stdlib Require Import String.

From SECF Require Import Utils Printing.
From SECF Require Import ListMaps MapsFunctor.
Require Import Stdlib.Classes.EquivDec.
From SECF Require Import MiniCET.
From SECF Require Import TestingSemantics ListMaps.

(*! Section testing_sync *)
Module Import MCC := MiniCETCommon(ListTotalMap).
Local Module Import MCSemantics := MiniCETSemantics(ListTotalMap).
Local Module Import IS := IdealStepSemantics(MCSemantics).

Definition gen_dbr : G dir :=
  b <- arbitrary;; ret (DBranch b).

Definition gen_dcall (pst: list nat) : G dir :=
  l <- (elems_ (0, 0) (proc_hd pst));; ret (DCall l).

Definition gen_dret (p: prog) : G dir :=
  l <- elems_ (0, 0) (wf_ret_addrs p);; ret (DRet l).

Instance ShowDirection : Show dir := {
  show dir := match dir with
    | DBranch b => ("DBranch " ++ show b)%string
    | DCall cptr => ("DCall " ++ show cptr)%string
    | DRet cptr => ("DRet" ++ show cptr)%string
  end
}.

(* Size of the stack region [gen_wt_mem] appends after the typed memory. *)
Definition stk_alloc := 10.

Definition lookup_sp (m : mem) (r : reg) : option cptr :=
    sp <- to_nat (r ! "sp");;
    pc_val <- nth_error m sp;;
    pc_fp <- to_fp pc_val;;
    ret pc_fp.

Definition is_br_or_call (i : inst) :=
  match i with
  | <{{branch _ to _}}> | <{{call _}}> => true
  | _                                  => false
  end.



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



Fixpoint map_opt {S T} (f: S -> option T) l : option (list T):=
  match l with
  | [] => Some []
  | a :: l' => a' <- f a;;
      l'' <- map_opt f l';;
      ret (a' :: l'')
  end.

Fixpoint fold_left_opt {S T} (f: T -> S -> option T) acc l : option T :=
  match l with
  | [] => Some acc
  | a :: l' => 
      a' <- f acc a;;
      fold_left_opt f a' l'
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

Definition sync_dir (p: prog) (d: direction) : option direction :=
  match d with
  | DRet pc => pc' <- ret_sync p pc;; ret (DRet pc')
  | d => Some d
  end.

Definition sync_dirs (p: prog) (ds: dirs) : option dirs :=
  map_opt (sync_dir p) ds.

(* Executable version of [val_match]: a pointer to a procedure entry is
   unchanged, since the hardened entry is the ctarget still at (l, 0); any other
   pointer is a return address, i.e. the pc just after a call, which in the
   hardened program is the msf check of that call's expansion ([ret_sync]). *)
Definition val_sync (p: prog) (v: val) : option val :=
  match v with
  | FP (l, 0) => Some (FP (l, 0))
  | FP pc => pc' <- ret_sync p pc;; Some (FP pc')
  | v => Some v
  end.

(* Registers are related pointwise by [val_match] as well, so one that holds a
   return address -- loaded off the stack, say -- has to be translated too. *)
Definition r_sync (p: prog) (r: reg) (ms: bool) : option reg :=
  let '(d, l) := r in
  d' <- val_sync p d;;
  l' <- map_opt (fun '(x, v) => v' <- val_sync p v;; Some (x, v')) l;;
  ret (msf !-> N (if ms then 1 else 0); (d', l')).

Definition spec_cfg_sync (p: prog) (ic: ideal_cfg): option spec_cfg :=
  let '(c, ms) := ic in
  let '(pc, r, m, stk) := c in
  pc' <- pc_sync p pc;;
  r' <- r_sync p r ms;;
  (* The stack lives in memory now, so the return addresses it holds are synced
     as part of the memory. This has to cover every cell, not just the slots
     listed in [stk]: a popped slot still holds the return address the caller
     left there, translated on the hardened side. [stk] itself is a list of
     slot indices and so is identical on both sides. *)
  (*! *)
  m' <- map_opt (val_sync p) m;;
  (*!! spec_cfg_sync-no-stack *)
  (*! let m' := m in *)
  ret (pc', r', m', stk, false, ms).

Definition steps_to_sync_point (tp: prog) (tsc: spec_cfg) (ds: dirs) : option nat :=
  let '(tc, ct, ms) := tsc in
  let '(pc, r, m, sk) := tc in

    blk <- nth_error tp (fst pc);;
    i <- nth_error (fst blk) (snd pc);;
    match i with
    | <{{x := _}}> => match (String.eqb x callee) with
                      | true => match tp[[pc+1]] with
                                    | Some i => match i with
                                                | <{{call _}}> => match ds with
                                                                  | [DCall lo] =>
                                                                                  let '(l, o) := lo in

                                                                                  blk <- nth_error tp l;;
                                                                                  i <- nth_error (fst blk) o;;

                                                                                  if (Bool.eqb (snd blk) true) && (o =? 0) then
                                                                                  (*! *)
                                                                                  Some 4
                                                                                  (*!! steps_to_sync_point-call-3 *)
                                                                                  (*! Some 3 *)
                                                                                  (*!! steps_to_sync_point-call-5 *)
                                                                                  (*! Some 5 *)
                                                                                  else None
                                                                  | _ => None
                                                                  end
                                                | _ => None
                                                end
                                    | None => None
                                    end
                      | false => match (String.eqb x msf) with
                                 | true => None
                                 | false => Some 1
                                 end
                      end
    | <{{ branch _ to _ }}> =>
                               match ds with
                               (*! *)
                               | [DBranch b] => Some (if b then 3 else 2)
                               (*!! step_to_sync_point-branch-always-3 *)
                               (*! | DBranch b :: _ => Some 3 *)
                               (*!! step_to_sync_point-branch-always-2 *)
                               (*! | DBranch b :: _ => Some 2 *)
                               (*!! step_to_sync_point-branch-inverted *)
                               (*! | DBranch b :: _ => Some (if b then 2 else 3) *)
                               | _ => None
                               end
    (* [ret] is compiled to [callee <- load[sp]; ret]: the load, the ret itself,
       and then the msf check sitting at the return address in the caller. *)
    | <{{x <- load[_]}}> =>
      match (String.eqb x callee) with
      | true => match tp[[pc+1]] with
                | Some <{{ret}}> => match ds with
                                   (*! *)
                                   | [DRet _] => Some 3
                                   (*!! steps_to_sync_point-ret-2 *)
                                   (*! | [DRet _] => Some 2 *)
                                   (*!! steps_to_sync_point-ret-4 *)
                                   (*! | [DRet _] => Some 4 *)
                                   | _ => None
                                   end
                | _ => Some 1
                end
      | false => Some 1
      end
    | _ => Some 1
    end.

Definition gen_pc_from_prog (p: prog) : G cptr :=
  iblk <- choose (0, max 0 (Datatypes.length(p) - 1)) ;;
  let blk := nth_default ([],false) p iblk in
  off <- choose (0, max 0 (Datatypes.length(fst blk) - 1));;
  ret (iblk, off).

Definition gen_wf_ret_addr (p: prog) : G cptr :=
  let addrs := wf_ret_addrs p in
  match addrs with
  | [] => ret (0, 0)
  | d :: _ => elems_ d addrs
  end.

Fixpoint gen_call_stack_from_prog_sized n (p: prog) : G (list cptr) :=
  match n with
  | 0 => ret []
  | S n' => liftM2 cons (gen_wf_ret_addr p) (gen_call_stack_from_prog_sized n' p)
  end.

(* [gen_wf_ret_addr] falls back to (0,0) when [p] has no call at all, and (0,0)
   is not a well-formed return address, so generate an empty stack instead. *)
Definition gen_call_stack (n: nat) (p: prog) : G (list cptr) :=
  if seq.nilp (wf_ret_addrs p) then ret [] else gen_call_stack_from_prog_sized n p.

(* Layout of the in-memory call stack, as implemented by [step]/[ideal_step] *)
Definition stk_slots (base: nat) (n: nat) : list nat := rev (seq (S base) n).

(* [stk] is given top first, like sk: its head goes to the highest slot. *)
Definition inject_stack_to_mem (stk: list cptr) (m: mem) (base: nat): mem :=
  List.fold_left (fun acc '(i, ptr) => upd i acc (FP ptr))
    (combine (stk_slots base (Datatypes.length stk)) stk) m.

(* Build a configuration whose call stack lives in the top [stk_alloc] cells of
   [m] (the region [gen_wt_mem] appends), keeping sp, sk and memory consistent. *)
Definition cfg_with_stack (pc: cptr) (r: reg) (m: mem) (stk: list cptr)
  (stk_alloc: nat) : cfg :=
  let base := Datatypes.length m - stk_alloc in
  let n := Datatypes.length stk in
  (pc, "sp"%string !-> N (base + n); r, inject_stack_to_mem stk m base,
   stk_slots base n).

Definition gen_directive_from_ideal_cfg (p: prog) (pst: list nat) (ic: ideal_cfg) : G dirs :=
  let '(c, ms) := ic in
  let '(pc, r, m, sk) := c in
  match p[[pc]] with
  | Some i =>
      match i with
      | <{{branch _ to _}}> =>
        d <- gen_dbr;;
        ret [d]
      | <{{call _}}> =>
        oneOf (
          d <- gen_dcall pst;;
          ret [d] ;;;
          [ pc <- gen_pc_from_prog p ;; ret [DCall pc] ]
        )
      | <{{ret}}> =>
        match sk with
        | [] => ret []
        | _ :: _ => d <- gen_dret p;; ret [d]
        end
      | _ => ret []
      end
  | None => untrace "lookup error" (ret [])
  end.

Definition get_directive_for_seq_behaviour (p: prog) (pst: list nat) (ic: ideal_cfg) : dirs :=
  let '(c, ms) := ic in
  let '(pc, r, m, sk) := c in
  match p[[pc]] with
  | Some i =>
      match i with
      | <{{branch e to _}}> =>
        match (to_nat (eval r e)) with
        | None => []
        | Some n => [DBranch (not_zero n)]
        end
      | <{{call e}}> =>
        match (to_fp (eval r e)) with
        | None => []
        | Some l => [DCall l]
        end
      | <{{ret}}> =>
        match sk with
        | [] => []
        | _ :: _ => 
          match lookup_sp m r with
          | Some pc => if wf_retb p pc then [DRet pc] else []
          | None => untrace "lookup error: wrong return stack lookup" ([])
          end
        end
      | _ => []
      end
  | None => untrace "lookup error" ([])
  end.

(* Instructions [ideal_step] refuses to execute without a directive. *)
Definition needs_dir (p: prog) (ic: ideal_cfg) : bool :=
  let '(c, _) := ic in
  let '(pc, _, _, sk) := c in
  match p[[pc]] with
  | Some <{{branch _ to _}}> | Some <{{call _}}> => true
  | Some <{{ret}}> => negb (seq.nilp sk)
  | _ => false
  end.

Definition gen_directive_triggering_misspec (p: prog) (pst: list nat) (ic: ideal_cfg) : G dirs :=
  let '(c, ms) := ic in
  let '(pc, r, m, sk) := c in
  match p[[pc]] with
  | Some i =>
      match i with
      | <{{branch e to _}}> =>
        match (to_nat (eval r e)) with
        | None => ret []
        (* [ideal_step] takes the branch on [(negb ms) && not_zero n], so that
           is the outcome the directive has to contradict. *)
        | Some n => ret [DBranch (negb ((negb ms) && not_zero n))]
        end
      | <{{call e}}> =>
        (* [ideal_step] calls (0, 0) while already mis-speculating. *)
        match (if ms then Some (0, 0) else to_fp (eval r e)) with
        | None => ret []
        | Some l =>
            let targets := (proc_hd pst) in
            let targets := filter (fun x => x <>b l) targets in
            match targets with
            | [] => ret []
            | e::tl => t <- elems_ e (e::tl);;
                       ret [DCall t]
            end
        end
      | <{{ret}}> =>
        match sk with
        | [] => ret []
        | _ :: _ =>
            match lookup_sp m r with
            | None => untrace "lookup_error: couldn't lookup sp" (ret [])
            | Some pc' =>
              let addrs := wf_ret_addrs p in
              let other_addrs := filter (fun x => negb (x ==b pc')) addrs in
              match other_addrs with
              | [] => ret []
              | e :: tl => t <- elems_ e (e :: tl);; ret [DRet t]
              end
            end
        end
      | _ => ret []
      end
  | None => untrace "lookup error" (ret [])
  end.

Theorem val_beq : forall (n m : val), {n = m} + {n <> m}.
Proof.
  dec_eq.
Defined.

Theorem observation_beq : forall (n m : observation), {n = m} + {n <> m}.
Proof.
  dec_eq.
Defined.
(* 
Scheme Equality for val.
Scheme Equality for observation. *)

Check (@equiv_decb cptr Logic.eq _ _).




Instance direction_EqDec : EqDec direction Logic.eq.
Proof.
  intros x y.
  destruct x, y; try (right; discriminate).
  - destruct (b' == b'0).
    + left. now rewrite e.
    + right. now intros [= H].
  - destruct (lo == lo0).
    + left. now rewrite e.
    + right. now intros [= H].
  - destruct (lo == lo0).
    + left. now rewrite e.
    + right. now intros [= H].
Defined.

(* Compute ([DBranch true] <>b []).
Compute ([] <>b [DBranch true]). *)


Definition spec_cfg_eqb_up_to_callee (st1 st2 : spec_cfg) :=
  let '(pc1, r1, m1, sk1, c1, ms1) := st1 in
  let '(pc2, r2, m2, sk2, c2, ms2) := st2 in
  (pc1 ==b pc2)
  && (sk1 ==b sk2)
  && (c1 ==b c2) && (ms1 ==b ms2)
  && (m1 ==b m2)
  && pub_equivb (t_empty public) r1 (callee !-> (r1 ! callee) ; r2).

Instance showCfg : Show cfg := {
  show '(pc, reg, mem, stk) := 
    ("pc: " ++ show pc ++ ";" ++ nl ++ "reg: " ++ show reg ++ ";" ++ nl ++ "mem: " ++ show mem ++ ";" ++ nl ++ "stk: " ++ show stk)%string
}.

Definition single_step_cc := (
  let stk_size := 3 in
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  let p := transform_load_store_prog c tm p in
  forAll (gen_reg_wt c pst) (fun rs1 =>
  forAll (gen_wt_mem tm pst stk_alloc) (fun m1 =>
  forAll (gen_pc_from_prog p) (fun pc =>
  forAll (gen_call_stack stk_size p) (fun stk =>
  forAll ( @arbitrary bool _)  (fun ms =>
  let icfg := (cfg_with_stack pc rs1 m1 stk stk_alloc, ms) in
  let '((_, reg, mem, stk'), _) := icfg in
  printTestCase ("Reg: " ++ nl ++ show reg ++ nl ++ "Injected mem: " ++ nl ++ show mem ++ nl)%string (
  printTestCase ("Hardened program:" ++ nl ++ show (uslh_prog p))%string (
  match (spec_cfg_sync p icfg) with
  | None => collect "hello"%string (checker false)
  | Some tcfg =>
      forAll (gen_directive_from_ideal_cfg p pst icfg) (fun ds =>
      match (sync_dirs p ds) with
      | None => collect "dir sync failed"%string (checker tt)
      | Some tds =>
      match ideal_step p (S_Running icfg) ds with
      | (S_Fault, _, oideal) =>
          match (steps_to_sync_point (uslh_prog p) tcfg tds) with
          | None => match spec_steps 4 (uslh_prog p) (S_Running tcfg) tds with
                    | (S_Fault, _, ospec) =>   (checker (obs_eqb oideal ospec))
                    | _ => trace "spec exec didn't fail"%string (checker false)
                    end
          | Some n => collect ("ideal step failed for "%string ++ show (p[[pc]]) ++ " but steps_to_sync_point was Some"%string)%string (checker tt)
          end
      | (S_Term, _, oideal) =>
          match (steps_to_sync_point (uslh_prog p) tcfg tds) with
          (* [callee <- load[sp]] and then the [ret] that terminates *)
          | None => match spec_steps 2 (uslh_prog p) (S_Running tcfg) tds with
                    | (S_Term, _, ospec) =>   (checker (obs_eqb oideal ospec))
                    | _ => trace "spec exec didn't terminate"%string (checker false)
                    end
          | Some n => collect ("ideal step failed for "%string ++ show (p[[pc]]) ++ " but steps_to_sync_point was Some"%string)%string (checker tt)
          end
      | (S_Running icfg', _, oideal) =>
          match (steps_to_sync_point (uslh_prog p) tcfg tds) with
          | None => trace "Ideal step succeeds, but steps_to_sync_point undefined" (checker false)
          | Some n => match spec_steps n (uslh_prog p) (S_Running tcfg) tds with
                      | (S_Running tcfg', _, ospec) => match (spec_cfg_sync p icfg') with
                                              | None => collect "sync fails "%string (checker tt)
                                              | Some tcfgref => match (spec_cfg_eqb_up_to_callee tcfg' tcfgref) with
                                                                | true =>   (checker (obs_eqb oideal ospec))
                                                                | false =>   (checker false)
                                                                end
                                              end
                      | (_, ds', os) => trace ("spec exec fails "%string ++ (show os) ++ show (uslh_prog p)) (checker false)
                      end
          end
      | _ => collect "ideal exec undef"%string (checker tt)
      end
      end
      )
  end
  ))))))))).

QuickChick single_step_cc.

Definition single_step_sf := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  let p' := transform_load_store_prog c tm p in
  forAll (gen_reg_wt c pst) (fun rs1 =>
  forAll (gen_wt_mem tm pst stk_alloc) (fun m1 =>
  forAll (gen_pc_from_prog p') (fun pc =>
  forAll (gen_call_stack 3 p') (fun stk =>
  let sc := cfg_with_stack pc rs1 m1 stk stk_alloc in
  match step p' (S_Running sc) with
  | (S_Undef, _) => trace ("seq exec fails sc: "%string ++ (show sc) ++ ", prog: "%string ++ show p' ++ " prog end!!!"%string) (checker false)
  | _ => checker true
  end)))))).

Definition single_step_ideal_sf := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  let p' := transform_load_store_prog c tm p in
  forAll (gen_reg_wt c pst) (fun rs1 =>
  forAll (gen_wt_mem tm pst stk_alloc) (fun m1 =>
  forAll (gen_pc_from_prog p') (fun pc =>
  forAll (gen_call_stack 3 p') (fun stk =>
  forAll (@arbitrary bool _) (fun ms =>
  let icfg := (cfg_with_stack pc rs1 m1 stk stk_alloc, ms) in
  forAll (gen_directive_from_ideal_cfg p' pst icfg) (fun ds =>
  match ideal_step p' (S_Running icfg) ds with
  | (S_Undef, _, _) => trace ("ideal exec fails sc: "%string ++ (show icfg) ++ ", prog: "%string ++ show p' ++ " prog end!!!"%string) (checker false)
  | _ => checker true
  end)))))))).




Definition single_step := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  let p := transform_load_store_prog c tm p in
  forAll (gen_reg_wt c pst) (fun rs1 =>
  forAll (gen_reg_wt c pst) (fun rs2 =>
  forAll (gen_wt_mem tm pst stk_alloc) (fun m1 =>
  forAll (gen_wt_mem tm pst stk_alloc) (fun m2 =>
  forAll (gen_pc_from_prog p) (fun pc =>
  forAll (gen_call_stack 3 p) (fun stk =>
  let icfg1 := (cfg_with_stack pc rs1 m1 stk stk_alloc, true) in
  let icfg2 := (cfg_with_stack pc rs2 m2 stk stk_alloc, true) in
  forAll (gen_directive_from_ideal_cfg p pst icfg1) (fun ds =>
  match (ideal_step p (S_Running icfg1) ds) with
  | (S_Running _, _, o1) =>
      match (ideal_step p (S_Running icfg2) ds) with
      | (S_Running _, _, o2) => checker (obs_eqb o1 o2)
      | _ => checker false
      end
  | (S_Undef, _, o1) =>
      match (ideal_step p (S_Running icfg2) ds) with
      | (S_Undef, _, o2) => checker (obs_eqb o1 o2)
      | _ => checker false
      end
  | (S_Fault, _, o1) =>
      match (ideal_step p (S_Running icfg2) ds) with
      | (S_Fault, _, o2) => checker (obs_eqb o1 o2)
      | _ => checker false
      end
  | (S_Term, _, o1) =>
      match (ideal_step p (S_Running icfg2) ds) with
      | (S_Term, _, o2) => checker (obs_eqb o1 o2)
      | _ => checker false
      end
  end
  ))))))))).

(*! QuickChick single_step. *)
QuickChick single_step.


Definition single_step_seq_ideal := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs1 =>
  forAll (gen_wt_mem tm pst stk_alloc) (fun m1 =>
  forAll (gen_pc_from_prog p) (fun pc =>
  forAll (gen_call_stack 3 p) (fun stk =>
  let cfg := cfg_with_stack pc rs1 m1 stk stk_alloc in
  let icfg := (cfg, false) in
  let ds := get_directive_for_seq_behaviour p pst icfg in
  match (step p (S_Running cfg)) with
  | (S_Running _, o1) =>
      match (ideal_step p (S_Running icfg) ds) with
      | (S_Running _, _, o2) => untrace (show o1 ++ " / " ++ show o2) (checker (obs_eqb o1 o2))
      | (S_Undef, _, _) => collect "ideal undef (non-wf stack)"%string (checker tt)
      | _ => untrace "not running" (checker false)
      end
  | (S_Undef, o1) =>
      match (ideal_step p (S_Running icfg) ds) with
      | (S_Undef, _, o2) => untrace (show o1 ++ " / " ++ show o2) (checker (obs_eqb o1 o2))
      | _ => untrace "not undef" (checker false)
      end
  | (S_Fault, o1) =>
      match (ideal_step p (S_Running icfg) ds) with
      | (S_Fault, _, o2) => untrace (show o1 ++ " / " ++ show o2) (checker (obs_eqb o1 o2))
      | _ => untrace "not fault" (checker false)
      end
  | (S_Term, o1) =>
      match (ideal_step p (S_Running icfg) ds) with
      | (S_Term, _, o2) => untrace (show o1 ++ " / " ++ show o2) (checker (obs_eqb o1 o2))
      | _ => untrace "not term" (checker false)
      end
  end
  )))))).
(*! QuickChick single_step_seq_ideal. *)
QuickChick single_step_seq_ideal.


Definition single_step_trigger := (
  forAll (gen_prog_wt_with_basic_blk 3 8) (fun '(c, tm, pst, p) =>
  forAll (gen_reg_wt c pst) (fun rs1 =>
  forAll (gen_wt_mem tm pst stk_alloc) (fun m1 =>
  forAll (gen_pc_from_prog p) (fun pc =>
  forAll (gen_call_stack 3 p) (fun stk =>
  let cfg := cfg_with_stack pc rs1 m1 stk stk_alloc in
  let icfg := (cfg, false) in
  forAll (gen_directive_triggering_misspec p pst icfg) (fun ds =>
  (* An empty [ds] here means no mis-speculating directive exists at this pc --
     a [ret] whose return address is the program's only well-formed one, say --
     and [ideal_step] would just report S_Undef for the missing direction. *)
  if seq.nilp ds && needs_dir p icfg then
    collect "no mis-speculating direction exists"%string (checker tt)
  else
  match (step p (S_Running cfg)) with
  | (S_Running _, o1) =>
      match (ideal_step p (S_Running icfg) ds) with
      | (S_Running icfg', _, o2) => untrace (show o1 ++ " / " ++ show o2) (checker ((obs_eqb o1 o2) && (match ds with [] => true | _ => snd icfg' end)))
      | (S_Undef, _, _) => collect "ideal undef (non-wf stack)"%string (checker false)
      | _ => untrace "not running" (checker false)
      end
  | (S_Undef, o1) =>
      match (ideal_step p (S_Running icfg) ds) with
      | (S_Undef, _, o2) => untrace (show o1 ++ " / " ++ show o2) (checker (obs_eqb o1 o2))
      | _ => untrace "not undef" (checker false)
      end
  | (S_Fault, o1) =>
      match (ideal_step p (S_Running icfg) ds) with
      | (S_Fault, _, o2) => untrace (show o1 ++ " / " ++ show o2) (checker (obs_eqb o1 o2))
      | _ => untrace "not fault" (checker false)
      end
  | (S_Term, o1) =>
      match (ideal_step p (S_Running icfg) ds) with
      | (S_Term, _, o2) => untrace (show o1 ++ " / " ++ show o2) (checker (obs_eqb o1 o2))
      | _ => untrace "not term" (checker false)
      end
  end
  ))))))).
(*! QuickChick single_step_trigger. *)
QuickChick single_step_trigger.
