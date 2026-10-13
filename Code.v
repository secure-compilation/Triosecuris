From Stdlib Require Import List Strings.String Bool.Bool Arith.PeanoNat.
Import Nat ListNotations.
Set Default Goal Selector "!".
From SECF Require Import MiniCET Utils Printing.
Require Import Stdlib.Classes.EquivDec.
From QuickChick Require Import QuickChick.
Require Export ExtLib.Structures.Monads.
Require Export ExtLib.Data.Monads.OptionMonad.
Import MonadNotation. Open Scope monad_scope.

(* The program representation and the program counter the semantics is run
   over.  [BlockCode] below is the (block, offset) machine; a flat
   instruction-index machine is the other intended instance. *)
(* [prog] is deliberately NOT abstract: a flat instruction index is an index
   into a block program, so both machines read the same [MiniCET.prog] and the
   generators, the hardening and the printers need no change. *)
Module Type Code.
  Parameter pc : Type.

  Parameter max_in_domain : nat.

  Parameter fetch    : prog -> pc -> option inst.
  Parameter next     : pc -> pc.
  Parameter of_label : nat -> pc.
  Parameter pc_eqb   : pc -> pc -> bool.
  Parameter ipc      : pc.
  Parameter null_pc  : pc.

  Parameter to_val    : pc -> val.
  Parameter of_val    : val -> option pc.
  Parameter eval_fptr : cptr -> val.

  (* [None] when the target names no block at all, which the semantics reports
     as S_Undef; [Some false] is a block that is not a procedure entry, which is
     S_Fault. *)
  Parameter is_proc_entry : prog -> pc -> option bool.
  Parameter wf_retb       : prog -> pc -> bool.

  (* Observations and directives stay in cptr, so the two machines' traces are
     comparable.  [to_cptr] is total; it takes the program because recovering a
     (block, offset) from a flat index needs it. *)
  Parameter to_cptr : prog -> pc -> cptr.
  Parameter of_cptr : prog -> cptr -> option pc.


  Declare Instance show_pc : Show pc.
End Code.

Module BlockCode <: Code.
  Definition pc : Type := cptr.

  Definition max_in_domain : nat := 4096.

  Definition fetch    : prog -> pc -> option inst := MiniCET.fetch.
  Definition next     : pc -> pc := MiniCET.inc.
  Definition of_label (l : nat) : pc := (l, 0).
  Definition pc_eqb   : pc -> pc -> bool := MiniCET.pc_eqb.
  Definition ipc      : pc := (0, 0).
  Definition null_pc  : pc := MiniCET.null_pc.

  Definition to_val    : pc -> val := FP.
  Definition of_val    : val -> option pc := to_fp.
  Definition eval_fptr : cptr -> val := FP.

  Definition is_proc_entry (p : prog) (q : pc) : option bool :=
    blk <- nth_error p (fst q);;
    Some (snd blk && (snd q ==b 0)).

  Definition wf_retb : prog -> pc -> bool := MiniCET.wf_retb.

  Definition to_cptr (_ : prog) (q : pc) : cptr := q.
  Definition of_cptr (_ : prog) (c : cptr) : option pc := Some c.


  #[export] Instance show_pc : Show pc := Printing.showCptr.
End BlockCode.
