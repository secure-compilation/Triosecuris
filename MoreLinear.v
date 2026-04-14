

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat. Import Nat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import Classes.EquivDec.
From Stdlib Require Import String.

Set Default Goal Selector "!".

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.

Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Structures.Traversable.
Require Import ExtLib.Data.List.
Require Import ExtLib.Data.Monads.OptionMonad.
Import MonadNotation. Open Scope monad_scope.

From SECF Require Import Utils.
From SECF Require Import MapsFunctor.
From SECF Require Import MiniCET.
From SECF Require Import sflib.

Inductive ty : Type := TNum.

Derive (Arbitrary, Shrink) for ty.
Derive Show for ty.

Inductive observation : Type :=
| ODiv (n1 : nat) (n2 : nat)
| OBranch (b:bool)
| OLoad (n:nat)
| OStore (n:nat)
| OCall (l: nat).

Definition obs := list observation.

Definition ty_eqb (x y: ty) := match x, y with
                               | TNum, TNum => true
                               end.


Fixpoint coord_to_flat_idx {X} (ll: list (list X)) (c: nat * nat) : option nat :=
  let '(a, b) := c in
  match ll with
  | [] => None
  | l :: ls => match a with
             | 0 => if (b <? Datatypes.length l)%nat then Some b else None
             | S a' => match coord_to_flat_idx ls (a', b) with
                      | Some idx => Some (Datatypes.length l + idx)
                      | None => None
                      end
             end
  end.

Fixpoint flat_idx_to_coord {X} (ll: list (list X)) (idx: nat) : option (nat * nat) :=
  match ll with
  | [] => None
  | l :: ls =>
      let len := Datatypes.length l in
      if (idx <? len)%nat then Some (0, idx)
      else
        match flat_idx_to_coord ls (idx - len) with
        | Some (a', b') => Some (S a', b')
        | _ => None
        end
  end.

Lemma coord_flat_inverse
    A (ll: list (list A)) a b idx
    (CTI: coord_to_flat_idx ll (a, b) = Some idx) :
  flat_idx_to_coord ll idx = Some (a, b).
Proof.
  ginduction ll; i; ss.
  destruct ((idx <? Datatypes.length a)%nat) eqn:E.
  { des_ifs. eapply IHll in Heq. clear -E.
    exfalso. rewrite ltb_lt in E. lia. }
  des_ifs.
  - eapply IHll in Heq0.
    rewrite add_comm in Heq.
    rewrite add_sub in Heq. clarify.
  - eapply IHll in Heq0.
    rewrite add_comm in Heq.
    rewrite add_sub in Heq. clarify.
Qed.

Lemma flat_coord_inverse
    A (ll: list (list A)) a b idx
    (ITC: flat_idx_to_coord ll idx = Some (a, b)) :
  coord_to_flat_idx ll (a, b) = Some idx.
Proof.
  ginduction ll; ii; ss.
  destruct ((idx <? Datatypes.length a)%nat) eqn:E; clarify.
  rewrite ltb_ge in E.
  des_ifs.
  - eapply IHll in Heq0. clarify. f_equal. lia.
  - eapply IHll in Heq0. clarify.
Qed.

Definition pc_inj (p: MiniCET.prog) (len: nat) (pc: MiniCET.cptr) : option nat :=
  let fstp := map fst p in
  match coord_to_flat_idx fstp pc with
  | Some n => Some (n + len)
  | _ => None
  end.

Lemma coord_to_flat_idx_inject {X} (p: list (list X)) pc1 pc2 pc1' pc2'
  (DIFF: pc1 <> pc2)
  (INJ1: coord_to_flat_idx p pc1 = Some pc1')
  (INJ2: coord_to_flat_idx p pc2 = Some pc2') :
  pc1' <> pc2'.
Proof.
  ginduction p; ss; ii.
  { destruct pc1; ss. }
  des_ifs_safe. des_ifs.
  { rewrite ltb_lt in Heq. lia. }
  { rewrite ltb_lt in Heq0. lia. }
  assert ((n4, n2) <> (n3, n0)).
  { ii. eapply DIFF. inv H. auto. }
  exploit IHp; eauto. lia.
Qed.

Lemma pc_inj_inject p pc1 pc2 l pc1' pc2'
  (DIFF: pc1 <> pc2)
  (INJ1: pc_inj p l pc1 = Some pc1')
  (INJ2: pc_inj p l pc2 = Some pc2') :
  pc1' <> pc2'.
Proof.
  unfold pc_inj in *. des_ifs. ii.
  exploit coord_to_flat_idx_inject; eauto. lia.
Qed.

Definition pc_inj_inv (p: MiniCET.prog) (l: nat) (pc: nat) : option cptr :=
  let fstp := map fst p in
  flat_idx_to_coord fstp (sub pc l).

Definition flat_fetch (p: MiniCET.prog) (l: nat) (pc: nat) : option inst :=
  match pc_inj_inv p l pc with
  | Some pc' => fetch p pc'
  | _ => None
  end.



Lemma pc_inj_total p len pc i
  (INBDD: fetch p pc = Some i) :
  exists pc', pc_inj p len pc = Some pc'.
Proof.
  unfold pc_inj, MiniCET.fetch in *. destruct pc as (l & o).
  ginduction p; ss; ii; clarify.
  - rewrite nth_error_nil in INBDD; clarify.
  - rewrite nth_error_cons in INBDD.
    destruct l as [|l'] eqn:Hl.
    + assert (nth_error (fst a) o <> None) by (unfold not; i; clarify).
      rewrite nth_error_Some in H.
      rewrite <- ltb_lt in H. rewrite H.
      eauto.
    + specialize IHp with (l:=l') (o:=o) (i:=i).
      des_ifs; eauto.
Qed.

Definition prog := list inst.

Definition fetch (p: prog) (len: nat) (pc: nat) : option inst :=
  nth_error p (pc - len).

Inductive direction : Type :=
| DBranch (b':bool)
| DCall (l:nat)
| DRet (l:nat).

Definition dirs := list direction.

Definition is_dbranch (d:direction) : option bool :=
  match d with
  | DBranch b => Some b
  | _ => None
  end.

Definition is_dcall (d:direction) : option nat :=
  match d with
  | DCall pc => Some pc
  | _ => None
  end.

Definition val_injectb (p: MiniCET.prog) (len: nat) (vsrc vtgt: val) : bool :=
  match vsrc, vtgt with
  | FP l, N n => match pc_inj p len l with
                | Some n' => Nat.eqb n n'
                | None => false
                end
  | N n, N n' => Nat.eqb n n'
  | UV, _ => true
  | _, _ => false
  end.

Definition val_inject (p: MiniCET.prog) (len: nat) (vsrc vtgt: val) : Prop :=
  match vsrc, vtgt with
  | FP l, N n => match pc_inj p len l with
                | Some n' => (n = n')%nat
                | None => False
                end
  | N n, N n' => (n = n')
  | UV, _ => True
  | _, _ => False
  end.

Module MoreLinearCommon (M: TMap).

Notation "'_' '!->' v" := (M.init v)
    (at level 100, right associativity).
Notation "x '!->' v ';' m" := (M.t_update m x v)
    (at level 100, v at next level, right associativity).
Notation "m '!' x" := (M.t_apply m x)
    (at level 20, left associativity).

Definition reg := M.t val.
Definition reg_init := M.init UV.
Definition dir := direction.
Definition dirs := dirs.
Definition pc := nat.
Definition cfg : Type := ((pc * reg)* mem) * list pc.
Definition spec_cfg : Type := ((cfg * bool) * bool).
Definition ideal_cfg : Type := (cfg * bool)%type.
Definition ipc: pc := 0.
Definition istk: list pc := [].
Definition icfg (ipc : pc) (ireg : reg) (mem : mem) (istk : list pc): cfg :=
  (ipc, ireg, mem, istk).

Definition fetch := MoreLinear.fetch.

Definition no_fp (r: reg) : Prop :=
  forall x, match (to_fp (r ! x)) with
       | Some _ => False
       | None => True
       end.

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
  | <{&l}> => N 0
  end.

End MoreLinearCommon.

Fixpoint machine_exp (p: MiniCET.prog) (len: nat) (e: exp) : option exp :=
  match e with
  | ANum _ | AId _ => Some e
  | FPtr l => match pc_inj p len l with
             | Some l' => Some (ANum l')
             | None => None
             end
  | ABin o e1 e2 => match machine_exp p len e1, machine_exp p len e2 with
                   | Some e1', Some e2' => Some (ABin o e1' e2')
                   | _, _ => None
                   end
  | ACTIf e1 e2 e3 => match machine_exp p len e1, machine_exp p len e2, machine_exp p len e3 with
                     | Some e1', Some e2', Some e3' => Some (ACTIf e1' e2' e3')
                     | _, _, _ => None
                     end
  end.

Definition machine_inst (p: MiniCET.prog) (len: nat) (i: inst) : option inst :=
  match i with
  | <{{branch e to l}}> =>
    match machine_exp p len e, pc_inj p len (l, 0) with
    | Some e', Some l' => Some <{{ branch e' to l' }}>
    | _, _ => None
    end
  | <{{jump l}}> =>
    match pc_inj p len (l, 0) with
    | Some l' => Some <{{ jump l' }}>
    | _ => None
    end
  | ICall e =>
    match machine_exp p len e with
    | Some e' => Some (ICall e')
    | _ => None
    end
  | IAsgn x e =>
    match machine_exp p len e with
    | Some e' => Some (IAsgn x e')
    | _ => None
    end
  | IDiv x e1 e2 =>
    match machine_exp p len e1, machine_exp p len e2 with
    | Some e1', Some e2' => Some (IDiv x e1' e2')
    | _, _ => None
    end
  | ILoad x e =>
    match machine_exp p len e with
    | Some e' => Some (ILoad x e')
    | _ => None
    end
  | IStore e1 e2 =>
    match machine_exp p len e1, machine_exp p len e2 with
    | Some e1', Some e2' => Some (IStore e1' e2')
    | _, _ => None
    end
  | IPeek _ | ISkip | IRet | ICTarget => Some i
  end.

Definition transpose {X : Type} (l : list (option X)) : option (list X) :=
  fold_right (fun ox ol =>
                match ox, ol with
                | Some x, Some l => Some (x :: l)
                | _, _ => None
                end) (Some nil) l.

Definition machine_blk (p: MiniCET.prog) (len: nat) (blk: (list inst * bool)) : option (list inst) :=
  let ob := map (machine_inst p len) (fst blk) in
  transpose ob.

Definition _machine_prog  (p_ctx: MiniCET.prog) (p: MiniCET.prog) (len: nat) : option prog :=
  let op := map (machine_blk p_ctx len) p in
  let op' := transpose op in
  match op' with
  | Some lp => Some (List.concat lp)
  | _ => None
  end.

Definition machine_prog (p: MiniCET.prog) (len: nat) : option prog :=
  _machine_prog p p len.

Module SimCommon (M: TMap).

Module MiniC := MiniCETCommon(M).
Import MiniC.

Module MoreLinearC := MoreLinearCommon(M).
Import MoreLinearC.

Definition regs := MiniC.reg.
Definition regt := MoreLinearC.reg.

Definition reg_inject (p: MiniCET.prog) (len: nat) (r1: regs) (r2: regt) : Prop :=
  forall x, val_inject p len (r1 ! x) (r2 ! x).

Lemma eval_binop_inject p len o v1 v1' v2 v2'
  (INJ1: val_inject p len v1 v1')
  (INJ2: val_inject p len v2 v2') :
  val_inject p len (eval_binop o v1 v2) (eval_binop o v1' v2').
Proof.
  red in INJ1, INJ2. des_ifs. destruct o; ss.
  f_equal.
  assert (DEC: pc1 = pc0 \/ pc1 <> pc0).
  { clear. destruct pc1 as [l1 o1]. destruct pc0 as [l0 o0].
    destruct (Nat.eq_dec l1 l0); destruct (Nat.eq_dec o1 o0); auto.
    1-3: right; ii; clarify. }
  des; subst; clarify.
  { repeat rewrite Nat.eqb_refl. auto. }
  hexploit pc_inj_inject; [|eapply Heq0|eapply Heq|]; auto.
  ii. rewrite <- Nat.eqb_neq in H. rewrite H.
  rewrite andb_lazy_alt.
  destruct pc1 as [l1 o1]. destruct pc0 as [l0 o0].
  ss. des_ifs. rewrite Nat.eqb_neq. rewrite Nat.eqb_eq in Heq1.
  ii. subst; clarify.
Qed.

Lemma eval_inject p len r1 r2 e1 e2
  (INJ: reg_inject p len r1 r2)
  (TRANS: machine_exp p len e1 = Some e2) :
  val_inject p len (MiniC.eval r1 e1) (MoreLinearC.eval r2 e2).
Proof.
  ginduction e1; ss; ii; clarify.
  - des_ifs. ss.
    hexploit IHe1_1; eauto. intros INJ1. hexploit IHe1_2; eauto. intros INJ2.
    eapply (eval_binop_inject p len o); eauto.
  - des_ifs_safe. hexploit IHe1_1; eauto. i. ss.
    destruct (MiniC.eval r1 e1_1); ss; auto. des_ifs_safe. ss. clarify.
    des_ifs.
    + hexploit IHe1_2; eauto.
    + hexploit IHe1_3; eauto.
  - des_ifs. ss. clarify.
Qed.

End SimCommon.

