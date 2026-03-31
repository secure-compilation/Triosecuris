(** MiniMIR **)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Strings.String String.
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

From SECF Require Import Utils.
From SECF Require Import MapsFunctor.
Require Import Stdlib.Classes.EquivDec.

Declare Custom Entry com.
Declare Scope com_scope.



Inductive binop : Type :=
  | BinPlus
  | BinMinus
  | BinMult
  | BinEq
  | BinLe
  | BinAnd
  | BinImpl.

Definition cptr : Type := nat * nat.

Variant val : Type :=
  | N (n:nat)
  | FP (pc: cptr)
  | UV.

Inductive ty : Type := | TNum | TPtr.

Definition not_zero (n : nat) : bool := negb (n =? 0).
Definition bool_to_nat (b : bool) : nat := if b then 1 else 0.

Definition eval_binop_nat (o:binop) (n1 n2 : nat) : nat :=
  match o with
  | BinPlus => n1 + n2
  | BinMinus => n1 - n2
  | BinMult => n1 * n2
  | BinEq => bool_to_nat (n1 =? n2)
  | BinLe => bool_to_nat (n1 <=? n2)
  | BinAnd => bool_to_nat (not_zero n1 && not_zero n2)
  | BinImpl => bool_to_nat (negb (not_zero n1) || not_zero n2)
  end.

Inductive exp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | ABin (o : binop) (e1 e2 : exp)
  | ACTIf (b : exp) (e1 e2 : exp)
  | FPtr (l : cptr).



Definition APlus := ABin BinPlus.
Definition AMinus := ABin BinMinus.
Definition AMult := ABin BinMult.
Definition BTrue := ANum 1.
Definition BFalse := ANum 0.
Definition BAnd := ABin BinAnd.
Definition BImpl := ABin BinImpl.
Definition BNot b := BImpl b BFalse.
Definition BOr e1 e2 := BImpl (BNot e1) e2.
Definition BEq := ABin BinEq.
Definition BNeq e1 e2 := BNot (BEq e1 e2).
Definition BLe := ABin BinLe.
Definition BGt e1 e2 := BNot (BLe e1 e2).
Definition BLt e1 e2 := BGt e2 e1.

Hint Unfold eval_binop_nat : core.
Hint Unfold APlus AMinus AMult : core.
Hint Unfold BTrue BFalse : core.
Hint Unfold BAnd BImpl BNot BOr BEq BNeq BLe BGt BLt : core.


Definition U : string := "U".
Definition V : string := "V".
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition AP : string := "AP".
Definition AS : string := "AS".
Definition msf : string := "msf".
Definition callee : string := "callee".

Coercion AId : string >-> exp.
Coercion ANum : nat >-> exp.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"   := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"   := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x < y"   := (BLt x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Notation "be '?' e1 ':' e2"  := (ACTIf be e1 e2)
                 (in custom com at level 20, no associativity).

Notation "'&' l"   := (FPtr l)
                        (in custom com at level 75,
                          l constr at level 0, right associativity).

Notation "<{{ e }}>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.

Open Scope com_scope.





Definition to_nat (v:val) : option nat :=
  match v with
  | N n => Some n
  | _ => None
  end.

Definition to_fp (v:val) : option cptr :=
  match v with
  | FP l => Some l
  | _ => None
  end.

Definition eval_binop (o:binop) (v1 v2 : val) : val :=
  match v1, v2 with
  | N n1, N n2 => N (eval_binop_nat o n1 n2)
  | FP l1, FP l2 =>
      match o with
      | BinEq => N (bool_to_nat ((fst l1 =? fst l2) && (snd l1 =? snd l2)))
      | _ => UV
      end
  | _, _ => UV
  end.

Inductive inst : Type :=
  | ISkip
  | IAsgn (x : string) (e : exp)
  | IDiv (x : string) (e1 : exp) (e2: exp)
  | IBranch (e : exp) (l : nat)
  | IJump (l : nat)
  | ILoad (x : string) (a : exp)
  | IStore (a : exp) (e : exp)
  | ICall (fp:exp)
  | ICTarget
  (*| IPeek (x : string)*)
  | IRet.

Notation "'skip'"  :=
  ISkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
  (IAsgn x y)
    (in custom com at level 0, x constr at level 0,
      y custom com at level 85, no associativity) : com_scope.
Notation "x '<-' 'div' e1 ',' e2" :=
  (IDiv x e1 e2)
    (in custom com at level 0, x constr at level 0,
    e1 custom com, e2 custom com, (* JB: unsure of the levels here, automatic ones seem fine? *)
      no associativity) : com_scope.
Notation "'branch' e 'to' l"  :=
  (IBranch e l)
     (in custom com at level 0, e custom com at level 85,
      l constr at level 0, no associativity) : com_scope.
Notation "'jump' l"  :=
  (IJump l)
     (in custom com at level 0,
      l constr at level 0, no associativity) : com_scope.
Notation "x '<-' 'load[' a ']'"  :=
  (ILoad x a)
     (in custom com at level 0, x constr at level 0,
      a custom com at level 85, no associativity) : com_scope.
Notation "'store[' a ']'  '<-' e"  :=
  (IStore a e)
     (in custom com at level 0, a custom com at level 0,
      e custom com at level 85,
         no associativity) : com_scope.
Notation "'call' e" :=
  (ICall e)
    (in custom com at level 89, e custom com at level 99) : com_scope.
Notation "'ctarget'"  :=
  ICTarget (in custom com at level 0) : com_scope.
(*Notation "x '<-' 'peek'" :=*)
  (*(IPeek x)*)
    (*(in custom com at level 0, x constr at level 0,*)
      (*no associativity) : com_scope.*)
Notation "'ret'"  :=
  IRet (in custom com at level 0) : com_scope.

Definition prog := list (list inst * bool).



Notation "'i[' x ; .. ; y ']'" := (cons x .. (cons y nil) ..)
  (in custom com at level 89, x custom com at level 99,
      y custom com at level 99, no associativity) : com_scope.

Check <{{ skip }}>.
Check <{{ i[skip ; skip ; skip] }}>.
Check <{ 1 + 2 }>.
Check <{ 2 = 1 }>.
Check <{{ Z := X }}>.
Check <{{ Z := X + 3 }}>.
Check <{{ Z <- div X, 2 }}>.
Check <{ true && ~(false && true) }>.
Check <{{ call 0 }}>.
Check <{{ ctarget }}>.
Check <{{ ret }}>.
Check <{{ branch 42 to 42 }}>.
Check <{{X<-load[8]}}>.
Check <{{store[X + Y]<- (Y + 42)}}>.


Definition mem := list val.

Inductive observation : Type :=
  | ODiv (n1 : nat) (n2 : nat)
  | OBranch (b:bool)
  | OLoad (n:nat)
  | OStore (n:nat)
  | OCall (l: cptr).
  (*JB: We don't need an observation for returns, correct? *)

Definition obs := list observation.

Definition observation_eqb (os1 : observation) (os2 : observation) : bool :=
  match os1, os2 with
  | OBranch b, OBranch b' => Bool.eqb b b'
  | OLoad i, OLoad i' => (i =? i')
  | OStore i, OStore i' => (i =? i')
  | OCall v, OCall v' => (fst v =? fst v') && (snd v =? snd v')
  | _, _ => false
  end.

Definition obs_eqb (o1 : obs) (o2 : obs) : bool :=
  forallb (fun '(os1, os2) => observation_eqb os1 os2) (List.combine o1 o2).

Definition fetch (p:prog) (pc:cptr) : option inst :=
  let '(l,o) := pc in
  r <- nth_error p l;;
  nth_error (fst r) o.

Notation "p '[[' pc ']]'" := (fetch p pc) : com_scope.

Definition inc (pc:cptr) : cptr :=
  let '(l,o) := pc in (l,o+1).

Notation "pc '+' '1'" := (inc pc) : com_scope.

Inductive direction : Type :=
  | DBranch (b':bool)
  | DCall (lo:cptr)
  | DRet (lo:cptr).

Definition dirs := list direction.

Definition is_true (b:bool) : option unit :=
  if b then Some tt else None.

Definition is_false (b:bool) : option unit :=
  if b then None else Some tt.

Definition is_dbranch (d:direction) : option bool :=
  match d with
  | DBranch b => Some b
  | _ => None
  end.

Definition is_dcall (d:direction) : option cptr :=
  match d with
  | DCall pc => Some pc
  | _ => None
  end.

Definition is_dret (d:direction) : option cptr :=
  match d with
  | DRet pc => Some pc
  | _ => None
  end.

Definition if_some {a:Type} (o:option a) (f:a->bool) : bool :=
  match o with
  | Some x => f x
  | None => true
  end.


Definition M (A: Type) := nat -> A * prog.

Definition uslh_ret {A: Type} (x: A) : M A :=
  fun c => (x, []).

Definition uslh_bind {A B: Type} (m: M A) (f: A -> M B) : M B :=
  fun c =>
    let '(r, p) := m c in
    let '(r', p') := f r (c + Datatypes.length p) in
    (r', p ++ p').

#[export] Instance monadUSLH : Monad M :=
  { ret := @uslh_ret;
    bind := @uslh_bind
  }.

(* Definition map2 {A B C} (f: A -> B -> C) (l1: list A) (l2: list B) : list C := *)
(*   map (fun '(a, b) => f a b) (combine l1 l2). *)

(* Definition mapM {A B C: Type} (f: A -> B -> M C) (l: list A) (pcl: list B) : M (list C) := *)
(*   sequence (map2 f l pcl). *)

Definition mapM {A B: Type} (f: A -> M B) (l: list A) : M (list B) :=
  sequence (List.map f l).

From SECF Require Import sflib.
Close Scope string_scope.
Require Import ExtLib.Structures.MonadLaws.

Lemma monadUSLH_law: MonadLaws monadUSLH.
Proof.
  econs; ii.
  - ss. unfold uslh_bind. ss. unfold M in *.
    extensionalities x.
    rewrite add_0_r.
    destruct (f a x) eqn:X. ss.
  - extensionalities x. ss.
    unfold uslh_bind.
    destruct (aM x) eqn:X; ss.
    unfold app. rewrite rev_append_correct.
    rewrite app_nil_r. unfold rev. rewrite rev_append_correct.
    rewrite app_nil_r. rewrite rev_involutive. reflexivity.
  - extensionalities x. ss.
    unfold uslh_bind, uslh_ret; ss.
    destruct (aM x) eqn:X; ss.
    destruct (f a (x + Datatypes.length p)) eqn:X1; ss.
    replace (x + Datatypes.length (app p p0)) with (x + Datatypes.length p + Datatypes.length p0).
    2:{ unfold app. rewrite rev_append_correct.
        unfold rev. rewrite rev_append_correct. rewrite app_nil_r.
        rewrite rev_involutive. rewrite length_app. rewrite add_assoc. reflexivity.
      }
    des_ifs. unfold app, rev. do 7 rewrite rev_append_correct.
    do 3 rewrite app_nil_r. do 3 rewrite rev_involutive. rewrite app_assoc.
    reflexivity.
Qed.

Lemma mapT_id_cons_to_bind :
  forall {M : Type -> Type} {Monad_M : Monad M} {ML: MonadLaws Monad_M}
         {A : Type} (hd : M A) (tl : list (M A)),
  mapT id (hd :: tl) = x <- hd ;; xs <- mapT id tl ;; ret (x :: xs).
Proof.
  i. unfold mapT, Traversable_list. ss.
  unfold apM, pure.
  unfold liftM.
  rewrite bind_of_return; auto.
  rewrite bind_associativity; auto.
  unfold id. ss.
  rewrite <- bind_associativity; auto.
  rewrite bind_associativity; auto.
  f_equal. extensionalities a.
  rewrite bind_of_return; auto.
Qed.

Lemma bind_inv {A B} m (f: A -> M B) c res np
    (BIND: bind m f c = (res, np)) :
  exists a pm rf pf,
    m c = (a, pm)
  /\ f a (c + Datatypes.length pm) = (rf, pf)
  /\ res = rf
  /\ np = pm ++ pf.
Proof.
  unfold bind, monadUSLH, uslh_bind in BIND.
  destruct (m c) eqn:MC.
  destruct (f a (c + Datatypes.length p)) eqn:FAC. clarify. esplits; eauto.
  eapply tr_app_correct.
Qed.

Lemma unfold_mapM A B (f: A -> M B) hd tl:
  mapM f (hd :: tl) = x <- f hd ;; xs <- mapM f tl ;; ret (x :: xs).
Proof.
  unfold mapM.
  assert (sequence (map f (hd :: tl)) = mapT id (f hd :: map f tl)) by ss.
  rewrite H.
  erewrite mapT_id_cons_to_bind; auto.
Unshelve.
apply monadUSLH_law.
Qed.

Lemma mapM_cons_inv {A B} (f: A -> M B) hd tl c res np
    (MM: mapM f (hd :: tl) c = (res, np)) :
  exists res_hd np_hd res_tl np_tl,
    f hd c = (res_hd, np_hd)
  /\ mapM f tl (c + Datatypes.length np_hd) = (res_tl, np_tl)
  /\ res = res_hd :: res_tl
  /\ np = np_hd ++ np_tl.
Proof.
  rewrite unfold_mapM in MM.
  exploit bind_inv; eauto. i. des. subst.
  exploit bind_inv; eauto. i. des. subst.
  ss. unfold uslh_ret in x3. clarify. ss.
  esplits; eauto. rewrite app_nil_r. auto.
Qed.

Lemma mapM_app_inv {A B} (f: A -> M B) l1 l2 c res np
    (MM: mapM f (l1 ++ l2) c = (res, np)) :
  exists res1 np1 res2 np2,
    mapM f l1 c = (res1, np1)
  /\ mapM f l2 (c + Datatypes.length np1) = (res2, np2)
  /\ res = res1 ++ res2
  /\ np = np1 ++ np2.
Proof.
  ginduction l1; ss; ii.
  { unfold mapM at 1. ss. unfold uslh_ret. esplits; eauto; ss.
    rewrite add_0_r. auto. }
  exploit mapM_cons_inv; eauto. i. des. subst.
  exploit IHl1; eauto. i. des. subst.
  rewrite <- add_assoc in x3. rewrite <- length_app in x3.

  assert (mapM f (a :: l1) c = (res_hd :: res1, np_hd ++ np1)).
  { clear - x0 x2. rewrite unfold_mapM.
    ss. unfold uslh_bind. rewrite x0. rewrite x2. ss. f_equal.
    do 2 rewrite tr_app_correct. rewrite app_nil_r. auto. }
  esplits; eauto. rewrite app_assoc. auto.
Qed.

Fixpoint foldM {A B: Type} (f : B -> A -> M B) (acc : B) (l: list A) : M B :=
  match l with
  | nil => ret acc
  | hd :: tl => el <- f acc hd;; foldM f el tl
  end.

Fixpoint fold_rightM {A B : Type} (f : A -> B -> M B) (l : list A) (init : B) : M B :=
  match l with
  | [] => ret init
  | hd :: tl => r <- fold_rightM f tl init;; f hd r
  end.

Definition concatM {A: Type} (m: M (list (list A))) : M (list A) :=
  xss <- m;; ret (List.concat xss).

Definition add_block (bl: list inst) (c: nat) := (c, [(bl, false)]).

Definition add_block_M (bl: list inst) : M nat :=
  fun c => add_block bl c.

Lemma mapM_perserve_len {A B} l (f: A -> M B) c res newp
  (MM: mapM f l c = (res, newp)) :
  Datatypes.length l = Datatypes.length res.
Proof.
  ginduction l; ss; ii.
  - unfold mapM in MM. ss.
    unfold uslh_ret in MM. clarify.
  - rewrite unfold_mapM in MM.
    unfold bind in MM. ss. unfold uslh_bind in MM.
    destruct (f a c) eqn:X. ss.
    destruct (mapM f l (c + Datatypes.length p)) eqn:X'; ss.
    eapply IHl in X'. rewrite X'. clarify.
Qed.

Definition uslh_inst (i: inst) (l: nat) (o: nat) : M (list inst) :=
  match i with
  | <{{ctarget}}> => ret [<{{skip}}>]
  | <{{x<-div e1,e2}}> => 
      let e1' := <{ (msf=1) ? 0 : e1 }> in
      let e2' := <{ (msf=1) ? 0 : e2}> in (*JB: Is masking to 0 fine here? *)
      ret [<{{x<-div e1', e2'}}>]
  | <{{x<-load[e]}}> =>
      let e' := <{ (msf=1) ? 0 : e }> in
      ret [<{{x<-load[e']}}>]
  | <{{store[e] <- e1}}> =>
      let e' := <{ (msf=1) ? 0 : e }> in
      ret [<{{store[e'] <- e1}}>]
  | <{{branch e to l}}> =>
      let e' := <{ (msf=1) ? 0 : e }> in
      l' <- add_block_M <{{ i[(msf := ((~e') ? 1 : msf)); jump l] }}>;;
      ret <{{ i[branch e' to l'; (msf := (e' ? 1 : msf))] }}>
  | <{{call e}}> =>
      let e' := <{ (msf=1) ? &(0,0) : e }> in
      let e'' := <{ callee = &((l, o + 2)) }> in
      ret <{{ i[callee:=e'; call e'; (msf := (e'' ? msf : 1))] }}>
  | <{{ret}}> =>
      ret <{{ i[callee <- load[AId "sp"%string]; ret] }}>
  | _ => ret [i]
  end.

Definition uslh_inst_sz (i: inst) : nat :=
  match i with
  | <{{branch _ to _}}> => 2
  | <{{call _}}> => 3
  | <{{ret}}> => 2
  | _ => 1
  end.

Fixpoint _offset_uslh (bl: list inst) (s: nat) : list nat :=
  match bl with
  | [] => []
  | i :: tl => s :: _offset_uslh tl (s + uslh_inst_sz i)
  end.

Definition add_index_uslh (bl: list inst) (is_proc: bool) : list (nat * inst) :=
  combine (_offset_uslh bl (if is_proc then 2 else 0)) bl.

Definition uslh_blk (nblk: nat * (list inst * bool)) : M (list inst * bool) :=
  let '(l, (bl, is_proc)) := nblk in
  let pcs := add_index_uslh bl is_proc in
  bl' <- concatM (mapM (fun '(o, i) => uslh_inst i l o) pcs);;
  if is_proc then
    ret (<{{ i[ctarget; msf := (callee = &(l,0)) ? msf : 1] }}> ++ bl', true)
  else
    ret (bl', false).

Definition uslh_prog (p: prog) : prog :=
  let idx_p := (add_index p) in
  let '(p',newp) := mapM uslh_blk idx_p (Datatypes.length p) in
  (p' ++ newp).

Fixpoint group_by_proc_impl (p: prog) (current_proc_acc: prog) : list prog :=
  match p with
  | [] => match current_proc_acc with
         | [] => []
         | _ => [rev current_proc_acc]
         end
  | (blk, is_proc) :: tl =>
      if is_proc then
        match current_proc_acc with
        | [] => group_by_proc_impl tl [(blk, is_proc)]
        | _ => (rev current_proc_acc) :: group_by_proc_impl tl [(blk, is_proc)]
        end
      else group_by_proc_impl tl ((blk, is_proc) :: current_proc_acc)
  end.

Definition group_by_proc (p: prog) : list prog :=
  group_by_proc_impl p [].

Definition sample_prog_for_grouping : prog := [
  (nil, true);
  (nil, false);
  (nil, false);
  (nil, true);
  (nil, false);
  (nil, true)
].

Compute (group_by_proc sample_prog_for_grouping).

Compute (Datatypes.length (group_by_proc sample_prog_for_grouping)).

Definition proc_map := (fun (x: prog) => Datatypes.length x).

Definition pst_calc (p: prog) : list nat := (map proc_map (group_by_proc p)).

Compute (pst_calc sample_prog_for_grouping).





Definition wf_label (p:prog) (is_proc:bool) (l:nat) : bool :=
  match nth_error p l with
  | Some (_,b) => Bool.eqb is_proc b
  | None => false
  end.

Fixpoint wf_exp (p:prog) (e : exp) : bool :=
  match e with
  | ANum _ | AId _ => true
  | ABin _ e1 e2 => wf_exp p e1 && wf_exp p e2
  | <{b ? e1 : e2}> => wf_exp p b && wf_exp p e1 && wf_exp p e2
  | <{&l}> => (snd l =? 0) && wf_label p true (fst l)
  end.

Definition wf_inst (p:prog) (i : inst) : bool :=
  match i with
  | <{{skip}}> | <{{ctarget}}> | <{{ret}}> => true
  | <{{_:=e}}> | <{{_<-load[e]}}> | <{{call e}}> => wf_exp p e
  | <{{_<-div e1, e2}}> => wf_exp p e1 && wf_exp p e2
  | <{{store[e]<-e'}}> => wf_exp p e && wf_exp p e'
  | <{{branch e to l}}> => wf_exp p e && wf_label p false l
  | <{{jump l}}> => wf_label p false l
  end.

Definition wf_blk (p:prog) (blb : list inst * bool) : bool :=
  forallb (wf_inst p) (fst blb).

Definition wf (p:prog) : bool :=
  forallb (wf_blk p) p.



Definition nonempty_block (blk: list inst * bool) : bool :=
  negb (seq.nilp (fst blk)).

Definition nonempty_block_prog (p: prog) : bool :=
  forallb nonempty_block p.

Definition block_terminator (blk: list inst * bool) : bool :=
  match (rev (fst blk)) with
  | [] => true
  | ihd::itl =>
      match ihd with
      | IRet | IJump _ => true
      | _ => false
      end
  end.

Definition block_terminator_prog (p: prog) : bool :=
  forallb block_terminator p.

Definition wf_direction (pc: cptr) (p: prog) (d: direction) : bool :=
  match d, p[[pc]] with
  | DBranch b, Some (IBranch e l) => is_some p[[(l, 0)]]

  | DCall pc', Some (ICall e) => is_some p[[pc']]
  | DRet (l, S o), Some (IRet) => match p[[(l, o)]] with 
                                  | Some (ICall e) => true
                                  | _ => false
                                  end
  | _, _ =>  false
  end.

Definition wf_dirs (pc: cptr) (p: prog) (ds: dirs) : bool :=
  forallb (wf_direction pc p) ds.

Definition nonempty_mem (m : mem) :Prop := (0 < Datatypes.length m)%nat.

Fixpoint e_unused (x:string) (e:exp) : Prop :=
  match e with
  | ANum n      => True
  | AId y       => y <> x
  | FPtr _      => True
  | ACTIf e1 e2 e3 => e_unused x e1 /\ e_unused x e2 /\ e_unused x e3
  | ABin _ e1 e2 => e_unused x e1 /\ e_unused x e2
  end.

Definition i_unused (x:string) (i:inst) : Prop :=
  match i with
  | <{{skip}}> | <{{jump _}}> | <{{ret}}> | <{{ctarget}}> => True
  | <{{y := e}}> => y <> x /\ e_unused x e
  | <{{branch e to l}}> => e_unused x e
  | <{{y <- load[i]}}> => y <> x /\ e_unused x i
  | <{{store[i] <- e}}> => e_unused x i /\ e_unused x e
  | <{{y <- div e1, e2}}> => y <> x /\ e_unused x e1 /\ e_unused x e2
  | <{{call e}}> => e_unused x e
  end.

Definition b_unused (x: string) (blk: list inst) : Prop :=
  Forall (fun i => i_unused x i) blk.

Definition unused_prog (x: string) (p:prog) : Prop :=
  let '(bs, cts) := split p in
  Forall (fun b => b_unused x b) bs.

Definition no_ct_inst (i: inst) : Prop :=
  match i with
  | <{{ctarget}}> => False
  | _ => True
  end.

Definition no_ct_blk (blk: list inst) : Prop :=
  Forall no_ct_inst blk.

Definition no_ct_prog (p:prog) : Prop :=
  let '(bs, cts) := split p in
  Forall no_ct_blk bs.

Inductive state A : Type :=
  | S_Running (a: A)
  | S_Undef
  | S_Fault
  | S_Term.
Arguments S_Running {A} a.
Arguments S_Undef {A}.
Arguments S_Fault {A}.
Arguments S_Term {A}.

Instance state_Monad : Monad state.
Proof.
  constructor.
  - intros T t.
    now apply S_Running.
  - intros T U st f.
    destruct st eqn: H.
    + now apply f.
    + apply S_Undef.
    + apply S_Fault.
    + apply S_Term.
Defined.

Module MiniCETCommon (M: TMap).

Notation "'_' '!->' v" := (M.init v)
    (at level 100, right associativity).
Notation "x '!->' v ';' m" := (M.t_update m x v)
    (at level 100, v at next level, right associativity).
Notation "m '!' x" := (M.t_apply m x)
    (at level 20, left associativity).


Definition reg := M.t val.
Definition reg_init := M.init UV.


Definition no_callee_msf (r: reg) : Prop :=
  match (r ! msf), (r ! callee) with
  | UV, UV => True
  | _, _ => False
  end.

Definition cfg : Type := ((cptr*reg)*mem)*list cptr.
Definition spec_cfg : Type := ((cfg * bool) * bool).
Definition ideal_cfg : Type := cfg * bool.

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


Definition final_spec_cfg (p: prog) (sc: spec_cfg) : bool :=
  let '(c, ct, ms) := sc in
  let '(pc, rs, m, stk) := c in
  match fetch p pc with
  | Some i => match i with
             | IRet => if seq.nilp stk then true else false
             | ICTarget => if ct
                          then false
                          else true
             | _ => false
             end
  | None => false
  end.

End MiniCETCommon.
