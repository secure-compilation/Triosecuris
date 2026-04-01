From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Arith.EqNat.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import List. Import ListNotations.
Set Default Goal Selector "!".
Require Import Stdlib.Classes.EquivDec.

From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Data.List.
Import MonadNotation.

From SECF Require Import MiniCET MapsFunctor ListMaps Shrinking.
Module Import MCC := MiniCETCommon(ListTotalMap).

Definition label := bool.

Definition public : label := true.
Definition secret : label := false.

Definition pub_vars := ListTotalMap.t label.
Definition pub_arrs := ListTotalMap.t label.

Notation t_apply := ListTotalMap.t_apply.

Definition pub_equiv (P : ListTotalMap.t label) {X:Type} (s1 s2 : ListTotalMap.t X) :=
  forall x:string, t_apply P x = true -> t_apply s1 x = t_apply s2 x.

Definition pub_equivb (P : ListTotalMap.t label) {X:Type} `{EqDec X} (s1 s2 : ListTotalMap.t X) : bool :=
  match P, s1, s2 with
  | (dP,mP), (d1,m1), (d2,m2) =>
      if dP
      then forallb (fun x => if t_apply P x
                             then (t_apply s1 x) ==b (t_apply s2 x) else true)
                   (union (map_dom mP) (union (map_dom m1) (map_dom m2)))
           && (d1 ==b d2)
      else forallb (fun x => if t_apply P x
                             then (t_apply s1 x) ==b (t_apply s2 x) else true)
                   (map_dom mP)
  end.

Inductive Forall3 {A B C} (P : A -> B -> C -> Prop) : list A -> list B -> list C -> Prop :=
  | Forall3_nil : Forall3 P [] [] []
  | Forall3_cons x y z l k k' :
    P x y z -> Forall3 P l k k' -> Forall3 P (x :: l) (y :: k) (z :: k').

Definition pub_equiv_list (P: list label) {X:Type} (m1 m2: list X) :=
  Forall3 (fun (a:label) (b:X) (c:X) => if a then b = c else True) P m1 m2.

Fixpoint forallb3 {A B C} (P : A -> B -> C -> bool) (a: list A) (b: list B) (c: list C) : bool :=
  match a, b, c with
  | [], [], [] => true
  | hdp::tlp, hd1::tl1, hd2::tl2 => (P hdp hd1 hd2) && (forallb3 P tlp tl1 tl2)
  | _, _, _ => false
  end.

Definition pub_equiv_listb (P: list label) {X:Type} `{EqDec X} (m1 m2: list X) :=
  forallb3 (fun (a:label) (b:X) (c:X) => if a then (b ==b c) else true) P m1 m2.

Definition gen_pub_equiv (P : ListTotalMap.t label) {X: Type} `{Gen X} (s: ListTotalMap.t X) : G (ListTotalMap.t X) :=
  let '(d, m) := s in
  new_m <- List.fold_left (fun (acc : G (Map X)) (c : string * X) => let '(k, v) := c in
    new_m <- acc;;
    new_v <- (if t_apply P k then ret v else arbitrary);;
    ret ((k, new_v)::new_m)
  ) m (ret []);;
  ret (d, new_m).

Definition gen_pub_vars : G pub_vars :=
  default <- arbitrary;;
  x0 <- arbitrary;;
  x1 <- arbitrary;;
  x2 <- arbitrary;;
  x3 <- arbitrary;;
  x4 <- arbitrary;;
  x5 <- arbitrary;;
  ret (
    "X0" !-> x0; "X1" !-> x1;
    "X2" !-> x2; "X3" !-> x3;
    "X4" !-> x4; "X5" !-> x5;
    _ !-> default
  ) % string.

#[export] Instance genVal : Gen val :=
  {arbitrary := freq [(2, n <- arbitrary;; ret (N n));
                      (1, l <- arbitrary;; ret (FP l))] }.

Definition val_eqb (v1 v2: val) : bool :=
  match v1, v2 with
  | N n1, N n2 => Nat.eqb n1 n2
  | FP (l1, o1), FP (l2, o2) => Nat.eqb l1 l2 && Nat.eqb o1 o2
  | UV, UV => true
  | _, _ => false
  end.

Notation "x =v y" := (val_eqb x y) (at level 50).

Lemma val_eqb_spec:
  forall v1 v2, val_eqb v1 v2 = true <-> v1 = v2.
Proof.
  intros. split; intros.
  - destruct v1, v2; simpl in *; try discriminate.
    + rewrite Nat.eqb_eq in H. auto.
    + destruct pc. inversion H.
    + destruct pc, pc0; simpl in *.
      eapply andb_prop in H. destruct H.
      rewrite Nat.eqb_eq in H, H0. subst. auto.
    + destruct pc. inversion H.
    + auto.
  - subst. unfold val_eqb. destruct v2; auto.
    { eapply Nat.eqb_refl. }
    destruct pc. repeat rewrite Nat.eqb_refl. auto.
Qed.

Lemma val_eqb_spec':
  forall v1 v2, val_eqb v1 v2 = false <-> v1 <> v2.
Proof.
  intros. split; intros.
  - destruct v1, v2; simpl in *; try discriminate.
    + rewrite Nat.eqb_neq in H. red. intros. inversion H0.
      subst. contradiction.
    + destruct pc, pc0; simpl in *. red. intros.
      inversion H0. subst. 
      repeat rewrite Nat.eqb_refl in H. simpl in H. inversion H.
  - destruct v1, v2; simpl in *; auto.
    + rewrite Nat.eqb_neq. red. intros. subst.
      apply H. auto.
    + destruct pc. auto.
    + destruct pc, pc0.
      destruct (n =? n1) eqn:X;
        destruct (n0 =? n2) eqn:Y; simpl; auto.
      rewrite Nat.eqb_eq in X, Y. exfalso. eapply H. subst; auto.
    + destruct pc. auto.
    + exfalso. eapply H. auto.
Qed.

Instance EqDec_val : EqDec val eq.
Proof.
  red. intros.
  destruct (val_eqb x y) eqn:Heqb.
  - rewrite val_eqb_spec in Heqb. subst.
    left. reflexivity.
  - rewrite val_eqb_spec' in Heqb.
    right. red. intros.
    inversion H. subst. eapply Heqb; auto.
Defined.

Definition gen_state : G (ListTotalMap.t val) :=
  d <- arbitrary;;
  v0 <- arbitrary;;
  v1 <- arbitrary;;
  v2 <- arbitrary;;
  v3 <- arbitrary;;
  v4 <- arbitrary;;
  v5 <- arbitrary;;
  ret (d, [("X0",v0); ("X1",v1); ("X2",v2);
           ("X3",v3); ("X4",v4); ("X5",v5)]) % string.

Definition gen_pub_mem : G (list label) :=
  x0 <- arbitrary;;
  x1 <- arbitrary;;
  x2 <- arbitrary;;
  x3 <- arbitrary;;
  x4 <- arbitrary;;
  x5 <- arbitrary;;
  ret ( [x0; x1; x2; x3; x4; x5]
  ) % string.

Definition gen_mem : G (list val) :=
  x0 <- arbitrary;;
  x1 <- arbitrary;;
  x2 <- arbitrary;;
  x3 <- arbitrary;;
  x4 <- arbitrary;;
  x5 <- arbitrary;;
  ret ( [x0; x1; x2; x3; x4; x5]
  ) % string.

Fixpoint _gen_pub_mem_equiv (P : list label) {X: Type} `{Gen X} (m: list X) : G (list X) :=
  match P, m with
  | [], [] => ret []
  | hdp::tlp, hdm::tlm =>
      hd <- (if hdp then ret hdm else arbitrary);;
      tl <-_gen_pub_mem_equiv tlp tlm;;
      ret (hd::tl)
  | _, _ => ret []
  end.

Fixpoint gen_pub_mem_equiv (P : list label) {X: Type} `{Gen X} (m: list X) : G (list X) :=
  if (Datatypes.length P =? Datatypes.length m)
  then _gen_pub_mem_equiv P m
  else ret [].

Fixpoint remove_one_secret (P: list label) {X: Type} (s: list X) : list (list X) :=
    match P, s with
    | [], [] => []
    | hp::tp, hr::tr =>
        let removed_one_items := (remove_one_secret tp tr) in
        let add_hd := List.map (fun tl => hr :: tl) removed_one_items in
        if hp
        then add_hd
        else tr :: removed_one_items
    | _, _ => []
    end.

Definition list_minus {X : Type} `{EqDec X} (l1 l2 : list X) : list X :=
  filter (fun x => negb (existsb (fun y => x ==b y) l2)) l1.

#[export] Instance EqDec_nat : EqDec nat eq.
Proof.
  red. intros.
  destruct (Nat.eqb x y) eqn:Heb.
  - rewrite Nat.eqb_eq in Heb. left. subst. reflexivity.
  - rewrite Nat.eqb_neq in Heb. right. red. intros. apply Heb.
    apply H.
Qed.

Definition eitherOf {A} (a : G A) (b : G A) : G A := freq [(1, a); (1, b)].


Notation " 'oneOf' ( x ;;; l ) " :=
  (oneOf_ x (cons x l))  (at level 1, no associativity) : qc_scope.

Notation " 'oneOf' ( x ;;; y ;;; l ) " :=
  (oneOf_ x (cons x (cons y l)))  (at level 1, no associativity) : qc_scope.





#[export] Instance genTotalMap (A:Type) `{Gen A} : Gen (ListTotalMap.t A) :=
  {arbitrary := (d <- arbitrary;;
                 v0 <- arbitrary;;
                 v1 <- arbitrary;;
                 v2 <- arbitrary;;
                 v3 <- arbitrary;;
                 v4 <- arbitrary;;
                 v5 <- arbitrary;;
                 ret (d,[("X0",v0); ("X1",v1); ("X2",v2);
                         ("X3",v3); ("X4",v4); ("X5",v5)])%string)}.

#[export] Instance genId : Gen string :=
  {arbitrary := (n <- freq [(10, ret 0);
                             (9, ret 1);
                             (8, ret 2);
                             (4, ret 3);
                             (2, ret 4);
                             (1, ret 5)];;
                 ret ("X" ++ show n)%string) }.


Notation " 'oneOf' ( x ;;; l ) " :=
  (oneOf_ x (cons x l))  (at level 1, no associativity) : qc_scope.

Notation " 'oneOf' ( x ;;; y ;;; l ) " :=
  (oneOf_ x (cons x (cons y l)))  (at level 1, no associativity) : qc_scope.

Derive Arbitrary for binop.
Derive Arbitrary for exp.
Derive Arbitrary for inst.

Definition is_defined (v:val) : bool :=
  match v with
  | UV => false
  | _ => true
  end.

Fixpoint max n m := match n, m with
                   | 0, _ => m
                   | _, 0 => n
                   | S n', S m' => S (max n' m')
                   end.

Derive (Arbitrary, Shrink) for ty.

Definition ty_eqb (x y: ty) := match x, y with
                               | TNum, TNum | TPtr, TPtr => true
                               | _, _ => false
                               end.

Definition rctx := ListTotalMap.t ty.
Definition tmem := list ty.

Fixpoint ty_of_exp (c : rctx) (e : exp) : ty :=
  match e with
  | ANum _ => TNum
  | AId x => c ! x
  | ABin _ _ _ => TNum

  | ACTIf _ _ x => ty_of_exp c x
  | FPtr _ => TPtr
end.

Definition filter_vars_by_ty (t: ty) (c: rctx) : list string :=
  filter (fun x => ty_eqb (c ! x) t) (map_dom (snd c)).

Definition is_ptr (c : rctx) (var : string) :=
  match c ! var with
  | TPtr => true
  | _ => false
  end.


Definition is_br_or_call (i : inst) :=
  match i with
  | <{{branch _ to _}}> | <{{call _}}> => true
  | _                                  => false
  end.




Fixpoint _gen_partition (fuel program_length: nat) : G (list nat) :=
  match fuel with
  | 0 => ret [program_length]
  | S fuel' =>
      match program_length with
      | O => ret []
      | S O => ret [1]
      | S (S program_length') => (k <- choose(1, program_length - 1);;
                     rest <- _gen_partition fuel' (program_length - k);;
                     ret (k :: rest))
      end
  end.

Definition gen_partition (pl: nat): G (list nat) := _gen_partition pl pl.

Fixpoint proc_hd (pst: list nat) : list (nat * nat) :=
  match pst with
  | [] => []
  | hd :: tl => (0, 0) :: map (fun x => (fst x + hd, 0)) (proc_hd tl)
  end.

Compute (proc_hd [3; 3; 1; 1]).


Definition gen_callable (pl : nat) : G (list (nat * nat)) :=
  pst <- gen_partition pl ;; ret (proc_hd pst).

Definition gen_vars (len: nat) : G (list string) :=
  vectorOf len arbitrary.

Sample (gen_vars 5).

Definition ex_vars : list string :=
  ["X0"%string; "X1"%string; "X2"%string; "X3"%string; "X4"%string].

Fixpoint remove_dupes {a:Type} (eqb:a->a->bool) (t : list a) : list a :=
  match t with
  | [] => []
  | x :: xs => if existsb (eqb x) xs
               then      remove_dupes eqb xs
               else x :: remove_dupes eqb xs
  end.

#[export] Instance genTMem `{Gen ty} : Gen tmem :=
  {arbitrary := t <- arbitrary;;
                tm <- arbitrary;;
                ret (t :: tm) }.


Definition gen_exp_leaf_wt (t: ty) (c: rctx) (pst: list nat) : G exp :=
  match t with
  | TNum =>
      oneOf (liftM ANum arbitrary ;;;
               (let not_ptrs := filter (fun x => negb (is_ptr c x)) (map_dom (snd c)) in
                if seq.nilp not_ptrs then [] else
                  [liftM AId (elems_ "X0"%string not_ptrs)] ) )
  | _ =>
      oneOf (liftM FPtr (elems_ (0, 0) (proc_hd pst));;;
               (let ptrs := filter (fun x => (is_ptr c x)) (map_dom (snd c)) in
                if seq.nilp ptrs then [] else
                  [liftM AId (elems_ "X0"%string ptrs)] ) )
  end.

Fixpoint gen_exp_no_ptr_wt (sz : nat) (c : rctx) (pst: list nat) : G exp :=
  match sz with
  | O => gen_exp_leaf_wt TNum c []
  | S sz' =>
      freq [ (2, gen_exp_leaf_wt TNum c []);
             (sz, eitherOf
                    (liftM3 ABin arbitrary (gen_exp_no_ptr_wt sz' c pst) (gen_exp_no_ptr_wt sz' c pst))
                    (liftM2 (ABin BinEq) (gen_exp_leaf_wt TPtr c pst)  (gen_exp_leaf_wt TPtr c pst)));
             (sz, liftM3 ACTIf (gen_exp_no_ptr_wt sz' c pst) (gen_exp_no_ptr_wt sz' c pst) (gen_exp_no_ptr_wt sz' c pst))
          ]
  end
with gen_exp_ptr_wt (sz : nat) (c : rctx) (pst: list nat) : G exp :=
  match sz with
  | O => gen_exp_leaf_wt TPtr c pst
  | S sz' =>
      freq [ (2, gen_exp_leaf_wt TPtr c pst);
             (sz, liftM3 ACTIf (gen_exp_no_ptr_wt sz' c pst) (gen_exp_ptr_wt sz' c pst) (gen_exp_ptr_wt sz' c pst))
          ]
  end.

Fixpoint gen_exp_wt (sz: nat) (c: rctx) (pst: list nat) : G exp :=
  match sz with
  | O =>
      t <- arbitrary;;
      gen_exp_leaf_wt t c pst
  | S sz' =>
      freq [
          (2, t <- arbitrary;; gen_exp_leaf_wt t c pst);
          (sz, binop <- arbitrary;; match binop with
                | BinEq => eitherOf
                    (liftM2 (ABin BinEq) (gen_exp_no_ptr_wt sz' c pst) (gen_exp_no_ptr_wt sz' c pst))
                    (liftM2 (ABin BinEq) (gen_exp_leaf_wt TPtr c pst) (gen_exp_leaf_wt TPtr c pst))
                | _ => liftM2 (ABin binop) (gen_exp_no_ptr_wt sz' c pst) (gen_exp_no_ptr_wt sz' c pst)
              end);
             (sz, liftM3 ACTIf (gen_exp_no_ptr_wt sz' c pst) (gen_exp_wt sz' c pst) (gen_exp_wt sz' c pst))
          ]
  end.

Fixpoint gen_exp_ty_wt (t: ty) (sz: nat) (c: rctx) (pst: list nat) : G exp :=
  match t with
  | TNum => gen_exp_no_ptr_wt sz c pst
  | TPtr => gen_exp_ptr_wt sz c pst
  end.

Definition gen_val_wt (t: ty) (pst: list nat) : G val :=
  match t with
  | TNum => liftM N arbitrary
  | TPtr => match (proc_hd pst) with
           | [] => ret (FP (0, 0))
           | p::pst' => liftM FP (elems_ p (p::pst'))
           end
  end.

Definition gen_reg_wt (c: rctx) (pst: list nat) : G reg :=
  let wt_vars := snd c in
  let gen_binds := mapGen (fun '(name, t) =>  (v <- gen_val_wt t pst;; ret (name, v))) wt_vars in
  default_val <- gen_val_wt (fst c) pst;;
  b <- gen_binds;;
  ret (default_val, b).

Definition gen_asgn_wt (t: ty) (c: rctx) (pst: list nat) : G inst :=
  let tlst := filter (fun '(_, t') => ty_eqb t t') (snd c) in
  let vars := map_dom tlst in
  if seq.nilp vars
  then ret <{ skip }>
  else
    x <- elems_ "X0"%string vars;;
    a <- gen_exp_ty_wt t 1 c pst;;
    ret <{ x := a }>.

Definition add_zeros (l: list nat) : list (nat * nat) :=
  map (fun x => (x, 0)) l.

Definition gen_branch_wt (c: rctx) (pl: nat) (pst: list nat) (default : nat * nat) : G inst :=
  let vars := (map_dom (snd c)) in
  let jlst := (list_minus (add_zeros (seq 0 pl)) (proc_hd pst)) in
  e <- gen_exp_ty_wt TNum 1 c pst;;
  l <- elems_ default jlst;;
  ret <{ branch e to (fst l) }>.

Definition gen_jump_wt (pl: nat) (pst: list nat) (default : nat * nat) : G inst :=
  l <- elems_ default (list_minus (add_zeros (seq 0 pl)) (proc_hd pst));;
  ret <{ jump (fst l) }>.

Definition filter_typed {A : Type} (t : ty) (l : list (A * ty)): list A :=
  map fst (filter (fun '(_, t') => ty_eqb t t') l).

Notation " 'elems' ( h ;;; tl )" := (elems_ h (cons h tl))
  (at level 1, no associativity) : qc_scope.

Definition gen_load_wt (t: ty) (c: rctx) (tm: tmem) (pl: nat) (pst: list nat) : G inst :=
  let vars := filter_typed t (snd c) in
  sz <- choose(1, 3);;
  exp <- gen_exp_ty_wt TNum sz c pst;;
  match vars with
  | h :: tl =>
    x <- elems ( h ;;; tl);;
    ret <{ x <- load[exp] }>
  | _ => ret <{ skip }>
  end.

Definition gen_store_wt (c: rctx) (tm: tmem) (pl: nat) (pst: list nat) : G inst :=
  match tm with
  | h :: tl =>
    t <- elems (h ;;; tl);;
    e1 <- gen_exp_ty_wt TNum 1 c pst;;
    e2 <- gen_exp_ty_wt t 1 c pst;;
    ret <{ store[e1] <- e2 }>
  | _ => ret <{ skip }>
  end.

Definition compose_load_store_guard (t : ty) (id_exp : exp) (mem : tmem) : exp :=
  let indices := seq 0 (Datatypes.length mem) in
  let idx := filter_typed t (combine indices mem) in
  let tc := fold_left
            (fun acc x => BOr x acc)
            (map (fun id => <{{ id_exp = ANum id }}>) idx)
            <{{ false }}> in
  let mem_sz := ANum (Datatypes.length mem) in
  let guardc := BLt id_exp mem_sz in
  BAnd tc guardc.
Eval compute in (compose_load_store_guard TNum <{ AId "X0"%string }> [TNum ; TPtr; TNum ]).

Definition transform_load_store_inst (c : rctx) (mem : tmem) (acc : list inst) (i : inst) : M (bool * list inst) :=
  match i with
  | <{{ x <- load[e] }}> =>
      let t := t_apply c x in
      merge <- add_block_M acc;;
      new <- add_block_M <{{ i[ x <- load[e]; jump merge] }}>;;
      ret (true, <{{ i[branch (compose_load_store_guard t e mem) to new; jump merge] }}>)
  | <{{ store[e] <- e1 }}> =>
      merge <- add_block_M acc;;
      new <- add_block_M <{{ i[store[e] <- e1; jump merge] }}>;;
      ret (true, <{{ i[branch (compose_load_store_guard (ty_of_exp c e1) e mem) to new; jump merge] }}>)
  | _ => ret (false, [i])
  end.

Definition split_and_merge (c : rctx) (mem : tmem) (i : inst) (acc : list inst) : M (list inst) :=
  tr <- transform_load_store_inst c mem acc i;;
  let '(is_split, new_insts) := tr in


  if is_split then
    ret new_insts

  else

    ret (new_insts ++ acc).

Definition transform_load_store_blk (c : rctx) (mem : tmem) (nblk : list inst * bool): M (list inst * bool) :=
  let (bl, is_proc) := nblk in
  folded <- fold_rightM (split_and_merge c mem) bl <{{ i[ ret ] }}>;;
  ret (folded, is_proc).

Definition transform_load_store_prog (c : rctx) (mem : tmem) (p : prog) :=
  let '(p', newp) := mapM (transform_load_store_blk c mem) p (Datatypes.length p) in
  (p' ++ newp).



Definition gen_call_wt (c: rctx) (pst: list nat) : G inst :=
  e <- gen_exp_ptr_wt 1 c pst;;
  ret <{ call e }>.

Definition _gen_inst_wt (gen_asgn : ty -> rctx -> list nat -> G inst)
                        (gen_branch : rctx -> nat -> list nat -> nat * nat -> G inst)
                        (gen_jump : nat -> list nat -> nat * nat -> G inst)
                        (gen_load : ty -> rctx -> tmem -> nat -> list nat -> G inst)
                        (gen_store : rctx -> tmem -> nat -> list nat -> G inst)
                        (gen_call : rctx -> list nat -> G inst)
                        (c: rctx) (tm: tmem) (sz:nat) (pl: nat) (pst: list nat) : G inst :=
  let insts :=
     [ (1, ret ISkip);
       (1, ret IRet);
       (sz, t <- arbitrary;; gen_asgn t c pst);
       (sz, t <- arbitrary;; gen_load t c tm pl pst);
       (sz, gen_store c tm pl pst);
       (sz, gen_call c pst) ] in
  let non_proc_labels := list_minus (add_zeros (seq 0 pl)) (proc_hd pst) in
  match non_proc_labels with
  | nil => freq_ (ret ISkip) insts
  | hd :: _ => freq_ (ret ISkip) (insts ++ [ (2, gen_branch c pl pst hd) ])
  end.


Definition gen_nonterm_wt (gen_asgn : ty -> rctx -> list nat -> G inst)
                          (gen_load : ty -> rctx -> tmem -> nat -> list nat -> G inst)
                          (gen_store : rctx -> tmem -> nat -> list nat -> G inst)
                          (gen_call : rctx -> list nat -> G inst)
                          (c: rctx) (tm: tmem) (sz:nat) (pl: nat) (pst: list nat) : G inst :=
  freq [ (1, ret ISkip);
         (sz, t <- arbitrary;; gen_asgn t c pst);
         (sz, t <- arbitrary;; gen_load t c tm pl pst);
         (sz, gen_store c tm pl pst);
         (sz, gen_call c pst)].

Definition _gen_term_wt (gen_branch : rctx -> nat -> list nat -> nat * nat -> G inst)
                      (gen_jump : nat -> list nat -> nat * nat -> G inst)
                      (c: rctx) (tm: tmem)   (pl: nat) (pst: list nat) : G inst :=
  let non_proc_labels := list_minus (add_zeros (seq 0 pl)) (proc_hd pst) in
  match non_proc_labels with
  | nil => ret IRet
  | hd :: _ => freq_ (ret IRet) ([(1, ret IRet) ; (2, gen_jump pl pst hd)])
  end.

Definition gen_term_wt (c: rctx) (tm: tmem) (pl: nat) (pst: list nat) : G inst :=
  _gen_term_wt gen_branch_wt gen_jump_wt c tm pl pst.

Definition gen_inst_wt (c: rctx) (tm: tmem) (sz:nat) (pl: nat) (pst: list nat) : G inst :=
  _gen_inst_wt gen_asgn_wt gen_branch_wt gen_jump_wt gen_load_wt gen_store_wt gen_call_wt
               c tm sz pl pst.

Definition gen_blk_wt (c: rctx) (tm: tmem) (bsz pl: nat) (pst: list nat) : G (list inst) :=
  vectorOf bsz (gen_inst_wt c tm bsz pl pst).

Definition _gen_blk_body_wt (c: rctx) (tm: tmem) (bsz pl: nat) (pst: list nat) : G (list inst) :=
  vectorOf (bsz - 1) (gen_inst_wt c tm bsz pl pst).

Definition gen_blk_with_term_wt (c: rctx) (tm: tmem) (bsz pl: nat) (pst: list nat) : G (list inst) :=
  blk <- _gen_blk_body_wt c tm bsz pl pst;;
  term <- gen_term_wt c tm pl pst;;
  ret (blk ++ [term]).

Definition basic_block_checker (blk: list inst) : bool :=
  match blk with
  | [] => false
  | _ => match seq.last ISkip blk with
        | IRet | IJump _ => true
        | _ => false
        end
  end.

Definition basic_block_gen_example : G (list inst) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  gen_blk_with_term_wt c tm 8 8 [3; 3; 1; 1].

Fixpoint _gen_proc_with_term_wt (c: rctx) (tm: tmem) (fsz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret []
  | S fsz' => n <- choose (1, max 1 bsz);;
             blk <- gen_blk_with_term_wt c tm n pl pst;;
             rest <- _gen_proc_with_term_wt c tm fsz' bsz pl pst;;
             ret ((blk, false) :: rest)
  end.

Definition gen_proc_with_term_wt (c: rctx) (tm: tmem) (fsz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret []
  | S fsz' => n <- choose (1, max 1 bsz);;
             blk <- gen_blk_with_term_wt c tm n pl pst;;
             rest <- _gen_proc_with_term_wt c tm fsz' bsz pl pst;;
             ret ((blk, true) :: rest)
  end.

Fixpoint _gen_prog_with_term_wt (c: rctx) (tm: tmem) (bsz pl: nat) (pst pst': list nat) : G (list (list inst * bool)) :=
  match pst' with
  | [] => ret []
  | hd :: tl => hd_proc <- gen_proc_with_term_wt c tm hd bsz pl pst;;
               tl_proc <- _gen_prog_with_term_wt c tm bsz pl pst tl;;
               ret (hd_proc ++ tl_proc)
  end.

Definition gen_prog_with_term_wt_example (pl: nat) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  pst <- gen_partition pl;;
  let bsz := 5%nat in
  _gen_prog_with_term_wt c tm bsz pl pst pst.

Definition prog_basic_block_checker (p: prog) : bool :=
  forallb (fun bp => (basic_block_checker (fst bp))) p.


Fixpoint _gen_proc_wt (c: rctx) (tm: tmem) (psz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match psz with
  | O => ret []
  | S psz' => n <- choose (1, max 1 bsz);;
             blk <- gen_blk_wt c tm n pl pst;;
             rest <- _gen_proc_wt c tm psz' bsz pl pst;;
             ret ((blk, false) :: rest)
  end.

Definition gen_proc_wt (c: rctx) (tm: tmem) (psz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match psz with
  | O => ret []
  | S psz' => n <- choose (1, max 1 bsz);;
             blk <- gen_blk_wt c tm n pl pst;;
             rest <- _gen_proc_wt c tm psz' bsz pl pst;;
             ret ((blk, true) :: rest)
  end.

Fixpoint _gen_prog_wt (c: rctx) (tm: tmem) (bsz pl: nat) (pst pst': list nat) : G (list (list inst * bool)) :=
  match pst' with
  | [] => ret []
  | hd :: tl => hd_proc <- gen_proc_wt c tm hd bsz pl pst;;
               tl_proc <- _gen_prog_wt c tm bsz pl pst tl;;
               ret (hd_proc ++ tl_proc)
  end.

Definition gen_prog_wt_example (pl: nat) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  pst <- gen_partition pl;;
  let bsz := 5%nat in
  _gen_prog_wt c tm bsz pl pst pst.

Definition test_wt_example : G bool :=
  prog <- gen_prog_wt_example 8;;
  ret (wf prog).

Definition gen_prog_wt (bsz pl: nat) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  pst <- gen_partition pl;;
  _gen_prog_wt c tm bsz pl pst pst.

Definition gen_prog_wt' (c : rctx) (pst : list nat) (bsz pl : nat) :=
  tm <- arbitrary;;
  _gen_prog_wt c tm bsz pl pst pst.



Fixpoint ty_exp (c: rctx) (e: exp) : option ty :=
  match e with
  | ANum _ => Some TNum
  | FPtr _ => Some TPtr
  | AId x => Some (t_apply c x)
  | ACTIf e1 e2 e3 => match ty_exp c e1 with
                     | Some TNum => match ty_exp c e2, ty_exp c e3 with
                                   | Some TNum, Some TNum => Some TNum
                                   | Some TPtr, Some TPtr => Some TPtr
                                   | _, _ => None
                                   end
                     | _ => None
                     end
  | ABin bop e1 e2 => match bop with
                     | BinEq =>  match ty_exp c e1, ty_exp c e2 with
                                | Some t1, Some t2 => if (ty_eqb t1 t2) then Some TNum else None
                                | _, _ => None
                                end
                     | _ => match ty_exp c e1, ty_exp c e2 with
                           | Some TNum, Some TNum => Some TNum
                           | _, _ => None
                           end
                     end
  end.

Fixpoint ty_inst (c: rctx) (tm: tmem) (p: prog) (i: inst) : bool :=
  match i with
  | ISkip | ICTarget | IRet => true
  | IAsgn x e => match ty_exp c e with
                | Some t => ty_eqb (t_apply c x) t
                | _ => false
                end
  | IBranch e l => match ty_exp c e with
                  | Some TNum => wf_label p false l
                  | _ => false
                  end
  | IJump l => wf_label p false l

  | ILoad x e => match e with
                | ANum n =>
                    match nth_error tm n with
                    | Some t => ty_eqb (t_apply c x) t
                    | _ => false
                    end
                | _ => match ty_exp c e with
                      | Some TNum => true
                      | _ => false
                      end
                end
  | IStore a e => match a with
                 | ANum n =>
                     match nth_error tm n, ty_exp c e with
                     | Some t1, Some t2 => ty_eqb t1 t2
                     | _, _ => false
                     end
                 | _ => match ty_exp c a, ty_exp c e with
                       | Some TNum, Some _ => true
                       | _, _ => false
                       end
                 end
  | ICall e => match e with
              | FPtr (l, 0) => wf_label p true l
              | _ => match ty_exp c e with
                    | Some TPtr => true
                    | _ => false
                    end
              end
  | _ => false
  end.

Definition ty_blk (c: rctx) (tm: tmem) (p: prog) (blk: list inst * bool) : bool :=
  forallb (ty_inst c tm p) (fst blk).

Definition ty_prog (c: rctx) (tm: tmem) (p: prog) : bool :=
  forallb (ty_blk c tm p) p.

Definition gen_prog_ty_ctx_wt (bsz pl: nat) : G (rctx * tmem * prog) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  pst <- gen_partition pl;;
  p <- _gen_prog_wt c tm bsz pl pst pst;;
  ret (c, tm, p).





Definition join (l1 l2 : label) : label := l1 && l2.

Fixpoint vars_exp (e:exp) : list string :=
  match e with
  | ANum n => []
  | AId i => [i]
  | ABin op e1 e2 => vars_exp e1 ++ vars_exp e2
  | ACTIf e1 e2 e3 => vars_exp e1 ++ vars_exp e2 ++ vars_exp e3
  | FPtr n => []
  end.

Definition vars_inst (i: inst) : list string :=
  match i with
  | ISkip | IRet | ICTarget | IJump _ => []
  | IAsgn x e => x :: vars_exp e
  | IBranch e l => vars_exp e
  | ILoad x e => x :: vars_exp e
  | IStore e1 e2 => vars_exp e1 ++ vars_exp e2
  | ICall e => vars_exp e
  | IDiv x e1 e2 => x :: (vars_exp e1 ++ vars_exp e2)
  | IPeek _ => [] (* We don't want to generate peek for the source code. *)
  end.

Fixpoint vars_blk (blk: list inst) : list string :=
  List.concat (map vars_inst blk).

Fixpoint _vars_prog (p: prog) : list string :=
  match p with
  | [] => []
  | (blk, _) :: tl => vars_blk blk ++ _vars_prog tl
  end.

Definition vars_prog (p: prog) : list string :=
  remove_dupes String.eqb (_vars_prog p).

Definition label_of_exp (P:pub_vars) (e:exp) : label :=
  List.fold_left (fun l a => join l (P ! a)) (vars_exp e) public.





Definition gen_prog_ty_ctx_wt' (bsz pl: nat) : G (rctx * tmem * list nat * prog) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  pst <- gen_partition pl;;
  p <- _gen_prog_wt c tm bsz pl pst pst;;
  ret (c, tm, pst, p).

Definition gen_prog_wt_with_basic_blk (bsz pl: nat) : G (rctx * tmem * list nat * prog) :=
  c <- arbitrary;;
  tm <- arbitrary;;
  pst <- gen_partition pl;;
  p <- _gen_prog_with_term_wt c tm bsz pl pst pst;;
  ret (c, tm, pst, p).

Definition gen_wt_mem (tm: tmem) (pst: list nat) : G mem :=
  let indices := seq 0 (Datatypes.length tm) in
  let idx_tm := combine indices tm in
  let gen_binds := mapGen (fun '(idx, t) => (v <- gen_val_wt t pst;; ret (idx, v))) idx_tm in
  r <- gen_binds;;
  ret (snd (split r)).



Definition all_possible_vars : list string := (["X0"%string; "X1"%string; "X2"%string; "X3"%string; "X4"%string; "X5"%string]).

Fixpoint member (n: nat) (l: list nat) : bool :=
  match l with
  | [] => false
  | hd::tl => if (hd =? n) then true else member n tl
  end.

Fixpoint _tms_to_pm (tms: list nat) (len: nat) (cur: nat) : list label :=
  match len with
  | 0 => []
  | S len' => member cur tms :: _tms_to_pm tms len' (S cur)
  end.


Definition tms_to_pm (len: nat) (tms: list nat) : list label :=
  _tms_to_pm tms len 0.

Compute (tms_to_pm 8 [3; 4; 5]).


Definition wt_valb (v: val) (t: ty) : bool :=
  match v, t with
  | N _, TNum | FP _, TPtr => true
  | _, _ => false
  end.

Definition rs_wtb (rs : total_map val) (c : rctx) : bool :=
  let '(dv, m) := rs in
  let '(dt, tm) := c in
  wt_valb dv dt && forallb (fun '(x, t) => wt_valb (t_apply rs x) t) tm.

Fixpoint _gen_pub_mem_equiv_same_ty (P : list label) (m: list val) : G (list val) :=
  let f := fun v => match v with
                 | N _ => n <- arbitrary;; ret (N n)
                 | FP _ => l <- arbitrary;; ret (FP l)
                 | UV => ret UV
                 end in
  match P, m with
  | [], [] => ret []
  | hdp::tlp, hdm::tlm =>
      hd <- (if hdp then ret hdm else f hdm);;
      tl <-_gen_pub_mem_equiv_same_ty tlp tlm;;
      ret (hd::tl)
  | _, _ => ret []
  end.

Fixpoint gen_pub_mem_equiv_same_ty (P : list label) (m: list val) : G (list val) :=
  if (Datatypes.length P =? Datatypes.length m)
  then _gen_pub_mem_equiv_same_ty P m
  else ret [].

Definition m_wtb (m: mem) (tm: tmem) : bool :=
  let mtm := combine m tm in
  forallb (fun '(v, t) => wt_valb v t) mtm.



Definition gen_inst_no_obs (pl: nat) (pst: list nat) : G inst :=
  let jlb := (list_minus (add_zeros (seq 0 (pl - 1))) (proc_hd pst)) in
  if seq.nilp jlb
  then ret <{ skip }>
  else freq [
           (1, ret ISkip);
           (1, ret IRet);
           (1, l <- elems_ (0,0) jlb;; ret (IJump (fst l)))
         ].

Definition gen_blk_no_obs (bsz pl: nat) (pst: list nat) : G (list inst) :=
  vectorOf bsz (gen_inst_no_obs pl pst).

Fixpoint _gen_proc_no_obs (fsz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret []
  | S fsz' =>
      n <- choose (1, max 1 bsz);;
      blk <- gen_blk_no_obs n pl pst;;
      rest <- _gen_proc_no_obs fsz' bsz pl pst;;
      ret ((blk, false) :: rest)
  end.

Definition gen_proc_no_obs (fsz bsz pl: nat) (pst: list nat) : G (list (list inst * bool)) :=
  match fsz with
  | O => ret []
  | S fsz' =>
      n <- choose (1, max 1 bsz);;
      blk <- gen_blk_no_obs n pl pst;;
      rest <- _gen_proc_no_obs fsz' bsz pl pst;;
      ret ((blk, true) :: rest)
  end.

Fixpoint _gen_prog_no_obs (bsz pl: nat) (pst pst': list nat) : G (list (list inst * bool)) :=
  match pst' with
  | [] => ret []
  | hd :: tl =>
      hd_proc <- gen_proc_no_obs hd bsz pl pst;;
      tl_proc <- _gen_prog_no_obs bsz pl pst tl;;
      ret (hd_proc ++ tl_proc)
  end.

Definition gen_no_obs_prog : G prog :=
  pl <- choose(2, 6);;
  pst <- gen_partition pl;;
  let bsz := 3 in
  _gen_prog_no_obs bsz pl pst pst.

Definition empty_mem : mem := [].

Definition empty_rs : reg := t_empty (FP (0, 0)).

Definition spec_rs (rs: reg) := (callee !-> (FP (0, 0)); (msf !-> (N 0); rs)).
