(*** The initial framework taken from the artifact of Arranz-Olmos et. al., "Preservation of Speculative Constant-Time by Compilation" ***)
(*** See: https://dl.acm.org/doi/10.1145/3704880 and https://artifacts.formosa-crypto.org/data/sct-preservation.tbz ***)

From Stdlib Require Import List PeanoNat Relation_Definitions.
From SECF Require Import Utils.
Import ListNotations.
#[local, warning="-notation-overridden"]
Notation "x ++ y" := (List.app x y) (right associativity, at level 60).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class Language (input : Type) :=
  {
    prog : Type;
    directive : Type;
    observation : Type;
    machine : Type;
    initial_machine : prog -> input -> machine;
    step :
      prog ->
      machine ->
      directive ->
      observation ->
      machine ->
      Prop;
    sequential_safe1 : prog -> machine -> Prop;
  }.

Arguments prog {_} {L} : rename.
Arguments directive {_} {L} : rename.
Arguments observation {_} {L} : rename.
Arguments machine {_} {L} : rename.
Arguments initial_machine {_} {L} : rename.
Arguments step {_} {L} : rename.
Arguments sequential_safe1 {_} {L} : rename.

Section SEM.

Context
  {input : Type}
  {L : Language input}
.

Inductive sem (p : prog) :
  machine -> list directive -> list observation -> machine -> Prop :=
| sem_refl :
    forall m, sem p m [] [] m

| sem_step :
    forall m m' m'' d o ds os,
      step p m d o m' ->
      sem p m' ds os m'' ->
      sem p m (d :: ds) (o :: os) m''
.

Definition sem_p
  (p : prog)
  (inp : input)
  (ds : list directive)
  (os : list observation)
  (m' : machine) :
  Prop :=
  sem p (initial_machine p inp) ds os m'.

End SEM.

Section FACTS.

Context
  {input : Type}
  {L : Language input}
.

Lemma semI p m ds os m' :
  sem p m ds os m' <->
  match ds with
  | [] => os = [] /\ m' = m
  | d :: ds' =>
      exists o os' mi,
        os = o :: os' /\ step p m d o mi /\ sem p mi ds' os' m'
    end.
Proof.
  split.
  - intros H. destruct H as [m0 | m0 mi m0' d o ds0 os0 Hstep Hsem].
    + split; reflexivity.
    + exists o, os0, mi. split; [reflexivity|]. split; assumption.
  - destruct ds as [|d ds].
    + intros [-> ->]. apply sem_refl.
    + intros [o [os' [mi [-> [Hstep Hsem]]]]].
      eapply sem_step; eassumption.
Qed.

Lemma sem_step1 p m d o m' :
  step p m d o m' ->
  sem p m [d] [o] m'.
Proof.
  intros h.
  eapply sem_step; [exact h | apply sem_refl].
Qed.

Lemma sem_step1I p m m' d os :
  sem p m [d] os m' ->
  exists2 o, os = [o] & step p m d o m'.
Proof.
  intros H. apply semI in H.
  destruct H as [o [os' [mi [-> [Hstep Hsem]]]]].
  apply semI in Hsem. destruct Hsem as [-> ->].
  exists o; [reflexivity | exact Hstep].
Qed.

Lemma sem_cat p m m' m'' D D' O O' :
  sem p m D O m' ->
  sem p m' D' O' m'' ->
  sem p m (D ++ D') (O ++ O') m''.
Proof.
  intros H1 H2.
  revert H2.
  induction H1; intros H2; simpl.
  - exact H2.
  - eapply sem_step; [eassumption|].
    apply IHsem; assumption.
Qed.

Lemma size_obs p m ds os m' :
  sem p m ds os m' ->
  length ds = length os.
Proof. induction 1; simpl; congruence. Qed.

End FACTS.

Section SAFETY.

  Context
    {input : Type}
    {L : Language input}
  .

  Definition sequential_safe (p : prog) (m : machine) : Prop :=
    forall ds os m', sem p m ds os m' -> sequential_safe1 p m'.

  Lemma sequential_safe_sem p m m' ds os :
    sequential_safe p m ->
    sem p m ds os m' ->
    sequential_safe p m'.
  Proof.
    intros hsafe hsem ds' os' m'' hsem'.
    apply (hsafe (ds ++ ds') (os ++ os')).
    eapply sem_cat; eassumption.
  Qed.

  Lemma sequential_safe_step p m m' d o :
    sequential_safe p m ->
    step p m d o m' ->
    sequential_safe p m'.
  Proof.
    intros hsafe hstep.
    eapply sequential_safe_sem; [exact hsafe|].
    apply sem_step1.
    exact hstep.
  Qed.

End SAFETY.

Section BACKWARD.

Context
  {input : Type}
  {Ls Lt : Language input}
.

Definition compiler : Type := prog (L := Ls) -> prog (L := Lt) -> Prop.

Definition input_sync : Type := prog (L := Ls) -> input -> input -> Prop.

Section HISTORY.

  Context (history : Type).

  Definition sim_t0 : Type :=
    history ->
    machine (L := Ls) ->
    machine (L := Lt) ->
    Prop.

  Definition Tdir_t0 : Type :=
    history ->
    directive (L := Lt) ->
    list (directive (L := Ls)).

  Definition Tobs_t0 : Type :=
    history ->
    directive (L := Lt) ->
    list (observation (L := Ls)) ->
    list (observation (L := Lt)).

End HISTORY.

Class History :=
  {
    history : Type;
    init_hist : history;
    This : history -> directive (L := Lt) -> observation (L := Lt) -> history;
  }.

Definition sim_t {hist : History} := Eval hnf in sim_t0 history.
Definition Tdir_t {hist : History} := Eval hnf in Tdir_t0 history.
Definition Tobs_t {hist : History} := Eval hnf in Tobs_t0 history.

Definition safe_step_preserves_sim
  (p_s : prog (L := Ls))
  (p_t : prog (L := Lt))
  {hist : History}
  (sim : sim_t)
  (Tdir : Tdir_t)
  (Tobs : Tobs_t) :
  Prop :=
  forall d h o_t s t t',
    sim h s t ->
    sequential_safe p_s s ->
    step p_t t d o_t t' ->
    exists s' os_s,
      sem p_s s (Tdir h d) os_s s'
      /\ [o_t] = Tobs h d os_s
      /\ sim (This h d o_t) s' t'.

Definition initial_sim
  (p_s : prog (L := Ls))
  (p_t : prog (L := Lt))
  (sync : input_sync)
  {hist : History}
  (sim : sim_t) :
  Prop :=
  forall inp inp',
    sync p_s inp inp' ->
    sim init_hist (initial_machine p_s inp) (initial_machine p_t inp').

Definition has_safe_bw_simulation (compile : compiler) (sync : input_sync) :=
  forall p_s p_t,
    compile p_s p_t ->
    exists (_ : History) sim Tdir Tobs,
      initial_sim p_s p_t sync sim
      /\ safe_step_preserves_sim p_s p_t sim Tdir Tobs.


(* -------------------------------------------------------------------------- *)
(* Most passes don't need safety. *)

Definition step_preserves_sim
  (p_s : prog (L := Ls))
  (p_t : prog (L := Lt))
  {hist : History}
  (sim : sim_t)
  (Tdir : Tdir_t)
  (Tobs : Tobs_t) :
  Prop :=
  forall d h o_t s t t',
    sim h s t ->
    step p_t t d o_t t' ->
    exists s' os_s,
      sem p_s s (Tdir h d) os_s s'
      /\ [o_t] = Tobs h d os_s
      /\ sim (This h d o_t) s' t'.

Definition has_bw_simulation (compile : compiler) (sync : input_sync) :=
  forall p_s p_t,
    compile p_s p_t ->
    exists (_ : History) sim Tdir Tobs,
      initial_sim p_s p_t sync sim
      /\ step_preserves_sim p_s p_t sim Tdir Tobs.

Lemma lift_bw_simulation compile sync :
  has_bw_simulation compile sync ->
  has_safe_bw_simulation compile sync.
Proof.
  intros hbw p_s p_t hcomp.
  destruct (hbw p_s p_t hcomp) as [hist [sim [Tdir [Tobs [hinit hbw']]]]].
  exists hist, sim, Tdir, Tobs.
  split; [exact hinit|].
  intros d h o_t s t t' hsim _ hstep.
  exact (hbw' d h o_t s t t' hsim hstep).
Qed.


(* -------------------------------------------------------------------------- *)
(* Lifting single-step simulation into multi-step ones. *)

Section TRANSFORMERS.

  Context
    {hist : History}
    (Tdir : Tdir_t)
    (Tobs : Tobs_t)
  .

  Fixpoint Tdir_sem
    (h : history)
    (ds : list (directive (L := Lt)))
    (os_t : list (observation (L := Lt))) :
    list (directive (L := Ls)) :=
    match ds, os_t with
    | d :: ds, o :: os_t => Tdir h d ++ Tdir_sem (This h d o) ds os_t
    | _, _ => []
    end.

  Fixpoint Tobs_sem
    (h : history)
    (ds : list (directive (L := Lt)))
    (os_t : list (observation (L := Lt)))
    (os_s : list (observation (L := Ls))) :
    list (observation (L := Lt)) :=
    match ds, os_t with
    | d :: ds, o :: os_t =>
        let n := length (Tdir h d) in
        Tobs h d (firstn n os_s) ++ Tobs_sem (This h d o) ds os_t (skipn n os_s)
    | _, _ => []
    end.

End TRANSFORMERS.

(* We don't need to ensure that the resulting machines are related. *)
Definition safe_sem_preserves_sim
  (p_s : prog (L := Ls))
  (p_t : prog (L := Lt))
  {hist : History}
  (sim : sim_t)
  (Tdir : Tdir_t)
  (Tobs : Tobs_t) :
  Prop :=
  forall ds h os_t s t t',
    sim h s t ->
    sequential_safe p_s s ->
    sem p_t t ds os_t t' ->
    exists s' os_s,
      sem p_s s (Tdir_sem Tdir h ds os_t) os_s s'
      /\ os_t = Tobs_sem Tdir Tobs h ds os_t os_s.

Lemma lift_step_preserves_sim p_s p_t {_ : History} sim Tdir Tobs :
  safe_step_preserves_sim p_s p_t sim Tdir Tobs ->
  safe_sem_preserves_sim p_s p_t sim Tdir Tobs.
Proof.
  intros hbw ds.
  induction ds as [|d ds hind]; intros h os_t s t t' hsim hsafe hsem; apply semI in hsem.
  - destruct hsem as [-> ->].
    exists s, [].
    split; [apply sem_refl | reflexivity].
  - destruct hsem as [o_t [os_t' [ti [-> [hstep hsem]]]]].
    destruct (hbw _ _ _ _ _ _ hsim hsafe hstep) as [s' [os_s [hsem_s [hobs hsim']]]].
    pose proof (sequential_safe_sem hsafe hsem_s) as hsafe'.
    destruct (hind _ _ _ _ _ hsim' hsafe' hsem) as [s'' [os_s' [hsem_s' hobs']]].
    exists s'', (os_s ++ os_s'). simpl. split.
    + eapply sem_cat; eassumption.
    + rewrite (size_obs hsem_s), firstn_app, skipn_app, Nat.sub_diag,
        firstn_O, skipn_O, app_nil_r, firstn_all, skipn_all, app_nil_l, <- hobs, <- hobs'.
      reflexivity.
Qed.


(* -------------------------------------------------------------------------- *)
(* Using directives and observations as history suffices. *)

Section TRACE_AS_HISTORY.

Let current_hist {_ : History} (h : list (directive (L := Lt) * observation (L := Lt))) :=
  fold_left (fun h0 dobs => This h0 (fst dobs) (snd dobs)) h init_hist.
Let sim_hist {_ : History} (sim : sim_t) h := sim (current_hist h).
Let Tdir_hist {_ : History} (Tdir : Tdir_t) h := Tdir (current_hist h).
Let Tobs_hist {_ : History} (Tobs : Tobs_t) h := Tobs (current_hist h).

#[local]
Instance TraceHist : History :=
  {|
    history := list (directive (L := Lt) * observation (L := Lt));
    init_hist := [];
    This := fun h d o => h ++ [(d, o)];
  |}.

Lemma trace_as_history compile sync :
  has_bw_simulation compile sync ->
  forall p_s p_t,
    compile p_s p_t ->
    exists sim Tdir Tobs,
      initial_sim (hist := TraceHist) p_s p_t sync sim
      /\ step_preserves_sim (hist := TraceHist) p_s p_t sim Tdir Tobs.
Proof.
  intros hbw p_s p_t hcomp.
  destruct (hbw p_s p_t hcomp) as [hist [sim [Tdir [Tobs [hinit hbw']]]]].
  exists (sim_hist sim), (Tdir_hist Tdir), (Tobs_hist Tobs).
  split; [exact hinit|].
  intros d h o_t s t t' hsim hstep_t.
  destruct (hbw' _ _ _ _ _ _ hsim hstep_t) as [s' [os_s [hsem_s [hobs hsim']]]].
  exists s', os_s.
  split; [exact hsem_s|].
  split; [exact hobs|].
  unfold sim_hist, current_hist. simpl.
  rewrite fold_left_app. exact hsim'.
Qed.

End TRACE_AS_HISTORY.


(* -------------------------------------------------------------------------- *)
(* Lock-step simulations. *)

Definition safe_step_preserves_sim_lockstep_h
  (p_s : prog (L := Ls))
  (p_t : prog (L := Lt))
  {hist : History}
  (sim : sim_t)
  (Tdir : history -> directive (L := Lt) -> directive (L := Ls))
  (Tobs :
    history ->
    directive (L := Lt) ->
    observation (L := Ls) ->
    observation (L := Lt)) :
  Prop :=
  forall d h o_t s t t',
    sim h s t ->
    sequential_safe p_s s ->
    step p_t t d o_t t' ->
    exists s' o_s,
      step p_s s (Tdir h d) o_s s'
      /\ o_t = Tobs h d o_s
      /\ sim (This h d o_t) s' t'.

Definition has_safe_lockstep_h_bw_simulation (compile : compiler) (sync : input_sync) :=
  forall p_s p_t,
    compile p_s p_t ->
    exists (_ : History) sim Tdir Tobs,
      initial_sim p_s p_t sync sim
      /\ safe_step_preserves_sim_lockstep_h p_s p_t sim Tdir Tobs.

Lemma lift_safe_lockstep_h compile sync :
  has_safe_lockstep_h_bw_simulation compile sync ->
  has_safe_bw_simulation compile sync.
Proof.
  intros hbw p_s p_t hcomp.
  destruct (hbw p_s p_t hcomp) as [hist [sim [Tdir [Tobs [hinit hbw']]]]].
  exists
    hist,
    sim,
    (fun h d => [Tdir h d]),
    (fun h d os => map (Tobs h d) os).
  split; [exact hinit|].
  intros d h o_t s t t' hsim hsafe hstep_t.
  destruct (hbw' _ _ _ _ _ _ hsim hsafe hstep_t) as [s' [o_s [hstep_s [-> hsim']]]].
  exists s', [o_s].
  split; [apply sem_step1; exact hstep_s|].
  split; [reflexivity | exact hsim'].
Qed.


(* -------------------------------------------------------------------------- *)
(* Lock-step simulations without history. *)

Definition step_preserves_sim_lockstep
  (p_s : prog (L := Ls))
  (p_t : prog (L := Lt))
  (sim : machine (L := Ls) -> machine (L := Lt) -> Prop)
  (Tdir : directive (L := Lt) -> directive (L := Ls))
  (Tobs : observation (L := Ls) -> observation (L := Lt)) :
  Prop :=
  forall d o_t s t t',
    sim s t ->
    step p_t t d o_t t' ->
    exists s' o_s,
      step p_s s (Tdir d) o_s s'
      /\ o_t = Tobs o_s
      /\ sim s' t'.

Definition has_lockstep_bw_simulation (compile : compiler) (sync : input_sync) :=
  forall p_s p_t,
    compile p_s p_t ->
    exists sim Tdir Tobs,
      (forall inp inp',
          sync p_s inp inp' ->
          sim (initial_machine p_s inp) (initial_machine p_t inp'))
      /\ step_preserves_sim_lockstep p_s p_t sim Tdir Tobs.

Lemma lift_lockstep compile sync :
  has_lockstep_bw_simulation compile sync ->
  has_bw_simulation compile sync.
Proof.
  intros hbw p_s p_t hcomp.
  destruct (hbw p_s p_t hcomp) as [sim [Tdir [Tobs [hinit hbw']]]].
  exists
    TraceHist,
    (fun _ => sim),
    (fun _ d => [Tdir d]),
    (fun _ _ os => map Tobs os).
  split; [exact hinit|].
  intros d h o_t s t t' hsim hstep_t.
  destruct (hbw' _ _ _ _ _ hsim hstep_t) as [s' [o_s [hstep_s [-> hsim']]]].
  exists s', [o_s].
  split; [apply sem_step1; exact hstep_s|].
  split; [reflexivity | exact hsim'].
Qed.

End BACKWARD.

Section FORWARD.

Context
  {input : Type}
  {Ls Lt : Language input}
  (p_s : prog (L := Ls))
  (p_t : prog (L := Lt))
  (R : machine (L := Ls) -> machine (L := Lt) -> Prop)
  (Tdir : directive (L := Lt) -> directive (L := Ls))
  (Tobs : observation (L := Ls) -> observation (L := Lt)).

Record forward_lock_step_simulation_diagram : Prop :=
  { fls_init :
    forall inp, R (initial_machine p_s inp) (initial_machine p_t inp)
  ; fls_step :
    forall d s o s' t,
      R s t ->
      step p_s s (Tdir d) o s' ->
      exists2 t', step p_t t d (Tobs o) t' & R s' t'
  }.

Context (diag: forward_lock_step_simulation_diagram).

Definition forward_semantics_preservation : Prop :=
  forall inp ds os s,
    sem_p p_s inp (map Tdir ds) os s ->
    exists t, sem_p p_t inp ds (map Tobs os) t.

Lemma forward_lock_step_to_full_trace : forward_semantics_preservation.
Proof.
  intros inp ds.
  pose proof (fls_init diag inp) as r.
  revert r.
  unfold sem_p.
  generalize (initial_machine p_t inp) as t.
  generalize (initial_machine p_s inp) as s.
  clear inp.
  induction ds as [|d ds ih]; intros s t r os s' H; apply semI in H.
  - destruct H as [-> _].
    exists t. apply sem_refl.
  - destruct H as [o [os' [mi [-> [step_s sem_s]]]]].
    destruct (fls_step diag r step_s) as [t' step_t r'].
    destruct (ih _ _ r' _ _ sem_s) as [tf exec_t].
    exists tf. simpl. eapply sem_step; eassumption.
Qed.

End FORWARD.

Section COMPOSITION.

Context
  {input : Type}
  {L0 L1 L2 : Language input}
  (compile2 : compiler (Ls := L1) (Lt := L2))
  (compile1 : compiler (Ls := L0) (Lt := L1))
.

Definition compose : compiler (Ls := L0) (Lt := L2) :=
  fun p_s p_t => exists2 p_i, compile1 p_s p_i & compile2 p_i p_t.

End COMPOSITION.

(* -------------------------------------------------------------------------- *)
(* Speculative constant time (phi-SCT). *)

Section DEFINITION.

Context
  {input : Type}
  {L : Language input}
.

Definition is_sct (phi : relation input) (p : prog) : Prop :=
  forall ds os1 os2 inp1 inp2 out1 out2,
    phi inp1 inp2 ->
    sem_p p inp1 ds os1 out1 ->
    sem_p p inp2 ds os2 out2 ->
    os1 = os2.

End DEFINITION.

Definition sequential_safe_phi
  {input : Type}
  {L : Language input}
  (p : prog)
  (phi : relation input) :
  Prop :=
  forall inp1 inp2,
    phi inp1 inp2 ->
    sequential_safe p (initial_machine p inp1)
    /\ sequential_safe p (initial_machine p inp2).

Section ANTITONE.

Context
  {input : Type}
  {L : Language input}
  (phi phi' : relation input)
  (hsub : forall inp1 inp2, phi' inp1 inp2 -> phi inp1 inp2)
.

Lemma is_sct_antitone p :
  is_sct phi p -> is_sct phi' p.
Proof.
  intros hsct ds os1 os2 inp1 inp2 out1 out2 hphi'.
  exact (hsct ds os1 os2 inp1 inp2 out1 out2 (hsub hphi')).
Qed.

Lemma sequential_safe_phi_antitone p :
  sequential_safe_phi p phi -> sequential_safe_phi p phi'.
Proof.
  intros hsafe inp1 inp2 hphi'.
  exact (hsafe inp1 inp2 (hsub hphi')).
Qed.

End ANTITONE.

Section PRESERVATION.

Context
  {input : Type}
  {Ls Lt : Language input}
  (compile : compiler (Ls := Ls) (Lt := Lt))
  (sync : input_sync (Ls := Ls))
.

Definition sync_rel (p_s : prog (L := Ls)) (phi : relation input) : relation input :=
  fun inp1' inp2' =>
    exists inp1 inp2,
      phi inp1 inp2 /\ sync p_s inp1 inp1' /\ sync p_s inp2 inp2'.

Definition preserves_safety (phi : relation input) : Prop :=
  forall p_s p_t,
    compile p_s p_t ->
    sequential_safe_phi p_s phi ->
    sequential_safe_phi p_t (sync_rel p_s phi).

Definition preserves_sct (phi : relation input) : Prop :=
  forall p_s p_t,
    compile p_s p_t ->
    sequential_safe_phi p_s phi ->
    is_sct phi p_s ->
    is_sct (sync_rel p_s phi) p_t.

Lemma safe_step_preserves_sim_same_obs
  (p_s : prog (L := Ls))
  (p_t : prog (L := Lt))
  {hist : History (Lt := Lt)}
  (sim : sim_t (Ls := Ls) (Lt := Lt))
  (Tdir : Tdir_t (Ls := Ls) (Lt := Lt))
  (Tobs : Tobs_t (Ls := Ls) (Lt := Lt))
  (phi : relation input)
  inp1 inp2 :
  safe_step_preserves_sim p_s p_t sim Tdir Tobs ->
  is_sct phi p_s ->
  phi inp1 inp2 ->
  forall ds h D O1 O2 s1 s2 t1 t2 os1 os2 t1' t2',
    sem_p p_s inp1 D O1 s1 ->
    sem_p p_s inp2 D O2 s2 ->
    sequential_safe p_s s1 ->
    sequential_safe p_s s2 ->
    sim h s1 t1 ->
    sim h s2 t2 ->
    sem p_t t1 ds os1 t1' ->
    sem p_t t2 ds os2 t2' ->
    os1 = os2.
Proof.
  intros hbw hsct hphi ds.
  induction ds as [|d ds hind];
    intros h D O1 O2 s1 s2 t1 t2 os1 os2 t1' t2'
      hpre1 hpre2 hsafe1 hsafe2 hsim1 hsim2 hsem1 hsem2;
    apply semI in hsem1; apply semI in hsem2.
  - destruct hsem1 as [-> _], hsem2 as [-> _]. reflexivity.
  - destruct hsem1 as [o1 [os1' [ti1 [-> [hstep1 hsem1]]]]].
    destruct hsem2 as [o2 [os2' [ti2 [-> [hstep2 hsem2]]]]].
    destruct (hbw _ _ _ _ _ _ hsim1 hsafe1 hstep1) as [s1' [os_s1 [hsem_s1 [hobs1 hsim1']]]].
    destruct (hbw _ _ _ _ _ _ hsim2 hsafe2 hstep2) as [s2' [os_s2 [hsem_s2 [hobs2 hsim2']]]].
    assert (O1 = O2) as <- by exact (hsct _ _ _ _ _ _ _ hphi hpre1 hpre2).
    assert (os_s1 = os_s2) as <-.
    { apply (app_inv_head O1).
      exact (hsct _ _ _ _ _ _ _ hphi (sem_cat hpre1 hsem_s1) (sem_cat hpre2 hsem_s2)). }
    assert (o1 = o2) as <- by congruence.
    f_equal.
    exact (hind (This h d o1) (D ++ Tdir h d) (O1 ++ os_s1) (O1 ++ os_s1)
             s1' s2' ti1 ti2 os1' os2' t1' t2'
             (sem_cat hpre1 hsem_s1) (sem_cat hpre2 hsem_s2)
             (sequential_safe_sem hsafe1 hsem_s1) (sequential_safe_sem hsafe2 hsem_s2)
             hsim1' hsim2' hsem1 hsem2).
Qed.

Lemma has_safe_bw_simulation_preserves_sct phi :
  has_safe_bw_simulation compile sync ->
  preserves_sct phi.
Proof.
  intros hbw p_s p_t hcomp hsafe hsct ds os1 os2 inp1' inp2' out1 out2
    [inp1 [inp2 [hphi [hsync1 hsync2]]]] hsem_t1 hsem_t2.
  destruct (hbw p_s p_t hcomp) as [hist [sim [Tdir [Tobs [hinit hbw']]]]].
  destruct (hsafe _ _ hphi) as [hsafe1 hsafe2].
  exact (safe_step_preserves_sim_same_obs hbw' hsct hphi
           (sem_refl _ _) (sem_refl _ _) hsafe1 hsafe2
           (hinit _ _ hsync1) (hinit _ _ hsync2) hsem_t1 hsem_t2).
Qed.

End PRESERVATION.

Section COMPOSITION.

Context
  {input : Type}
  {L0 L1 L2 : Language input}
  (compile2 : compiler (Ls := L1) (Lt := L2))
  (compile1 : compiler (Ls := L0) (Lt := L1))
  (sync2 : input_sync (Ls := L1))
  (sync1 : input_sync (Ls := L0))
.

Definition compose_sync : input_sync (Ls := L0) :=
  fun p_s inp inp'' =>
    forall p_i,
      compile1 p_s p_i ->
      exists2 inp', sync1 p_s inp inp' & sync2 p_i inp' inp''.

Lemma sync_rel_compose p_s p_i phi :
  compile1 p_s p_i ->
  forall inp1'' inp2'',
    sync_rel compose_sync p_s phi inp1'' inp2'' ->
    sync_rel sync2 p_i (sync_rel sync1 p_s phi) inp1'' inp2''.
Proof.
  intros h1 inp1'' inp2'' [inp1 [inp2 [hphi [hsync1 hsync2]]]].
  destruct (hsync1 _ h1) as [inp1' hs1 hs1'].
  destruct (hsync2 _ h1) as [inp2' hs2 hs2'].
  exists inp1', inp2'.
  split; [|split; assumption].
  exists inp1, inp2.
  split; [assumption | split; assumption].
Qed.

Lemma compose_safety phi :
  (forall phi', preserves_safety compile2 sync2 phi') ->
  preserves_safety compile1 sync1 phi ->
  preserves_safety (compose compile2 compile1) compose_sync phi.
Proof.
  intros hpsafe2 hpsafe1 p_s p_t [p_i h1 h2] hsafe.
  apply (sequential_safe_phi_antitone (sync_rel_compose h1)).
  apply (hpsafe2 _ _ _ h2).
  exact (hpsafe1 _ _ h1 hsafe).
Qed.

Lemma compose_sct phi :
  preserves_safety compile1 sync1 phi ->
  (forall phi', preserves_sct compile2 sync2 phi') ->
  preserves_sct compile1 sync1 phi ->
  preserves_sct (compose compile2 compile1) compose_sync phi.
Proof.
  intros hpsafe hpres2 hpres1 p_s p_t [p_i h1 h2] hsafe hsct.
  apply (is_sct_antitone (sync_rel_compose h1)).
  apply (hpres2 _ _ _ h2).
  - exact (hpsafe _ _ h1 hsafe).
  - exact (hpres1 _ _ h1 hsafe hsct).
Qed.

End COMPOSITION.

(* --- Triosecuris: parametrized observational equivalence (applicable to all semantics, with directions in sequential being unit) *)
Section OBSERVATIONAL_EQUIVALENCE.
  Context
    {input : Type}
    {L : Language input}
  .

  Definition same_obs (p : prog) (inp1 inp2 : input) :=
    forall ds os1 os2 out1 out2,
      sem_p p inp1 ds os1 out1 ->
      sem_p p inp2 ds os2 out2 ->
      (Utils.prefix os1 os2) \/ (Utils.prefix os2 os1).

End OBSERVATIONAL_EQUIVALENCE.

(* --- phi-SCT inputs imply same observations, easy *)
Lemma is_sct_same_obs {input : Type} {L : Language input} (phi : relation input) (p : prog (L := L)) (inp1 inp2 : input):
  is_sct phi p -> phi inp1 inp2 -> same_obs p inp1 inp2.
Proof.
  intros Hsct Hphi.
  unfold is_sct in Hsct.
  unfold same_obs.
  intros ds os1 os2 out1 out2 Hsem1 Hsem2.
  specialize (Hsct ds os1 os2 inp1 inp2 out1 out2 Hphi Hsem1 Hsem2).
  left.
  rewrite Hsct.
  apply prefix_refl.
Qed.

(* --- same observations on inp1 and inp2 imply phi-SCT on exactly this inputs, hacky but ok *)
Lemma same_obs_is_sct {input : Type} {L : Language input} (p : prog (L := L)) inp1 inp2 :
  same_obs p inp1 inp2 ->
  is_sct (fun a b => a = inp1 /\ b = inp2) p.
Proof.
  intros Hso ds os1 os2 a b out1 out2 Hsameobs Hsem1 Hsem2.
  pose proof (size_obs Hsem1) as Hlen1.
  pose proof (size_obs Hsem2) as Hlen2.
  rewrite Hlen1 in Hlen2.
  destruct Hsameobs as [Ha Hb]; subst.
  destruct (Hso _ _ _ _ _ Hsem1 Hsem2) as [Hpre | Hpre].
  - apply prefix_same_length; [exact Hpre | congruence].
  - symmetry. apply prefix_same_length; [exact Hpre | congruence].
Qed.

Section RELATIVE_SECURITY.
  Context
    {input : Type}
    {Ls Lt : Language input}
    (compile : compiler (Ls := Ls) (Lt := Lt))
    (sync : prog (L := Ls) -> input -> input -> Prop)
  .

  Definition relative_secure p_s p_t inp1 inp2 :=
      forall inp1' inp2',
      same_obs p_s inp1 inp2 ->
      sync p_s inp1 inp1' ->
      sync p_s inp2 inp2' ->
      compile p_s p_t ->
      same_obs p_t inp1' inp2'.
End RELATIVE_SECURITY.

Section SCT_PRESERVATION_RELSEC.
  Context
    {input : Type}
    {Ls Lt : Language input}
    (compile : compiler (Ls := Ls) (Lt := Lt))
    (sync : input_sync (Ls := Ls))
  .

  Lemma preserves_sct_relsec p_s p_t inp1 inp2 :
    (forall phi, preserves_sct compile sync phi) ->
    sequential_safe p_s (initial_machine p_s inp1) ->
    sequential_safe p_s (initial_machine p_s inp2) ->
    relative_secure compile sync p_s p_t inp1 inp2.
  Proof.
    intros Hphisct Hsafe1 Hsafe2 inp1' inp2' Hsameobs Hsync1 Hsync2 Hcompile.
    apply (is_sct_same_obs 
            (phi := sync_rel sync p_s (fun a b => a = inp1 /\ b = inp2))).
    - apply (Hphisct _ p_s p_t Hcompile).
      + intros a b [-> ->]. split.
        -- apply Hsafe1.
        -- apply Hsafe2.
      + exact (same_obs_is_sct Hsameobs).
    - exists inp1, inp2. auto.
  Qed.
End SCT_PRESERVATION_RELSEC.
